/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import Lean

/-!
# Audit.Core — compile-time checks for circular *physical* definitions

The kernel certifies that a proof follows from its definitions; it cannot certify that a
definition is the physical object its name claims. This module shrinks that residual trust to an
enumerable, printed list — the way `#print axioms` shrinks logical trust to the axiom list — and
turns three circularity shapes into deterministic build failures (Roy's point, 2026-09-23):

1. **Circular prediction.** `audit_datum c "tag"` marks a constant whose value was fixed by the datum
   `tag` (measured or back-solved). `audit_prediction t "tag"` marks a theorem presented as predicting
   `tag`. `#audit_circularity` walks each prediction's transitive constant closure (types and
   values, as `#print axioms` does) and errors if it reaches a datum with the same tag.
2. **Name ≠ object.** `audit_bridge d "claim" shadow P` registers a physical identification attached to
   declaration `d`, together with a *finite shadow* `P` — a decidable proposition that must hold if the
   identification is right. The command runs `decide` on `P` and on `¬P`: `WITNESSED`, `REFUTED`
   (build error) or `UNDECIDED`.
3. **Physics-free theorem.** `#audit_uses t c` replaces every occurrence of the constant `c` in the
   statement and the proof term of `t` by a free variable of the same type and re-typechecks. If that
   succeeds, `t` holds for *every* `c` — it says nothing about the physics `c` names — and the command
   errors. The check is pure type-checking (no search); a failure to re-typecheck is reported as
   `USES` (conservative: it never reports a false `PHYSICS-FREE`).

`#audit_report` prints the registered trusted-meaning base.
-/

open Lean Elab Command Meta

namespace SpectralPhysics.Audit

/-- One registry entry. `kind` ∈ {"datum", "prediction", "bridge"}. -/
structure Entry where
  kind : String
  decl : Name
  tag : String
  deriving Inhabited, BEq, Repr

initialize auditExt : SimplePersistentEnvExtension Entry (Array Entry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun as => as.foldl (· ++ ·) #[] }

/-- Transitive closure of constants reachable from `n` through types and values. -/
partial def closure (env : Environment) (n : Name) : NameSet :=
  (go n).run {} |>.2
where
  go (n : Name) : StateM NameSet Unit := do
    if (← get).contains n then return
    modify (·.insert n)
    let some info := env.find? n | return
    for m in info.type.getUsedConstants do go m
    if let some v := info.value? (allowOpaque := true) then
      for m in v.getUsedConstants do go m

private def register (k : String) (n : Name) (tag : String) : CommandElabM Unit :=
  modifyEnv (auditExt.addEntry · { kind := k, decl := n, tag := tag })

/-- Is `n` defined in a library module (Mathlib, core, …) rather than in the framework? -/
def isLibConst (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some i =>
    let m := (env.header.moduleNames[i.toNat]!).toString
    ["Mathlib", "Init", "Lean", "Std", "Batteries", "Aesop", "Qq", "Plausible"].any (fun p => m.startsWith p)
  | none => false

syntax (name := auditDatum) "audit_datum " ident str : command
/-- Declare provenance for a literal-bearing input that is NOT fitted to a prediction target
(measured value, posit, convention). Kind "input"; it satisfies `#audit_literals`. -/
syntax (name := auditInput) "audit_input " ident str : command
syntax (name := auditPrediction) "audit_prediction " ident str : command
syntax (name := auditCircularity) "#audit_circularity" : command
syntax (name := auditUses) "#audit_uses " ident ident : command
syntax (name := auditBridge) "audit_bridge " ident str " shadow " term : command
syntax (name := auditReport) "#audit_report" : command

elab_rules : command
  | `(audit_datum $id:ident $s:str) => do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    register "datum" n s.getString
  | `(audit_input $id:ident $s:str) => do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    register "input" n s.getString
  | `(audit_prediction $id:ident $s:str) => do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    register "prediction" n s.getString

elab_rules : command
  | `(#audit_circularity) => do
    let env ← getEnv
    let es := auditExt.getState env
    let data := es.filter (·.kind == "datum")
    let mut bad : Array String := #[]
    for p in es.filter (·.kind == "prediction") do
      let cl := closure env p.decl
      for d in data do
        if d.tag == p.tag && cl.contains d.decl then
          bad := bad.push s!"CIRCULAR: prediction {p.decl} (\"{p.tag}\") depends on datum {d.decl}"
    if bad.isEmpty then
      logInfo m!"audit_circularity: {(es.filter (·.kind == "prediction")).size} prediction(s), no datum in its own ancestry"
    else
      throwError (String.intercalate "\n" bad.toList)

/-- `true` iff `thm` fails to re-typecheck with `c` abstracted, i.e. its proof uses `c`'s content. -/
def usesConst (thm c : Name) : MetaM Bool := do
  let info ← getConstInfo thm
  let some v := info.value? (allowOpaque := true)
    | throwError "{thm} has no value to audit"
  let cinfo ← getConstInfo c
  unless cinfo.levelParams.isEmpty do
    throwError "{c} is universe-polymorphic; not supported by this prototype"
  withLocalDeclD `x cinfo.type fun x => do
    let rep (e : Expr) : Expr := e.replace fun s => if s.isConstOf c then some x else none
    let ty' := rep info.type
    let v' := rep v
    try
      Meta.check v'
      let t ← inferType v'
      return !(← isDefEq t ty')
    catch _ => return true

elab_rules : command
  | `(#audit_uses $t:ident $c:ident) => do
    let tn ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo t
    let cn ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo c
    let uses ← liftTermElabM <| usesConst tn cn
    if uses then
      logInfo m!"audit_uses: {tn} USES {cn}"
    else
      throwError "PHYSICS-FREE: {tn} re-typechecks with {cn} replaced by an arbitrary value"

elab_rules : command
  | `(audit_bridge $d:ident $claim:str shadow $p:term) => do
    let dn ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
    let tryDecide (stx : Term) : CommandElabM Bool := liftTermElabM <| Term.withoutErrToSorry do
      try
        let e ← Term.elabTermAndSynthesize (← `((by decide : $stx))) none
        Term.synthesizeSyntheticMVarsNoPostponing
        let e ← instantiateMVars e
        return !e.hasSyntheticSorry && !e.hasMVar
      catch _ => return false
    let status ←
      if ← tryDecide p then pure "WITNESSED"
      else if ← tryDecide (← `(¬ $p)) then pure "REFUTED"
      else pure "UNDECIDED"
    register "bridge" dn s!"{status}: {claim.getString}"
    if status == "REFUTED" then
      throwError "BRIDGE REFUTED: {dn} — \"{claim.getString}\": its finite shadow is false (kernel-checked by decide)"
    else
      logInfo m!"audit_bridge: {dn} {status}"

elab_rules : command
  | `(#audit_report) => do
    let es := auditExt.getState (← getEnv)
    let line (e : Entry) := s!"  [{e.kind}] {e.decl} : {e.tag}"
    logInfo m!"trusted-meaning base ({es.size} entries):\n{String.intercalate "\n" (es.toList.map line)}"


/-- Framework (non-library) definitions, opaques and axioms reachable from `thm`'s statement and proof. -/
def frameworkConsts (env : Environment) (thm : Name) : Array Name := Id.run do
  let some info := env.find? thm | return #[]
  let used := info.type.getUsedConstants ++ ((info.value? (allowOpaque := true)).map (·.getUsedConstants) |>.getD #[])
  let isLib (n : Name) : Bool :=
    match env.getModuleIdxFor? n with
    | some i =>
      let m := (env.header.moduleNames[i.toNat]!).toString
      m.startsWith "Mathlib" || m.startsWith "Init" || m.startsWith "Lean" || m.startsWith "Std" || m.startsWith "Batteries" || m.startsWith "Aesop" || m.startsWith "Qq" || m.startsWith "Plausible"
    | none => false
  let mut out : Array Name := #[]
  for n in used do
    if out.contains n || n == thm || isLib n then continue
    match env.find? n with
    | some (.defnInfo d) => if d.levelParams.isEmpty then out := out.push n
    | some (.opaqueInfo d) => if d.levelParams.isEmpty then out := out.push n
    | some (.axiomInfo d) => if d.levelParams.isEmpty then out := out.push n
    | _ => pure ()
  return out

/-- `true` iff `thm` re-typechecks with ALL of `cs` abstracted (physics-free with respect to them). -/
def freeOfAll (thm : Name) (cs : Array Name) : MetaM Bool := do
  let info ← getConstInfo thm
  let some v := info.value? (allowOpaque := true) | return false
  let rec go (i : Nat) (ty v : Expr) : MetaM Bool := do
    if h : i < cs.size then
      let c := cs[i]
      let cty ← instantiateMVars (← getConstInfo c).type
      -- earlier abstractions already applied to ty/v; types of later constants keep the originals (conservative)
      withLocalDeclD (Name.mkSimple s!"x{i}") cty fun x => do
        let rep (e : Expr) : Expr := e.replace fun s => if s.isConstOf c then some x else none
        go (i + 1) (rep ty) (rep v)
    else
      try
        Meta.check v
        isDefEq (← inferType v) ty
      catch _ => return false
  go 0 info.type v

syntax (name := auditFree) "#audit_free " ident+ : command
syntax (name := auditLiterals) "#audit_literals " ident+ : command

/-- Framework definitions in `thm`'s closure whose value is a hard-coded number and whose
provenance is not declared in the registry (any kind). Closes literal laundering: a number copied
from elsewhere carries no dependency edge, so the closure walk alone cannot see where it came from. -/
def undeclaredLiterals (env : Environment) (thm : Name) : Array Name := Id.run do
  let declared : NameSet := (auditExt.getState env).foldl (fun acc e => acc.insert e.decl) {}
  let mut out := #[]
  for n in (closure env thm).toList do
    if isLibConst env n || declared.contains n then continue
    if let some (.defnInfo d) := env.find? n then
      -- hard-coded number: no framework constant in the value, and a decimal or a numeral ≥ 3
      -- (catches `0.0609` and `609 / 10000` alike)
      -- only framework defs / opaques / axioms count; shared auxiliary proofs (`_proof_k`) do not
      let isFrameworkObj (m : Name) : Bool :=
        !isLibConst env m && !m.isInternal &&
          (match env.find? m with
           | some (.defnInfo _) | some (.opaqueInfo _) | some (.axiomInfo _) => true
           | _ => false)
      let noFramework := !(d.value.getUsedConstants.any isFrameworkObj)
      let numeral := d.value.find? fun e =>
        e.isAppOf ``OfScientific.ofScientific || (match e with | .lit (.natVal k) => k ≥ 3 | _ => false)
      if noFramework && numeral.isSome then out := out.push n
  return out.qsort (·.toString < ·.toString)

elab_rules : command
  | `(#audit_free $ts:ident*) => do
    let env ← getEnv
    let mut lines : Array String := #[]
    for t in ts do
      let tn ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo t
      let cs := frameworkConsts env tn
      let free ← liftTermElabM <| freeOfAll tn cs
      let concTrue ← liftTermElabM do
        forallTelescope (← getConstInfo tn).type fun _ b => return b.isConstOf ``True
      let verdict :=
        if cs.isEmpty then (if concTrue then "VACUOUS (conclusion True)" else "NO-FRAMEWORK-CONSTANTS")
        else if free then "PHYSICS-FREE" else "USES"
      lines := lines.push s!"{verdict}  {tn}  [{cs.size} framework const(s): {String.intercalate ", " (cs.toList.map toString)}]"
    logInfo m!"{String.intercalate "\n" lines.toList}"

elab_rules : command
  | `(#audit_literals $ts:ident*) => do
    let env ← getEnv
    let mut bad : Array String := #[]
    for t in ts do
      let tn ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo t
      let u := undeclaredLiterals env tn
      unless u.isEmpty do
        bad := bad.push s!"UNDECLARED-LITERAL: {tn} depends on {String.intercalate ", " (u.toList.map toString)}"
    if bad.isEmpty then logInfo m!"audit_literals: every hard-coded number in the closure has declared provenance"
    else throwError (String.intercalate "\n" bad.toList)

end SpectralPhysics.Audit
