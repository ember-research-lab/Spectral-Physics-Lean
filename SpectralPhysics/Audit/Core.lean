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

syntax (name := auditDatum) "audit_datum " ident str : command
syntax (name := auditPrediction) "audit_prediction " ident str : command
syntax (name := auditCircularity) "#audit_circularity" : command
syntax (name := auditUses) "#audit_uses " ident ident : command
syntax (name := auditBridge) "audit_bridge " ident str " shadow " term : command
syntax (name := auditReport) "#audit_report" : command

elab_rules : command
  | `(audit_datum $id:ident $s:str) => do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    register "datum" n s.getString
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

end SpectralPhysics.Audit
