import SpectralPhysics
/-! Census — `#print axioms` for every theorem/axiom in `SpectralPhysics.*`.

For each declaration (private ones included) runs `Lean.collectAxioms`, keeps the
non-standard axioms (anything but propext / Classical.choice / Quot.sound), and adds
mechanical shell flags:
  * `TRUE_CONCL`        — conclusion (under ∀/→) is `True` or has a `True` conjunct
  * `DECOUPLED_WITNESS` — `∃ x, A ∧ B` where `B` ignores `x` and `A` mentions only `x`
  * `PROOF_TRIVIAL`     — proof term is a bare `rfl` / `trivial`
Output: TSV on stdout. Driven by `scripts/census.py`; see scripts/README.md.
Origin: 2026-09-10 soundness census (validated against hostile controls). -/
open Lean Meta Elab Command

def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

partial def conclusion : Expr → Expr
  | .forallE _ _ b _ => conclusion b
  | .mdata _ e => conclusion e
  | e => e

partial def hasTrueConjunct : Expr → Bool
  | e =>
    if e.isConstOf ``True then true
    else if e.isAppOfArity ``And 2 then hasTrueConjunct e.appFn!.appArg! || hasTrueConjunct e.appArg!
    else false

partial def conjuncts : Expr → List Expr
  | e => if e.isAppOfArity ``And 2 then conjuncts e.appFn!.appArg! ++ conjuncts e.appArg! else [e]

/-- `∃ x, A ∧ B …` where some conjunct mentions `x` and no other bound/free var
(pure constraint on the witness) and every OTHER conjunct ignores `x`. -/
partial def decoupledWitness : Expr → Bool
  | .forallE _ _ b _ => decoupledWitness b
  | .mdata _ e => decoupledWitness e
  | e =>
    if e.isAppOfArity ``Exists 2 then
      match e.appArg! with
      | .lam _ _ body _ =>
        let cs := conjuncts body
        cs.length ≥ 2 &&
          cs.any (fun c => c.hasLooseBVar 0 && c.looseBVarRange ≤ 1 && !c.hasFVar) &&
          cs.all (fun c => (c.hasLooseBVar 0 && c.looseBVarRange ≤ 1) || !c.hasLooseBVar 0) &&
          cs.any (fun c => !c.hasLooseBVar 0)
      | _ => false
    else false

/-- Proof term (under λ) is a bare `rfl`/`Iff.rfl`/`True.intro`/`trivial`. -/
partial def trivialProof : Expr → Bool
  | .lam _ _ b _ => trivialProof b
  | .mdata _ e => trivialProof e
  | e => [``Eq.refl, ``rfl, ``Iff.refl, ``Iff.rfl, ``True.intro, ``trivial, ``HEq.refl].any
      (fun c => e.getAppFn.isConstOf c)

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mods := env.header.moduleNames
  for i in [:mods.size] do
    let m := mods[i]!
    unless (`SpectralPhysics).isPrefixOf m do continue
    IO.println s!"MODULE\t{m}"
    for n in env.header.moduleData[i]!.constNames do
      if n.isInternalDetail && !isPrivateName n then continue
      let some ci := env.find? n | continue
      let kind := match ci with
        | .thmInfo _ => "thm" | .axiomInfo _ => "axiom" | _ => "other"
      unless kind == "thm" || kind == "axiom" do continue
      let axs := (← liftCoreM (Lean.collectAxioms n)).filter (fun a => !standardAxioms.contains a)
      let concl := conclusion ci.type
      let flags := (if hasTrueConjunct concl then ["TRUE_CONCL"] else []) ++
        (if decoupledWitness ci.type then ["DECOUPLED_WITNESS"] else []) ++
        (if (ci.value?.map (fun v => trivialProof v)).getD false then ["PROOF_TRIVIAL"] else [])
      IO.println s!"{kind}\t{m}\t{n}\t{",".intercalate (axs.toList.map toString)}\t{",".intercalate flags}"
