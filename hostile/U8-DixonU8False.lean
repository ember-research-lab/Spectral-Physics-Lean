import SpectralPhysics.DixonOrderOne.Verdict
/-! Hostile instantiation for U8 (2026-08-18): the citation-axiom
`bochniak_sitarz_zerothOrder_reduction : (∃ D, OrderOne D LeftMult RightMult) → ZerothOrder LeftMult RightMult`
quantifies over an unconstrained `D`. The zero map satisfies OrderOne vacuously, so the axiom
forces ZerothOrder, which `not_zerothOrder_canonical_dixon` refutes ⇒ False. -/
namespace SpectralPhysics.DixonOrderOne
open CayleyDickson

theorem zero_map_orderOne : OrderOne (fun _ => (0 : OctonionFactor)) LeftMult RightMult := by
  intro a b
  funext x
  simp [commutator_apply, LeftMult, RightMult]

theorem u8_false : False :=
  not_zerothOrder_canonical_dixon
    (bochniak_sitarz_zerothOrder_reduction ⟨_, zero_map_orderOne⟩)

#print axioms u8_false
end SpectralPhysics.DixonOrderOne
