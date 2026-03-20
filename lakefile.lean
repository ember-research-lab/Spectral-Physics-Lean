import Lake
open Lake DSL

package spectralPhysics where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib SpectralPhysics

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"
