import Lake
open Lake DSL

package spectralPhysics where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib SpectralPhysics

-- Hostile audit for the SelfModelDeficitUnconditional honesty pass
-- (2026-09-06 lane A). Built with the default `lake build` target.
@[default_target]
lean_lib SMDUHostile where
  srcDir := "test"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"
