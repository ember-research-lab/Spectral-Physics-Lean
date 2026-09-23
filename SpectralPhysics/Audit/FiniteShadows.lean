/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/

/-!
# Audit.FiniteShadows — kernel-decidable finite shadows of operator identifications

The smallest complex with a 2-cell: the clique complex of `K₃` (vertices `0 1 2`, edges `01 02 12`,
one triangle `012`). Integer matrices are lists of rows so that `decide` evaluates them in the kernel
(no `native_decide`, so no extra axioms).

`D = d + d*` on `C⁰ ⊕ C¹` (the "graph Dirac" of the 2026-09-22 adoption) squares to `L₀ ⊕ L₁^down`,
not to `L₀ ⊕ L₁^Hodge`; the difference is the up-Laplacian `d₁ᵀd₁`, which needs the 2-cell.
Tier 0 (2026-09-22 counterexample, `~/ember-tasks/graph-dirac-square-check-2026-09-22/`).
-/

namespace SpectralPhysics.Audit.Shadow

/-- An integer matrix as a list of rows. -/
abbrev Mat := List (List Int)

def transpose : Mat → Mat
  | [] => []
  | r :: rs => (List.range r.length).map fun j => (r :: rs).map fun row => row.getD j 0

def dot (u v : List Int) : Int := (List.zipWith (· * ·) u v).foldl (· + ·) 0

def mul (a b : Mat) : Mat := a.map fun row => (transpose b).map (dot row)

def add (a b : Mat) : Mat := List.zipWith (List.zipWith (· + ·)) a b

def zeros (r c : Nat) : Mat := List.replicate r (List.replicate c 0)

/-- Block-diagonal `a ⊕ b` (square blocks). -/
def blockDiag (a b : Mat) : Mat :=
  a.map (· ++ List.replicate b.length 0) ++ b.map (List.replicate a.length 0 ++ ·)

/-- `[[0, bᵀ], [b, 0]]` for `b : C⁰ → C¹` (rows = edges, columns = vertices). -/
def offDiag (b : Mat) : Mat :=
  let nv := (b.headD []).length
  let ne := b.length
  (transpose b).map (List.replicate nv 0 ++ ·) ++ b.map (· ++ List.replicate ne 0)

/-- Coboundary `d₀ : C⁰ → C¹` of `K₃`, edges ordered `01, 02, 12`. -/
def d0 : Mat := [[-1, 1, 0], [-1, 0, 1], [0, -1, 1]]

/-- Coboundary `d₁ : C¹ → C²`: `(d₁ω)(012) = ω(12) − ω(02) + ω(01)`. -/
def d1 : Mat := [[1, -1, 1]]

/-- "Graph Dirac" on vertices ⊕ edges. -/
def D : Mat := offDiag d0

def L0 : Mat := mul (transpose d0) d0
def L1down : Mat := mul d0 (transpose d0)
def L1hodge : Mat := add L1down (mul (transpose d1) d1)

/-- Sanity: `d₁ d₀ = 0`, so this is a cochain complex. -/
theorem d_squared_zero : mul d1 d0 = [[0, 0, 0]] := by decide

/-- The correct identity (Tier 0): `(d + d*)² = L₀ ⊕ L₁^down`. -/
theorem graphDirac_square_eq_down : mul D D = blockDiag L0 L1down := by decide

/-- The 2026-09-22 identification's finite shadow is false: `(d + d*)² ≠ L₀ ⊕ L₁^Hodge`. -/
theorem graphDirac_square_ne_hodge : mul D D ≠ blockDiag L0 L1hodge := by decide

end SpectralPhysics.Audit.Shadow
