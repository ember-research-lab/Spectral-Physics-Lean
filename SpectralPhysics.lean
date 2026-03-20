-- Spectral Physics: Lean Formalization
-- The Algebraic Spine — From Three Axioms to Five Predictions
--
-- Ember Research Lab, 2026
-- Aaron Ben-Shalom
--
-- This project formalizes the derivation chain:
--   Axioms 1-3 → Laplacian uniqueness → Division algebra forcing
--   → A_obs = ℂ ⊗ ℍ ⊗ 𝕆 → τ = 1/(2+φ) → {α_s, λ_Cabibbo, T_c/v, θ₁₃, δ_CP}

import SpectralPhysics.Algebra.CayleyDickson
import SpectralPhysics.Algebra.Hurwitz
import SpectralPhysics.Axioms.RelationalStructure
import SpectralPhysics.Axioms.Laplacian
import SpectralPhysics.Axioms.Composition
import SpectralPhysics.Algebra.Forcing
import SpectralPhysics.Triad.SelfReferentialTriad
import SpectralPhysics.Triad.GoldenRatio
import SpectralPhysics.Predictions.StrongCoupling
import SpectralPhysics.Predictions.CabibboAngle
import SpectralPhysics.Predictions.ElectroweakRatio
