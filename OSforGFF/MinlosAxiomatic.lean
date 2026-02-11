/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/

import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Analysis.LocallyConvex.Basic
import Mathlib.Topology.Algebra.Module.WeakDual

import OSforGFF.Minlos
import OSforGFF.NuclearSpace

/-!
# Minlos theorem (axiomatic) and Gaussian measure construction

This module contains the *axiomatic* Minlos theorem used by the current GFF construction.
The non-axiomatic core lemmas (Gaussian characteristic functional and positive-definiteness
infrastructure) are in `OSforGFF/Minlos.lean`.

**Axiom contained here:**
`minlos_theorem`.
-/

open Complex MeasureTheory
open scoped BigOperators

noncomputable section

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

-- We need a measurable space structure on the weak dual
instance : MeasurableSpace (WeakDual ℝ E) := borel _

/-- **Minlos Theorem** (existence and uniqueness): On a nuclear locally convex space `E`,
    a continuous, positive definite, normalized functional `Φ : E → ℂ` is the characteristic
    functional of a unique probability measure `μ` on `WeakDual ℝ E`. -/
axiom minlos_theorem
  [NuclearSpace E]
  (Φ : E → ℂ)
  (h_continuous : Continuous Φ)
  (h_positive_definite : IsPositiveDefinite Φ)
  (h_normalized : Φ 0 = 1) :
  ∃! μ : ProbabilityMeasure (WeakDual ℝ E),
    ∀ f : E, Φ f = ∫ ω, Complex.exp (I * (ω f)) ∂μ.toMeasure

/-- Derived uniqueness: two probability measures whose characteristic functionals both
    equal a continuous, positive definite, normalized `Φ` must be equal. -/
theorem minlos_uniqueness
  [NuclearSpace E]
  {Φ : E → ℂ} (hΦ_cont : Continuous Φ)
  (hΦ_pd : IsPositiveDefinite Φ) (hΦ_norm : Φ 0 = 1)
  {μ₁ μ₂ : ProbabilityMeasure (WeakDual ℝ E)}
  (h₁ : ∀ f : E, ∫ ω, Complex.exp (I * (ω f)) ∂μ₁.toMeasure = Φ f)
  (h₂ : ∀ f : E, ∫ ω, Complex.exp (I * (ω f)) ∂μ₂.toMeasure = Φ f) :
  μ₁ = μ₂ := by
  obtain ⟨μ₀, _, huniq⟩ := minlos_theorem (E := E) Φ hΦ_cont hΦ_pd hΦ_norm
  exact (huniq μ₁ (fun f => (h₁ f).symm)).trans (huniq μ₂ (fun f => (h₂ f).symm)).symm

/-! ## Gaussian specialization -/

/-- Application of Minlos theorem to Gaussian measures.

If the covariance form can be realized as a squared norm via a linear embedding `T` into
a real inner product space `H`, then the Gaussian characteristic functional
`Φ(f) = exp(-½⟨f, Cf⟩)` satisfies the Minlos hypotheses. -/
theorem minlos_gaussian_construction
  [NuclearSpace E]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  (T : E →ₗ[ℝ] H)
  (covariance_form : E → E → ℝ)
  (h_eq : ∀ f, covariance_form f f = (‖T f‖^2 : ℝ))
  (h_zero : covariance_form 0 0 = 0)
  (h_continuous : Continuous (fun f => covariance_form f f))
  : ∃ μ : ProbabilityMeasure (WeakDual ℝ E),
    (∀ f : E, gaussian_characteristic_functional covariance_form f =
              ∫ ω, Complex.exp (I * (ω f)) ∂μ.toMeasure) := by
  -- Prove the three Minlos hypotheses for the Gaussian CF
  have h_cf_cont : Continuous (gaussian_characteristic_functional covariance_form) := by
    exact continuous_exp.comp (continuous_const.mul (continuous_ofReal.comp h_continuous))
  have h_cf_pd := gaussian_positive_definite_via_embedding T covariance_form h_eq
  have h_cf_norm : gaussian_characteristic_functional covariance_form 0 = 1 := by
    simp [gaussian_characteristic_functional, h_zero]
  -- Extract existence from `∃!`
  obtain ⟨μ, hchar, _⟩ := minlos_theorem
    (E := E) (Φ := gaussian_characteristic_functional covariance_form)
    h_cf_cont h_cf_pd h_cf_norm
  exact ⟨μ, hchar⟩

/-- Convenience variant returning the characteristic identity with the integral on the left. -/
theorem gaussian_measure_characteristic_functional
  [NuclearSpace E]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  (T : E →ₗ[ℝ] H)
  (covariance_form : E → E → ℝ)
  (h_eq : ∀ f, covariance_form f f = (‖T f‖^2 : ℝ))
  (h_zero : covariance_form 0 0 = 0)
  (h_continuous : Continuous (fun f => covariance_form f f))
  : ∃ μ : ProbabilityMeasure (WeakDual ℝ E),
    (∀ f : E, ∫ ω, Complex.exp (I * (ω f)) ∂μ.toMeasure =
              gaussian_characteristic_functional covariance_form f) := by
  obtain ⟨μ, hchar⟩ := minlos_gaussian_construction (E := E) T covariance_form h_eq h_zero h_continuous
  exact ⟨μ, fun f => (hchar f).symm⟩

/-- Corollary for Gaussian measures: if the covariance form is invariant under `g`,
    then the Gaussian measure is invariant under the induced dual action (via uniqueness). -/
theorem gaussian_measure_symmetry
  [NuclearSpace E]
  (covariance_form : E → E → ℝ)
  (h_cf_cont : Continuous (gaussian_characteristic_functional covariance_form))
  (h_cf_pd : IsPositiveDefinite (gaussian_characteristic_functional covariance_form))
  (h_cf_norm : gaussian_characteristic_functional covariance_form 0 = 1)
  (μ : ProbabilityMeasure (WeakDual ℝ E))
  (h_char : ∀ f : E, ∫ ω, Complex.exp (I * (ω f)) ∂μ.toMeasure =
                     gaussian_characteristic_functional covariance_form f)
  (g : E →L[ℝ] E)
  (h_covar_symm : ∀ f : E, covariance_form (g f) (g f) = covariance_form f f)
  -- The pushforward measure under the dual action
  (μ_push : ProbabilityMeasure (WeakDual ℝ E))
  (h_push_char : ∀ f : E, ∫ ω, Complex.exp (I * (ω f)) ∂μ_push.toMeasure =
                          ∫ ω, Complex.exp (I * (ω (g f))) ∂μ.toMeasure)
  : μ_push = μ := by
  have h_Φ_symm : ∀ f, gaussian_characteristic_functional covariance_form (g f) =
                       gaussian_characteristic_functional covariance_form f := by
    intro f
    simp [gaussian_characteristic_functional, h_covar_symm]
  exact minlos_uniqueness (E := E) h_cf_cont h_cf_pd h_cf_norm
    (fun f => by rw [h_push_char, h_char (g f), h_Φ_symm]) h_char

