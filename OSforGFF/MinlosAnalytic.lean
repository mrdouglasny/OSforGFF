/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/

import Mathlib.Data.Complex.Basic
--import Mathlib.Topology.Algebra.Module.Complex
import Mathlib.Analysis.LocallyConvex.Basic
import Mathlib.Topology.Algebra.Module.WeakDual
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Constructions
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

import OSforGFF.Basic
import OSforGFF.Minlos
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Minlos Analyticity — Symmetry and Moments for Gaussian Measures

This file provides infrastructure for Gaussian measures constructed via Minlos' theorem:
- `CovarianceForm`: Real symmetric bilinear form for covariance
- `negMap`, `integral_neg_invariance`: Symmetry under sign flip (uses Minlos uniqueness)
- `moment_zero_from_realCF`: Zero mean from characteristic functional symmetry
-/

open Classical
open TopologicalSpace MeasureTheory Complex Filter

/-! ## Contents

This file provides infrastructure for Gaussian measures via Minlos.
This file contains no axioms (axioms are only in `Minlos.lean`, `NuclearSpace.lean`, `OS0_GFF.lean`).
-/

noncomputable section

namespace MinlosAnalytic

-- Ensure FieldConfiguration is a BorelSpace since it uses the borel measurable space
instance : BorelSpace FieldConfiguration := ⟨rfl⟩

/-- A real symmetric, positive semidefinite covariance form on real test functions,
    together with a proof that the associated Gaussian characteristic functional
    exp(-½Q(f,f)) is positive definite. -/
structure CovarianceForm where
  Q : TestFunction → TestFunction → ℝ
  symm : ∀ f g, Q f g = Q g f
  psd  : ∀ f, 0 ≤ Q f f
  cont_diag : Continuous fun f => Q f f
  add_left : ∀ f₁ f₂ g, Q (f₁ + f₂) g = Q f₁ g + Q f₂ g
  smul_left : ∀ (c : ℝ) f g, Q (c • f) g = c * Q f g
  gaussian_cf_pd : IsPositiveDefinite
    (fun f : TestFunction => Complex.exp (-(1/2 : ℂ) * (Q f f : ℂ)))

/-- The negation map on field configurations: T(ω) = -ω -/
def negMap : FieldConfiguration → FieldConfiguration := fun ω => -ω

/-- The negation map is measurable -/
lemma negMap_measurable : Measurable negMap := by
  -- The negation map is continuous on WeakDual, hence measurable
  -- WeakDual is a topological vector space and negation is continuous
  apply Continuous.measurable
  -- negMap is the same as the continuous linear map x ↦ -x
  exact continuous_neg

/-- Symmetry under global sign flip induced by the real Gaussian CF.
    Note: Requires NuclearSpace instance for Minlos uniqueness theorem. -/
lemma integral_neg_invariance
  [NuclearSpace TestFunction]
  (C : CovarianceForm) (μ : ProbabilityMeasure FieldConfiguration)
  (h_realCF : ∀ f : TestFunction,
     ∫ ω, Complex.exp (Complex.I * (ω f)) ∂μ.toMeasure
       = Complex.exp (-(1/2 : ℂ) * (C.Q f f))) :
  ∀ (f : FieldConfiguration → ℂ), Integrable f μ.toMeasure →
    ∫ ω, f ω ∂μ.toMeasure = ∫ ω, f (-ω) ∂μ.toMeasure := by
  intro f hInt
  classical
  -- Plan:
  -- 1) Consider T(ω) = -ω and the pushforward μneg := μ ◦ T^{-1}.
  -- 2) Show μneg has the same characteristic functional as μ using h_realCF and (-ω) a = -ω a.
  -- 3) Conclude μneg = μ by Minlos uniqueness.
  -- 4) Use the change-of-variables for map to get the desired integral identity.

  -- Step 1: Define the pushforward measure
  let μneg := μ.toMeasure.map negMap
  have hμneg_prob : IsProbabilityMeasure μneg := by
    exact Measure.isProbabilityMeasure_map (Measurable.aemeasurable negMap_measurable)

  -- Step 2: Show characteristic functionals are equal
  have hCF_equal : ∀ g : TestFunction,
      ∫ ω, Complex.exp (Complex.I * (distributionPairing ω g)) ∂μneg
        = ∫ ω, Complex.exp (Complex.I * (distributionPairing ω g)) ∂μ.toMeasure := by
    intro g
    -- Use the change of variables formula for the map
    have h_aestrongly_measurable : AEStronglyMeasurable (fun ω => Complex.exp (Complex.I * (distributionPairing ω g))) μneg := by
      -- Inner map: ω ↦ distributionPairing ω g is measurable via continuous linear map
      have h_inner_meas : Measurable (fun ω : FieldConfiguration => distributionPairing ω g) := by
        simpa [distributionPairingCLM_apply] using (distributionPairingCLM g).continuous.measurable
      -- Outer map: x ↦ exp(I * x) is continuous hence measurable
      have h_cont_mulI : Continuous (fun x : ℝ => (Complex.I : ℂ) * (x : ℂ)) :=
        continuous_const.mul continuous_ofReal
      have h_cont_exp : Continuous (fun z : ℂ => Complex.exp z) := Complex.continuous_exp
      have h_outer_meas : Measurable (fun x : ℝ => Complex.exp ((Complex.I : ℂ) * (x : ℂ))) :=
        (h_cont_exp.comp h_cont_mulI).measurable
      -- Composition is measurable, hence AEStronglyMeasurable
      exact (h_outer_meas.comp h_inner_meas).aestronglyMeasurable
    rw [integral_map (Measurable.aemeasurable negMap_measurable) h_aestrongly_measurable]
    -- The integrand becomes: exp(I * ((-ω) g)) = exp(I * (-(ω g))) = exp(-I * (ω g))
    have h_neg_pairing : (fun ω => Complex.exp (Complex.I * (distributionPairing (negMap ω) g))) =
                         (fun ω => Complex.exp (Complex.I * (distributionPairing (-ω) g))) := by
      simp [negMap]
    rw [h_neg_pairing]
    -- Step 1: (-ω) g = -(ω g) by linearity (negation is scalar multiplication by -1)
    have h_neg_eq : ∀ ω : FieldConfiguration, distributionPairing (-ω) g = -distributionPairing ω g := by
      intro ω
      have h_neg_smul : -ω = (-1 : ℝ) • ω := (neg_one_smul ℝ ω).symm
      rw [h_neg_smul, distributionPairing_smul]
      ring
    -- Step 2: Rewrite the LHS using h_neg_eq
    have h_lhs_eq : (fun ω => Complex.exp (Complex.I * (distributionPairing (-ω) g : ℂ))) =
                    (fun ω => Complex.exp (-(Complex.I * (distributionPairing ω g : ℂ)))) := by
      funext ω
      rw [h_neg_eq]
      simp only [ofReal_neg, mul_neg]
    conv_lhs => rw [h_lhs_eq]
    -- Step 3: exp(-I*x) = conj(exp(I*x)) for real x
    have h_exp_neg_conj : ∀ x : ℝ, Complex.exp (-(Complex.I * (x : ℂ))) = starRingEnd ℂ (Complex.exp (Complex.I * (x : ℂ))) := by
      intro x
      rw [← Complex.exp_conj]
      congr 1
      simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
      ring
    have h_integrand_conj : (fun ω => Complex.exp (-(Complex.I * (distributionPairing ω g : ℂ)))) =
                            (fun ω => starRingEnd ℂ (Complex.exp (Complex.I * (distributionPairing ω g : ℂ)))) := by
      funext ω
      exact h_exp_neg_conj (distributionPairing ω g)
    conv_lhs => rw [h_integrand_conj]
    -- Step 4: Use integral_conj and that the CF is real
    -- The integral ∫ conj(f) = conj(∫ f), and the CF value is real, so conj(CF) = CF
    rw [integral_conj]
    -- The CF h_realCF says ∫ exp(I*ωg) = exp(-½Q(g,g)) which is real
    -- Since exp of a real number is real, conj(exp(-½Q(g,g))) = exp(-½Q(g,g))
    -- First unfold distributionPairing to match h_realCF
    simp only [distributionPairing] at *
    rw [h_realCF g]
    -- exp(-½Q(g,g)) is exp of a real, so conj = self
    have h_CF_is_real : (Complex.exp (-(1/2 : ℂ) * (C.Q g g : ℂ))).im = 0 := by
      -- Rewrite as exp of a real cast to ℂ
      have h_eq : (-(1/2 : ℂ) * (C.Q g g : ℂ)) = ((-(1/2 : ℝ) * C.Q g g : ℝ) : ℂ) := by
        push_cast
        ring
      rw [h_eq]
      exact Complex.exp_ofReal_im (-(1/2) * C.Q g g)
    rw [Complex.conj_eq_iff_im.mpr h_CF_is_real]

  -- Step 3: Apply uniqueness of measures (Minlos theorem)
  -- Both μneg and μ have the Gaussian CF exp(-½Q(f,f)).
  let μneg_prob : ProbabilityMeasure FieldConfiguration := ⟨μneg, hμneg_prob⟩
  -- Derive continuity and normalization of the Gaussian CF from CovarianceForm
  have h_cf_cont : Continuous
      (fun f : TestFunction => Complex.exp (-(1/2 : ℂ) * (C.Q f f : ℂ))) :=
    continuous_exp.comp (continuous_const.mul (continuous_ofReal.comp C.cont_diag))
  have h_cf_norm : (fun f : TestFunction =>
      Complex.exp (-(1/2 : ℂ) * (C.Q f f : ℂ))) 0 = 1 := by
    simp [show C.Q 0 0 = 0 from by simpa using C.smul_left 0 0 0]
  have hμeq_prob : μneg_prob = μ := by
    simp only [distributionPairing] at hCF_equal h_realCF
    exact minlos_uniqueness h_cf_cont C.gaussian_cf_pd h_cf_norm
      (fun g => (hCF_equal g).trans (h_realCF g)) h_realCF
  have hμeq : μneg = μ.toMeasure := by
    have h := congrArg ProbabilityMeasure.toMeasure hμeq_prob
    exact h

  -- Step 4: Use the equality of measures to get the integral identity
  -- Since μneg = μ.toMeasure, we can use change of variables on the original measure
  have hf_aestrongly_measurable : AEStronglyMeasurable f μneg := by
    -- Since μneg = μ.toMeasure, AEStronglyMeasurable on μneg is the same as on μ.toMeasure
    rw [hμeq]
    exact hInt.aestronglyMeasurable
  -- The change of variables formula gives us:
  -- ∫ f dμ = ∫ f d(μ.map negMap⁻¹) = ∫ (f ∘ negMap) dμ = ∫ f(-ω) dμ
  have h_cov : ∫ ω, f ω ∂μneg = ∫ ω, f (negMap ω) ∂μ.toMeasure := by
    exact integral_map (Measurable.aemeasurable negMap_measurable) hf_aestrongly_measurable
  rw [hμeq] at h_cov
  rw [h_cov]
  simp [negMap]

/-- Zero mean from the real Gaussian characteristic functional, via symmetry and L¹. -/
lemma moment_zero_from_realCF
  [NuclearSpace TestFunction]
  (C : CovarianceForm) (μ : ProbabilityMeasure FieldConfiguration)
  (h_realCF : ∀ f : TestFunction,
     ∫ ω, Complex.exp (Complex.I * (ω f)) ∂μ.toMeasure
       = Complex.exp (-(1/2 : ℂ) * (C.Q f f)))
  (a : TestFunction)
  (hInt1 : Integrable (fun ω => (ω a : ℂ)) μ.toMeasure) :
  ∫ ω, (ω a : ℂ) ∂μ.toMeasure = 0 := by
  classical
  -- Symmetry: ∫ f(ω) = ∫ f(-ω)
  have hInv := integral_neg_invariance C μ h_realCF (fun ω => (ω a : ℂ)) hInt1
  -- Flip integrand: ((-ω) a : ℂ) = - (ω a : ℂ)
  have hflip : (fun ω : FieldConfiguration => ((-ω) a : ℂ)) = (fun ω => - (ω a : ℂ)) := by
    funext ω
    rw [ContinuousLinearMap.neg_apply]
    simp
  -- Hence ∫ X = ∫ -X = -∫ X
  have : ∫ ω, (ω a : ℂ) ∂μ.toMeasure = - ∫ ω, (ω a : ℂ) ∂μ.toMeasure := by
    simpa [hflip, integral_neg, hInt1] using hInv
  -- 2 · ∫ X = 0 ⇒ ∫ X = 0
  exact self_eq_neg.mp this

end MinlosAnalytic
