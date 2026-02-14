/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/

import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Distribution.TemperateGrowth
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Topology.Algebra.Module.WeakDual
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic
import Mathlib.Tactic.Positivity

import OSforGFF.Basic
import OSforGFF.Schwinger
import OSforGFF.GFFMconstruct
import OSforGFF.GFFIsGaussian
import OSforGFF.OS0_GFF
import OSforGFF.OS2_GFF
import OSforGFF.ComplexTestFunction
import OSforGFF.TimeTranslation
import OSforGFF.CovarianceMomentum
import OSforGFF.OS_Axioms
import OSforGFF.L2TimeIntegral
import OSforGFF.SchwartzTranslationDecay
import OSforGFF.OS4_MGF
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.MeasureTheory.Group.Measure

/-!
# OS4 Ergodicity Axiom for Gaussian Free Field

This file proves that the Gaussian Free Field satisfies the OS4 (Ergodicity) axiom,
assuming the OS4_PolynomialClustering property with decay exponent α = 6.

## Main Results

* `OS4_PolynomialClustering_implies_OS4_Ergodicity`: The main theorem showing that
  polynomial clustering with α=6 implies ergodicity for the GFF.

## Strategy Overview

The proof proceeds through a sequence of reductions:
- OS4'' (Polynomial Clustering with α=6) ⟹ OS4' (Ergodicity on generating functions)
- OS4' ⟹ OS4 (Full ergodicity on linear combinations)

The key insight is that polynomial decay of correlations at large time separations
implies ergodicity via variance bounds.
-/

open MeasureTheory Real
open TopologicalSpace
open scoped BigOperators

noncomputable section

namespace OS4_Ergodicity

open OS4infra

-- Re-export names that external files reference with OS4_Ergodicity. prefix
export OS4infra (
  timeTranslationDistribution_pairingℂ
  gff_generating_time_invariant
)

/-! ## OS4 Axiom Variants

We define intermediate formulations of OS4 that are easier to prove directly.
-/

/-- OS4' (Ergodicity on generating functions): For any f ∈ S(ℝ × ℝ³),
    lim_{t→∞} (1/t) ∫₀ᵗ e^{⟨T_s φ, f⟩} ds → 𝔼_μ[e^{⟨φ,f⟩}] in L²(μ_GFF)
-/
def OS4'_Ergodicity_generating (m : ℝ) [Fact (0 < m)] : Prop :=
  ∀ (f : TestFunctionℂ),
    let μ := (gaussianFreeField_free m).toMeasure
    Filter.Tendsto
      (fun T : ℝ =>
        ∫ ω, ‖(1 / T) * ∫ s in Set.Icc (0 : ℝ) T,
          Complex.exp (distributionPairingℂ_real (timeTranslationDistribution s ω) f)
          - ∫ ω', Complex.exp (distributionPairingℂ_real ω' f) ∂μ‖^2 ∂μ)
      Filter.atTop
      (nhds 0)

/-- OS4'' (Polynomial Clustering): This is exactly OS4_PolynomialClustering
    specialized to the GFF with decay exponent α = 6. -/
def OS4''_Clustering (m : ℝ) [Fact (0 < m)] : Prop :=
  OS4_PolynomialClustering (gaussianFreeField_free m) 6 (by norm_num)

/-! ## GFF Integrability Lemmas -/

/-- The GFF exponential is integrable with respect to the GFF measure. -/
lemma gff_exp_pairing_integrable (m : ℝ) [Fact (0 < m)] (f : TestFunctionℂ) :
    Integrable (fun ω => Complex.exp (distributionPairingℂ_real ω f))
      (gaussianFreeField_free m).toMeasure := by
  -- |exp(z)| = exp(Re z), so bound by exp(|Re z|)
  let f_re := (complex_testfunction_decompose f).1
  have h_int : Integrable (fun ω => Real.exp |ω f_re|) (gaussianFreeField_free m).toMeasure :=
    QFT.gff_exp_abs_pairing_integrable m f_re
  have h_dom : ∀ ω, ‖Complex.exp (distributionPairingℂ_real ω f)‖ ≤ ‖Real.exp |ω f_re|‖ := fun ω => by
    rw [Complex.norm_exp, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    -- (distributionPairingℂ_real ω f).re = ω f_re by definition
    have h_re : (distributionPairingℂ_real ω f).re = ω f_re := by
      simp only [distributionPairingℂ_real, Complex.add_re, Complex.ofReal_re,
        Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im]
      ring
    rw [h_re]
    exact Real.exp_le_exp.mpr (le_abs_self _)
  -- Use Integrable.mono: if g is integrable and ‖f‖ ≤ ‖g‖ a.e., then f is integrable
  refine h_int.mono ?_ (Filter.Eventually.of_forall h_dom)
  -- Need AEStronglyMeasurable for exp ∘ distributionPairingℂ_real
  exact (Complex.continuous_exp.comp (QFT.distributionPairingℂ_real_continuous f)).aestronglyMeasurable

/-- Time-translated complex exponential is in L² under the GFF measure.
    This follows from |exp(z)|² = exp(2 Re z) ≤ exp(2|Re z|) which is integrable.
    (Copied from OS4Ron.lean - needed for integrability proofs) -/
lemma gff_exp_time_translated_memLp_two (m : ℝ) [Fact (0 < m)] (s : ℝ) (f : TestFunctionℂ) :
    MemLp (fun ω : FieldConfiguration =>
        Complex.exp (distributionPairingℂ_real (timeTranslationDistribution s ω) f))
      2 (gaussianFreeField_free m).toMeasure := by
  let g := timeTranslationSchwartzℂ (-s) f
  have h_eq : (fun ω => Complex.exp (distributionPairingℂ_real (timeTranslationDistribution s ω) f))
      = (fun ω => Complex.exp (distributionPairingℂ_real ω g)) := by
    ext ω; rw [timeTranslationDistribution_pairingℂ]
  rw [h_eq]
  -- Need ∫ ‖exp(...)‖² < ∞, i.e., ∫ exp(2 Re(...)) < ∞
  have h_meas : AEStronglyMeasurable
      (fun ω : FieldConfiguration => Complex.exp (distributionPairingℂ_real ω g))
      (gaussianFreeField_free m).toMeasure := by
    apply Continuous.aestronglyMeasurable
    exact Complex.continuous_exp.comp (QFT.distributionPairingℂ_real_continuous g)
  -- The dominating function: exp(2|ω g_re|) is integrable
  have h_dom : Integrable (fun ω : FieldConfiguration =>
      Real.exp (2 * |ω (complex_testfunction_decompose g).1|))
      (gaussianFreeField_free m).toMeasure := by
    have h_L2 := QFT.gff_exp_abs_pairing_memLp m (complex_testfunction_decompose g).1 2 (by norm_num)
    rw [MeasureTheory.memLp_two_iff_integrable_sq_norm] at h_L2
    · convert h_L2 using 1
      ext ω
      have h_pos : 0 ≤ Real.exp |ω (complex_testfunction_decompose g).1| := Real.exp_nonneg _
      rw [Real.norm_eq_abs, abs_of_nonneg h_pos, sq, ← Real.exp_add]
      ring_nf
    · exact MemLp.aestronglyMeasurable h_L2
  -- The bound: ‖exp(z)‖² = exp(2 Re z) ≤ exp(2|Re z|)
  have h_sq_norm_bound : ∀ ω : FieldConfiguration,
      ‖Complex.exp (distributionPairingℂ_real ω g)‖^2 ≤
        Real.exp (2 * |ω (complex_testfunction_decompose g).1|) := fun ω => by
    have h_norm : ‖Complex.exp (distributionPairingℂ_real ω g)‖ =
        Real.exp (Complex.re (distributionPairingℂ_real ω g)) := by
      simpa using Complex.norm_exp (distributionPairingℂ_real ω g)
    have h_re : Complex.re (distributionPairingℂ_real ω g) =
        ω (complex_testfunction_decompose g).1 := by
      simp [distributionPairingℂ_real]
    rw [h_norm, h_re, sq, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h_le : ω (complex_testfunction_decompose g).1 ≤ |ω (complex_testfunction_decompose g).1| :=
      le_abs_self _
    linarith
  -- Conclude MemLp 2 via domination
  rw [MeasureTheory.memLp_two_iff_integrable_sq_norm h_meas]
  have h_sq_meas : AEStronglyMeasurable (fun ω => ‖Complex.exp (distributionPairingℂ_real ω g)‖^2)
      (gaussianFreeField_free m).toMeasure := h_meas.norm.pow 2
  apply h_dom.mono' h_sq_meas
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact h_sq_norm_bound ω

/-! ## GFF Time Translation Invariance -/

/-- Time translation commutes with pointwise conjugation. -/
lemma timeTranslationSchwartzℂ_conj_comm (t : ℝ) (f : TestFunctionℂ) :
    timeTranslationSchwartzℂ t (conjSchwartz f) = conjSchwartz (timeTranslationSchwartzℂ t f) := by
  ext x
  simp only [timeTranslationSchwartzℂ_apply, conjSchwartz_apply]

/-- The product exp(⟨ω, T_t g₁⟩) · conj(exp(⟨ω, T_t g₂⟩)) integral is time-shift invariant.
    This follows from the GFF characteristic function and covariance time-translation invariance. -/
lemma gff_exp_product_time_shift_invariant (m : ℝ) [Fact (0 < m)] (g₁ g₂ : TestFunctionℂ) (t : ℝ) :
    let μ := (gaussianFreeField_free m).toMeasure
    ∫ ω, Complex.exp (distributionPairingℂ_real ω (timeTranslationSchwartzℂ t g₁)) *
         starRingEnd ℂ (Complex.exp (distributionPairingℂ_real ω (timeTranslationSchwartzℂ t g₂))) ∂μ =
    ∫ ω, Complex.exp (distributionPairingℂ_real ω g₁) *
         starRingEnd ℂ (Complex.exp (distributionPairingℂ_real ω g₂)) ∂μ := by
  intro μ
  -- Rewrite conj(exp(z)) = exp(conj(z))
  simp_rw [(Complex.exp_conj _).symm]
  simp_rw [← Complex.exp_add]
  -- conj(⟨ω, g⟩) = ⟨ω, conjSchwartz g⟩
  simp_rw [distributionPairingℂ_real_conj]
  -- Time translation commutes with conjugation: rewrite RHS direction
  simp_rw [← timeTranslationSchwartzℂ_conj_comm t]
  -- ⟨ω, f⟩ + ⟨ω, g⟩ = ⟨ω, f + g⟩ by linearity
  have h_add : ∀ ω (f g : TestFunctionℂ),
      distributionPairingℂ_real ω f + distributionPairingℂ_real ω g =
      distributionPairingℂ_real ω (f + g) := fun ω f g => by
    have := pairing_linear_combo ω f g 1 1
    simp at this
    exact this.symm
  simp_rw [h_add]
  -- T_t f + T_t g = T_t(f + g)
  have h_T_add : ∀ (f g : TestFunctionℂ),
      timeTranslationSchwartzℂ t f + timeTranslationSchwartzℂ t g =
      timeTranslationSchwartzℂ t (f + g) := fun f g => by
    ext x; simp [timeTranslationSchwartzℂ_apply]
  simp_rw [h_T_add]
  -- Now both are ∫ exp(⟨ω, T_t h⟩) and ∫ exp(⟨ω, h⟩) for h = g₁ + conjSchwartz g₂
  exact gff_generating_time_invariant m t (g₁ + conjSchwartz g₂)

/-- The L² norm of A_s is constant in s by stationarity.
    Proof: Uses OS2 → gff_exp_product_time_shift_invariant → this result. -/
lemma gff_exp_L2_norm_constant (m : ℝ) [Fact (0 < m)] (f : TestFunctionℂ) (s : ℝ) :
    ∫ ω, ‖Complex.exp (distributionPairingℂ_real (timeTranslationDistribution s ω) f)‖^2
      ∂(gaussianFreeField_free m).toMeasure =
    ∫ ω, ‖Complex.exp (distributionPairingℂ_real ω f)‖^2
      ∂(gaussianFreeField_free m).toMeasure := by
  let μ := (gaussianFreeField_free m).toMeasure
  -- Step 1: Time translation duality ⟨T_s ω, f⟩ = ⟨ω, T_{-s} f⟩
  have h_duality : ∀ ω, Complex.exp (distributionPairingℂ_real (timeTranslationDistribution s ω) f) =
      Complex.exp (distributionPairingℂ_real ω (timeTranslationSchwartzℂ (-s) f)) := fun ω =>
    congrArg Complex.exp (timeTranslationDistribution_pairingℂ s ω f)

  -- Step 2: Key identity z * conj(z) = ‖z‖² (both as real, and as ℂ via cast)
  have h_norm_sq_real : ∀ z : ℂ, z * starRingEnd ℂ z = (‖z‖^2 : ℝ) := fun z => by
    rw [RCLike.mul_conj]; push_cast; rfl

  -- Step 3: Product integral time-invariance (from OS2 via gff_exp_product_time_shift_invariant)
  have h_product_eq : ∫ ω, Complex.exp (distributionPairingℂ_real ω (timeTranslationSchwartzℂ (-s) f)) *
         starRingEnd ℂ (Complex.exp (distributionPairingℂ_real ω (timeTranslationSchwartzℂ (-s) f))) ∂μ =
      ∫ ω, Complex.exp (distributionPairingℂ_real ω f) *
         starRingEnd ℂ (Complex.exp (distributionPairingℂ_real ω f)) ∂μ :=
    gff_exp_product_time_shift_invariant m f f (-s)

  -- Step 4: Rewrite LHS using duality
  have h_lhs_eq : ∫ ω, ‖Complex.exp (distributionPairingℂ_real (timeTranslationDistribution s ω) f)‖^2 ∂μ =
      ∫ ω, ‖Complex.exp (distributionPairingℂ_real ω (timeTranslationSchwartzℂ (-s) f))‖^2 ∂μ := by
    congr 1

  rw [h_lhs_eq]

  -- Convert: ∫ ‖exp(⟨ω, g⟩)‖² = (∫ exp * conj(exp)).re
  have h_int_re_eq : ∀ g : TestFunctionℂ,
      ∫ ω, ‖Complex.exp (distributionPairingℂ_real ω g)‖^2 ∂μ =
      (∫ ω, Complex.exp (distributionPairingℂ_real ω g) *
            starRingEnd ℂ (Complex.exp (distributionPairingℂ_real ω g)) ∂μ).re := by
    intro g
    -- The integrand exp * conj(exp) = ↑(‖exp‖²) is real-valued
    have h_integrand_real : ∀ ω, (Complex.exp (distributionPairingℂ_real ω g) *
          starRingEnd ℂ (Complex.exp (distributionPairingℂ_real ω g))) =
        (‖Complex.exp (distributionPairingℂ_real ω g)‖^2 : ℝ) := fun ω => h_norm_sq_real _
    simp_rw [h_integrand_real]
    -- Goal: ∫ ‖exp‖² = (∫ ↑(‖exp‖²)).re
    -- Use integral_complex_ofReal: ∫ (f : ℂ) = ∫ f for real-valued f
    conv_rhs => arg 1; rw [integral_complex_ofReal]
    simp only [Complex.ofReal_re]

  rw [h_int_re_eq (timeTranslationSchwartzℂ (-s) f), h_int_re_eq f, h_product_eq]

/-- The time average (1/T)∫A_s ds is in L²(μ). -/
lemma time_average_memLp_two (m : ℝ) [Fact (0 < m)] (f : TestFunctionℂ) (T : ℝ) (hT : T > 0) :
    MemLp (fun ω => (1/T : ℂ) * ∫ s in Set.Icc (0 : ℝ) T,
        Complex.exp (distributionPairingℂ_real (timeTranslationDistribution s ω) f))
      2 (gaussianFreeField_free m).toMeasure := by
  let μ := (gaussianFreeField_free m).toMeasure
  let A := fun s ω => Complex.exp (distributionPairingℂ_real (timeTranslationDistribution s ω) f)
  -- A_s is in L² for each s
  have h_As_L2 : ∀ s, MemLp (A s) 2 μ := fun s => gff_exp_time_translated_memLp_two m s f
  -- Uniform L² norm via stationarity
  have h_uniform : ∀ s, ∫ ω, ‖A s ω‖^2 ∂μ = ∫ ω, ‖A 0 ω‖^2 ∂μ := fun s => by
    rw [gff_exp_L2_norm_constant m f s]
    -- A 0 ω = exp(pairing (T_0 ω) f) = exp(pairing ω f) since T_0 = id
    congr 1
    ext ω
    simp only [A, timeTranslationDistribution_zero]
  -- Joint measurability on [0,T] × Ω
  have h_joint_meas : AEStronglyMeasurable (Function.uncurry A)
      ((volume.restrict (Set.Icc 0 T)).prod μ) := by
    apply MeasureTheory.StronglyMeasurable.aestronglyMeasurable
    apply MeasureTheory.stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
    · intro ω
      simp only [A]
      exact Complex.continuous_exp.comp (continuous_distributionPairingℂ_timeTranslation ω f)
    · intro s
      have h_eq : (fun ω => Complex.exp (distributionPairingℂ_real (timeTranslationDistribution s ω) f)) =
          (fun ω => Complex.exp (distributionPairingℂ_real ω (timeTranslationSchwartzℂ (-s) f))) := by
        ext ω; rw [timeTranslationDistribution_pairingℂ]
      show StronglyMeasurable (fun ω => Complex.exp (distributionPairingℂ_real (timeTranslationDistribution s ω) f))
      rw [h_eq]
      exact (Complex.continuous_exp.comp (QFT.distributionPairingℂ_real_continuous _)).stronglyMeasurable
  -- Measurability of the time average
  have h_avg_meas : AEStronglyMeasurable
      (fun ω => (1/T : ℂ) * ∫ s in Set.Icc 0 T, A s ω) μ := by
    -- Swap measure order: (vol|[0,T]).prod μ → μ.prod (vol|[0,T])
    have h_swap : AEStronglyMeasurable (fun (p : FieldConfiguration × ℝ) => A p.2 p.1)
        (μ.prod (volume.restrict (Set.Icc 0 T))) :=
      AEStronglyMeasurable.prod_swap h_joint_meas
    have h_int_meas : AEStronglyMeasurable (fun ω => ∫ s in Set.Icc 0 T, A s ω) μ :=
      AEStronglyMeasurable.integral_prod_right' h_swap
    -- c * f = c • f for ℂ
    convert AEStronglyMeasurable.const_smul h_int_meas (1/T : ℂ)
  -- Apply the proved theorem from L2TimeIntegral
  exact OSforGFF.time_average_memLp_two μ A T hT h_As_L2 h_uniform h_joint_meas h_avg_meas

/-- The error term squared is integrable (for T > 0). -/
lemma gff_err_sq_integrable (m : ℝ) [Fact (0 < m)] (T : ℝ) (hT : T > 0) (f : TestFunctionℂ) :
    Integrable (fun ω =>
      ‖((1 : ℝ) / T) • (∫ s in Set.Icc (0 : ℝ) T,
          Complex.exp (distributionPairingℂ_real (timeTranslationDistribution s ω) f))
        - ∫ ω', Complex.exp (distributionPairingℂ_real ω' f) ∂(gaussianFreeField_free m).toMeasure‖^2)
      (gaussianFreeField_free m).toMeasure := by
  let μ := (gaussianFreeField_free m).toMeasure
  let A := fun s ω => Complex.exp (distributionPairingℂ_real (timeTranslationDistribution s ω) f)
  let EA := ∫ ω, A 0 ω ∂μ
  -- Step 1: Time average is in L²
  have h_avg_L2 : MemLp (fun ω => (1/T : ℂ) * ∫ s in Set.Icc (0 : ℝ) T, A s ω) 2 μ :=
    time_average_memLp_two m f T hT
  -- Step 2: EA is constant, hence in L² (probability measure → finite measure)
  haveI : IsProbabilityMeasure μ :=
    MeasureTheory.ProbabilityMeasure.instIsProbabilityMeasureToMeasure (gaussianFreeField_free m)
  have h_const_L2 : MemLp (fun _ : FieldConfiguration => EA) 2 μ := memLp_const EA
  -- Step 3: Difference is in L² (L² is a vector space)
  have h_diff_L2 : MemLp (fun ω => (1/T : ℂ) * (∫ s in Set.Icc (0 : ℝ) T, A s ω) - EA) 2 μ := by
    have h := h_avg_L2.sub h_const_L2
    convert h using 2
  -- Step 4: L² function has integrable square
  have h_sq_int : Integrable (fun ω => ‖(1/T : ℂ) * (∫ s in Set.Icc (0 : ℝ) T, A s ω) - EA‖^2) μ := by
    have h_meas := h_diff_L2.1
    rw [memLp_two_iff_integrable_sq_norm h_meas] at h_diff_L2
    exact h_diff_L2
  -- Goal matches h_sq_int up to notation: smul ↔ mul, and ∫ ω' ... ↔ EA
  have h_EA : ∫ ω' : FieldConfiguration, Complex.exp (distributionPairingℂ_real ω' f) ∂μ = EA := by
    simp only [EA, A]
    congr 1
    ext ω'
    congr 2
    exact (timeTranslationDistribution_zero ω').symm
  -- Rewrite the goal to match h_sq_int
  have h_eq : (fun ω => ‖((1 : ℝ) / T) • (∫ s in Set.Icc (0 : ℝ) T,
          Complex.exp (distributionPairingℂ_real (timeTranslationDistribution s ω) f))
        - ∫ ω', Complex.exp (distributionPairingℂ_real ω' f) ∂μ‖^2) =
      (fun ω => ‖(1/T : ℂ) * (∫ s in Set.Icc (0 : ℝ) T, A s ω) - EA‖^2) := by
    ext ω
    congr 2
    rw [h_EA]
    congr 1
    rw [one_div, Complex.real_smul, Complex.ofReal_inv]
    simp only [one_div, A]
  rw [h_eq]
  exact h_sq_int

/-! ## Decay Integral Bounds -/

/-- Double integral bound: ∫∫_{[0,T]²} (1+|s-u|)^{-3} ≤ 2T·C for some constant C. -/
lemma double_integral_decay_bound :
    ∃ C : ℝ, C > 0 ∧ ∀ T : ℝ, T > 0 →
      ∫ s in Set.Icc (0 : ℝ) T, ∫ u in Set.Icc (0 : ℝ) T,
        (1 + |s - u|)^(-(3 : ℝ)) ≤ 2 * T * C := by
  -- Use the textbook axiom for α = 3 > 1
  obtain ⟨C₀, hC₀_pos, hC₀_bound⟩ := OSforGFF.double_integral_polynomial_decay_bound_proved 3 (by norm_num : (3 : ℝ) > 1)
  use C₀, hC₀_pos
  intro T hT
  calc ∫ s in Set.Icc (0 : ℝ) T, ∫ u in Set.Icc (0 : ℝ) T, (1 + |s - u|)^(-(3 : ℝ))
      ≤ C₀ * T := hC₀_bound T hT
    _ ≤ 2 * T * C₀ := by nlinarith

/-- Product expectation stationarity. -/
lemma gff_product_expectation_stationarity (m : ℝ) [Fact (0 < m)] (f : TestFunctionℂ)
    (s u : ℝ) :
    let μ := (gaussianFreeField_free m).toMeasure
    let A := fun t ω => Complex.exp (distributionPairingℂ_real (timeTranslationDistribution t ω) f)
    ∫ ω, A s ω * starRingEnd ℂ (A u ω) ∂μ =
    ∫ ω, A (s - u) ω * starRingEnd ℂ (A 0 ω) ∂μ := by
  intro μ A
  -- A t ω = exp(⟨ω, T_{-t} f⟩) by timeTranslationDistribution_pairingℂ
  have h_A : ∀ t ω, A t ω = Complex.exp (distributionPairingℂ_real ω (timeTranslationSchwartzℂ (-t) f)) := by
    intro t ω; simp only [A]; rw [timeTranslationDistribution_pairingℂ]

  -- Rewrite using h_A
  simp_rw [h_A]
  simp only [neg_zero, timeTranslationSchwartzℂ_zero]

  -- Key: T_{-s} f = T_{-u}(T_{u-s} f) since -s = -u + (u - s)
  have h_comp : timeTranslationSchwartzℂ (-s) f =
      timeTranslationSchwartzℂ (-u) (timeTranslationSchwartzℂ (u - s) f) := by
    have h_sum : (-s : ℝ) = -u + (u - s) := by ring
    rw [h_sum, ← timeTranslationSchwartzℂ_add]

  have h_shift : (u - s : ℝ) = -(s - u) := by ring

  calc ∫ ω, Complex.exp (distributionPairingℂ_real ω (timeTranslationSchwartzℂ (-s) f)) *
           starRingEnd ℂ (Complex.exp (distributionPairingℂ_real ω (timeTranslationSchwartzℂ (-u) f))) ∂μ
      = ∫ ω, Complex.exp (distributionPairingℂ_real ω (timeTranslationSchwartzℂ (-u) (timeTranslationSchwartzℂ (u - s) f))) *
           starRingEnd ℂ (Complex.exp (distributionPairingℂ_real ω (timeTranslationSchwartzℂ (-u) f))) ∂μ := by
        rw [h_comp]
    _ = ∫ ω, Complex.exp (distributionPairingℂ_real ω (timeTranslationSchwartzℂ (u - s) f)) *
           starRingEnd ℂ (Complex.exp (distributionPairingℂ_real ω f)) ∂μ :=
        gff_exp_product_time_shift_invariant m (timeTranslationSchwartzℂ (u - s) f) f (-u)
    _ = ∫ ω, Complex.exp (distributionPairingℂ_real ω (timeTranslationSchwartzℂ (-(s - u)) f)) *
           starRingEnd ℂ (Complex.exp (distributionPairingℂ_real ω f)) ∂μ := by
        rw [h_shift]

/-! ## GFF Covariance Continuity -/

/-- The Schwinger two-point function (covariance) is continuous under time translation.
    s ↦ C(T_s f, g) is continuous.
    (Proved via dominated convergence, copied from GFFCovarianceContinuity.) -/
lemma gff_covariance_timeTranslation_continuous (m : ℝ) [Fact (0 < m)]
    (f g : TestFunctionℂ) :
    Continuous (fun s => SchwingerFunctionℂ₂ (gaussianFreeField_free m)
      (timeTranslationSchwartzℂ s f) g) := by
  -- Step 1: S₂ = freeCovarianceℂ_bilinear for the GFF
  simp_rw [gff_two_point_equals_covarianceℂ_free]
  -- Step 2: Expand the bilinear form definition
  unfold freeCovarianceℂ_bilinear
  -- L^∞ bounds for Schwartz functions
  obtain ⟨Cf, hCf⟩ := bounded_of_continuous_tendsto_zero f.continuous (schwartz_tendsto_zero f)
  obtain ⟨Cg, hCg⟩ := bounded_of_continuous_tendsto_zero g.continuous (schwartz_tendsto_zero g)
  -- Time translation preserves the bound
  have hTsf_bdd : ∀ s x, ‖(timeTranslationSchwartzℂ s f) x‖ ≤ Cf := by
    intro s x
    simp only [timeTranslationSchwartzℂ_apply]
    exact hCf (timeShift s x)
  -- Convert to product integral for continuous_of_dominated
  have h_fubini : ∀ s, ∫ x, ∫ y, (timeTranslationSchwartzℂ s f) x * (freeCovariance m x y : ℂ) * g y =
      ∫ p : SpaceTime × SpaceTime, (timeTranslationSchwartzℂ s f) p.1 * (freeCovariance m p.1 p.2 : ℂ) * g p.2
        ∂(volume.prod volume) := by
    intro s
    have h_int := freeCovarianceℂ_bilinear_integrable m (timeTranslationSchwartzℂ s f) g
    rw [Measure.volume_eq_prod] at h_int
    exact (MeasureTheory.integral_prod _ h_int).symm
  simp_rw [h_fubini]
  -- Bound using |g(y)| instead of Cg
  let bound' : SpaceTime × SpaceTime → ℝ := fun p => Cf * ‖(freeCovariance m p.1 p.2 : ℂ)‖ * ‖g p.2‖
  -- Pointwise bound
  have h_bdd' : ∀ s p, ‖(timeTranslationSchwartzℂ s f) p.1 * (freeCovariance m p.1 p.2 : ℂ) * g p.2‖ ≤ bound' p := by
    intro s ⟨x, y⟩
    simp only [bound']
    calc ‖(timeTranslationSchwartzℂ s f) x * (freeCovariance m x y : ℂ) * g y‖
        = ‖(timeTranslationSchwartzℂ s f) x‖ * ‖(freeCovariance m x y : ℂ)‖ * ‖g y‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ Cf * ‖(freeCovariance m x y : ℂ)‖ * ‖g y‖ := by
          apply mul_le_mul_of_nonneg_right
          apply mul_le_mul_of_nonneg_right (hTsf_bdd s x) (norm_nonneg _)
          exact norm_nonneg _
  -- The bound is integrable via convolution estimate
  have h_bound_int : Integrable bound' (volume.prod volume) := by
    simp only [bound']
    have h_eq : (fun p : SpaceTime × SpaceTime => Cf * ‖(freeCovariance m p.1 p.2 : ℂ)‖ * ‖g p.2‖) =
        (fun p => Cf * (‖(freeCovariance m p.1 p.2 : ℂ)‖ * ‖g p.2‖)) := by ext p; ring
    rw [h_eq]
    apply Integrable.const_mul
    have h_transl : ∀ x y, freeCovariance m x y = freeCovarianceKernel m (x - y) := by
      intro x y; simp only [freeCovariance, freeCovarianceBessel, freeCovarianceKernel, zero_sub, norm_neg]
    have h_eq2 : (fun p : SpaceTime × SpaceTime => ‖(freeCovariance m p.1 p.2 : ℂ)‖ * ‖g p.2‖) =
        (fun p => ‖(freeCovarianceKernel m (p.1 - p.2) : ℂ)‖ * ‖g p.2‖) := by ext p; rw [h_transl]
    rw [h_eq2]
    have hK_int : Integrable (freeCovarianceKernel m) (volume : Measure SpaceTime) :=
      freeCovarianceKernel_integrable m (Fact.out)
    have hg_int : Integrable (fun y => ‖g y‖) (volume : Measure SpaceTime) :=
      (SchwartzMap.integrable (μ := volume) g).norm
    have hK_norm : Integrable (fun z => ‖(freeCovarianceKernel m z : ℂ)‖) (volume : Measure SpaceTime) := by
      have := hK_int.norm
      simp only [Real.norm_eq_abs] at this
      convert this using 1
      ext z; simp
    have h_eq3 : (fun p : SpaceTime × SpaceTime => ‖(freeCovarianceKernel m (p.1 - p.2) : ℂ)‖ * ‖g p.2‖) =
        (fun p => ‖g p.2‖ * ‖(freeCovarianceKernel m (p.1 - p.2) : ℂ)‖) := by ext p; ring
    rw [h_eq3]
    let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.mul ℝ ℝ
    have h_conv := Integrable.convolution_integrand L hg_int hK_norm
    convert h_conv using 1
  -- Apply continuous_of_dominated
  apply MeasureTheory.continuous_of_dominated
  · intro s
    have h_int := freeCovarianceℂ_bilinear_integrable m (timeTranslationSchwartzℂ s f) g
    rw [Measure.volume_eq_prod] at h_int
    exact h_int.aestronglyMeasurable
  · intro s; exact Filter.Eventually.of_forall (h_bdd' s)
  · exact h_bound_int
  · filter_upwards with ⟨x, y⟩
    exact ((f.continuous.comp (TimeTranslation.continuous_timeShift_param x)).mul continuous_const).mul continuous_const

/-- The GFF covariance function (s, u) ↦ E[A_s · conj(A_u)] - E[A]·conj(E[A]) is continuous.

    Proved using the Gaussian algebraic structure:
    1. By stationarity, Cov(s,u) = g(s-u) for g(t) = E[A_t·conj(A_0)] - EA·conj(EA)
    2. By Gaussian MGF formula, g(t) = EA·conj(EA)·(exp(C(T_{-t}f, conj(f))) - 1)
    3. C(T_s f, g) is continuous in s by dominated convergence
    4. Compose with exp and subtraction -/
lemma gff_covariance_continuous (m : ℝ) [Fact (0 < m)] (f : TestFunctionℂ) :
    let μ := (gaussianFreeField_free m).toMeasure
    let A := fun t ω => Complex.exp (distributionPairingℂ_real (timeTranslationDistribution t ω) f)
    let EA := ∫ ω, Complex.exp (distributionPairingℂ_real ω f) ∂μ
    Continuous (fun (p : ℝ × ℝ) =>
      ∫ ω, A p.1 ω * starRingEnd ℂ (A p.2 ω) ∂μ - EA * starRingEnd ℂ EA) := by
  intro μ A EA
  -- Rewrite using stationarity: the function factors through (s, u) ↦ s - u
  have h_factors : (fun p : ℝ × ℝ => ∫ ω, A p.1 ω * starRingEnd ℂ (A p.2 ω) ∂μ - EA * starRingEnd ℂ EA)
      = (fun p : ℝ × ℝ => ∫ ω, A (p.1 - p.2) ω * starRingEnd ℂ (A 0 ω) ∂μ - EA * starRingEnd ℂ EA) := by
    ext p
    have := gff_product_expectation_stationarity m f p.1 p.2
    simp only at this ⊢
    rw [this]
  rw [h_factors]
  -- (s, u) ↦ s - u is continuous
  have h_sub_cont : Continuous (fun p : ℝ × ℝ => p.1 - p.2) := continuous_fst.sub continuous_snd
  -- t ↦ E[A_t * conj(A_0)] is continuous via Gaussian MGF formula
  have h_integral_cont : Continuous (fun t => ∫ ω, A t ω * starRingEnd ℂ (A 0 ω) ∂μ) := by
    -- Establish the explicit formula for the integrand
    have h_integrand_eq : ∀ t ω, A t ω * starRingEnd ℂ (A 0 ω) =
        Complex.exp (distributionPairingℂ_real ω (timeTranslationSchwartzℂ (-t) f)) *
        Complex.exp (distributionPairingℂ_real ω (conjSchwartz f)) := by
      intro t ω
      simp only [A]
      rw [timeTranslationDistribution_pairingℂ]
      simp only [timeTranslationDistribution_zero]
      congr 1
      rw [← Complex.exp_conj, ← distributionPairingℂ_real_conj]
    -- The integral has an explicit formula via gff_joint_mgf_factorization
    have h_formula : ∀ t, ∫ ω, A t ω * starRingEnd ℂ (A 0 ω) ∂μ =
        (∫ ω, Complex.exp (distributionPairingℂ_real ω (timeTranslationSchwartzℂ (-t) f)) ∂μ) *
        (∫ ω, Complex.exp (distributionPairingℂ_real ω (conjSchwartz f)) ∂μ) *
        Complex.exp (SchwingerFunctionℂ₂ (gaussianFreeField_free m)
          (timeTranslationSchwartzℂ (-t) f) (conjSchwartz f)) := by
      intro t
      have h_eq : (fun ω => A t ω * starRingEnd ℂ (A 0 ω)) =
          (fun ω => Complex.exp (distributionPairingℂ_real ω (timeTranslationSchwartzℂ (-t) f)) *
                    Complex.exp (distributionPairingℂ_real ω (conjSchwartz f))) := by
        ext ω; exact h_integrand_eq t ω
      rw [h_eq]
      have h_exp_add : (fun ω => Complex.exp (distributionPairingℂ_real ω (timeTranslationSchwartzℂ (-t) f)) *
                                Complex.exp (distributionPairingℂ_real ω (conjSchwartz f))) =
          (fun ω => Complex.exp (distributionPairingℂ_real ω (timeTranslationSchwartzℂ (-t) f) +
                                 distributionPairingℂ_real ω (conjSchwartz f))) := by
        ext ω; rw [← Complex.exp_add]
      rw [h_exp_add]
      exact gff_joint_mgf_factorization m (timeTranslationSchwartzℂ (-t) f) (conjSchwartz f)
    -- E[exp(T_{-t}f)] = EA by time translation invariance
    have h_E_shifted : ∀ t, ∫ ω, Complex.exp (distributionPairingℂ_real ω (timeTranslationSchwartzℂ (-t) f)) ∂μ = EA := by
      intro t
      simp only [EA, μ]
      exact gff_generating_time_invariant m (-t) f
    let E_conj := ∫ ω, Complex.exp (distributionPairingℂ_real ω (conjSchwartz f)) ∂μ
    -- t ↦ C(T_{-t}f, conjSchwartz f) is continuous
    have h_cov_cont : Continuous (fun t =>
        SchwingerFunctionℂ₂ (gaussianFreeField_free m) (timeTranslationSchwartzℂ (-t) f) (conjSchwartz f)) := by
      have := gff_covariance_timeTranslation_continuous m f (conjSchwartz f)
      exact this.comp continuous_neg
    have h_exp_cov_cont : Continuous (fun t =>
        Complex.exp (SchwingerFunctionℂ₂ (gaussianFreeField_free m)
          (timeTranslationSchwartzℂ (-t) f) (conjSchwartz f))) :=
      Complex.continuous_exp.comp h_cov_cont
    -- Simplify using the formula
    have h_simplified : (fun t => ∫ ω, A t ω * starRingEnd ℂ (A 0 ω) ∂μ) =
        (fun t => EA * E_conj * Complex.exp (SchwingerFunctionℂ₂ (gaussianFreeField_free m)
          (timeTranslationSchwartzℂ (-t) f) (conjSchwartz f))) := by
      ext t
      rw [h_formula t, h_E_shifted t]
    rw [h_simplified]
    exact (continuous_const.mul continuous_const).mul h_exp_cov_cont
  -- Compose: (s, u) ↦ s - u ↦ E[A_{s-u} * conj(A_0)] - const
  exact (h_integral_cont.comp h_sub_cont).sub continuous_const

/-! ## Variance Bounds -/

/-- L² variance can be bounded by double integral of covariance.

    This combines the textbook axiom (which gives ‖∫∫ Cov‖) with triangle inequality
    to get the bound in terms of ∫∫ ‖Cov‖ which is what we need for decay estimates. -/
lemma L2_time_average_variance_bound (m : ℝ) [Fact (0 < m)] (f : TestFunctionℂ) (T : ℝ) (hT : T > 0) :
    let μ := (gaussianFreeField_free m).toMeasure
    let A := fun s ω => Complex.exp (distributionPairingℂ_real (timeTranslationDistribution s ω) f)
    let EA := ∫ ω, Complex.exp (distributionPairingℂ_real ω f) ∂μ
    let Cov := fun s u => ∫ ω, A s ω * starRingEnd ℂ (A u ω) ∂μ - EA * starRingEnd ℂ EA
    ∫ ω, ‖(1 / T) * (∫ s in Set.Icc (0 : ℝ) T, A s ω) - EA‖^2 ∂μ ≤
      (1 / T^2) * ∫ s in Set.Icc (0 : ℝ) T, ∫ u in Set.Icc (0 : ℝ) T, ‖Cov s u‖ := by
  intro μ A EA Cov
  -- GFF is a probability measure
  haveI h_prob : IsProbabilityMeasure μ :=
    MeasureTheory.ProbabilityMeasure.instIsProbabilityMeasureToMeasure (gaussianFreeField_free m)

  -- Stationarity: E[A_s] = EA for all s (GFF is time-translation invariant)
  -- Uses: A s ω = exp(⟨T_s ω, f⟩) = exp(⟨ω, T_{-s} f⟩) by duality
  -- And: ∫ exp(⟨ω, T_{-s} f⟩) dμ = ∫ exp(⟨ω, f⟩) dμ by gff_generating_time_invariant
  have h_mean : ∀ s, ∫ ω, A s ω ∂μ = EA := fun s => by
    simp only [A, EA, μ]
    have h_duality : (fun ω => Complex.exp (distributionPairingℂ_real (timeTranslationDistribution s ω) f)) =
        (fun ω => Complex.exp (distributionPairingℂ_real ω (timeTranslationSchwartzℂ (-s) f))) := by
      ext ω; rw [timeTranslationDistribution_pairingℂ]
    rw [h_duality]
    exact gff_generating_time_invariant m (-s) f

  -- Joint measurability on [0,T] × Ω
  have h_meas : AEStronglyMeasurable (Function.uncurry A)
      ((volume.restrict (Set.Icc 0 T)).prod μ) := by
    -- Use Carathéodory condition: continuous in s for each ω, measurable in ω for each s
    apply MeasureTheory.StronglyMeasurable.aestronglyMeasurable
    apply MeasureTheory.stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
    · -- ∀ ω, Continuous (fun s => A s ω)
      intro ω
      simp only [A]
      exact Complex.continuous_exp.comp (continuous_distributionPairingℂ_timeTranslation ω f)
    · -- ∀ s, StronglyMeasurable (A s)
      intro s
      -- A s = fun ω => exp(⟨T_s ω, f⟩) = fun ω => exp(⟨ω, T_{-s} f⟩) by duality
      have h_eq : (fun ω => Complex.exp (distributionPairingℂ_real (timeTranslationDistribution s ω) f)) =
          (fun ω => Complex.exp (distributionPairingℂ_real ω (timeTranslationSchwartzℂ (-s) f))) := by
        ext ω; rw [timeTranslationDistribution_pairingℂ]
      -- A s equals this rewritten function
      show StronglyMeasurable (fun ω => Complex.exp (distributionPairingℂ_real (timeTranslationDistribution s ω) f))
      rw [h_eq]
      -- Now prove continuity of the rewritten function → StronglyMeasurable
      exact (Complex.continuous_exp.comp (QFT.distributionPairingℂ_real_continuous _)).stronglyMeasurable

  -- L² integrability on [0,T] × Ω (crucial for Fubini)
  -- Proof outline:
  -- 1. ∫∫|A(s,ω)|² d(vol|[0,T] × μ) = ∫_[0,T] (∫_Ω |A(s,ω)|² dμ) ds  (Tonelli)
  -- 2. For each s, A(s,·) ∈ L²(μ) by gff_exp_time_translated_memLp_two (Fernique)
  -- 3. ∫_Ω |A(s,ω)|² dμ = snorm(A s)² is constant in s (stationarity)
  -- 4. Therefore ∫_[0,T] C² ds = T·C² < ∞
  have h_L2 : MeasureTheory.MemLp (Function.uncurry A) 2
      ((volume.restrict (Set.Icc 0 T)).prod μ) := by
    -- Use the proved theorem from L2TimeIntegral for L² on product space
    apply OSforGFF.memLp_prod_of_uniform_slicewise_bound μ A T h_meas
    · -- Each A_s is in L²(μ) by Fernique
      exact fun s => gff_exp_time_translated_memLp_two m s f
    · -- L² norm is constant in s (stationarity from OS2)
      intro s
      simp only [A]
      have h_0 : timeTranslationDistribution 0 = id := funext timeTranslationDistribution_zero
      simp only [h_0, id_eq]
      exact gff_exp_L2_norm_constant m f s

  -- Each time-slice is L²(Ω) by Fernique
  have h_slice_L2 : ∀ s, MemLp (A s) 2 μ := fun s =>
    gff_exp_time_translated_memLp_two m s f
  -- s ↦ A_s(ω) is continuous for each ω, hence integrable on [0,T]
  have h_cont_s : ∀ ω, Continuous (fun s => A s ω) := fun ω => by
    simp only [A]
    exact Complex.continuous_exp.comp (continuous_distributionPairingℂ_timeTranslation ω f)
  have h_slice_int : ∀ᵐ ω ∂μ, Integrable (fun s => A s ω) (volume.restrict (Set.Icc 0 T)) :=
    ae_of_all _ fun ω => (h_cont_s ω).continuousOn.integrableOn_compact isCompact_Icc
  -- Helper: A s is strongly measurable in ω for each s
  have h_sm_slice : ∀ s, StronglyMeasurable (fun ω => A s ω) := by
    intro s; simp only [A]
    have h_eq : (fun ω => Complex.exp (distributionPairingℂ_real
        (timeTranslationDistribution s ω) f)) =
        (fun ω => Complex.exp (distributionPairingℂ_real ω
        (timeTranslationSchwartzℂ (-s) f))) := by
      ext ω; rw [timeTranslationDistribution_pairingℂ]
    rw [h_eq]
    exact (Complex.continuous_exp.comp
      (QFT.distributionPairingℂ_real_continuous _)).stronglyMeasurable
  -- Fubini integrability for the covariance triple integral swap
  -- Uses textbook axiom: L² slices + continuity + measurability → triple product integrable
  have h_Fubini : Integrable (fun (x : FieldConfiguration × (ℝ × ℝ)) =>
      (A x.2.1 x.1 - EA) * starRingEnd ℂ (A x.2.2 x.1 - EA))
      (μ.prod ((volume.restrict (Set.Icc 0 T)).prod (volume.restrict (Set.Icc 0 T)))) :=
    OSforGFF.L2_process_covariance_fubini_integrable μ A EA T hT h_L2 h_cont_s h_sm_slice
  -- Apply the proved variance bound: ‖variance‖ ≤ T⁻² * ‖∫∫ Cov‖
  have h_axiom := OSforGFF.L2_variance_time_average_bound μ A EA T hT h_mean
    h_Fubini h_slice_L2 h_slice_int

  -- The LHS is a nonnegative real, so ‖LHS‖ = LHS
  have h_lhs_nonneg : 0 ≤ ∫ ω, ‖(T⁻¹ : ℂ) * (∫ s in Set.Icc (0 : ℝ) T, A s ω) - EA‖^2 ∂μ :=
    integral_nonneg (fun _ => sq_nonneg _)

  -- Convert ‖∫ω ‖...‖²‖ back to ∫ω ‖...‖² (since it's a nonneg real)
  have h_lhs_eq : ‖∫ ω, ‖(T⁻¹ : ℂ) * (∫ s in Set.Icc (0 : ℝ) T, A s ω) - EA‖^2 ∂μ‖ =
      ∫ ω, ‖(T⁻¹ : ℂ) * (∫ s in Set.Icc (0 : ℝ) T, A s ω) - EA‖^2 ∂μ :=
    Real.norm_of_nonneg h_lhs_nonneg

  -- Triangle inequality: ‖∫∫ Cov‖ ≤ ∫∫ ‖Cov‖
  -- First establish that Cov is continuous (from gff_covariance_continuous)
  have h_Cov_cont : Continuous (fun (p : ℝ × ℝ) => Cov p.1 p.2) := gff_covariance_continuous m f

  -- The inner integral s ↦ ∫_u Cov s u is continuous by continuous_parametric_integral_of_continuous
  have h_inner_cont : Continuous (fun s => ∫ u in Set.Icc (0 : ℝ) T, Cov s u) := by
    apply continuous_parametric_integral_of_continuous h_Cov_cont isCompact_Icc

  -- Similarly, s ↦ ∫_u ‖Cov s u‖ is continuous
  have h_inner_norm_cont : Continuous (fun s => ∫ u in Set.Icc (0 : ℝ) T, ‖Cov s u‖) := by
    apply continuous_parametric_integral_of_continuous _ isCompact_Icc
    exact continuous_norm.comp h_Cov_cont

  have h_triangle : ‖∫ s in Set.Icc (0 : ℝ) T, ∫ u in Set.Icc (0 : ℝ) T, Cov s u‖ ≤
      ∫ s in Set.Icc (0 : ℝ) T, ∫ u in Set.Icc (0 : ℝ) T, ‖Cov s u‖ := by
    calc ‖∫ s in Set.Icc (0 : ℝ) T, ∫ u in Set.Icc (0 : ℝ) T, Cov s u‖
        ≤ ∫ s in Set.Icc (0 : ℝ) T, ‖∫ u in Set.Icc (0 : ℝ) T, Cov s u‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ s in Set.Icc (0 : ℝ) T, ∫ u in Set.Icc (0 : ℝ) T, ‖Cov s u‖ := by
          apply MeasureTheory.setIntegral_mono
          · -- Integrability of s ↦ ‖∫_u Cov s u‖ on [0,T]
            exact (continuous_norm.comp h_inner_cont).integrableOn_Icc
          · -- Integrability of s ↦ ∫_u ‖Cov s u‖ on [0,T]
            exact h_inner_norm_cont.integrableOn_Icc
          · intro s; exact norm_integral_le_integral_norm _

  -- Combine: variance ≤ T⁻² * ‖∫∫ Cov‖ ≤ T⁻² * ∫∫ ‖Cov‖
  -- Note: (1/T) = T⁻¹ as complex numbers
  have h_inv : (1 / T : ℂ) = (T⁻¹ : ℂ) := by simp [one_div]
  have h_inv_sq : (1 / T^2 : ℝ) = T⁻¹^2 := by field_simp
  rw [h_inv_sq]
  calc ∫ ω, ‖(1 / T : ℂ) * (∫ s in Set.Icc (0 : ℝ) T, A s ω) - EA‖^2 ∂μ
      = ∫ ω, ‖(T⁻¹ : ℂ) * (∫ s in Set.Icc (0 : ℝ) T, A s ω) - EA‖^2 ∂μ := by rw [h_inv]
    _ = ‖∫ ω, ‖(T⁻¹ : ℂ) * (∫ s in Set.Icc (0 : ℝ) T, A s ω) - EA‖^2 ∂μ‖ := h_lhs_eq.symm
    _ ≤ T⁻¹^2 * ‖∫ s in Set.Icc (0 : ℝ) T, ∫ u in Set.Icc (0 : ℝ) T, Cov s u‖ := h_axiom
    _ ≤ T⁻¹^2 * ∫ s in Set.Icc (0 : ℝ) T, ∫ u in Set.Icc (0 : ℝ) T, ‖Cov s u‖ := by
        apply mul_le_mul_of_nonneg_left h_triangle
        positivity

/-! ## Clustering Implies Covariance Decay -/

/-- OS4'' clustering implies covariance decay with exponent -3. -/
lemma clustering_implies_covariance_decay (m : ℝ) [Fact (0 < m)] (f : TestFunctionℂ)
    (h_cluster : OS4''_Clustering m) :
    ∃ (c : ℝ), c ≥ 0 ∧ ∀ s u : ℝ, s ≥ 0 → u ≥ 0 →
      let μ := (gaussianFreeField_free m).toMeasure
      let A := fun t ω => Complex.exp (distributionPairingℂ_real (timeTranslationDistribution t ω) f)
      let EA := ∫ ω, Complex.exp (distributionPairingℂ_real ω f) ∂μ
      ‖∫ ω, A s ω * starRingEnd ℂ (A u ω) ∂μ - EA * starRingEnd ℂ EA‖ ≤
        c * (1 + |s - u|)^(-(3 : ℝ)) := by
  -- Get clustering constant for (conjSchwartz f, f) pair
  obtain ⟨c_ff, hc_ff_nonneg, hc_ff⟩ := h_cluster (conjSchwartz f) f

  use c_ff
  refine ⟨hc_ff_nonneg, ?_⟩

  intro s u hs hu μ A EA

  -- Use stationarity to reduce to time difference
  have h_stat := gff_product_expectation_stationarity m f s u
  simp only at h_stat
  rw [h_stat]

  -- Handle both cases s ≥ u and s < u
  by_cases h_sign : s ≥ u
  · -- Case s ≥ u: |s - u| = s - u
    have h_abs : |s - u| = s - u := abs_of_nonneg (sub_nonneg.mpr h_sign)
    rw [h_abs]
    have ht : s - u ≥ 0 := sub_nonneg.mpr h_sign

    -- Rewrite A t ω * conj(A 0 ω) to match OS4'' clustering form
    have h_integrand_eq : ∀ ω, A (s - u) ω * starRingEnd ℂ (A 0 ω) =
        Complex.exp (distributionPairingℂ_real ω (conjSchwartz f) +
                     distributionPairingℂ_real (timeTranslationDistribution (s - u) ω) f) := by
      intro ω
      simp only [A]
      rw [timeTranslationDistribution_zero]
      have h1 : starRingEnd ℂ (Complex.exp (distributionPairingℂ_real ω f)) =
          Complex.exp (starRingEnd ℂ (distributionPairingℂ_real ω f)) := (Complex.exp_conj _).symm
      rw [h1, distributionPairingℂ_real_conj, ← Complex.exp_add]
      ring_nf

    have h_const_eq : EA * starRingEnd ℂ EA =
        (∫ ω, Complex.exp (distributionPairingℂ_real ω (conjSchwartz f)) ∂μ) *
        (∫ ω, Complex.exp (distributionPairingℂ_real ω f) ∂μ) := by
      simp only [EA]
      have h_conj_int : starRingEnd ℂ (∫ ω, Complex.exp (distributionPairingℂ_real ω f) ∂μ) =
          ∫ ω, starRingEnd ℂ (Complex.exp (distributionPairingℂ_real ω f)) ∂μ := integral_conj.symm
      rw [h_conj_int]
      have h_conj_exp : ∀ ω, starRingEnd ℂ (Complex.exp (distributionPairingℂ_real ω f)) =
          Complex.exp (distributionPairingℂ_real ω (conjSchwartz f)) := fun ω => by
        rw [(Complex.exp_conj _).symm, distributionPairingℂ_real_conj]
      simp_rw [h_conj_exp]
      ring

    have h_cluster_bound := hc_ff (s - u) ht
    have h_int_rw : ∫ ω, A (s - u) ω * starRingEnd ℂ (A 0 ω) ∂μ =
        ∫ ω, Complex.exp (distributionPairingℂ_real ω (conjSchwartz f) +
              distributionPairingℂ_real (timeTranslationDistribution (s - u) ω) f) ∂μ := by
      congr 1 with ω; exact h_integrand_eq ω

    calc ‖∫ ω, A (s - u) ω * starRingEnd ℂ (A 0 ω) ∂μ - EA * starRingEnd ℂ EA‖
        = ‖∫ ω, Complex.exp (distributionPairingℂ_real ω (conjSchwartz f) +
              distributionPairingℂ_real (timeTranslationDistribution (s - u) ω) f) ∂μ -
            (∫ ω, Complex.exp (distributionPairingℂ_real ω (conjSchwartz f)) ∂μ) *
            (∫ ω, Complex.exp (distributionPairingℂ_real ω f) ∂μ)‖ := by
          rw [h_int_rw, h_const_eq]
      _ ≤ c_ff * (1 + (s - u))^(-(6:ℝ)) := h_cluster_bound
      _ ≤ c_ff * (1 + (s - u))^(-(3:ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ hc_ff_nonneg
          have h_base : 1 ≤ 1 + (s - u) := by linarith
          exact Real.rpow_le_rpow_of_exponent_le h_base (by norm_num : (-6 : ℝ) ≤ -3)

  · -- Case s < u: |s - u| = u - s
    push_neg at h_sign
    have h_abs : |s - u| = u - s := by rw [abs_sub_comm]; exact abs_of_nonneg (by linarith)
    rw [h_abs]

    have h_pos : u - s > 0 := by linarith
    have h_nonneg : u - s ≥ 0 := le_of_lt h_pos

    -- By norm conjugation symmetry: ‖X‖ = ‖conj(X)‖
    -- Taking conjugate swaps A(s-u) and A(0), then use commutativity
    have h_norm_eq : ‖∫ ω, A (s - u) ω * starRingEnd ℂ (A 0 ω) ∂μ - EA * starRingEnd ℂ EA‖ =
        ‖∫ ω, A 0 ω * starRingEnd ℂ (A (s - u) ω) ∂μ - EA * starRingEnd ℂ EA‖ := by
      rw [← Complex.norm_conj, map_sub, ← integral_conj]
      -- conj(a * conj(b)) = conj(a) * b and conj(EA * conj(EA)) = conj(EA) * EA = EA * conj(EA)
      have h_int_eq : ∫ ω, starRingEnd ℂ (A (s - u) ω * starRingEnd ℂ (A 0 ω)) ∂μ =
          ∫ ω, A 0 ω * starRingEnd ℂ (A (s - u) ω) ∂μ := by
        congr 1 with ω
        simp only [map_mul, starRingEnd_self_apply]
        ring
      have h_const_eq' : starRingEnd ℂ (EA * starRingEnd ℂ EA) = EA * starRingEnd ℂ EA := by
        simp only [map_mul, starRingEnd_self_apply]
        ring
      rw [h_int_eq, h_const_eq']
    rw [h_norm_eq]

    -- Use stationarity with shift (u - s): ∫ A(0) * conj(A(s-u)) = ∫ A(u-s) * conj(A(0))
    have h_stat2 := gff_product_expectation_stationarity m f 0 (s - u)
    simp only at h_stat2
    have h_simp : (0 : ℝ) - (s - u) = u - s := by ring
    rw [h_simp] at h_stat2
    rw [h_stat2]

    -- Now we can apply the s ≥ u case machinery with t = u - s ≥ 0
    have h_integrand_eq : ∀ ω, A (u - s) ω * starRingEnd ℂ (A 0 ω) =
        Complex.exp (distributionPairingℂ_real ω (conjSchwartz f) +
                     distributionPairingℂ_real (timeTranslationDistribution (u - s) ω) f) := by
      intro ω
      simp only [A]
      rw [timeTranslationDistribution_zero]
      have h1 : starRingEnd ℂ (Complex.exp (distributionPairingℂ_real ω f)) =
          Complex.exp (starRingEnd ℂ (distributionPairingℂ_real ω f)) := (Complex.exp_conj _).symm
      rw [h1, distributionPairingℂ_real_conj, ← Complex.exp_add]
      ring_nf

    have h_const_eq : EA * starRingEnd ℂ EA =
        (∫ ω, Complex.exp (distributionPairingℂ_real ω (conjSchwartz f)) ∂μ) *
        (∫ ω, Complex.exp (distributionPairingℂ_real ω f) ∂μ) := by
      simp only [EA]
      have h_conj_int : starRingEnd ℂ (∫ ω, Complex.exp (distributionPairingℂ_real ω f) ∂μ) =
          ∫ ω, starRingEnd ℂ (Complex.exp (distributionPairingℂ_real ω f)) ∂μ := integral_conj.symm
      rw [h_conj_int]
      have h_conj_exp : ∀ ω, starRingEnd ℂ (Complex.exp (distributionPairingℂ_real ω f)) =
          Complex.exp (distributionPairingℂ_real ω (conjSchwartz f)) := fun ω => by
        rw [(Complex.exp_conj _).symm, distributionPairingℂ_real_conj]
      simp_rw [h_conj_exp]
      ring

    have h_cluster_bound := hc_ff (u - s) h_nonneg
    have h_int_rw : ∫ ω, A (u - s) ω * starRingEnd ℂ (A 0 ω) ∂μ =
        ∫ ω, Complex.exp (distributionPairingℂ_real ω (conjSchwartz f) +
              distributionPairingℂ_real (timeTranslationDistribution (u - s) ω) f) ∂μ := by
      congr 1 with ω; exact h_integrand_eq ω

    calc ‖∫ ω, A (u - s) ω * starRingEnd ℂ (A 0 ω) ∂μ - EA * starRingEnd ℂ EA‖
        = ‖∫ ω, Complex.exp (distributionPairingℂ_real ω (conjSchwartz f) +
              distributionPairingℂ_real (timeTranslationDistribution (u - s) ω) f) ∂μ -
            (∫ ω, Complex.exp (distributionPairingℂ_real ω (conjSchwartz f)) ∂μ) *
            (∫ ω, Complex.exp (distributionPairingℂ_real ω f) ∂μ)‖ := by
          rw [h_int_rw, h_const_eq]
      _ ≤ c_ff * (1 + (u - s))^(-(6:ℝ)) := h_cluster_bound
      _ ≤ c_ff * (1 + (u - s))^(-(3:ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ hc_ff_nonneg
          have h_base : 1 ≤ 1 + (u - s) := by linarith
          exact Real.rpow_le_rpow_of_exponent_le h_base (by norm_num : (-6 : ℝ) ≤ -3)

/-- The norm of the GFF covariance is integrable on [0,T] for each fixed first argument.
    Uses gff_covariance_norm_integrableOn_slice_axiom to avoid expensive type unification. -/
lemma gff_covariance_norm_integrableOn_slice (m : ℝ) [Fact (0 < m)] (f : TestFunctionℂ)
    (s : ℝ) (T : ℝ) :
    let μ := (gaussianFreeField_free m).toMeasure
    let A := fun t ω => Complex.exp (distributionPairingℂ_real (timeTranslationDistribution t ω) f)
    let EA := ∫ ω, Complex.exp (distributionPairingℂ_real ω f) ∂μ
    let Cov := fun s' u => ∫ ω, A s' ω * starRingEnd ℂ (A u ω) ∂μ - EA * starRingEnd ℂ EA
    MeasureTheory.IntegrableOn (fun u => ‖Cov s u‖) (Set.Icc 0 T) := by
  intro μ A EA Cov
  haveI : IsProbabilityMeasure μ :=
    MeasureTheory.ProbabilityMeasure.instIsProbabilityMeasureToMeasure (gaussianFreeField_free m)
  exact OSforGFF.gff_covariance_norm_integrableOn_slice_proved μ A EA s T
    (gff_covariance_continuous m f)

/-! ## Variance Decay from Clustering -/

/-- Covariance decay implies variance tends to zero. -/
lemma variance_decay_from_clustering (m : ℝ) [Fact (0 < m)] (f : TestFunctionℂ)
    (c : ℝ) (hc : c ≥ 0)
    (h_cov_decay : ∀ s u : ℝ, s ≥ 0 → u ≥ 0 →
      let μ := (gaussianFreeField_free m).toMeasure
      let A := fun t ω => Complex.exp (distributionPairingℂ_real (timeTranslationDistribution t ω) f)
      let EA := ∫ ω, Complex.exp (distributionPairingℂ_real ω f) ∂μ
      ‖∫ ω, A s ω * starRingEnd ℂ (A u ω) ∂μ - EA * starRingEnd ℂ EA‖ ≤
        c * (1 + |s - u|)^(-(3 : ℝ))) :
    let μ := (gaussianFreeField_free m).toMeasure
    Filter.Tendsto
      (fun T : ℝ =>
        ∫ ω, ‖(1 / T) * ∫ s in Set.Icc (0 : ℝ) T,
          Complex.exp (distributionPairingℂ_real (timeTranslationDistribution s ω) f)
          - ∫ ω', Complex.exp (distributionPairingℂ_real ω' f) ∂μ‖^2 ∂μ)
      Filter.atTop
      (nhds 0) := by
  intro μ

  -- Get the constant C from double integral bound
  obtain ⟨C, hC_pos, h_double⟩ := double_integral_decay_bound

  -- For T > 0, variance ≤ 2·c·C / T
  have h_upper : ∀ T > 0,
      ∫ ω, ‖(1 / T) * ∫ s in Set.Icc (0 : ℝ) T,
          Complex.exp (distributionPairingℂ_real (timeTranslationDistribution s ω) f)
        - ∫ ω', Complex.exp (distributionPairingℂ_real ω' f) ∂μ‖^2 ∂μ ≤ 2 * c * C / T := by
    intro T hT
    -- The chain of inequalities:
    -- 1. variance ≤ (1/T²) · ∫∫ ‖Cov‖  (by L2_time_average_variance_bound)
    -- 2. ∫∫ ‖Cov‖ ≤ ∫∫ c·(1+|s-u|)^{-3}  (by h_cov_decay pointwise)
    -- 3. ∫∫ c·(1+|s-u|)^{-3} = c · ∫∫ (1+|s-u|)^{-3} ≤ c · 2TC  (by double_integral_decay_bound)
    -- 4. So variance ≤ (1/T²) · c · 2TC = 2cC/T
    have h_double_T := h_double T hT

    -- Define A, EA, Cov consistently with L2_time_average_variance_bound
    let A := fun s ω => Complex.exp (distributionPairingℂ_real (timeTranslationDistribution s ω) f)
    let EA := ∫ ω, Complex.exp (distributionPairingℂ_real ω f) ∂μ
    let Cov := fun s u => ∫ ω, A s ω * starRingEnd ℂ (A u ω) ∂μ - EA * starRingEnd ℂ EA

    -- Step 1: L2_time_average_variance_bound gives variance ≤ (1/T²) · ∫∫ ‖Cov‖
    have h_var := L2_time_average_variance_bound m f T hT

    -- Step 2: ‖Cov(s,u)‖ ≤ c·(1+|s-u|)^{-3} for s,u in [0,T]
    have h_cov_bound : ∀ s u, s ∈ Set.Icc (0 : ℝ) T → u ∈ Set.Icc (0 : ℝ) T →
        ‖Cov s u‖ ≤ c * (1 + |s - u|)^(-(3 : ℝ)) := by
      intro s u hs hu
      simp only [Set.mem_Icc] at hs hu
      exact h_cov_decay s u hs.1 hu.1

    -- Step 3: ∫∫ ‖Cov‖ ≤ c · ∫∫ (1+|s-u|)^{-3} ≤ c · 2TC
    -- First establish continuity facts for integrability
    have h_Cov_cont : Continuous (fun (p : ℝ × ℝ) => Cov p.1 p.2) := gff_covariance_continuous m f
    have h_decay_cont : Continuous (fun (p : ℝ × ℝ) => c * (1 + |p.1 - p.2|)^(-(3 : ℝ))) := by
      apply Continuous.mul continuous_const
      apply Continuous.rpow_const
      · exact continuous_const.add (continuous_abs.comp (continuous_fst.sub continuous_snd))
      · intro x
        left
        -- 1 + |x.1 - x.2| ≥ 1 > 0, so never zero
        linarith [abs_nonneg (x.1 - x.2)]

    have h_cov_double_bound : ∫ s in Set.Icc (0 : ℝ) T, ∫ u in Set.Icc (0 : ℝ) T, ‖Cov s u‖ ≤
        c * (2 * T * C) := by
      -- First bound by ∫∫ c·(1+|s-u|)^{-3}
      -- Define curried versions for continuous_parametric_integral_of_continuous
      let CovNorm : ℝ → ℝ → ℝ := fun s u => ‖Cov s u‖
      let DecayFn : ℝ → ℝ → ℝ := fun s u => c * (1 + |s - u|)^(-(3 : ℝ))
      have h_CovNorm_cont : Continuous (Function.uncurry CovNorm) :=
        continuous_norm.comp h_Cov_cont
      have h_DecayFn_cont : Continuous (Function.uncurry DecayFn) := h_decay_cont
      have h1 : ∫ s in Set.Icc (0 : ℝ) T, ∫ u in Set.Icc (0 : ℝ) T, ‖Cov s u‖ ≤
          ∫ s in Set.Icc (0 : ℝ) T, ∫ u in Set.Icc (0 : ℝ) T, c * (1 + |s - u|)^(-(3 : ℝ)) := by
        apply MeasureTheory.setIntegral_mono_on
        · -- Integrability of s ↦ ∫ u, ‖Cov s u‖ over [0,T]
          apply Continuous.integrableOn_Icc
          exact continuous_parametric_integral_of_continuous h_CovNorm_cont isCompact_Icc
        · -- Integrability of s ↦ ∫ u, c*(1+|s-u|)^{-3} over [0,T]
          apply Continuous.integrableOn_Icc
          exact continuous_parametric_integral_of_continuous h_DecayFn_cont isCompact_Icc
        · exact measurableSet_Icc
        · intro s hs
          -- Technical integrability: ‖Cov s ·‖ and decay function are continuous hence integrable on [0,T]
          -- These follow from gff_covariance_continuous and continuity of the decay function
          -- Inner integrability follows from gff_covariance_continuous + Continuous.integrableOn_Icc
          -- but Lean times out on the type unification with the Cov definition
          have h_inner_int1 : MeasureTheory.IntegrableOn (fun u => ‖Cov s u‖) (Set.Icc 0 T) :=
            gff_covariance_norm_integrableOn_slice m f s T
          have h_inner_int2 : MeasureTheory.IntegrableOn
              (fun u => c * (1 + |s - u|)^(-(3 : ℝ))) (Set.Icc 0 T) := by
            apply Continuous.integrableOn_Icc
            exact h_decay_cont.comp (Continuous.prodMk_right s)
          exact MeasureTheory.setIntegral_mono_on h_inner_int1 h_inner_int2 measurableSet_Icc
            (fun u hu => h_cov_bound s u hs hu)
      -- Pull out constant c: ∫∫ c*f = c * ∫∫ f, then apply h_double_T
      have h2 : ∫ s in Set.Icc (0 : ℝ) T, ∫ u in Set.Icc (0 : ℝ) T, c * (1 + |s - u|)^(-(3 : ℝ)) ≤
          c * (2 * T * C) := by
        -- Pull out c from the integral
        simp_rw [MeasureTheory.integral_const_mul]
        -- Now: c * ∫∫ (1+|s-u|)^{-3} ≤ c * (2*T*C)
        exact mul_le_mul_of_nonneg_left h_double_T hc
      linarith

    -- Rewrite goal to match h_var's form
    -- The subtraction `∫ exp - mean` needs to become `(∫ exp) - mean` after scaling
    have h_goal_eq : ∀ ω, ‖(1 / T) * (∫ s in Set.Icc (0 : ℝ) T,
            Complex.exp (distributionPairingℂ_real (timeTranslationDistribution s ω) f)
          - ∫ ω', Complex.exp (distributionPairingℂ_real ω' f) ∂μ)‖^2 =
        ‖(1 / T) * (∫ s in Set.Icc (0 : ℝ) T, A s ω) - EA‖^2 := by
      intro ω
      -- (1/T) * ∫(A - EA) = (1/T) * (∫A - T*EA) = (1/T)*∫A - EA
      -- Uses: ∫_{[0,T]} EA = T * EA (constant integral over interval of length T)
      congr 2
      -- Goal: (1/T) * ∫(A - EA) = (1/T) * ∫A - EA
      -- Step 1: Split the integral: ∫(A - EA) = ∫A - ∫EA
      have h_EA_int : MeasureTheory.IntegrableOn (fun _ : ℝ => EA) (Set.Icc 0 T) MeasureTheory.volume := by
        apply MeasureTheory.integrableOn_const
        · simp only [Real.volume_Icc, sub_zero]; exact ENNReal.ofReal_ne_top
        · simp [enorm]
      have h_A_int : MeasureTheory.IntegrableOn (fun s => A s ω) (Set.Icc 0 T) MeasureTheory.volume := by
        -- A s ω = exp(⟨T_s ω, f⟩) is continuous in s (bounded on compact [0,T])
        apply Continuous.integrableOn_Icc
        exact Complex.continuous_exp.comp (continuous_distributionPairingℂ_timeTranslation ω f)
      have h_split : ∫ s in Set.Icc (0 : ℝ) T, (A s ω - EA) =
          (∫ s in Set.Icc (0 : ℝ) T, A s ω) - ∫ s in Set.Icc (0 : ℝ) T, EA :=
        MeasureTheory.integral_sub h_A_int h_EA_int
      -- Step 2: Compute ∫_{[0,T]} EA = T * EA
      have h_const_int : ∫ s in Set.Icc (0 : ℝ) T, EA = T * EA := by
        rw [MeasureTheory.setIntegral_const]
        have h_vol : MeasureTheory.volume.real (Set.Icc (0 : ℝ) T) = T := by
          simp only [MeasureTheory.Measure.real, Real.volume_Icc, sub_zero]
          exact ENNReal.toReal_ofReal (le_of_lt hT)
        rw [h_vol]
        simp only [Complex.real_smul]
      -- Step 3: Algebra: (1/T) * (∫A - T*EA) = (1/T)*∫A - EA
      rw [h_split, h_const_int]
      have hT_ne : T ≠ 0 := ne_of_gt hT
      have hT_cne : (T : ℂ) ≠ 0 := by exact_mod_cast hT_ne
      field_simp [hT_cne]
    simp_rw [h_goal_eq]
    calc ∫ ω, ‖(1 / T) * (∫ s in Set.Icc (0 : ℝ) T, A s ω) - EA‖^2 ∂μ
        ≤ (1 / T^2) * ∫ s in Set.Icc (0 : ℝ) T, ∫ u in Set.Icc (0 : ℝ) T, ‖Cov s u‖ := h_var
      _ ≤ (1 / T^2) * (c * (2 * T * C)) := by
          apply mul_le_mul_of_nonneg_left h_cov_double_bound
          positivity
      _ = 2 * c * C / T := by field_simp

  -- 2·c·C / T → 0 as T → ∞
  have h_tends : Filter.Tendsto (fun T : ℝ => 2 * c * C / T) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun T : ℝ => T⁻¹) Filter.atTop (nhds 0) := tendsto_inv_atTop_zero
    have h2 : Filter.Tendsto (fun T : ℝ => (2 * c * C) * T⁻¹) Filter.atTop (nhds ((2 * c * C) * 0)) :=
      Filter.Tendsto.const_mul (2 * c * C) h1
    simp only [mul_zero] at h2
    convert h2 using 1 with T

  -- Lower bound: variance ≥ 0
  have h_nonneg : ∀ T, 0 ≤ ∫ ω, ‖(1 / T) * ∫ s in Set.Icc (0 : ℝ) T,
      Complex.exp (distributionPairingℂ_real (timeTranslationDistribution s ω) f)
    - ∫ ω', Complex.exp (distributionPairingℂ_real ω' f) ∂μ‖^2 ∂μ := by
    intro T; apply integral_nonneg; intro; apply sq_nonneg

  -- Squeeze theorem
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_tends
  · exact Filter.Eventually.of_forall h_nonneg
  · filter_upwards [Filter.eventually_gt_atTop 0] with T hT; exact h_upper T hT

/-! ## Main Theorem Chain -/

/-- Bound for norm squared of weighted sum using Cauchy-Schwarz. -/
lemma norm_sq_weighted_sum_le {n : ℕ} (w : Fin n → ℂ) (a : Fin n → ℂ) :
    ‖∑ j, w j * a j‖^2 ≤ (∑ j, ‖w j‖^2) * (∑ j, ‖a j‖^2) := by
  have h1 : ‖∑ j, w j * a j‖ ≤ ∑ j, ‖w j‖ * ‖a j‖ := by
    calc ‖∑ j, w j * a j‖ ≤ ∑ j, ‖w j * a j‖ := norm_sum_le _ _
      _ = ∑ j, ‖w j‖ * ‖a j‖ := by simp_rw [norm_mul]
  have h2 : ‖∑ j, w j * a j‖^2 ≤ (∑ j, ‖w j‖ * ‖a j‖)^2 :=
    sq_le_sq' (by nlinarith [norm_nonneg (∑ j, w j * a j)]) h1
  have h3 : (∑ j : Fin n, ‖w j‖ * ‖a j‖)^2 ≤ (∑ j, ‖w j‖^2) * (∑ j, ‖a j‖^2) := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖w j‖) (fun j => ‖a j‖)
    simp at this; exact this
  linarith

/-- OS4' → OS4: Generating function ergodicity implies full ergodicity.

    The proof uses Cauchy-Schwarz to bound the variance of ∑ⱼ zⱼ exp(⟨ω, fⱼ⟩)
    by the sum of individual variances, then applies OS4' to each term. -/
theorem OS4'_implies_OS4 (m : ℝ) [Fact (0 < m)] :
    OS4'_Ergodicity_generating m → OS4_Ergodicity (gaussianFreeField_free m) := by
  intro h_erg n z f
  let μ := (gaussianFreeField_free m).toMeasure
  let A : FieldConfiguration → ℂ := fun ω => ∑ j, z j * Complex.exp (distributionPairingℂ_real ω (f j))

  -- Define the "error" for each generating function
  -- Note: This matches the structure in OS4'_Ergodicity_generating
  -- Parsed as: (1/T) * (∫_s (exp - mean)) where mean is constant in s
  let Err : Fin n → ℝ → FieldConfiguration → ℂ := fun j T ω =>
    (1 / T) * ∫ s in Set.Icc (0 : ℝ) T,
      Complex.exp (distributionPairingℂ_real (timeTranslationDistribution s ω) (f j))
      - ∫ ω', Complex.exp (distributionPairingℂ_real ω' (f j)) ∂μ

  -- The L² variance for each generating function fⱼ
  let Var_j : Fin n → ℝ → ℝ := fun j T =>
    ∫ ω, ‖Err j T ω‖^2 ∂μ

  -- OS4' tells us each Var_j T → 0 as T → ∞
  have h_each_tends : ∀ j, Filter.Tendsto (Var_j j) Filter.atTop (nhds 0) := fun j => h_erg (f j)

  -- The sum of Var_j tends to 0 (finite sum of convergent sequences)
  have h_sum_tends : Filter.Tendsto (fun T => ∑ j, Var_j j T) Filter.atTop (nhds 0) := by
    have := tendsto_finset_sum Finset.univ (fun j _ => h_each_tends j)
    simp at this; exact this

  -- The constant ∑|zⱼ|²
  let Z : ℝ := ∑ j, ‖z j‖^2

  -- Upper bound: variance ≤ Z · ∑ Var_j (for T > 0)
  have h_upper : ∀ T > 0, ∫ ω, ‖(1 / T) * ∫ s in Set.Icc (0 : ℝ) T, A (timeTranslationDistribution s ω)
      - ∫ ω', A ω' ∂μ‖^2 ∂μ ≤ Z * ∑ j, Var_j j T := by
    intro T hT
    -- The error for A equals ∑ⱼ zⱼ · Err_j (linearity)
    have h_err_eq : ∀ ω, (1 / T) * ∫ s in Set.Icc (0 : ℝ) T, A (timeTranslationDistribution s ω)
        - ∫ ω', A ω' ∂μ = ∑ j, z j * Err j T ω := by
      intro ω
      simp only [A, Err]
      -- Linearity: ∫ (∑ zⱼ expⱼ) = ∑ zⱼ · ∫ expⱼ, then distribute 1/T and subtraction
      -- Key lemmas: MeasureTheory.integral_finset_sum (for both integrals)
      -- Each exp(⟨T_s ω, f_j⟩) is integrable by Fernique (gff_exp_pairing_integrable)
      -- The structure is: (1/T) * ∫_s (∑ z_j exp_j - mean) = ∑_j z_j * ((1/T) * ∫_s (exp_j - mean_j))
      -- where mean = ∫_ω' (∑_j z_j exp_j) is constant in s
      -- Step 1: Expand the sum inside the time integral and pull out constant subtrahend
      -- ∫_s (∑_j (z_j * exp_j) - C) = ∫_s (∑_j (z_j * exp_j - z_j * mean_j))
      -- where we use C = ∑_j z_j * mean_j

      -- Mean as a sum
      have h_exp_int : ∀ j, Integrable
          (fun ω' => z j * Complex.exp (distributionPairingℂ_real ω' (f j))) μ := fun j => by
        apply Integrable.const_mul
        exact gff_exp_pairing_integrable m (f j)
      have h_mean_sum : ∫ ω', ∑ j, z j * Complex.exp (distributionPairingℂ_real ω' (f j)) ∂μ =
          ∑ j, z j * ∫ ω', Complex.exp (distributionPairingℂ_real ω' (f j)) ∂μ := by
        rw [MeasureTheory.integral_finset_sum Finset.univ (fun j _ => h_exp_int j)]
        simp_rw [MeasureTheory.integral_const_mul]

      -- Rewrite integrand: (∑_j z_j * exp_j) - (∑_j z_j * mean_j) = ∑_j z_j * (exp_j - mean_j)
      have h_integrand_eq : ∀ s,
          (∑ j, z j * Complex.exp (distributionPairingℂ_real (timeTranslationDistribution s ω) (f j)))
          - (∫ ω', ∑ j, z j * Complex.exp (distributionPairingℂ_real ω' (f j)) ∂μ) =
          ∑ j, z j * (Complex.exp (distributionPairingℂ_real (timeTranslationDistribution s ω) (f j))
            - ∫ ω', Complex.exp (distributionPairingℂ_real ω' (f j)) ∂μ) := by
        intro s
        rw [h_mean_sum, ← Finset.sum_sub_distrib]
        congr 1 with j
        ring

      -- The time integral of the difference
      have h_diff_int : ∀ j, MeasureTheory.IntegrableOn
          (fun s => z j * (Complex.exp (distributionPairingℂ_real (timeTranslationDistribution s ω) (f j))
            - ∫ ω', Complex.exp (distributionPairingℂ_real ω' (f j)) ∂μ))
          (Set.Icc 0 T) := fun j => by
        apply Continuous.integrableOn_Icc
        apply Continuous.mul continuous_const
        apply Continuous.sub
        · exact Complex.continuous_exp.comp (continuous_distributionPairingℂ_timeTranslation ω (f j))
        · exact continuous_const

      -- Now rewrite LHS
      simp_rw [h_integrand_eq]
      rw [MeasureTheory.integral_finset_sum Finset.univ (fun j _ => h_diff_int j)]
      simp_rw [MeasureTheory.integral_const_mul]
      rw [Finset.mul_sum]
      congr 1 with j
      ring
    -- Apply Cauchy-Schwarz pointwise
    have h_cs : ∀ ω, ‖∑ j, z j * Err j T ω‖^2 ≤ Z * ∑ j, ‖Err j T ω‖^2 :=
      fun ω => norm_sq_weighted_sum_le z (fun j => Err j T ω)
    -- Each ‖Err j T ·‖² is integrable (needed for integral_mono and integral_finset_sum)
    have h_each_int : ∀ j, Integrable (fun ω => ‖Err j T ω‖^2) μ := by
      intro j
      -- gff_err_sq_integrable gives integrability for ((1/T) • ∫ exp) - mean
      have h_int := gff_err_sq_integrable m T hT (f j)
      -- Convert from smul to mul and unfold Err
      simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one] at h_int
      -- The Err definition unfolds to the same form
      convert h_int using 2
      rename_i ω
      simp only [Err]
      -- Need: ‖(1/T) * ∫(exp - mean)‖² = ‖(1/T) * ∫ exp - mean‖²
      congr 2
      -- Define the time-translated exp and the mean
      let exp_s := fun s => Complex.exp (distributionPairingℂ_real (timeTranslationDistribution s ω) (f j))
      let mean := ∫ ω', Complex.exp (distributionPairingℂ_real ω' (f j)) ∂μ
      have h_vol_fin : volume (Set.Icc (0 : ℝ) T) ≠ ⊤ := by
        simp only [Real.volume_Icc, sub_zero, ne_eq]; exact ENNReal.ofReal_ne_top
      have h_const : ∫ s in Set.Icc (0 : ℝ) T, mean = T * mean := by
        rw [MeasureTheory.setIntegral_const]
        simp only [Measure.real, Real.volume_Icc, sub_zero]
        rw [ENNReal.toReal_ofReal (le_of_lt hT), Complex.real_smul]
      have h_exp_cont : Continuous exp_s :=
        Complex.continuous_exp.comp (continuous_distributionPairingℂ_timeTranslation ω (f j))
      have h_exp_int : MeasureTheory.IntegrableOn exp_s (Set.Icc 0 T) := h_exp_cont.integrableOn_Icc
      have h_const_int : MeasureTheory.IntegrableOn (fun _ => mean) (Set.Icc 0 T) :=
        MeasureTheory.integrableOn_const h_vol_fin
      have h_sub : ∫ s in Set.Icc (0 : ℝ) T, (exp_s s - mean) =
          (∫ s in Set.Icc (0 : ℝ) T, exp_s s) - T * mean := by
        rw [MeasureTheory.integral_sub h_exp_int h_const_int, h_const]
      simp only [exp_s, mean] at h_sub
      rw [h_sub]
      have hT_ne : (T : ℂ) ≠ 0 := by simp only [ne_eq, Complex.ofReal_eq_zero]; exact ne_of_gt hT
      field_simp
      ring
    -- RHS integrability: Z * ∑ ‖Err_j‖² where each term is integrable
    have h_sum_int : Integrable (fun ω => Z * ∑ j, ‖Err j T ω‖^2) μ := by
      apply Integrable.const_mul
      apply MeasureTheory.integrable_finset_sum
      intro j _; exact h_each_int j
    -- Each Err j T · is AEStronglyMeasurable
    -- We derive this from h_each_int: Integrable (‖Err j T ·‖²) implies AEStronglyMeasurable (Err j T ·)
    -- via: ‖f‖² integrable → ‖f‖² AEStronglyMeasurable → f AEStronglyMeasurable
    have h_err_meas : ∀ j, AEStronglyMeasurable (Err j T ·) μ := by
      intro j
      -- Use the parametric integral measurability theorem (proved in L2TimeIntegral)
      haveI : IsProbabilityMeasure μ :=
        MeasureTheory.ProbabilityMeasure.instIsProbabilityMeasureToMeasure (gaussianFreeField_free m)
      let A_j := fun s ω => Complex.exp (distributionPairingℂ_real (timeTranslationDistribution s ω) (f j))
      let EA_j := ∫ ω', Complex.exp (distributionPairingℂ_real ω' (f j)) ∂μ
      have h_cont : ∀ ω, Continuous (fun s => A_j s ω) := fun ω =>
        Complex.continuous_exp.comp (continuous_distributionPairingℂ_timeTranslation ω (f j))
      have h_meas_s : ∀ s, Measurable (A_j s) := by
        intro s
        have h_eq : (fun ω => Complex.exp (distributionPairingℂ_real (timeTranslationDistribution s ω) (f j))) =
            (fun ω => Complex.exp (distributionPairingℂ_real ω (timeTranslationSchwartzℂ (-s) (f j)))) := by
          ext ω; rw [timeTranslationDistribution_pairingℂ]
        show Measurable (A_j s)
        simp only [A_j]; rw [h_eq]
        exact (Complex.continuous_exp.comp (QFT.distributionPairingℂ_real_continuous _)).measurable
      exact OSforGFF.gff_time_integral_aestronglyMeasurable_proved μ A_j EA_j T h_cont h_meas_s
    -- LHS integrability: ‖∑ z_j * Err_j‖² is bounded by Z * ∑ ‖Err_j‖² (via h_cs)
    have h_weighted_int : Integrable (fun ω => ‖∑ j, z j * Err j T ω‖^2) μ := by
      apply Integrable.mono' h_sum_int
      · apply AEStronglyMeasurable.pow
        apply AEStronglyMeasurable.norm
        -- ∑ j, z j * Err j T · is AEStronglyMeasurable (finite sum of measurable)
        have h_sum : AEStronglyMeasurable (∑ j : Fin n, fun ω => z j * Err j T ω) μ := by
          apply Finset.aestronglyMeasurable_sum Finset.univ
          intro j _
          exact (h_err_meas j).const_smul (z j)
        convert h_sum using 1
        ext ω
        simp only [Finset.sum_apply]
      · filter_upwards with ω
        calc ‖‖∑ j, z j * Err j T ω‖ ^ 2‖ = ‖∑ j, z j * Err j T ω‖ ^ 2 := by
              rw [Real.norm_of_nonneg (sq_nonneg _)]
          _ ≤ Z * ∑ j, ‖Err j T ω‖ ^ 2 := h_cs ω
    -- Integrate
    calc ∫ ω, ‖(1 / T) * ∫ s in Set.Icc (0 : ℝ) T, A (timeTranslationDistribution s ω)
          - ∫ ω', A ω' ∂μ‖^2 ∂μ
        = ∫ ω, ‖∑ j, z j * Err j T ω‖^2 ∂μ := by congr 1 with ω; rw [h_err_eq ω]
      _ ≤ ∫ ω, Z * ∑ j, ‖Err j T ω‖^2 ∂μ := by
          apply MeasureTheory.integral_mono h_weighted_int h_sum_int
          intro ω; exact h_cs ω
      _ = Z * ∫ ω, ∑ j, ‖Err j T ω‖^2 ∂μ := by rw [← MeasureTheory.integral_const_mul]
      _ = Z * ∑ j, ∫ ω, ‖Err j T ω‖^2 ∂μ := by
          congr 1
          exact integral_finset_sum Finset.univ fun i a ↦ h_each_int i
      _ = Z * ∑ j, Var_j j T := rfl

  -- Squeeze: 0 ≤ variance ≤ Z · (∑ Var_j) → 0
  have h_nonneg : ∀ T, 0 ≤ ∫ ω, ‖(1 / T) * ∫ s in Set.Icc (0 : ℝ) T, A (timeTranslationDistribution s ω)
      - ∫ ω', A ω' ∂μ‖^2 ∂μ := fun T => MeasureTheory.integral_nonneg (fun _ => sq_nonneg _)

  have h_Z_nonneg : 0 ≤ Z := Finset.sum_nonneg (fun j _ => sq_nonneg _)

  have h_tends_upper : Filter.Tendsto (fun T => Z * ∑ j, Var_j j T) Filter.atTop (nhds 0) := by
    have := Filter.Tendsto.const_mul Z h_sum_tends
    simp only [mul_zero] at this; exact this

  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_tends_upper
  · exact Filter.Eventually.of_forall h_nonneg
  · filter_upwards [Filter.eventually_gt_atTop 0] with T hT; exact h_upper T hT

/-- OS4'' → OS4': Polynomial clustering implies generating function ergodicity. -/
theorem OS4''_implies_OS4' (m : ℝ) [Fact (0 < m)] :
    OS4''_Clustering m → OS4'_Ergodicity_generating m := by
  intro h_cluster f
  dsimp [OS4'_Ergodicity_generating]

  -- Get the covariance decay bound from clustering
  obtain ⟨c, hc_nonneg, hc_bound⟩ := clustering_implies_covariance_decay m f h_cluster

  -- Apply variance decay
  exact variance_decay_from_clustering m f c hc_nonneg hc_bound

/-- OS4'' → OS4: The full chain from clustering to ergodicity. -/
theorem OS4''_implies_OS4_Ergodicity (m : ℝ) [Fact (0 < m)] :
    OS4''_Clustering m → OS4_Ergodicity (gaussianFreeField_free m) := by
  intro h_cluster
  exact OS4'_implies_OS4 m (OS4''_implies_OS4' m h_cluster)

/-- **Main Theorem**: OS4_PolynomialClustering with α=6 implies OS4_Ergodicity for the GFF.

    This is the main result connecting the clustering axiom to ergodicity.
-/
theorem OS4_PolynomialClustering_implies_OS4_Ergodicity (m : ℝ) [Fact (0 < m)] :
    OS4_PolynomialClustering (gaussianFreeField_free m) 6 (by norm_num) →
    OS4_Ergodicity (gaussianFreeField_free m) :=
  OS4''_implies_OS4_Ergodicity m

end OS4_Ergodicity
