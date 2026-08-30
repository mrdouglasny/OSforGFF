/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Copyright (c) 2026 Sergey A. Cherkis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sergey A. Cherkis, Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/

import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Distribution.TemperateGrowth
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.Chebyshev

import OSforGFF.Spacetime.Basic
import OSforGFF.Schwinger.Defs
import OSforGFF.Measure.Construct
import OSforGFF.Measure.IsGaussian
import OSforGFF.OS.OS0_Analyticity
import OSforGFF.OS.OS2_Invariance
import OSforGFF.Spacetime.ComplexTestFunction
import OSforGFF.Spacetime.TimeTranslation
import OSforGFF.OS.Axioms

/-!
# OS4 — Shared Infrastructure

Shared lemmas for OS4_Clustering and OS4_Ergodicity:

- Time translation duality: ⟨T_s ω, g⟩ = ⟨ω, T_{−s} g⟩
- GFF MGF formula: 𝔼[e^{⟨ω,f⟩}] = exp(½ S₂(f,f)) and its time-translation invariance
- Joint MGF factorization: 𝔼[e^{⟨ω,f+T_{−s}g⟩}] = E_f · E_g · exp(S₂(f, T_{−s}g))
- Exponential bound: |e^z − 1| ≤ |z| · e^{|z|}
-/

open MeasureTheory Real OSforGFF
open TopologicalSpace
open scoped BigOperators

noncomputable section

variable {d : ℕ} [Fact (2 ≤ d)]

namespace OS4infra

/-! ## Time Translation Infrastructure

We re-export the core TimeTranslation API so that importers of OS4infra
get these names in scope without a separate TimeTranslation import.
-/

export TimeTranslation (
  timeIndex getTime timeShift timeShiftConst
  timeShift_time timeShift_spatial timeShift_add timeShift_zero timeShift_comm
  timeShift_contDiff timeShift_dist timeShift_isometry timeShift_antilipschitz
  timeShift_eq_add_const timeShift_hasTemperateGrowth
  timeTranslationSchwartzCLM timeTranslationSchwartz
  timeTranslationSchwartzℂCLM timeTranslationSchwartzℂ
  timeTranslationSchwartz_apply timeTranslationSchwartzℂ_apply
  timeTranslationSchwartz_add timeTranslationSchwartzℂ_add
  timeTranslationSchwartz_zero timeTranslationSchwartzℂ_zero
  timeTranslationSchwartz_add_fun timeTranslationSchwartz_smul
  continuous_timeTranslationSchwartz
  timeTranslationDistribution
  timeTranslationDistribution_apply timeTranslationDistribution_add timeTranslationDistribution_zero
)

/-! ## Time Translation Decomposition Lemmas -/

omit [Fact (2 ≤ d)] in
/-- Time translation commutes with real part extraction for complex Schwartz functions. -/
lemma timeTranslationSchwartzℂ_decompose_fst (s : ℝ) (g : SchwartzTestFunctionℂ d) :
    (complex_testfunction_decompose (timeTranslationSchwartzℂ s g)).1 =
    timeTranslationSchwartz s (complex_testfunction_decompose g).1 := by
  ext x
  simp only [complex_testfunction_decompose_fst_apply, timeTranslationSchwartz_apply,
    timeTranslationSchwartzℂ_apply]

omit [Fact (2 ≤ d)] in
/-- Time translation commutes with imaginary part extraction for complex Schwartz functions. -/
lemma timeTranslationSchwartzℂ_decompose_snd (s : ℝ) (g : SchwartzTestFunctionℂ d) :
    (complex_testfunction_decompose (timeTranslationSchwartzℂ s g)).2 =
    timeTranslationSchwartz s (complex_testfunction_decompose g).2 := by
  ext x
  simp only [complex_testfunction_decompose_snd_apply, timeTranslationSchwartz_apply,
    timeTranslationSchwartzℂ_apply]

omit [Fact (2 ≤ d)] in
/-- Time translation on distributions is compatible with complex pairing.
    ⟨T_s ω, g⟩_ℂ = ⟨ω, T_{-s} g⟩_ℂ -/
lemma timeTranslationDistribution_pairingℂ (s : ℝ) (ω : FieldConfiguration d)
    (g : SchwartzTestFunctionℂ d) :
    distributionPairingℂ_real (timeTranslationDistribution s ω) g =
    distributionPairingℂ_real ω (timeTranslationSchwartzℂ (-s) g) := by
  simp only [distributionPairingℂ_real]
  set g_re := (complex_testfunction_decompose g).1
  set g_im := (complex_testfunction_decompose g).2
  set g'_re := (complex_testfunction_decompose (timeTranslationSchwartzℂ (-s) g)).1
  set g'_im := (complex_testfunction_decompose (timeTranslationSchwartzℂ (-s) g)).2
  have h_re : g'_re = timeTranslationSchwartz (-s) g_re := timeTranslationSchwartzℂ_decompose_fst (-s) g
  have h_im : g'_im = timeTranslationSchwartz (-s) g_im := timeTranslationSchwartzℂ_decompose_snd (-s) g
  simp only [timeTranslationDistribution_apply]
  rw [h_re, h_im]

/-! ## Continuity of Complex Pairing under Time Translation -/

/-- s ↦ ⟨T_s ω, g⟩_ℂ is continuous. Uses the proved `continuous_timeTranslationSchwartz`. -/
lemma continuous_distributionPairingℂ_timeTranslation (ω : FieldConfiguration d)
    (g : SchwartzTestFunctionℂ d) :
    Continuous (fun s => distributionPairingℂ_real (timeTranslationDistribution s ω) g) := by
  have h_eq : (fun s => distributionPairingℂ_real (timeTranslationDistribution s ω) g)
      = (fun s => distributionPairingℂ_real ω (timeTranslationSchwartzℂ (-s) g)) := by
    ext s
    exact timeTranslationDistribution_pairingℂ s ω g
  rw [h_eq]
  simp only [distributionPairingℂ_real]
  set g_re := (complex_testfunction_decompose g).1 with hg_re
  set g_im := (complex_testfunction_decompose g).2 with hg_im
  have h_decomp_re : ∀ s, (complex_testfunction_decompose (timeTranslationSchwartzℂ (-s) g)).1
      = timeTranslationSchwartz (-s) g_re := fun s => timeTranslationSchwartzℂ_decompose_fst (-s) g
  have h_decomp_im : ∀ s, (complex_testfunction_decompose (timeTranslationSchwartzℂ (-s) g)).2
      = timeTranslationSchwartz (-s) g_im := fun s => timeTranslationSchwartzℂ_decompose_snd (-s) g
  simp only [h_decomp_re, h_decomp_im]
  apply Continuous.add
  · apply Complex.continuous_ofReal.comp
    have h_trans_cont : Continuous (fun s => timeTranslationSchwartz (-s) g_re) := by
      exact (TimeTranslation.continuous_timeTranslationSchwartz g_re).comp continuous_neg
    exact ω.continuous.comp h_trans_cont
  · apply Continuous.mul continuous_const
    apply Complex.continuous_ofReal.comp
    have h_trans_cont : Continuous (fun s => timeTranslationSchwartz (-s) g_im) := by
      exact (TimeTranslation.continuous_timeTranslationSchwartz g_im).comp continuous_neg
    exact ω.continuous.comp h_trans_cont

/-! ## Euclidean Group Infrastructure for Time Translation -/

/-- Time translation as a Euclidean group element.
    timeTranslationE t = (1, -timeShiftConst t) where 1 is the identity rotation. -/
def timeTranslationE (t : ℝ) : QFT.E d := ⟨1, -timeShiftConst t⟩

omit [Fact (2 ≤ d)] in
/-- The Euclidean action of timeTranslationE equals timeTranslationSchwartzℂ. -/
lemma euclidean_action_timeTranslationE (t : ℝ) (f : SchwartzTestFunctionℂ d) :
    QFT.euclidean_action (timeTranslationE t) f = timeTranslationSchwartzℂ t f := by
  ext x
  simp only [QFT.euclidean_action_apply, QFT.euclidean_pullback_eq_inv_act]
  simp only [timeTranslationE, QFT.act]
  simp only [timeTranslationSchwartzℂ_apply, timeShift_eq_add_const]
  congr 1
  simp only [QFT.inv_R, QFT.inv_t, QFT.LinearIsometry.inv]
  have h1 : ∀ v, (LinearIsometry.toLinearIsometryEquiv (1 : QFT.O d) rfl).symm v = v := fun v => by
    have hv : (LinearIsometry.toLinearIsometryEquiv (1 : QFT.O d) rfl) v = v := rfl
    rw [← hv]; exact LinearIsometryEquiv.symm_apply_apply _ v
  simp only [LinearIsometryEquiv.coe_toLinearIsometry, h1, neg_neg]

/-! ## GFF Covariance Invariance -/

/-- The GFF covariance is invariant under simultaneous time translation. -/
lemma freeCovarianceℂ_bilinear_timeTranslation_invariant (m : ℝ) [Fact (0 < m)] [GFFPropagator d m] (t : ℝ)
    (f g : SchwartzTestFunctionℂ d) :
    freeCovarianceℂ_bilinear m (timeTranslationSchwartzℂ t f) (timeTranslationSchwartzℂ t g) =
    freeCovarianceℂ_bilinear m f g := by
  rw [← euclidean_action_timeTranslationE t f, ← euclidean_action_timeTranslationE t g]
  exact QFT.freeCovarianceℂ_bilinear_euclidean_invariant m (timeTranslationE t) f g

/-! ## GFF Moment Generating Function -/

/-- MGF formula for GFF: ∫ exp(⟨ω,J⟩) dμ = exp(+(1/2) * C(J,J)).
    This follows from the characteristic function formula via substitution J → (-I)•J. -/
lemma gff_mgf_formula (m : ℝ) [Fact (0 < m)] [GFFPropagator d m] (J : SchwartzTestFunctionℂ d) :
    (∫ ω, Complex.exp (distributionPairingℂ_real ω J) ∂(gaussianFreeField_free m).toMeasure) =
    Complex.exp ((1/2 : ℂ) * freeCovarianceℂ_bilinear m J J) := by
  let negI : ℂ := -Complex.I
  have h_to_cf : (∫ ω, Complex.exp (distributionPairingℂ_real ω J)
      ∂(gaussianFreeField_free m).toMeasure) =
      GJGeneratingFunctionalℂ (gaussianFreeField_free m) (negI • J) := by
    unfold GJGeneratingFunctionalℂ
    congr 1
    ext ω
    congr 1
    have h_lin : distributionPairingℂ_real ω (negI • J) =
        negI * distributionPairingℂ_real ω J := by
      have := pairing_linear_combo ω J 0 negI 0
      simp at this
      exact this
    rw [h_lin]
    simp only [negI]
    ring_nf
    simp [Complex.I_sq]
  rw [h_to_cf, GFFIsGaussian.gff_complex_characteristic_OS0 m]
  have h_cov : freeCovarianceℂ_bilinear m (negI • J) (negI • J) =
      -freeCovarianceℂ_bilinear m J J := by
    rw [freeCovarianceℂ_bilinear_smul_left, freeCovarianceℂ_bilinear_smul_right]
    simp only [negI]
    ring_nf
    simp [Complex.I_sq]
  rw [h_cov]
  ring_nf

/-- The GFF generating function is invariant under time translation. -/
lemma gff_generating_time_invariant (m : ℝ) [Fact (0 < m)] [GFFPropagator d m] (s : ℝ) (f : SchwartzTestFunctionℂ d) :
    ∫ ω, Complex.exp (distributionPairingℂ_real ω (timeTranslationSchwartzℂ s f))
      ∂(gaussianFreeField_free m).toMeasure =
    ∫ ω, Complex.exp (distributionPairingℂ_real ω f)
      ∂(gaussianFreeField_free m).toMeasure := by
  rw [gff_mgf_formula, gff_mgf_formula]
  rw [freeCovarianceℂ_bilinear_timeTranslation_invariant m s f f]

/-! ## Joint MGF Factorization -/

/-- Joint MGF factorization for GFF.
    E[e^{⟨ω,f⟩+⟨ω,g⟩}] = E[e^{⟨ω,f⟩}] E[e^{⟨ω,g⟩}] e^{C(f,g)}
    This follows from the GFF being Gaussian. -/
lemma gff_joint_mgf_factorization (m : ℝ) [Fact (0 < m)] [GFFPropagator d m] (f g : SchwartzTestFunctionℂ d) :
    (∫ ω, Complex.exp (distributionPairingℂ_real ω f + distributionPairingℂ_real ω g)
      ∂(gaussianFreeField_free m).toMeasure) =
    (∫ ω, Complex.exp (distributionPairingℂ_real ω f) ∂(gaussianFreeField_free m).toMeasure) *
    (∫ ω, Complex.exp (distributionPairingℂ_real ω g) ∂(gaussianFreeField_free m).toMeasure) *
    Complex.exp (SchwingerFunctionℂ₂ (gaussianFreeField_free m) f g) := by
  have h_pairing_add : ∀ ω, distributionPairingℂ_real ω f + distributionPairingℂ_real ω g =
      distributionPairingℂ_real ω (f + g) := by
    intro ω
    have := pairing_linear_combo ω f g 1 1
    simp at this
    exact this.symm
  have h_lhs : (∫ ω, Complex.exp (distributionPairingℂ_real ω f + distributionPairingℂ_real ω g)
      ∂(gaussianFreeField_free m).toMeasure) =
      (∫ ω, Complex.exp (distributionPairingℂ_real ω (f + g))
      ∂(gaussianFreeField_free m).toMeasure) := by
    congr 1; ext ω; rw [h_pairing_add]
  rw [h_lhs]
  rw [gff_mgf_formula, gff_mgf_formula, gff_mgf_formula]
  rw [gff_two_point_equals_covarianceℂ_free]
  rw [freeCovarianceℂ_bilinear_add_left, freeCovarianceℂ_bilinear_add_right,
      freeCovarianceℂ_bilinear_add_right]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  have h_sym : freeCovarianceℂ_bilinear m g f = freeCovarianceℂ_bilinear m f g :=
    freeCovarianceℂ_bilinear_symm m g f
  rw [h_sym]
  ring

/-! ## Exponential Bound -/

/-- ‖e^x - 1‖ ≤ ‖x‖ · e^{‖x‖} for complex x. -/
lemma exp_sub_one_bound_general (x : ℂ) : ‖Complex.exp x - 1‖ ≤ ‖x‖ * Real.exp ‖x‖ := by
  have h1 : ‖Complex.exp x - 1‖ ≤ Real.exp ‖x‖ - 1 := by
    have h := Complex.norm_exp_sub_sum_le_exp_norm_sub_sum x 1
    simp only [Finset.range_one, Finset.sum_singleton, pow_zero, Nat.factorial_zero,
               Nat.cast_one, div_one] at h
    exact h
  have h2 : Real.exp ‖x‖ - 1 ≤ ‖x‖ * Real.exp ‖x‖ := by
    have hr := norm_nonneg x
    have hexp_pos := Real.exp_pos ‖x‖
    by_cases hr1 : ‖x‖ ≤ 1
    · have : 1 - Real.exp (-‖x‖) ≤ ‖x‖ := by
        have h := Real.add_one_le_exp (-‖x‖)
        linarith
      calc Real.exp ‖x‖ - 1
          = Real.exp ‖x‖ * (1 - Real.exp (-‖x‖)) := by
            rw [Real.exp_neg]
            field_simp
        _ ≤ Real.exp ‖x‖ * ‖x‖ := by
            apply mul_le_mul_of_nonneg_left this (le_of_lt hexp_pos)
        _ = ‖x‖ * Real.exp ‖x‖ := mul_comm _ _
    · push Not at hr1
      calc Real.exp ‖x‖ - 1
          ≤ Real.exp ‖x‖ := by linarith [hexp_pos]
        _ ≤ ‖x‖ * Real.exp ‖x‖ := by
            have h1 : 1 ≤ ‖x‖ := le_of_lt hr1
            exact (le_mul_iff_one_le_left hexp_pos).mpr h1
  linarith

end OS4infra
