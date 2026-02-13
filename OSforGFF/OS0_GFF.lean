/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/

import Mathlib.Tactic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic


import OSforGFF.Basic
import OSforGFF.Schwinger
import OSforGFF.OS_Axioms
import OSforGFF.GFFMconstruct
import OSforGFF.ComplexTestFunction
import Mathlib.MeasureTheory.Measure.Complex
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Topology.Algebra.Module.Basic

/-!
# OS0 Analyticity Axiom

This file contains the proof that the Gaussian Free Field satisfies the OS0 axiom
(analyticity of the generating functional).

## Main Results

- `gaussianFreeField_satisfies_OS0`: The GFF generating functional is analytic.

## Mathematical Background

For a Gaussian measure with covariance C, the generating functional is:
  Z[f] = exp(-½⟨f, Cf⟩)

This is analytic in f because:
1. The bilinear form ⟨f, Cf⟩ is continuous
2. The exponential of an analytic function is analytic
3. Finite sums/linear combinations preserve analyticity
-/

noncomputable section

/-! ## Axioms in this file

This file contains the following axiom:
- `differentiable_analyticAt_finDim`: Goursat's theorem in n dimensions (Hartogs' theorem)
-/

open MeasureTheory Complex BigOperators SchwartzMap
open scoped MeasureTheory ComplexConjugate

namespace QFT

/-! ## Analyticity Theorem

The key mathematical fact is that the exponential of a continuous quadratic form
is analytic.
-/


open MeasureTheory Complex

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

/-! ### Multivariate Case

The multivariate case uses the same differentiation-under-the-integral approach.
For functions `f : (Fin n → ℂ) → Ω → ℂ` where each fiber is ℂ-analytic, we show
the integral is ℂ-differentiable everywhere, hence analytic.

The key insight is that `Fin n → ℂ` is a finite-dimensional ℂ-vector space,
so analyticity is equivalent to being everywhere ℂ-differentiable. -/

/-- Axiom: A ℂ-differentiable function on a finite-dimensional complex space is analytic
    (Goursat's theorem in n dimensions). -/
axiom differentiable_analyticAt_finDim
    {n : ℕ}
    (f : (Fin n → ℂ) → ℂ)
    (hf : Differentiable ℂ f)
    (z : Fin n → ℂ) :
    AnalyticAt ℂ f z

/-- Multivariate holomorphic integral theorem: If `f : (Fin n → ℂ) → Ω → ℂ` is analytic
in `z` for each `w`, has locally bounded L¹ norm, and its Fréchet derivative satisfies
local integrable bounds, then the integral `F z = ∫ f z w ∂μ` is analytic in `z`.

This is the multivariate generalization needed for OS0, where we have n complex
parameters z₁, ..., zₙ.

The key hypotheses are:
- `h_fderiv_bound`: For each z₀, there exists ε > 0 and an integrable bound such that
  the Fréchet derivative is bounded by this function on the ball around z₀
- `h_int`: The function f(z₀, ·) is integrable
- `h_fderiv_meas`: The Fréchet derivative is measurable in the second argument -/
theorem holomorphic_integral_of_locally_L1_bound
    {n : ℕ}
    (f : (Fin n → ℂ) → Ω → ℂ)
    (h_meas : ∀ z, AEStronglyMeasurable (f z) μ)
    (h_analytic : ∀ w z₀, AnalyticAt ℂ (fun z => f z w) z₀)
    (h_int : ∀ z₀, Integrable (f z₀) μ)
    (h_fderiv_meas : ∀ z₀, AEStronglyMeasurable (fun w => fderiv ℂ (f · w) z₀) μ)
    (h_fderiv_bound : ∀ z₀ : Fin n → ℂ, ∃ ε > 0, ∃ bound : Ω → ℝ, Integrable bound μ ∧
      ∀ᵐ w ∂μ, ∀ z ∈ Metric.ball z₀ ε, ‖fderiv ℂ (f · w) z‖ ≤ bound w) :
    AnalyticOn ℂ (fun z => ∫ w, f z w ∂μ) Set.univ := by
  -- Strategy: show differentiability everywhere and convert via Hartogs' axiom
  intro z₀ _
  apply AnalyticAt.analyticWithinAt
  apply differentiable_analyticAt_finDim
  intro z₀
  -- Get the Fréchet derivative bound from the hypothesis
  obtain ⟨ε, hε_pos, bound, h_bound_int, h_fderiv_bnd⟩ := h_fderiv_bound z₀
  -- Each fiber has a Fréchet derivative
  have h_has_fderiv : ∀ᵐ w ∂μ, ∀ z ∈ Metric.ball z₀ ε, HasFDerivAt (f · w) (fderiv ℂ (f · w) z) z := by
    filter_upwards with w z _hz
    exact ((h_analytic w z).differentiableAt).hasFDerivAt
  -- Apply hasFDerivAt_integral_of_dominated_of_fderiv_le
  have h_result := hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℂ) (Metric.ball_mem_nhds z₀ hε_pos)
    (by exact Filter.Eventually.of_forall h_meas)
    (h_int z₀)
    (h_fderiv_meas z₀)
    h_fderiv_bnd
    h_bound_int
    h_has_fderiv
  exact h_result.differentiableAt

/-! ## OS0 for the Gaussian Free Field -/

/-! ### Axioms for GFF Generating Functional Analyticity

These axioms capture the preconditions needed to apply the holomorphic integral theorem
to the GFF generating functional. The generating functional is:

  Z[J] = ∫ exp(i⟨ω, J⟩) dμ(ω)

where dμ is the Gaussian measure on field configurations.
-/

variable (m : ℝ) [Fact (0 < m)]

/-- The complex pairing is continuous in ω.
    This follows from the continuity of the evaluation map on WeakDual. -/
theorem distributionPairingℂ_real_continuous (f : TestFunctionℂ) :
    Continuous (fun ω : FieldConfiguration => distributionPairingℂ_real ω f) := by
  -- distributionPairingℂ_real ω f = ω f_re + I * ω f_im
  -- where f_re = schwartz_comp_clm f reCLM and f_im = schwartz_comp_clm f imCLM
  simp only [distributionPairingℂ_real, complex_testfunction_decompose]
  -- Now we need: Continuous (ω ↦ ↑(ω (schwartz_comp_clm f reCLM)) + I * ↑(ω (schwartz_comp_clm f imCLM)))
  -- Each evaluation ω ↦ ω g is continuous by WeakDual.eval_continuous
  have h_re : Continuous (fun ω : FieldConfiguration => (ω (schwartz_comp_clm f Complex.reCLM) : ℂ)) :=
    Complex.continuous_ofReal.comp (WeakDual.eval_continuous _)
  have h_im : Continuous (fun ω : FieldConfiguration => (ω (schwartz_comp_clm f Complex.imCLM) : ℂ)) :=
    Complex.continuous_ofReal.comp (WeakDual.eval_continuous _)
  -- The full pairing is a continuous combination
  exact h_re.add (continuous_const.mul h_im)

/-- The GFF integrand for the generating functional is measurable in ω for each z. -/
theorem gff_integrand_measurable
    (n : ℕ) (J : Fin n → TestFunctionℂ) (z : Fin n → ℂ) :
    AEStronglyMeasurable
      (fun ω : FieldConfiguration =>
        Complex.exp (Complex.I * distributionPairingℂ_real ω (∑ i, z i • J i)))
      (μ_GFF m).toMeasure := by
  -- The integrand is exp(I * pairing(ω, ∑ z_i • J_i))
  -- 1. pairing is continuous in ω (just proved above)
  have h_pairing_cont : Continuous
      (fun ω : FieldConfiguration => distributionPairingℂ_real ω (∑ i, z i • J i)) :=
    distributionPairingℂ_real_continuous (∑ i, z i • J i)
  -- 2. Multiplication by I is continuous
  have h_mul_I_cont : Continuous
      (fun ω : FieldConfiguration => Complex.I * distributionPairingℂ_real ω (∑ i, z i • J i)) :=
    continuous_const.mul h_pairing_cont
  -- 3. exp is continuous
  have h_exp_cont : Continuous
      (fun ω : FieldConfiguration =>
        Complex.exp (Complex.I * distributionPairingℂ_real ω (∑ i, z i • J i))) :=
    Complex.continuous_exp.comp h_mul_I_cont
  -- Continuous functions are strongly measurable
  exact h_exp_cont.aestronglyMeasurable

/-- The GFF integrand is analytic in z for each fixed field configuration ω.
    This follows from the fact that:
    1. z ↦ ∑ᵢ zᵢ • Jᵢ is linear (hence analytic) in z
    2. ω ↦ ⟨ω, f⟩ is linear in f
    3. exp(i · _) is entire -/
theorem gff_integrand_analytic
    (n : ℕ) (J : Fin n → TestFunctionℂ) (ω : FieldConfiguration) (z₀ : Fin n → ℂ) :
    AnalyticAt ℂ
      (fun z : Fin n → ℂ =>
        Complex.exp (Complex.I * distributionPairingℂ_real ω (∑ i, z i • J i)))
      z₀ := by
  -- The function is exp ∘ (I * pairing ∘ linear_combination)
  -- Each component is analytic, and composition of analytic functions is analytic
  -- exp is entire, so we need to show the argument is analytic
  apply AnalyticAt.cexp
  -- Now show I * distributionPairingℂ_real ω (∑ i, z i • J i) is analytic in z
  apply AnalyticAt.mul
  · -- Complex.I is constant, hence analytic
    exact analyticAt_const
  · -- distributionPairingℂ_real ω (∑ i, z i • J i) is analytic in z
    -- The function z ↦ distributionPairingℂ_real ω (∑ i, z i • J i) is linear in z
    -- because distributionPairingℂ_real is linear in its test function argument
    -- and the sum is linear in z.

    -- A linear function from a finite-dimensional space to ℂ is analytic.
    -- The function is: z ↦ ∑ i, z i * (distributionPairingℂ_real ω (J i))
    -- which is a finite sum of z i times constants.

    -- Rewrite using linearity of distributionPairingℂ_real
    have h_linear : ∀ z : Fin n → ℂ, distributionPairingℂ_real ω (∑ i, z i • J i) =
        ∑ i, z i * distributionPairingℂ_real ω (J i) := fun z => by
      -- distributionPairingℂ_real is linear in the test function
      -- Use pairing_linear_combo: pairing(t•f + s•g) = t * pairing(f) + s * pairing(g)
      -- First establish the basic linearity properties
      have h_add : ∀ f g : TestFunctionℂ, distributionPairingℂ_real ω (f + g) =
          distributionPairingℂ_real ω f + distributionPairingℂ_real ω g := fun f g => by
        have := pairing_linear_combo ω f g 1 1
        simp at this
        exact this
      have h_smul : ∀ (c : ℂ) (f : TestFunctionℂ), distributionPairingℂ_real ω (c • f) =
          c * distributionPairingℂ_real ω f := fun c f => by
        have := pairing_linear_combo ω f 0 c 0
        simp at this
        exact this
      have h_zero : distributionPairingℂ_real ω 0 = 0 := by
        have := pairing_linear_combo ω 0 0 0 0
        simp at this
        exact this
      -- Use Finset.induction_on for the sum
      have h_gen : ∀ (s : Finset (Fin n)),
          distributionPairingℂ_real ω (∑ i ∈ s, z i • J i) =
          ∑ i ∈ s, z i * distributionPairingℂ_real ω (J i) := by
        intro s
        induction s using Finset.induction_on with
        | empty => simp [h_zero]
        | insert i s hi ih =>
          rw [Finset.sum_insert hi, Finset.sum_insert hi]
          rw [h_add, h_smul, ih]
      exact h_gen Finset.univ
    -- Now show ∑ i, z i * c_i is analytic (it's a polynomial)
    simp_rw [h_linear]
    -- Use Finset.analyticAt_fun_sum: if each f_i is analytic, then z ↦ ∑ i, f_i z is analytic
    apply Finset.analyticAt_fun_sum
    intro i _
    -- Show z ↦ z i * c_i is analytic
    apply AnalyticAt.mul
    · -- z ↦ z i is a continuous linear map (projection), hence analytic
      exact ContinuousLinearMap.analyticAt (ContinuousLinearMap.proj (R := ℂ) i) z₀
    · -- c_i = distributionPairingℂ_real ω (J i) is a constant function in z
      exact analyticAt_const

/-- The norm of exp(I * distributionPairingℂ_real ω f) equals exp(-(ω f_im))
    where f_im is the imaginary part of the complex test function.

    Proof: For a complex test function f with real/imaginary parts f_re, f_im:
    - distributionPairingℂ_real ω f = (ω f_re) + I * (ω f_im)
    - I * distributionPairingℂ_real ω f = I * (ω f_re) - (ω f_im)
    - Re(I * distributionPairingℂ_real ω f) = -(ω f_im)
    - ‖exp(z)‖ = exp(Re(z)), so ‖exp(I * ...)‖ = exp(-(ω f_im)) -/
lemma norm_exp_I_distributionPairingℂ_real (f : TestFunctionℂ) (ω : FieldConfiguration) :
    ‖Complex.exp (Complex.I * distributionPairingℂ_real ω f)‖ =
      Real.exp (-(ω (complex_testfunction_decompose f).2)) := by
  -- Use Complex.norm_exp: ‖exp(z)‖ = exp(z.re)
  rw [Complex.norm_exp]
  -- Need to show: (I * distributionPairingℂ_real ω f).re = -(ω f_im)
  congr 1
  -- Expand distributionPairingℂ_real
  simp only [distributionPairingℂ_real, complex_testfunction_decompose]
  -- I * ((ω f_re : ℂ) + I * (ω f_im : ℂ)) = I * (ω f_re) - (ω f_im)
  -- The real part is -(ω f_im)
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.add_re, Complex.ofReal_re,
             Complex.add_im, Complex.ofReal_im, Complex.mul_im]
  ring

/-- Integrability of exp(-ω f) for a real test function f under the GFF measure.
    This follows from the Gaussian nature: for centered Gaussian X with variance σ²,
    E[exp(-X)] = exp(σ²/2). -/
lemma gff_exp_neg_pairing_integrable (f : TestFunction) :
    Integrable (fun ω : FieldConfiguration => Real.exp (-(ω f)))
      (μ_GFF m).toMeasure := by
  -- Use the exponential square integrability axiom
  -- For any α > 0, exp(α x²) is integrable, and exp(-x) ≤ exp(α x² + 1/(4α))
  obtain ⟨α, hα_pos, h_integ⟩ := gaussianFreeField_pairing_expSq_integrable m f
  -- exp(-x) ≤ exp(α x² + 1/(4α)) by completing the square: -x = -(√α x - 1/(2√α))² + α x² + 1/(4α)
  have h_bound : ∀ x : ℝ, Real.exp (-x) ≤ Real.exp (1 / (4 * α)) * Real.exp (α * x^2) := fun x => by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    -- Need: -x ≤ 1/(4α) + α x²
    -- This is equivalent to: α x² + x + 1/(4α) ≥ 0
    -- Which is (√α x + 1/(2√α))² ≥ 0
    have h : α * x^2 + x + 1 / (4 * α) = (Real.sqrt α * x + 1 / (2 * Real.sqrt α))^2 := by
      have hα_sqrt : Real.sqrt α > 0 := Real.sqrt_pos.mpr hα_pos
      have hα_ne : Real.sqrt α ≠ 0 := ne_of_gt hα_sqrt
      field_simp
      rw [Real.sq_sqrt (le_of_lt hα_pos)]
      ring
    linarith [sq_nonneg (Real.sqrt α * x + 1 / (2 * Real.sqrt α))]
  -- The dominating function g(ω) = exp(1/(4α)) * exp(α (ω f)²) is integrable
  have h_dom_integrable : Integrable
      (fun ω => Real.exp (1 / (4 * α)) * Real.exp (α * (distributionPairingCLM f ω)^2))
      (μ_GFF m).toMeasure := h_integ.const_mul (Real.exp (1 / (4 * α)))
  -- exp(-ω f) is measurable
  have h_meas : AEStronglyMeasurable (fun ω : FieldConfiguration => Real.exp (-(ω f)))
      (μ_GFF m).toMeasure :=
    (Continuous.comp Real.continuous_exp (Continuous.neg (WeakDual.eval_continuous f))).aestronglyMeasurable
  -- Pointwise bound: ‖exp(-ω f)‖ ≤ exp(1/(4α)) * exp(α (ω f)²)
  have h_ae_bound : ∀ᵐ ω ∂(μ_GFF m).toMeasure,
      ‖Real.exp (-(ω f))‖ ≤ Real.exp (1 / (4 * α)) * Real.exp (α * (distributionPairingCLM f ω)^2) := by
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    simp only [distributionPairingCLM_apply, distributionPairing]
    exact h_bound (ω f)
  -- Apply Integrable.mono'
  exact h_dom_integrable.mono' h_meas h_ae_bound

/-- exp(|ω f|) is in L^2 (and in fact all L^p) under the GFF measure.
    This follows from Fernique's theorem: if exp(α x²) is integrable, then exp(|x|)^p is integrable
    for all p < ∞ because |x|^p ≤ C_p * exp(ε x²) for small ε. -/
lemma gff_exp_abs_pairing_memLp (f : TestFunction) (p : ENNReal) (hp : p ≠ ⊤) :
    MemLp (fun ω : FieldConfiguration => Real.exp |ω f|) p (μ_GFF m).toMeasure := by
  -- By Fernique, ∃ α > 0 such that exp(α x²) is integrable
  obtain ⟨α, hα_pos, h_fernique⟩ := gaussianFreeField_pairing_expSq_integrable m f
  -- For any p < ∞, we use exp(|x|)^p = exp(p|x|) ≤ exp(p²/(4α)) * exp(α x²)
  -- because p|x| ≤ p²/(4α) + α x² by AM-GM: 2√(p|x| * α x²) ≤ p|x| + α x²
  -- Actually, more directly: p|x| = (p/(2√α)) * (2√α |x|) ≤ p²/(4α) + α x²
  -- So exp(p|x|) ≤ exp(p²/(4α)) * exp(α x²)
  -- Thus ∫ exp(p|x|)^1 ≤ C * ∫ exp(α x²) < ∞

  -- For the formal proof, we establish L¹ first (which we already have) then bootstrap
  -- The MemLp condition requires showing ∫ ‖exp(|ω f|)‖^p < ∞

  -- Case split on whether p = 0 (trivial) or p > 0
  rcases eq_or_ne p 0 with rfl | hp_pos
  · exact memLp_zero_iff_aestronglyMeasurable.mpr
      (Real.continuous_exp.comp (continuous_abs.comp (WeakDual.eval_continuous f))).aestronglyMeasurable

  -- For 0 < p < ∞, we need ∫ (exp |x|)^p dμ < ∞
  -- (exp |x|)^p = exp(p * |x|), and for p finite this is bounded by C * exp(α x²)
  -- The detailed proof uses Young's inequality: p|x| ≤ p²/(4α) + α x²

  -- Here we use the fact that for any test function, linear functionals on Gaussian
  -- measures have all moments finite, so any polynomial growth times exponential decay
  -- is integrable. We axiomatize this as part of the Fernique condition.

  -- For now, use the fact that we have L¹ integrability and the function is AE bounded
  -- by a multiple of exp(α x²) which is integrable
  have h_aesm : AEStronglyMeasurable (fun ω => Real.exp |ω f|) (μ_GFF m).toMeasure :=
    (Real.continuous_exp.comp (continuous_abs.comp (WeakDual.eval_continuous f))).aestronglyMeasurable

  -- The core estimate: exp(p|x|) ≤ C * exp(α x²) for some C depending on p and α
  -- This follows from: p|x| ≤ p²/(4α) + α x² (Young's inequality)
  -- So exp(p|x|) ≤ exp(p²/(4α)) * exp(α x²)
  -- The proof: ‖exp(|x|)‖^p = exp(p.toReal * |x|) ≤ C * exp(α x²) for Young's constant C
  -- Therefore ∫ ‖exp(|x|)‖^p dμ ≤ C * ∫ exp(α x²) dμ < ∞

  -- Young's inequality: for α > 0 and any real r, we have r|x| ≤ r²/(4α) + α x²
  -- This follows from (r/(2√α) - √α|x|)² ≥ 0
  have h_young : ∀ x : ℝ, p.toReal * |x| ≤ p.toReal^2 / (4 * α) + α * x^2 := fun x => by
    have hα_ne : α ≠ 0 := ne_of_gt hα_pos
    have h_sqrt_pos : Real.sqrt α > 0 := Real.sqrt_pos.mpr hα_pos
    have h_sqrt_sq : Real.sqrt α ^ 2 = α := Real.sq_sqrt (le_of_lt hα_pos)
    -- Let a = p/(2√α), b = √α|x|. Then (a-b)² ≥ 0 gives a² + b² ≥ 2ab = p|x|
    have ha : p.toReal / (2 * Real.sqrt α) = p.toReal / 2 / Real.sqrt α := by ring
    have hb_sq : (Real.sqrt α * |x|)^2 = α * x^2 := by rw [mul_pow, h_sqrt_sq, sq_abs]
    have ha_sq : (p.toReal / (2 * Real.sqrt α))^2 = p.toReal^2 / (4 * α) := by
      rw [div_pow, mul_pow, h_sqrt_sq]; ring
    have hab : 2 * (p.toReal / (2 * Real.sqrt α)) * (Real.sqrt α * |x|) = p.toReal * |x| := by
      field_simp
    have h_sq := sq_nonneg (p.toReal / (2 * Real.sqrt α) - Real.sqrt α * |x|)
    calc p.toReal * |x| = 2 * (p.toReal / (2 * Real.sqrt α)) * (Real.sqrt α * |x|) := hab.symm
      _ ≤ (p.toReal / (2 * Real.sqrt α))^2 + (Real.sqrt α * |x|)^2 := by nlinarith [h_sq]
      _ = p.toReal^2 / (4 * α) + α * x^2 := by rw [ha_sq, hb_sq]

  -- Exponential bound: exp(p|x|) ≤ exp(p²/(4α)) * exp(α x²)
  have h_exp_bound : ∀ x : ℝ,
      Real.exp (p.toReal * |x|) ≤ Real.exp (p.toReal^2 / (4 * α)) * Real.exp (α * x^2) := fun x => by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (h_young x)

  -- The constant C = exp(p²/(4α))
  let C := Real.exp (p.toReal^2 / (4 * α))

  -- The dominating function C * exp(α x²) is integrable
  have h_dom : Integrable (fun ω => C * Real.exp (α * (ω f)^2)) (μ_GFF m).toMeasure := by
    have h_const_mul : Integrable (fun ω => C * Real.exp (α * (distributionPairingCLM f ω)^2)) (μ_GFF m).toMeasure := by
      exact h_fernique.const_mul C
    simp only [distributionPairingCLM_apply, distributionPairing] at h_const_mul
    exact h_const_mul

  -- For the MemLp construction, we need snorm to be finite
  -- snorm f p μ = (∫ ‖f‖^p)^(1/p) for p ∈ (0, ∞)
  -- ‖exp(|x|)‖^p = exp(|x|)^p = exp(p * |x|)

  -- The key: exp(p|ω f|) ≤ C * exp(α (ω f)²) and RHS is integrable
  have h_norm_pow_bound : ∀ ω : FieldConfiguration,
      Real.exp (p.toReal * |ω f|) ≤ C * Real.exp (α * (ω f)^2) := fun ω => by
    have h1 := h_exp_bound (ω f)
    exact h1

  -- Integrability of exp(p|ω f|) follows from domination
  have h_exp_p_integrable : Integrable (fun ω => Real.exp (p.toReal * |ω f|)) (μ_GFF m).toMeasure := by
    have h_meas : AEStronglyMeasurable (fun ω => Real.exp (p.toReal * |ω f|)) (μ_GFF m).toMeasure :=
      (Real.continuous_exp.comp (continuous_const.mul (continuous_abs.comp
        (WeakDual.eval_continuous f)))).aestronglyMeasurable
    -- Use Integrable.mono': if g is integrable and ‖f‖ ≤ g a.e., then f is integrable
    apply h_dom.mono' h_meas
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact h_norm_pow_bound ω

  -- Now we construct MemLp using the snorm condition
  -- For 0 < p < ∞, MemLp f p μ iff AEStronglyMeasurable f μ ∧ snorm f p μ < ⊤
  -- snorm f p μ = (∫ ‖f‖^p.toReal)^(1/p.toReal) when 0 < p < ⊤

  -- The key observation: ‖exp(|x|)‖^(p.toReal) = exp(p.toReal * |x|)
  have h_norm_rpow : ∀ x : ℝ, ‖Real.exp |x|‖ ^ p.toReal = Real.exp (p.toReal * |x|) := fun x => by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [← Real.exp_mul]
    congr 1
    ring

  -- Convert integrability of exp(p|x|) to eLpNorm bound
  -- Using: eLpNorm f p μ < ∞ ↔ ∫⁻ ‖f‖ₑ^p ∂μ < ∞
  have h_eLpNorm_lt : eLpNorm (fun ω => Real.exp |ω f|) p (μ_GFF m).toMeasure < ⊤ := by
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp_pos hp]
    -- Need: ∫⁻ ‖exp(|ω f|)‖ₑ^p < ⊤
    -- Since ‖exp(|x|)‖ₑ = exp(|x|), we have ‖exp(|x|)‖ₑ^p = exp(p|x|)
    -- and exp(p|x|) is integrable by h_exp_p_integrable
    have h_eq : ∀ ω : FieldConfiguration,
        (‖Real.exp |ω f|‖ₑ : ENNReal) ^ p.toReal = ENNReal.ofReal (Real.exp (p.toReal * |ω f|)) := by
      intro ω
      have h_pos : 0 < Real.exp |ω f| := Real.exp_pos _
      rw [Real.enorm_eq_ofReal (le_of_lt h_pos)]
      rw [ENNReal.ofReal_rpow_of_nonneg (le_of_lt h_pos) (ENNReal.toReal_nonneg)]
      congr 1
      -- exp(|x|)^p = exp(p * |x|)
      rw [← Real.exp_mul]
      ring_nf
    simp_rw [h_eq]
    -- Use that integrability implies lintegral is finite
    have h_fin := h_exp_p_integrable.hasFiniteIntegral
    rw [HasFiniteIntegral] at h_fin
    convert h_fin using 1
    apply lintegral_congr
    intro ω
    rw [Real.enorm_eq_ofReal (le_of_lt (Real.exp_pos _))]

  exact ⟨h_aesm, h_eLpNorm_lt⟩

/-- Integrability of exp(|ω f|) under the GFF measure.
    This is the L¹ special case of gff_exp_abs_pairing_memLp. -/
lemma gff_exp_abs_pairing_integrable (f : TestFunction) :
    Integrable (fun ω : FieldConfiguration => Real.exp |ω f|) (μ_GFF m).toMeasure :=
  memLp_one_iff_integrable.mp (gff_exp_abs_pairing_memLp m f 1 ENNReal.one_ne_top)

/-- Product of exponentials of absolute pairings is in L².
    If we have k test functions g₁, ..., gₖ, then exp(∑ᵢ |ω gᵢ|) = ∏ᵢ exp(|ω gᵢ|).
    Each exp(|ω gᵢ|) ∈ L^(2k) by gff_exp_abs_pairing_memLp.
    By generalized Hölder (MemLp.prod'), a product of k functions in L^(2k) is in L². -/
lemma gff_exp_abs_sum_memLp {ι : Type*} (s : Finset ι) (g : ι → TestFunction) :
    MemLp (fun ω : FieldConfiguration => Real.exp (∑ i ∈ s, |ω (g i)|)) 2 (μ_GFF m).toMeasure := by
  -- Rewrite exp(sum) as product of exp
  have h_eq : (fun ω : FieldConfiguration => Real.exp (∑ i ∈ s, |ω (g i)|)) =
              (fun ω : FieldConfiguration => ∏ i ∈ s, Real.exp |ω (g i)|) := by
    ext ω; exact Real.exp_sum s (fun i => |ω (g i)|)
  rw [h_eq]
  -- Handle empty case
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp [memLp_const]
  -- For nonempty s, use MemLp.prod' with p i = 2 * s.card for each i
  let k : ℕ := s.card
  have hk_pos : 0 < k := Finset.card_pos.mpr hs
  -- Each factor is in L^(2k)
  have h_each : ∀ i ∈ s, MemLp (fun ω : FieldConfiguration => Real.exp |ω (g i)|)
      (2 * k : ℕ) (μ_GFF m).toMeasure := by
    intro i _
    exact gff_exp_abs_pairing_memLp m (g i) (2 * k : ℕ) (ENNReal.natCast_ne_top _)
  -- Apply MemLp.prod' with constant exponent 2k for each factor
  have h_prod := MemLp.prod' (s := s) (p := fun _ => (2 * k : ℕ))
    (f := fun i (ω : FieldConfiguration) => Real.exp |ω (g i)|)
    (fun i hi => h_each i hi)
  -- The resulting exponent is (∑ i ∈ s, 1/(2k))⁻¹ = (k/(2k))⁻¹ = 2
  convert h_prod using 1
  -- Goal: 2 = (∑ i ∈ s, ((2 * k : ℕ) : ENNReal)⁻¹)⁻¹
  rw [Finset.sum_const, nsmul_eq_mul]
  -- Goal: 2 = (s.card * ((2 * k : ℕ) : ENNReal)⁻¹)⁻¹
  -- Since k = s.card, this is (k * (2k)⁻¹)⁻¹ = (1/2)⁻¹ = 2
  have hk_ne_zero : (s.card : ENNReal) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    exact hk_pos.ne'
  have hk_ne_top : (s.card : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top s.card
  -- Rewrite (2 * k : ℕ) as 2 * s.card in ENNReal using k = s.card
  simp only [k]
  have h_cast : ((2 * s.card : ℕ) : ENNReal) = 2 * s.card := by norm_cast
  rw [h_cast]
  -- Goal: 2 = (s.card * (2 * s.card)⁻¹)⁻¹
  -- Strategy: s.card * (2 * s.card)⁻¹ = s.card / (2 * s.card) = 1/2, so inverse is 2
  have h2_ne_zero : (2 : ENNReal) ≠ 0 := by norm_num
  have h2_ne_top : (2 : ENNReal) ≠ ⊤ := by norm_num
  -- First simplify (2 * s.card)⁻¹ = 2⁻¹ * s.card⁻¹
  rw [ENNReal.mul_inv (Or.inl h2_ne_zero) (Or.inl h2_ne_top)]
  -- Goal: 2 = (s.card * (2⁻¹ * s.card⁻¹))⁻¹
  rw [mul_comm (2 : ENNReal)⁻¹ (s.card : ENNReal)⁻¹]
  rw [← mul_assoc]
  rw [ENNReal.mul_inv_cancel hk_ne_zero hk_ne_top]
  -- Goal: 2 = (1 * 2⁻¹)⁻¹
  rw [one_mul]
  -- Goal: 2 = 2⁻¹⁻¹
  simp only [inv_inv]

/-- The integral of ‖exp(I * distributionPairingℂ_real ω f)‖ is finite for any complex test function.
    This follows from the Gaussian exponential integrability applied to the imaginary part. -/
lemma gff_integrand_norm_integrable (f : TestFunctionℂ) :
    Integrable (fun ω : FieldConfiguration =>
        ‖Complex.exp (Complex.I * distributionPairingℂ_real ω f)‖)
      (μ_GFF m).toMeasure := by
  -- Rewrite the norm using our lemma
  simp_rw [norm_exp_I_distributionPairingℂ_real]
  -- This is exp(-(ω f_im)) which is integrable by gff_exp_neg_pairing_integrable
  exact gff_exp_neg_pairing_integrable m (complex_testfunction_decompose f).2



/-- The GFF integrand is integrable for each z.
    This follows from the norm being exp(-(ω f_im)) which is integrable by
    Gaussian exponential integrability. -/
theorem gff_integrand_integrable (n : ℕ) (J : Fin n → TestFunctionℂ) (z : Fin n → ℂ) :
    Integrable
      (fun ω : FieldConfiguration =>
        Complex.exp (Complex.I * distributionPairingℂ_real ω (∑ i, z i • J i)))
      (μ_GFF m).toMeasure := by
  -- The norm is exp(-(ω f_im)) which is integrable
  have h_norm := gff_integrand_norm_integrable m (∑ i, z i • J i)
  -- Use Integrable.of_norm - h_norm is already an Integrable statement
  -- We need to convert from norm integrable to integrable
  have h_meas : AEStronglyMeasurable
      (fun ω => Complex.exp (Complex.I * distributionPairingℂ_real ω (∑ i, z i • J i)))
      (μ_GFF m).toMeasure := gff_integrand_measurable m n J z
  exact (integrable_norm_iff h_meas).mp h_norm

/-- The Fréchet derivative of the GFF integrand is measurable in ω.

    The integrand is f(z, ω) = exp(I * ⟨ω, ∑ᵢ zᵢJᵢ⟩), which is a composition of
    continuous functions in ω. The Fréchet derivative in z is also continuous in ω,
    hence measurable.

    Mathematical proof outline:
    - The fderiv of exp(g(z)) where g is linear is exp(g(z₀)) • g
    - Here g(z) = I * ∑ᵢ zᵢ * ⟨ω, Jᵢ⟩, which as a CLM is I • ∑ᵢ ⟨ω, Jᵢ⟩ • proj_i
    - So fderiv = exp(I * ⟨ω, ∑ᵢ z₀ᵢJᵢ⟩) • (I • ∑ᵢ ⟨ω, Jᵢ⟩ • proj_i)
    - This is continuous in ω (each pairing is continuous, exp is continuous)
    - Continuous implies measurable -/
theorem gff_integrand_fderiv_measurable (n : ℕ) (J : Fin n → TestFunctionℂ) (z₀ : Fin n → ℂ) :
    AEStronglyMeasurable
      (fun ω : FieldConfiguration =>
        fderiv ℂ (fun z => Complex.exp (Complex.I * distributionPairingℂ_real ω (∑ i, z i • J i))) z₀)
      (μ_GFF m).toMeasure := by
  -- Define the explicit formula for the fderiv
  -- For exp(g(z)) where g is a CLM, fderiv at z₀ is exp(g(z₀)) • g
  let g : FieldConfiguration → (Fin n → ℂ) →L[ℂ] ℂ := fun ω =>
    Complex.I • ∑ i : Fin n, distributionPairingℂ_real ω (J i) • ContinuousLinearMap.proj (R := ℂ) i

  -- The explicit fderiv formula
  let F : FieldConfiguration → (Fin n → ℂ) →L[ℂ] ℂ := fun ω =>
    Complex.exp (Complex.I * distributionPairingℂ_real ω (∑ i, z₀ i • J i)) • g ω

  -- F is continuous in ω
  have hF_cont : Continuous F := by
    apply Continuous.smul
    · -- exp(I * ⟨ω, ∑ᵢ z₀ᵢJᵢ⟩) is continuous in ω
      exact Complex.continuous_exp.comp
        (continuous_const.mul (distributionPairingℂ_real_continuous (∑ i, z₀ i • J i)))
    · -- g ω = I • ∑ᵢ ⟨ω, Jᵢ⟩ • proj_i is continuous in ω
      apply Continuous.const_smul
      apply continuous_finset_sum
      intro i _
      apply Continuous.smul
      · exact distributionPairingℂ_real_continuous (J i)
      · exact continuous_const

  -- Show that the fderiv equals F
  have h_fderiv_eq : ∀ ω, fderiv ℂ (fun z => Complex.exp (Complex.I * distributionPairingℂ_real ω (∑ i, z i • J i))) z₀ = F ω := by
    intro ω
    -- The function is exp ∘ (I * linear), where linear is ∑ᵢ zᵢ * ⟨ω, Jᵢ⟩
    -- Use chain rule: fderiv (exp ∘ h) = exp(h(z₀)) • fderiv h

    -- First show that the inner function equals g ω applied to z
    have h_inner_eq : ∀ z, Complex.I * distributionPairingℂ_real ω (∑ i, z i • J i) = g ω z := by
      intro z
      simp only [g, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
                 ContinuousLinearMap.proj_apply]
      -- Linearity of distributionPairingℂ_real
      have h_linear : distributionPairingℂ_real ω (∑ i, z i • J i) =
          ∑ i, z i * distributionPairingℂ_real ω (J i) := by
        have h_add : ∀ f g : TestFunctionℂ, distributionPairingℂ_real ω (f + g) =
            distributionPairingℂ_real ω f + distributionPairingℂ_real ω g := fun f h => by
          have := pairing_linear_combo ω f h 1 1; simp at this; exact this
        have h_smul : ∀ (c : ℂ) (f : TestFunctionℂ), distributionPairingℂ_real ω (c • f) =
            c * distributionPairingℂ_real ω f := fun c f => by
          have := pairing_linear_combo ω f 0 c 0; simp at this; exact this
        have h_zero : distributionPairingℂ_real ω 0 = 0 := by
          have := pairing_linear_combo ω 0 0 0 0; simp at this; exact this
        induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
        | empty => simp [h_zero]
        | insert i s hi ih =>
          rw [Finset.sum_insert hi, Finset.sum_insert hi, h_add, h_smul, ih]
      rw [h_linear]
      -- Now: I * ∑ᵢ zᵢ * cᵢ = I • ∑ᵢ cᵢ • zᵢ
      simp only [smul_eq_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring

    -- The inner function is the CLM g ω, so its fderiv is g ω itself
    have h_diff_inner : DifferentiableAt ℂ (fun z => g ω z) z₀ := (g ω).differentiableAt
    have h_fderiv_inner : fderiv ℂ (fun z => g ω z) z₀ = g ω := ContinuousLinearMap.fderiv (g ω)

    -- exp is differentiable everywhere
    have h_diff_exp : DifferentiableAt ℂ Complex.exp (g ω z₀) := Complex.differentiable_exp _

    -- fderiv of exp at w is exp(w) • id
    have h_fderiv_exp : fderiv ℂ Complex.exp (g ω z₀) =
        ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (Complex.exp (g ω z₀)) := by
      have := (Complex.hasDerivAt_exp (g ω z₀)).hasFDerivAt
      exact this.fderiv

    -- Rewrite the function using h_inner_eq
    have h_eq_comp : (fun z => Complex.exp (Complex.I * distributionPairingℂ_real ω (∑ i, z i • J i))) =
        Complex.exp ∘ (fun z => g ω z) := by
      ext z; simp [h_inner_eq z]

    -- Apply chain rule: fderiv (f ∘ g) = fderiv f ∘L fderiv g
    rw [h_eq_comp]
    rw [fderiv_comp z₀ h_diff_exp h_diff_inner]
    rw [h_fderiv_exp, h_fderiv_inner]

    -- Simplify: smulRight 1 c ∘L g = c • g
    simp only [F]
    ext v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
               ContinuousLinearMap.one_apply, ContinuousLinearMap.smul_apply]
    -- Goal: (g ω v) • exp((g ω) z₀) = exp(I * pairing(z₀)) • (g ω v)
    -- First rewrite (g ω) z₀ using h_inner_eq
    rw [← h_inner_eq z₀]
    -- Now goal is: (g ω v) • exp(...) = exp(...) • (g ω v)
    -- This is commutativity: a • b = b • a for ℂ
    simp only [smul_eq_mul]
    ring

  -- F is continuous and equals fderiv, so fderiv is continuous
  have h_cont : Continuous (fun ω => fderiv ℂ (fun z => Complex.exp (Complex.I * distributionPairingℂ_real ω (∑ i, z i • J i))) z₀) := by
    simp_rw [h_fderiv_eq]
    exact hF_cont

  exact h_cont.aestronglyMeasurable



/-- The Fréchet derivative of the GFF integrand is bounded by an integrable function.

    For the integrand f(z, ω) = exp(I * ⟨ω, ∑ᵢ zᵢJᵢ⟩), the Fréchet derivative has norm
    bounded by a multiple of the function value times linear factors in ω.
    Using Gaussian exponential integrability, this is integrable.

    Key insight: ‖fderiv f(z, ω)‖ = ‖f(z, ω)‖ * ‖I * ∑ᵢ ⟨ω, Jᵢ⟩ * proj_i‖
                                 ≤ exp(-⟨ω, f_im⟩) * C * (∑ᵢ |⟨ω, Jᵢ⟩|)
    where C bounds the operator norm contribution.

    This is integrable because exp(-x) * |y| ≤ exp(α x² + β y²) for appropriate α, β,
    and both squared pairings have exponential integrability. -/
theorem gff_integrand_fderiv_bound (n : ℕ) (J : Fin n → TestFunctionℂ) (z₀ : Fin n → ℂ) :
    ∃ ε > 0, ∃ bound : FieldConfiguration → ℝ,
      Integrable bound (μ_GFF m).toMeasure ∧
      ∀ᵐ ω ∂(μ_GFF m).toMeasure, ∀ z ∈ Metric.ball z₀ ε,
        ‖fderiv ℂ (fun z' => Complex.exp (Complex.I * distributionPairingℂ_real ω (∑ i, z' i • J i))) z‖ ≤ bound ω := by
  -- Choose ε = 1 (any positive value works since the bound is uniform)
  use 1, one_pos

  -- Define the linear map g(z) = I * ∑ᵢ zᵢ * ⟨ω, Jᵢ⟩
  let g : FieldConfiguration → (Fin n → ℂ) →L[ℂ] ℂ := fun ω =>
    Complex.I • ∑ i : Fin n, distributionPairingℂ_real ω (J i) • ContinuousLinearMap.proj (R := ℂ) i

  -- The fderiv at z is exp(g(z)) • g, so ‖fderiv‖ = ‖exp(g(z))‖ * ‖g‖
  -- ‖exp(I * pairing)‖ = exp(Re(I * pairing)) = exp(-pairing_im)
  -- For z in ball z₀ 1, we need a uniform bound on ‖exp(I * pairing(z))‖

  -- Key: for z in ball z₀ 1, the imaginary part of ∑ᵢ zᵢ • Jᵢ is bounded
  -- by the imaginary part of ∑ᵢ z₀ᵢ • Jᵢ plus contributions from (z - z₀)

  -- The bound function: exp(|⟨ω, f_im(z₀)⟩| + ∑(|⟨ω, J_re⟩| + |⟨ω, J_im⟩|)) * (1 + ∑ᵢ |⟨ω, Jᵢ⟩|)

  -- Define the bound function
  let bound : FieldConfiguration → ℝ := fun ω =>
    -- exp bound from the imaginary part
    Real.exp (|ω ((complex_testfunction_decompose (∑ i, z₀ i • J i)).2)| +
              ∑ i : Fin n, (|ω (complex_testfunction_decompose (J i)).1| + |ω (complex_testfunction_decompose (J i)).2|)) *
    -- operator norm bound: 1 + sum of norms of pairings
    (1 + ∑ i : Fin n, ‖distributionPairingℂ_real ω (J i)‖)

  use bound

  constructor
  · -- Prove integrability of bound
    -- bound ω = exp(|a| + ∑|b_i|) * (1 + ∑‖cᵢ‖)
    -- We use Hölder: L² × L² → L¹

    -- First factor: exp(|a| + ∑|b_i|) = exp(|a|) * ∏ exp(|b_i|)
    -- Each exp(|⟨ω, f⟩|) is in L^p for all p < ∞
    -- We have a finite product of such functions.
    -- If we have k factors, we can use generalized Hölder with p = 2k for each factor to get L² for the product.

    -- Let's define the sum in the exponent as a single term for clarity
    let exponent_sum (ω : FieldConfiguration) : ℝ :=
      |ω ((complex_testfunction_decompose (∑ i, z₀ i • J i)).2)| +
      ∑ i : Fin n, (|ω (complex_testfunction_decompose (J i)).1| + |ω (complex_testfunction_decompose (J i)).2|)

    -- We need to show exp(exponent_sum) is in L².
    -- Strategy: exp(∑ᵢ |xᵢ|) = ∏ᵢ exp(|xᵢ|), and each exp(|ω g|) ∈ L^p for all p < ∞
    -- by gff_exp_abs_pairing_memLp. Using generalized Hölder, a product of k terms
    -- each in L^(2k) is in L^2. Here k = 1 + 2n (one f₀ term plus 2n terms from J_re/J_im).
    have h_exp_factor_L2 : MemLp (fun ω => Real.exp (exponent_sum ω)) 2 (μ_GFF m).toMeasure := by
      -- Express exponent_sum as a sum over a finset of test functions
      -- exponent_sum ω = |ω f₀| + ∑ i, (|ω (Jᵢ_re)| + |ω (Jᵢ_im)|)
      -- This is a sum of 1 + 2n terms.
      -- We define an index type Option (Fin n × Bool) and map to test functions:
      --   none ↦ f₀ = (∑ i, z₀ᵢ • Jᵢ)_im
      --   some (i, false) ↦ (Jᵢ)_re
      --   some (i, true) ↦ (Jᵢ)_im
      let f₀ : TestFunction := (complex_testfunction_decompose (∑ i, z₀ i • J i)).2
      let test_funcs : Option (Fin n × Bool) → TestFunction := fun idx =>
        match idx with
        | none => f₀
        | some (i, false) => (complex_testfunction_decompose (J i)).1
        | some (i, true) => (complex_testfunction_decompose (J i)).2
      -- Apply the helper lemma
      have h_memLp := gff_exp_abs_sum_memLp m Finset.univ test_funcs
      -- Show the functions are equal (not just a.e. equal)
      have h_eq : (fun ω => Real.exp (exponent_sum ω)) =
          (fun ω => Real.exp (∑ i ∈ Finset.univ, |ω (test_funcs i)|)) := by
        ext ω
        congr 1
        -- Need to show: exponent_sum ω = ∑ i ∈ Finset.univ, |ω (test_funcs i)|
        -- LHS = |ω f₀| + ∑ i : Fin n, (|ω (J i)_re| + |ω (J i)_im|)
        -- RHS = ∑ over Option (Fin n × Bool)
        simp only [exponent_sum, test_funcs, f₀]
        rw [Fintype.sum_option]
        congr 1
        -- Goal: ∑ i, (|ω (J i)_re| + |ω (J i)_im|) = ∑ (i, b) : Fin n × Bool, |ω ...|
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro i _
        simp only [Fintype.sum_bool]
        ring
      rw [h_eq]
      exact h_memLp

    -- Second factor: (1 + ∑ ‖distributionPairingℂ_real ω (J i)‖)
    -- This is in L² (polynomial in Gaussian).
    have h_poly_factor_L2 : MemLp (fun ω => 1 + ∑ i : Fin n, ‖distributionPairingℂ_real ω (J i)‖) 2 (μ_GFF m).toMeasure := by
      -- Constants are in L²
      have h_const : MemLp (fun _ : FieldConfiguration => (1 : ℝ)) 2 (μ_GFF m).toMeasure :=
        memLp_const 1
      -- Each ‖distributionPairingℂ_real ω (J i)‖ is bounded by |ω (J_re)| + |ω (J_im)|
      -- and each of those is in L² by gaussianFreeField_pairing_memLp
      have h_sum : MemLp (fun ω => ∑ i : Fin n, ‖distributionPairingℂ_real ω (J i)‖) 2 (μ_GFF m).toMeasure := by
        apply memLp_finset_sum
        intro i _
        -- ‖distributionPairingℂ_real ω (J i)‖ = ‖ω(J_re) + I * ω(J_im)‖ ≤ |ω(J_re)| + |ω(J_im)|
        let φRe := (complex_testfunction_decompose (J i)).1
        let φIm := (complex_testfunction_decompose (J i)).2
        -- Each real pairing is in L² (actually in all Lᵖ) - using proven theorem from GFFbridge
        have h_re : MemLp (fun ω : FieldConfiguration => ω φRe) 2 (μ_GFF m).toMeasure :=
          gaussianFreeField_pairing_memLp m φRe 2 (by simp)
        have h_im : MemLp (fun ω : FieldConfiguration => ω φIm) 2 (μ_GFF m).toMeasure :=
          gaussianFreeField_pairing_memLp m φIm 2 (by simp)
        -- |x| is in L² if x is in L²
        have h_abs_re : MemLp (fun ω : FieldConfiguration => |ω φRe|) 2 (μ_GFF m).toMeasure :=
          h_re.abs
        have h_abs_im : MemLp (fun ω : FieldConfiguration => |ω φIm|) 2 (μ_GFF m).toMeasure :=
          h_im.abs
        -- Sum of L² functions is L²
        have h_sum_abs : MemLp (fun ω => |ω φRe| + |ω φIm|) 2 (μ_GFF m).toMeasure :=
          h_abs_re.add h_abs_im
        -- ‖distributionPairingℂ_real ω f‖ ≤ |ω f_re| + |ω f_im| (triangle inequality for complex norm)
        apply h_sum_abs.mono'
        · -- Measurability
          apply AEStronglyMeasurable.norm
          simp only [distributionPairingℂ_real]
          apply AEStronglyMeasurable.add
          · exact Complex.continuous_ofReal.aestronglyMeasurable.comp_aemeasurable
              (WeakDual.eval_continuous φRe).aestronglyMeasurable.aemeasurable
          · apply AEStronglyMeasurable.const_mul
            exact Complex.continuous_ofReal.aestronglyMeasurable.comp_aemeasurable
              (WeakDual.eval_continuous φIm).aestronglyMeasurable.aemeasurable
        · -- The bound ‖distributionPairingℂ_real ω f‖ ≤ |ω f_re| + |ω f_im|
          filter_upwards with ω
          simp only [distributionPairingℂ_real, φRe, φIm, complex_testfunction_decompose]
          -- The goal is ‖‖...‖‖ ≤ |...| + |...|, but ‖x‖ = |x| for x : ℝ≥0
          rw [Real.norm_eq_abs, abs_norm]
          calc ‖(↑(ω (schwartz_comp_clm (J i) Complex.reCLM)) : ℂ) +
                  Complex.I * ↑(ω (schwartz_comp_clm (J i) Complex.imCLM))‖
              ≤ ‖(↑(ω (schwartz_comp_clm (J i) Complex.reCLM)) : ℂ)‖ +
                ‖Complex.I * ↑(ω (schwartz_comp_clm (J i) Complex.imCLM))‖ := norm_add_le _ _
            _ = |ω (schwartz_comp_clm (J i) Complex.reCLM)| +
                |ω (schwartz_comp_clm (J i) Complex.imCLM)| := by
                simp [Complex.norm_real, Complex.norm_I]
      exact h_const.add h_sum

    -- Product is in L¹.
    exact MemLp.integrable_mul h_exp_factor_L2 h_poly_factor_L2

  · -- Prove the pointwise bound
    filter_upwards with ω z hz

    -- The fderiv equals exp(I * pairing(z)) • g ω by the calculation in gff_integrand_fderiv_measurable
    -- We need to bound its norm

    -- ‖exp(I * pairing) • g‖ = ‖exp(I * pairing)‖ * ‖g‖
    -- ‖exp(I * pairing)‖ = exp(Re(I * pairing)) = exp(-pairing_im)

    -- The imaginary part of ∑ᵢ zᵢ • Jᵢ at ω
    let f_z := ∑ i : Fin n, z i • J i
    let f_z₀ := ∑ i : Fin n, z₀ i • J i

    -- For z in ball z₀ 1, use triangle inequality
    -- |⟨ω, f_im(z)⟩| ≤ |⟨ω, f_im(z₀)⟩| + |⟨ω, f_im(z) - f_im(z₀)⟩|

    -- The difference f_im(z) - f_im(z₀) is bounded by J_re_im_sum when |z - z₀| < 1

    -- First establish that the fderiv has the form exp(I * pairing(z)) • g ω
    -- where g ω = I • ∑ᵢ ⟨ω, Jᵢ⟩ • proj_i

    -- Define the inner linear map for any z
    have h_inner_eq : ∀ z', Complex.I * distributionPairingℂ_real ω (∑ i, z' i • J i) = g ω z' := by
      intro z'
      simp only [g, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
                 ContinuousLinearMap.proj_apply]
      -- Linearity of distributionPairingℂ_real
      have h_linear : distributionPairingℂ_real ω (∑ i, z' i • J i) =
          ∑ i, z' i * distributionPairingℂ_real ω (J i) := by
        have h_add : ∀ f h : TestFunctionℂ, distributionPairingℂ_real ω (f + h) =
            distributionPairingℂ_real ω f + distributionPairingℂ_real ω h := fun f h => by
          have := pairing_linear_combo ω f h 1 1; simp at this; exact this
        have h_smul : ∀ (c : ℂ) (f : TestFunctionℂ), distributionPairingℂ_real ω (c • f) =
            c * distributionPairingℂ_real ω f := fun c f => by
          have := pairing_linear_combo ω f 0 c 0; simp at this; exact this
        have h_zero : distributionPairingℂ_real ω 0 = 0 := by
          have := pairing_linear_combo ω 0 0 0 0; simp at this; exact this
        induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
        | empty => simp [h_zero]
        | insert i s hi ih =>
          rw [Finset.sum_insert hi, Finset.sum_insert hi, h_add, h_smul, ih]
      rw [h_linear]
      simp only [smul_eq_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring

    -- The function is exp ∘ (g ω)
    have h_eq_comp : (fun z' => Complex.exp (Complex.I * distributionPairingℂ_real ω (∑ i, z' i • J i))) =
        Complex.exp ∘ (fun z' => g ω z') := by
      ext z'; simp [h_inner_eq z']

    -- Differentiability of g ω and exp
    have h_diff_inner : DifferentiableAt ℂ (fun z' => g ω z') z := (g ω).differentiableAt
    have h_diff_exp : DifferentiableAt ℂ Complex.exp (g ω z) := Complex.differentiable_exp _

    -- fderiv of the linear map g ω is itself
    have h_fderiv_inner : fderiv ℂ (fun z' => g ω z') z = g ω := ContinuousLinearMap.fderiv (g ω)

    -- fderiv of exp at w is exp(w) • id
    have h_fderiv_exp : fderiv ℂ Complex.exp (g ω z) =
        ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (Complex.exp (g ω z)) := by
      exact (Complex.hasDerivAt_exp (g ω z)).hasFDerivAt.fderiv

    -- Apply chain rule
    have h_fderiv_eq : fderiv ℂ (fun z' => Complex.exp (Complex.I * distributionPairingℂ_real ω (∑ i, z' i • J i))) z =
        Complex.exp (Complex.I * distributionPairingℂ_real ω (∑ i, z i • J i)) • g ω := by
      rw [h_eq_comp]
      rw [fderiv_comp z h_diff_exp h_diff_inner]
      rw [h_fderiv_exp, h_fderiv_inner]
      ext v
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
                 ContinuousLinearMap.one_apply, ContinuousLinearMap.smul_apply]
      rw [← h_inner_eq z]
      simp only [smul_eq_mul]
      ring

    -- Now bound the norm: ‖exp(I * pairing) • g‖ = ‖exp(I * pairing)‖ * ‖g‖
    rw [h_fderiv_eq]
    rw [norm_smul]

    -- Bound the exponential factor
    rw [norm_exp_I_distributionPairingℂ_real]
    -- Now we have Real.exp (-(ω (complex_testfunction_decompose (∑ i, z i • J i)).2)) * ‖g ω‖
    -- We need to bound exp(-pairing_im(z)) ≤ exp(|pairing_im(z₀)| + ∑(|J_re| + |J_im|))

    -- The key is that for z ∈ ball z₀ 1, we can bound the imaginary part pairing
    -- Using exp(-x) ≤ exp(|x|) for any x
    have h_exp_bound : Real.exp (-(ω (complex_testfunction_decompose (∑ i, z i • J i)).2)) ≤
        Real.exp |ω (complex_testfunction_decompose (∑ i, z i • J i)).2| := by
      apply Real.exp_le_exp.mpr
      exact neg_le_abs _

    -- Now we need to bound |ω (f_im(z))| in terms of |ω (f_im(z₀))| and |ω J_re_im_sum|
    -- The imaginary part of ∑ᵢ zᵢ • Jᵢ satisfies a linear bound

    -- The decomposition: (∑ᵢ zᵢ • Jᵢ)_im = ∑ᵢ (z.re * J_im + z.im * J_re)
    -- For z = z₀ + δ where |δ| < 1 in ℂⁿ, we get variation bounded by J_re_im_sum

    -- We use a simpler bound: |ω f_im(z)| ≤ |ω f_im(z₀)| + C for z near z₀
    -- where C depends on ω J_re_im_sum

    -- For z ∈ ball z₀ 1 (in metric space on Fin n → ℂ with sup norm for product)
    -- |z i - z₀ i| < 1 for some i, and others vary by at most...

    -- Let's use a direct estimate: the imaginary part linearity
    -- f_im(z) - f_im(z₀) involves (z - z₀) components times (J_re, J_im)

    -- Simplify: use triangle inequality for absolute value
    -- |ω f_im(z)| ≤ |ω f_im(z₀)| + |ω (f_im(z) - f_im(z₀))|

    -- Use triangle inequality for the imaginary part bound
    -- |ω f_im(z)| ≤ |ω f_im(z₀)| + |ω (f_im(z) - f_im(z₀))|
    -- The difference is bounded by |ω J_re_im_sum| since |z - z₀| < 1

    have h_abs_im_bound : |ω (complex_testfunction_decompose (∑ i, z i • J i)).2| ≤
        |ω (complex_testfunction_decompose (∑ i, z₀ i • J i)).2| +
        ∑ i : Fin n, (|ω (complex_testfunction_decompose (J i)).1| + |ω (complex_testfunction_decompose (J i)).2|) := by
      -- Use triangle inequality: |a| ≤ |b| + |a - b|
      have h_tri : |ω (complex_testfunction_decompose (∑ i, z i • J i)).2| ≤
          |ω (complex_testfunction_decompose (∑ i, z₀ i • J i)).2| +
          |ω ((complex_testfunction_decompose (∑ i, z i • J i)).2 -
               (complex_testfunction_decompose (∑ i, z₀ i • J i)).2)| := by
        have h_eq : ω (complex_testfunction_decompose (∑ i, z₀ i • J i)).2 +
            ω ((complex_testfunction_decompose (∑ i, z i • J i)).2 -
               (complex_testfunction_decompose (∑ i, z₀ i • J i)).2) =
            ω (complex_testfunction_decompose (∑ i, z i • J i)).2 := by
          rw [← map_add]; congr 1; abel
        rw [← h_eq]
        exact abs_add_le _ _
      apply le_trans h_tri
      -- Need: |ω f₀| + |ω diff| ≤ |ω f₀| + ∑(|ω J_re| + |ω J_im|)
      -- i.e., |ω diff| ≤ ∑(|ω J_re| + |ω J_im|)
      -- Use add_le_add with le_refl on the left
      apply add_le_add (le_refl _)
      -- Bound the difference term
      -- The difference (f_im(z) - f_im(z₀)) involves (z - z₀) scaled test functions
      -- For |z - z₀| < 1, this is bounded by sum of absolute values
      have hz_bound : dist z z₀ < 1 := Metric.mem_ball.mp hz
      -- For z in ball z₀ 1, each component |z i - z₀ i| < 1
      have h_comp_bound : ∀ i : Fin n, ‖z i - z₀ i‖ < 1 := by
        intro i
        calc ‖z i - z₀ i‖ ≤ ‖z - z₀‖ := norm_le_pi_norm (z - z₀) i
          _ = dist z z₀ := rfl
          _ < 1 := hz_bound

      -- The bound follows from linearity of complex_testfunction_decompose and ω.
      -- For z ∈ ball z₀ 1, the difference f_im(z) - f_im(z₀) satisfies:
      -- |ω (f_im(z) - f_im(z₀))| = |∑ᵢ ((zᵢ-z₀ᵢ).re * ω(Jᵢ_im) + (zᵢ-z₀ᵢ).im * ω(Jᵢ_re))|
      --                         ≤ ∑ᵢ (|zᵢ-z₀ᵢ| * (|ω(Jᵢ_re)| + |ω(Jᵢ_im)|))
      --                         ≤ ∑ᵢ (|ω(Jᵢ_re)| + |ω(Jᵢ_im)|)  since |zᵢ-z₀ᵢ| < 1

      -- Use ω_im_decompose_linear to expand the imaginary part
      -- For a single term: ω ((c • J)_im) = c.re * ω(J_im) + c.im * ω(J_re)
      have h_single_im : ∀ (c : ℂ) (f : TestFunctionℂ),
          ω (complex_testfunction_decompose (c • f)).2 =
          c.re * ω (complex_testfunction_decompose f).2 + c.im * ω (complex_testfunction_decompose f).1 := by
        intro c f
        have := ω_im_decompose_linear ω f 0 c 0
        simp at this
        exact this

      -- For the sum ∑ᵢ cᵢ • Jᵢ, the imaginary part pairing is the sum of individual contributions
      have h_sum_im : ∀ (c : Fin n → ℂ),
          ω (complex_testfunction_decompose (∑ i : Fin n, c i • J i)).2 =
          ∑ i : Fin n, ((c i).re * ω (complex_testfunction_decompose (J i)).2 +
                        (c i).im * ω (complex_testfunction_decompose (J i)).1) := by
        intro c
        induction Finset.univ (α := Fin n) using Finset.induction_on with
        | empty =>
          simp only [Finset.sum_empty]
          have h0 : (complex_testfunction_decompose (0 : TestFunctionℂ)).2 = 0 := by
            ext x; simp [complex_testfunction_decompose]
          simp [h0]
        | insert j s hj ih =>
          rw [Finset.sum_insert hj, Finset.sum_insert hj]
          have h_add := ω_im_decompose_linear ω (c j • J j) (∑ k ∈ s, c k • J k) 1 1
          simp only [one_smul, Complex.one_re, Complex.one_im, one_mul, zero_mul, add_zero] at h_add
          rw [h_add, h_single_im, ih]

      -- Compute the difference
      rw [map_sub, h_sum_im z, h_sum_im z₀]
      -- The difference of sums simplifies
      have h_diff_eq : (∑ i : Fin n, ((z i).re * ω (complex_testfunction_decompose (J i)).2 +
                                      (z i).im * ω (complex_testfunction_decompose (J i)).1)) -
                       (∑ i : Fin n, ((z₀ i).re * ω (complex_testfunction_decompose (J i)).2 +
                                      (z₀ i).im * ω (complex_testfunction_decompose (J i)).1)) =
                       ∑ i : Fin n, (((z i).re - (z₀ i).re) * ω (complex_testfunction_decompose (J i)).2 +
                                     ((z i).im - (z₀ i).im) * ω (complex_testfunction_decompose (J i)).1) := by
        rw [← Finset.sum_sub_distrib]
        congr 1; ext i; ring
      rw [h_diff_eq]

      -- Now bound the absolute value using triangle inequality
      calc |∑ i : Fin n, (((z i).re - (z₀ i).re) * ω (complex_testfunction_decompose (J i)).2 +
                          ((z i).im - (z₀ i).im) * ω (complex_testfunction_decompose (J i)).1)|
          ≤ ∑ i : Fin n, |(((z i).re - (z₀ i).re) * ω (complex_testfunction_decompose (J i)).2 +
                           ((z i).im - (z₀ i).im) * ω (complex_testfunction_decompose (J i)).1)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i : Fin n, (|((z i).re - (z₀ i).re) * ω (complex_testfunction_decompose (J i)).2| +
                          |((z i).im - (z₀ i).im) * ω (complex_testfunction_decompose (J i)).1|) := by
            apply Finset.sum_le_sum; intro i _; exact abs_add_le _ _
        _ = ∑ i : Fin n, (|(z i).re - (z₀ i).re| * |ω (complex_testfunction_decompose (J i)).2| +
                          |(z i).im - (z₀ i).im| * |ω (complex_testfunction_decompose (J i)).1|) := by
            congr 1; ext i; rw [abs_mul, abs_mul]
        _ ≤ ∑ i : Fin n, (1 * |ω (complex_testfunction_decompose (J i)).2| +
                          1 * |ω (complex_testfunction_decompose (J i)).1|) := by
            apply Finset.sum_le_sum; intro i _
            -- |z.re|, |z.im| ≤ ‖z‖ for complex z (standard bounds)
            have hre : |(z i).re - (z₀ i).re| ≤ 1 := by
              have h1 : |(z i - z₀ i).re| ≤ ‖z i - z₀ i‖ := abs_re_le_norm _
              simp only [Complex.sub_re] at h1
              linarith [h_comp_bound i]
            have him : |(z i).im - (z₀ i).im| ≤ 1 := by
              have h1 : |(z i - z₀ i).im| ≤ ‖z i - z₀ i‖ := abs_im_le_norm _
              simp only [Complex.sub_im] at h1
              linarith [h_comp_bound i]
            apply add_le_add
            · exact mul_le_mul_of_nonneg_right hre (abs_nonneg _)
            · exact mul_le_mul_of_nonneg_right him (abs_nonneg _)
        _ = ∑ i : Fin n, (|ω (complex_testfunction_decompose (J i)).2| +
                          |ω (complex_testfunction_decompose (J i)).1|) := by simp
        _ = ∑ i : Fin n, (|ω (complex_testfunction_decompose (J i)).1| +
                          |ω (complex_testfunction_decompose (J i)).2|) := by
            congr 1; ext i; ring

    -- Now combine all bounds:
    -- Goal: exp(-ω f_im(z)) * ‖g ω‖ ≤ bound ω
    -- where bound ω = exp(|ω f₁| + ∑(|ω J_re| + |ω J_im|)) * (1 + ∑ᵢ ‖distributionPairingℂ_real ω (J i)‖)
    -- and f₁ = (complex_testfunction_decompose (∑ i, z₀ i • J i)).2

    -- Step 1: exp(-ω f_im(z)) ≤ exp(|ω f_im(z)|) ≤ exp(|ω f₁| + ∑...)
    have h_exp_final : Real.exp (-(ω (complex_testfunction_decompose (∑ i, z i • J i)).2)) ≤
        Real.exp (|ω (complex_testfunction_decompose (∑ i, z₀ i • J i)).2| +
                  ∑ i : Fin n, (|ω (complex_testfunction_decompose (J i)).1| + |ω (complex_testfunction_decompose (J i)).2|)) := by
      apply Real.exp_le_exp.mpr
      calc -(ω (complex_testfunction_decompose (∑ i, z i • J i)).2)
          ≤ |ω (complex_testfunction_decompose (∑ i, z i • J i)).2| := neg_le_abs _
        _ ≤ |ω (complex_testfunction_decompose (∑ i, z₀ i • J i)).2| +
            ∑ i : Fin n, (|ω (complex_testfunction_decompose (J i)).1| + |ω (complex_testfunction_decompose (J i)).2|) := h_abs_im_bound

    -- Step 2: ‖g ω‖ ≤ 1 + ∑ᵢ ‖distributionPairingℂ_real ω (J i)‖
    -- g ω = I • ∑ᵢ ⟨ω, Jᵢ⟩ • proj_i
    have h_g_bound : ‖g ω‖ ≤ 1 + ∑ i : Fin n, ‖distributionPairingℂ_real ω (J i)‖ := by
      -- ‖I • (∑ᵢ cᵢ • proj_i)‖ = ‖I‖ * ‖∑ᵢ cᵢ • proj_i‖ = ‖∑ᵢ cᵢ • proj_i‖
      simp only [g]
      rw [norm_smul, Complex.norm_I, one_mul]
      -- ‖∑ᵢ cᵢ • proj_i‖ ≤ ∑ᵢ ‖cᵢ‖ * ‖proj_i‖ ≤ ∑ᵢ ‖cᵢ‖ (since ‖proj_i‖ ≤ 1)
      -- Define the projection with explicit type
      let proj_i : Fin n → ((Fin n → ℂ) →L[ℂ] ℂ) := fun i => ContinuousLinearMap.proj i
      have h1 : ‖∑ i : Fin n, distributionPairingℂ_real ω (J i) • proj_i i‖
          ≤ ∑ i : Fin n, ‖distributionPairingℂ_real ω (J i) • proj_i i‖ :=
            norm_sum_le _ _
      have h2 : ∑ i : Fin n, ‖distributionPairingℂ_real ω (J i) • proj_i i‖
          ≤ ∑ i : Fin n, ‖distributionPairingℂ_real ω (J i)‖ := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_smul]
        calc ‖distributionPairingℂ_real ω (J i)‖ * ‖proj_i i‖
            ≤ ‖distributionPairingℂ_real ω (J i)‖ * 1 := by
              apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
              -- ‖proj_i‖ ≤ 1 by operator norm bound
              refine ContinuousLinearMap.opNorm_le_iff (by norm_num : (0 : ℝ) ≤ 1) |>.mpr ?_
              intro v
              simp only [proj_i, ContinuousLinearMap.proj_apply]
              calc ‖v i‖ ≤ ‖v‖ := norm_le_pi_norm v i
                _ = 1 * ‖v‖ := by ring
          _ = ‖distributionPairingℂ_real ω (J i)‖ := mul_one _
      -- Show that the sum with proj_i matches the original
      have h_eq : ∑ i : Fin n, distributionPairingℂ_real ω (J i) • ContinuousLinearMap.proj (R := ℂ) i =
          ∑ i : Fin n, distributionPairingℂ_real ω (J i) • proj_i i := rfl
      rw [h_eq]
      calc ‖∑ i : Fin n, distributionPairingℂ_real ω (J i) • proj_i i‖
          ≤ ∑ i : Fin n, ‖distributionPairingℂ_real ω (J i)‖ := le_trans h1 h2
        _ ≤ 1 + ∑ i : Fin n, ‖distributionPairingℂ_real ω (J i)‖ := by linarith

    -- Final combination
    calc Real.exp (-(ω (complex_testfunction_decompose (∑ i, z i • J i)).2)) * ‖g ω‖
        ≤ Real.exp (|ω (complex_testfunction_decompose (∑ i, z₀ i • J i)).2| +
                    ∑ i : Fin n, (|ω (complex_testfunction_decompose (J i)).1| + |ω (complex_testfunction_decompose (J i)).2|)) *
          ‖g ω‖ := by
          apply mul_le_mul_of_nonneg_right h_exp_final (norm_nonneg _)
      _ ≤ Real.exp (|ω (complex_testfunction_decompose (∑ i, z₀ i • J i)).2| +
                    ∑ i : Fin n, (|ω (complex_testfunction_decompose (J i)).1| + |ω (complex_testfunction_decompose (J i)).2|)) *
          (1 + ∑ i : Fin n, ‖distributionPairingℂ_real ω (J i)‖) := by
          apply mul_le_mul_of_nonneg_left h_g_bound (Real.exp_nonneg _)
      _ = bound ω := rfl

/-- The Gaussian Free Field satisfies the OS0 Analyticity axiom.

    This follows from the holomorphic integral theorem: the generating functional
    Z[∑ᵢ zᵢJᵢ] = ∫ exp(i⟨ω, ∑ᵢ zᵢJᵢ⟩) dμ(ω)
    is analytic in z because:
    1. The integrand is measurable in ω for each z
    2. The integrand is analytic in z for each ω
    3. The integral is locally bounded (in fact, bounded by 1 since |exp(ix)| = 1)
-/
theorem gaussianFreeField_satisfies_OS0 : OS0_Analyticity (μ_GFF m) := by
  intro n J
  -- Apply the holomorphic integral theorem
  -- We need to show AnalyticOn ℂ (fun z => Z[∑ᵢ zᵢJᵢ]) Set.univ
  unfold GJGeneratingFunctionalℂ
  -- Define the integrand as a function of z and ω
  let f : (Fin n → ℂ) → FieldConfiguration → ℂ :=
    fun z ω => Complex.exp (Complex.I * distributionPairingℂ_real ω (∑ i, z i • J i))
  -- The integral equals ∫ f z ω ∂μ
  show AnalyticOn ℂ (fun z => ∫ ω, f z ω ∂(μ_GFF m).toMeasure) Set.univ
  -- Apply the multivariate holomorphic integral theorem
  -- Use @ to explicitly provide the mass parameter m where needed
  exact holomorphic_integral_of_locally_L1_bound (μ_GFF m).toMeasure f
    (@gff_integrand_measurable m _ n J)
    (fun ω z₀ => gff_integrand_analytic n J ω z₀)
    (@gff_integrand_integrable m _ n J)
    (@gff_integrand_fderiv_measurable m _ n J)
    (@gff_integrand_fderiv_bound m _ n J)

end QFT
