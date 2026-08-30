/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Copyright (c) 2026 Sergey A. Cherkis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sergey A. Cherkis, Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/

import Mathlib.Tactic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Topology.Constructions

import OSforGFF.Spacetime.Basic
import OSforGFF.OS.Axioms
import OSforGFF.Covariance.ParsevalGeneric
import OSforGFF.General.FunctionalAnalysis
import OSforGFF.Covariance.RealForm
import OSforGFF.Measure.Construct
import OSforGFF.Measure.IsGaussian

/-!
# OS1 — Regularity (Exponential Bounds)

Proves |Z[f]| ≤ exp(c · ‖f‖²_{L²}) with p = 2 and c = 1/(2m²). The argument:

1. |Z[f]| = exp(−½ Re⟨f, Cf⟩_ℂ)
2. Decompose f = f_re + i·f_im, then Re⟨f, Cf⟩ = ⟨f_re, Cf_re⟩ − ⟨f_im, Cf_im⟩
3. Since C is positive semidefinite, −Re⟨f, Cf⟩ ≤ ⟨f_im, Cf_im⟩
4. In momentum space: ⟨g, Cg⟩ = ∫ |ĝ(k)|²/((2π)²|k|²+m²) dk ≤ ‖g‖²_{L²}/m²
   (Plancherel + bound 1/((2π)²|k|²+m²) ≤ 1/m²)
5. Combine: |Z[f]| ≤ exp(‖f‖²_{L²}/(2m²))

Local integrability of the two-point function `x ↦ C(0, x)` follows from global
integrability of the radial covariance profile (`GFFPropagator.integrable`).

## Main result

- `gaussianFreeField_satisfies_OS1`
-/

open MeasureTheory Complex BigOperators SchwartzMap Real QFT OSforGFF
open scoped MeasureTheory ENNReal

variable {d : ℕ} [Fact (2 ≤ d)]

/-! ## Preliminaries -/

omit [Fact (2 ≤ d)] in
/-- Plancherel (Schwartz): L² norm preservation for the Fourier transform.
    This follows directly from Mathlib's `SchwartzMap.integral_norm_sq_fourier`.
    Mathlib's Fourier transform is unitary-normalized, so no multiplicative constant is needed. -/
theorem fourier_plancherel_schwartz (g : SchwartzTestFunctionℂ d) :
    ∫ k, ‖(SchwartzMap.fourierTransformCLM ℂ g) k‖^2 ∂volume =
      ∫ x, ‖g x‖^2 ∂volume :=
  SchwartzMap.integral_norm_sq_fourier g

/-- **Two-point Schwinger function of the GFF**: the centered position-space covariance
    kernel `K(x) = C(0, x)`.

    Mathematically: ⟨φ(x)φ(0)⟩_μ = C(0, x) for the Gaussian measure with covariance C.
    The abstract `SchwingerTwoPointFunction` is defined as a mollified limit; for the GFF
    it agrees with this kernel away from the origin (`schwingerTwoPointFunction_eq_GFF`,
    via `double_mollifier_convergence`). -/
noncomputable def SchwingerTwoPointFunction_GFF (m : ℝ) [Fact (0 < m)] [GFFPropagator d m]
    (x : SpaceTime d) : ℝ :=
  freeCovarianceKernel d m x

/-- The GFF two-point function equals the centered covariance kernel by definition. -/
theorem schwingerTwoPoint_eq_freeCovariance (m : ℝ) [Fact (0 < m)] [GFFPropagator d m]
    (x : SpaceTime d) :
  SchwingerTwoPointFunction_GFF m x = freeCovarianceKernel d m x := rfl

/-- The abstract two-point Schwinger function of the GFF equals the concrete covariance
    kernel away from the origin: the mollified limit defining `SchwingerTwoPointFunction`
    evaluates to the continuous kernel via `schwingerTwoPointFunction_eq_kernel`. -/
theorem schwingerTwoPointFunction_eq_GFF (m : ℝ) [Fact (0 < m)] [GFFPropagator d m]
    (x : SpaceTime d) (hx : x ≠ 0) :
  SchwingerTwoPointFunction (gaussianFreeField_free (d := d) m) x
    = SchwingerTwoPointFunction_GFF m x := by
  have h_cont : ContinuousOn (freeCovarianceKernel d m)
      {y : SpaceTime d | y ≠ 0} := freeCovarianceKernel_continuousOn
  have h_S₂ : ∀ (f g : SchwartzTestFunction d),
      SchwingerFunction₂ (gaussianFreeField_free (d := d) m) f g =
      ∫ u, ∫ v, f u * freeCovarianceKernel d m (u - v) * g v := by
    -- Chain: S₂(f,g) = ∫ω (ωf)(ωg) dμ = freeCovarianceFormR m f g = ∫∫ f(u) C(u,v) g(v)
    -- where C(u,v) = K(u-v) by translation invariance
    intro f g
    -- Step 1: S₂ = ∫ω (ωf)(ωg) via schwinger_eq_covariance
    rw [schwinger_eq_covariance]
    -- Unfold distributionPairing to ω f
    simp only [distributionPairing]
    -- Step 2: For GFF, ∫ω (ωf)(ωg) = freeCovarianceFormR via schwinger_eq_covariance_real
    rw [GFFIsGaussian.schwinger_eq_covariance_real m f g]
    -- Step 3: freeCovarianceFormR = ∫∫ f(u) * freeCovariance(u,v) * g(v)
    unfold freeCovarianceFormR
    -- Step 4: freeCovariance(u,v) = K(u-v) by translation invariance
    congr 1
    ext u
    congr 1
    ext v
    rw [freeCovariance_eq_kernel u v]
  -- Apply the general kernel theorem
  rw [schwingerTwoPointFunction_eq_kernel (gaussianFreeField_free (d := d) m) x hx
        (freeCovarianceKernel d m) h_cont h_S₂]
  -- By definition of SchwingerTwoPointFunction_GFF
  rfl

/-- The abstract SchwingerTwoPointFunction equals the covariance kernel for the GFF.
    Note: Only holds for x ≠ 0 since the covariance is undefined at coincident points. -/
theorem schwingerTwoPointFunction_eq_freeCovariance (m : ℝ) [Fact (0 < m)] [GFFPropagator d m]
    (x : SpaceTime d) (hx : x ≠ 0) :
  SchwingerTwoPointFunction (gaussianFreeField_free (d := d) m) x = freeCovarianceKernel d m x := by
  rw [schwingerTwoPointFunction_eq_GFF m x hx, schwingerTwoPoint_eq_freeCovariance]

/-- The abstract two-point Schwinger function agrees a.e. with the covariance kernel:
    the two functions agree away from the origin, and `{0}` is Lebesgue-null. -/
lemma schwingerTwoPoint_ae_eq_kernel (m : ℝ) [Fact (0 < m)] [GFFPropagator d m] :
    (fun x => SchwingerTwoPointFunction (gaussianFreeField_free (d := d) m) x)
      =ᶠ[ae (volume : Measure (SpaceTime d))] freeCovarianceKernel d m := by
  have hd : 0 < d := by have := (Fact.out : 2 ≤ d); omega
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have : Nontrivial (SpaceTime d) := inferInstance
  -- The complement of {0} has full measure, so {x ≠ 0} ∈ ae volume
  have h_mem : {x : SpaceTime d | x ≠ 0} ∈ ae volume := by
    rw [MeasureTheory.mem_ae_iff]
    simp only [ne_eq, Set.compl_setOf, not_not]
    exact MeasureTheory.measure_singleton (0 : SpaceTime d)
  -- The functions agree on this set
  exact Filter.eventuallyEq_of_mem h_mem
    (fun x hx => schwingerTwoPointFunction_eq_freeCovariance m x hx)

/-! ## GFF Exponential Bound

Elementary bound on the GFF generating function using complex exponential properties.
-/

/-- The norm of the GFF generating function equals the exponential of minus one-half
    the real part of the covariance. This is an elementary property of complex exponentials:
    |exp(z)| = exp(Re z). -/
lemma gff_generating_norm_eq (m : ℝ) [Fact (0 < m)] [GFFPropagator d m] (f : SchwartzTestFunctionℂ d) :
  ‖GJGeneratingFunctionalℂ (gaussianFreeField_free (d := d) m) f‖ =
    Real.exp (-(1/2) * (freeCovarianceℂ_bilinear m f f).re) := by
  rw [gff_complex_generating, gff_two_point_equals_covarianceℂ_free, Complex.norm_exp]
  simp only [Complex.neg_re, Complex.mul_re]
  norm_num

/-- Using bilinearity and the real/imaginary decomposition, the real part of C(f,f)
    satisfies Re C(f,f) = C(Re f, Re f) - C(Im f, Im f). Combined with monotonicity
    of exp, this gives the bound exp(-1/2 Re C(f,f)) ≤ exp(1/2 C(Im f, Im f)). -/
lemma gff_generating_bound_by_imaginary (m : ℝ) [Fact (0 < m)] [GFFPropagator d m]
    (f : SchwartzTestFunctionℂ d) :
  Real.exp (-(1/2) * (freeCovarianceℂ_bilinear m f f).re) ≤
    Real.exp ((1/2) * (freeCovarianceℂ_bilinear m (toComplex (complex_testfunction_decompose f).2)
                                                    (toComplex (complex_testfunction_decompose f).2)).re) := by
  -- Apply monotonicity of exp: it suffices to show -(1/2) Re C(f,f) ≤ (1/2) C(Im f, Im f)
  apply Real.exp_le_exp.mpr
  -- Abbreviate the imaginary and real parts
  set fIm := (complex_testfunction_decompose f).2
  set fRe := (complex_testfunction_decompose f).1
  -- Equivalently: -Re C(f,f) ≤ Re C(toComplex fIm, toComplex fIm)
  suffices h : -(freeCovarianceℂ_bilinear m f f).re ≤
               (freeCovarianceℂ_bilinear m (toComplex fIm) (toComplex fIm)).re by linarith
  -- Expand using toComplex to connect with the bilinear expansion
  let frC := toComplex fRe
  let fiC := toComplex fIm
  have hf : f = frC + Complex.I • fiC := by
    ext x
    simpa [frC, fiC, fRe, fIm, toComplex_apply, smul_eq_mul, complex_testfunction_decompose]
      using complex_testfunction_decompose_recompose f x
  -- Expand the bilinear form using bilinearity
  have h_expand : freeCovarianceℂ_bilinear m f f =
      freeCovarianceℂ_bilinear m frC frC + Complex.I * freeCovarianceℂ_bilinear m frC fiC +
      Complex.I * freeCovarianceℂ_bilinear m fiC frC - freeCovarianceℂ_bilinear m fiC fiC := by
    calc freeCovarianceℂ_bilinear m f f
      _ = freeCovarianceℂ_bilinear m (frC + Complex.I • fiC) (frC + Complex.I • fiC) := by rw [hf]
      _ = freeCovarianceℂ_bilinear m frC (frC + Complex.I • fiC) +
          freeCovarianceℂ_bilinear m (Complex.I • fiC) (frC + Complex.I • fiC) := by
        rw [freeCovarianceℂ_bilinear_add_left]
      _ = freeCovarianceℂ_bilinear m frC frC + freeCovarianceℂ_bilinear m frC (Complex.I • fiC) +
          (freeCovarianceℂ_bilinear m (Complex.I • fiC) frC +
           freeCovarianceℂ_bilinear m (Complex.I • fiC) (Complex.I • fiC)) := by
        rw [freeCovarianceℂ_bilinear_add_right, freeCovarianceℂ_bilinear_add_right]
      _ = freeCovarianceℂ_bilinear m frC frC + Complex.I * freeCovarianceℂ_bilinear m frC fiC +
          Complex.I * freeCovarianceℂ_bilinear m fiC frC - freeCovarianceℂ_bilinear m fiC fiC := by
        rw [freeCovarianceℂ_bilinear_smul_right, freeCovarianceℂ_bilinear_smul_left,
            freeCovarianceℂ_bilinear_smul_left, freeCovarianceℂ_bilinear_smul_right]
        -- Now we have I * (I * ...) which equals -(...) by I^2 = -1
        rw [show Complex.I * (Complex.I * freeCovarianceℂ_bilinear m fiC fiC) =
                 -(freeCovarianceℂ_bilinear m fiC fiC) by
                 rw [← mul_assoc, Complex.I_mul_I]; ring]
        ring
  -- Take real part: Re C(f,f) = Re C(frC,frC) - Re C(fiC,fiC)
  -- The cross terms with I have zero real part, so they vanish
  have h_re : (freeCovarianceℂ_bilinear m f f).re =
              (freeCovarianceℂ_bilinear m frC frC).re - (freeCovarianceℂ_bilinear m fiC fiC).re := by
    rw [h_expand]
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im]
    -- For real test functions frC and fiC, the bilinear form produces real values
    -- so the imaginary parts are zero
    have h_im_zero : (freeCovarianceℂ_bilinear m frC fiC).im = 0 := by
      -- Use agreement with the real covariance on real test functions
      have h := QFT.freeCovarianceℂ_bilinear_agrees_on_reals m fRe fIm
      -- Take imaginary parts; RHS is ofReal, hence zero imaginary part
      simpa [frC, fiC, Complex.ofReal_im] using congrArg Complex.im h
    have h_im_zero' : (freeCovarianceℂ_bilinear m fiC frC).im = 0 := by
      -- Use symmetry
      have : freeCovarianceℂ_bilinear m fiC frC = freeCovarianceℂ_bilinear m frC fiC :=
        freeCovarianceℂ_bilinear_symm m fiC frC
      rw [this, h_im_zero]
    simp [h_im_zero, h_im_zero']
  -- Therefore: -Re C(f,f) = -Re C(frC,frC) + Re C(fiC,fiC)
  rw [h_re]
  -- Since Re C(frC,frC) ≥ 0 by positivity, we have the bound
  have h_pos : 0 ≤ (freeCovarianceℂ_bilinear m frC frC).re := by
    -- For real test functions frC = toComplex fRe, the complex conjugate is the identity
    -- so freeCovarianceℂ_bilinear agrees with freeCovarianceℂ
    rw [← freeCovarianceℂ_eq_bilinear_on_reals m]
    exact freeCovarianceℂ_positive (m := m) frC
  linarith

/-
The covariance of the imaginary part is bounded by (1/m²) times the L² norm squared.
This uses the momentum space representation and the bound 1/((2π)²‖k‖² + m²) ≤ 1/m²,
plus Plancherel and the pointwise bound |Im f| ≤ |f|.
-/
lemma covariance_imaginary_L2_bound (m : ℝ) [Fact (0 < m)] [GFFPropagator d m]
    (f : SchwartzTestFunctionℂ d) :
  (freeCovarianceℂ_bilinear m (toComplex (complex_testfunction_decompose f).2)
                              (toComplex (complex_testfunction_decompose f).2)).re ≤
    (1 / m^2) * ∫ x, ‖f x‖^2 ∂volume := by
  -- Abbreviations
  set fIm := (complex_testfunction_decompose f).2
  set F := (SchwartzMap.fourierTransformCLM ℂ (toComplex fIm))

  -- Parseval: real part of the covariance equals the momentum-space integral
  have h_parsevalC :
      (freeCovarianceℂ m (toComplex fIm) (toComplex fIm)).re
        = ∫ k, ‖(SchwartzMap.fourierTransformCLM ℂ (toComplex fIm)) k‖^2 * freePropagatorMom d m k ∂volume :=
    parseval_covariance_schwartz (toComplex fIm)

  -- For real test functions, complex covariance equals the complex bilinear form
  have h_eq_bilin :
      freeCovarianceℂ m (toComplex fIm) (toComplex fIm)
        = freeCovarianceℂ_bilinear m (toComplex fIm) (toComplex fIm) :=
    QFT.freeCovarianceℂ_eq_bilinear_on_reals m fIm fIm

  have h_re_eq :
      (freeCovarianceℂ_bilinear m (toComplex fIm) (toComplex fIm)).re
        = ∫ k, ‖F k‖^2 * freePropagatorMom d m k ∂volume := by
    simpa [h_eq_bilin, F]
      using h_parsevalC

  -- Bound the propagator: 1/((2π)²‖k‖² + m²) ≤ 1/m²
  have h_bound : ∀ k, freePropagatorMom d m k ≤ 1 / m^2 := by
    intro k
    unfold OSforGFF.freePropagatorMom
    have hmpos : 0 < m := Fact.out
    have hm2pos : 0 < m^2 := sq_pos_of_pos hmpos
    have hden : m^2 ≤ (2 * Real.pi)^2 * ‖k‖^2 + m^2 := by
      have : 0 ≤ (2 * Real.pi)^2 * ‖k‖^2 := by positivity
      linarith
    -- 0 < m^2 and m^2 ≤ (2π)²‖k‖² + m^2 ⇒ 1 / ((2π)²‖k‖² + m^2) ≤ 1 / m^2
    have := one_div_le_one_div_of_le (a := m^2) (b := (2 * Real.pi)^2 * ‖k‖^2 + m^2) (by exact hm2pos) hden
    simpa [one_div] using this

  -- Show integrability of ‖F‖² via MemLp → Integrable (square norm)
  have hF_memLp : MemLp F 2 volume := F.memLp 2 volume
  have hF_meas : AEStronglyMeasurable F volume := hF_memLp.1
  have hF_sq_int : Integrable (fun k => ‖F k‖^2) volume :=
    (memLp_two_iff_integrable_sq_norm hF_meas).1 hF_memLp

  -- Pull out the (1/m²) bound from the integral using a real integral monotonicity helper
  have h_dom_int : Integrable (fun k => (1 / m^2) * ‖F k‖^2) volume :=
    Integrable.const_mul hF_sq_int (1 / m^2)

  have h_nonneg : ∀ k, 0 ≤ ‖F k‖^2 * freePropagatorMom d m k := by
    intro k; exact mul_nonneg (by positivity) (freePropagatorMom_nonneg m k)

  have h_le_pt : ∀ k, ‖F k‖^2 * freePropagatorMom d m k ≤ (1 / m^2) * ‖F k‖^2 := by
    intro k
    have := mul_le_mul_of_nonneg_left (h_bound k) (by positivity : 0 ≤ ‖F k‖^2)
    simpa [mul_comm] using this

  have h_int_le :
      ∫ k, ‖F k‖^2 * freePropagatorMom d m k ∂volume
        ≤ ∫ k, (1 / m^2) * ‖F k‖^2 ∂volume := by
    exact real_integral_mono_of_le (μ := volume)
      (f := fun k => ‖F k‖^2 * freePropagatorMom d m k)
      (g := fun k => (1 / m^2) * ‖F k‖^2)
      h_dom_int h_nonneg h_le_pt

  -- Convert the right integral to pull out the constant
  have h_weight_pull :
      ∫ k, ‖F k‖^2 * freePropagatorMom d m k ∂volume ≤
        (1 / m^2) * ∫ k, ‖F k‖^2 ∂volume := by
    have h_const_pull : ∫ k, (1 / m^2) * ‖F k‖^2 ∂volume
        = (1 / m^2) * ∫ k, ‖F k‖^2 ∂volume :=
      integral_const_mul_eq (μ := volume) (c := (1 / m^2))
        (f := fun k => ‖F k‖^2) hF_sq_int
    calc
      ∫ k, ‖F k‖^2 * freePropagatorMom d m k ∂volume
          ≤ ∫ k, (1 / m^2) * ‖F k‖^2 ∂volume := h_int_le
      _ = (1 / m^2) * ∫ k, ‖F k‖^2 ∂volume := h_const_pull

  -- Combine with Parseval to reach a bound in terms of ‖F‖²
  have : (freeCovarianceℂ_bilinear m (toComplex fIm) (toComplex fIm)).re ≤
      (1 / m^2) * (∫ k, ‖F k‖^2 ∂volume) := by
    simpa [h_re_eq] using h_weight_pull

  -- Plancherel: ∫‖F‖² = ∫‖toComplex fIm‖²
  have h_plancherel : ∫ k, ‖F k‖^2 ∂volume = ∫ x, ‖(toComplex fIm) x‖^2 ∂volume := by
    simpa [F] using fourier_plancherel_schwartz (toComplex fIm)

  -- Pointwise bound: ‖Im f‖ ≤ ‖f‖ ⇒ squares and integrals obey same inequality
  have h_im_pointwise : ∀ x, ‖(toComplex fIm) x‖^2 ≤ ‖f x‖^2 := by
    intro x
    -- Rewrite the LHS as |Im(f x)| and square via multiplication monotonicity
    have hL : ‖(toComplex fIm) x‖ = |(f x).im| := by
      simp [toComplex_apply, fIm, complex_testfunction_decompose]
    -- Robust proof without external lemma names: |Im z|^2 ≤ ‖z‖^2
    have habs_sq : |(f x).im| ^ 2 = ((f x).im) ^ 2 := by
      simp [pow_two]
    have hineq : ((f x).im) ^ 2 ≤ (f x).re ^ 2 + (f x).im ^ 2 := by
      exact le_add_of_nonneg_left (sq_nonneg _)
    have hnorm_sq : ‖f x‖ ^ 2 = (f x).re ^ 2 + (f x).im ^ 2 := by
      simpa [Complex.normSq_apply, pow_two] using (Complex.sq_norm (f x))
    have hsq : |(f x).im| ^ 2 ≤ ‖f x‖ ^ 2 := by simpa [habs_sq, hnorm_sq] using hineq
    simpa [hL, fIm] using hsq

  -- Show integrability of both sides to apply integral monotonicity
  have hIm_memLp : MemLp (toComplex fIm) 2 volume := (toComplex fIm).memLp 2 volume
  have hIm_meas : AEStronglyMeasurable (toComplex fIm) volume := hIm_memLp.1
  have hIm_sq_int : Integrable (fun x => ‖(toComplex fIm) x‖^2) volume :=
    (memLp_two_iff_integrable_sq_norm hIm_meas).1 hIm_memLp

  have hf_memLp : MemLp f 2 volume := f.memLp 2 volume
  have hf_meas : AEStronglyMeasurable f volume := hf_memLp.1
  have hf_sq_int : Integrable (fun x => ‖f x‖^2) volume :=
    (memLp_two_iff_integrable_sq_norm hf_meas).1 hf_memLp

  have h_imag_bound : ∫ x, ‖(toComplex fIm) x‖^2 ∂volume ≤ ∫ x, ‖f x‖^2 ∂volume := by
    exact real_integral_mono_of_le (μ := volume)
      (f := fun x => ‖(toComplex fIm) x‖^2)
      (g := fun x => ‖f x‖^2)
      hf_sq_int (by intro x; exact sq_nonneg _) (by intro x; simpa using h_im_pointwise x)

  -- Final chain of inequalities
  calc (freeCovarianceℂ_bilinear m (toComplex fIm) (toComplex fIm)).re
      ≤ (1 / m^2) * (∫ k, ‖F k‖^2 ∂volume) := this
    _ = (1 / m^2) * ∫ x, ‖(toComplex fIm) x‖^2 ∂volume := by simp [h_plancherel]
    _ ≤ (1 / m^2) * ∫ x, ‖f x‖^2 ∂volume := by
          exact mul_le_mul_of_nonneg_left h_imag_bound (by positivity)


/-- The GFF generating functional satisfies the exponential bound
    |Z[f]| ≤ exp((1/2m²)||f||²_{L²}). This combines the norm equality,
    the bound by imaginary part, and the L² bound to give the final OS1 estimate. -/
lemma gff_generating_L2_bound (m : ℝ) [Fact (0 < m)] [GFFPropagator d m] (f : SchwartzTestFunctionℂ d) :
  ‖GJGeneratingFunctionalℂ (gaussianFreeField_free (d := d) m) f‖ ≤
    Real.exp ((1 / (2 * m^2)) * ∫ x, ‖f x‖^2 ∂volume) := by
  set fIm := (complex_testfunction_decompose f).2
  calc ‖GJGeneratingFunctionalℂ (gaussianFreeField_free (d := d) m) f‖
    _ = Real.exp (-(1/2) * (freeCovarianceℂ_bilinear m f f).re) := gff_generating_norm_eq m f
    _ ≤ Real.exp ((1/2) * (freeCovarianceℂ_bilinear m (toComplex fIm) (toComplex fIm)).re) :=
        gff_generating_bound_by_imaginary m f
    _ ≤ Real.exp ((1/2) * ((1 / m^2) * ∫ x, ‖f x‖^2 ∂volume)) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_left (covariance_imaginary_L2_bound m f) (by norm_num)
    _ = Real.exp ((1 / (2 * m^2)) * ∫ x, ‖f x‖^2 ∂volume) := by ring_nf

/-! ## Two-Point Function Local Integrability -/

/-- The two-point Schwinger function is locally integrable: it agrees a.e. with the
    covariance kernel `x ↦ C(x, 0)`, which is globally integrable
    (`GFFPropagator.integrable`). -/
lemma gff_two_point_locally_integrable (m : ℝ) [Fact (0 < m)] [GFFPropagator d m] :
  TwoPointIntegrable (gaussianFreeField_free (d := d) m) := by
  unfold TwoPointIntegrable
  exact ((freeCovarianceKernel_integrable (d := d) (m := m)).congr
    (schwingerTwoPoint_ae_eq_kernel m).symm).locallyIntegrable

/-! ## OS1 Verification for the GFF

Using the exponential L²-bound for the generating functional and local
integrability of the two-point function, we verify OS1 as stated in
`OS_Axioms.lean` (with the p-th power appearing inside the exponential).
-/

open MeasureTheory

/-- The Gaussian free field satisfies OS1 regularity with `p = 2` and
    `c = 1/(2 m^2)`. This uses `gff_generating_L2_bound` and
    `gff_two_point_locally_integrable` established above. -/
theorem gaussianFreeField_satisfies_OS1 (m : ℝ) [Fact (0 < m)] [GFFPropagator d m] :
  OS1_Regularity (gaussianFreeField_free (d := d) m) := by
  -- Choose parameters p = 2 and c = 1/(2 m^2)
  refine ⟨(2 : ℝ), (1 / (2 * m^2)), by norm_num, by norm_num, ?cpos, ?bound, ?tpInt⟩
  · -- c > 0
    have hmpos : 0 < m := Fact.out
    have hm2pos : 0 < m^2 := by exact sq_pos_of_pos hmpos
    have hdenpos : 0 < 2 * m^2 := by nlinarith
    exact one_div_pos.mpr hdenpos
  · -- Exponential bound: |Z[f]| ≤ exp(c(∫|f| + ∫|f|^2))
    intro f
    -- Start from the established L² bound
    have hL2_nat : ‖GJGeneratingFunctionalℂ (gaussianFreeField_free (d := d) m) f‖ ≤
        Real.exp ((1 / (2 * m^2)) * ∫ x, ‖f x‖^(2:ℕ) ∂volume) :=
      gff_generating_L2_bound m f
    -- Convert the exponent from ℕ to ℝ
    have heq : ∫ x, ‖f x‖^(2:ℕ) ∂volume = ∫ x, ‖f x‖^(2:ℝ) ∂volume := by
      congr 1
      funext x
      norm_num
    have hL2 : ‖GJGeneratingFunctionalℂ (gaussianFreeField_free (d := d) m) f‖ ≤
        Real.exp ((1 / (2 * m^2)) * ∫ x, ‖f x‖^(2:ℝ) ∂volume) := by
      rw [← heq]
      exact hL2_nat
    -- Strengthen the exponent by adding the nonnegative L¹ term
    have hmono : (1 / (2 * m^2)) * ∫ x, ‖f x‖^(2:ℝ) ∂volume ≤
                 (1 / (2 * m^2)) * (∫ x, ‖f x‖ ∂volume + ∫ x, ‖f x‖^(2:ℝ) ∂volume) := by
      -- This is immediate since a ≤ a + b for any b ≥ 0; here b = ∫|f| ≥ 0
      have hI1_nonneg : 0 ≤ ∫ x, ‖f x‖ ∂volume := by
        -- Pointwise nonnegativity of the integrand implies nonnegativity of the integral
        have hpt : ∀ x, 0 ≤ ‖f x‖ := by intro x; exact norm_nonneg _
        -- `integral_nonneg` is applicable to nonnegative functions over `volume`
        exact integral_nonneg hpt
      have hcpos : 0 ≤ (1 / (2 * m^2)) := by positivity
      -- Use `add_nonneg` and rearrange
      have hadd : (1 / (2 * m^2)) * ∫ x, ‖f x‖ ∂volume ≥ 0 := by
        exact mul_nonneg hcpos hI1_nonneg
      calc (1 / (2 * m^2)) * ∫ x, ‖f x‖^(2:ℝ) ∂volume
        _ ≤ (1 / (2 * m^2)) * ∫ x, ‖f x‖^(2:ℝ) ∂volume + (1 / (2 * m^2)) * ∫ x, ‖f x‖ ∂volume :=
            le_add_of_nonneg_right hadd
        _ = (1 / (2 * m^2)) * (∫ x, ‖f x‖ ∂volume + ∫ x, ‖f x‖^(2:ℝ) ∂volume) := by
            rw [mul_add, add_comm]
    -- Apply monotonicity of the exponential function to close the proof
    calc ‖GJGeneratingFunctionalℂ (gaussianFreeField_free (d := d) m) f‖
        ≤ Real.exp ((1 / (2 * m^2)) * ∫ x, ‖f x‖^(2:ℝ) ∂volume) := hL2
      _ ≤ Real.exp ((1 / (2 * m^2)) * (∫ x, ‖f x‖ ∂volume + ∫ x, ‖f x‖^(2:ℝ) ∂volume)) :=
          Real.exp_le_exp.mpr hmono
  · -- Two-point integrability for p = 2
    intro hp2
    -- `hp2` is unused since we picked `p = 2` explicitly
    simpa using gff_two_point_locally_integrable m
