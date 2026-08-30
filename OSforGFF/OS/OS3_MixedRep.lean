/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Copyright (c) 2026 Sergey A. Cherkis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sergey A. Cherkis, Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/

import OSforGFF.OS.OS3_MixedRepInfra

/-!
# OS3 — Mixed Representation via Schwinger Parametrization

Derives the mixed (momentum-position) representation of the covariance bilinear form
by performing the Fubini exchanges justified in `OS3_MixedRepInfra`. The chain is:

1. Schwinger → heat kernel: ⟨Θf, Cf⟩ = ∫₀^∞ e^{−sm²} [∫∫ f*(x) f(y) H(s,|Θx−y|)] ds
2. Fourier representation of heat kernel introduces spatial momenta k̄
3. k₀ Gaussian integral: ∫ e^{ik₀(x₀+y₀)} e^{−sk₀²} dk₀ = √(π/s) e^{−(x₀+y₀)²/4s}
4. Laplace transform in s: ∫₀^∞ s^{−1/2} e^{−(x₀+y₀)²/4s − sω²} ds = √(π/ω²) e^{−ω|x₀+y₀|}
5. Fubini theorems (from `OS3_MixedRepInfra`) justify every change of integration order.

The final result (Bessel K_{1/2} identity) is:

  ⟨Θf, Cf⟩ = (1/(2(2π)^{d−1})) ∫_{k̄} ∫∫ f*(x) f(y) (1/ω) e^{−ω|x₀+y₀|} e^{ik̄·(x̄−ȳ)} dk̄ dx dy

with ω = √(‖k̄‖² + m²) the relativistic energy of the spatial momentum k̄ ∈ ℝ^{d−1}.
This is the integration order exchange from eq. (4.19) that the naive approach could
not justify due to the non-absolute-integrability of 1/√(k²+m²) in the spatial
momentum space. The entry point is `GFFPropagator.schwinger_eq`, so the derivation
holds for every dimension d ≥ 2.

## Physical Interpretation

The mixed representation exhibits:
- **Causality**: Exponential decay `e^(-ω|x⁰+y⁰|)` for `x⁰,y⁰ ≤ 0` (reflection positivity support).
- **On-shell condition**: The energy-momentum relation `ω² = |k|² + m²` is built into the structure.
- **Feynman propagator**: The k⁰ integral has poles at ±iω, corresponding to particle propagation.

## References

- Osterwalder & Schrader, "Axioms for Euclidean Green's Functions I & II" (1973, 1975)
- Glimm & Jaffe, "Quantum Physics: A Functional Integral Point of View" (1987), §11.4
- Haag, "Local Quantum Physics" (1996), §V.3

-/

open MeasureTheory Complex Real Filter QFT LaplaceIntegral OSforGFF
open TopologicalSpace
open scoped Real InnerProductSpace BigOperators

noncomputable section

variable {d : ℕ} [Fact (2 ≤ d)] {m : ℝ} [Fact (0 < m)]

/-- The 1D Gaussian Fourier transform in real form:
    ∫ exp(-ik₀t) exp(-sk₀²) dk₀ = √(π/s) exp(-t²/(4s))

    This follows from Mathlib's `fourierIntegral_gaussian`. -/
lemma gaussian_fourier_1d (s : ℝ) (hs : 0 < s) (t : ℝ) :
    ∫ k₀ : ℝ, Complex.exp (-Complex.I * k₀ * t) * Complex.exp (-(s : ℂ) * k₀^2) =
    Real.sqrt (π / s) * Complex.exp (-(t^2 / (4 * s) : ℝ)) := by
  -- Use Mathlib's fourierIntegral_gaussian with b = s and t' = -t
  -- Mathlib: ∫ x, cexp(I * t * x) * cexp(-b * x²) = (π/b)^(1/2) * cexp(-t²/(4b))
  have hs_re : 0 < (s : ℂ).re := by simp [hs]
  have h := fourierIntegral_gaussian hs_re ((-t : ℝ) : ℂ)
  -- Rewrite LHS to match Mathlib's form
  have h_lhs : ∫ k₀ : ℝ, Complex.exp (-Complex.I * k₀ * t) * Complex.exp (-(s : ℂ) * k₀^2) =
               ∫ x : ℝ, Complex.exp (Complex.I * (-t : ℂ) * x) * Complex.exp (-(s : ℂ) * x^2) := by
    congr 1
    ext x
    congr 2
    ring
  -- Need to convert ↑(-t) to -↑t
  have h_neg : ((-t : ℝ) : ℂ) = -(t : ℂ) := by push_cast; ring
  simp only [h_neg] at h
  rw [h_lhs, h]
  -- Now simplify RHS: (π/s)^(1/2) * cexp(-(-t)²/(4s)) = √(π/s) * cexp(-t²/(4s))
  congr 1
  · -- (π/s)^(1/2) = √(π/s) as complex
    have h_pos : 0 < π / s := div_pos Real.pi_pos hs
    -- Key: (x : ℂ)^(1/2 : ℂ) = (x^(1/2) : ℂ) for x ≥ 0
    have h_half : (1 / 2 : ℂ) = (↑(1 / 2 : ℝ) : ℂ) := by norm_num
    rw [h_half]
    have h_cpow : (↑(π / s : ℝ) : ℂ) ^ (↑(1 / 2 : ℝ) : ℂ) = ↑((π / s : ℝ) ^ (1 / 2 : ℝ)) :=
      (Complex.ofReal_cpow (le_of_lt h_pos) (1 / 2)).symm
    have h_div : (↑π / ↑s : ℂ) = (↑(π / s : ℝ) : ℂ) := by push_cast; ring
    rw [h_div, h_cpow]
    congr 1
    rw [Real.sqrt_eq_rpow]
  · -- (-t)² = t²
    congr 1
    push_cast
    ring

/-- Gaussian exponential factorizes: exp(-s‖k‖²) = exp(-sk₀²) × exp(-s‖k_sp‖²) -/
lemma gaussian_exp_factorize (s : ℂ) (k : (SpaceTime d)) :
    Complex.exp (-s * ‖k‖^2) =
    Complex.exp (-s * (k 0)^2) * Complex.exp (-s * ‖spatialPart k‖^2) := by
  rw [← Complex.exp_add]
  congr 1
  -- Use the real decomposition: ‖k‖^2 = (k 0)^2 + ‖spatialPart k‖^2
  have h : (‖k‖^2 : ℝ) = (k 0)^2 + ‖spatialPart k‖^2 := spacetime_norm_sq_decompose k
  -- Note: the goal has (↑‖k‖)^2 not ↑(‖k‖^2), so we need to simplify first
  simp only [← Complex.ofReal_pow]
  -- Now goal is: -s * ↑(‖k‖^2) = -s * ↑((k 0)^2) + -s * ↑(‖spatialPart k‖^2)
  rw [h]
  push_cast
  ring

/-- The k₀-integral evaluates to √(π/s) exp(-t²/(4s)) times the k_sp-dependent factor.

    For z = Θx - y with z₀ = -x₀ - y₀:
    ∫_k exp(-ik·z) exp(-s|k|²) = (∫_{k₀} exp(-ik₀z₀) exp(-sk₀²)) × (∫_{k_sp} exp(-ik_sp·z_sp) exp(-s|k_sp|²))
                                = √(π/s) exp(-z₀²/(4s)) × ∫_{k_sp} exp(-ik_sp·z_sp) exp(-s|k_sp|²) -/
lemma k_integral_after_k0_eval (s : ℝ) (hs : 0 < s) (z : (SpaceTime d)) :
    ∫ k : (SpaceTime d), Complex.exp (-Complex.I * ⟪k, z⟫_ℝ) * Complex.exp (-(s : ℂ) * ‖k‖^2) =
    (Real.sqrt (π / s) : ℂ) * Complex.exp (-(((z 0)^2 / (4 * s)) : ℝ)) *
      ∫ k_sp : (SpatialCoords d), Complex.exp (-Complex.I * spatialDot k_sp (spatialPart z)) *
                               Complex.exp (-(s : ℂ) * ‖k_sp‖^2) := by
  -- Step 1: Factor the integrand into k₀-part × k_sp-part using existing lemmas
  have h_factor : ∀ k : (SpaceTime d),
      Complex.exp (-Complex.I * ⟪k, z⟫_ℝ) * Complex.exp (-(s : ℂ) * ‖k‖^2) =
      (Complex.exp (-Complex.I * (k 0 * z 0)) * Complex.exp (-(s : ℂ) * (k 0)^2)) *
      (Complex.exp (-Complex.I * spatialDot (spatialPart k) (spatialPart z)) *
       Complex.exp (-(s : ℂ) * ‖spatialPart k‖^2)) := by
    intro k
    -- Use gaussian_exp_factorize for the norm part
    have h_gauss := gaussian_exp_factorize (s : ℂ) k
    -- Use spacetime_inner_decompose for the inner product part
    have h_inner := spacetime_inner_decompose k z
    -- Factor the inner product exponential
    have h_inner_exp : Complex.exp (-Complex.I * ⟪k, z⟫_ℝ) =
        Complex.exp (-Complex.I * (k 0 * z 0)) *
        Complex.exp (-Complex.I * spatialDot (spatialPart k) (spatialPart z)) := by
      rw [h_inner, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [h_inner_exp, h_gauss]
    ring
  -- Step 2: Rewrite integrand using factorization
  conv_lhs => arg 2; ext k; rw [h_factor k]
  -- Step 3: Integrability for k₀ (1D Gaussian)
  -- Use Mathlib's integrable_cexp_neg_mul_sq_norm_add with V = ℝ, d = 1
  -- This gives ∫ exp(-s * k₀² + c * ⟪1, k₀⟫) where ⟪1, k₀⟫_ℝ = k₀
  have h_int_k0 : Integrable (fun k₀ : ℝ =>
      Complex.exp (-Complex.I * (k₀ * z 0)) * Complex.exp (-(s : ℂ) * k₀^2)) volume := by
    have hs_cplx : 0 < (s : ℂ).re := by simp [hs]
    have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℝ) hs_cplx (-Complex.I * z 0) 1
    -- The lemma gives: Integrable (fun k₀ ↦ cexp(-s * |k₀|² + (-I * z0) * ⟪1, k₀⟫_ℝ))
    -- Since ⟪1, k₀⟫_ℝ = 1 * k₀ = k₀ in ℝ, this is: cexp(-s * k₀² - I * z0 * k₀)
    convert h using 1
    ext k₀
    rw [← Complex.exp_add]
    congr 1
    -- Goal: -I * (k₀ * z0) + (-s * k₀²) = -s * |k₀|² + (-I * z0) * ⟪1, k₀⟫
    -- Use real_inner_eq_mul: ⟪1, k₀⟫_ℝ = 1 * k₀ = k₀
    rw [real_inner_eq_mul, one_mul]
    simp only [Real.norm_eq_abs, sq_abs, ← Complex.ofReal_pow, ← Complex.ofReal_neg]
    -- The goal is now algebraic - both sides are equal by commutativity/associativity
    -- -I * (↑k₀ * ↑z0) + ↑(-s) * ↑(k₀²) = ↑(-s) * ↑(k₀²) + -I * ↑z0 * ↑k₀
    ring
  -- Step 4: Integrability for k_sp (3D Gaussian)
  -- The lemma gives: Integrable (fun v ↦ cexp(-s * ‖v‖² + (-I) * ⟪z_sp, v⟫_ℝ))
  have h_int_ksp : Integrable (fun k_sp : (SpatialCoords d) =>
      Complex.exp (-Complex.I * spatialDot k_sp (spatialPart z)) *
      Complex.exp (-(s : ℂ) * ‖k_sp‖^2)) volume := by
    have hs_cplx : 0 < (s : ℂ).re := by simp [hs]
    have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add_of_euclideanSpace
      hs_cplx (-Complex.I) (spatialPart z)
    convert h using 1
    ext k_sp
    rw [← Complex.exp_add]
    congr 1
    -- Goal: match -I * spatialDot(k_sp, z_sp) + (-s * ‖k_sp‖²) with -s * ‖k_sp‖² + (-I) * ⟪z_sp, k_sp⟫
    -- Use spatialDot_eq_inner: spatialDot k z = ⟪k, z⟫_ℝ, and inner product is symmetric
    rw [spatialDot_eq_inner]
    simp only [← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_neg]
    -- The inner product is symmetric
    rw [real_inner_comm]
    push_cast
    ring
  -- Step 5: Apply integral_spacetime_prod_split
  rw [integral_spacetime_prod_split h_int_k0 h_int_ksp]
  -- Step 6: Apply gaussian_fourier_1d to k₀ integral
  have h_k0 : ∫ k₀ : ℝ, Complex.exp (-Complex.I * (k₀ * z 0)) * Complex.exp (-(s : ℂ) * k₀^2) =
              Real.sqrt (π / s) * Complex.exp (-(((z 0)^2 / (4 * s)) : ℝ)) := by
    have h := gaussian_fourier_1d s hs (z 0)
    -- gaussian_fourier_1d gives: ∫ k₀, exp(-I * k₀ * z0) * exp(-s * k₀²) = √(π/s) * exp(-z0²/(4s))
    -- The difference is associativity: -I * (k₀ * z0) vs (-I * k₀) * z0, which are equal
    -- Show integrands are pointwise equal
    have h_eq : ∀ k₀ : ℝ, Complex.exp (-Complex.I * (k₀ * z 0)) * Complex.exp (-(s : ℂ) * k₀^2) =
                          Complex.exp (-Complex.I * k₀ * (z 0)) * Complex.exp (-(s : ℂ) * k₀^2) := by
      intro k₀
      congr 2
      ring
    simp_rw [h_eq]
    exact h
  rw [h_k0]

/-- The time component of (timeReflection x - y). -/
lemma timeReflection_sub_zero (x y : (SpaceTime d)) :
    (timeReflection x - y) 0 = -(x 0) - y 0 := rfl

/-- The spatial part of (timeReflection x - y) equals spatialPart x - spatialPart y. -/
lemma spatialPart_timeReflection_sub (x y : (SpaceTime d)) :
    spatialPart (timeReflection x - y) = spatialPart x - spatialPart y := rfl

/-- **THEOREM**: Heat kernel bilinear form after k₀ integration.

    Starting from the Schwinger representation with heat kernel H(s,r):

    ∫₀^∞ exp(-sm²) ∫∫ f̄(x)f(y) H(s, |Θx-y|) dx dy ds

    After substituting H(s,r) = (2π)^{-d} ∫_k exp(-ik·z) exp(-s|k|²) and
    performing the k₀ integral using the 1D Gaussian FT:

    ∫_{-∞}^∞ exp(-ik₀t) exp(-sk₀²) dk₀ = √(π/s) · exp(-t²/(4s))

    we obtain:

    (2π)^{-4} ∫₀^∞ ∫_p̄ ∫∫ f̄(x)f(y) √(π/s) exp(-t²/(4s)) exp(-s(|p̄|² + m²)) exp(-ip̄·r̄) dx dy d³p̄ ds

    where t = -x₀ - y₀ (time separation under reflection) and r̄ = x̄ - ȳ (spatial separation).

    The exp(-sm²) factor combines with exp(-s|p̄|²) to give exp(-s(|p̄|² + m²)). -/
theorem heatKernel_bilinear_fourier_form (m : ℝ) [Fact (0 < m)] (f : (SchwartzTestFunctionℂ d)) :
    ∫ s in Set.Ioi 0, (Real.exp (-s * m^2) : ℂ) *
      ∫ x : (SpaceTime d), ∫ y : (SpaceTime d),
        (starRingEnd ℂ (f x)) * f y * heatKernelProfile d s ‖timeReflection x - y‖ =
    (1 / (2 * π) ^ d : ℝ) *
    ∫ s in Set.Ioi 0, ∫ k_sp : (SpatialCoords d), ∫ x : (SpaceTime d), ∫ y : (SpaceTime d),
      (starRingEnd ℂ (f x)) * f y *
        (Real.sqrt (π / s) : ℂ) * Complex.exp (-((-(x 0) - y 0)^2 / (4 * s) : ℝ)) *
        Complex.exp (-(s : ℂ) * (‖k_sp‖^2 + m^2)) *
        Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y)) := by
  -- Step 1: For s > 0, substitute heatKernel_eq_gaussianFT
  have h_hk : ∀ s : ℝ, 0 < s → ∀ z : (SpaceTime d),
      (heatKernelProfile d s ‖z‖ : ℂ) =
      (1 / (2 * π) ^ d : ℝ) *
      ∫ k : (SpaceTime d), Complex.exp (-Complex.I * ⟪k, z⟫_ℝ) * Complex.exp (-(s : ℂ) * ‖k‖^2) :=
    fun s hs z => heatKernel_eq_gaussianFT s hs z

  -- Step 2: Rewrite LHS using h_hk under the s-integral
  have h_step1 : ∫ s in Set.Ioi 0, (Real.exp (-s * m^2) : ℂ) *
      ∫ x : (SpaceTime d), ∫ y : (SpaceTime d),
        (starRingEnd ℂ (f x)) * f y * heatKernelProfile d s ‖timeReflection x - y‖ =
      ∫ s in Set.Ioi 0, (Real.exp (-s * m^2) : ℂ) *
        ∫ x : (SpaceTime d), ∫ y : (SpaceTime d),
          (starRingEnd ℂ (f x)) * f y *
          ((1 / (2 * π) ^ d : ℝ) *
           ∫ k : (SpaceTime d), Complex.exp (-Complex.I * ⟪k, timeReflection x - y⟫_ℝ) *
                            Complex.exp (-(s : ℂ) * ‖k‖^2)) := by
    apply MeasureTheory.setIntegral_congr_ae measurableSet_Ioi
    filter_upwards with s hs
    congr 1
    apply integral_congr_ae
    filter_upwards with x
    apply integral_congr_ae
    filter_upwards with y
    congr 1
    exact h_hk s (Set.mem_Ioi.mp hs) (timeReflection x - y)

  -- Step 3: Apply k_integral_after_k0_eval to evaluate the k-integral
  -- For each (s, x, y), this replaces the k-integral with:
  -- √(π/s) exp(-z₀²/(4s)) × ∫_{k_sp} exp(-I k_sp·z_sp) exp(-s‖k_sp‖²)
  -- where z = Θx - y, z₀ = -(x₀) - y₀, z_sp = x_sp - y_sp
  have h_step2 : ∫ s in Set.Ioi 0, (Real.exp (-s * m^2) : ℂ) *
      ∫ x : (SpaceTime d), ∫ y : (SpaceTime d),
        (starRingEnd ℂ (f x)) * f y *
        ((1 / (2 * π) ^ d : ℝ) *
         ∫ k : (SpaceTime d), Complex.exp (-Complex.I * ⟪k, timeReflection x - y⟫_ℝ) *
                          Complex.exp (-(s : ℂ) * ‖k‖^2)) =
      ∫ s in Set.Ioi 0, (Real.exp (-s * m^2) : ℂ) *
        ∫ x : (SpaceTime d), ∫ y : (SpaceTime d),
          (starRingEnd ℂ (f x)) * f y *
          ((1 / (2 * π) ^ d : ℝ) *
           ((Real.sqrt (π / s) : ℂ) * Complex.exp (-(((-(x 0) - y 0)^2 / (4 * s)) : ℝ)) *
            ∫ k_sp : (SpatialCoords d),
              Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y)) *
              Complex.exp (-(s : ℂ) * ‖k_sp‖^2))) := by
    apply MeasureTheory.setIntegral_congr_ae measurableSet_Ioi
    filter_upwards with s hs
    have hs_pos : 0 < s := Set.mem_Ioi.mp hs
    congr 1
    apply integral_congr_ae
    filter_upwards with x
    apply integral_congr_ae
    filter_upwards with y
    congr 1
    congr 1
    -- Apply k_integral_after_k0_eval
    have h_k := k_integral_after_k0_eval s hs_pos (timeReflection x - y)
    -- Rewrite using helper lemmas for time and spatial components
    rw [timeReflection_sub_zero, spatialPart_timeReflection_sub] at h_k
    exact h_k

  -- Step 4: Rearrange the integrand to match fubini_ksp_xy_swap LHS form
  -- Move the constant outside x,y integrals and swap k_sp integrand order
  have h_step3 : ∫ s in Set.Ioi 0, (Real.exp (-s * m^2) : ℂ) *
      ∫ x : (SpaceTime d), ∫ y : (SpaceTime d),
        (starRingEnd ℂ (f x)) * f y *
        ((1 / (2 * π) ^ d : ℝ) *
         ((Real.sqrt (π / s) : ℂ) * Complex.exp (-(((-(x 0) - y 0)^2 / (4 * s)) : ℝ)) *
          ∫ k_sp : (SpatialCoords d),
            Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y)) *
            Complex.exp (-(s : ℂ) * ‖k_sp‖^2))) =
      ∫ s in Set.Ioi 0, (Real.exp (-s * m^2) : ℂ) *
        ((1 / (2 * π) ^ d : ℝ) *
         ∫ x : (SpaceTime d), ∫ y : (SpaceTime d),
           (starRingEnd ℂ (f x)) * f y *
           (Real.sqrt (π / s) : ℂ) * Complex.exp (-(((-(x 0) - y 0)^2 / (4 * s)) : ℝ)) *
           ∫ k_sp : (SpatialCoords d),
             Complex.exp (-(s : ℂ) * ‖k_sp‖^2) *
             Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y))) := by
    apply MeasureTheory.setIntegral_congr_ae measurableSet_Ioi
    filter_upwards with s hs
    congr 1
    -- First reorder the k_sp integrand using mul_comm
    have h_ksp_reorder : ∀ x y : (SpaceTime d),
        (∫ k_sp : (SpatialCoords d),
          Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y)) *
          Complex.exp (-(s : ℂ) * ‖k_sp‖^2)) =
        (∫ k_sp : (SpatialCoords d),
          Complex.exp (-(s : ℂ) * ‖k_sp‖^2) *
          Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y))) := by
      intro x y
      apply integral_congr_ae
      filter_upwards with k_sp
      ring
    -- Now show the full equality
    simp_rw [h_ksp_reorder]
    have h_icm : ∀ (c : ℂ) (g : (SpaceTime d) → ℂ),
        c * ∫ a, g a = ∫ a, c * g a :=
      fun c g => (MeasureTheory.integral_const_mul (L := ℂ) c g).symm
    rw [h_icm]
    apply integral_congr_ae
    filter_upwards with x
    rw [h_icm]
    apply integral_congr_ae
    filter_upwards with y
    ring

  -- Step 5: Apply fubini_ksp_xy_swap to swap k_sp outside (x, y)
  have h_step4 : ∫ s in Set.Ioi 0, (Real.exp (-s * m^2) : ℂ) *
      ((1 / (2 * π) ^ d : ℝ) *
       ∫ x : (SpaceTime d), ∫ y : (SpaceTime d),
         (starRingEnd ℂ (f x)) * f y *
         (Real.sqrt (π / s) : ℂ) * Complex.exp (-(((-(x 0) - y 0)^2 / (4 * s)) : ℝ)) *
         ∫ k_sp : (SpatialCoords d),
           Complex.exp (-(s : ℂ) * ‖k_sp‖^2) *
           Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y))) =
      ∫ s in Set.Ioi 0, (Real.exp (-s * m^2) : ℂ) *
        ((1 / (2 * π) ^ d : ℝ) *
         ∫ k_sp : (SpatialCoords d), ∫ x : (SpaceTime d), ∫ y : (SpaceTime d),
           (starRingEnd ℂ (f x)) * f y *
           (Real.sqrt (π / s) : ℂ) * Complex.exp (-(((-(x 0) - y 0)^2 / (4 * s)) : ℝ)) *
           Complex.exp (-(s : ℂ) * ‖k_sp‖^2) *
           Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y))) := by
    apply MeasureTheory.setIntegral_congr_ae measurableSet_Ioi
    filter_upwards with s hs
    have hs_pos : 0 < s := Set.mem_Ioi.mp hs
    congr 1
    congr 1
    exact fubini_ksp_xy_swap s hs_pos f

  -- Step 6: Factor out (1/(2π)^d) from the s-integral
  have h_step5 : ∫ s in Set.Ioi 0, (Real.exp (-s * m^2) : ℂ) *
      ((1 / (2 * π) ^ d : ℝ) *
       ∫ k_sp : (SpatialCoords d), ∫ x : (SpaceTime d), ∫ y : (SpaceTime d),
         (starRingEnd ℂ (f x)) * f y *
         (Real.sqrt (π / s) : ℂ) * Complex.exp (-(((-(x 0) - y 0)^2 / (4 * s)) : ℝ)) *
         Complex.exp (-(s : ℂ) * ‖k_sp‖^2) *
         Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y))) =
      (1 / (2 * π) ^ d : ℝ) *
        ∫ s in Set.Ioi 0, (Real.exp (-s * m^2) : ℂ) *
          ∫ k_sp : (SpatialCoords d), ∫ x : (SpaceTime d), ∫ y : (SpaceTime d),
            (starRingEnd ℂ (f x)) * f y *
            (Real.sqrt (π / s) : ℂ) * Complex.exp (-(((-(x 0) - y 0)^2 / (4 * s)) : ℝ)) *
            Complex.exp (-(s : ℂ) * ‖k_sp‖^2) *
            Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y)) := by
    -- Use smul version for set integrals
    rw [← smul_eq_mul, ← smul_eq_mul]
    rw [← integral_smul]
    apply MeasureTheory.setIntegral_congr_ae measurableSet_Ioi
    filter_upwards with s hs
    simp only [smul_eq_mul]
    ring

  -- Step 7: Push exp(-sm²) inside k_sp integral and combine exponentials
  have h_step6 : (1 / (2 * π) ^ d : ℝ) *
      ∫ s in Set.Ioi 0, (Real.exp (-s * m^2) : ℂ) *
        ∫ k_sp : (SpatialCoords d), ∫ x : (SpaceTime d), ∫ y : (SpaceTime d),
          (starRingEnd ℂ (f x)) * f y *
          (Real.sqrt (π / s) : ℂ) * Complex.exp (-(((-(x 0) - y 0)^2 / (4 * s)) : ℝ)) *
          Complex.exp (-(s : ℂ) * ‖k_sp‖^2) *
          Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y)) =
      (1 / (2 * π) ^ d : ℝ) *
        ∫ s in Set.Ioi 0, ∫ k_sp : (SpatialCoords d), ∫ x : (SpaceTime d), ∫ y : (SpaceTime d),
          (starRingEnd ℂ (f x)) * f y *
          (Real.sqrt (π / s) : ℂ) * Complex.exp (-(((-(x 0) - y 0)^2 / (4 * s)) : ℝ)) *
          Complex.exp (-(s : ℂ) * (‖k_sp‖^2 + m^2)) *
          Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y)) := by
    congr 1
    apply MeasureTheory.setIntegral_congr_ae measurableSet_Ioi
    filter_upwards with s hs
    -- First push exp(-sm²) into all the integrals
    have h_icm_sc : ∀ (c : ℂ) (g : (SpatialCoords d) → ℂ),
        c * ∫ a, g a = ∫ a, c * g a :=
      fun c g => (MeasureTheory.integral_const_mul (L := ℂ) c g).symm
    have h_icm_st : ∀ (c : ℂ) (g : (SpaceTime d) → ℂ),
        c * ∫ a, g a = ∫ a, c * g a :=
      fun c g => (MeasureTheory.integral_const_mul (L := ℂ) c g).symm
    rw [h_icm_sc]
    apply integral_congr_ae
    filter_upwards with k_sp
    rw [h_icm_st]
    apply integral_congr_ae
    filter_upwards with x
    rw [h_icm_st]
    apply integral_congr_ae
    filter_upwards with y
    -- Combine exp(-sm²) with exp(-s‖k_sp‖²) to get exp(-s(‖k_sp‖² + m²))
    -- First convert ↑(rexp ...) to cexp(↑...)
    rw [Complex.ofReal_exp]
    -- Now combine exponentials
    have h_exp_combine : Complex.exp (↑(-s * m^2)) * Complex.exp (-(s : ℂ) * ‖k_sp‖^2) =
        Complex.exp (-(s : ℂ) * (‖k_sp‖^2 + m^2)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    -- Now rearrange and apply
    calc Complex.exp (↑(-s * m^2)) *
           ((starRingEnd ℂ (f x)) * f y *
            (Real.sqrt (π / s) : ℂ) * Complex.exp (-(((-(x 0) - y 0)^2 / (4 * s)) : ℝ)) *
            Complex.exp (-(s : ℂ) * ‖k_sp‖^2) *
            Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y)))
        = (starRingEnd ℂ (f x)) * f y *
          (Real.sqrt (π / s) : ℂ) * Complex.exp (-(((-(x 0) - y 0)^2 / (4 * s)) : ℝ)) *
          (Complex.exp (↑(-s * m^2)) * Complex.exp (-(s : ℂ) * ‖k_sp‖^2)) *
          Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y)) := by ring
      _ = (starRingEnd ℂ (f x)) * f y *
          (Real.sqrt (π / s) : ℂ) * Complex.exp (-(((-(x 0) - y 0)^2 / (4 * s)) : ℝ)) *
          Complex.exp (-(s : ℂ) * (‖k_sp‖^2 + m^2)) *
          Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y)) := by
        rw [h_exp_combine]

  -- Chain all steps together
  calc ∫ s in Set.Ioi 0, (Real.exp (-s * m^2) : ℂ) *
         ∫ x : (SpaceTime d), ∫ y : (SpaceTime d),
           (starRingEnd ℂ (f x)) * f y * heatKernelProfile d s ‖timeReflection x - y‖
       = _ := h_step1
     _ = _ := h_step2
     _ = _ := h_step3
     _ = _ := h_step4
     _ = _ := h_step5
     _ = _ := h_step6

/-! ### Helper lemmas for Laplace s-integral evaluation -/

omit [Fact (2 ≤ d)] in
/-- ω = √(‖k_sp‖² + m²) is positive for m > 0. -/
lemma omega_pos (k_sp : (SpatialCoords d)) (m : ℝ) (hm : 0 < m) :
    0 < Real.sqrt (‖k_sp‖^2 + m^2) := by positivity

/-- The s-integral evaluation for fixed (k_sp, x, y):

    ∫_s √(π/s) exp(-t²/(4s)) exp(-s·ω²) ds = (π/ω) exp(-ω|t|)

    where t = -(x₀) - y₀ and ω = √(‖k_sp‖² + m²).

    This uses `laplace_integral_half_power_nonneg` from LaplaceIntegral.lean.

    **Proof outline:**
    1. Factor √(π/s) = √π · s^(-1/2)
    2. Combine exponentials: exp(-t²/(4s)) * exp(-s*ω²) = exp(-t²/(4s) - s*ω²)
    3. Apply laplace_integral_half_power_nonneg with a = t²/4, b = ω²
    4. Result: √π * √(π/ω²) * exp(-2√((t²/4)*ω²)) = (π/ω) * exp(-ω|t|) -/
lemma s_integral_eval (t : ℝ) (ω : ℝ) (hω : 0 < ω) :
    ∫ s in Set.Ioi 0, Real.sqrt (π / s) * Real.exp (-(t^2 / (4 * s))) *
      Real.exp (-s * ω^2) = (π / ω) * Real.exp (-ω * |t|) := by
  -- Setup hypotheses
  have ha : 0 ≤ t^2/4 := div_nonneg (sq_nonneg t) (by norm_num : (0:ℝ) ≤ 4)
  have hb : 0 < ω^2 := sq_pos_of_pos hω
  -- Step 1: Rewrite integrand to match laplace_integral_half_power_nonneg form
  -- √(π/s) * exp(-t²/(4s)) * exp(-sω²) = √π * s^(-1/2) * exp(-(t²/4)/s - ω²*s)
  have h_integrand : ∀ s ∈ Set.Ioi (0:ℝ),
      Real.sqrt (π / s) * Real.exp (-(t^2 / (4 * s))) * Real.exp (-s * ω^2) =
      Real.sqrt π * (s^(-(1/2 : ℝ)) * Real.exp (-(t^2/4)/s - ω^2*s)) := by
    intro s hs
    have hs' : 0 < s := hs
    -- sqrt(π/s) = sqrt(π) * s^(-1/2)
    have h_sqrt : Real.sqrt (π / s) = Real.sqrt π * s^(-(1/2 : ℝ)) := by
      rw [Real.sqrt_div Real.pi_pos.le, div_eq_mul_inv]
      congr 1
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hs'.le]
    rw [h_sqrt]
    -- Combine exponentials: exp(-t²/(4s)) * exp(-sω²) = exp(-(t²/(4s)) - sω²)
    have h_exp : Real.exp (-(t^2 / (4 * s))) * Real.exp (-s * ω^2) =
                 Real.exp (-(t^2/4)/s - ω^2*s) := by
      rw [← Real.exp_add]
      congr 1
      field_simp
      ring
    -- Combine using associativity and multiplication
    calc Real.sqrt π * s^(-(1/2 : ℝ)) * Real.exp (-(t^2 / (4 * s))) * Real.exp (-s * ω^2)
        = Real.sqrt π * s^(-(1/2 : ℝ)) * (Real.exp (-(t^2 / (4 * s))) * Real.exp (-s * ω^2)) := by ring
      _ = Real.sqrt π * s^(-(1/2 : ℝ)) * Real.exp (-(t^2/4)/s - ω^2*s) := by rw [h_exp]
      _ = Real.sqrt π * (s^(-(1/2 : ℝ)) * Real.exp (-(t^2/4)/s - ω^2*s)) := by ring
  -- Step 2: Rewrite integral using the integrand equivalence
  rw [setIntegral_congr_fun measurableSet_Ioi h_integrand]
  -- Step 3: Factor out √π from the integral
  rw [MeasureTheory.integral_const_mul]
  -- Step 4: Apply laplace_integral_half_power_nonneg
  have h_laplace := laplace_integral_half_power_nonneg (t^2/4) (ω^2) ha hb
  rw [h_laplace]
  -- Step 5: Algebraic simplification
  -- √π * (√(π/ω²) * exp(-2√((t²/4)*ω²))) = (π/ω) * exp(-ω|t|)
  -- First simplify sqrt(π/ω²) = sqrt(π)/ω
  have h_sqrt_div : Real.sqrt (π / ω^2) = Real.sqrt π / ω := by
    rw [Real.sqrt_div Real.pi_pos.le, Real.sqrt_sq_eq_abs, abs_of_pos hω]
  rw [h_sqrt_div]
  -- Now LHS = sqrt(π) * ((sqrt(π)/ω) * exp(-2*sqrt(t²ω²/4)))
  -- First use associativity: √π * (a * b) = (√π * a) * b
  have h_assoc : Real.sqrt π * (Real.sqrt π / ω * Real.exp (-2 * Real.sqrt (t^2 / 4 * ω^2))) =
      (Real.sqrt π * (Real.sqrt π / ω)) * Real.exp (-2 * Real.sqrt (t^2 / 4 * ω^2)) := by
    ring
  rw [h_assoc]
  have h_prod_sqrt : Real.sqrt π * (Real.sqrt π / ω) = π / ω := by
    field_simp
    exact Real.sq_sqrt Real.pi_pos.le
  rw [h_prod_sqrt]
  -- Now simplify the exponent: 2*sqrt((t²/4)*ω²) = ω*|t|
  congr 2
  have h1 : (0:ℝ) ≤ t^2/4 := ha
  rw [Real.sqrt_mul h1, Real.sqrt_sq_eq_abs, abs_of_pos hω]
  have h2 : Real.sqrt (t^2/4) = |t|/2 := by
    rw [Real.sqrt_div (sq_nonneg t), Real.sqrt_sq_eq_abs]
    congr 1
    rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
  rw [h2]
  ring

/-- **Complex version of s_integral_eval**: The Laplace integral identity in ℂ.

    This is a direct corollary of `s_integral_eval`, converting the real integral
    to complex form. The key observation is that all terms in the integrand are
    real numbers cast to ℂ, so we can use `integral_ofReal` to relate the integrals.

    ∫_s (↑√(π/s)) * cexp(-↑(t²/(4s))) * cexp(-↑(sω²)) ds = ↑((π/ω) * exp(-ω|t|))
-/
lemma s_integral_eval_complex (t : ℝ) (ω : ℝ) (hω : 0 < ω) :
    ∫ s in Set.Ioi 0, (Real.sqrt (π / s) : ℂ) *
      Complex.exp (-(t^2 / (4 * s) : ℝ)) *
      Complex.exp (-(s * ω^2 : ℝ)) =
    (((π / ω) * Real.exp (-ω * |t|) : ℝ) : ℂ) := by
  -- Step 1: Convert integrand to single real cast: ↑a * ↑b * ↑c = ↑(a * b * c)
  have h_integrand : ∀ s ∈ Set.Ioi (0:ℝ),
      (Real.sqrt (π / s) : ℂ) * Complex.exp (-(t^2 / (4 * s) : ℝ)) *
        Complex.exp (-(s * ω^2 : ℝ)) =
      (((Real.sqrt (π / s) * Real.exp (-(t^2 / (4 * s))) * Real.exp (-(s * ω^2))) : ℝ) : ℂ) := by
    intro s _
    -- cexp(-↑r) = ↑(Real.exp(-r)) by ofReal_neg and ofReal_exp
    have h1 : Complex.exp (-(t^2 / (4 * s) : ℝ)) = (Real.exp (-(t^2 / (4 * s))) : ℂ) := by
      rw [← Complex.ofReal_neg, Complex.ofReal_exp]
    have h2 : Complex.exp (-(s * ω^2 : ℝ)) = (Real.exp (-(s * ω^2)) : ℂ) := by
      rw [← Complex.ofReal_neg, Complex.ofReal_exp]
    rw [h1, h2]
    -- Now: ↑√(π/s) * ↑(exp(...)) * ↑(exp(...)) = ↑(√(π/s) * exp(...) * exp(...))
    -- Combine using ofReal_mul: ↑a * ↑b = ↑(a*b)
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
  rw [setIntegral_congr_fun measurableSet_Ioi h_integrand]
  -- Step 2: Normalize -(x * ω²) to -x * ω² to match s_integral_eval
  have h_form : ∀ x : ℝ, -(x * ω^2) = -x * ω^2 := by intro x; ring
  simp_rw [h_form]
  -- Step 3: Goal is ∫ x in S, ↑(f x) = ↑(result)
  -- Use integral_complex_ofReal: ∫ x in S, ↑(f x) = ↑(∫ x in S, f x)
  rw [integral_complex_ofReal]
  -- Now goal is: ↑(∫ x in S, f x) = ↑(result), which follows from s_integral_eval
  exact congrArg Complex.ofReal (s_integral_eval t ω hω)

/-- **Complex-valued s-integral**: For fixed (k_sp, x, y, f), the inner s-integral
    with complex exponentials evaluates to the propagator form.

    This wraps `s_integral_eval` by:
    1. Factoring out constant terms (f̄f and phase)
    2. Converting Complex.exp to Real.exp for real arguments
    3. Applying s_integral_eval
    4. Reassembling the complex result

    Note: The integrand has the form:
    f̄ * f * √(π/s) * cexp(-t²/(4s)) * cexp(-sω²) * cexp(-I*phase)

    where all exponentials have real arguments (cast to ℂ). -/
lemma s_integral_complex_eval (k_sp : (SpatialCoords d)) (x y : (SpaceTime d)) (m : ℝ) (hm : 0 < m)
    (f : (SchwartzTestFunctionℂ d)) :
    ∫ s in Set.Ioi 0, (starRingEnd ℂ (f x)) * f y *
      (Real.sqrt (π / s) : ℂ) * Complex.exp (-((-(x 0) - y 0)^2 / (4 * s) : ℝ)) *
      Complex.exp (-(s : ℂ) * (‖k_sp‖^2 + m^2)) *
      Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y)) =
    (starRingEnd ℂ (f x)) * f y * (π / Real.sqrt (‖k_sp‖^2 + m^2) : ℂ) *
      Complex.exp (-(|-(x 0) - y 0| : ℝ) * Real.sqrt (‖k_sp‖^2 + m^2)) *
      Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y)) := by
  -- The key insight: all s-dependent terms have real arguments
  -- We factor out constant terms, apply s_integral_eval, and reassemble
  let t := -(x 0) - y 0
  let ω := Real.sqrt (‖k_sp‖^2 + m^2)
  have hω : 0 < ω := omega_pos k_sp m hm
  -- Factor out terms not depending on s
  have h_factor : ∀ s ∈ Set.Ioi (0:ℝ),
      (starRingEnd ℂ (f x)) * f y *
        (Real.sqrt (π / s) : ℂ) * Complex.exp (-((-(x 0) - y 0)^2 / (4 * s) : ℝ)) *
        Complex.exp (-(s : ℂ) * (‖k_sp‖^2 + m^2)) *
        Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y)) =
      (starRingEnd ℂ (f x)) * f y *
        Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y)) *
        ((Real.sqrt (π / s) : ℂ) * Complex.exp (-((-(x 0) - y 0)^2 / (4 * s) : ℝ)) *
         Complex.exp (-(s : ℂ) * (‖k_sp‖^2 + m^2))) := by
    intro s _
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi h_factor]
  have h_icm_r : ∀ (c : ℂ) (g : ℝ → ℂ) (μ : MeasureTheory.Measure ℝ),
      ∫ a, c * g a ∂μ = c * ∫ a, g a ∂μ :=
    fun c g μ => MeasureTheory.integral_const_mul (L := ℂ) c g
  rw [h_icm_r]
  -- Goal: C * ∫ a, [√(π/a) * cexp(-t²/(4a)) * cexp(-↑a*(↑‖k_sp‖²+↑m²))] = C * (π/ω) * cexp(-ω|t|) * phase
  -- where C = f̄f * cexp(-I*...) and ω = √(‖k_sp‖² + m²)
  --
  -- Step 1: Convert cexp(-↑a * (↑‖k_sp‖² + ↑m²)) to cexp(-(a * ω²) : ℝ)
  -- using ω² = ‖k_sp‖² + m²
  have h_omega_sq : ω^2 = ‖k_sp‖^2 + m^2 := by
    simp only [ω]
    exact Real.sq_sqrt (by nlinarith [sq_nonneg ‖k_sp‖, sq_pos_of_pos hm])
  have h_exp_conv : ∀ a ∈ Set.Ioi (0:ℝ),
      Complex.exp (-(a : ℂ) * ((‖k_sp‖^2 : ℂ) + (m^2 : ℂ))) =
      Complex.exp (-(a * ω^2 : ℝ)) := by
    intro a _
    congr 1
    rw [h_omega_sq]
    push_cast
    ring
  have h_integrand_conv : ∀ a ∈ Set.Ioi (0:ℝ),
      (Real.sqrt (π / a) : ℂ) * Complex.exp (-((-(x 0) - y 0)^2 / (4 * a) : ℝ)) *
        Complex.exp (-(a : ℂ) * ((‖k_sp‖^2 : ℂ) + (m^2 : ℂ))) =
      (Real.sqrt (π / a) : ℂ) * Complex.exp (-(t^2 / (4 * a) : ℝ)) *
        Complex.exp (-(a * ω^2 : ℝ)) := by
    intro a ha
    rw [h_exp_conv a ha]
  rw [setIntegral_congr_fun measurableSet_Ioi h_integrand_conv]
  -- Step 2: Apply s_integral_eval_complex
  rw [s_integral_eval_complex t ω hω]
  -- Step 3: Algebraic simplification to match the goal
  -- After s_integral_eval_complex:
  -- LHS: C * ↑((π / ω) * Real.exp (-ω * |t|))
  -- RHS: f̄f * (↑π / ↑ω) * cexp(-↑|t| * ↑ω) * phase
  --
  -- We need to:
  -- 1. Split the single cast: ↑(a * b) = ↑a * ↑b
  -- 2. Convert Real.exp to Complex.exp: ↑(rexp r) = cexp ↑r
  -- 3. Rearrange using ring
  --
  -- First, split the cast:
  simp only [Complex.ofReal_mul, Complex.ofReal_div]
  -- Convert Real.exp to Complex.exp: ↑(rexp r) = cexp ↑r
  rw [Complex.ofReal_exp]
  -- Now we have: C * (↑π / ↑ω * cexp ↑(-ω * |t|)) = RHS
  -- Rearrange the exp argument: -ω * |t| = -|t| * ω
  have h_arg : ((-ω * |t| : ℝ) : ℂ) = ((-|t| * ω : ℝ) : ℂ) := by
    congr 1; ring
  rw [h_arg]
  -- Convert ↑(-|t| * ω) to -↑|t| * ↑ω
  rw [Complex.ofReal_mul, Complex.ofReal_neg]
  -- Unfold t and ω in the goal
  simp only [t, ω]
  -- Final algebraic rearrangement
  ring

/-- **THEOREM**: Laplace transform evaluation for the s-integral.

    The key identity (Bessel K_{1/2} / modified Laplace transform):

    √π · ∫₀^∞ s^{-1/2} exp(-t²/(4s) - sω²) ds = (π/ω) · exp(-ω|t|)

    where ω = √(|p̄|² + m²) is the relativistic dispersion relation.

    This transforms the Schwinger proper-time representation into the
    Euclidean propagator in mixed (p̄, x₀) representation:

    1/(2π)^d · ∫_p̄ ∫₀^∞ √(π/s) exp(-t²/(4s)) exp(-s(|p̄|² + m²)) exp(-ip̄·r̄) ds dp̄
    = 1/(2(2π)^{d−1}) · ∫_p̄ (1/ω) exp(-ω|t|) exp(-ip̄·r̄) dp̄

    **Normalization:** (1/(2π)^d) × π = 1/(2(2π)^{d−1}) ✓

    **Proof:** Uses `fubini_s_xy_swap` to move s inside, then
    `s_integral_eval` to evaluate the Laplace transform. -/
theorem laplace_s_integral_with_norm (m : ℝ) [Fact (0 < m)] (f : (SchwartzTestFunctionℂ d)) :
    (1 / (2 * π) ^ d : ℝ) *
    ∫ k_sp : (SpatialCoords d), ∫ s in Set.Ioi 0, ∫ x : (SpaceTime d), ∫ y : (SpaceTime d),
      (starRingEnd ℂ (f x)) * f y *
        (Real.sqrt (π / s) : ℂ) * Complex.exp (-((-(x 0) - y 0)^2 / (4 * s) : ℝ)) *
        Complex.exp (-(s : ℂ) * (‖k_sp‖^2 + m^2)) *
        Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y)) =
    (1 / (2 * (2 * π) ^ (d - 1)) : ℝ) *
      ∫ k_spatial : (SpatialCoords d), ∫ x : (SpaceTime d), ∫ y : (SpaceTime d),
        let ω := Real.sqrt (‖k_spatial‖^2 + m^2)
        (starRingEnd ℂ (f x)) * f y * (1 / ω : ℝ) *
          Complex.exp (-(|-(x 0) - y 0| : ℝ) * ω) *
          Complex.exp (-Complex.I * spatialDot k_spatial (spatialPart x - spatialPart y)) := by
  have hm : 0 < m := Fact.out
  -- Step 1: For each k_sp, swap s with (x, y) using fubini_s_xy_swap
  have h_fubini : ∀ k_sp : (SpatialCoords d),
      ∫ s in Set.Ioi 0, ∫ x : (SpaceTime d), ∫ y : (SpaceTime d),
        (starRingEnd ℂ (f x)) * f y *
          (Real.sqrt (π / s) : ℂ) * Complex.exp (-((-(x 0) - y 0)^2 / (4 * s) : ℝ)) *
          Complex.exp (-(s : ℂ) * (‖k_sp‖^2 + m^2)) *
          Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y)) =
      ∫ x : (SpaceTime d), ∫ y : (SpaceTime d), ∫ s in Set.Ioi 0,
        (starRingEnd ℂ (f x)) * f y *
          (Real.sqrt (π / s) : ℂ) * Complex.exp (-((-(x 0) - y 0)^2 / (4 * s) : ℝ)) *
          Complex.exp (-(s : ℂ) * (‖k_sp‖^2 + m^2)) *
          Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y)) :=
    fun k_sp => fubini_s_xy_swap m f k_sp
  -- Step 2: Rewrite using Fubini for each k_sp
  have h_lhs_fubini : ∫ k_sp : (SpatialCoords d), ∫ s in Set.Ioi 0, ∫ x : (SpaceTime d), ∫ y : (SpaceTime d),
      (starRingEnd ℂ (f x)) * f y *
        (Real.sqrt (π / s) : ℂ) * Complex.exp (-((-(x 0) - y 0)^2 / (4 * s) : ℝ)) *
        Complex.exp (-(s : ℂ) * (‖k_sp‖^2 + m^2)) *
        Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y)) =
      ∫ k_sp : (SpatialCoords d), ∫ x : (SpaceTime d), ∫ y : (SpaceTime d), ∫ s in Set.Ioi 0,
        (starRingEnd ℂ (f x)) * f y *
          (Real.sqrt (π / s) : ℂ) * Complex.exp (-((-(x 0) - y 0)^2 / (4 * s) : ℝ)) *
          Complex.exp (-(s : ℂ) * (‖k_sp‖^2 + m^2)) *
          Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y)) := by
    congr 1
    ext k_sp
    exact h_fubini k_sp
  rw [h_lhs_fubini]
  -- Step 3: For each (k_sp, x, y), the s-integral evaluates via the Laplace transform
  -- Apply s_integral_complex_eval to the inner s-integral
  have h_s_eval : ∀ k_sp : (SpatialCoords d), ∀ x y : (SpaceTime d),
      ∫ (s : ℝ) in Set.Ioi 0,
        (starRingEnd ℂ (f x)) * f y *
          (Real.sqrt (π / s) : ℂ) * Complex.exp (-((-(x 0) - y 0)^2 / (4 * s) : ℝ)) *
          Complex.exp (-(s : ℂ) * (‖k_sp‖^2 + m^2)) *
          Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y)) =
      (starRingEnd ℂ (f x)) * f y * (π / Real.sqrt (‖k_sp‖^2 + m^2) : ℂ) *
        Complex.exp (-(|-(x 0) - y 0| : ℝ) * Real.sqrt (‖k_sp‖^2 + m^2)) *
        Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y)) :=
    fun k_sp x y => s_integral_complex_eval k_sp x y m hm f
  -- Use the s-integral evaluation
  have h_inner_eval : ∫ (k_sp : (SpatialCoords d)) (x : (SpaceTime d)) (y : (SpaceTime d)),
      ∫ (s : ℝ) in Set.Ioi 0,
        (starRingEnd ℂ (f x)) * f y *
          (Real.sqrt (π / s) : ℂ) * Complex.exp (-((-(x 0) - y 0)^2 / (4 * s) : ℝ)) *
          Complex.exp (-(s : ℂ) * (‖k_sp‖^2 + m^2)) *
          Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y)) =
      ∫ (k_sp : (SpatialCoords d)) (x : (SpaceTime d)) (y : (SpaceTime d)),
        (starRingEnd ℂ (f x)) * f y * (π / Real.sqrt (‖k_sp‖^2 + m^2) : ℂ) *
          Complex.exp (-(|-(x 0) - y 0| : ℝ) * Real.sqrt (‖k_sp‖^2 + m^2)) *
          Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y)) := by
    congr 1
    ext k_sp
    congr 1
    ext x
    congr 1
    ext y
    exact h_s_eval k_sp x y
  rw [h_inner_eval]
  -- Step 4: Apply normalization constant identity
  -- LHS: (1/(2π)^d) * ∫ [... (π/ω) ...]
  -- RHS: (1/(2(2π)^3)) * ∫ [... (1/ω) ...]
  --
  -- Key identity: (1/(2π)^d) * π = 1/(2(2π)^{d−1})
  --
  -- The mathematical content is proven:
  -- - s_integral_eval: Laplace transform identity ✓
  -- - the normalization identity (1/(2π)^d) * π = 1/(2(2π)^{d−1}) ✓
  -- - fubini_s_xy_swap: Integral order swap
  --
  -- The remaining work is purely algebraic: pulling π from π/ω into the front
  -- constant and showing the result equals (1/(2(2π)^3)) * ∫[... (1/ω) ...].

  -- Step A: Pull π out of the integrand: (π/ω) = π * (1/ω)
  have h_integrand : ∀ k_sp : (SpatialCoords d), ∀ x y : (SpaceTime d),
      (starRingEnd ℂ (f x)) * f y * (π / Real.sqrt (‖k_sp‖^2 + m^2) : ℂ) *
        Complex.exp (-(|-(x 0) - y 0| : ℝ) * Real.sqrt (‖k_sp‖^2 + m^2)) *
        Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y)) =
      (π : ℂ) * ((starRingEnd ℂ (f x)) * f y * ((1 / Real.sqrt (‖k_sp‖^2 + m^2) : ℝ) : ℂ) *
        Complex.exp (-(|-(x 0) - y 0| : ℝ) * Real.sqrt (‖k_sp‖^2 + m^2)) *
        Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y))) := by
    intro k_sp x y
    have hω : ((Real.sqrt (‖k_sp‖^2 + m^2) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (omega_pos k_sp m hm).ne'
    push_cast
    field_simp

  -- Step B: Apply the integrand factorization across the triple integral
  have h_pull : (∫ (k_sp : (SpatialCoords d)) (x : (SpaceTime d)) (y : (SpaceTime d)),
      (starRingEnd ℂ (f x)) * f y * (π / Real.sqrt (‖k_sp‖^2 + m^2) : ℂ) *
        Complex.exp (-(|-(x 0) - y 0| : ℝ) * Real.sqrt (‖k_sp‖^2 + m^2)) *
        Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y)))
      = (π : ℂ) * ∫ (k_sp : (SpatialCoords d)) (x : (SpaceTime d)) (y : (SpaceTime d)),
        (starRingEnd ℂ (f x)) * f y * ((1 / Real.sqrt (‖k_sp‖^2 + m^2) : ℝ) : ℂ) *
          Complex.exp (-(|-(x 0) - y 0| : ℝ) * Real.sqrt (‖k_sp‖^2 + m^2)) *
          Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y)) := by
    simp_rw [h_integrand]
    simp only [← smul_eq_mul (π : ℂ)]
    simp_rw [MeasureTheory.integral_smul]

  rw [h_pull, ← mul_assoc]

  -- Step C: Front constant identity, uniform in d: (1/(2π)^d) · π = 1/(2·(2π)^(d-1))
  have h_const : ((1 / (2 * π) ^ d : ℝ) : ℂ) * (π : ℂ)
      = ((1 / (2 * (2 * π) ^ (d - 1)) : ℝ) : ℂ) := by
    have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
    have h2π : (2 * (π : ℂ)) ≠ 0 := by simp [hπ]
    have hd1 : d - 1 + 1 = d := by have h : 2 ≤ d := Fact.out; omega
    have hpow : (2 * (π : ℂ)) ^ d = (2 * (π : ℂ)) ^ (d - 1) * (2 * (π : ℂ)) := by
      conv_lhs => rw [← hd1]
      rw [pow_succ]
    push_cast
    rw [hpow]
    field_simp
  rw [h_const]

/-- **THEOREM**: The triple product (s, x, y) of the
    Schwinger-heat kernel bilinear form is integrable.

    This allows applying Fubini to swap ∫_s with ∫_x ∫_y.

    **Proof:**
    Uses `Integrable.mono'` with the bound from `schwinger_bound_integrable`.
    The pointwise bound |integrand| ≤ bound is verified for s > 0,
    and the set s ≤ 0 has measure zero under the restricted measure. -/
theorem schwinger_bilinear_integrable (m : ℝ) [Fact (0 < m)] (f : (SchwartzTestFunctionℂ d)) :
    Integrable (fun (p : ℝ × (SpaceTime d) × (SpaceTime d)) =>
      (starRingEnd ℂ (f p.2.1)) * f p.2.2 *
      Real.exp (-p.1 * m^2) * heatKernelProfile d p.1 ‖timeReflection p.2.1 - p.2.2‖)
      ((volume.restrict (Set.Ioi 0)).prod (volume.prod volume)) := by
  -- Get the mass positivity
  have hm : 0 < m := Fact.out
  -- Get boundedness of f: Schwartz functions are bounded
  have hf_bdd : ∃ Cf, ∀ x, ‖f x‖ ≤ Cf := by
    use ‖f.toBoundedContinuousFunction‖
    intro x
    exact BoundedContinuousFunction.norm_coe_le_norm f.toBoundedContinuousFunction x
  obtain ⟨Cf, hCf⟩ := hf_bdd
  -- Get integrability of f (Schwartz functions are L¹)
  have hf_int : Integrable (fun x => ‖f x‖) (volume : Measure (SpaceTime d)) := f.integrable.norm
  have hf_L1 : Integrable f (volume : Measure (SpaceTime d)) := f.integrable

  -- Key insight: the bound separates into factors
  -- |integrand| ≤ ‖f(x)‖ * ‖f(y)‖ * exp(-sm²) * H(s, ‖Θx-y‖)
  --            ≤ ‖f(x)‖ * Cf * exp(-sm²) * H(s, ‖Θx-y‖)
  --
  -- The total integral of this bound is finite because:
  -- 1. For each s > 0: ∫_x ∫_y ‖f(x)‖ * Cf * H(s, ‖Θx-y‖) dy dx
  --    = Cf * ∫_x ‖f(x)‖ * [∫_y H(s, ‖Θx-y‖) dy] dx
  --    = Cf * ∫_x ‖f(x)‖ * 1 dx  (by heatKernelProfile_integral_eq_one)
  --    = Cf * ‖f‖_{L¹}
  --
  -- 2. The s-integral: ∫_{s>0} exp(-sm²) * Cf * ‖f‖_{L¹} ds
  --    = Cf * ‖f‖_{L¹} * (1/m²) < ∞
  --
  -- Full formalization requires:
  -- - Showing the bound is integrable on the triple product
  -- - AEStronglyMeasurable of the integrand
  -- - Pointwise norm bound
  -- Then apply Integrable.mono'

  -- The heat kernel L¹ normalization is the key:
  have h_heat_L1 : ∀ s > 0, ∫ z : (SpaceTime d), heatKernelProfile d s ‖z‖ = 1 :=
    fun s hs => heatKernelProfile_integral_eq_one d s hs

  -- The s-integral of exp(-sm²) converges
  have h_exp_int : ∫ s in Set.Ioi 0, Real.exp (-s * m^2) = 1 / m^2 := by
    have := integral_exp_neg_mul_Ioi_eq_inv (m^2) (sq_pos_of_pos hm)
    simp only [one_div] at this ⊢
    convert this using 2
    ext s
    ring_nf

  -- Define the integrand
  let F : ℝ × (SpaceTime d) × (SpaceTime d) → ℂ := fun p =>
    (starRingEnd ℂ (f p.2.1)) * f p.2.2 *
    Real.exp (-p.1 * m^2) * heatKernelProfile d p.1 ‖timeReflection p.2.1 - p.2.2‖

  -- Define the real-valued dominating function
  let bound : ℝ × (SpaceTime d) × (SpaceTime d) → ℝ := fun p =>
    ‖f p.2.1‖ * Cf * Real.exp (-p.1 * m^2) * heatKernelProfile d p.1 ‖timeReflection p.2.1 - p.2.2‖

  -- The measure
  let μ : Measure (ℝ × (SpaceTime d) × (SpaceTime d)) :=
    (volume.restrict (Set.Ioi 0)).prod ((volume : Measure (SpaceTime d)).prod volume)

  -- Pointwise bound: ‖F p‖ ≤ bound p for s > 0
  have h_bound : ∀ p : ℝ × (SpaceTime d) × (SpaceTime d), p.1 ∈ Set.Ioi 0 →
      ‖F p‖ ≤ bound p := by
    intro p hp
    simp only [F, bound, Set.mem_Ioi] at hp ⊢
    rw [norm_mul, norm_mul, norm_mul]
    -- ‖conj(f x)‖ = ‖f x‖
    have h1 : ‖(starRingEnd ℂ) (f p.2.1)‖ = ‖f p.2.1‖ := RCLike.norm_conj _
    rw [h1]
    -- ‖exp(-sm²)‖ = exp(-sm²) since exp is positive
    have h2 : ‖(Real.exp (-p.1 * m^2) : ℂ)‖ = Real.exp (-p.1 * m^2) := by
      simp only [Complex.norm_real]
      exact abs_of_pos (Real.exp_pos _)
    rw [h2]
    -- ‖H(s,r)‖ = H(s,r) since H is non-negative for s > 0
    have h3 : ‖(heatKernelProfile d p.1 ‖timeReflection p.2.1 - p.2.2‖ : ℂ)‖ =
        heatKernelProfile d p.1 ‖timeReflection p.2.1 - p.2.2‖ := by
      simp only [Complex.norm_real]
      exact abs_of_nonneg (heatKernelProfile_nonneg d p.1 _ hp)
    rw [h3]
    -- Now: ‖f x‖ * ‖f y‖ * exp * H ≤ ‖f x‖ * Cf * exp * H
    have h4 : ‖f p.2.2‖ ≤ Cf := hCf p.2.2
    have h_exp_pos : 0 ≤ Real.exp (-p.1 * m^2) := le_of_lt (Real.exp_pos _)
    have h_H_nonneg : 0 ≤ heatKernelProfile d p.1 ‖timeReflection p.2.1 - p.2.2‖ :=
      heatKernelProfile_nonneg d p.1 _ hp
    -- Rearrange: (a * b) * c * d ≤ (a * Cf) * c * d when b ≤ Cf
    have h_rearrange : ‖f p.2.1‖ * ‖f p.2.2‖ ≤ ‖f p.2.1‖ * Cf :=
      mul_le_mul_of_nonneg_left h4 (norm_nonneg _)
    have h_mid : ‖f p.2.1‖ * ‖f p.2.2‖ * Real.exp (-p.1 * m^2) ≤
                 ‖f p.2.1‖ * Cf * Real.exp (-p.1 * m^2) :=
      mul_le_mul_of_nonneg_right h_rearrange h_exp_pos
    exact mul_le_mul_of_nonneg_right h_mid h_H_nonneg

  -- Cf is non-negative: 0 ≤ ‖f 0‖ ≤ Cf
  have hCf_nonneg : 0 ≤ Cf := le_trans (norm_nonneg (f 0)) (hCf 0)

  -- The bound is non-negative
  have h_bound_nonneg : ∀ p : ℝ × (SpaceTime d) × (SpaceTime d), p.1 ∈ Set.Ioi 0 → 0 ≤ bound p := by
    intro p hp
    simp only [bound, Set.mem_Ioi] at hp ⊢
    apply mul_nonneg
    apply mul_nonneg
    apply mul_nonneg (norm_nonneg _) hCf_nonneg
    exact le_of_lt (Real.exp_pos _)
    exact heatKernelProfile_nonneg d p.1 _ hp

  -- The bound is integrable: ∫∫∫ bound = Cf * ‖f‖_{L¹} / m²
  -- This follows from Tonelli's theorem applied in the order y, x, s
  have h_bound_integrable : Integrable bound μ := by
    -- Strategy: Use integrable_prod_iff to reduce to iterated integrals.
    -- The bound factors as:
    --   bound(s, x, y) = [‖f x‖ * Cf * exp(-sm²)] * H(s, ‖Θx - y‖)
    --
    -- Step 1: For each s > 0, ∫_y H(s, ‖Θx - y‖) dy = 1 (by h_heat_L1 and translation)
    -- Step 2: Thus ∫∫ bound(s, x, y) dy dx = Cf * exp(-sm²) * ∫_x ‖f x‖ dx = Cf * exp(-sm²) * ‖f‖_{L¹}
    -- Step 3: ∫_s Cf * exp(-sm²) * ‖f‖_{L¹} ds = Cf * ‖f‖_{L¹} / m² < ∞
    --
    -- The formal proof requires showing:
    -- (a) AEStronglyMeasurable bound μ
    -- (b) For a.e. s: (x, y) ↦ bound(s, x, y) is integrable on (SpaceTime d) × (SpaceTime d)
    -- (c) s ↦ ∫∫ |bound(s, x, y)| dy dx is integrable on Ioi 0
    --
    -- For (a): bound involves continuous functions (norm, exp, heatKernel)
    -- For (b): Use heat kernel normalization + Schwartz integrability
    -- For (c): Use exp(-sm²) integrability
    --
    -- Since bound ≥ 0, we have |bound| = bound.
    --
    -- Key lemma chain:
    -- ∫∫∫ bound ≤ Cf * (∫_x ‖f x‖) * (∫_s exp(-sm²)) * sup_s(∫_y H(s,‖·‖))
    --           = Cf * ‖f‖_{L¹} * (1/m²) * 1 < ∞
    --
    -- Use schwinger_bound_integrable
    exact schwinger_bound_integrable m f Cf hCf

  -- AEStronglyMeasurable of F
  have h_meas : AEStronglyMeasurable F μ := by
    -- F involves products of continuous functions
    -- F p = conj(f p.2.1) * f p.2.2 * exp(-p.1 * m²) * H(p.1, ‖Θ p.2.1 - p.2.2‖)
    apply AEStronglyMeasurable.mul
    · apply AEStronglyMeasurable.mul
      · apply AEStronglyMeasurable.mul
        · -- conj(f p.2.1) is measurable
          apply Continuous.aestronglyMeasurable
          exact continuous_star.comp (f.continuous.comp continuous_snd.fst)
        · -- f p.2.2 is measurable
          apply Continuous.aestronglyMeasurable
          exact f.continuous.comp continuous_snd.snd
      · -- exp(-p.1 * m²) : ℂ is measurable
        apply Continuous.aestronglyMeasurable
        exact continuous_ofReal.comp (Real.continuous_exp.comp
          ((continuous_fst.neg).mul continuous_const))
    · -- H(p.1, ‖Θ p.2.1 - p.2.2‖) : ℂ is AEStronglyMeasurable
      -- Use heatKernelPositionSpace_aestronglyMeasurable
      exact heatKernelPositionSpace_aestronglyMeasurable

  -- Apply Integrable.mono'
  apply Integrable.mono' h_bound_integrable h_meas
  -- Show ‖F p‖ ≤ bound p a.e. under the restricted measure
  -- Since μ = (volume.restrict (Set.Ioi 0)).prod (volume.prod volume),
  -- we only need to verify the bound for s > 0 (μ-a.e.)
  -- The set {p | p.1 ∉ Ioi 0} has μ-measure zero since the first marginal is restricted to Ioi 0
  rw [ae_iff]
  -- First show that {p | p.1 ≤ 0} has μ-measure zero
  have h_null : μ {p : ℝ × (SpaceTime d) × (SpaceTime d) | p.1 ≤ 0} = 0 := by
    have h_preimage : {p : ℝ × (SpaceTime d) × (SpaceTime d) | p.1 ≤ 0} = Set.Iic 0 ×ˢ Set.univ := by
      ext p; simp only [Set.mem_setOf_eq, Set.mem_prod, Set.mem_Iic, Set.mem_univ, and_true]
    rw [h_preimage, Measure.prod_prod]
    rw [Measure.restrict_apply measurableSet_Iic]
    simp only [Set.Iic_inter_Ioi, Set.Ioc_self, measure_empty, zero_mul]
  -- The set where the bound fails is contained in {p | p.1 ≤ 0}
  apply measure_mono_null _ h_null
  intro p hp
  simp only [Set.mem_setOf_eq, not_le] at hp
  simp only [Set.mem_setOf_eq]
  by_contra h_pos
  push Not at h_pos
  have hpIoi : p.1 ∈ Set.Ioi 0 := h_pos
  exact not_lt.mpr (h_bound p hpIoi) hp

/-- The permutation map (x, (y, s)) ↦ (s, (x, y)) as a measurable equivalence.
    Constructed by composing prodAssoc.symm (reassociating) with prodComm (swapping). -/
private def schwinger_tripleReorder :
    (SpaceTime d) × ((SpaceTime d) × ℝ) ≃ᵐ ℝ × ((SpaceTime d) × (SpaceTime d)) :=
  MeasurableEquiv.prodAssoc.symm.trans MeasurableEquiv.prodComm

omit [Fact (2 ≤ d)] in
/-- The schwinger_tripleReorder map is measure-preserving on product Lebesgue measures
    with the s-measure restricted to Ioi 0. -/
private lemma measurePreserving_schwinger_tripleReorder :
    MeasurePreserving schwinger_tripleReorder
      ((volume : Measure (SpaceTime d)).prod (volume.prod (volume.restrict (Set.Ioi 0))))
      ((volume.restrict (Set.Ioi 0)).prod (volume.prod volume)) := by
  unfold schwinger_tripleReorder
  -- Step 1: prodAssoc.symm preserves measure from μ.prod(μ.prod ν) to (μ.prod μ).prod ν
  have h1 : MeasurePreserving
      (MeasurableEquiv.prodAssoc (α := (SpaceTime d)) (β := (SpaceTime d)) (γ := ℝ)).symm
      ((volume : Measure (SpaceTime d)).prod (volume.prod (volume.restrict (Set.Ioi 0))))
      ((volume.prod volume).prod (volume.restrict (Set.Ioi 0))) :=
    (measurePreserving_prodAssoc volume volume (volume.restrict (Set.Ioi 0))).symm
      MeasurableEquiv.prodAssoc
  -- Step 2: prodComm preserves measure from (μ.prod μ).prod ν to ν.prod(μ.prod μ)
  have h2 : MeasurePreserving
      (MeasurableEquiv.prodComm (α := (SpaceTime d) × (SpaceTime d)) (β := ℝ))
      (((volume : Measure (SpaceTime d)).prod volume).prod (volume.restrict (Set.Ioi 0)))
      ((volume.restrict (Set.Ioi 0)).prod (volume.prod volume)) :=
    MeasureTheory.Measure.measurePreserving_swap
  exact h2.comp h1

/-- **Fubini swap for the Schwinger integrand.**

    Given integrability of the Schwinger integrand on the product space,
    the iterated integrals can be computed in either order:
    ∫_x ∫_y ∫_s F = ∫_s ∫_x ∫_y F

    **Proof:**
    Both sides equal ∫∫∫ F over (Ioi 0) × (SpaceTime d) × (SpaceTime d) by Fubini-Tonelli.
    The proof uses `integral_prod` to convert iterated integrals to product integrals,
    and the measure-preserving map `schwinger_tripleReorder` to connect them. -/
theorem schwinger_fubini_core (m : ℝ) [Fact (0 < m)] (f : (SchwartzTestFunctionℂ d)) :
    ∫ x : (SpaceTime d), ∫ y : (SpaceTime d), ∫ s in Set.Ioi 0,
      (starRingEnd ℂ (f x)) * f y *
        (Real.exp (-s * m^2) : ℂ) * heatKernelProfile d s ‖timeReflection x - y‖ =
    ∫ s in Set.Ioi 0, ∫ x : (SpaceTime d), ∫ y : (SpaceTime d),
      (starRingEnd ℂ (f x)) * f y *
        (Real.exp (-s * m^2) : ℂ) * heatKernelProfile d s ‖timeReflection x - y‖ := by
  -- Define the integrand function
  let F : (SpaceTime d) → (SpaceTime d) → ℝ → ℂ := fun x y s =>
    (starRingEnd ℂ (f x)) * f y *
      (Real.exp (-s * m^2) : ℂ) * heatKernelProfile d s ‖timeReflection x - y‖

  -- Define product functions for LHS and RHS orderings
  let fL : (SpaceTime d) × ((SpaceTime d) × ℝ) → ℂ := fun p => F p.1 p.2.1 p.2.2
  let fR : ℝ × ((SpaceTime d) × (SpaceTime d)) → ℂ := fun q => F q.2.1 q.2.2 q.1

  -- Get integrability on (s, (x, y)) from schwinger_bilinear_integrable
  have h_int_sxy := schwinger_bilinear_integrable m f

  -- Show h_int_sxy equals Integrable fR on the (s, x, y) measure
  have h_int_fR : Integrable fR ((volume.restrict (Set.Ioi 0)).prod (volume.prod volume)) := by
    convert h_int_sxy using 1

  -- Transfer to (x, (y, s)) via measure-preserving map
  have h_int_xys : Integrable fL
      ((volume : Measure (SpaceTime d)).prod (volume.prod (volume.restrict (Set.Ioi 0)))) := by
    have hcomp : fL = fR ∘ schwinger_tripleReorder := rfl
    rw [hcomp]
    exact (measurePreserving_schwinger_tripleReorder.integrable_comp_emb
        schwinger_tripleReorder.measurableEmbedding).mpr h_int_fR

  -- LHS = ∫ fL on product space (via Fubini twice)
  have hLHS : ∫ x, ∫ y, ∫ s in Set.Ioi 0, F x y s ∂volume ∂volume ∂volume =
      ∫ p, fL p ∂((volume : Measure (SpaceTime d)).prod (volume.prod (volume.restrict (Set.Ioi 0)))) := by
    -- Convert inner ∫y ∫s → ∫(y,s) using Fubini
    have inner_fubini : ∀ᵐ x ∂(volume : Measure (SpaceTime d)),
        ∫ y, ∫ s in Set.Ioi 0, F x y s ∂volume =
        ∫ ys, F x ys.1 ys.2 ∂(volume.prod (volume.restrict (Set.Ioi 0))) := by
      filter_upwards [h_int_xys.prod_right_ae] with x hx
      exact (integral_prod (fun ys => F x ys.1 ys.2) hx).symm
    rw [integral_congr_ae inner_fubini]
    exact (integral_prod fL h_int_xys).symm

  -- RHS = ∫ fR on product space (via Fubini twice)
  have hRHS : ∫ s in Set.Ioi 0, ∫ x, ∫ y, F x y s ∂volume ∂volume =
      ∫ q, fR q ∂((volume.restrict (Set.Ioi 0)).prod (volume.prod volume)) := by
    -- Convert inner ∫x ∫y → ∫(x,y) using Fubini
    have inner_fubini : ∀ᵐ s ∂(volume.restrict (Set.Ioi 0) : Measure ℝ),
        ∫ x, ∫ y, F x y s ∂volume ∂volume =
        ∫ xy, F xy.1 xy.2 s ∂(volume.prod volume) := by
      filter_upwards [h_int_sxy.prod_right_ae] with s hs
      exact (integral_prod (fun xy => F xy.1 xy.2 s) hs).symm
    rw [integral_congr_ae inner_fubini]
    exact (integral_prod fR h_int_sxy).symm

  -- Key identity: fL = fR ∘ schwinger_tripleReorder
  have hfL_eq : ∀ p, fL p = fR (schwinger_tripleReorder p) := fun _ => rfl

  -- Connect via measure-preserving transformation
  calc ∫ x, ∫ y, ∫ s in Set.Ioi 0, F x y s ∂volume ∂volume ∂volume
      = ∫ p, fL p ∂((volume : Measure (SpaceTime d)).prod (volume.prod (volume.restrict (Set.Ioi 0)))) := hLHS
    _ = ∫ p, fR (schwinger_tripleReorder p)
          ∂((volume : Measure (SpaceTime d)).prod (volume.prod (volume.restrict (Set.Ioi 0)))) := rfl
    _ = ∫ q, fR q ∂((volume.restrict (Set.Ioi 0)).prod (volume.prod volume)) :=
        measurePreserving_schwinger_tripleReorder.integral_comp
          schwinger_tripleReorder.measurableEmbedding fR
    _ = ∫ s in Set.Ioi 0, ∫ x, ∫ y, F x y s ∂volume ∂volume := hRHS.symm

/-- **Triple integral order swap.**

    Given integrability (from `schwinger_bilinear_integrable`), Fubini's theorem ensures:
    ∫ x ∫ y, F(x,y) * [∫ s, G(s,x,y)] = ∫ s, [∫ x ∫ y, F(x,y) * G(s,x,y)]

    **Proof sketch:**
    This follows from Mathlib's `MeasureTheory.integral_integral_swap` (Fubini-Tonelli)
    applied to the integrable function from `schwinger_bilinear_integrable`.
    The key steps:
    1. Rewrite both sides as integrals over ℝ × (SpaceTime d) × (SpaceTime d)
    2. Apply Fubini to swap the order of integration
    3. Use the integrability hypothesis to justify the swap -/
theorem schwinger_fubini_swap (m : ℝ) [Fact (0 < m)] (f : (SchwartzTestFunctionℂ d)) :
    ∫ x : (SpaceTime d), ∫ y : (SpaceTime d),
      (starRingEnd ℂ (f x)) * f y *
        (∫ s in Set.Ioi 0, (Real.exp (-s * m^2) : ℂ) *
          heatKernelProfile d s ‖timeReflection x - y‖) =
    ∫ s in Set.Ioi 0, (Real.exp (-s * m^2) : ℂ) *
      ∫ x : (SpaceTime d), ∫ y : (SpaceTime d),
        (starRingEnd ℂ (f x)) * f y * heatKernelProfile d s ‖timeReflection x - y‖ := by
  -- This follows from Fubini's theorem applied to the integrable function
  -- from schwinger_bilinear_integrable.
  --
  -- The proof uses:
  -- 1. Pull f̄(x) * f(y) into the s-integral (independent of s)
  -- 2. Fubini: swap ∫ x ∫ y ∫ s → ∫ s ∫ x ∫ y
  -- 3. Factor exp(-sm²) out of spatial integrals (independent of x, y)
  --
  -- The key technical ingredient is schwinger_bilinear_integrable which ensures
  -- integrability on the triple product space, justifying the Fubini swap.
  have h_int := schwinger_bilinear_integrable m f

  -- Step 1: Rewrite LHS by pulling f̄ f into the s-integral
  have h_pull_in : ∀ x y : (SpaceTime d),
      (starRingEnd ℂ (f x)) * f y *
        (∫ s in Set.Ioi 0, (Real.exp (-s * m^2) : ℂ) *
          heatKernelProfile d s ‖timeReflection x - y‖) =
      ∫ s in Set.Ioi 0, (starRingEnd ℂ (f x)) * f y *
        (Real.exp (-s * m^2) : ℂ) * heatKernelProfile d s ‖timeReflection x - y‖ := by
    intro x y
    have h_icm : ∀ (c : ℂ) (g : ℝ → ℂ) (μ : MeasureTheory.Measure ℝ),
        c * ∫ a, g a ∂μ = ∫ a, c * g a ∂μ :=
      fun c g μ => (MeasureTheory.integral_const_mul (L := ℂ) c g).symm
    rw [h_icm]
    congr 1
    ext s
    ring
  simp_rw [h_pull_in]

  -- Step 2: Rewrite RHS by factoring exp(-sm²) out of spatial integrals
  have h_factor_out : ∀ s : ℝ,
      (Real.exp (-s * m^2) : ℂ) *
        ∫ x : (SpaceTime d), ∫ y : (SpaceTime d),
          (starRingEnd ℂ (f x)) * f y * heatKernelProfile d s ‖timeReflection x - y‖ =
      ∫ x : (SpaceTime d), ∫ y : (SpaceTime d),
        (starRingEnd ℂ (f x)) * f y *
          (Real.exp (-s * m^2) : ℂ) * heatKernelProfile d s ‖timeReflection x - y‖ := by
    intro s
    have h_icm : ∀ (c : ℂ) (g : (SpaceTime d) → ℂ),
        c * ∫ a, g a = ∫ a, c * g a :=
      fun c g => (MeasureTheory.integral_const_mul (L := ℂ) c g).symm
    rw [h_icm]
    congr 1
    ext x
    rw [h_icm]
    congr 1
    ext y
    ring
  simp_rw [h_factor_out]

  -- Step 3: Apply Fubini to swap ∫_x ∫_y ∫_s with ∫_s ∫_x ∫_y
  --
  -- After steps 1 and 2, both sides have the integrand:
  -- F(s,x,y) = f̄(x) * f(y) * exp(-sm²) * H(s, ‖Θx-y‖)
  --
  -- LHS = ∫_x ∫_y [∫_s F(s,x,y) ds] dy dx
  -- RHS = ∫_s [∫_x ∫_y F(s,x,y) dy dx] ds
  --
  -- By Fubini-Tonelli, given F is integrable on the product space (h_int),
  -- both equal the triple integral ∫∫∫ F over (Ioi 0) × (SpaceTime d) × (SpaceTime d).
  --
  -- The formal proof requires showing:
  -- (a) ∫_x ∫_y ∫_s F = ∫_{(x,y)} ∫_s F = ∫_{(s,x,y)} F  (by integral_integral twice)
  -- (b) ∫_s ∫_x ∫_y F = ∫_s ∫_{(x,y)} F = ∫_{(s,x,y)} F  (by integral_integral twice)
  -- Hence (a) = (b).

  exact schwinger_fubini_core m f

/-- The kernel-level Schwinger representation holds for Θx ≠ y.
    This is the propagator-class bridge `GFFPropagator.schwinger_eq`: away from coincident
    points the radial profile equals the proper-time (heat kernel) integral. -/
lemma freeCovariance_eq_schwingerRep (m : ℝ) [Fact (0 < m)] [GFFPropagator d m]
    (x y : (SpaceTime d)) (hxy : timeReflection x ≠ y) :
    (freeCovariance d m (timeReflection x) y : ℂ) =
    ∫ s in Set.Ioi 0, (Real.exp (-s * m^2) : ℂ) *
      heatKernelProfile d s ‖timeReflection x - y‖ := by
  have hr : 0 < ‖timeReflection x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have h' : freeCovariance d m (timeReflection x) y =
      ∫ t in Set.Ioi 0, Real.exp (-t * m^2) * heatKernelProfile d t ‖timeReflection x - y‖ := by
    have h := GFFPropagator.schwinger_eq (d := d) (m := m) ‖timeReflection x - y‖ hr
    simp only [freeCovariance]
    rw [h]
    rfl
  -- Cast to complex
  rw [h']
  -- Convert real integral to complex integral
  -- Goal: ↑(∫ t in Ioi 0, f t) = ∫ s in Ioi 0, ↑(f s)
  -- Use integral_complex_ofReal (reversed)
  rw [← integral_complex_ofReal]
  congr 1
  ext s
  push_cast
  ring

/-- **Bessel bilinear form equals the Schwinger heat kernel form.**

    This follows from:
    1. **Kernel equality** (a.e.): For Θx ≠ y (which is a.e. in the product measure),
       freeCovariance d (Θx) y = properTimeCovariance d m |Θx - y| = ∫₀^∞ e^{-sm²} H(s, |Θx-y|) ds
       This is proven via `GFFPropagator.schwinger_eq`.

    2. **Fubini swap**: Exchanging the s-integral with the x,y-integrals.
       Uses `schwinger_bilinear_integrable`.

    **Mathematical statement:**
    ∫∫ conj(f(x)) C(Θx,y) f(y) dx dy = ∫₀^∞ e^{-sm²} [∫∫ conj(f) f H(s,|Θx-y|) dx dy] ds
-/
theorem bilinear_schwinger_eq_heatKernel (m : ℝ) [Fact (0 < m)] [GFFPropagator d m] (f : (SchwartzTestFunctionℂ d)) :
    ∫ x : (SpaceTime d), ∫ y : (SpaceTime d),
      (starRingEnd ℂ (f x)) * (freeCovariance d m (timeReflection x) y : ℂ) * f y =
    ∫ s in Set.Ioi 0, (Real.exp (-s * m^2) : ℂ) *
      ∫ x : (SpaceTime d), ∫ y : (SpaceTime d),
        (starRingEnd ℂ (f x)) * f y * heatKernelProfile d s ‖timeReflection x - y‖ := by
  -- The proof uses:
  -- 1. freeCovariance_eq_schwingerRep: kernel equality for Θx ≠ y
  -- 2. The diagonal {Θx = y} has measure zero
  -- 3. schwinger_bilinear_integrable: allows Fubini swap

  have hm : 0 < m := Fact.out
  have h_int := schwinger_bilinear_integrable m f

  -- Step 1: Rewrite LHS by substituting kernel equality for each (x,y)
  -- For Θx ≠ y: freeCovariance d m (Θx) y = ∫ s, exp(-sm²) H(s, ‖Θx-y‖)
  -- The set {(x,y) : Θx = y} has measure zero in (SpaceTime d) × (SpaceTime d)

  -- The integrand transformation:
  -- conj(f x) * C(Θx,y) * f y = conj(f x) * f y * ∫ s, exp(-sm²) H(s, ‖Θx-y‖)
  --                           = ∫ s, conj(f x) * f y * exp(-sm²) H(s, ‖Θx-y‖)

  -- Step 2: Apply Fubini to swap the integration order
  -- ∫ x ∫ y [∫ s, F(s,x,y)] = ∫ s [∫ x ∫ y, F(s,x,y)]
  -- This is justified by h_int (integrability on product space)

  -- The proof requires showing:
  -- (a) The a.e. equality holds (diagonal has measure zero)
  -- (b) Fubini applies (we have integrability)
  -- (c) The constant exp(-sm²) can be factored out

  -- Key insight: Both sides equal the same triple integral, just computed in different orders.
  -- Define the integrand F(s,x,y) = conj(f x) * f y * exp(-sm²) * H(s, ‖Θx-y‖)
  --
  -- LHS computes: ∫ x ∫ y, [∫ s, F(s,x,y)]  (s innermost)
  -- RHS computes: ∫ s, [∫ x ∫ y, F(s,x,y)]  (s outermost)
  --
  -- By Fubini (using h_int), these are equal.

  -- Step 1: Rewrite LHS using kernel equality
  -- For each (x,y) with Θx ≠ y, substitute the Schwinger representation
  have h_kernel_eq : ∀ x y, timeReflection x ≠ y →
      (starRingEnd ℂ (f x)) * (freeCovariance d m (timeReflection x) y : ℂ) * f y =
      (starRingEnd ℂ (f x)) * f y *
        (∫ s in Set.Ioi 0, (Real.exp (-s * m^2) : ℂ) *
          heatKernelProfile d s ‖timeReflection x - y‖) := by
    intro x y hxy
    rw [freeCovariance_eq_schwingerRep m x y hxy]
    ring

  -- The diagonal {(x,y) : Θx = y} is a proper affine subspace of codimension 4,
  -- hence has measure zero in the product measure.

  -- Step 2: Show h_kernel_eq holds almost everywhere
  -- The set where Θx = y is a proper affine subspace, hence has measure zero
  -- For each x, {y : Θx = y} is a singleton, which has measure zero (NoAtoms).
  have h_ae : ∀ᵐ x ∂(volume : Measure (SpaceTime d)), ∀ᵐ y ∂volume,
      (starRingEnd ℂ (f x)) * (freeCovariance d m (timeReflection x) y : ℂ) * f y =
      (starRingEnd ℂ (f x)) * f y *
        (∫ s in Set.Ioi 0, (Real.exp (-s * m^2) : ℂ) *
          heatKernelProfile d s ‖timeReflection x - y‖) := by
    filter_upwards with x
    -- The set {y : Θx = y} = {Θx} is a singleton with measure zero
    have h_singleton : (volume : Measure (SpaceTime d)) {timeReflection x} = 0 :=
      MeasureTheory.measure_singleton (timeReflection x)
    -- Show: ∀ᵐ y, y ≠ Θx
    have h_compl : ∀ᵐ y ∂(volume : Measure (SpaceTime d)), y ≠ timeReflection x := by
      rw [ae_iff]
      -- Need to show: volume {y | ¬(y ≠ Θx)} = 0
      -- i.e., volume {y | y = Θx} = 0
      have heq : {a | ¬a ≠ timeReflection x} = {timeReflection x} := by
        ext y; simp only [Set.mem_setOf_eq, ne_eq, not_not, Set.mem_singleton_iff]
      rw [heq]
      exact h_singleton
    filter_upwards [h_compl] with y hy
    exact h_kernel_eq x y (Ne.symm hy)

  -- Step 3: Rewrite LHS using a.e. equality
  have lhs_eq : ∫ x : (SpaceTime d), ∫ y : (SpaceTime d),
        (starRingEnd ℂ (f x)) * (freeCovariance d m (timeReflection x) y : ℂ) * f y =
      ∫ x : (SpaceTime d), ∫ y : (SpaceTime d),
        (starRingEnd ℂ (f x)) * f y *
          (∫ s in Set.Ioi 0, (Real.exp (-s * m^2) : ℂ) *
            heatKernelProfile d s ‖timeReflection x - y‖) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [h_ae] with x hx
    exact MeasureTheory.integral_congr_ae hx
  rw [lhs_eq]

  -- Step 4: Apply Fubini to swap the integration order
  -- This uses schwinger_fubini_swap
  exact schwinger_fubini_swap m f

/-- **Heat kernel bilinear form equals the mixed representation.**

    This encapsulates the multi-step transformation from heat kernel to mixed rep:
    1. Apply `heatKernel_eq_gaussianFT`: H(s,r) = (1/(2π)^d) ∫_k exp(-ik·z) exp(-s|k|²)
    2. Decompose k = (k₀, k_sp) into time and spatial momenta
    3. Do k₀ integral using `gaussian_fourier_1d`: gives √(π/s) exp(-t²/(4s))
    4. Fubini swap: exchange s and k_sp integrals (justified by Schwartz decay)
    5. Do s-integral using `laplace_integral_half_power` with a = t²/4, b = |k_sp|² + m²:
       √π ∫₀^∞ s^{-1/2} exp(-t²/(4s) - (|k_sp|²+m²)s) ds = (π/ω) exp(-ω|t|)
    6. Normalize: (1/(2π)^d) × π = 1/(2(2π)^{d−1})
-/
theorem heatKernel_bilinear_to_mixed_rep (m : ℝ) [Fact (0 < m)] (f : (SchwartzTestFunctionℂ d))
    (hf_supp : ∀ x, x 0 ≤ 0 → f x = 0) :
    ∫ s in Set.Ioi 0, (Real.exp (-s * m^2) : ℂ) *
      ∫ x : (SpaceTime d), ∫ y : (SpaceTime d),
        (starRingEnd ℂ (f x)) * f y * heatKernelProfile d s ‖timeReflection x - y‖ =
    (1 / (2 * (2 * π) ^ (d - 1)) : ℝ) *
      ∫ k_spatial : (SpatialCoords d), ∫ x : (SpaceTime d), ∫ y : (SpaceTime d),
        let ω := Real.sqrt (‖k_spatial‖^2 + m^2)
        (starRingEnd ℂ (f x)) * f y * (1 / ω : ℝ) *
          Complex.exp (-(|-(x 0) - y 0| : ℝ) * ω) *
          Complex.exp (-Complex.I * spatialDot k_spatial (spatialPart x - spatialPart y)) := by
  -- Substitute the Gaussian Fourier representation of the heat kernel, split
  -- k = (k₀, k_sp), and evaluate the k₀ integral (`heatKernel_bilinear_fourier_form`).
  have h_stage4_form : ∫ s in Set.Ioi 0, (Real.exp (-s * m^2) : ℂ) *
      ∫ x : (SpaceTime d), ∫ y : (SpaceTime d),
        (starRingEnd ℂ (f x)) * f y * heatKernelProfile d s ‖timeReflection x - y‖ =
      (1 / (2 * π) ^ d : ℝ) *
      ∫ s in Set.Ioi 0, ∫ k_sp : (SpatialCoords d), ∫ x : (SpaceTime d), ∫ y : (SpaceTime d),
        (starRingEnd ℂ (f x)) * f y *
          (Real.sqrt (π / s) : ℂ) * Complex.exp (-((-(x 0) - y 0)^2 / (4 * s) : ℝ)) *
          Complex.exp (-(s : ℂ) * (‖k_sp‖^2 + m^2)) *
          Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y)) :=
    heatKernel_bilinear_fourier_form m f

  -- Fubini: exchange the s and k_sp integrals (fubini_s_ksp_swap)
  have h_after_fubini : (1 / (2 * π) ^ d : ℝ) *
      ∫ s in Set.Ioi 0, ∫ k_sp : (SpatialCoords d), ∫ x : (SpaceTime d), ∫ y : (SpaceTime d),
        (starRingEnd ℂ (f x)) * f y *
          (Real.sqrt (π / s) : ℂ) * Complex.exp (-((-(x 0) - y 0)^2 / (4 * s) : ℝ)) *
          Complex.exp (-(s : ℂ) * (‖k_sp‖^2 + m^2)) *
          Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y)) =
      (1 / (2 * π) ^ d : ℝ) *
      ∫ k_sp : (SpatialCoords d), ∫ s in Set.Ioi 0, ∫ x : (SpaceTime d), ∫ y : (SpaceTime d),
        (starRingEnd ℂ (f x)) * f y *
          (Real.sqrt (π / s) : ℂ) * Complex.exp (-((-(x 0) - y 0)^2 / (4 * s) : ℝ)) *
          Complex.exp (-(s : ℂ) * (‖k_sp‖^2 + m^2)) *
          Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y)) := by
    congr 1
    exact fubini_s_ksp_swap (d := d) m f hf_supp

  -- Laplace evaluation of the s-integral and normalization
  -- The s-integral evaluates to (π/ω) exp(-ω|t|)
  -- Combined with normalization: (1/(2π)^d) × π = 1/(2(2π)^{d−1})
  have h_stage67 : (1 / (2 * π) ^ d : ℝ) *
      ∫ k_sp : (SpatialCoords d), ∫ s in Set.Ioi 0, ∫ x : (SpaceTime d), ∫ y : (SpaceTime d),
        (starRingEnd ℂ (f x)) * f y *
          (Real.sqrt (π / s) : ℂ) * Complex.exp (-((-(x 0) - y 0)^2 / (4 * s) : ℝ)) *
          Complex.exp (-(s : ℂ) * (‖k_sp‖^2 + m^2)) *
          Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y)) =
      (1 / (2 * (2 * π) ^ (d - 1)) : ℝ) *
        ∫ k_spatial : (SpatialCoords d), ∫ x : (SpaceTime d), ∫ y : (SpaceTime d),
          let ω := Real.sqrt (‖k_spatial‖^2 + m^2)
          (starRingEnd ℂ (f x)) * f y * (1 / ω : ℝ) *
            Complex.exp (-(|-(x 0) - y 0| : ℝ) * ω) *
            Complex.exp (-Complex.I * spatialDot k_spatial (spatialPart x - spatialPart y)) :=
    laplace_s_integral_with_norm m f

  calc ∫ s in Set.Ioi 0, (Real.exp (-s * m^2) : ℂ) *
        ∫ x : (SpaceTime d), ∫ y : (SpaceTime d),
          (starRingEnd ℂ (f x)) * f y * heatKernelProfile d s ‖timeReflection x - y‖
      = (1 / (2 * π) ^ d : ℝ) *
        ∫ s in Set.Ioi 0, ∫ k_sp : (SpatialCoords d), ∫ x : (SpaceTime d), ∫ y : (SpaceTime d),
          (starRingEnd ℂ (f x)) * f y *
            (Real.sqrt (π / s) : ℂ) * Complex.exp (-((-(x 0) - y 0)^2 / (4 * s) : ℝ)) *
            Complex.exp (-(s : ℂ) * (‖k_sp‖^2 + m^2)) *
            Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y)) := h_stage4_form
    _ = (1 / (2 * π) ^ d : ℝ) *
        ∫ k_sp : (SpatialCoords d), ∫ s in Set.Ioi 0, ∫ x : (SpaceTime d), ∫ y : (SpaceTime d),
          (starRingEnd ℂ (f x)) * f y *
            (Real.sqrt (π / s) : ℂ) * Complex.exp (-((-(x 0) - y 0)^2 / (4 * s) : ℝ)) *
            Complex.exp (-(s : ℂ) * (‖k_sp‖^2 + m^2)) *
            Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y)) := h_after_fubini
    _ = (1 / (2 * (2 * π) ^ (d - 1)) : ℝ) *
        ∫ k_spatial : (SpatialCoords d), ∫ x : (SpaceTime d), ∫ y : (SpaceTime d),
          let ω := Real.sqrt (‖k_spatial‖^2 + m^2)
          (starRingEnd ℂ (f x)) * f y * (1 / ω : ℝ) *
            Complex.exp (-(|-(x 0) - y 0| : ℝ) * ω) *
            Complex.exp (-Complex.I * spatialDot k_spatial (spatialPart x - spatialPart y)) := h_stage67

/-- **THEOREM**: The Bessel bilinear form equals the mixed representation form.

    This connects the position-space Bessel kernel to its momentum-space
    mixed representation (spatial in momentum, time in position).

    ∫∫ conj(f(x)) C(Θx, y) f(y) dx dy
    = (1/(2(2π)^{d-1})) ∫_{k_sp} ∫_x ∫_y conj(f) f (1/ω) exp(-ω|t|) exp(-i k_sp·r_sp)

    where ω = √(|k_sp|² + m²), t = -x₀ - y₀, r_sp = x_sp - y_sp.

    **Proof outline** (directly at bilinear level):

    1. **Schwinger representation**: Insert C(Θx,y) = ∫₀^∞ exp(-sm²) H(s,|Θx-y|) ds

    2. **Heat kernel as Gaussian FT**: By `heatKernel_eq_gaussianFT`,
       H(s,r) = (1/(2π)^d) ∫_k exp(-ik·z) exp(-s|k|²) d^d k

    3. **Decompose k = (k₀, k_sp)**: The k-integral becomes a product of 1D (time) and (d−1)-dimensional (spatial) integrals

    4. **Do k₀ integral**: By `gaussian_fourier_1d` (PROVEN),
       ∫ exp(-ik₀t) exp(-sk₀²) dk₀ = √(π/s) exp(-t²/(4s))

    5. **Fubini to swap s and k_sp**: Justified by Schwartz decay of f (absolute convergence)

    6. **Do s-integral**: By `laplace_integral_half_power` (THEOREM) with a = t²/4, b = ω²:
       √π · ∫₀^∞ s^{-1/2} exp(-t²/(4s) - ω²s) ds = (π/ω) exp(-ω|t|)

    7. **Normalize**: (1/(2π)^d) × π = 1/(2(2π)^{d−1}) ✓

    **Note**: Working directly at bilinear level ensures absolute convergence
    (Schwartz test functions provide decay even when t = 0). -/
theorem bessel_bilinear_eq_mixed_representation (m : ℝ) [Fact (0 < m)] [GFFPropagator d m] (f : (SchwartzTestFunctionℂ d))
    (hf_supp : ∀ x, x 0 ≤ 0 → f x = 0) :
  ∫ x : (SpaceTime d), ∫ y : (SpaceTime d),
    (starRingEnd ℂ (f x)) *
    (freeCovariance d m (timeReflection x) y : ℂ) *
    f y =
  (1 / (2 * (2 * π) ^ (d - 1)) : ℝ) *
  ∫ k_spatial : (SpatialCoords d), ∫ x : (SpaceTime d), ∫ y : (SpaceTime d),
    let ω := Real.sqrt (‖k_spatial‖^2 + m^2)
    (starRingEnd ℂ (f x)) * f y *
    (1 / ω : ℝ) *
    Complex.exp (-(|-(x 0) - y 0| : ℝ) * ω) *
    Complex.exp (-Complex.I * spatialDot k_spatial (spatialPart x - spatialPart y)) := by
  -- Step 1: Convert Bessel bilinear form to heat kernel form via Schwinger representation
  rw [bilinear_schwinger_eq_heatKernel]
  -- Step 2: Convert heat kernel form to mixed representation
  exact heatKernel_bilinear_to_mixed_rep m f hf_supp

/-! ## Non-negativity -/


end
