/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

/-!
# Fourier Transforms for QFT

This file contains Fourier transform identities needed for the Gaussian Free Field,
particularly for proving reflection positivity of the free covariance.

## Main Results

- `fourier_lorentzian_1d`: The 1D Fourier transform of the Lorentzian 1/(k² + μ²)
  gives exponential decay: ∫ dk e^{ikx} / (k² + μ²) = (π/μ) e^{-μ|x|}

- `fourier_exponential_decay'`: The inverse transform - Fourier transform of e^{-μ|x|}
  gives the Lorentzian: ∫ dx e^{ikx} e^{-μ|x|} = 2μ/(k² + μ²)

## Mathematical Background

The key identity for reflection positivity is:

  C(x - y) = ∫ dᵈk / (2π)ᵈ · e^{ik·(x-y)} / (k² + m²)

For the time direction k₀, we need:

  ∫ dk₀ e^{ik₀(x₀ - y₀)} / (k₀² + μ²) = (π/μ) e^{-μ|x₀ - y₀|}

where μ² = |p̄|² + m² (with p̄ the spatial momentum).

When x₀ > 0 and y₀ < 0 (positive and negative time respectively), we have
x₀ - y₀ > 0, so the exponential is e^{-μ(x₀ - y₀)} which factorizes as
e^{-μx₀} · e^{μy₀}, enabling the reflection positivity argument.

## Proof Strategy

The 1D result follows from Fourier inversion:
1. Compute half-line integrals using the fundamental theorem of calculus
2. Sum to get FT[e^{-μ|x|}] = 2μ/(k² + μ²)
3. Apply Fourier inversion to derive the Lorentzian result

-/

open MeasureTheory Complex Real
open scoped BigOperators FourierTransform

noncomputable section

/-- The exponential decay function is integrable when μ > 0.
    Proof: Split ℝ into (-∞, 0] ∪ (0, ∞) and use:
    - integrableOn_exp_mul_Iic for exp(μx) on (-∞, 0] (since μ > 0)
    - integrableOn_exp_mul_Ioi for exp(-μx) on (0, ∞) (since -μ < 0) -/
lemma integrable_exponential_decay (μ : ℝ) (hμ : 0 < μ) :
    Integrable (fun x : ℝ => Real.exp (-μ * |x|)) volume := by
  rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ))]
  apply IntegrableOn.union
  · -- On (-∞, 0]: |x| = -x, so exp(-μ|x|) = exp(μx)
    have h1 : ∀ x ∈ Set.Iic (0 : ℝ), Real.exp (-μ * |x|) = Real.exp (μ * x) := by
      intro x hx
      simp only [Set.mem_Iic] at hx
      rw [abs_of_nonpos hx]
      ring_nf
    rw [integrableOn_congr_fun h1 measurableSet_Iic]
    exact integrableOn_exp_mul_Iic hμ 0
  · -- On (0, ∞): |x| = x, so exp(-μ|x|) = exp(-μx)
    have h1 : ∀ x ∈ Set.Ioi (0 : ℝ), Real.exp (-μ * |x|) = Real.exp ((-μ) * x) := by
      intro x hx
      simp only [Set.mem_Ioi] at hx
      rw [abs_of_pos hx]
    rw [integrableOn_congr_fun h1 measurableSet_Ioi]
    exact exp_neg_integrableOn_Ioi 0 hμ

/-- The Fourier integrand of exponential decay is integrable.
    Proof: |exp(ikx)| = 1, so the norm of the integrand equals exp(-μ|x|),
    which is integrable by integrable_exponential_decay. -/
lemma integrable_exponential_decay_fourier (μ : ℝ) (hμ : 0 < μ) (k : ℝ) :
    Integrable (fun x : ℝ => Complex.exp (Complex.I * k * x) * Real.exp (-μ * |x|)) volume := by
  have hint : Integrable (fun x : ℝ => (Real.exp (-μ * |x|) : ℂ)) volume :=
    Integrable.ofReal (integrable_exponential_decay μ hμ)
  apply Integrable.bdd_mul (c := 1) hint
  · apply Continuous.aestronglyMeasurable
    refine Complex.continuous_exp.comp ?_
    refine Continuous.mul ?_ continuous_ofReal
    exact continuous_const
  · filter_upwards with x
    rw [Complex.norm_exp]
    simp only [Complex.mul_re, Complex.I_re, Complex.ofReal_re, zero_mul,
               Complex.I_im, Complex.ofReal_im, mul_zero, sub_zero, Real.exp_zero, le_refl]

/-! ### Half-Line Integrals and Antiderivatives

The half-line integrals are the fundamental building blocks. We compute these using
the fundamental theorem of calculus for improper integrals, then combine them to
get the Fourier transform of e^{-μ|x|}, and finally use Fourier inversion to
derive the Lorentzian result.
-/

/-- The coefficient ik + α is nonzero when α ≠ 0 (since Re(ik + α) = α ≠ 0). -/
lemma ik_add_ne_zero (α : ℝ) (hα : α ≠ 0) (k : ℝ) : Complex.I * k + (α : ℂ) ≠ 0 := by
  intro h
  have hre : (Complex.I * k + (α : ℂ)).re = 0 := by simp [h]
  simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re,
             Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero] at hre
  simp only [zero_add] at hre
  exact hα hre

/-- Complex exponential e^{cx} tends to 0 as x → +∞ when Re(c) < 0.
    Proof: ‖e^{cx}‖ = e^{Re(c)·x} → 0 since Re(c) < 0 and x → +∞. -/
theorem tendsto_cexp_atTop_zero {c : ℂ} (hc : c.re < 0) :
    Filter.Tendsto (fun x : ℝ => Complex.exp (c * x)) Filter.atTop (nhds 0) := by
  rw [Complex.tendsto_exp_nhds_zero_iff]
  have h : ∀ x : ℝ, (c * x).re = c.re * x := by
    intro x; simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  simp_rw [h]
  have hneg : 0 < -c.re := neg_pos.mpr hc
  have h1 : Filter.Tendsto (fun x => (-c.re) * x) Filter.atTop Filter.atTop :=
    Filter.tendsto_id.const_mul_atTop hneg
  have h2 : Filter.Tendsto (fun x => -(-c.re * x)) Filter.atTop Filter.atBot :=
    Filter.Tendsto.comp Filter.tendsto_neg_atTop_atBot h1
  convert h2 using 1; funext x; ring

/-- Complex exponential e^{cx} tends to 0 as x → -∞ when Re(c) > 0.
    Proof: ‖e^{cx}‖ = e^{Re(c)·x} → 0 since Re(c) > 0 and x → -∞. -/
theorem tendsto_cexp_atBot_zero {c : ℂ} (hc : c.re > 0) :
    Filter.Tendsto (fun x : ℝ => Complex.exp (c * x)) Filter.atBot (nhds 0) := by
  rw [Complex.tendsto_exp_nhds_zero_iff]
  have h : ∀ x : ℝ, (c * x).re = c.re * x := by
    intro x; simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  simp_rw [h]
  exact Filter.tendsto_id.const_mul_atBot hc

/-- The integrand e^{(ik-μ)x} is integrable on [0, ∞) when μ > 0.
    This follows from the exponential decay since Re(ik - μ) = -μ < 0. -/
theorem integrableOn_exp_decay_Ioi (μ : ℝ) (hμ : 0 < μ) (k : ℝ) :
    MeasureTheory.IntegrableOn
      (fun x : ℝ => Complex.exp ((Complex.I * k - μ) * x))
      (Set.Ioi 0) volume := by
  have hc_re : (Complex.I * k - μ).re < 0 := by
    simp only [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re,
               Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero]
    linarith
  exact integrableOn_exp_mul_complex_Ioi hc_re 0

/-- The integrand e^{(ik+μ)x} is integrable on (-∞, 0] when μ > 0.
    This follows from the exponential decay since Re(ik + μ) = μ > 0. -/
theorem integrableOn_exp_growth_Iic (μ : ℝ) (hμ : 0 < μ) (k : ℝ) :
    MeasureTheory.IntegrableOn
      (fun x : ℝ => Complex.exp ((Complex.I * k + μ) * x))
      (Set.Iic 0) volume := by
  have hc_re : 0 < (Complex.I * k + μ).re := by
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re,
               Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, zero_add]
    exact hμ
  exact integrableOn_exp_mul_complex_Iic hc_re 0

/-- ik - μ is nonzero when μ ≠ 0 (since Re(ik - μ) = -μ ≠ 0). -/
lemma ik_sub_ne_zero (μ : ℝ) (hμ : μ ≠ 0) (k : ℝ) : Complex.I * k - (μ : ℂ) ≠ 0 := by
  intro h
  have hre : (Complex.I * k - (μ : ℂ)).re = 0 := by simp [h]
  simp only [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re,
             Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, zero_sub] at hre
  exact hμ (neg_eq_zero.mp hre)

/-- The integral over the positive half-line [0, ∞):
    ∫₀^∞ e^{ikx} e^{-μx} dx = 1/(μ - ik)

    Proof: Use FTC with antiderivative e^{(ik-μ)x}/(ik-μ).
    At +∞: e^{(ik-μ)x} → 0 since Re(ik-μ) = -μ < 0.
    At 0: e^0/(ik-μ) = 1/(ik-μ).
    Result: 0 - 1/(ik-μ) = -1/(ik-μ) = 1/(μ-ik). -/
theorem fourier_exp_decay_positive_halfline (μ : ℝ) (hμ : 0 < μ) (k : ℝ) :
    ∫ x : ℝ in Set.Ioi 0, Complex.exp (Complex.I * k * x) * Real.exp (-μ * x) =
      1 / (μ - Complex.I * k) := by
  -- Combine exponentials: e^{ikx} * e^{-μx} = e^{(ik-μ)x}
  have h_combine : ∀ x : ℝ, Complex.exp (Complex.I * k * x) * Real.exp (-μ * x) =
      Complex.exp ((Complex.I * k - μ) * x) := by
    intro x
    have h_real_to_complex : (Real.exp (-μ * x) : ℂ) = Complex.exp ((-μ : ℂ) * x) := by
      rw [Complex.ofReal_exp]; congr 1; simp only [Complex.ofReal_mul, Complex.ofReal_neg]
    rw [h_real_to_complex, ← Complex.exp_add]; congr 1; ring
  simp_rw [h_combine]
  -- Let c = ik - μ
  set c : ℂ := Complex.I * k - μ with hc_def
  have hc_ne : c ≠ 0 := ik_sub_ne_zero μ (ne_of_gt hμ) k
  have hc_re : c.re < 0 := by
    simp only [hc_def, Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re,
               Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero]
    linarith
  -- Antiderivative: d/dx[e^{cx}/c] = e^{cx}
  have h_antideriv : ∀ x ∈ Set.Ici (0 : ℝ),
      HasDerivAt (fun t : ℝ => Complex.exp (c * t) / c) (Complex.exp (c * x)) x := by
    intro x _
    have h1 : HasDerivAt (fun t : ℝ => c * (t : ℂ)) c x := by
      have hid : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 x := Complex.ofRealCLM.hasDerivAt
      simpa using hid.const_mul c
    have h_exp : HasDerivAt (fun t : ℝ => Complex.exp (c * t)) (Complex.exp (c * x) * c) x :=
      HasDerivAt.cexp h1
    have h_div : HasDerivAt (fun t : ℝ => Complex.exp (c * t) / c)
        (Complex.exp (c * x) * c / c) x := h_exp.div_const c
    convert h_div using 1; field_simp
  -- Limit at +∞: e^{cx}/c → 0 since Re(c) < 0
  have h_tendsto : Filter.Tendsto (fun x : ℝ => Complex.exp (c * x) / c) Filter.atTop (nhds 0) := by
    have h_exp_tendsto := tendsto_cexp_atTop_zero hc_re
    have h_zero_div : (0 : ℂ) / c = 0 := zero_div c
    rw [← h_zero_div]
    exact Filter.Tendsto.div_const h_exp_tendsto c
  -- Integrability
  have h_int : IntegrableOn (fun x : ℝ => Complex.exp (c * x)) (Set.Ioi 0) volume := by
    have hsimp : c = Complex.I * k - μ := rfl
    rw [hsimp]
    exact integrableOn_exp_decay_Ioi μ hμ k
  -- Apply FTC: ∫₀^∞ f' = lim f - f(0)
  have h_ftc := integral_Ioi_of_hasDerivAt_of_tendsto' h_antideriv h_int h_tendsto
  rw [h_ftc]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, zero_sub]
  -- -(1/c) = 1/(μ - ik) since c = ik - μ, so μ - ik = -c
  have hdenom_ne : (μ : ℂ) - Complex.I * k ≠ 0 := by
    have h : (μ : ℂ) - Complex.I * k = -c := by simp only [hc_def]; ring
    rw [h]; exact neg_ne_zero.mpr hc_ne
  field_simp [hc_ne, hdenom_ne]
  ring

/-- The integral over the negative half-line (-∞, 0]:
    ∫_{-∞}^0 e^{ikx} e^{μx} dx = 1/(μ + ik)

    Proof: Use FTC with antiderivative e^{(ik+μ)x}/(ik+μ).
    At -∞: e^{(ik+μ)x} → 0 since Re(ik+μ) = μ > 0.
    At 0: e^0/(ik+μ) = 1/(ik+μ) = 1/(μ+ik). -/
theorem fourier_exp_decay_negative_halfline (μ : ℝ) (hμ : 0 < μ) (k : ℝ) :
    ∫ x : ℝ in Set.Iic 0, Complex.exp (Complex.I * k * x) * Real.exp (μ * x) =
      1 / (μ + Complex.I * k) := by
  -- Combine exponentials: e^{ikx} * e^{μx} = e^{(ik+μ)x}
  have h_combine : ∀ x : ℝ, Complex.exp (Complex.I * k * x) * Real.exp (μ * x) =
      Complex.exp ((Complex.I * k + μ) * x) := by
    intro x
    have h_real_to_complex : (Real.exp (μ * x) : ℂ) = Complex.exp ((μ : ℂ) * x) := by
      rw [Complex.ofReal_exp]; congr 1; simp only [Complex.ofReal_mul]
    rw [h_real_to_complex, ← Complex.exp_add]; congr 1; ring
  simp_rw [h_combine]
  -- Let c = ik + μ
  set c : ℂ := Complex.I * k + μ with hc_def
  have hc_ne : c ≠ 0 := ik_add_ne_zero μ (ne_of_gt hμ) k
  have hc_re : c.re > 0 := by
    simp only [hc_def, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re,
               Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, zero_add]
    exact hμ
  -- Antiderivative: d/dx[e^{cx}/c] = e^{cx}
  have h_antideriv : ∀ x ∈ Set.Iic (0 : ℝ),
      HasDerivAt (fun t : ℝ => Complex.exp (c * t) / c) (Complex.exp (c * x)) x := by
    intro x _
    have h1 : HasDerivAt (fun t : ℝ => c * (t : ℂ)) c x := by
      have hid : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 x := Complex.ofRealCLM.hasDerivAt
      simpa using hid.const_mul c
    have h_exp : HasDerivAt (fun t : ℝ => Complex.exp (c * t)) (Complex.exp (c * x) * c) x :=
      HasDerivAt.cexp h1
    have h_div : HasDerivAt (fun t : ℝ => Complex.exp (c * t) / c)
        (Complex.exp (c * x) * c / c) x := h_exp.div_const c
    convert h_div using 1; field_simp
  -- Limit at -∞: e^{cx}/c → 0 since Re(c) > 0
  have h_tendsto : Filter.Tendsto (fun x : ℝ => Complex.exp (c * x) / c) Filter.atBot (nhds 0) := by
    have h_exp_tendsto := tendsto_cexp_atBot_zero hc_re
    have h_zero_div : (0 : ℂ) / c = 0 := zero_div c
    rw [← h_zero_div]
    exact Filter.Tendsto.div_const h_exp_tendsto c
  -- Integrability
  have h_int : IntegrableOn (fun x : ℝ => Complex.exp (c * x)) (Set.Iic 0) volume := by
    have hsimp : c = Complex.I * k + μ := rfl
    rw [hsimp]
    exact integrableOn_exp_growth_Iic μ hμ k
  -- Apply FTC: ∫_{-∞}^0 f' = f(0) - lim_{-∞} f
  have h_ftc := integral_Iic_of_hasDerivAt_of_tendsto' h_antideriv h_int h_tendsto
  rw [h_ftc]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, sub_zero]
  -- 1/c = 1/(ik + μ) = 1/(μ + ik)
  congr 1
  simp only [hc_def]; ring

/-- The full integral as sum of half-line integrals.
    This is the key decomposition:
    ∫_{-∞}^∞ e^{ikx} e^{-μ|x|} dx = ∫_{-∞}^0 e^{ikx} e^{μx} dx + ∫_0^∞ e^{ikx} e^{-μx} dx
                                   = 1/(μ+ik) + 1/(μ-ik)
                                   = 2μ/(k² + μ²) -/
lemma fourier_exponential_decay_split (μ : ℝ) (hμ : 0 < μ) (k : ℝ) :
    (∫ x : ℝ in Set.Iic 0, Complex.exp (Complex.I * k * x) * Real.exp (μ * x)) +
    (∫ x : ℝ in Set.Ioi 0, Complex.exp (Complex.I * k * x) * Real.exp (-μ * x)) =
      2 * μ / (k^2 + μ^2) := by
  rw [fourier_exp_decay_negative_halfline μ hμ k, fourier_exp_decay_positive_halfline μ hμ k]
  -- 1/(μ + ik) + 1/(μ - ik) = 2μ/(μ² + k²) = 2μ/(k² + μ²)
  have hdenom_ne : (μ : ℂ) + Complex.I * k ≠ 0 := by
    intro h
    have hre : ((μ : ℂ) + Complex.I * k).re = 0 := by simp [h]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
               Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero] at hre
    linarith
  have hdenom_ne' : (μ : ℂ) - Complex.I * k ≠ 0 := by
    intro h
    have hre : ((μ : ℂ) - Complex.I * k).re = 0 := by simp [h]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
               Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero] at hre
    linarith
  -- Combine fractions: 1/(μ+ik) + 1/(μ-ik) = (μ-ik + μ+ik)/((μ+ik)(μ-ik)) = 2μ/(μ²+k²)
  have hdenom_prod : (μ : ℂ) + Complex.I * k ≠ 0 ∧ (μ : ℂ) - Complex.I * k ≠ 0 :=
    ⟨hdenom_ne, hdenom_ne'⟩
  have h_prod : ((μ : ℂ) + Complex.I * k) * ((μ : ℂ) - Complex.I * k) = μ^2 + k^2 := by
    ring_nf
    simp only [Complex.I_sq]
    ring
  rw [add_comm, div_add_div _ _ hdenom_ne' hdenom_ne]
  congr 1
  · ring
  · rw [mul_comm]
    ring_nf
    simp only [Complex.I_sq]
    ring

/-! ### Fourier Transform of Exponential Decay

The Fourier transform of e^{-μ|x|} gives the Lorentzian 2μ/(k² + μ²).
This is the "forward" direction of the Fourier pair.
-/

/-- The Fourier transform of the exponential decay function e^{-μ|x|}.
    ∫_{-∞}^{∞} e^{ikx} e^{-μ|x|} dx = 2μ/(k² + μ²)

    This follows from splitting at x = 0 (see fourier_exponential_decay_split). -/
lemma fourier_exponential_decay' (μ : ℝ) (hμ : 0 < μ) (k : ℝ) :
    ∫ x : ℝ, Complex.exp (Complex.I * k * x) * Real.exp (-μ * |x|) =
      2 * μ / (k^2 + μ^2) := by
  -- On Iic: |x| = -x, so e^{-μ|x|} = e^{μx}
  have h_Iic : ∫ x : ℝ in Set.Iic 0, Complex.exp (Complex.I * k * x) * Real.exp (-μ * |x|) =
      ∫ x : ℝ in Set.Iic 0, Complex.exp (Complex.I * k * x) * Real.exp (μ * x) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Iic
    intro x hx
    simp only [Set.mem_Iic] at hx
    simp only [abs_of_nonpos hx]
    ring_nf
  -- On Ioi: |x| = x, so e^{-μ|x|} = e^{-μx}
  have h_Ioi : ∫ x : ℝ in Set.Ioi 0, Complex.exp (Complex.I * k * x) * Real.exp (-μ * |x|) =
      ∫ x : ℝ in Set.Ioi 0, Complex.exp (Complex.I * k * x) * Real.exp (-μ * x) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    simp only [Set.mem_Ioi] at hx
    simp only [abs_of_pos hx]
  -- Integrability on both halves follows from global integrability
  have h_int_full := integrable_exponential_decay_fourier μ hμ k
  have h_int_Iic : IntegrableOn
      (fun x : ℝ => Complex.exp (Complex.I * k * x) * Real.exp (-μ * |x|)) (Set.Iic 0) volume :=
    h_int_full.integrableOn
  have h_int_Ioi : IntegrableOn
      (fun x : ℝ => Complex.exp (Complex.I * k * x) * Real.exp (-μ * |x|)) (Set.Ioi 0) volume :=
    h_int_full.integrableOn
  -- Split the integral: ∫_ℝ = ∫_{≤0} + ∫_{>0}
  have h_split : ∫ x : ℝ, Complex.exp (Complex.I * k * x) * Real.exp (-μ * |x|) =
      (∫ x : ℝ in Set.Iic 0, Complex.exp (Complex.I * k * x) * Real.exp (-μ * |x|)) +
      (∫ x : ℝ in Set.Ioi 0, Complex.exp (Complex.I * k * x) * Real.exp (-μ * |x|)) := by
    rw [← MeasureTheory.setIntegral_union₀ (Set.Iic_disjoint_Ioi (le_refl (0:ℝ))).aedisjoint
        measurableSet_Ioi.nullMeasurableSet h_int_Iic h_int_Ioi]
    rw [Set.Iic_union_Ioi]
    exact MeasureTheory.setIntegral_univ.symm
  rw [h_split, h_Iic, h_Ioi]
  exact fourier_exponential_decay_split μ hμ k

/-! ### Fourier Inversion and the Lorentzian Transform

By the Fourier inversion theorem, if FT[f](k) = g(k), then IFT[g](x) = f(x).
Since FT[e^{-μ|x|}](k) = 2μ/(k² + μ²), the inverse gives:
  (1/2π) ∫ e^{ikx} · 2μ/(k² + μ²) dk = e^{-μ|x|}
Rearranging: ∫ e^{ikx} / (k² + μ²) dk = (π/μ) e^{-μ|x|}

## Relation to Mathlib's Fourier Transform

Mathlib's Fourier transform uses the convention:
  FT_mathlib(f)(ξ) = ∫ exp(2πi⟨x,ξ⟩) f(x) dx

For ℝ with standard inner product ⟨x,ξ⟩ = xξ, this becomes:
  FT_mathlib(f)(ξ) = ∫ exp(2πixξ) f(x) dx

Our convention uses:
  FT(f)(k) = ∫ exp(ikx) f(x) dx

The relationship is: FT(f)(k) = FT_mathlib(f)(k/(2π))

Mathlib provides `MeasureTheory.Integrable.fourierInv_fourier_eq` which says:
If f is integrable, FT(f) is integrable, and f is continuous at x, then
  IFT(FT(f))(x) = f(x)
-/

/-- The exponential decay function e^{-μ|x|} as a function ℝ → ℂ. -/
noncomputable def expDecayFun (μ : ℝ) : ℝ → ℂ := fun x => Real.exp (-μ * |x|)

/-- The exponential decay function is continuous. -/
lemma continuous_expDecayFun (μ : ℝ) : Continuous (expDecayFun μ) := by
  unfold expDecayFun
  refine Continuous.comp continuous_ofReal ?_
  refine Real.continuous_exp.comp ?_
  exact continuous_const.mul continuous_abs

/-- The exponential decay function is integrable over ℝ. -/
lemma integrable_expDecayFun (μ : ℝ) (hμ : 0 < μ) : Integrable (expDecayFun μ) volume := by
  unfold expDecayFun
  exact Integrable.ofReal (integrable_exponential_decay μ hμ)

/-- Mathlib's Fourier transform of expDecayFun equals the scaled Lorentzian.
    FT_mathlib(e^{-μ|x|})(ξ) = 2μ/(4π²ξ² + μ²)
    This follows from fourier_exponential_decay' via the substitution k = -2πξ. -/
lemma fourierIntegral_expDecayFun_eq (μ : ℝ) (hμ : 0 < μ) (ξ : ℝ) :
    𝓕 (expDecayFun μ) ξ = 2 * μ / (4 * π^2 * ξ^2 + μ^2) := by
  rw [Real.fourier_eq']
  unfold expDecayFun
  simp only [smul_eq_mul]
  -- Mathlib uses exp(-2πi⟪y, ξ⟫) = exp(-2πi y ξ)
  -- We relate this to fourier_exponential_decay' with k = -2πξ
  -- First simplify inner product to multiplication
  have h_inner : ∀ v : ℝ, @inner ℝ ℝ _ v ξ = v * ξ := fun v => by
    rw [show @inner ℝ ℝ _ v ξ = ξ * v from RCLike.inner_apply v ξ]; ring
  simp_rw [h_inner]
  -- Rewrite integral to match fourier_exponential_decay'
  have h_int_eq : ∫ v : ℝ, Complex.exp (↑(-2 * π * (v * ξ)) * I) * ↑(Real.exp (-μ * |v|)) =
      ∫ v : ℝ, Complex.exp (Complex.I * (-2 * π * ξ) * v) * Real.exp (-μ * |v|) := by
    congr 1
    ext v
    congr 1
    · congr 1
      push_cast; ring
  rw [h_int_eq]
  have h := fourier_exponential_decay' μ hμ (-2 * π * ξ)
  -- h: ∫ exp(I * ↑(-2πξ) * v) * ... = 2μ / (↑(-2πξ)² + μ²)
  -- goal: ∫ exp(I * (-2 * ↑π * ↑ξ) * v) * ... = 2μ / (4π²ξ² + μ²)
  convert h using 2
  · ext v
    congr 2
    push_cast; ring
  · push_cast; ring

/-- The Mathlib Fourier transform of expDecayFun is integrable. -/
lemma integrable_fourierIntegral_expDecayFun (μ : ℝ) (hμ : 0 < μ) :
    Integrable (𝓕 (expDecayFun μ)) volume := by
  have h_eq : 𝓕 (expDecayFun μ) =
      fun ξ : ℝ => (2 * μ / (4 * π^2 * ξ^2 + μ^2) : ℂ) := by
    ext ξ
    exact fourierIntegral_expDecayFun_eq μ hμ ξ
  rw [h_eq]
  -- Use the real Lorentzian integrability
  have hμ_ne : μ ≠ 0 := ne_of_gt hμ
  have h_scale : (2 * π / μ : ℝ) ≠ 0 := by positivity
  -- First show integrability of the scaled Lorentzian
  have h_lorentz : Integrable (fun ξ : ℝ => (2 / μ) * (1 + (2 * π / μ * ξ)^2)⁻¹) volume := by
    apply Integrable.const_mul
    exact (integrable_comp_smul_iff volume (fun y : ℝ => (1 + y^2)⁻¹) h_scale).mpr integrable_inv_one_add_sq
  -- Show the two real functions are equal
  have h_eq_real : (fun ξ : ℝ => 2 * μ / (4 * π^2 * ξ^2 + μ^2)) =
      (fun ξ => (2 / μ) * (1 + (2 * π / μ * ξ)^2)⁻¹) := by
    ext ξ
    have denom_pos : (0 : ℝ) < 4 * π^2 * ξ^2 + μ^2 := by nlinarith [sq_nonneg ξ, sq_nonneg μ, Real.pi_pos]
    have h1 : (2 * π / μ * ξ)^2 = 4 * π^2 * ξ^2 / μ^2 := by ring
    rw [h1]
    have hμsq_pos : (0 : ℝ) < μ^2 := sq_pos_of_pos hμ
    field_simp
    ring
  -- Now show the complex function is integrable
  have h_int_real : Integrable (fun ξ : ℝ => 2 * μ / (4 * π^2 * ξ^2 + μ^2)) volume := by
    rw [h_eq_real]; exact h_lorentz
  convert h_int_real.ofReal using 1
  ext ξ
  push_cast
  rfl

/-- Fourier inversion theorem for the exponential decay / Lorentzian pair.
    If FT[e^{-μ|x|}](k) = 2μ/(k² + μ²), then the inverse transform gives:
    (1/2π) ∫ e^{ikx} · 2μ/(k² + μ²) dk = e^{-μ|x|}

    This follows from Mathlib's Fourier inversion theorem applied to the exponential decay function,
    combined with the explicit formula for its Fourier transform and a change of variables. -/
theorem fourier_inversion_exp_decay (μ : ℝ) (hμ : 0 < μ) (x : ℝ) :
    (1 / (2 * π) : ℂ) * ∫ k : ℝ, Complex.exp (Complex.I * k * x) * (2 * μ / (k^2 + μ^2)) =
      (Real.exp (-μ * |x|) : ℂ) := by
  -- From Mathlib's inversion theorem: 𝓕⁻ (𝓕 f) = f
  have hinv_fun : 𝓕⁻ (𝓕 (expDecayFun μ)) = expDecayFun μ :=
    Continuous.fourierInv_fourier_eq (continuous_expDecayFun μ)
      (integrable_expDecayFun μ hμ) (integrable_fourierIntegral_expDecayFun μ hμ)
  have hinv : 𝓕⁻ (𝓕 (expDecayFun μ)) x = expDecayFun μ x := congrFun hinv_fun x
  -- RHS simplification
  have hRHS : expDecayFun μ x = (Real.exp (-μ * |x|) : ℂ) := rfl
  rw [hRHS] at hinv
  -- Expand LHS of hinv using fourierInv definition: 𝓕⁻ g w = ∫ v, exp(2πi⟪v, w⟫) • g v
  rw [Real.fourierInv_eq'] at hinv
  -- Substitute the Fourier transform
  have hFT : ∀ ξ : ℝ, 𝓕 (expDecayFun μ) ξ =
      2 * μ / (4 * π^2 * ξ^2 + μ^2) := fourierIntegral_expDecayFun_eq μ hμ
  simp_rw [hFT, smul_eq_mul] at hinv
  -- hinv is now: ∫ ξ, exp(2πi⟪ξ, x⟫) * (2μ/(4π²ξ² + μ²)) = exp(-μ|x|)
  -- Simplify inner product on ℝ: ⟪ξ, x⟫ = ξ * x
  have h_inner : ∀ ξ : ℝ, @inner ℝ ℝ _ ξ x = ξ * x := fun ξ => by
    rw [show @inner ℝ ℝ _ ξ x = x * ξ from RCLike.inner_apply ξ x]; ring
  simp_rw [h_inner] at hinv
  -- Now hinv: ∫ ξ, exp(2πi ξ x) * (2μ/(4π²ξ² + μ²)) = exp(-μ|x|)
  -- Simplify the exponential: exp(2πi(ξ*x)) = exp(2πi x ξ)
  have h_char : ∀ ξ : ℝ, Complex.exp (↑(2 * π * (ξ * x)) * I) =
      Complex.exp (Complex.I * (2 * π * x) * ξ) := by
    intro ξ
    congr 1
    simp only [ofReal_mul, ofReal_ofNat]
    ring
  simp_rw [h_char] at hinv
  -- hinv: ∫ v, exp(I * 2πx * v) * (2μ / (4π²v² + μ²)) = exp(-μ|x|)
  -- Goal: (1/2π) * ∫ k, exp(I * k * x) * (2μ / (k² + μ²)) = exp(-μ|x|)
  -- Change of variables: k = 2πv transforms hinv to the goal
  have h2π_pos : (0 : ℝ) < 2 * π := by positivity
  -- Define G(k) = exp(I * k * x) * (2μ / (k² + μ²))
  let G : ℝ → ℂ := fun k => Complex.exp (Complex.I * k * x) * (2 * μ / (k^2 + μ^2))
  -- Key: ∫ G(2π * v) dv = |2π|⁻¹ * ∫ G(k) dk
  have h_cv : ∫ v : ℝ, G ((2 * π) * v) = |2 * π|⁻¹ * ∫ k, G k := by
    have h := MeasureTheory.Measure.integral_comp_smul volume G (2 * π)
    simp only [Module.finrank_self, pow_one, smul_eq_mul, abs_inv] at h
    exact h
  -- Show that G(2π * v) equals the integrand in hinv
  have hG_eq : ∀ v : ℝ, G ((2 * π) * v) =
      Complex.exp (Complex.I * (2 * π * x) * v) * (2 * μ / (4 * π^2 * v^2 + μ^2)) := by
    intro v
    simp only [G]
    congr 1
    · congr 1
      push_cast
      ring
    · congr 1
      have : (↑((2 * π) * v) : ℂ)^2 = 4 * π^2 * v^2 := by push_cast; ring
      rw [this]
  simp_rw [hG_eq] at h_cv
  -- Substitute into hinv
  rw [h_cv] at hinv
  rw [abs_of_pos h2π_pos] at hinv
  -- hinv is now: (2π)⁻¹ * ∫ G(k) dk = exp(-μ|x|)
  -- Simplify G to match the goal
  have hG_def : ∀ k : ℝ, G k = Complex.exp (Complex.I * k * x) * (2 * μ / (k^2 + μ^2)) := by
    intro k; rfl
  simp_rw [hG_def] at hinv
  -- Adjust coefficient
  have h_coeff : (1 / (2 * π) : ℂ) = ((2 * π)⁻¹ : ℝ) := by
    simp only [one_div, Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_ofNat]
  rw [h_coeff]
  exact hinv

/-! ### The Lorentzian Fourier Transform (Main Result)

We derive the Lorentzian Fourier transform from the Fourier inversion theorem.
-/

/-- The 1D Fourier transform of the Lorentzian/Cauchy distribution.
    This is the fundamental identity:
    ∫_{-∞}^{∞} e^{ikx} / (k² + μ²) dk = (π/μ) e^{-μ|x|}

    Derivation from Fourier inversion:
    From `fourier_inversion_exp_decay`: (1/2π) ∫ e^{ikx} · 2μ/(k² + μ²) dk = e^{-μ|x|}
    Multiply both sides by π/μ:
      (1/2π) · (π/μ) · 2μ ∫ e^{ikx} / (k² + μ²) dk = (π/μ) e^{-μ|x|}
      ∫ e^{ikx} / (k² + μ²) dk = (π/μ) e^{-μ|x|} -/
theorem fourier_lorentzian_1d (μ : ℝ) (hμ : 0 < μ) (x : ℝ) :
    ∫ k : ℝ, Complex.exp (Complex.I * k * x) / (k^2 + μ^2) =
      (π / μ) * Real.exp (-μ * |x|) := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have hμ' : μ ≠ 0 := ne_of_gt hμ
  have h2π : (2 : ℝ) * π ≠ 0 := by positivity
  have h2μ : (2 : ℝ) * μ ≠ 0 := by positivity
  -- Start from fourier_inversion_exp_decay:
  -- (1/2π) * ∫ e^{ikx} * (2μ/(k² + μ²)) dk = e^{-μ|x|}
  have hinv := fourier_inversion_exp_decay μ hμ x
  -- Rewrite the integral: ∫ e^{ikx} * (2μ/(k² + μ²)) = (2μ) * ∫ e^{ikx} / (k² + μ²)
  have h_factor : ∫ k : ℝ, Complex.exp (Complex.I * k * x) * (2 * μ / (k^2 + μ^2)) =
                  (2 * μ : ℂ) * ∫ k : ℝ, Complex.exp (Complex.I * k * x) / (k^2 + μ^2) := by
    trans (2 * (μ : ℂ)) * ∫ k : ℝ, Complex.exp (Complex.I * k * x) / (k^2 + μ^2)
    · rw [show (fun k : ℝ => Complex.exp (Complex.I * k * x) * (2 * μ / (k^2 + μ^2))) =
          (fun k : ℝ => (2 * (μ : ℂ)) * (Complex.exp (Complex.I * k * x) / (k^2 + μ^2))) from
        funext (fun k => by ring)]
      exact integral_const_mul _ _
    · rfl
  rw [h_factor] at hinv
  -- hinv : (1/2π) * (2μ * ∫ ...) = e^{-μ|x|}
  -- Rearrange: (μ/π) * ∫ ... = e^{-μ|x|}
  have hμπ_ne : (μ : ℂ) / π ≠ 0 := by
    simp only [ne_eq, div_eq_zero_iff, Complex.ofReal_eq_zero]
    push Not
    exact ⟨hμ', hπ⟩
  -- Simplify coefficient: (1/2π) * (2μ * I) = (μ/π) * I
  have h_rearrange : (1 : ℂ) / (2 * π) * (2 * μ * ∫ k : ℝ, Complex.exp (Complex.I * k * x) / (k^2 + μ^2)) =
                     (μ / π : ℂ) * ∫ k : ℝ, Complex.exp (Complex.I * k * x) / (k^2 + μ^2) := by
    ring
  rw [h_rearrange] at hinv
  -- hinv : (μ/π) * ∫ ... = e^{-μ|x|}
  -- Divide both sides by (μ/π): ∫ ... = e^{-μ|x|} / (μ/π) = (π/μ) * e^{-μ|x|}
  have h_solve : ∫ k : ℝ, Complex.exp (Complex.I * k * x) / (k^2 + μ^2) =
                 (↑(Real.exp (-μ * |x|)) : ℂ) / (μ / π) := by
    rw [mul_comm] at hinv
    exact eq_div_of_mul_eq hμπ_ne hinv
  rw [h_solve]
  -- Simplify: e^{...} / (μ/π) = e^{...} * (π/μ) = (π/μ) * e^{...}
  rw [div_div_eq_mul_div]
  ring

end

/-- Negative phase variant: ∫ e^{-ikx} / (k² + μ²) dk = (π/μ) e^{-μ|x|}

    This follows from `fourier_lorentzian_1d` by the substitution k ↦ -k.
    Since (-k)² = k² and the integral over ℝ is symmetric, we get the same result. -/
theorem fourier_lorentzian_1d_neg (μ : ℝ) (hμ : 0 < μ) (x : ℝ) :
    ∫ k : ℝ, Complex.exp (-Complex.I * k * x) / (k^2 + μ^2) =
      (π / μ) * Real.exp (-μ * |x|) := by
  -- Use fourier_lorentzian_1d with (-x), then show exp(I * k * (-x)) = exp(-I * k * x)
  have h := fourier_lorentzian_1d μ hμ (-x)
  rw [abs_neg] at h
  -- Now h : ∫ k, exp(I * k * (-x)) / ... = (π/μ) * exp(-μ * |x|)
  -- We need: ∫ k, exp(-I * k * x) / ... = (π/μ) * exp(-μ * |x|)
  convert h using 2
  ext k
  congr 1
  -- Need: -I * k * x = I * k * (-x)
  simp only [Complex.ofReal_neg, neg_mul, mul_neg]

/-! ## Application to Free Field Propagator

The free field propagator in d Euclidean dimensions is:

  C(x) = ∫ dᵈk/(2π)ᵈ · e^{ik·x} / (k² + m²)

We can split this into time and spatial parts. After integrating over the
time component k₀, we get an exponential factor e^{-μ|x₀|} where
μ = √(|p̄|² + m²).
-/

/-! ## Proof Strategy: Fourier Inversion Approach

### Overview

The main result `fourier_lorentzian_1d` is derived via Fourier inversion:

1. **Half-line integrals** (FTC): Compute ∫₀^∞ e^{(ik-μ)x} dx and ∫_{-∞}^0 e^{(ik+μ)x} dx
   using the fundamental theorem of calculus for improper integrals.

2. **Fourier transform of e^{-μ|x|}**: Split into half-lines and sum:
   FT[e^{-μ|x|}](k) = 2μ/(k² + μ²)

3. **Fourier inversion**: Apply (1/2π) ∫ e^{ikx} · FT[f](k) dk = f(x) to get:
   (1/2π) ∫ e^{ikx} · 2μ/(k² + μ²) dk = e^{-μ|x|}

4. **Lorentzian result**: Rearrange to obtain:
   ∫ e^{ikx} / (k² + μ²) dk = (π/μ) e^{-μ|x|}

### Key Lemmas (in dependency order)

1. `tendsto_cexp_atTop_zero`, `tendsto_cexp_atBot_zero`: Limits at ±∞
2. `integrableOn_exp_decay_Ioi`, `integrableOn_exp_growth_Iic`: Integrability
3. `fourier_exp_decay_positive_halfline`, `fourier_exp_decay_negative_halfline`: Half-line integrals
4. `fourier_exponential_decay_split`: Sum to get 2μ/(k² + μ²)
5. `fourier_inversion_exp_decay`: Inversion gives e^{-μ|x|}
6. `fourier_lorentzian_1d`: Main result; `fourier_lorentzian_1d_neg` is its negative
   phase-convention variant (substitution k ↦ -k), the form the OS3 layer consumes.
-/
/-! ## Integrability Lemmas -/

