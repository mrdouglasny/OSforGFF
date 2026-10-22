/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Copyright (c) 2026 Sergey A. Cherkis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sergey A. Cherkis, Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/
module

public import OSforGFF.General.BesselK
public import OSforGFF.Instances.Dim2
public import OSforGFF.Covariance.Propagator
public import OSforGFF.Measure.Construct
public import Mathlib.MeasureTheory.Integral.Gamma

/-!
# The five-dimensional instance — proper-time evaluation

The radial profile of the free covariance in five dimensions is the `K_{3/2}` profile
`(1 + mr) e^{-mr}/(8π²r³)`. This file evaluates the underlying proper-time integral in closed form
as the order `ν = -3/2` case of the master Bessel identity `schwingerIntegral_eq_besselK`, using
the half-integer value `besselK_three_half` (`K_{3/2}(z) = √(π/(2z)) e^{-z} (1 + 1/z)`), obtained by
the substitution `u = sinh(t/2)` and the Gaussian zeroth and second moments.

The master theorem applies in every dimension `d ≥ 2`, in particular at `d = 5`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Real Topology intervalIntegral

namespace OSforGFF

/-- Gaussian second moment on the half-line: `∫₀^∞ u² e^{-b u²} du = √π / (4 b^{3/2})` (`b > 0`). -/
private lemma gaussian_moment2 (b : ℝ) (hb : 0 < b) :
    ∫ u in Ioi (0:ℝ), u ^ 2 * exp (-b * u ^ 2) = Real.sqrt π / (4 * b ^ (3/2 : ℝ)) := by
  have hshape : ∫ u in Ioi (0:ℝ), u ^ 2 * exp (-b * u ^ 2)
      = ∫ u in Ioi (0:ℝ), u ^ (2:ℝ) * exp (-b * u ^ (2:ℝ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
    have hu0 : (0:ℝ) < u := hu
    rw [Real.rpow_two]
  rw [hshape, integral_rpow_mul_exp_neg_mul_rpow (by norm_num) (by norm_num) hb]
  have hgamma : Real.Gamma ((2 + 1) / 2) = Real.sqrt π / 2 := by
    rw [show ((2:ℝ) + 1) / 2 = 1/2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
        Real.Gamma_one_half_eq]
    ring
  rw [hgamma, show (-(2 + 1) / 2 : ℝ) = -(3/2 : ℝ) by norm_num, Real.rpow_neg hb.le]
  rw [div_eq_mul_inv, mul_comm]
  field_simp
  ring

/-- The half-integer Bessel value of order `3/2`: `K_{3/2}(z) = √(π/(2z)) e^{-z} (1 + 1/z)` for
    `z > 0` (via `cosh(3t/2) = cosh(t/2)(1 + 4 sinh²(t/2))`, the substitution `u = sinh(t/2)`, and the
    Gaussian zeroth and second moments). -/
lemma besselK_three_half (z : ℝ) (hz : 0 < z) :
    besselK (3/2) z = Real.sqrt (Real.pi / (2 * z)) * exp (-z) * (1 + 1/z) := by
  have hb : (0:ℝ) < 2 * z := by linarith
  have hint : besselK (3/2) z =
      exp (-z) * ∫ t in Ici 0, exp (-(2*z) * sinh (t/2)^2) * (cosh (t/2) * (1 + 4 * sinh (t/2)^2)) := by
    unfold besselK
    rw [← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ici (fun t _ => ?_)
    have hcosh : cosh t = 1 + 2 * sinh (t/2)^2 := by
      rw [show t = 2*(t/2) from by ring, Real.cosh_two_mul, Real.cosh_sq']; ring
    have hc32 : cosh ((3/2) * t) = cosh (t/2) * (1 + 4 * sinh (t/2)^2) := by
      have h3 : cosh ((3/2) * t) = 4 * cosh (t/2)^3 - 3 * cosh (t/2) := by
        rw [show (3/2:ℝ) * t = 3 * (t/2) by ring, Real.cosh_three_mul]
      rw [h3, show cosh (t/2)^3 = cosh (t/2) * cosh (t/2)^2 by ring, Real.cosh_sq']; ring
    rw [hc32, hcosh,
        show -z * (1 + 2 * sinh (t/2)^2) = -z + -(2*z) * sinh (t/2)^2 by ring, Real.exp_add]
    ring
  have hcov : ∫ t in Ici 0, exp (-(2*z) * sinh (t/2)^2) * (cosh (t/2) * (1 + 4 * sinh (t/2)^2)) =
      2 * ∫ u in Ici 0, exp (-(2*z) * u^2) * (1 + 4 * u^2) := by
    have hderiv : ∀ t ∈ Ici (0:ℝ),
        HasDerivWithinAt (fun t => sinh (t/2)) (cosh (t/2) / 2) (Ici 0) t := by
      intro t _
      have h1 : HasDerivAt (fun t : ℝ => t/2) (1/2) t := (hasDerivAt_id t).div_const 2
      have h2 : HasDerivAt (fun t : ℝ => sinh (t/2)) (cosh (t/2) * (1/2)) t := by
        simpa [Function.comp_def] using (Real.hasDerivAt_sinh (t/2)).comp t h1
      rw [show cosh (t/2) / 2 = cosh (t/2) * (1/2) by ring]
      exact h2.hasDerivWithinAt
    have hmono : MonotoneOn (fun t => sinh (t/2)) (Ici 0) :=
      fun a _ b _ hab => Real.sinh_le_sinh.mpr (by linarith)
    have himg : (fun t => sinh (t/2)) '' Ici 0 = Ici 0 := by
      ext y; simp only [mem_image, mem_Ici]
      constructor
      · rintro ⟨t, ht, rfl⟩; exact Real.sinh_nonneg_iff.mpr (by linarith)
      · intro hy
        refine ⟨2 * Real.arsinh y, ?_, ?_⟩
        · have : 0 ≤ Real.arsinh y := Real.arsinh_nonneg_iff.mpr hy
          linarith
        · rw [show 2 * Real.arsinh y / 2 = Real.arsinh y by ring, Real.sinh_arsinh]
    have h := integral_image_eq_integral_deriv_smul_of_monotoneOn (F := ℝ)
      measurableSet_Ici hderiv hmono (fun u => exp (-(2*z) * u^2) * (1 + 4 * u^2))
    rw [himg] at h
    rw [h, ← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ici (fun t _ => ?_)
    simp only [smul_eq_mul]; ring
  have hsplit : ∫ u in Ici 0, exp (-(2*z) * u^2) * (1 + 4 * u^2) =
      Real.sqrt (π / (2*z)) / 2 + 4 * (Real.sqrt π / (4 * (2*z) ^ (3/2:ℝ))) := by
    rw [integral_Ici_eq_integral_Ioi]
    have hIntG : IntegrableOn (fun u => exp (-(2*z) * u^2)) (Ioi 0) :=
      (integrable_exp_neg_mul_sq hb).integrableOn
    have hIntM : IntegrableOn (fun u => u^2 * exp (-(2*z) * u^2)) (Ioi 0) := by
      refine (integrableOn_rpow_mul_exp_neg_mul_rpow (s := 2) (p := 2) (b := 2*z)
        (by norm_num) (by norm_num) hb).congr_fun (fun u hu => ?_) measurableSet_Ioi
      have hu0 : (0:ℝ) < u := hu
      simp only [Real.rpow_two]
    rw [show (fun u => exp (-(2*z) * u^2) * (1 + 4 * u^2))
          = (fun u => exp (-(2*z) * u^2) + 4 * (u^2 * exp (-(2*z) * u^2))) from by funext u; ring,
        MeasureTheory.integral_add hIntG (hIntM.const_mul 4), MeasureTheory.integral_const_mul,
        integral_gaussian_Ioi, gaussian_moment2 (2*z) hb]
  rw [hint, hcov, hsplit]
  have h32 : (2*z) ^ (3/2:ℝ) = (2*z) * Real.sqrt (2*z) := by
    rw [show (3/2:ℝ) = 1 + 1/2 by norm_num, Real.rpow_add hb, Real.rpow_one, ← Real.sqrt_eq_rpow]
  have hsd : Real.sqrt (π / (2*z)) = Real.sqrt π / Real.sqrt (2*z) := Real.sqrt_div' π hb.le
  rw [h32, hsd]
  field_simp

/-- The five-dimensional proper-time covariance is the `K_{3/2}` profile:
    `properTimeCovariance 5 m r = (1 + mr) e^{-mr}/(8π²r³)` for `m, r > 0`. -/
theorem properTimeCovariance_dim5_eq (m r : ℝ) (hm : 0 < m) (hr : 0 < r) :
    properTimeCovariance 5 m r = (1 + m * r) * exp (-(m * r)) / (8 * π ^ 2 * r ^ 3) := by
  have hmr : 0 < m * r := mul_pos hm hr
  rw [properTimeCovariance_const_mul 5 m r]
  have h := schwingerIntegral_eq_besselK (-(3/2)) m r hm hr
  rw [besselK_neg, besselK_three_half (m * r) hmr,
      show (-(3/2):ℝ) - 1 = -(5/2:ℝ) by norm_num] at h
  have hrm : (r / (2*m)) ^ (-(3/2):ℝ) * Real.sqrt (π / (2*(m*r))) = 2*m*Real.sqrt π / r^2 := by
    have h1 : (r / (2*m)) ^ (-(3/2):ℝ) = (2*m/r) * Real.sqrt (2*m/r) := by
      rw [show (-(3/2):ℝ) = (-1) + (-(1/2)) by norm_num, Real.rpow_add (by positivity),
          Real.rpow_neg_one, inv_div,
          show (r / (2*m)) ^ (-(1/2):ℝ) = Real.sqrt (2*m/r) by
            rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, ← Real.sqrt_inv, inv_div]]
    rw [h1, mul_assoc, ← Real.sqrt_mul (by positivity),
        show 2*m/r * (π/(2*(m*r))) = π * (r^2)⁻¹ by field_simp,
        Real.sqrt_mul Real.pi_pos.le, Real.sqrt_inv, Real.sqrt_sq hr.le]
    field_simp
  have h4pi : (4*π) ^ (-(5/2):ℝ) = 1 / (32 * π^2 * Real.sqrt π) := by
    rw [Real.rpow_neg (by positivity), show (5/2:ℝ) = 2 + 1/2 by norm_num,
        Real.rpow_add (by positivity), Real.rpow_two, ← Real.sqrt_eq_rpow,
        show Real.sqrt (4*π) = 2*Real.sqrt π by
          rw [show (4:ℝ)*π = 2^2*π by ring, Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]]
    rw [show (4*π)^2 * (2*Real.sqrt π) = 32 * π^2 * Real.sqrt π by ring, one_div]
  rw [show (-((5:ℕ):ℝ)/2) = -(5/2:ℝ) by norm_num, h,
      show (4*π)^(-(5/2):ℝ) * (2 * (r/(2*m))^(-(3/2):ℝ) *
          (Real.sqrt (π/(2*(m*r))) * exp (-(m*r)) * (1 + 1/(m*r))))
        = (4*π)^(-(5/2):ℝ) * 2 * ((r/(2*m))^(-(3/2):ℝ) * Real.sqrt (π/(2*(m*r)))) *
          (exp (-(m*r)) * (1 + 1/(m*r))) by ring,
      hrm, h4pi]
  have hsp : Real.sqrt π ≠ 0 := Real.sqrt_ne_zero'.mpr Real.pi_pos
  have hmr' : m * r ≠ 0 := ne_of_gt hmr
  field_simp
  ring

/-- `2 ≤ 5`, needed for the time/space split. -/
instance instFactTwoLeFive : Fact ((2 : ℕ) ≤ 5) := ⟨by norm_num⟩

/-- The five-dimensional free propagator: `Cprofile` is the `K_{3/2}` closed form
    `(1 + mr) e^{-mr}/(8π²r³)` and the Schwinger bridge is `properTimeCovariance_dim5_eq`. -/
noncomputable instance instGFFPropagatorDim5 (m : ℝ) [Fact (0 < m)] :
    GFFPropagator 5 m where
  Cprofile r := if r = 0 then 0 else (1 + m * r) * Real.exp (-(m * r)) / (8 * Real.pi ^ 2 * r ^ 3)
  schwinger_eq r hr := by
    rw [ite_eq_right (ne_of_gt hr), properTimeCovariance_dim5_eq m r Fact.out hr]

end OSforGFF
