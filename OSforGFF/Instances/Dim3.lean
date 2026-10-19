/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Copyright (c) 2026 Sergey A. Cherkis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sergey A. Cherkis, Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/
module

public import OSforGFF.General.BesselK
public import OSforGFF.Covariance.Propagator
public import OSforGFF.Measure.Construct

/-!
# The three-dimensional (Yukawa) instance — proper-time evaluation

The radial profile of the free covariance in three dimensions is the Yukawa potential
`e^{-mr}/(4πr)`. This file evaluates the underlying proper-time integral in closed form as the
order `ν = -1/2` case of the master Bessel identity `schwingerIntegral_eq_besselK`, using the
elementary half-integer value `besselK_half` (`K_{1/2}(z) = √(π/(2z)) e^{-z}`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Real Set

namespace OSforGFF

/-- The three-dimensional proper-time integral in closed form:
    `∫₀^∞ t^{-3/2} e^{-m²t - r²/(4t)} dt = (2√π/r) e^{-mr}` for `m, r > 0`. The order `ν = -1/2`
    instance of the master identity `schwingerIntegral_eq_besselK`, evaluated with `besselK_half`. -/
theorem schwingerIntegral_dim3 (m r : ℝ) (hm : 0 < m) (hr : 0 < r) :
    ∫ t in Ioi 0, t ^ (-(3 / 2 : ℝ)) * Real.exp (-m ^ 2 * t - r ^ 2 / (4 * t)) =
      2 * Real.sqrt Real.pi / r * Real.exp (-(m * r)) := by
  have hmr : 0 < m * r := mul_pos hm hr
  have h := schwingerIntegral_eq_besselK (-(1 / 2)) m r hm hr
  rw [besselK_neg, besselK_half (m * r),
      show (-(1 / 2) : ℝ) - 1 = -(3 / 2 : ℝ) by norm_num] at h
  have hsqrt : (r / (2 * m)) ^ (-(1 / 2) : ℝ) * Real.sqrt (Real.pi / (2 * (m * r))) =
      Real.sqrt Real.pi / r := by
    have h1 : (r / (2 * m)) ^ (-(1 / 2) : ℝ) = Real.sqrt (2 * m / r) := by
      rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, ← Real.sqrt_inv, inv_div]
    rw [h1, ← Real.sqrt_mul (by positivity),
        show 2 * m / r * (Real.pi / (2 * (m * r))) = Real.pi * (r ^ 2)⁻¹ by field_simp,
        Real.sqrt_mul Real.pi_pos.le, Real.sqrt_inv, Real.sqrt_sq hr.le, ← div_eq_mul_inv]
  rw [h, show (2 : ℝ) * (r / (2 * m)) ^ (-(1 / 2) : ℝ) *
        (Real.sqrt (Real.pi / (2 * (m * r))) * Real.exp (-(m * r)))
      = 2 * ((r / (2 * m)) ^ (-(1 / 2) : ℝ) * Real.sqrt (Real.pi / (2 * (m * r)))) *
          Real.exp (-(m * r)) by ring, hsqrt]
  ring

/-- The three-dimensional proper-time covariance is the Yukawa profile:
    `properTimeCovariance 3 m r = e^{-mr}/(4πr)` for `m, r > 0`. -/
theorem properTimeCovariance_dim3_eq (m r : ℝ) (hm : 0 < m) (hr : 0 < r) :
    properTimeCovariance 3 m r = Real.exp (-(m * r)) / (4 * Real.pi * r) := by
  -- Pull the constant `(4π)^{-3/2}` out; the remaining integral is `schwingerIntegral_dim3`.
  rw [properTimeCovariance_const_mul 3 m r,
      show (-((3 : ℕ) : ℝ) / 2) = -(3 / 2 : ℝ) by norm_num, schwingerIntegral_dim3 m r hm hr]
  -- `(4π)^{-3/2}·(2√π/r)·e^{-mr} = e^{-mr}/(4πr)`, since `(4π)^{-3/2}·2√π = 1/(4π)`.
  have hc : (4 * Real.pi) ^ (-(3 / 2 : ℝ)) * (2 * Real.sqrt Real.pi) = 1 / (4 * Real.pi) := by
    have hsp : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
    have h32 : (4 * Real.pi) ^ (-(3 / 2 : ℝ)) = 1 / (8 * Real.pi * Real.sqrt Real.pi) := by
      rw [Real.rpow_neg (by positivity)]
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by positivity), Real.rpow_one,
          ← Real.sqrt_eq_rpow, show (4 : ℝ) * Real.pi = 2 ^ 2 * Real.pi by ring,
          Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
      ring
    rw [h32]
    field_simp
    ring
  rw [show (4 * Real.pi) ^ (-(3 / 2 : ℝ)) * (2 * Real.sqrt Real.pi / r * Real.exp (-(m * r))) =
        (4 * Real.pi) ^ (-(3 / 2 : ℝ)) * (2 * Real.sqrt Real.pi) * (Real.exp (-(m * r)) / r) by ring,
      hc]
  ring

/-- `2 ≤ 3`, needed for the time/space split. -/
instance instFactTwoLeThree : Fact ((2 : ℕ) ≤ 3) := ⟨by norm_num⟩

/-- The three-dimensional free propagator: `Cprofile` is the Yukawa closed form
    `e^{-mr}/(4πr)` and the Schwinger bridge is `properTimeCovariance_dim3_eq`. -/
noncomputable instance instGFFPropagatorDim3 (m : ℝ) [Fact (0 < m)] :
    GFFPropagator 3 m where
  Cprofile r := if r = 0 then 0 else Real.exp (-(m * r)) / (4 * Real.pi * r)
  schwinger_eq r hr := by
    rw [ite_eq_right (ne_of_gt hr), properTimeCovariance_dim3_eq m r Fact.out hr]

end OSforGFF
