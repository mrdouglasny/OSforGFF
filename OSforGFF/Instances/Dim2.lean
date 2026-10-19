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
# The two-dimensional instance — proper-time evaluation

The radial profile of the free covariance in two dimensions is the modified Bessel profile
`K₀(mr)/(2π)`. This file evaluates the underlying proper-time integral in closed form: at `d = 2`
the heat-kernel prefactor is `(4πt)⁻¹`, so after pulling out the constant `(4π)⁻¹` the proper-time
integral is exactly the Schwinger integral
`∫₀^∞ (1/t) e^{-m²t - r²/(4t)} dt = 2 K₀(mr)` (`schwingerIntegral_eq_besselK0`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Real Set

namespace OSforGFF

/-- The two-dimensional proper-time covariance is the Bessel-`K₀` profile:
    `properTimeCovariance 2 m r = K₀(mr)/(2π)` for `m, r > 0`. -/
theorem properTimeCovariance_dim2_eq (m r : ℝ) (hm : 0 < m) (hr : 0 < r) :
    properTimeCovariance 2 m r = 1 / (2 * Real.pi) * besselK0 (m * r) := by
  -- Pull the constant `(4π)^{-1}` out; the remaining integral is `schwingerIntegral_eq_besselK0`.
  rw [properTimeCovariance_const_mul 2 m r]
  have hre : (∫ t in Ioi 0, t ^ (-((2 : ℕ) : ℝ) / 2) * Real.exp (-m ^ 2 * t - r ^ 2 / (4 * t)))
      = ∫ t in Ioi 0, (1 / t) * Real.exp (-m ^ 2 * t - r ^ 2 / (4 * t)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    rw [show (-((2 : ℕ) : ℝ) / 2) = (-1 : ℝ) by norm_num, Real.rpow_neg_one, one_div]
  rw [hre, schwingerIntegral_eq_besselK0 m r hm hr,
      show (-((2 : ℕ) : ℝ) / 2) = (-1 : ℝ) by norm_num, Real.rpow_neg_one]
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- `2 ≤ 2`, needed for the time/space split. -/
instance instFactTwoLeTwo : Fact ((2 : ℕ) ≤ 2) := ⟨le_refl 2⟩

/-- The two-dimensional free propagator: `Cprofile` is the Bessel closed form
    `K₀(mr)/(2π)` and the Schwinger bridge is `properTimeCovariance_dim2_eq`. -/
noncomputable instance instGFFPropagatorDim2 (m : ℝ) [Fact (0 < m)] :
    GFFPropagator 2 m where
  Cprofile r := if r = 0 then 0 else 1 / (2 * Real.pi) * besselK0 (m * r)
  schwinger_eq r hr := by
    rw [ite_eq_right (ne_of_gt hr), properTimeCovariance_dim2_eq m r Fact.out hr]

end OSforGFF
