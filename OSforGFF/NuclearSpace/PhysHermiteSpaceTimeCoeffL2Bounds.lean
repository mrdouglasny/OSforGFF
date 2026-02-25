/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import OSforGFF.NuclearSpace.PhysHermiteSpaceTimeHilbertBasis
import OSforGFF.NuclearSpace.PhysHermiteSpaceTimeCoeffRapidDecay

/-!
# `L²`-bounds for basic harmonic-oscillator operators on spacetime Schwartz functions

This file develops `L²` (Hilbert) bounds for the coordinate ladder operators
`raiseOpCLM` / `lowerOpCLM` and for coordinate multiplication/derivative operators.

These are the analytic inputs needed to compare Schwartz seminorms with the
coefficient/graph-norm seminorms coming from the spacetime harmonic oscillator.
-/

open scoped BigOperators NNReal ENNReal RealInnerProductSpace

namespace PhysLean

noncomputable section

open MeasureTheory

namespace SpaceTimeHermite

local notation "SpaceTimeL2" => (SpaceTime →₂[(volume : Measure SpaceTime)] ℝ)

/-! ## Normalization constants under raising/lowering -/

private lemma normConstSpaceTime_raise (ξ : ℝ) (i : Fin STDimension) (n : ℕ) :
    normConstSpaceTime ξ (raise i n) =
      ((2 : ℝ) * ((((idx n i : ℕ) + 1 : ℕ) : ℝ))) * normConstSpaceTime ξ n := by
  fin_cases i <;>
    simp [normConstSpaceTime, Fin.prod_univ_four, raise, idx, pow_succ, Nat.factorial_succ] <;> ring

/-! ## Normalized coefficient action of ladder operators -/

private lemma coeffCLM_SpaceTime_eq_sqrt_normConstSpaceTime_mul_normalizedCoeffCLM_SpaceTime
    (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) (f : TestFunction) :
    coeffCLM_SpaceTime ξ hξ n f =
      Real.sqrt (normConstSpaceTime ξ n) * normalizedCoeffCLM_SpaceTime ξ hξ n f := by
  have hsqrt_ne :
      Real.sqrt (normConstSpaceTime ξ n) ≠ 0 := by
    have hpos : 0 < normConstSpaceTime ξ n := normConstSpaceTime_pos (ξ := ξ) hξ n
    exact (Real.sqrt_ne_zero').2 hpos
  calc
    coeffCLM_SpaceTime ξ hξ n f
        = (Real.sqrt (normConstSpaceTime ξ n)) *
            ((Real.sqrt (normConstSpaceTime ξ n))⁻¹ * coeffCLM_SpaceTime ξ hξ n f) := by
            simp [mul_assoc, hsqrt_ne, -coeffCLM_SpaceTime_apply, -normConstSpaceTime_def]
    _ = Real.sqrt (normConstSpaceTime ξ n) * normalizedCoeffCLM_SpaceTime ξ hξ n f := by
            simp [normalizedCoeffCLM_SpaceTime_apply, smul_eq_mul, mul_assoc,
              -coeffCLM_SpaceTime_apply, -normConstSpaceTime_def]

private lemma sqrt_normConstSpaceTime_raise (ξ : ℝ) (i : Fin STDimension) (n : ℕ) :
    Real.sqrt (normConstSpaceTime ξ (raise i n)) =
      Real.sqrt (((2 : ℝ) * ((((idx n i : ℕ) + 1 : ℕ) : ℝ)))) *
        Real.sqrt (normConstSpaceTime ξ n) := by
  have hA : 0 ≤ ((2 : ℝ) * ((((idx n i : ℕ) + 1 : ℕ) : ℝ))) := by positivity
  rw [normConstSpaceTime_raise (ξ := ξ) (i := i) (n := n)]
  simpa [mul_assoc] using (Real.sqrt_mul hA (normConstSpaceTime ξ n))

private lemma two_mul_inv_sqrt_two :
    (2 : ℝ) * (Real.sqrt (2 : ℝ))⁻¹ = Real.sqrt (2 : ℝ) := by
  have hsqrt2_ne : Real.sqrt (2 : ℝ) ≠ 0 := by
    simpa using (Real.sqrt_ne_zero').2 (by norm_num : (0 : ℝ) < 2)
  have hdiv : (2 : ℝ) / Real.sqrt (2 : ℝ) = Real.sqrt (2 : ℝ) := by
    field_simp [hsqrt2_ne]
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (Real.mul_self_sqrt (by positivity : (0 : ℝ) ≤ (2 : ℝ))).symm
  simpa [div_eq_mul_inv] using hdiv

private lemma mul_inv_sqrt_eq_sqrt (a : ℝ) (ha : 0 < a) :
    a * (Real.sqrt a)⁻¹ = Real.sqrt a := by
  have ha0 : 0 ≤ a := le_of_lt ha
  have hsqrt_a_ne : Real.sqrt a ≠ 0 := (Real.sqrt_ne_zero').2 ha
  have hdiv : a / Real.sqrt a = Real.sqrt a := by
    field_simp [hsqrt_a_ne]
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using (Real.mul_self_sqrt ha0).symm
  simpa [div_eq_mul_inv] using hdiv

lemma normalizedCoeffCLM_SpaceTime_lowerOpCLM (ξ : ℝ) (hξ : ξ ≠ 0) (i : Fin STDimension)
    (n : ℕ) (f : TestFunction) :
    normalizedCoeffCLM_SpaceTime ξ hξ n (lowerOpCLM ξ i f) =
      Real.sqrt (((2 : ℝ) * ((((idx n i : ℕ) + 1 : ℕ) : ℝ)))) *
        normalizedCoeffCLM_SpaceTime ξ hξ (raise i n) f := by
  simp [normalizedCoeffCLM_SpaceTime_apply, -coeffCLM_SpaceTime_apply, -lowerOpCLM_apply,
    -normConstSpaceTime_def]
  rw [coeffCLM_SpaceTime_lowerOpCLM (ξ := ξ) (hξ := hξ) (i := i) (n := n) (f := f)]
  rw [coeffCLM_SpaceTime_eq_sqrt_normConstSpaceTime_mul_normalizedCoeffCLM_SpaceTime
    (ξ := ξ) (hξ := hξ) (n := raise i n) (f := f)]
  rw [sqrt_normConstSpaceTime_raise (ξ := ξ) (i := i) (n := n)]
  have hsqrt_ne :
      Real.sqrt (normConstSpaceTime ξ n) ≠ 0 := by
    have hpos : 0 < normConstSpaceTime ξ n := normConstSpaceTime_pos (ξ := ξ) hξ n
    exact (Real.sqrt_ne_zero').2 hpos
  have hsqrt_idx_ne : Real.sqrt ((↑(idx n i) : ℝ) + 1) ≠ 0 := by
    have : 0 < (↑(idx n i) : ℝ) + 1 := by positivity
    exact (Real.sqrt_ne_zero').2 this
  simp [mul_assoc, mul_left_comm, mul_comm, hsqrt_ne, hsqrt_idx_ne,
    -normConstSpaceTime_def, -coeffCLM_SpaceTime_apply, -normalizedCoeffCLM_SpaceTime_apply]

lemma normalizedCoeffCLM_SpaceTime_raiseOpCLM_raise (ξ : ℝ) (hξ : ξ ≠ 0) (i : Fin STDimension)
    (n : ℕ) (f : TestFunction) :
    normalizedCoeffCLM_SpaceTime ξ hξ (raise i n) (raiseOpCLM ξ i f) =
      Real.sqrt (((2 : ℝ) * ((((idx n i : ℕ) + 1 : ℕ) : ℝ)))) *
        normalizedCoeffCLM_SpaceTime ξ hξ n f := by
  simp [normalizedCoeffCLM_SpaceTime_apply, -coeffCLM_SpaceTime_apply, -raiseOpCLM_apply,
    -normConstSpaceTime_def]
  rw [coeffCLM_SpaceTime_raiseOpCLM (ξ := ξ) (hξ := hξ) (i := i)
    (n := raise i n) (f := f)]
  simp [idx_raise_self, lower_raise, -coeffCLM_SpaceTime_apply, -normConstSpaceTime_def,
    mul_assoc, mul_left_comm, mul_comm]
  rw [coeffCLM_SpaceTime_eq_sqrt_normConstSpaceTime_mul_normalizedCoeffCLM_SpaceTime
    (ξ := ξ) (hξ := hξ) (n := n) (f := f)]
  rw [sqrt_normConstSpaceTime_raise (ξ := ξ) (i := i) (n := n)]
  have hsqrt_ne :
      Real.sqrt (normConstSpaceTime ξ n) ≠ 0 := by
    have hpos : 0 < normConstSpaceTime ξ n := normConstSpaceTime_pos (ξ := ξ) hξ n
    exact (Real.sqrt_ne_zero').2 hpos
  have htpos : 0 < ((2 : ℝ) * ((((idx n i : ℕ) + 1 : ℕ) : ℝ))) := by positivity
  have hsqrt_t_ne : Real.sqrt (((2 : ℝ) * ((((idx n i : ℕ) + 1 : ℕ) : ℝ)))) ≠ 0 :=
    (Real.sqrt_ne_zero').2 htpos
  simp [mul_assoc, mul_left_comm, mul_comm, hsqrt_ne, hsqrt_t_ne,
    -normConstSpaceTime_def, -coeffCLM_SpaceTime_apply, -normalizedCoeffCLM_SpaceTime_apply]
  set a : ℝ := ((↑(idx n i) : ℝ) + 1)
  set c : ℝ := (normalizedCoeffCLM_SpaceTime ξ hξ n) f
  have ha_pos : 0 < a := by positivity
  calc
    2 * ((Real.sqrt (2 : ℝ))⁻¹ * (a * ((Real.sqrt a)⁻¹ * c)))
        = ((2 : ℝ) * (Real.sqrt (2 : ℝ))⁻¹) * (a * ((Real.sqrt a)⁻¹ * c)) := by
            simp [mul_assoc]
    _ = Real.sqrt (2 : ℝ) * (a * ((Real.sqrt a)⁻¹ * c)) := by
            simp [two_mul_inv_sqrt_two]
    _ = Real.sqrt (2 : ℝ) * ((a * (Real.sqrt a)⁻¹) * c) := by
            simp [mul_assoc]
    _ = Real.sqrt (2 : ℝ) * (Real.sqrt a * c) := by
            simp [mul_inv_sqrt_eq_sqrt (a := a) ha_pos]

end SpaceTimeHermite

end

end PhysLean
