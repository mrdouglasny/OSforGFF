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

private lemma normConstSpaceTime_raise₀ (ξ : ℝ) (n : ℕ) :
    normConstSpaceTime ξ (raise₀ n) =
      ((2 : ℝ) * ((unpair₄₁ n + 1 : ℕ) : ℝ)) * normConstSpaceTime ξ n := by
  simp [normConstSpaceTime, Fin.prod_univ_four, pow_succ, Nat.factorial_succ]
  ring

private lemma normConstSpaceTime_raise₁ (ξ : ℝ) (n : ℕ) :
    normConstSpaceTime ξ (raise₁ n) =
      ((2 : ℝ) * ((unpair₄₂ n + 1 : ℕ) : ℝ)) * normConstSpaceTime ξ n := by
  simp [normConstSpaceTime, Fin.prod_univ_four, pow_succ, Nat.factorial_succ]
  ring

private lemma normConstSpaceTime_raise₂ (ξ : ℝ) (n : ℕ) :
    normConstSpaceTime ξ (raise₂ n) =
      ((2 : ℝ) * ((unpair₄₃ n + 1 : ℕ) : ℝ)) * normConstSpaceTime ξ n := by
  simp [normConstSpaceTime, Fin.prod_univ_four, pow_succ, Nat.factorial_succ]
  ring

private lemma normConstSpaceTime_raise₃ (ξ : ℝ) (n : ℕ) :
    normConstSpaceTime ξ (raise₃ n) =
      ((2 : ℝ) * ((unpair₄₄ n + 1 : ℕ) : ℝ)) * normConstSpaceTime ξ n := by
  simp [normConstSpaceTime, Fin.prod_univ_four, pow_succ, Nat.factorial_succ]
  ring

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

private lemma sqrt_normConstSpaceTime_raise₀ (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) :
    Real.sqrt (normConstSpaceTime ξ (raise₀ n)) =
      Real.sqrt (((2 : ℝ) * ((unpair₄₁ n + 1 : ℕ) : ℝ))) * Real.sqrt (normConstSpaceTime ξ n) := by
  have hA : 0 ≤ ((2 : ℝ) * ((unpair₄₁ n + 1 : ℕ) : ℝ)) := by positivity
  rw [normConstSpaceTime_raise₀ (ξ := ξ) (n := n)]
  simpa [mul_assoc] using (Real.sqrt_mul hA (normConstSpaceTime ξ n))

private lemma sqrt_normConstSpaceTime_raise₁ (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) :
    Real.sqrt (normConstSpaceTime ξ (raise₁ n)) =
      Real.sqrt (((2 : ℝ) * ((unpair₄₂ n + 1 : ℕ) : ℝ))) * Real.sqrt (normConstSpaceTime ξ n) := by
  have hA : 0 ≤ ((2 : ℝ) * ((unpair₄₂ n + 1 : ℕ) : ℝ)) := by positivity
  rw [normConstSpaceTime_raise₁ (ξ := ξ) (n := n)]
  simpa [mul_assoc] using (Real.sqrt_mul hA (normConstSpaceTime ξ n))

private lemma sqrt_normConstSpaceTime_raise₂ (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) :
    Real.sqrt (normConstSpaceTime ξ (raise₂ n)) =
      Real.sqrt (((2 : ℝ) * ((unpair₄₃ n + 1 : ℕ) : ℝ))) * Real.sqrt (normConstSpaceTime ξ n) := by
  have hA : 0 ≤ ((2 : ℝ) * ((unpair₄₃ n + 1 : ℕ) : ℝ)) := by positivity
  rw [normConstSpaceTime_raise₂ (ξ := ξ) (n := n)]
  simpa [mul_assoc] using (Real.sqrt_mul hA (normConstSpaceTime ξ n))

private lemma sqrt_normConstSpaceTime_raise₃ (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) :
    Real.sqrt (normConstSpaceTime ξ (raise₃ n)) =
      Real.sqrt (((2 : ℝ) * ((unpair₄₄ n + 1 : ℕ) : ℝ))) * Real.sqrt (normConstSpaceTime ξ n) := by
  have hA : 0 ≤ ((2 : ℝ) * ((unpair₄₄ n + 1 : ℕ) : ℝ)) := by positivity
  rw [normConstSpaceTime_raise₃ (ξ := ξ) (n := n)]
  simpa [mul_assoc] using (Real.sqrt_mul hA (normConstSpaceTime ξ n))

lemma normalizedCoeffCLM_SpaceTime_lowerOpCLM0 (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ)
    (f : TestFunction) :
    normalizedCoeffCLM_SpaceTime ξ hξ n (lowerOpCLM ξ (0 : Fin STDimension) f) =
      Real.sqrt (((2 : ℝ) * ((unpair₄₁ n + 1 : ℕ) : ℝ))) *
        normalizedCoeffCLM_SpaceTime ξ hξ (raise₀ n) f := by
  simp [normalizedCoeffCLM_SpaceTime_apply, -coeffCLM_SpaceTime_apply, -lowerOpCLM_apply,
    -normConstSpaceTime_def]
  have hLower0 :
      coeffCLM_SpaceTime ξ hξ n (lowerOpCLM ξ (0 : Fin STDimension) f) =
        coeffCLM_SpaceTime ξ hξ (raise₀ n) f := by
    simpa [raise, lower, idx] using
      (coeffCLM_SpaceTime_lowerOpCLM (ξ := ξ) (hξ := hξ) (i := (0 : Fin STDimension)) (n := n) (f := f))
  rw [hLower0]
  rw [coeffCLM_SpaceTime_eq_sqrt_normConstSpaceTime_mul_normalizedCoeffCLM_SpaceTime
    (ξ := ξ) (hξ := hξ) (n := raise₀ n) (f := f)]
  rw [sqrt_normConstSpaceTime_raise₀ (ξ := ξ) (hξ := hξ) (n := n)]
  have hsqrt_ne :
      Real.sqrt (normConstSpaceTime ξ n) ≠ 0 := by
    have hpos : 0 < normConstSpaceTime ξ n := normConstSpaceTime_pos (ξ := ξ) hξ n
    exact (Real.sqrt_ne_zero').2 hpos
  have hsqrt_unpair_ne : Real.sqrt ((↑(unpair₄₁ n) : ℝ) + 1) ≠ 0 := by
    have : 0 < (↑(unpair₄₁ n) : ℝ) + 1 := by positivity
    exact (Real.sqrt_ne_zero').2 this
  simp [mul_assoc, mul_left_comm, mul_comm, hsqrt_ne, hsqrt_unpair_ne,
    -normConstSpaceTime_def, -coeffCLM_SpaceTime_apply, -normalizedCoeffCLM_SpaceTime_apply]

lemma normalizedCoeffCLM_SpaceTime_lowerOpCLM1 (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ)
    (f : TestFunction) :
    normalizedCoeffCLM_SpaceTime ξ hξ n (lowerOpCLM ξ (1 : Fin STDimension) f) =
      Real.sqrt (((2 : ℝ) * ((unpair₄₂ n + 1 : ℕ) : ℝ))) *
        normalizedCoeffCLM_SpaceTime ξ hξ (raise₁ n) f := by
  simp [normalizedCoeffCLM_SpaceTime_apply, -coeffCLM_SpaceTime_apply, -lowerOpCLM_apply,
    -normConstSpaceTime_def]
  have hLower1 :
      coeffCLM_SpaceTime ξ hξ n (lowerOpCLM ξ (1 : Fin STDimension) f) =
        coeffCLM_SpaceTime ξ hξ (raise₁ n) f := by
    simpa [raise, lower, idx] using
      (coeffCLM_SpaceTime_lowerOpCLM (ξ := ξ) (hξ := hξ) (i := (1 : Fin STDimension)) (n := n) (f := f))
  rw [hLower1]
  rw [coeffCLM_SpaceTime_eq_sqrt_normConstSpaceTime_mul_normalizedCoeffCLM_SpaceTime
    (ξ := ξ) (hξ := hξ) (n := raise₁ n) (f := f)]
  rw [sqrt_normConstSpaceTime_raise₁ (ξ := ξ) (hξ := hξ) (n := n)]
  have hsqrt_ne :
      Real.sqrt (normConstSpaceTime ξ n) ≠ 0 := by
    have hpos : 0 < normConstSpaceTime ξ n := normConstSpaceTime_pos (ξ := ξ) hξ n
    exact (Real.sqrt_ne_zero').2 hpos
  have hsqrt_unpair_ne : Real.sqrt ((↑(unpair₄₂ n) : ℝ) + 1) ≠ 0 := by
    have : 0 < (↑(unpair₄₂ n) : ℝ) + 1 := by positivity
    exact (Real.sqrt_ne_zero').2 this
  simp [mul_assoc, mul_left_comm, mul_comm, hsqrt_ne, hsqrt_unpair_ne,
    -normConstSpaceTime_def, -coeffCLM_SpaceTime_apply, -normalizedCoeffCLM_SpaceTime_apply]

lemma normalizedCoeffCLM_SpaceTime_lowerOpCLM2 (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ)
    (f : TestFunction) :
    normalizedCoeffCLM_SpaceTime ξ hξ n (lowerOpCLM ξ (2 : Fin STDimension) f) =
      Real.sqrt (((2 : ℝ) * ((unpair₄₃ n + 1 : ℕ) : ℝ))) *
        normalizedCoeffCLM_SpaceTime ξ hξ (raise₂ n) f := by
  simp [normalizedCoeffCLM_SpaceTime_apply, -coeffCLM_SpaceTime_apply, -lowerOpCLM_apply,
    -normConstSpaceTime_def]
  have hLower2 :
      coeffCLM_SpaceTime ξ hξ n (lowerOpCLM ξ (2 : Fin STDimension) f) =
        coeffCLM_SpaceTime ξ hξ (raise₂ n) f := by
    simpa [raise, lower, idx] using
      (coeffCLM_SpaceTime_lowerOpCLM (ξ := ξ) (hξ := hξ) (i := (2 : Fin STDimension)) (n := n) (f := f))
  rw [hLower2]
  rw [coeffCLM_SpaceTime_eq_sqrt_normConstSpaceTime_mul_normalizedCoeffCLM_SpaceTime
    (ξ := ξ) (hξ := hξ) (n := raise₂ n) (f := f)]
  rw [sqrt_normConstSpaceTime_raise₂ (ξ := ξ) (hξ := hξ) (n := n)]
  have hsqrt_ne :
      Real.sqrt (normConstSpaceTime ξ n) ≠ 0 := by
    have hpos : 0 < normConstSpaceTime ξ n := normConstSpaceTime_pos (ξ := ξ) hξ n
    exact (Real.sqrt_ne_zero').2 hpos
  have hsqrt_unpair_ne : Real.sqrt ((↑(unpair₄₃ n) : ℝ) + 1) ≠ 0 := by
    have : 0 < (↑(unpair₄₃ n) : ℝ) + 1 := by positivity
    exact (Real.sqrt_ne_zero').2 this
  simp [mul_assoc, mul_left_comm, mul_comm, hsqrt_ne, hsqrt_unpair_ne,
    -normConstSpaceTime_def, -coeffCLM_SpaceTime_apply, -normalizedCoeffCLM_SpaceTime_apply]

lemma normalizedCoeffCLM_SpaceTime_lowerOpCLM3 (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ)
    (f : TestFunction) :
    normalizedCoeffCLM_SpaceTime ξ hξ n (lowerOpCLM ξ (3 : Fin STDimension) f) =
      Real.sqrt (((2 : ℝ) * ((unpair₄₄ n + 1 : ℕ) : ℝ))) *
        normalizedCoeffCLM_SpaceTime ξ hξ (raise₃ n) f := by
  simp [normalizedCoeffCLM_SpaceTime_apply, -coeffCLM_SpaceTime_apply, -lowerOpCLM_apply,
    -normConstSpaceTime_def]
  have hLower3 :
      coeffCLM_SpaceTime ξ hξ n (lowerOpCLM ξ (3 : Fin STDimension) f) =
        coeffCLM_SpaceTime ξ hξ (raise₃ n) f := by
    simpa [raise, lower, idx] using
      (coeffCLM_SpaceTime_lowerOpCLM (ξ := ξ) (hξ := hξ) (i := (3 : Fin STDimension)) (n := n) (f := f))
  rw [hLower3]
  rw [coeffCLM_SpaceTime_eq_sqrt_normConstSpaceTime_mul_normalizedCoeffCLM_SpaceTime
    (ξ := ξ) (hξ := hξ) (n := raise₃ n) (f := f)]
  rw [sqrt_normConstSpaceTime_raise₃ (ξ := ξ) (hξ := hξ) (n := n)]
  have hsqrt_ne :
      Real.sqrt (normConstSpaceTime ξ n) ≠ 0 := by
    have hpos : 0 < normConstSpaceTime ξ n := normConstSpaceTime_pos (ξ := ξ) hξ n
    exact (Real.sqrt_ne_zero').2 hpos
  have hsqrt_unpair_ne : Real.sqrt ((↑(unpair₄₄ n) : ℝ) + 1) ≠ 0 := by
    have : 0 < (↑(unpair₄₄ n) : ℝ) + 1 := by positivity
    exact (Real.sqrt_ne_zero').2 this
  simp [mul_assoc, mul_left_comm, mul_comm, hsqrt_ne, hsqrt_unpair_ne,
    -normConstSpaceTime_def, -coeffCLM_SpaceTime_apply, -normalizedCoeffCLM_SpaceTime_apply]

lemma normalizedCoeffCLM_SpaceTime_raiseOpCLM0_raise₀ (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ)
    (f : TestFunction) :
    normalizedCoeffCLM_SpaceTime ξ hξ (raise₀ n) (raiseOpCLM ξ (0 : Fin STDimension) f) =
      Real.sqrt (((2 : ℝ) * ((unpair₄₁ n + 1 : ℕ) : ℝ))) *
        normalizedCoeffCLM_SpaceTime ξ hξ n f := by
  simp [normalizedCoeffCLM_SpaceTime_apply, -coeffCLM_SpaceTime_apply, -raiseOpCLM_apply,
    -normConstSpaceTime_def]
  rw [coeffCLM_SpaceTime_raiseOpCLM (ξ := ξ) (hξ := hξ) (i := (0 : Fin STDimension))
    (n := raise₀ n) (f := f)]
  simp [unpair₄₁_raise₀, lower₀_raise₀, -coeffCLM_SpaceTime_apply, -normConstSpaceTime_def,
    mul_assoc, mul_left_comm, mul_comm]
  rw [coeffCLM_SpaceTime_eq_sqrt_normConstSpaceTime_mul_normalizedCoeffCLM_SpaceTime
    (ξ := ξ) (hξ := hξ) (n := n) (f := f)]
  rw [sqrt_normConstSpaceTime_raise₀ (ξ := ξ) (hξ := hξ) (n := n)]
  have hsqrt_ne :
      Real.sqrt (normConstSpaceTime ξ n) ≠ 0 := by
    have hpos : 0 < normConstSpaceTime ξ n := normConstSpaceTime_pos (ξ := ξ) hξ n
    exact (Real.sqrt_ne_zero').2 hpos
  have htpos : 0 < ((2 : ℝ) * ((unpair₄₁ n + 1 : ℕ) : ℝ)) := by positivity
  have hsqrt_t_ne : Real.sqrt (((2 : ℝ) * ((unpair₄₁ n + 1 : ℕ) : ℝ))) ≠ 0 :=
    (Real.sqrt_ne_zero').2 htpos
  simp [mul_assoc, mul_left_comm, mul_comm, hsqrt_ne, hsqrt_t_ne,
    -normConstSpaceTime_def, -coeffCLM_SpaceTime_apply, -normalizedCoeffCLM_SpaceTime_apply]
  set a : ℝ := (↑(unpair₄₁ n) + 1)
  set c : ℝ := (normalizedCoeffCLM_SpaceTime ξ hξ n) f
  have ha_pos : 0 < a := by positivity
  have hsqrt_a_ne : Real.sqrt a ≠ 0 := (Real.sqrt_ne_zero').2 ha_pos
  have hsqrt2_ne : Real.sqrt (2 : ℝ) ≠ 0 := by
    simpa using (Real.sqrt_ne_zero').2 (by norm_num : (0 : ℝ) < 2)
  have h2_mul_inv_sqrt2 : (2 : ℝ) * (Real.sqrt (2 : ℝ))⁻¹ = Real.sqrt (2 : ℝ) := by
    have hdiv : (2 : ℝ) / Real.sqrt (2 : ℝ) = Real.sqrt (2 : ℝ) := by
      field_simp [hsqrt2_ne]
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (Real.mul_self_sqrt (by positivity : (0 : ℝ) ≤ (2 : ℝ))).symm
    simpa [div_eq_mul_inv] using hdiv
  have ha_mul_inv_sqrt : a * (Real.sqrt a)⁻¹ = Real.sqrt a := by
    have ha0 : 0 ≤ a := le_of_lt ha_pos
    have hdiv : a / Real.sqrt a = Real.sqrt a := by
      field_simp [hsqrt_a_ne]
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using (Real.mul_self_sqrt ha0).symm
    simpa [div_eq_mul_inv] using hdiv
  calc
    2 * ((Real.sqrt (2 : ℝ))⁻¹ * (a * ((Real.sqrt a)⁻¹ * c)))
        = ((2 : ℝ) * (Real.sqrt (2 : ℝ))⁻¹) * (a * ((Real.sqrt a)⁻¹ * c)) := by
            simp [mul_assoc]
    _ = Real.sqrt (2 : ℝ) * (a * ((Real.sqrt a)⁻¹ * c)) := by
            simp [h2_mul_inv_sqrt2]
    _ = Real.sqrt (2 : ℝ) * ((a * (Real.sqrt a)⁻¹) * c) := by
            simp [mul_assoc]
    _ = Real.sqrt (2 : ℝ) * (Real.sqrt a * c) := by
            simp [ha_mul_inv_sqrt]

lemma normalizedCoeffCLM_SpaceTime_raiseOpCLM1_raise₁ (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ)
    (f : TestFunction) :
    normalizedCoeffCLM_SpaceTime ξ hξ (raise₁ n) (raiseOpCLM ξ (1 : Fin STDimension) f) =
      Real.sqrt (((2 : ℝ) * ((unpair₄₂ n + 1 : ℕ) : ℝ))) *
        normalizedCoeffCLM_SpaceTime ξ hξ n f := by
  simp [normalizedCoeffCLM_SpaceTime_apply, -coeffCLM_SpaceTime_apply, -raiseOpCLM_apply,
    -normConstSpaceTime_def]
  rw [coeffCLM_SpaceTime_raiseOpCLM (ξ := ξ) (hξ := hξ) (i := (1 : Fin STDimension))
    (n := raise₁ n) (f := f)]
  simp [unpair₄₂_raise₁, lower₁_raise₁, -coeffCLM_SpaceTime_apply, -normConstSpaceTime_def,
    mul_assoc, mul_left_comm, mul_comm]
  rw [coeffCLM_SpaceTime_eq_sqrt_normConstSpaceTime_mul_normalizedCoeffCLM_SpaceTime
    (ξ := ξ) (hξ := hξ) (n := n) (f := f)]
  rw [sqrt_normConstSpaceTime_raise₁ (ξ := ξ) (hξ := hξ) (n := n)]
  have hsqrt_ne :
      Real.sqrt (normConstSpaceTime ξ n) ≠ 0 := by
    have hpos : 0 < normConstSpaceTime ξ n := normConstSpaceTime_pos (ξ := ξ) hξ n
    exact (Real.sqrt_ne_zero').2 hpos
  have htpos : 0 < ((2 : ℝ) * ((unpair₄₂ n + 1 : ℕ) : ℝ)) := by positivity
  have hsqrt_t_ne : Real.sqrt (((2 : ℝ) * ((unpair₄₂ n + 1 : ℕ) : ℝ))) ≠ 0 :=
    (Real.sqrt_ne_zero').2 htpos
  simp [mul_assoc, mul_left_comm, mul_comm, hsqrt_ne, hsqrt_t_ne,
    -normConstSpaceTime_def, -coeffCLM_SpaceTime_apply, -normalizedCoeffCLM_SpaceTime_apply]
  set a : ℝ := (↑(unpair₄₂ n) + 1)
  set c : ℝ := (normalizedCoeffCLM_SpaceTime ξ hξ n) f
  have ha_pos : 0 < a := by positivity
  have hsqrt_a_ne : Real.sqrt a ≠ 0 := (Real.sqrt_ne_zero').2 ha_pos
  have hsqrt2_ne : Real.sqrt (2 : ℝ) ≠ 0 := by
    simpa using (Real.sqrt_ne_zero').2 (by norm_num : (0 : ℝ) < 2)
  have h2_mul_inv_sqrt2 : (2 : ℝ) * (Real.sqrt (2 : ℝ))⁻¹ = Real.sqrt (2 : ℝ) := by
    have hdiv : (2 : ℝ) / Real.sqrt (2 : ℝ) = Real.sqrt (2 : ℝ) := by
      field_simp [hsqrt2_ne]
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (Real.mul_self_sqrt (by positivity : (0 : ℝ) ≤ (2 : ℝ))).symm
    simpa [div_eq_mul_inv] using hdiv
  have ha_mul_inv_sqrt : a * (Real.sqrt a)⁻¹ = Real.sqrt a := by
    have ha0 : 0 ≤ a := le_of_lt ha_pos
    have hdiv : a / Real.sqrt a = Real.sqrt a := by
      field_simp [hsqrt_a_ne]
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using (Real.mul_self_sqrt ha0).symm
    simpa [div_eq_mul_inv] using hdiv
  calc
    2 * ((Real.sqrt (2 : ℝ))⁻¹ * (a * ((Real.sqrt a)⁻¹ * c)))
        = ((2 : ℝ) * (Real.sqrt (2 : ℝ))⁻¹) * (a * ((Real.sqrt a)⁻¹ * c)) := by
            simp [mul_assoc]
    _ = Real.sqrt (2 : ℝ) * (a * ((Real.sqrt a)⁻¹ * c)) := by
            simp [h2_mul_inv_sqrt2]
    _ = Real.sqrt (2 : ℝ) * ((a * (Real.sqrt a)⁻¹) * c) := by
            simp [mul_assoc]
    _ = Real.sqrt (2 : ℝ) * (Real.sqrt a * c) := by
            simp [ha_mul_inv_sqrt]

lemma normalizedCoeffCLM_SpaceTime_raiseOpCLM2_raise₂ (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ)
    (f : TestFunction) :
    normalizedCoeffCLM_SpaceTime ξ hξ (raise₂ n) (raiseOpCLM ξ (2 : Fin STDimension) f) =
      Real.sqrt (((2 : ℝ) * ((unpair₄₃ n + 1 : ℕ) : ℝ))) *
        normalizedCoeffCLM_SpaceTime ξ hξ n f := by
  simp [normalizedCoeffCLM_SpaceTime_apply, -coeffCLM_SpaceTime_apply, -raiseOpCLM_apply,
    -normConstSpaceTime_def]
  rw [coeffCLM_SpaceTime_raiseOpCLM (ξ := ξ) (hξ := hξ) (i := (2 : Fin STDimension))
    (n := raise₂ n) (f := f)]
  simp [unpair₄₃_raise₂, lower₂_raise₂, -coeffCLM_SpaceTime_apply, -normConstSpaceTime_def,
    mul_assoc, mul_left_comm, mul_comm]
  rw [coeffCLM_SpaceTime_eq_sqrt_normConstSpaceTime_mul_normalizedCoeffCLM_SpaceTime
    (ξ := ξ) (hξ := hξ) (n := n) (f := f)]
  rw [sqrt_normConstSpaceTime_raise₂ (ξ := ξ) (hξ := hξ) (n := n)]
  have hsqrt_ne :
      Real.sqrt (normConstSpaceTime ξ n) ≠ 0 := by
    have hpos : 0 < normConstSpaceTime ξ n := normConstSpaceTime_pos (ξ := ξ) hξ n
    exact (Real.sqrt_ne_zero').2 hpos
  have htpos : 0 < ((2 : ℝ) * ((unpair₄₃ n + 1 : ℕ) : ℝ)) := by positivity
  have hsqrt_t_ne : Real.sqrt (((2 : ℝ) * ((unpair₄₃ n + 1 : ℕ) : ℝ))) ≠ 0 :=
    (Real.sqrt_ne_zero').2 htpos
  simp [mul_assoc, mul_left_comm, mul_comm, hsqrt_ne, hsqrt_t_ne,
    -normConstSpaceTime_def, -coeffCLM_SpaceTime_apply, -normalizedCoeffCLM_SpaceTime_apply]
  set a : ℝ := (↑(unpair₄₃ n) + 1)
  set c : ℝ := (normalizedCoeffCLM_SpaceTime ξ hξ n) f
  have ha_pos : 0 < a := by positivity
  have hsqrt_a_ne : Real.sqrt a ≠ 0 := (Real.sqrt_ne_zero').2 ha_pos
  have hsqrt2_ne : Real.sqrt (2 : ℝ) ≠ 0 := by
    simpa using (Real.sqrt_ne_zero').2 (by norm_num : (0 : ℝ) < 2)
  have h2_mul_inv_sqrt2 : (2 : ℝ) * (Real.sqrt (2 : ℝ))⁻¹ = Real.sqrt (2 : ℝ) := by
    have hdiv : (2 : ℝ) / Real.sqrt (2 : ℝ) = Real.sqrt (2 : ℝ) := by
      field_simp [hsqrt2_ne]
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (Real.mul_self_sqrt (by positivity : (0 : ℝ) ≤ (2 : ℝ))).symm
    simpa [div_eq_mul_inv] using hdiv
  have ha_mul_inv_sqrt : a * (Real.sqrt a)⁻¹ = Real.sqrt a := by
    have ha0 : 0 ≤ a := le_of_lt ha_pos
    have hdiv : a / Real.sqrt a = Real.sqrt a := by
      field_simp [hsqrt_a_ne]
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using (Real.mul_self_sqrt ha0).symm
    simpa [div_eq_mul_inv] using hdiv
  calc
    2 * ((Real.sqrt (2 : ℝ))⁻¹ * (a * ((Real.sqrt a)⁻¹ * c)))
        = ((2 : ℝ) * (Real.sqrt (2 : ℝ))⁻¹) * (a * ((Real.sqrt a)⁻¹ * c)) := by
            simp [mul_assoc]
    _ = Real.sqrt (2 : ℝ) * (a * ((Real.sqrt a)⁻¹ * c)) := by
            simp [h2_mul_inv_sqrt2]
    _ = Real.sqrt (2 : ℝ) * ((a * (Real.sqrt a)⁻¹) * c) := by
            simp [mul_assoc]
    _ = Real.sqrt (2 : ℝ) * (Real.sqrt a * c) := by
            simp [ha_mul_inv_sqrt]

lemma normalizedCoeffCLM_SpaceTime_raiseOpCLM3_raise₃ (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ)
    (f : TestFunction) :
    normalizedCoeffCLM_SpaceTime ξ hξ (raise₃ n) (raiseOpCLM ξ (3 : Fin STDimension) f) =
      Real.sqrt (((2 : ℝ) * ((unpair₄₄ n + 1 : ℕ) : ℝ))) *
        normalizedCoeffCLM_SpaceTime ξ hξ n f := by
  simp [normalizedCoeffCLM_SpaceTime_apply, -coeffCLM_SpaceTime_apply, -raiseOpCLM_apply,
    -normConstSpaceTime_def]
  rw [coeffCLM_SpaceTime_raiseOpCLM (ξ := ξ) (hξ := hξ) (i := (3 : Fin STDimension))
    (n := raise₃ n) (f := f)]
  simp [unpair₄₄_raise₃, lower₃_raise₃, -coeffCLM_SpaceTime_apply, -normConstSpaceTime_def,
    mul_assoc, mul_left_comm, mul_comm]
  rw [coeffCLM_SpaceTime_eq_sqrt_normConstSpaceTime_mul_normalizedCoeffCLM_SpaceTime
    (ξ := ξ) (hξ := hξ) (n := n) (f := f)]
  rw [sqrt_normConstSpaceTime_raise₃ (ξ := ξ) (hξ := hξ) (n := n)]
  have hsqrt_ne :
      Real.sqrt (normConstSpaceTime ξ n) ≠ 0 := by
    have hpos : 0 < normConstSpaceTime ξ n := normConstSpaceTime_pos (ξ := ξ) hξ n
    exact (Real.sqrt_ne_zero').2 hpos
  have htpos : 0 < ((2 : ℝ) * ((unpair₄₄ n + 1 : ℕ) : ℝ)) := by positivity
  have hsqrt_t_ne : Real.sqrt (((2 : ℝ) * ((unpair₄₄ n + 1 : ℕ) : ℝ))) ≠ 0 :=
    (Real.sqrt_ne_zero').2 htpos
  simp [mul_assoc, mul_left_comm, mul_comm, hsqrt_ne, hsqrt_t_ne,
    -normConstSpaceTime_def, -coeffCLM_SpaceTime_apply, -normalizedCoeffCLM_SpaceTime_apply]
  set a : ℝ := (↑(unpair₄₄ n) + 1)
  set c : ℝ := (normalizedCoeffCLM_SpaceTime ξ hξ n) f
  have ha_pos : 0 < a := by
    positivity
  have hsqrt_a_ne : Real.sqrt a ≠ 0 := (Real.sqrt_ne_zero').2 ha_pos
  have hsqrt2_ne : Real.sqrt (2 : ℝ) ≠ 0 := by
    simpa using (Real.sqrt_ne_zero').2 (by norm_num : (0 : ℝ) < 2)
  have h2_mul_inv_sqrt2 : (2 : ℝ) * (Real.sqrt (2 : ℝ))⁻¹ = Real.sqrt (2 : ℝ) := by
    have hdiv : (2 : ℝ) / Real.sqrt (2 : ℝ) = Real.sqrt (2 : ℝ) := by
      field_simp [hsqrt2_ne]
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (Real.mul_self_sqrt (by positivity : (0 : ℝ) ≤ (2 : ℝ))).symm
    simpa [div_eq_mul_inv] using hdiv
  have ha_mul_inv_sqrt : a * (Real.sqrt a)⁻¹ = Real.sqrt a := by
    have ha0 : 0 ≤ a := le_of_lt ha_pos
    have hdiv : a / Real.sqrt a = Real.sqrt a := by
      field_simp [hsqrt_a_ne]
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using (Real.mul_self_sqrt ha0).symm
    simpa [div_eq_mul_inv] using hdiv
  calc
    2 * ((Real.sqrt (2 : ℝ))⁻¹ * (a * ((Real.sqrt a)⁻¹ * c)))
        = ((2 : ℝ) * (Real.sqrt (2 : ℝ))⁻¹) * (a * ((Real.sqrt a)⁻¹ * c)) := by
            simp [mul_assoc]
    _ = Real.sqrt (2 : ℝ) * (a * ((Real.sqrt a)⁻¹ * c)) := by
            simp [h2_mul_inv_sqrt2]
    _ = Real.sqrt (2 : ℝ) * ((a * (Real.sqrt a)⁻¹) * c) := by
            simp [mul_assoc]
    _ = Real.sqrt (2 : ℝ) * (Real.sqrt a * c) := by
            simp [ha_mul_inv_sqrt]

end SpaceTimeHermite

end

end PhysLean
