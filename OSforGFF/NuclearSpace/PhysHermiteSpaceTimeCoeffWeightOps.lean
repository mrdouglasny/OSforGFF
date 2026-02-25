/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import OSforGFF.NuclearSpace.PhysHermiteSpaceTimeCoeffDerivLadder
import OSforGFF.NuclearSpace.PhysHermiteSpaceTimeCoeffLadder
import OSforGFF.NuclearSpace.RapidDecaySeqBase

/-!
# Weight / number operators for spacetime Hermite coefficients

Multiplication- and derivative-coefficient ladder relations into
coordinatewise **number operators** on `TestFunction`.

A family of continuous linear maps `numPlusOneCLM ξ i` such that the spacetime
Hermite coefficient functionals satisfy

`coeffCLM_SpaceTime ξ hξ n (numPlusOneCLM ξ i f) = (idx n i + 1) * coeffCLM_SpaceTime ξ hξ n f`.

Iterating in `k` and composing over the four coordinates produces an operator which multiplies the
`n`-th coefficient by `(RapidDecaySeqMulti.base₄ n)^k`, giving the rapid-decay (`ℓ²`-weighted)
property of normalized coefficients via Bessel's inequality.
-/

open scoped BigOperators

namespace PhysLean

noncomputable section

open MeasureTheory

namespace SpaceTimeHermite

/-! ## Basic index identities -/

@[simp]
lemma lower₀_raise₀ (n : ℕ) : lower₀ (raise₀ n) = n := by
  refine (OSforGFF.RapidDecaySeqMulti.pairEquiv₄.symm.injective ?_)
  simpa [unpair₄] using (by
    rw [unpair₄_lower₀]
    simp : unpair₄ (lower₀ (raise₀ n)) = unpair₄ n)

@[simp]
lemma lower₁_raise₁ (n : ℕ) : lower₁ (raise₁ n) = n := by
  refine (OSforGFF.RapidDecaySeqMulti.pairEquiv₄.symm.injective ?_)
  simpa [unpair₄] using (by
    rw [unpair₄_lower₁]
    simp : unpair₄ (lower₁ (raise₁ n)) = unpair₄ n)

@[simp]
lemma lower₂_raise₂ (n : ℕ) : lower₂ (raise₂ n) = n := by
  refine (OSforGFF.RapidDecaySeqMulti.pairEquiv₄.symm.injective ?_)
  simpa [unpair₄] using (by
    rw [unpair₄_lower₂]
    simp : unpair₄ (lower₂ (raise₂ n)) = unpair₄ n)

@[simp]
lemma lower₃_raise₃ (n : ℕ) : lower₃ (raise₃ n) = n := by
  refine (OSforGFF.RapidDecaySeqMulti.pairEquiv₄.symm.injective ?_)
  simpa [unpair₄] using (by
    rw [unpair₄_lower₃]
    simp : unpair₄ (lower₃ (raise₃ n)) = unpair₄ n)

@[simp]
lemma lower_raise (i : Fin STDimension) (n : ℕ) : lower i (raise i n) = n := by
  fin_cases i <;> simp [raise, lower]

@[simp]
lemma idx_raise_self (i : Fin STDimension) (n : ℕ) : idx (raise i n) i = idx n i + 1 := by
  fin_cases i <;> simp [raise, idx]

/-! ## Coordinatewise ladder operators on `TestFunction` -/

/-- The (coordinatewise) operator `f ↦ (xᵢ/ξ) f - ξ (∂ᵢ f)` on `TestFunction`. -/
noncomputable def raiseOpCLM (ξ : ℝ) (i : Fin STDimension) : TestFunction →L[ℝ] TestFunction :=
  (ξ⁻¹) • mulCoordCLM i - ξ • derivCoordCLM i

/-- The (coordinatewise) operator `f ↦ (xᵢ/ξ) f + ξ (∂ᵢ f)` on `TestFunction`. -/
noncomputable def lowerOpCLM (ξ : ℝ) (i : Fin STDimension) : TestFunction →L[ℝ] TestFunction :=
  (ξ⁻¹) • mulCoordCLM i + ξ • derivCoordCLM i

@[simp]
lemma raiseOpCLM_apply (ξ : ℝ) (i : Fin STDimension) (f : TestFunction) :
    raiseOpCLM ξ i f = (ξ⁻¹) • mulCoordCLM i f - ξ • derivCoordCLM i f := by
  simp [raiseOpCLM]

@[simp]
lemma lowerOpCLM_apply (ξ : ℝ) (i : Fin STDimension) (f : TestFunction) :
    lowerOpCLM ξ i f = (ξ⁻¹) • mulCoordCLM i f + ξ • derivCoordCLM i f := by
  simp [lowerOpCLM]

/-! ## Coefficient action of the ladder operators -/

lemma coeffCLM_SpaceTime_lowerOpCLM (ξ : ℝ) (hξ : ξ ≠ 0) (i : Fin STDimension)
    (n : ℕ) (f : TestFunction) :
    coeffCLM_SpaceTime ξ hξ n (lowerOpCLM ξ i f)
      = coeffCLM_SpaceTime ξ hξ (raise i n) f := by
  simp [lowerOpCLM, coeffCLM_SpaceTime_mulCoord, coeffCLM_SpaceTime_derivCoord,
    div_eq_mul_inv, mul_assoc, sub_eq_add_neg,
    -coeffCLM_SpaceTime_apply, -mulCoordCLM_apply, -derivCoordCLM_apply]
  field_simp [hξ]
  ring

lemma coeffCLM_SpaceTime_raiseOpCLM (ξ : ℝ) (hξ : ξ ≠ 0) (i : Fin STDimension)
    (n : ℕ) (f : TestFunction) :
    coeffCLM_SpaceTime ξ hξ n (raiseOpCLM ξ i f)
      = (2 : ℝ) * (((idx n i : ℕ) : ℝ)) * coeffCLM_SpaceTime ξ hξ (lower i n) f := by
  simp [raiseOpCLM, coeffCLM_SpaceTime_mulCoord, coeffCLM_SpaceTime_derivCoord,
    div_eq_mul_inv, mul_assoc, sub_eq_add_neg,
    -coeffCLM_SpaceTime_apply, -mulCoordCLM_apply, -derivCoordCLM_apply]
  field_simp [hξ]
  ring

/-! ## The coordinatewise “number + 1” operator -/

/-- The coordinatewise “number + 1” operator, diagonal on Hermite coefficients:
`(1/2) * (lowerOp ∘ raiseOp)`. -/
noncomputable def numPlusOneCLM (ξ : ℝ) (i : Fin STDimension) : TestFunction →L[ℝ] TestFunction :=
  (1 / 2 : ℝ) • (lowerOpCLM ξ i).comp (raiseOpCLM ξ i)

lemma coeffCLM_SpaceTime_numPlusOneCLM (ξ : ℝ) (hξ : ξ ≠ 0) (i : Fin STDimension)
    (n : ℕ) (f : TestFunction) :
    coeffCLM_SpaceTime ξ hξ n (numPlusOneCLM ξ i f)
      = ((((idx n i : ℕ) + 1 : ℕ) : ℝ)) * coeffCLM_SpaceTime ξ hξ n f := by
  simp [numPlusOneCLM,
    -lowerOpCLM_apply, -raiseOpCLM_apply, -coeffCLM_SpaceTime_apply]
  rw [coeffCLM_SpaceTime_lowerOpCLM (ξ := ξ) (hξ := hξ) (i := i) (n := n) (f := raiseOpCLM ξ i f)]
  rw [coeffCLM_SpaceTime_raiseOpCLM (ξ := ξ) (hξ := hξ) (i := i) (n := raise i n) (f := f)]
  simp [lower_raise]
  ring

end SpaceTimeHermite

end

end PhysLean
