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

lemma coeffCLM_SpaceTime_lowerOpCLM0 (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) (f : TestFunction) :
    coeffCLM_SpaceTime ξ hξ n (lowerOpCLM ξ (0 : Fin STDimension) f)
      = coeffCLM_SpaceTime ξ hξ (raise₀ n) f := by
  simp [lowerOpCLM, coeffCLM_SpaceTime_mulCoord0, coeffCLM_SpaceTime_derivCoord0,
    div_eq_mul_inv, mul_assoc, sub_eq_add_neg,
    -coeffCLM_SpaceTime_apply, -mulCoordCLM_apply, -derivCoordCLM_apply]
  field_simp [hξ]
  ring

lemma coeffCLM_SpaceTime_lowerOpCLM1 (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) (f : TestFunction) :
    coeffCLM_SpaceTime ξ hξ n (lowerOpCLM ξ (1 : Fin STDimension) f)
      = coeffCLM_SpaceTime ξ hξ (raise₁ n) f := by
  simp [lowerOpCLM, coeffCLM_SpaceTime_mulCoord1, coeffCLM_SpaceTime_derivCoord1,
    div_eq_mul_inv, mul_assoc, sub_eq_add_neg,
    -coeffCLM_SpaceTime_apply, -mulCoordCLM_apply, -derivCoordCLM_apply]
  field_simp [hξ]
  ring

lemma coeffCLM_SpaceTime_lowerOpCLM2 (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) (f : TestFunction) :
    coeffCLM_SpaceTime ξ hξ n (lowerOpCLM ξ (2 : Fin STDimension) f)
      = coeffCLM_SpaceTime ξ hξ (raise₂ n) f := by
  simp [lowerOpCLM, coeffCLM_SpaceTime_mulCoord2, coeffCLM_SpaceTime_derivCoord2,
    div_eq_mul_inv, mul_assoc, sub_eq_add_neg,
    -coeffCLM_SpaceTime_apply, -mulCoordCLM_apply, -derivCoordCLM_apply]
  field_simp [hξ]
  ring

lemma coeffCLM_SpaceTime_lowerOpCLM3 (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) (f : TestFunction) :
    coeffCLM_SpaceTime ξ hξ n (lowerOpCLM ξ (3 : Fin STDimension) f)
      = coeffCLM_SpaceTime ξ hξ (raise₃ n) f := by
  simp [lowerOpCLM, coeffCLM_SpaceTime_mulCoord3, coeffCLM_SpaceTime_derivCoord3,
    div_eq_mul_inv, mul_assoc, sub_eq_add_neg,
    -coeffCLM_SpaceTime_apply, -mulCoordCLM_apply, -derivCoordCLM_apply]
  field_simp [hξ]
  ring

lemma coeffCLM_SpaceTime_raiseOpCLM0 (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) (f : TestFunction) :
    coeffCLM_SpaceTime ξ hξ n (raiseOpCLM ξ (0 : Fin STDimension) f)
      = (2 : ℝ) * (unpair₄₁ n) * coeffCLM_SpaceTime ξ hξ (lower₀ n) f := by
  simp [raiseOpCLM, coeffCLM_SpaceTime_mulCoord0, coeffCLM_SpaceTime_derivCoord0,
    div_eq_mul_inv, mul_assoc, sub_eq_add_neg,
    -coeffCLM_SpaceTime_apply, -mulCoordCLM_apply, -derivCoordCLM_apply]
  field_simp [hξ]
  ring

lemma coeffCLM_SpaceTime_raiseOpCLM1 (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) (f : TestFunction) :
    coeffCLM_SpaceTime ξ hξ n (raiseOpCLM ξ (1 : Fin STDimension) f)
      = (2 : ℝ) * (unpair₄₂ n) * coeffCLM_SpaceTime ξ hξ (lower₁ n) f := by
  simp [raiseOpCLM, coeffCLM_SpaceTime_mulCoord1, coeffCLM_SpaceTime_derivCoord1,
    div_eq_mul_inv, mul_assoc, sub_eq_add_neg,
    -coeffCLM_SpaceTime_apply, -mulCoordCLM_apply, -derivCoordCLM_apply]
  field_simp [hξ]
  ring

lemma coeffCLM_SpaceTime_raiseOpCLM2 (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) (f : TestFunction) :
    coeffCLM_SpaceTime ξ hξ n (raiseOpCLM ξ (2 : Fin STDimension) f)
      = (2 : ℝ) * (unpair₄₃ n) * coeffCLM_SpaceTime ξ hξ (lower₂ n) f := by
  simp [raiseOpCLM, coeffCLM_SpaceTime_mulCoord2, coeffCLM_SpaceTime_derivCoord2,
    div_eq_mul_inv, mul_assoc, sub_eq_add_neg,
    -coeffCLM_SpaceTime_apply, -mulCoordCLM_apply, -derivCoordCLM_apply]
  field_simp [hξ]
  ring

lemma coeffCLM_SpaceTime_raiseOpCLM3 (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) (f : TestFunction) :
    coeffCLM_SpaceTime ξ hξ n (raiseOpCLM ξ (3 : Fin STDimension) f)
      = (2 : ℝ) * (unpair₄₄ n) * coeffCLM_SpaceTime ξ hξ (lower₃ n) f := by
  simp [raiseOpCLM, coeffCLM_SpaceTime_mulCoord3, coeffCLM_SpaceTime_derivCoord3,
    div_eq_mul_inv, mul_assoc, sub_eq_add_neg,
    -coeffCLM_SpaceTime_apply, -mulCoordCLM_apply, -derivCoordCLM_apply]
  field_simp [hξ]
  ring

/-! ## The coordinatewise “number + 1” operator -/

/-- The coordinatewise “number + 1” operator, diagonal on Hermite coefficients:
`(1/2) * (lowerOp ∘ raiseOp)`. -/
noncomputable def numPlusOneCLM (ξ : ℝ) (i : Fin STDimension) : TestFunction →L[ℝ] TestFunction :=
  (1 / 2 : ℝ) • (lowerOpCLM ξ i).comp (raiseOpCLM ξ i)

lemma coeffCLM_SpaceTime_numPlusOneCLM0 (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) (f : TestFunction) :
    coeffCLM_SpaceTime ξ hξ n (numPlusOneCLM ξ (0 : Fin STDimension) f)
      = (unpair₄₁ n + 1) * coeffCLM_SpaceTime ξ hξ n f := by
  simp [numPlusOneCLM,
    -lowerOpCLM_apply, -raiseOpCLM_apply, -coeffCLM_SpaceTime_apply]
  rw [coeffCLM_SpaceTime_lowerOpCLM0 (ξ := ξ) (hξ := hξ) (n := n) (f := raiseOpCLM ξ 0 f)]
  rw [coeffCLM_SpaceTime_raiseOpCLM0 (ξ := ξ) (hξ := hξ) (n := raise₀ n) (f := f)]
  simp
  ring

lemma coeffCLM_SpaceTime_numPlusOneCLM1 (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) (f : TestFunction) :
    coeffCLM_SpaceTime ξ hξ n (numPlusOneCLM ξ (1 : Fin STDimension) f)
      = (unpair₄₂ n + 1) * coeffCLM_SpaceTime ξ hξ n f := by
  simp [numPlusOneCLM,
    -lowerOpCLM_apply, -raiseOpCLM_apply, -coeffCLM_SpaceTime_apply]
  rw [coeffCLM_SpaceTime_lowerOpCLM1 (ξ := ξ) (hξ := hξ) (n := n) (f := raiseOpCLM ξ 1 f)]
  rw [coeffCLM_SpaceTime_raiseOpCLM1 (ξ := ξ) (hξ := hξ) (n := raise₁ n) (f := f)]
  simp
  ring

lemma coeffCLM_SpaceTime_numPlusOneCLM2 (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) (f : TestFunction) :
    coeffCLM_SpaceTime ξ hξ n (numPlusOneCLM ξ (2 : Fin STDimension) f)
      = (unpair₄₃ n + 1) * coeffCLM_SpaceTime ξ hξ n f := by
  simp [numPlusOneCLM,
    -lowerOpCLM_apply, -raiseOpCLM_apply, -coeffCLM_SpaceTime_apply]
  rw [coeffCLM_SpaceTime_lowerOpCLM2 (ξ := ξ) (hξ := hξ) (n := n) (f := raiseOpCLM ξ 2 f)]
  rw [coeffCLM_SpaceTime_raiseOpCLM2 (ξ := ξ) (hξ := hξ) (n := raise₂ n) (f := f)]
  simp
  ring

lemma coeffCLM_SpaceTime_numPlusOneCLM3 (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) (f : TestFunction) :
    coeffCLM_SpaceTime ξ hξ n (numPlusOneCLM ξ (3 : Fin STDimension) f)
      = (unpair₄₄ n + 1) * coeffCLM_SpaceTime ξ hξ n f := by
  simp [numPlusOneCLM,
    -lowerOpCLM_apply, -raiseOpCLM_apply, -coeffCLM_SpaceTime_apply]
  rw [coeffCLM_SpaceTime_lowerOpCLM3 (ξ := ξ) (hξ := hξ) (n := n) (f := raiseOpCLM ξ 3 f)]
  rw [coeffCLM_SpaceTime_raiseOpCLM3 (ξ := ξ) (hξ := hξ) (n := raise₃ n) (f := f)]
  simp
  ring

end SpaceTimeHermite

end

end PhysLean
