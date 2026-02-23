import OSforGFF.NuclearSpace.PhysHermiteSpaceTimeCoeffWeightOps
import OSforGFF.NuclearSpace.PhysHermiteSpaceTimeCoeffs
import OSforGFF.NuclearSpace.RapidDecaySeqMulti

/-!
# Rapid decay of normalized spacetime Hermite coefficients

For `TestFunction = 𝓢(SpaceTime, ℝ)`, we show that the **normalized** spacetime Hermite coefficient
sequence lies in the 4D weighted rapid-decay sequence space

`OSforGFF.RapidDecaySeqBase.space OSforGFF.RapidDecaySeqMulti.base₄`.

Concretely, for every `k : ℕ`, the weighted sequence

`n ↦ (base₄ n)^k * (normalizedCoeffCLM_SpaceTime ξ hξ n f)`

is in `ℓ²`. The proof uses:
- the coefficient-diagonal “number + 1” operators `numPlusOneCLM`, and
- Bessel summability for the normalized eigenfunctions in `L²(SpaceTime)`.

Pre-requisite for transporting nuclearity from the abstract rapid-decay model to
Schwartz test functions via Hermite expansions.
-/

open scoped BigOperators NNReal ENNReal

namespace PhysLean

noncomputable section

namespace SpaceTimeHermite

open MeasureTheory

local notation "base₄" => OSforGFF.RapidDecaySeqMulti.base₄

/-! ## The product “number operator” and its action on normalized coefficients -/

/-- The product of the four coordinatewise “number + 1” operators. On coefficients it acts by
the scalar `base₄ n = ∏ᵢ (unpair₄ᵢ n + 1)`. -/
noncomputable def numAllCLM (ξ : ℝ) : TestFunction →L[ℝ] TestFunction :=
  (numPlusOneCLM ξ (0 : Fin STDimension)).comp
    ((numPlusOneCLM ξ (1 : Fin STDimension)).comp
      ((numPlusOneCLM ξ (2 : Fin STDimension)).comp
        (numPlusOneCLM ξ (3 : Fin STDimension))))

@[simp]
lemma numAllCLM_apply (ξ : ℝ) (f : TestFunction) :
    numAllCLM ξ f =
      numPlusOneCLM ξ (0 : Fin STDimension)
        (numPlusOneCLM ξ (1 : Fin STDimension)
          (numPlusOneCLM ξ (2 : Fin STDimension)
            (numPlusOneCLM ξ (3 : Fin STDimension) f))) := by
  simp [numAllCLM]

lemma normalizedCoeffCLM_SpaceTime_numPlusOneCLM0 (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) (f : TestFunction) :
    normalizedCoeffCLM_SpaceTime ξ hξ n (numPlusOneCLM ξ (0 : Fin STDimension) f)
      = (unpair₄₁ n + 1) * normalizedCoeffCLM_SpaceTime ξ hξ n f := by
  -- Keep `coeffCLM_SpaceTime` opaque (avoid unfolding to an integral).
  simp [normalizedCoeffCLM_SpaceTime, smul_eq_mul, -coeffCLM_SpaceTime_apply,
    coeffCLM_SpaceTime_numPlusOneCLM0, mul_left_comm, mul_comm]

lemma normalizedCoeffCLM_SpaceTime_numPlusOneCLM1 (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) (f : TestFunction) :
    normalizedCoeffCLM_SpaceTime ξ hξ n (numPlusOneCLM ξ (1 : Fin STDimension) f)
      = (unpair₄₂ n + 1) * normalizedCoeffCLM_SpaceTime ξ hξ n f := by
  simp [normalizedCoeffCLM_SpaceTime, smul_eq_mul, -coeffCLM_SpaceTime_apply,
    coeffCLM_SpaceTime_numPlusOneCLM1, mul_left_comm, mul_comm]

lemma normalizedCoeffCLM_SpaceTime_numPlusOneCLM2 (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) (f : TestFunction) :
    normalizedCoeffCLM_SpaceTime ξ hξ n (numPlusOneCLM ξ (2 : Fin STDimension) f)
      = (unpair₄₃ n + 1) * normalizedCoeffCLM_SpaceTime ξ hξ n f := by
  simp [normalizedCoeffCLM_SpaceTime, smul_eq_mul, -coeffCLM_SpaceTime_apply,
    coeffCLM_SpaceTime_numPlusOneCLM2, mul_left_comm, mul_comm]

lemma normalizedCoeffCLM_SpaceTime_numPlusOneCLM3 (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) (f : TestFunction) :
    normalizedCoeffCLM_SpaceTime ξ hξ n (numPlusOneCLM ξ (3 : Fin STDimension) f)
      = (unpair₄₄ n + 1) * normalizedCoeffCLM_SpaceTime ξ hξ n f := by
  simp [normalizedCoeffCLM_SpaceTime, smul_eq_mul, -coeffCLM_SpaceTime_apply,
    coeffCLM_SpaceTime_numPlusOneCLM3, mul_left_comm, mul_comm]

lemma normalizedCoeffCLM_SpaceTime_numAllCLM (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) (f : TestFunction) :
    normalizedCoeffCLM_SpaceTime ξ hξ n (numAllCLM ξ f)
      = base₄ n * normalizedCoeffCLM_SpaceTime ξ hξ n f := by
  -- apply the four diagonal actions, then rewrite the product as `base₄ n`
  simp [numAllCLM_apply,
    normalizedCoeffCLM_SpaceTime_numPlusOneCLM0 (ξ := ξ) (hξ := hξ) (n := n),
    normalizedCoeffCLM_SpaceTime_numPlusOneCLM1 (ξ := ξ) (hξ := hξ) (n := n),
    normalizedCoeffCLM_SpaceTime_numPlusOneCLM2 (ξ := ξ) (hξ := hξ) (n := n),
    normalizedCoeffCLM_SpaceTime_numPlusOneCLM3 (ξ := ξ) (hξ := hξ) (n := n),
    base₄_eq_unpair₄ (n := n), mul_assoc, mul_left_comm, mul_comm]

/-- The `k`-fold iterate of `numAllCLM`. -/
noncomputable def numAllPowCLM (ξ : ℝ) : ℕ → TestFunction →L[ℝ] TestFunction
  | 0 => 1
  | k + 1 => (numAllCLM ξ).comp (numAllPowCLM ξ k)

@[simp]
lemma numAllPowCLM_zero (ξ : ℝ) : numAllPowCLM ξ 0 = 1 := rfl

@[simp]
lemma numAllPowCLM_succ (ξ : ℝ) (k : ℕ) :
    numAllPowCLM ξ (k + 1) = (numAllCLM ξ).comp (numAllPowCLM ξ k) := rfl

@[simp]
lemma numAllPowCLM_succ_apply (ξ : ℝ) (k : ℕ) (f : TestFunction) :
    numAllPowCLM ξ (k + 1) f = numAllCLM ξ (numAllPowCLM ξ k f) := by
  simp [numAllPowCLM]

lemma normalizedCoeffCLM_SpaceTime_numAllPowCLM (ξ : ℝ) (hξ : ξ ≠ 0) (k n : ℕ) (f : TestFunction) :
    normalizedCoeffCLM_SpaceTime ξ hξ n (numAllPowCLM ξ k f)
      = (base₄ n) ^ k * normalizedCoeffCLM_SpaceTime ξ hξ n f := by
  induction k with
  | zero =>
      simp [numAllPowCLM]
  | succ k ih =>
      -- one more application multiplies coefficients by `base₄ n`
      have hstep :
          normalizedCoeffCLM_SpaceTime ξ hξ n (numAllPowCLM ξ (k + 1) f)
            = base₄ n * normalizedCoeffCLM_SpaceTime ξ hξ n (numAllPowCLM ξ k f) := by
        -- rewrite the iterate once, then apply the diagonal action lemma
        rw [numAllPowCLM_succ_apply (ξ := ξ) (k := k) (f := f)]
        exact (normalizedCoeffCLM_SpaceTime_numAllCLM (ξ := ξ) (hξ := hξ) (n := n)
          (f := numAllPowCLM ξ k f))
      -- now finish by induction and rearranging `pow_succ`
      calc
        normalizedCoeffCLM_SpaceTime ξ hξ n (numAllPowCLM ξ (k + 1) f)
            = base₄ n * normalizedCoeffCLM_SpaceTime ξ hξ n (numAllPowCLM ξ k f) := hstep
        _ = base₄ n * ((base₄ n) ^ k * normalizedCoeffCLM_SpaceTime ξ hξ n f) := by
              simp [ih]
        _ = (base₄ n) ^ (k + 1) * normalizedCoeffCLM_SpaceTime ξ hξ n f := by
              -- commute the new factor into the `pow_succ` shape
              simp [pow_succ, mul_assoc, mul_comm]

/-! ## Coefficients as an element of the rapid-decay sequence space -/

/-- The normalized coefficient sequence of `f : TestFunction`, as an element of the
rapid-decay sequence space `RapidDecaySeqBase.space base₄`. -/
noncomputable def normalizedCoeffRapidDecay (ξ : ℝ) (hξ : ξ ≠ 0) (f : TestFunction) :
    OSforGFF.RapidDecaySeqBase.space base₄ :=
  ⟨normalizedCoeffCLM_SpaceTime_pi ξ hξ f, by
    intro k
    -- `ℓ²` membership of coefficients after applying `numAllPowCLM ξ k`
    have hk' :
        Memℓp (normalizedCoeffCLM_SpaceTime_pi ξ hξ (numAllPowCLM ξ k f)) (2 : ℝ≥0∞) :=
      (normalizedCoeffL2 ξ hξ (numAllPowCLM ξ k f)).2
    -- identify the weighted sequence with those coefficients, pointwise
    have hfun :
        OSforGFF.RapidDecaySeqBase.weightFun base₄ k (normalizedCoeffCLM_SpaceTime_pi ξ hξ f)
          = normalizedCoeffCLM_SpaceTime_pi ξ hξ (numAllPowCLM ξ k f) := by
      funext n
      simp [OSforGFF.RapidDecaySeqBase.weightFun, OSforGFF.RapidDecaySeqBase.weight,
        normalizedCoeffCLM_SpaceTime_pi_apply,
        normalizedCoeffCLM_SpaceTime_numAllPowCLM (ξ := ξ) (hξ := hξ) (k := k) (n := n) (f := f),
        mul_comm]
    simpa [hfun] using hk'⟩

@[simp] lemma normalizedCoeffRapidDecay_coe (ξ : ℝ) (hξ : ξ ≠ 0) (f : TestFunction) :
    (normalizedCoeffRapidDecay ξ hξ f : ℕ → ℝ) = normalizedCoeffCLM_SpaceTime_pi ξ hξ f := rfl

@[simp] lemma normalizedCoeffRapidDecay_apply (ξ : ℝ) (hξ : ξ ≠ 0) (f : TestFunction) (n : ℕ) :
    (normalizedCoeffRapidDecay ξ hξ f : ℕ → ℝ) n = normalizedCoeffCLM_SpaceTime ξ hξ n f := by
  rfl

/-- The normalized coefficient map as a linear map `TestFunction → RapidDecaySeq₄`. -/
noncomputable def normalizedCoeffRapidDecayₗ (ξ : ℝ) (hξ : ξ ≠ 0) :
    TestFunction →ₗ[ℝ] OSforGFF.RapidDecaySeqBase.space base₄ where
  toFun := normalizedCoeffRapidDecay ξ hξ
  map_add' f g := by
    ext n
    simp [normalizedCoeffRapidDecay]
  map_smul' c f := by
    ext n
    simp [normalizedCoeffRapidDecay]

@[simp] lemma normalizedCoeffRapidDecayₗ_apply (ξ : ℝ) (hξ : ξ ≠ 0) (f : TestFunction) :
    normalizedCoeffRapidDecayₗ ξ hξ f = normalizedCoeffRapidDecay ξ hξ f := rfl

@[simp] lemma normalizedCoeffRapidDecayₗ_apply_apply (ξ : ℝ) (hξ : ξ ≠ 0) (f : TestFunction) (n : ℕ) :
    (normalizedCoeffRapidDecayₗ ξ hξ f : ℕ → ℝ) n = normalizedCoeffCLM_SpaceTime ξ hξ n f := by
  rfl

end SpaceTimeHermite

end

end PhysLean
