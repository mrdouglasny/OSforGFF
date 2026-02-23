import OSforGFF.NuclearSpace.PhysHermiteSpaceTime

/-!
# Normalized Hermite coefficient maps on spacetime

The normalized spacetime Hermite coefficients as continuous linear maps
on `TestFunction = 𝓢(SpaceTime, ℝ)`.
-/

open scoped BigOperators NNReal ENNReal InnerProductSpace RealInnerProductSpace

namespace PhysLean

noncomputable section

namespace SpaceTimeHermite

open MeasureTheory

/-! ## Normalized coefficient functionals on `TestFunction` -/

/-- The normalized coefficient functional on `TestFunction` against the 4D eigenfunction indexed by `n`.

The unnormalized coefficient functional `coeffCLM_SpaceTime` scaled by the inverse square
root of the `L²`-norm constant `normConstSpaceTime`. -/
noncomputable def normalizedCoeffCLM_SpaceTime (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) :
    TestFunction →L[ℝ] ℝ :=
  (Real.sqrt (normConstSpaceTime ξ n))⁻¹ • coeffCLM_SpaceTime ξ hξ n

@[simp]
lemma normalizedCoeffCLM_SpaceTime_apply (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) (f : TestFunction) :
    normalizedCoeffCLM_SpaceTime ξ hξ n f =
      (Real.sqrt (normConstSpaceTime ξ n))⁻¹ * coeffCLM_SpaceTime ξ hξ n f := by
  simp [normalizedCoeffCLM_SpaceTime, smul_eq_mul]

lemma normalizedCoeffCLM_SpaceTime_apply_eq_inner (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) (f : TestFunction) :
    normalizedCoeffCLM_SpaceTime ξ hξ n f =
      ⟪normalizedEigenfunctionSpaceTimeL2 (ξ := ξ) hξ n,
        f.toLp 2 (volume : Measure SpaceTime)⟫ := by
  simpa [normalizedCoeffCLM_SpaceTime, smul_eq_mul] using
    (inner_normalizedEigenfunctionSpaceTimeL2_toLp (ξ := ξ) (hξ := hξ) (n := n) (f := f)).symm

/-- The normalized coefficient map `TestFunction → (ℕ → ℝ)`. -/
noncomputable def normalizedCoeffCLM_SpaceTime_pi (ξ : ℝ) (hξ : ξ ≠ 0) :
    TestFunction →L[ℝ] (ℕ → ℝ) :=
  ContinuousLinearMap.pi (fun n : ℕ => normalizedCoeffCLM_SpaceTime ξ hξ n)

@[simp]
lemma normalizedCoeffCLM_SpaceTime_pi_apply (ξ : ℝ) (hξ : ξ ≠ 0) (f : TestFunction) (n : ℕ) :
    normalizedCoeffCLM_SpaceTime_pi ξ hξ f n = normalizedCoeffCLM_SpaceTime ξ hξ n f := by
  rfl

/-! ## The coefficient sequence as an element of `ℓ²(ℕ, ℝ)` -/

/-- The normalized coefficient sequence of `f : TestFunction`, bundled as an element of `ℓ²(ℕ, ℝ)`. -/
noncomputable def normalizedCoeffL2 (ξ : ℝ) (hξ : ξ ≠ 0) (f : TestFunction) : ℓ²(ℕ, ℝ) :=
  ⟨normalizedCoeffCLM_SpaceTime_pi ξ hξ f, by
    refine memℓp_gen (p := (2 : ℝ≥0∞)) ?_
    have htwo : ((2 : ℝ≥0∞).toReal) = (2 : ℝ) := by norm_num
    have hsNat :
        Summable (fun n : ℕ =>
          ‖⟪normalizedEigenfunctionSpaceTimeL2 (ξ := ξ) hξ n,
              f.toLp 2 (volume : Measure SpaceTime)⟫‖ ^ 2) :=
      summable_sq_inner_normalizedEigenfunctionSpaceTimeL2 (ξ := ξ) (hξ := hξ) f
    have hsPow :
        Summable (fun n : ℕ => ‖normalizedCoeffCLM_SpaceTime_pi ξ hξ f n‖ ^ 2) := by
      refine hsNat.congr ?_
      intro n
      simp [normalizedCoeffCLM_SpaceTime_pi_apply, normalizedCoeffCLM_SpaceTime_apply_eq_inner,
        -normalizedCoeffCLM_SpaceTime_apply]
    simpa [htwo, Real.rpow_natCast] using hsPow⟩

@[simp]
lemma normalizedCoeffL2_apply (ξ : ℝ) (hξ : ξ ≠ 0) (f : TestFunction) (n : ℕ) :
    (normalizedCoeffL2 ξ hξ f : ℕ → ℝ) n = normalizedCoeffCLM_SpaceTime_pi ξ hξ f n := rfl

lemma normalizedCoeffL2_apply_eq_inner (ξ : ℝ) (hξ : ξ ≠ 0) (f : TestFunction) (n : ℕ) :
    (normalizedCoeffL2 ξ hξ f : ℕ → ℝ) n =
      ⟪normalizedEigenfunctionSpaceTimeL2 (ξ := ξ) hξ n,
        f.toLp 2 (volume : Measure SpaceTime)⟫ := by
  simp [normalizedCoeffL2_apply, normalizedCoeffCLM_SpaceTime_pi_apply,
    normalizedCoeffCLM_SpaceTime_apply_eq_inner, -normalizedCoeffCLM_SpaceTime_apply]

end SpaceTimeHermite

end

end PhysLean
