import OSforGFF.NuclearSpace.PhysHermiteSpaceTimeCoeffNuclearity
import OSforGFF.NuclearSpace.Schwartz
import OSforGFF.NuclearSpace.PhysHermiteSpaceTimeHilbertBasis

/-!
# Bounding coefficient seminorms by Schwartz seminorms

This file starts the comparison between the coefficient seminorm sequence
`PhysLean.SpaceTimeHermite.coeffSeminormSeq ξ hξ` and the canonical Schwartz seminorm sequence
`OSforGFF.schwartzSeminormSeq`.

The key analytic ingredient for the easy direction is Bessel's inequality for the orthonormal
family of normalized spacetime Hermite eigenfunctions in `L²(SpaceTime)`.
-/

open scoped BigOperators NNReal ENNReal InnerProductSpace RealInnerProductSpace

namespace PhysLean

noncomputable section

namespace SpaceTimeHermite

open MeasureTheory

local notation "H" => ℓ²(ℕ, ℝ)

/-! ## Bessel estimate for normalized coefficients -/

lemma norm_normalizedCoeffL2_le_norm_toLp (ξ : ℝ) (hξ : ξ ≠ 0) (f : TestFunction) :
    ‖normalizedCoeffL2 ξ hξ f‖ ≤ ‖f.toLp 2 (volume : Measure SpaceTime)‖ := by
  -- Compare squares, then take square roots.
  have hp : (0 : ℝ) < ((2 : ℝ≥0∞).toReal) := by norm_num
  -- `‖a‖^2 = ∑ ‖a n‖^2` in `ℓ²`.
  have hnorm :
      ‖normalizedCoeffL2 ξ hξ f‖ ^ ((2 : ℝ≥0∞).toReal) =
        ∑' n : ℕ, ‖(normalizedCoeffL2 ξ hξ f : ℕ → ℝ) n‖ ^ ((2 : ℝ≥0∞).toReal) := by
    simpa using (lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) hp (normalizedCoeffL2 ξ hξ f))
  -- Rewrite the RHS using the inner product formula for coefficients.
  have hcoeff :
      (fun n : ℕ => ‖(normalizedCoeffL2 ξ hξ f : ℕ → ℝ) n‖ ^ ((2 : ℝ≥0∞).toReal)) =
        (fun n : ℕ =>
          ‖⟪normalizedEigenfunctionSpaceTimeL2 (ξ := ξ) hξ n,
              f.toLp 2 (volume : Measure SpaceTime)⟫‖ ^ ((2 : ℝ≥0∞).toReal)) := by
    funext n
    -- `toReal 2 = 2` and the coefficient is the inner product.
    -- Keep the coefficient map opaque; only rewrite to the inner product.
    simp only [normalizedCoeffL2_apply_eq_inner]
  -- Apply Bessel inequality in the Hilbert space `L²`.
  have hbessel :
      (∑' n : ℕ,
          ‖⟪normalizedEigenfunctionSpaceTimeL2 (ξ := ξ) hξ n,
              f.toLp 2 (volume : Measure SpaceTime)⟫‖ ^ 2)
        ≤ ‖f.toLp 2 (volume : Measure SpaceTime)‖ ^ 2 := by
    simpa using
      (Orthonormal.tsum_inner_products_le (𝕜 := ℝ)
        (v := normalizedEigenfunctionSpaceTimeL2 (ξ := ξ) hξ)
        (x := f.toLp 2 (volume : Measure SpaceTime))
        (orthonormal_normalizedEigenfunctionSpaceTimeL2 (ξ := ξ) hξ))
  -- Put everything together.
  -- First convert `hbessel` to a bound on `‖normalizedCoeffL2‖^2`.
  have hsq :
      ‖normalizedCoeffL2 ξ hξ f‖ ^ 2 ≤ ‖f.toLp 2 (volume : Measure SpaceTime)‖ ^ 2 := by
    -- rewrite `‖normalizedCoeffL2‖^2` as a `tsum` of coefficient squares, then use Bessel.
    have htwo : ((2 : ℝ≥0∞).toReal) = (2 : ℝ) := by norm_num
    have hnorm2 :
        ‖normalizedCoeffL2 ξ hξ f‖ ^ 2 =
          ∑' n : ℕ, ‖(normalizedCoeffL2 ξ hξ f : ℕ → ℝ) n‖ ^ 2 := by
      -- start from the `rpow` version and convert `toReal 2` to the usual square.
      -- (`Real.rpow_natCast` turns `x^(2:ℝ)` into `x^2`.)
      simpa [htwo, Real.rpow_natCast] using hnorm
    -- Now substitute the inner-product expression for the coefficients.
    have hnorm2' :
        ‖normalizedCoeffL2 ξ hξ f‖ ^ 2 =
          ∑' n : ℕ,
            ‖⟪normalizedEigenfunctionSpaceTimeL2 (ξ := ξ) hξ n,
                f.toLp 2 (volume : Measure SpaceTime)⟫‖ ^ 2 := by
      have hcoeff2 :
          (fun n : ℕ => ‖(normalizedCoeffL2 ξ hξ f : ℕ → ℝ) n‖ ^ 2) =
            (fun n : ℕ =>
              ‖⟪normalizedEigenfunctionSpaceTimeL2 (ξ := ξ) hξ n,
                  f.toLp 2 (volume : Measure SpaceTime)⟫‖ ^ 2) := by
        funext n
        have hn := congrArg (fun g : ℕ → ℝ => g n) hcoeff
        -- Convert `toReal 2`-powers to ordinary squares, keeping norms explicit.
        -- We rewrite `2 : ℝ` as `(2 : ℕ)` and then use `Real.rpow_natCast`.
        have htwo' : (2 : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
        -- Avoid unfolding the inner product further.
        simpa only [htwo, htwo', Real.rpow_natCast] using hn
      simp only [hnorm2, hcoeff2]
    -- Conclude.
    simpa [hnorm2'] using hbessel
  -- Now take square roots.
  have hn0 : 0 ≤ ‖normalizedCoeffL2 ξ hξ f‖ := norm_nonneg _
  have hf0 : 0 ≤ ‖f.toLp 2 (volume : Measure SpaceTime)‖ := norm_nonneg _
  -- `a^2 ≤ b^2` with `a,b ≥ 0` implies `a ≤ b`, using square roots.
  have hsqrt := Real.sqrt_le_sqrt hsq
  -- `sqrt (‖x‖^2) = ‖x‖` since norms are nonnegative.
  simpa [Real.sqrt_sq, abs_of_nonneg hn0, abs_of_nonneg hf0] using hsqrt

/-! ## Relating coefficient seminorms to `L²` bounds -/

lemma coeffToL2ₗ_eq_normalizedCoeffL2_numAllPowCLM (ξ : ℝ) (hξ : ξ ≠ 0) (k : ℕ) (f : TestFunction) :
    coeffToL2ₗ (ξ := ξ) hξ k f = normalizedCoeffL2 ξ hξ (numAllPowCLM ξ k f) := by
  ext n
  -- Both sides are the weighted normalized coefficient at `n`.
  simp only [coeffToL2ₗ_apply, normalizedCoeffL2_apply, normalizedCoeffCLM_SpaceTime_pi_apply,
    normalizedCoeffCLM_SpaceTime_numAllPowCLM]

lemma coeffSeminormSeq_eq_norm_normalizedCoeffL2_numAllPowCLM (ξ : ℝ) (hξ : ξ ≠ 0) (k : ℕ) (f : TestFunction) :
    coeffSeminormSeq ξ hξ k f = ‖normalizedCoeffL2 ξ hξ (numAllPowCLM ξ k f)‖ := by
  -- Avoid unfolding to integrals: rewrite through the `ℓ²` map `coeffToL2ₗ`.
  rw [coeffSeminormSeq_eq_norm_comp]
  -- Now rewrite the coefficient `ℓ²` element itself.
  simp [coeffToL2ₗ_eq_normalizedCoeffL2_numAllPowCLM (ξ := ξ) (hξ := hξ) (k := k) (f := f)]

lemma coeffSeminormSeq_eq_norm_toLp_numAllPowCLM (ξ : ℝ) (hξ : ξ ≠ 0) (k : ℕ) (f : TestFunction) :
    coeffSeminormSeq ξ hξ k f = ‖(numAllPowCLM ξ k f).toLp 2 (volume : Measure SpaceTime)‖ := by
  rw [coeffSeminormSeq_eq_norm_normalizedCoeffL2_numAllPowCLM (ξ := ξ) (hξ := hξ) (k := k) (f := f)]
  simpa using
    (norm_normalizedCoeffL2_eq_norm_toLp (ξ := ξ) (hξ := hξ) (f := numAllPowCLM ξ k f))

lemma coeffSeminormSeq_le_norm_toLp_numAllPowCLM (ξ : ℝ) (hξ : ξ ≠ 0) (k : ℕ) (f : TestFunction) :
    coeffSeminormSeq ξ hξ k f ≤ ‖(numAllPowCLM ξ k f).toLp 2 (volume : Measure SpaceTime)‖ := by
  -- Bessel inequality for the orthonormal family of eigenfunctions.
  rw [coeffSeminormSeq_eq_norm_normalizedCoeffL2_numAllPowCLM (ξ := ξ) (hξ := hξ) (k := k) (f := f)]
  exact norm_normalizedCoeffL2_le_norm_toLp (ξ := ξ) (hξ := hξ) (f := numAllPowCLM ξ k f)

/-! ## `coeffSeminormSeq` is bounded by the canonical Schwartz seminorm sequence -/

theorem isBounded_schwartzSeminormSeq_coeffSeminormSeq (ξ : ℝ) (hξ : ξ ≠ 0) :
    Seminorm.IsBounded OSforGFF.schwartzSeminormSeq (coeffSeminormSeq ξ hξ)
      (LinearMap.id : TestFunction →ₗ[ℝ] TestFunction) := by
  classical
  -- First, bound `‖g.toLp 2‖` by a fixed Schwartz seminorm `schwartzSeminormSeq K`.
  rcases
      (SchwartzMap.norm_toLp_le_seminorm (𝕜 := ℝ) (F := ℝ) (E := SpaceTime)
        (p := (2 : ℝ≥0∞)) (μ := (volume : Measure SpaceTime)))
    with ⟨K, C, hC0, hC⟩
  have htoLp :
      ∀ g : TestFunction,
        ‖g.toLp 2 (volume : Measure SpaceTime)‖ ≤ C * OSforGFF.schwartzSeminormSeq K g := by
    intro g
    have hsubset : Finset.Iic (K, 0) ⊆ Finset.Iic (K, K) := by
      intro i hi
      have hi' : i ≤ (K, 0) := Finset.mem_Iic.mp hi
      have hKK : (K, 0) ≤ (K, K) := Prod.mk_le_mk.2 ⟨le_rfl, Nat.zero_le _⟩
      exact Finset.mem_Iic.mpr (le_trans hi' hKK)
    have hsup :
        (Finset.Iic (K, 0)).sup (OSforGFF.schwartzSeminormFamily_TestFunction) g
          ≤ OSforGFF.schwartzSeminormSeq K g := by
      -- This is just `Finset.sup_mono` along the inclusion of index sets.
      have hsup' :
          (Finset.Iic (K, 0)).sup (OSforGFF.schwartzSeminormFamily_TestFunction) ≤
            (Finset.Iic (K, K)).sup (OSforGFF.schwartzSeminormFamily_TestFunction) :=
        Finset.sup_mono hsubset
      simpa [OSforGFF.schwartzSeminormSeq] using (hsup' g)
    -- Combine `hC` with the bound on the finite sup.
    have := hC g
    exact this.trans (mul_le_mul_of_nonneg_left hsup hC0)
  let Cnn : ℝ≥0 := ⟨C, hC0⟩
  intro k
  -- Control `schwartzSeminormSeq K (numAllPowCLM ξ k f)` by finitely many Schwartz seminorms of `f`.
  have hcont :
      Continuous
        ((OSforGFF.schwartzSeminormSeq K).comp
          ((numAllPowCLM ξ k : TestFunction →L[ℝ] TestFunction) : TestFunction →ₗ[ℝ] TestFunction)) := by
    -- Continuity of a generating seminorm, composed with a continuous linear map.
    exact (OSforGFF.schwartzSeminormSeq_withSeminorms.continuous_seminorm K).comp
      (numAllPowCLM ξ k).continuous
  rcases
      (Seminorm.bound_of_continuous (p := OSforGFF.schwartzSeminormSeq) (E := TestFunction)
        OSforGFF.schwartzSeminormSeq_withSeminorms
        ((OSforGFF.schwartzSeminormSeq K).comp
          ((numAllPowCLM ξ k : TestFunction →L[ℝ] TestFunction) : TestFunction →ₗ[ℝ] TestFunction)) hcont)
    with ⟨s, C₁, _hC₁ne, hle⟩
  refine ⟨s, Cnn * C₁, ?_⟩
  -- Now show the coefficient seminorm is bounded by the resulting finite sup.
  intro f
  have h₁ :
      coeffSeminormSeq ξ hξ k f ≤ ‖(numAllPowCLM ξ k f).toLp 2 (volume : Measure SpaceTime)‖ :=
    coeffSeminormSeq_le_norm_toLp_numAllPowCLM (ξ := ξ) (hξ := hξ) (k := k) (f := f)
  have h₂ :
      ‖(numAllPowCLM ξ k f).toLp 2 (volume : Measure SpaceTime)‖ ≤
        (Cnn : ℝ) * OSforGFF.schwartzSeminormSeq K (numAllPowCLM ξ k f) := by
    -- `htoLp` is stated with the real constant `C`; rewrite it as an `ℝ≥0` constant.
    simpa [Cnn] using (htoLp (g := numAllPowCLM ξ k f))
  have h₃ :
      OSforGFF.schwartzSeminormSeq K (numAllPowCLM ξ k f) ≤
        (C₁ : ℝ) * (s.sup OSforGFF.schwartzSeminormSeq) f := by
    -- Evaluate the seminorm inequality `hle` at `f`.
    simpa [Seminorm.comp_apply, Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul, mul_assoc] using
      (hle f)
  have h₄ :
      coeffSeminormSeq ξ hξ k f ≤ ((Cnn * C₁ : ℝ≥0) • s.sup OSforGFF.schwartzSeminormSeq) f := by
    -- Chain the inequalities and fold scalars back into `•`.
    have h12 := h₁.trans h₂
    have h123 :
        coeffSeminormSeq ξ hξ k f ≤ (Cnn : ℝ) * ((C₁ : ℝ) * (s.sup OSforGFF.schwartzSeminormSeq) f) := by
      have h23 :
          (Cnn : ℝ) * OSforGFF.schwartzSeminormSeq K (numAllPowCLM ξ k f) ≤
            (Cnn : ℝ) * ((C₁ : ℝ) * (s.sup OSforGFF.schwartzSeminormSeq) f) :=
        mul_le_mul_of_nonneg_left h₃ (by exact_mod_cast (zero_le Cnn))
      exact h12.trans h23
    -- Rewrite the RHS as a scalar multiple of the seminorm.
    simpa [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using h123
  -- The required form is exactly `hle` after composing with `LinearMap.id`.
  simpa using h₄

/-! Once we also know the **reverse** boundedness `schwartzSeminormSeq ≲ coeffSeminormSeq`,
the remaining hypothesis `OSforGFF.SchwartzNuclearInclusion` follows from the proved local
nuclearity of the coefficient inclusions.

This reverse boundedness is proved in `OSforGFF.NuclearSpace.PhysHermiteSpaceTimeSchwartzToCoeffBound`,
so combining the two directions yields `OSforGFF.SchwartzNuclearInclusion` (and hence
`OSforGFF.NuclearSpaceStd TestFunction`) in the spacetime Hermite model; see
`OSforGFF.NuclearSpace.PhysHermiteSpaceTimeSchwartzNuclearInclusion`.
-/
theorem schwartzNuclearInclusion_of_equiv_coeffSeminormSeq
    (ξ : ℝ) (hξ : ξ ≠ 0)
    (hb_sch_le_coeff :
      Seminorm.IsBounded (coeffSeminormSeq ξ hξ) OSforGFF.schwartzSeminormSeq
        (LinearMap.id : TestFunction →ₗ[ℝ] TestFunction)) :
    OSforGFF.SchwartzNuclearInclusion := by
  classical
  refine
    OSforGFF.schwartzNuclearInclusion_of_equivFamily
      (q := coeffSeminormSeq ξ hξ)
      (hqmono := coeffSeminormSeq_mono (ξ := ξ) (hξ := hξ))
      (hb_q_le_sch := isBounded_schwartzSeminormSeq_coeffSeminormSeq (ξ := ξ) (hξ := hξ))
      (hb_sch_le_q := hb_sch_le_coeff)
      (hqNuclear := coeffSeminormSeq_localNuclear (ξ := ξ) (hξ := hξ))

end SpaceTimeHermite

end

end PhysLean

