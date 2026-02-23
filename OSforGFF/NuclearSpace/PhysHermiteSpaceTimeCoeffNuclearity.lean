/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import OSforGFF.NuclearSpace.PhysHermiteSpaceTimeCoeffSeminorm

/-!
# Nuclearity of the coefficient-seminorm local inclusions

For the coefficient seminorm sequence `coeffSeminormSeq ξ hξ : ℕ → Seminorm ℝ TestFunction`, we show
that the local Banach inclusion map from level `k+2` to level `k` is nuclear.

This is the analogue (on `TestFunction`) of the diagonal nuclearity argument used for
`RapidDecaySeqBase.space base`.
-/

open scoped BigOperators NNReal ENNReal

namespace PhysLean

noncomputable section

namespace SpaceTimeHermite

open MeasureTheory

local notation "H" => ℓ²(ℕ, ℝ)
local notation "base₄" => OSforGFF.RapidDecaySeqMulti.base₄

/-! ## The coefficient `toL2` map inducing the seminorm -/

/-- The linear map `TestFunction → ℓ²` sending `f` to the `k`-weighted normalized coefficient
sequence. This is the map whose norm induces `coeffSeminormSeq ξ hξ k`. -/
noncomputable def coeffToL2ₗ (ξ : ℝ) (hξ : ξ ≠ 0) (k : ℕ) : TestFunction →ₗ[ℝ] H :=
  (OSforGFF.RapidDecaySeqBase.Space.toL2ₗ (base := base₄) k).comp (normalizedCoeffRapidDecayₗ ξ hξ)

@[simp] lemma coeffToL2ₗ_apply (ξ : ℝ) (hξ : ξ ≠ 0) (k : ℕ) (f : TestFunction) (n : ℕ) :
    (coeffToL2ₗ (ξ := ξ) hξ k f : ℕ → ℝ) n =
      (base₄ n) ^ k * normalizedCoeffCLM_SpaceTime ξ hξ n f := by
  simp only [coeffToL2ₗ, LinearMap.comp_apply, OSforGFF.RapidDecaySeqBase.Space.toL2ₗ_apply,
    OSforGFF.RapidDecaySeqBase.weight, normalizedCoeffRapidDecayₗ_apply_apply]

@[simp] lemma coeffSeminormSeq_eq_norm_comp (ξ : ℝ) (hξ : ξ ≠ 0) (k : ℕ) (f : TestFunction) :
    coeffSeminormSeq ξ hξ k f = ‖coeffToL2ₗ (ξ := ξ) hξ k f‖ := by
  rfl

/-! ## Compatibility of weights: the key diagonal identity -/

lemma diagPowInvCLM_two_coeffToL2 (ξ : ℝ) (hξ : ξ ≠ 0) (k : ℕ) (f : TestFunction) :
    OSforGFF.RapidDecaySeqBase.Space.diagPowInvCLM (base := base₄) OSforGFF.RapidDecaySeqMulti.one_le_base₄ 2
        (coeffToL2ₗ (ξ := ξ) hξ (k + 2) f)
      =
    coeffToL2ₗ (ξ := ξ) hξ k f := by
  simpa [coeffToL2ₗ, normalizedCoeffRapidDecayₗ_apply] using
    (OSforGFF.RapidDecaySeqBase.Space.diagPowInvCLM_two_toL2 (base := base₄)
      (hbase := OSforGFF.RapidDecaySeqMulti.one_le_base₄) (k := k)
      (x := normalizedCoeffRapidDecay ξ hξ f))

/-!
## Nuclearity of the inclusion `Banach(k+2) → Banach(k)`

We follow the same structure as `RapidDecaySeqBase.Space.isNuclearMap_inclCLM_succ_succ`,
but we do *not* need surjectivity of the coefficient maps: we transport nuclearity through
their closed ranges.
-/

open scoped Topology

-- Force quotient topology to be the norm-induced one (avoid inheriting Schwartz quotient topology).
local instance (priority := 1001) (ξ : ℝ) (hξ : ξ ≠ 0) (k : ℕ) :
    TopologicalSpace (OSforGFF.QuotBySeminorm (E := TestFunction) (coeffSeminormSeq ξ hξ k)) :=
  (PseudoMetricSpace.toUniformSpace.toTopologicalSpace :
    TopologicalSpace (OSforGFF.QuotBySeminorm (E := TestFunction) (coeffSeminormSeq ξ hξ k)))

/-! ### The induced map on the quotient -/

noncomputable def coeffToL2Quotₗ (ξ : ℝ) (hξ : ξ ≠ 0) (k : ℕ) :
    OSforGFF.QuotBySeminorm (E := TestFunction) (coeffSeminormSeq ξ hξ k) →ₗ[ℝ] H :=
  (OSforGFF.seminormKer (E := TestFunction) (p := coeffSeminormSeq ξ hξ k)).liftQ
    (coeffToL2ₗ (ξ := ξ) hξ k) (by
      intro f hf
      have hf0 : coeffSeminormSeq ξ hξ k f = 0 := hf
      have : ‖coeffToL2ₗ (ξ := ξ) hξ k f‖ = 0 := by
        simpa [coeffSeminormSeq_eq_norm_comp (ξ := ξ) (hξ := hξ) (k := k) (f := f)] using hf0
      exact (norm_eq_zero.mp this))

@[simp] lemma coeffToL2Quotₗ_mk (ξ : ℝ) (hξ : ξ ≠ 0) (k : ℕ) (f : TestFunction) :
    coeffToL2Quotₗ (ξ := ξ) hξ k
        (Submodule.Quotient.mk (p := OSforGFF.seminormKer (E := TestFunction) (p := coeffSeminormSeq ξ hξ k)) f) =
      coeffToL2ₗ (ξ := ξ) hξ k f := by
  simp [coeffToL2Quotₗ]

lemma norm_coeffToL2Quotₗ (ξ : ℝ) (hξ : ξ ≠ 0) (k : ℕ)
    (x : OSforGFF.QuotBySeminorm (E := TestFunction) (coeffSeminormSeq ξ hξ k)) :
    ‖coeffToL2Quotₗ (ξ := ξ) hξ k x‖ = ‖x‖ := by
  refine Submodule.Quotient.induction_on
    (p := OSforGFF.seminormKer (E := TestFunction) (p := coeffSeminormSeq ξ hξ k)) x ?_
  intro f
  -- both norms are induced from the same seminorm
  have hx :
      ‖(Submodule.Quotient.mk
          (p := OSforGFF.seminormKer (E := TestFunction) (p := coeffSeminormSeq ξ hξ k)) f :
        OSforGFF.QuotBySeminorm (E := TestFunction) (coeffSeminormSeq ξ hξ k))‖ =
        coeffSeminormSeq ξ hξ k f := by
    simpa using (OSforGFF.QuotBySeminorm.norm_mk (E := TestFunction) (p := coeffSeminormSeq ξ hξ k) f)
  calc
    ‖coeffToL2Quotₗ (ξ := ξ) hξ k
        (Submodule.Quotient.mk
          (p := OSforGFF.seminormKer (E := TestFunction) (p := coeffSeminormSeq ξ hξ k)) f)‖
        = ‖coeffToL2ₗ (ξ := ξ) hξ k f‖ := by simp [coeffToL2Quotₗ_mk]
    _ = coeffSeminormSeq ξ hξ k f := by rfl
    _ = ‖(Submodule.Quotient.mk
          (p := OSforGFF.seminormKer (E := TestFunction) (p := coeffSeminormSeq ξ hξ k)) f :
        OSforGFF.QuotBySeminorm (E := TestFunction) (coeffSeminormSeq ξ hξ k))‖ := by
          simp [hx]

/-! ### An isometric identification with the closed range -/

noncomputable def banachEquivL2Coeff (ξ : ℝ) (hξ : ξ ≠ 0) (k : ℕ) :
    OSforGFF.BanachOfSeminorm (E := TestFunction) (coeffSeminormSeq ξ hξ k) ≃ₗᵢ[ℝ]
      (LinearMap.range (coeffToL2Quotₗ (ξ := ξ) hξ k)).topologicalClosure := by
  -- Copy the `RapidDecaySeqBase.Space.banachEquivL2` pattern, but target the closed range.
  let E : Type :=
    OSforGFF.QuotBySeminorm (E := TestFunction) (coeffSeminormSeq ξ hξ k)
  let T : E →ₗ[ℝ] H := coeffToL2Quotₗ (ξ := ξ) hξ k
  let F : Submodule ℝ H := LinearMap.range T
  let Fc : Submodule ℝ H := F.topologicalClosure
  have hTnorm : ∀ x : E, ‖T x‖ = ‖x‖ := fun x => by
    simpa [T] using (norm_coeffToL2Quotₗ (ξ := ξ) (hξ := hξ) (k := k) x)
  have hTinj : Function.Injective T := by
    intro x y hxy
    have : T (x - y) = 0 := by simp [map_sub, hxy]
    have h0 : ‖T (x - y)‖ = 0 := by simpa using congrArg (fun z : H => ‖z‖) this
    have hnorm0 : ‖x - y‖ = 0 := by
      calc
        ‖x - y‖ = ‖T (x - y)‖ := (hTnorm (x - y)).symm
        _ = 0 := h0
    simpa using sub_eq_zero.mp (norm_eq_zero.mp hnorm0)
  let f : E ≃ₗ[ℝ] F := LinearEquiv.ofInjective T hTinj
  let e₁ : E →ₗ[ℝ] OSforGFF.BanachOfSeminorm (E := TestFunction) (coeffSeminormSeq ξ hξ k) :=
    (OSforGFF.BanachOfSeminorm.coeCLM (E := TestFunction) (coeffSeminormSeq ξ hξ k)).toLinearMap
  have h_dense₁ : DenseRange e₁ := by
    simpa [e₁] using
      (OSforGFF.BanachOfSeminorm.denseRange_coeCLM (E := TestFunction) (p := coeffSeminormSeq ξ hξ k))
  have hFFc : F ≤ Fc := Submodule.le_topologicalClosure F
  let e₂ : F →ₗ[ℝ] Fc := Submodule.inclusion hFFc
  have h_dense₂ : DenseRange e₂ := by
    have : DenseRange (Set.inclusion (show (F : Set H) ⊆ (Fc : Set H) from hFFc)) := by
      refine (denseRange_inclusion_iff (hst := (show (F : Set H) ⊆ (Fc : Set H) from hFFc))).2 ?_
      simpa only [Fc, Submodule.topologicalClosure_coe] using
        (subset_refl (closure (F : Set H)))
    simpa [e₂, Submodule.inclusion, Set.inclusion] using this
  have h_norm : ∀ x : E, ‖e₂ (f x)‖ = ‖e₁ x‖ := by
    intro x
    have hleft : ‖e₂ (f x)‖ = ‖T x‖ := by
      rfl
    have hright : ‖e₁ x‖ = ‖x‖ := by
      simp [e₁, OSforGFF.BanachOfSeminorm.coeCLM]
    simp [hleft, hright, hTnorm x, T, e₂]
  exact (f.extendOfIsometry (σ₁₂ := RingHom.id ℝ) e₁ e₂ h_dense₁ h_dense₂ h_norm)

@[simp]
lemma banachEquivL2Coeff_apply_coe (ξ : ℝ) (hξ : ξ ≠ 0) (k : ℕ)
    (x : OSforGFF.QuotBySeminorm (E := TestFunction) (coeffSeminormSeq ξ hξ k)) :
    ((banachEquivL2Coeff (ξ := ξ) hξ k
          (OSforGFF.BanachOfSeminorm.coeCLM (E := TestFunction) (coeffSeminormSeq ξ hξ k) x)) : H)
      = coeffToL2Quotₗ (ξ := ξ) hξ k x := by
  classical
  -- Make the dense-set argument visible to `LinearEquiv.extendOfIsometry_eq`.
  change
      ((banachEquivL2Coeff (ξ := ξ) hξ k)
          ((↑(OSforGFF.BanachOfSeminorm.coeCLM (E := TestFunction) (coeffSeminormSeq ξ hξ k)) :
              OSforGFF.QuotBySeminorm (E := TestFunction) (coeffSeminormSeq ξ hξ k) →ₗ[ℝ]
                OSforGFF.BanachOfSeminorm (E := TestFunction) (coeffSeminormSeq ξ hξ k)) x) : H)
        = coeffToL2Quotₗ (ξ := ξ) hξ k x
  -- Unfold the construction.
  simp (config := { zeta := true }) [banachEquivL2Coeff]
  have hx :
      (OSforGFF.BanachOfSeminorm.coeCLM (E := TestFunction) (coeffSeminormSeq ξ hξ k) x) =
        ((↑(OSforGFF.BanachOfSeminorm.coeCLM (E := TestFunction) (coeffSeminormSeq ξ hξ k)) :
            OSforGFF.QuotBySeminorm (E := TestFunction) (coeffSeminormSeq ξ hξ k) →ₗ[ℝ]
              OSforGFF.BanachOfSeminorm (E := TestFunction) (coeffSeminormSeq ξ hξ k)) x) := rfl
  rw [hx]
  -- Evaluate the extension on the dense range of `coeCLM`.
  rw [LinearEquiv.extendOfIsometry_eq]
  -- Now we are simply looking at the inclusion of a range element into its closure.
  simp

/-! ### Nuclearity of the local inclusion -/

set_option maxHeartbeats 400000 in
theorem isNuclearMap_inclCLM_coeffSeminormSeq_succ_succ (ξ : ℝ) (hξ : ξ ≠ 0) (k : ℕ) :
    OSforGFF.IsNuclearMap
      (OSforGFF.BanachOfSeminorm.inclCLM (E := TestFunction)
        (p := coeffSeminormSeq ξ hξ (k + 2))
        (q := coeffSeminormSeq ξ hξ k)
        (coeffSeminormSeq_mono (ξ := ξ) (hξ := hξ) (Nat.le_add_right k 2))) := by
  -- we conjugate the inclusion to the diagonal map on `ℓ²`, restricted to closed ranges.
  classical
  let E₀ := OSforGFF.BanachOfSeminorm (E := TestFunction) (coeffSeminormSeq ξ hξ (k + 2))
  let E₁ := OSforGFF.BanachOfSeminorm (E := TestFunction) (coeffSeminormSeq ξ hξ k)
  have hpq : coeffSeminormSeq ξ hξ k ≤ coeffSeminormSeq ξ hξ (k + 2) :=
    coeffSeminormSeq_mono (ξ := ξ) (hξ := hξ) (Nat.le_add_right k 2)
  let incl : E₀ →L[ℝ] E₁ :=
    OSforGFF.BanachOfSeminorm.inclCLM (E := TestFunction)
      (p := coeffSeminormSeq ξ hξ (k + 2))
      (q := coeffSeminormSeq ξ hξ k) hpq
  -- Isometries onto closed ranges
  let iso₀ := banachEquivL2Coeff (ξ := ξ) hξ (k := k + 2)
  let iso₁ := banachEquivL2Coeff (ξ := ξ) hξ (k := k)
  -- Coercions: `ContinuousLinearEquiv` → `ContinuousLinearMap`
  let iso₀L : E₀ →L[ℝ] _ := (iso₀.toContinuousLinearEquiv : E₀ ≃L[ℝ] _).toContinuousLinearMap
  let iso₁L : E₁ →L[ℝ] _ := (iso₁.toContinuousLinearEquiv : E₁ ≃L[ℝ] _).toContinuousLinearMap
  let iso₁Linv : _ →L[ℝ] E₁ := (iso₁.symm.toContinuousLinearEquiv : _ ≃L[ℝ] E₁).toContinuousLinearMap
  -- Closed ranges for the coefficient `toL2` maps at levels `k+2` and `k`.
  let Fc₀ : Submodule ℝ H := (LinearMap.range (coeffToL2Quotₗ (ξ := ξ) hξ (k + 2))).topologicalClosure
  let Fc₁ : Submodule ℝ H := (LinearMap.range (coeffToL2Quotₗ (ξ := ξ) hξ k)).topologicalClosure
  -- Diagonal map on `ℓ²` corresponding to the weight drop `(k+2) ↦ k`.
  let diag : H →L[ℝ] H :=
    OSforGFF.RapidDecaySeqBase.Space.diagPowInvCLM (base := base₄)
      OSforGFF.RapidDecaySeqMulti.one_le_base₄ 2
  -- Map between the closed ranges, implemented via orthogonal projection.
  let diagClosed : Fc₀ →L[ℝ] Fc₁ := (Fc₁.orthogonalProjection).comp (diag.comp Fc₀.subtypeL)
  -- Diagonal nuclear map on `ℓ²`
  have hsum_sigma :
      Summable (fun n : ℕ =>
        ‖OSforGFF.RapidDecaySeqBase.Space.sigma (base := base₄) 2 n‖) := by
    -- same computation as in `RapidDecaySeqBase`: `‖sigma 2 n‖ = (base₄ n ^ 2)⁻¹`
    have hpos : ∀ n, 0 < base₄ n := OSforGFF.RapidDecaySeqMulti.base₄_pos
    have hnorm :
        (fun n : ℕ => ‖OSforGFF.RapidDecaySeqBase.Space.sigma (base := base₄) 2 n‖) =
          fun n : ℕ => (base₄ n ^ 2)⁻¹ := by
      funext n
      have hposw : 0 < OSforGFF.RapidDecaySeqBase.weight (base := base₄) 2 n := by
        simpa [OSforGFF.RapidDecaySeqBase.weight] using pow_pos (hpos n) 2
      have hposInv : 0 < (OSforGFF.RapidDecaySeqBase.weight (base := base₄) 2 n)⁻¹ :=
        inv_pos_of_pos hposw
      simp [OSforGFF.RapidDecaySeqBase.Space.sigma, OSforGFF.RapidDecaySeqBase.weight,
        Real.norm_eq_abs]
    rw [hnorm]
    exact OSforGFF.RapidDecaySeqMulti.summable_inv_sq_base₄
  have h_diag :
      OSforGFF.IsNuclearMap
        (OSforGFF.RapidDecaySeqBase.Space.diagPowInvCLM (base := base₄)
          OSforGFF.RapidDecaySeqMulti.one_le_base₄ 2) :=
    OSforGFF.RapidDecaySeqBase.Space.isNuclearMap_diagPowInvCLM_of_summable
      (base := base₄) OSforGFF.RapidDecaySeqMulti.one_le_base₄ 2 hsum_sigma
  -- Show the conjugation identity on a dense set (range of `coeCLM`), then conclude by composition.
  have h_conj :
      iso₁L.comp incl =
        (diagClosed.comp iso₀L) := by
    apply ContinuousLinearMap.coeFn_injective
    -- It suffices to prove equality on the dense range of `coeCLM`.
    have hd :
        DenseRange
          (OSforGFF.BanachOfSeminorm.coeCLM (E := TestFunction) (coeffSeminormSeq ξ hξ (k + 2))) :=
      OSforGFF.BanachOfSeminorm.denseRange_coeCLM (E := TestFunction) (p := coeffSeminormSeq ξ hξ (k + 2))
    have hs :
        Dense
          (Set.range
            (OSforGFF.BanachOfSeminorm.coeCLM (E := TestFunction) (coeffSeminormSeq ξ hξ (k + 2)))) := by
      refine dense_iff_closure_eq.2 ?_
      exact (denseRange_iff_closure_range).1 hd
    refine Continuous.ext_on hs (by fun_prop) (by fun_prop) ?_
    rintro _ ⟨xq, rfl⟩
    refine Submodule.Quotient.induction_on
      (p := OSforGFF.seminormKer (E := TestFunction) (p := coeffSeminormSeq ξ hξ (k + 2))) xq ?_
    intro f
    -- Compare the two maps by coercion to `H`.
    apply Subtype.ext
    -- abbreviate the quotient representative
    let x : OSforGFF.QuotBySeminorm (E := TestFunction) (coeffSeminormSeq ξ hξ (k + 2)) :=
      Submodule.Quotient.mk f
    -- LHS: inclusion then `iso₁`
    have hL :
        ((iso₁L (incl (OSforGFF.BanachOfSeminorm.coeCLM (E := TestFunction)
              (coeffSeminormSeq ξ hξ (k + 2)) x))) : H) =
          coeffToL2ₗ (ξ := ξ) hξ k f := by
      -- Push the inclusion down to the quotient, then evaluate `iso₁` on the dense range.
      have hIncl :
          incl (OSforGFF.BanachOfSeminorm.coeCLM (E := TestFunction)
              (coeffSeminormSeq ξ hξ (k + 2)) x) =
            OSforGFF.BanachOfSeminorm.coeCLM (E := TestFunction)
              (coeffSeminormSeq ξ hξ k)
              (OSforGFF.QuotBySeminorm.inclCLM (E := TestFunction)
                (p := coeffSeminormSeq ξ hξ (k + 2))
                (q := coeffSeminormSeq ξ hξ k) hpq x) := by
        -- Avoid `simpa` here: `inclCLM_coeCLM` is a simp lemma and would rewrite itself to `True`.
        dsimp [incl]
        exact
          (OSforGFF.BanachOfSeminorm.inclCLM_coeCLM (E := TestFunction)
            (p := coeffSeminormSeq ξ hξ (k + 2)) (q := coeffSeminormSeq ξ hξ k) hpq x)
      -- Rewrite with `hIncl` and apply the evaluation lemma.
      rw [hIncl]
      -- Unfold `iso₁L`/`iso₁` only enough for `banachEquivL2Coeff_apply_coe` to fire.
      dsimp [iso₁L, iso₁]
      -- `simp` now reduces to the diagonal identity on the quotient representative `mk f`.
      -- (avoid `simpa using` here: the simp lemma would rewrite itself to `True`)
      rw [banachEquivL2Coeff_apply_coe (ξ := ξ) (hξ := hξ) (k := k)
        (x := OSforGFF.QuotBySeminorm.inclCLM (E := TestFunction)
          (p := coeffSeminormSeq ξ hξ (k + 2))
          (q := coeffSeminormSeq ξ hξ k) hpq x)]
      simp [OSforGFF.QuotBySeminorm.inclCLM_mk, x, coeffToL2Quotₗ_mk]
    -- RHS: `iso₀` then diagonal then projection
    have hiso₀ :
        ((iso₀L (OSforGFF.BanachOfSeminorm.coeCLM (E := TestFunction)
              (coeffSeminormSeq ξ hξ (k + 2)) x)) : H) =
          coeffToL2ₗ (ξ := ξ) hξ (k + 2) f := by
      -- evaluate `iso₀` on the dense range (avoid simp rewriting the lemma into `True`)
      have h :=
        (banachEquivL2Coeff_apply_coe (ξ := ξ) (hξ := hξ) (k := k + 2) (x := x))
      -- unfold `iso₀L`/`iso₀` so the left-hand side matches `h`
      dsimp [iso₀L, iso₀] at *
      -- rewrite the quotient term without triggering simp on `h` itself
      -- (since `banachEquivL2Coeff_apply_coe` is a simp lemma for the LHS).
      simpa only [x, coeffToL2Quotₗ_mk] using h
    have hdiag :
        diag (coeffToL2ₗ (ξ := ξ) hξ (k + 2) f) = coeffToL2ₗ (ξ := ξ) hξ k f := by
      simpa using (diagPowInvCLM_two_coeffToL2 (ξ := ξ) (hξ := hξ) (k := k) (f := f))
    -- show the diagonal output lies in `Fc₁`, hence projection is the identity
    have hmem :
        diag (coeffToL2ₗ (ξ := ξ) hξ (k + 2) f) ∈ Fc₁ := by
      -- it is already in the range, via the quotient point `mk f`
      have hr :
          coeffToL2Quotₗ (ξ := ξ) hξ k (Submodule.Quotient.mk f) ∈
            LinearMap.range (coeffToL2Quotₗ (ξ := ξ) hξ k) :=
        LinearMap.mem_range_self _ _
      have hr' :
          coeffToL2Quotₗ (ξ := ξ) hξ k (Submodule.Quotient.mk f) ∈ Fc₁ :=
        (Submodule.le_topologicalClosure _) hr
      -- rewrite the diagonal output using `hdiag`
      simpa [coeffToL2Quotₗ_mk, hdiag] using hr'
    have hproj :
        Fc₁.starProjection (diag (coeffToL2ₗ (ξ := ξ) hξ (k + 2) f)) =
          diag (coeffToL2ₗ (ξ := ξ) hξ (k + 2) f) :=
      (Fc₁.starProjection_eq_self_iff).2 hmem
    have hmem' : (coeffToL2ₗ (ξ := ξ) hξ k f) ∈ Fc₁ := by
      -- rewrite `hmem` using the diagonal identity
      simpa [hdiag] using hmem
    have hproj' : Fc₁.starProjection (coeffToL2ₗ (ξ := ξ) hξ k f) = coeffToL2ₗ (ξ := ξ) hξ k f :=
      (Fc₁.starProjection_eq_self_iff).2 hmem'
    have hR :
        ((diagClosed (iso₀L (OSforGFF.BanachOfSeminorm.coeCLM (E := TestFunction)
              (coeffSeminormSeq ξ hξ (k + 2)) x))) : H) =
          coeffToL2ₗ (ξ := ξ) hξ k f := by
      -- unfold `diagClosed`; coerce the orthogonal projection using the simp lemma
      -- `coe_orthogonalProjection_apply` (avoid the `starProjection_apply` loop).
      simp [diagClosed, ContinuousLinearMap.comp_apply, hiso₀, hproj', hdiag]
    -- Now conclude in `H`.
    calc
      ((iso₁L (incl (OSforGFF.BanachOfSeminorm.coeCLM (E := TestFunction)
            (coeffSeminormSeq ξ hξ (k + 2)) x))) : H)
          = coeffToL2ₗ (ξ := ξ) hξ k f := hL
      _ = ((diagClosed (iso₀L (OSforGFF.BanachOfSeminorm.coeCLM (E := TestFunction)
            (coeffSeminormSeq ξ hξ (k + 2)) x))) : H) := hR.symm
  have h_incl :
      incl = iso₁Linv.comp
        (diagClosed.comp iso₀L) := by
    -- First, insert `iso₁Linv ∘ iso₁L = id`.
    have h₁ : incl = iso₁Linv.comp (iso₁L.comp incl) := by
      ext y
      change incl y = iso₁.symm (iso₁ (incl y))
      simp
    -- Then rewrite using the conjugation identity `h_conj`.
    have h₂ :
        iso₁Linv.comp (iso₁L.comp incl) = iso₁Linv.comp (diagClosed.comp iso₀L) :=
      congrArg (fun T => iso₁Linv.comp T) h_conj
    exact h₁.trans h₂
  have h_diag_pre :
      OSforGFF.IsNuclearMap
        (diagClosed.comp iso₀L) := by
    -- `diag` is nuclear on `H`; pre/post-compose with bounded maps.
    have h_diag_sub :
        OSforGFF.IsNuclearMap
          (diag.comp Fc₀.subtypeL) :=
      OSforGFF.IsNuclearMap.comp_right (T := _)
        h_diag Fc₀.subtypeL
    have h_diag_proj :
        OSforGFF.IsNuclearMap
          ((Fc₁.orthogonalProjection).comp (diag.comp Fc₀.subtypeL)) :=
      OSforGFF.IsNuclearMap.comp_left (T := _)
        h_diag_sub Fc₁.orthogonalProjection
    exact OSforGFF.IsNuclearMap.comp_right (T := _) h_diag_proj iso₀L
  have h_all :
      OSforGFF.IsNuclearMap
        (iso₁Linv.comp (diagClosed.comp iso₀L)) :=
    OSforGFF.IsNuclearMap.comp_left (T := diagClosed.comp iso₀L) h_diag_pre iso₁Linv
  simpa [incl, ← h_incl] using h_all

/-! ### A convenience wrapper for `SchwartzNuclearInclusion` transfer -/

theorem coeffSeminormSeq_localNuclear (ξ : ℝ) (hξ : ξ ≠ 0) :
    ∀ n : ℕ, ∃ m : ℕ, ∃ hnm : n < m,
      OSforGFF.IsNuclearMap
        (OSforGFF.BanachOfSeminorm.inclCLM (E := TestFunction)
          (p := coeffSeminormSeq ξ hξ m)
          (q := coeffSeminormSeq ξ hξ n)
          ((coeffSeminormSeq_mono (ξ := ξ) (hξ := hξ)) (Nat.le_of_lt hnm))) := by
  intro n
  refine ⟨n + 2, Nat.lt_add_of_pos_right (n := n) (k := 2) (by decide : 0 < 2), ?_⟩
  -- Our main theorem gives the inclusion from `n+2` to `n`.
  simpa using (isNuclearMap_inclCLM_coeffSeminormSeq_succ_succ (ξ := ξ) (hξ := hξ) (k := n))

end SpaceTimeHermite

end

end PhysLean
