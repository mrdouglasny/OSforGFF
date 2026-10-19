/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Copyright (c) 2026 Sergey A. Cherkis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sergey A. Cherkis, Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/
module

public import OSforGFF.Spacetime.Basic
public import OSforGFF.Spacetime.ProdIntegrable

/-!
# Spacetime Decomposition

This file provides the measure-preserving decomposition of `SpaceTime d` into
time and spatial components: `SpaceTime d ≃ᵐ ℝ × SpatialCoords d`.

## Main Definitions

* `piLpMeasurableEquiv` - MeasurableEquiv between PiLp and underlying pi type
* `spacetimeDecomp` - The measurable equivalence `SpaceTime d ≃ᵐ ℝ × SpatialCoords d`

## Main Results

* `spacetimeDecomp_measurePreserving` - The decomposition preserves Lebesgue measure
* `spacetimeDecomp_apply` - Explicit formula: spacetimeDecomp k = (k 0, spatialPart k)
* `spacetime_norm_sq_decompose` - Norm decomposition: ‖k‖² = k₀² + ‖k_sp‖²
-/

@[expose] public section

open MeasureTheory MeasureSpace FiniteDimensional Real

/-! ### Integral Decomposition for `SpaceTime d`

We establish that integrals over `SpaceTime d` can be decomposed into
iterated integrals over ℝ (time component) and `SpatialCoords d` (spatial components).
This uses `MeasurableEquiv.piFinSuccAbove` and `measurePreserving_piFinSuccAbove`.

-/

variable {d : ℕ} [Fact (2 ≤ d)]

/-- MeasurableEquiv between PiLp and the underlying pi type. -/
def piLpMeasurableEquiv (n : ℕ) : PiLp 2 (fun _ : Fin n => ℝ) ≃ᵐ (Fin n → ℝ) where
  toEquiv := WithLp.equiv 2 _
  measurable_toFun := WithLp.measurable_ofLp 2 _
  measurable_invFun := WithLp.measurable_toLp 2 _

/-- Reindexing along `d = (d - 1) + 1` as a measurable equivalence of pi types. -/
def finSplitMeasurableEquiv :
    (Fin d → ℝ) ≃ᵐ (Fin (d - 1 + 1) → ℝ) :=
  MeasurableEquiv.piCongrLeft (fun _ => ℝ)
    (finCongr (show d = d - 1 + 1 by have h : 2 ≤ d := Fact.out; omega))

/-- The measurable equivalence from `SpaceTime d` to `ℝ × SpatialCoords d`.
    Composes four measure-preserving maps:
    1. piLpMeasurableEquiv : EuclideanSpace ℝ (Fin d) → (Fin d → ℝ)
    2. finSplitMeasurableEquiv : (Fin d → ℝ) → (Fin ((d-1)+1) → ℝ)
    3. piFinSuccAbove 0 : (Fin ((d-1)+1) → ℝ) → ℝ × (Fin (d-1) → ℝ)
    4. id × piLpMeasurableEquiv.symm : ℝ × (Fin (d-1) → ℝ) → ℝ × SpatialCoords d -/
def spacetimeDecomp : SpaceTime d ≃ᵐ ℝ × SpatialCoords d :=
  (piLpMeasurableEquiv d).trans
  ((finSplitMeasurableEquiv.trans
    (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0)).trans
  (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
    (piLpMeasurableEquiv (d - 1)).symm))

/-- Measure preservation for piLpMeasurableEquiv. -/
lemma piLpMeasurableEquiv_measurePreserving (n : ℕ) :
    MeasurePreserving (piLpMeasurableEquiv n)
      (volume : Measure (PiLp 2 (fun _ : Fin n => ℝ))) volume := by
  simp only [piLpMeasurableEquiv, MeasurableEquiv.coe_mk]
  exact PiLp.volume_preserving_ofLp (ι := Fin n)

/-- The spacetime decomposition preserves measure. -/
theorem spacetimeDecomp_measurePreserving :
    MeasurePreserving (spacetimeDecomp (d := d)) (volume : Measure (SpaceTime d)) volume := by
  unfold spacetimeDecomp
  -- Step 1: PiLp → (Fin d → ℝ) is measure-preserving
  have h1 : MeasurePreserving (piLpMeasurableEquiv d)
      (volume : Measure (SpaceTime d)) volume :=
    piLpMeasurableEquiv_measurePreserving d
  -- Step 1b: reindexing along d = (d-1)+1 is measure-preserving
  have h1b : MeasurePreserving (finSplitMeasurableEquiv (d := d))
      (volume : Measure (Fin d → ℝ)) volume :=
    volume_measurePreserving_piCongrLeft _ _
  -- Step 2: piFinSuccAbove 0 is measure-preserving
  have h2 : MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0)
      (volume : Measure (Fin (d - 1 + 1) → ℝ)) volume :=
    measurePreserving_piFinSuccAbove (fun _ => volume) 0
  -- Step 3: id × piLpMeasurableEquiv.symm is measure-preserving
  have h3 : MeasurePreserving
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
        (piLpMeasurableEquiv (d - 1)).symm)
      (volume : Measure (ℝ × (Fin (d - 1) → ℝ))) volume := by
    apply MeasurePreserving.prod
    · exact MeasurePreserving.id volume
    · simp only [piLpMeasurableEquiv, MeasurableEquiv.symm_mk]
      exact PiLp.volume_preserving_toLp (ι := Fin (d - 1))
  exact h1.trans ((h1b.trans h2).trans h3)

/-- Spacetime decomposition maps k to (k 0, spatialPart k). -/
theorem spacetimeDecomp_apply (k : SpaceTime d) :
    spacetimeDecomp k = (k 0, spatialPart k) := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by have h : 2 ≤ d := Fact.out; omega⟩
  rfl

/-- `spacetimeDecomp.symm` equals `spacetimeOfTimeSpace` (from ProdIntegrable.lean).
    Both construct a spacetime point from time t and spatial coordinates v. -/
lemma spacetimeDecomp_symm_eq_spacetimeOfTimeSpace (t : ℝ) (v : SpatialCoords d) :
    spacetimeDecomp.symm (t, v) = spacetimeOfTimeSpace t v := by
  have h_apply : spacetimeDecomp (spacetimeDecomp.symm (t, v)) = (t, v) :=
    spacetimeDecomp.apply_symm_apply (t, v)
  rw [spacetimeDecomp_apply] at h_apply
  have h_time : (spacetimeDecomp.symm (t, v) : SpaceTime d) 0 = t :=
    congr_arg Prod.fst h_apply
  have h_spatial : spatialPart (spacetimeDecomp.symm (t, v)) = v :=
    congr_arg Prod.snd h_apply
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by have h : 2 ≤ d := Fact.out; omega⟩
  ext i
  cases' i using Fin.cases with j
  · -- i = 0: time component
    rw [show spacetimeOfTimeSpace t v 0 = t from spacetimeOfTimeSpace_time t v]
    exact h_time
  · -- i = j + 1: spatial components
    rw [show ((spacetimeDecomp.symm (t, v) : SpaceTime (n + 1)) j.succ)
          = spatialPart (spacetimeDecomp.symm (t, v)) j from rfl, h_spatial]
    exact (spacetimeOfTimeSpace_spatial t v j).symm

/-- The spacetime norm decomposes into time and spatial parts: ‖k‖² = k₀² + ‖k_sp‖². -/
lemma spacetime_norm_sq_decompose (k : SpaceTime d) :
    ‖k‖^2 = (k 0)^2 + ‖spatialPart k‖^2 := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by have h : 2 ≤ d := Fact.out; omega⟩
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ]
  simp only [Real.norm_eq_abs, sq_abs]
  rfl

/-- For a product-type integrand f(k₀) × g(k_sp), the integral decomposes as a product. -/
lemma integral_spacetime_prod_split {f : ℝ → ℂ} {g : SpatialCoords d → ℂ}
    (_hf : Integrable f) (_hg : Integrable g) :
    ∫ k : SpaceTime d, f (k 0) * g (spatialPart k) =
    (∫ k₀ : ℝ, f k₀) * (∫ k_sp : SpatialCoords d, g k_sp) := by
  have h := spacetimeDecomp_measurePreserving.integral_comp' (fun p => f p.1 * g p.2)
  simp only [spacetimeDecomp_apply] at h
  rw [h]; exact integral_prod_mul f g
