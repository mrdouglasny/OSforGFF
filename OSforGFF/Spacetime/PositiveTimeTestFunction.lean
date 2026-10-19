/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Copyright (c) 2026 Sergey A. Cherkis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sergey A. Cherkis, Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/
import Mathlib.Tactic  -- gives `ext` and `simp` power
import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.LinearAlgebra.TensorAlgebra.Basic

import OSforGFF.Spacetime.Basic
import OSforGFF.Spacetime.DiscreteSymmetry

/-!
# Positive Time Test Functions and Star Operations

This file defines test functions supported in the positive time region and implements
the star operation (complex conjugation composed with time reflection) for test functions.

## Main definitions

* `HasPositiveTime`: Predicate for spacetime points with positive time component
* `positiveTimeSet`: The set of all positive time points
* `(PositiveTimeTestFunction d)`: Test functions supported in the positive time region
* `starTestFunction`: Star operation combining time reflection and complex conjugation
* `starRingEnd_iteratedFDeriv_norm_eq`: Helper lemma for norm preservation under star operation

## Main results

* `Star (SchwartzTestFunctionℂ d)`: Star instance for complex test functions
-/

noncomputable section

open TopologicalSpace Function SchwartzMap QFT

variable {d : ℕ} [Fact (2 ≤ d)]

/-- A spacetime point has positive time if its time component is positive -/
def HasPositiveTime (x : (SpaceTime d)) : Prop := getTimeComponent x > 0

/-- The set of all spacetime points with positive time -/
def positiveTimeSet : Set (SpaceTime d) := {x | HasPositiveTime x}

/-- Submodule of **real-valued** test functions supported in the positive time region -/
def PositiveTimeTestFunctions.submodule : Submodule ℝ (SchwartzTestFunction d) where
  carrier := { f : (SchwartzTestFunction d) | tsupport f ⊆ positiveTimeSet }
  zero_mem' := by
    simp only [Set.mem_ofPred_eq]
    suffices h : tsupport (0 : (SchwartzTestFunction d)) = ∅ by
      rw [h]
      apply Set.empty_subset
    rw [tsupport_eq_empty_iff]
    rfl
  add_mem' := fun {f g} hf hg => Set.Subset.trans (tsupport_add f g) (Set.union_subset hf hg)
  smul_mem' := by
    intro c f hf
    refine (tsupport_smul_subset_right (fun _ : (SpaceTime d) => c) f).trans hf

/-- Type of real-valued test functions supported in the positive time region -/
abbrev PositiveTimeTestFunction (d : ℕ) [Fact (2 ≤ d)] : Type :=
  PositiveTimeTestFunctions.submodule (d := d)

/-- Linear combinations of positive-time test functions are positive-time test functions. -/
lemma PositiveTimeTestFunction.sum_smul_mem
    {n : ℕ} (f : Fin n → (PositiveTimeTestFunction d)) (c : Fin n → ℝ) :
    ∃ g : (PositiveTimeTestFunction d), g.val = ∑ i, c i • (f i).val := by
  -- Use the fact that PositiveTimeTestFunctions.submodule is closed under finite linear combinations
  use ∑ i, c i • (f i)
  -- The sum automatically lives in the submodule by the submodule properties
  simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower]

/-- Submodule of **complex-valued** test functions supported in the positive time region.
    This is a ℂ-submodule since ℂ-scalar multiplication preserves support. -/
def PositiveTimeTestFunctionsℂ.submodule : Submodule ℂ (SchwartzTestFunctionℂ d) where
  carrier := { f : (SchwartzTestFunctionℂ d) | tsupport f ⊆ positiveTimeSet }
  zero_mem' := by
    simp only [Set.mem_ofPred_eq]
    suffices h : tsupport (0 : (SchwartzTestFunctionℂ d)) = ∅ by
      rw [h]
      apply Set.empty_subset
    rw [tsupport_eq_empty_iff]
    rfl
  add_mem' := fun {f g} hf hg => Set.Subset.trans (tsupport_add f g) (Set.union_subset hf hg)
  smul_mem' := by
    intro c f hf
    refine (tsupport_smul_subset_right (fun _ : (SpaceTime d) => c) f).trans hf

/-- Type of complex-valued test functions supported in the positive time region -/
abbrev PositiveTimeTestFunctionℂ (d : ℕ) [Fact (2 ≤ d)] : Type :=
  PositiveTimeTestFunctionsℂ.submodule (d := d)

lemma PositiveTimeTestFunctionℂ.zero_on_nonpositive
    (f : (PositiveTimeTestFunctionℂ d)) {x : (SpaceTime d)}
    (hx : getTimeComponent x ≤ 0) : f.val x = 0 := by
  classical
  have hx_not_support : x ∉ tsupport f.val := by
    intro hx_mem
    have hx_pos : getTimeComponent x > 0 := by
      have hx_mem_pos : x ∈ positiveTimeSet := f.property hx_mem
      simpa [positiveTimeSet, HasPositiveTime] using hx_mem_pos
    have : getTimeComponent x < getTimeComponent x := lt_of_le_of_lt hx hx_pos
    exact (lt_irrefl _ this)
  exact image_eq_zero_of_notMem_tsupport hx_not_support

omit [Fact (2 ≤ d)] in
/-- Helper lemma: starRingEnd ℂ commutes through derivatives and preserves norms -/
lemma starRingEnd_iteratedFDeriv_norm_eq (g : (SchwartzTestFunctionℂ d)) (n : ℕ) (x : (SpaceTime d)) :
  ‖iteratedFDeriv ℝ n (fun x => starRingEnd ℂ (g x)) x‖ = ‖iteratedFDeriv ℝ n g x‖ := by
  -- Use the fact that starRingEnd ℂ = Complex.conjLIE (as functions)
  have h : (fun x => starRingEnd ℂ (g x)) = Complex.conjLIE ∘ g := by
    ext y
    rw [Function.comp_apply]
    -- Use the fact that conjLIE and starRingEnd are the same
    exact congr_fun (@RCLike.conjLIE_apply ℂ _) (g y)
  rw [h]
  -- Now apply the norm preservation lemma for LinearIsometryEquiv
  exact LinearIsometryEquiv.norm_iteratedFDeriv_comp_left Complex.conjLIE g x n

/-- Star operation on test functions: time reflection followed by complex conjugation -/
noncomputable def starTestFunction (f : (SchwartzTestFunctionℂ d)) : (SchwartzTestFunctionℂ d) :=
  -- Apply time reflection then complex conjugation pointwise
  let f_reflected := compTimeReflection f
  -- Apply complex conjugation to each value
  ⟨fun x => starRingEnd ℂ (f_reflected x),
   -- Smoothness: starRingEnd is smooth and compTimeReflection gives smooth functions
   by
     -- Apply the continuous linear map contDiff lemma
     apply ContDiff.comp
     · -- starRingEnd ℂ is smooth
       exact ContinuousLinearMap.contDiff (Complex.conjLIE.toContinuousLinearMap)
     · -- f_reflected is smooth
       exact f_reflected.smooth ⊤,
   -- Decay
   fun k n => by
     -- Use the bound from f_reflected and the fact that starRingEnd is an isometry
     obtain ⟨C, hC⟩ := f_reflected.decay' k n
     use C
     intro x
     -- Since starRingEnd ℂ is complex conjugation, which is an isometry,
     -- it preserves the norms of derivatives. This follows from standard properties
     -- of linear isometries and the chain rule for derivatives.
     have h_eq : ‖iteratedFDeriv ℝ n (fun x => starRingEnd ℂ (f_reflected x)) x‖ = ‖iteratedFDeriv ℝ n f_reflected x‖ :=
       starRingEnd_iteratedFDeriv_norm_eq f_reflected n x
     calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x => starRingEnd ℂ (f_reflected x)) x‖
         = ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f_reflected x‖ := by rw [h_eq]
       _ ≤ C := hC x⟩

/-- Star instance for complex test functions -/
noncomputable instance : Star (SchwartzTestFunctionℂ d) where
  star f := starTestFunction f

lemma PositiveTimeTestFunction.zero_on_nonpositive
    (f : (PositiveTimeTestFunction d)) {x : (SpaceTime d)}
    (hx : getTimeComponent x ≤ 0) : f.val x = 0 := by
  classical
  have hx_not_support : x ∉ tsupport f.val := by
    intro hx_mem
    have hx_pos : getTimeComponent x > 0 := by
      have hx_mem_pos : x ∈ positiveTimeSet := f.property hx_mem
      simpa [positiveTimeSet, HasPositiveTime] using hx_mem_pos
    have : getTimeComponent x < getTimeComponent x := lt_of_le_of_lt hx hx_pos
    exact (lt_irrefl _ this)
  exact image_eq_zero_of_notMem_tsupport hx_not_support

end
