/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import OSforGFF.FunctionalAnalysis

/-!
# Coordinate-free Euclidean time direction API

This module packages the minimal coordinate-free data needed for OS-style time evolution:

- a distinguished unit direction `e` in an ambient Euclidean space `E`,
- scalar-time translations `x ↦ x + t • e`,
- a reflection operator compatible with that time coordinate,
- induced actions on Schwartz test functions.

The goal is to decouple OS-axiom statements from hard-coded coordinate indices.
-/

namespace OSforGFF
namespace Spacetime

open MeasureTheory
open scoped RealInnerProductSpace

/-- Choice of Euclidean time direction: a unit vector `e`. -/
structure TimeDirection (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  vec : E
  norm_eq_one : ‖vec‖ = 1

namespace TimeDirection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (τ : TimeDirection E)

/-- Time-coordinate functional associated to `τ`. -/
noncomputable def timeCoord : E →L[ℝ] ℝ :=
  innerSL ℝ τ.vec

@[simp] lemma timeCoord_apply (x : E) :
    τ.timeCoord x = (innerSL ℝ τ.vec) x := rfl

lemma timeCoord_vec : τ.timeCoord τ.vec = 1 := by
  calc
    τ.timeCoord τ.vec = ‖τ.vec‖ ^ (2 : ℕ) := by
      simpa [timeCoord] using (real_inner_self_eq_norm_sq τ.vec)
    _ = 1 := by simpa [τ.norm_eq_one]

lemma timeCoord_smul_vec (t : ℝ) : τ.timeCoord (t • τ.vec) = t := by
  simpa [τ.timeCoord_vec] using (map_smul τ.timeCoord t τ.vec)

/-- Scalar-time translation along the distinguished direction `τ.vec`. -/
def translateAlong (t : ℝ) (x : E) : E :=
  x + t • τ.vec

@[simp] lemma translateAlong_zero (x : E) : τ.translateAlong 0 x = x := by
  simp [translateAlong]

@[simp] lemma translateAlong_add (s t : ℝ) (x : E) :
    τ.translateAlong (s + t) x = τ.translateAlong s (τ.translateAlong t x) := by
  simp [translateAlong, add_smul, add_left_comm, add_comm]

@[simp] lemma translateAlong_sub (t : ℝ) (x : E) :
    τ.translateAlong (-t) (τ.translateAlong t x) = x := by
  simp [translateAlong, add_assoc]

lemma timeCoord_translateAlong (t : ℝ) (x : E) :
    τ.timeCoord (τ.translateAlong t x) = τ.timeCoord x + t := by
  calc
    τ.timeCoord (τ.translateAlong t x)
        = τ.timeCoord x + τ.timeCoord (t • τ.vec) := by
            simpa [TimeDirection.translateAlong] using (τ.timeCoord.map_add x (t • τ.vec))
    _ = τ.timeCoord x + t := by simp [τ.timeCoord_smul_vec]

/-- Translation along `τ.vec` preserves Lebesgue measure. -/
lemma translateAlong_measurePreserving
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (t : ℝ) :
    MeasurePreserving (τ.translateAlong t) (volume : Measure E) (volume : Measure E) := by
  refine ⟨(continuous_id.add continuous_const).measurable, ?_⟩
  simpa [translateAlong] using map_add_right_eq_self (volume : Measure E) (t • τ.vec)

end TimeDirection

/-- Reflection data compatible with a chosen time direction. -/
structure TimeDirectionOps (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (τ : TimeDirection E) where
  /-- Reflection map (as a linear isometry). -/
  reflect : E ≃ₗᵢ[ℝ] E
  /-- Reflection flips the `τ`-time coordinate. -/
  reflect_timeCoord : ∀ x : E, τ.timeCoord (reflect x) = - τ.timeCoord x
  /-- Reflection is pointwise involutive. -/
  reflect_involutive : ∀ x : E, reflect (reflect x) = x
  /-- Reflection fixes the hyperplane orthogonal to `τ`. -/
  reflect_fix_hyperplane : ∀ x : E, τ.timeCoord x = 0 → reflect x = x

namespace TimeDirectionOps

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {τ : TimeDirection E} (ops : TimeDirectionOps E τ)

/-- Positive-time half-space associated to `τ`. -/
def nonnegativeHalfSpace (opsArg : TimeDirectionOps E τ) : Set E :=
  let _ := opsArg
  {x | 0 ≤ τ.timeCoord x}

/-- Non-positive-time half-space associated to `τ`. -/
def nonpositiveHalfSpace (opsArg : TimeDirectionOps E τ) : Set E :=
  let _ := opsArg
  {x | τ.timeCoord x ≤ 0}

lemma reflect_mem_nonnegative_iff (x : E) :
    ops.reflect x ∈ ops.nonnegativeHalfSpace ↔ x ∈ ops.nonpositiveHalfSpace := by
  constructor
  · intro hx
    change 0 ≤ τ.timeCoord (ops.reflect x) at hx
    have hx' : 0 ≤ -τ.timeCoord x := by
      simpa [ops.reflect_timeCoord x] using hx
    exact neg_nonneg.mp hx'
  · intro hx
    change τ.timeCoord x ≤ 0 at hx
    have hx' : 0 ≤ -τ.timeCoord x := neg_nonneg.mpr hx
    change 0 ≤ τ.timeCoord (ops.reflect x)
    simpa [ops.reflect_timeCoord x] using hx'

lemma reflect_mem_nonpositive_iff (x : E) :
    ops.reflect x ∈ ops.nonpositiveHalfSpace ↔ x ∈ ops.nonnegativeHalfSpace := by
  constructor
  · intro hx
    change τ.timeCoord (ops.reflect x) ≤ 0 at hx
    have hx' : -τ.timeCoord x ≤ 0 := by
      simpa [ops.reflect_timeCoord x] using hx
    exact neg_nonpos.mp hx'
  · intro hx
    change 0 ≤ τ.timeCoord x at hx
    have hx' : -τ.timeCoord x ≤ 0 := neg_nonpos.mpr hx
    change τ.timeCoord (ops.reflect x) ≤ 0
    simpa [ops.reflect_timeCoord x] using hx'

@[simp] lemma reflect_apply_reflect (x : E) :
    ops.reflect (ops.reflect x) = x :=
  ops.reflect_involutive x

/-- Reflection preserves Lebesgue measure. -/
lemma reflect_measurePreserving
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] :
    MeasurePreserving ops.reflect (volume : Measure E) (volume : Measure E) := by
  simpa using ops.reflect.measurePreserving

/-- Time-direction translation action on Schwartz functions. -/
noncomputable def translateAlongTestFunction {𝕜 : Type*} [RCLike 𝕜]
    (ops : TimeDirectionOps E τ) (t : ℝ) (f : SchwartzMap E 𝕜) : SchwartzMap E 𝕜 :=
  let _ := ops
  f.translate (t • τ.vec)

@[simp] lemma translateAlongTestFunction_apply {𝕜 : Type*} [RCLike 𝕜]
    (t : ℝ) (f : SchwartzMap E 𝕜) (x : E) :
    translateAlongTestFunction (ops := ops) t f x = f (x - t • τ.vec) := by
  simpa [translateAlongTestFunction] using
    (SchwartzMap.translate_apply f (t • τ.vec) x)

/-- Reflection action on real-valued Schwartz functions. -/
noncomputable def reflectTestFunctionReal [FiniteDimensional ℝ E] :
    SchwartzMap E ℝ →L[ℝ] SchwartzMap E ℝ := by
  let g : E → E := fun x => ops.reflect x
  have hgrowth : g.HasTemperateGrowth := by
    simpa [g] using
      ((ops.reflect.toContinuousLinearEquiv : E ≃L[ℝ] E).toContinuousLinearMap.hasTemperateGrowth)
  have hupper : ∃ (k : ℕ) (C : ℝ), ∀ x : E, ‖x‖ ≤ C * (1 + ‖g x‖) ^ k := by
    refine ⟨1, 1, ?_⟩
    intro x
    have hnorm : ‖g x‖ = ‖x‖ := by
      simpa [g] using (ops.reflect.norm_map x)
    calc
      ‖x‖ = ‖g x‖ := by simpa [hnorm]
      _ ≤ 1 + ‖g x‖ := by linarith [norm_nonneg (g x)]
      _ = (1 : ℝ) * (1 + ‖g x‖) ^ (1 : ℕ) := by ring
  exact SchwartzMap.compCLM (𝕜 := ℝ) (hg := hgrowth) (hg_upper := hupper)

@[simp] lemma reflectTestFunctionReal_apply [FiniteDimensional ℝ E]
    (f : SchwartzMap E ℝ) (x : E) :
    reflectTestFunctionReal (ops := ops) f x = f (ops.reflect x) := by
  rfl

end TimeDirectionOps

end Spacetime
end OSforGFF
