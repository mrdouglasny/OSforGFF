/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Copyright (c) 2026 Sergey A. Cherkis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sergey A. Cherkis, Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/

import Mathlib.Tactic  -- gives `ext` and `simp` power
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.Group.Support
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.InnerProductSpace.PiL2

import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.Topology.MetricSpace.Isometry

import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.FiniteMeasureExt

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Density

import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Real

--import Mathlib.LinearAlgebra.TensorAlgebra.Basic

import OSforGFF.Spacetime.Basic
import OSforGFF.Spacetime.Euclidean

/-!
# Time Reflection Θ and Discrete Symmetries

Time reflection Θ: (t, x̄) ↦ (−t, x̄) as an orthogonal involution on ℝᵈ.
Properties: self-inverse (Θ² = id), measure-preserving, isometric.

Induced actions on test functions: (Θf)(x) = f(Θx) = f(−t, x̄).
Foundation for the OS3 reflection positivity axiom.
-/

open MeasureTheory

namespace QFT

variable {d : ℕ} [Fact (2 ≤ d)]

abbrev timeReflection (x : (SpaceTime d)) : (SpaceTime d) :=
  (WithLp.equiv 2 _).symm (Function.update x.ofLp 0 (-x.ofLp 0))

def timeReflectionLinear : (SpaceTime d) →ₗ[ℝ] (SpaceTime d) :=
{ toFun := timeReflection
  map_add' := by
    intro x y
    apply PiLp.ext
    intro i
    simp only [timeReflection, WithLp.equiv_symm_apply]
    by_cases h : i = 0
    · subst h
      simp [Function.update_self]
      ring
    · simp [Function.update_of_ne h]
  map_smul' := by
    intro c x
    apply PiLp.ext
    intro i
    simp only [timeReflection, RingHom.id_apply, WithLp.equiv_symm_apply]
    by_cases h : i = 0
    · subst h
      simp [Function.update_self]
    · simp [Function.update_of_ne h] }

noncomputable def timeReflectionCLM : (SpaceTime d) →L[ℝ] (SpaceTime d) :=
timeReflectionLinear.toContinuousLinearMap (E := (SpaceTime d)) (F' := (SpaceTime d))

open InnerProductSpace

/-- Time reflection preserves inner products -/
lemma timeReflection_inner_map (x y : (SpaceTime d)) :
    ⟪timeReflection x, timeReflection y⟫_ℝ = ⟪x, y⟫_ℝ := by
  -- Direct proof using fintype inner product
  simp only [inner]
  congr 1
  ext i
  simp only [timeReflection]
  by_cases h : i = 0
  · rw [h]; simp
  · simp [h]

/-- Time reflection as a linear isometry equivalence -/
@[simp] lemma timeReflection_involutive (x : (SpaceTime d)) :
    timeReflection (timeReflection x) = x := by
  apply PiLp.ext
  intro i
  simp only [timeReflection, WithLp.equiv_symm_apply]
  by_cases h : i = 0
  · subst h
    simp [Function.update_self]
  · simp [Function.update_of_ne h]

def timeReflectionLE : (SpaceTime d) ≃ₗᵢ[ℝ] (SpaceTime d) :=
{ toFun := timeReflection
  invFun := timeReflection  -- Time reflection is self-inverse
  left_inv := timeReflection_involutive
  right_inv := timeReflection_involutive
  map_add' := timeReflectionLinear.map_add'
  map_smul' := timeReflectionLinear.map_smul'
  norm_map' := by
    intro x
    -- The goal is to show that the LinearIsometryEquiv preserves norms
    -- First simplify the LinearIsometryEquiv application
    show ‖timeReflection x‖ = ‖x‖
    -- Use that time reflection preserves inner products
    have h : ⟪timeReflection x, timeReflection x⟫_ℝ = ⟪x, x⟫_ℝ := timeReflection_inner_map x x
    -- For real inner product spaces, ⟪x, x⟫ = ‖x‖^2 directly
    have h1 : ⟪timeReflection x, timeReflection x⟫_ℝ = ‖timeReflection x‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq]
    have h2 : ⟪x, x⟫_ℝ = ‖x‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq]
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
    rw [← h1, ← h2, h] }

/-- Time reflection preserves Lebesgue measure. -/
lemma timeReflection_measurePreserving :
    MeasurePreserving (timeReflection (d := d)) volume volume := by
  -- Any linear isometry equivalence preserves the volume measure.
  exact (timeReflectionLE).measurePreserving

example (x : (SpaceTime d)) :
    timeReflectionCLM x =
      Function.update x (0 : Fin d) (-x 0) := rfl

/-- Composition with time reflection as a continuous linear map on **complex-valued**
    test functions. This maps a test function `f` to the function `x ↦ f(timeReflection(x))`,
    where `timeReflection` negates the time coordinate (0th component) while
    preserving spatial coordinates. This version acts on complex test functions and
    is used to formulate the Osterwalder-Schrader star operation. -/
private lemma timeReflection_hg_upper :
    ∃ (k : ℕ) (C : ℝ), ∀ (x : (SpaceTime d)), ‖x‖ ≤ C * (1 + ‖timeReflectionCLM x‖) ^ k := by
  use 1, 1
  intro x
  have h_iso : ‖timeReflectionCLM x‖ = ‖x‖ := by
    have h_norm_preserved : ‖timeReflection x‖ = ‖x‖ := LinearIsometryEquiv.norm_map timeReflectionLE x
    rw [← h_norm_preserved]
    rfl
  rw [h_iso]
  have hx : ‖x‖ ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
  calc
    ‖x‖ ≤ 1 + ‖x‖ := hx
    _ = 1 * (1 + ‖x‖) ^ (1 : ℕ) := by simp [pow_one]

noncomputable def compTimeReflection : (SchwartzTestFunctionℂ d) →L[ℝ] (SchwartzTestFunctionℂ d) :=
  SchwartzMap.compCLM (𝕜 := ℝ)
    (hg := timeReflectionCLM.hasTemperateGrowth)
    (hg_upper := timeReflection_hg_upper)

/-- Composition with time reflection as a continuous linear map on **real-valued**
    test functions. This version will be used when working with positive-time
    subspaces defined over ℝ, so that reflection positivity can be formulated
    without passing through complex scalars. -/
noncomputable def compTimeReflectionReal : (SchwartzTestFunction d) →L[ℝ] (SchwartzTestFunction d) := by
  exact SchwartzMap.compCLM (𝕜 := ℝ)
    (hg := timeReflectionCLM.hasTemperateGrowth)
    (hg_upper := timeReflection_hg_upper)

/-- Time reflection is linear on real test functions. -/
lemma compTimeReflectionReal_linear_combination {n : ℕ} (f : Fin n → (SchwartzTestFunction d)) (c : Fin n → ℝ) :
    compTimeReflectionReal (∑ i, c i • f i) = ∑ i, c i • compTimeReflectionReal (f i) := by
  -- This follows directly from the linearity of the continuous linear map compTimeReflectionReal
  simp only [map_sum, map_smul]

end QFT
