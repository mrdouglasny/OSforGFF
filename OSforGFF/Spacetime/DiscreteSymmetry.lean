/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
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

import Mathlib.Topology.Algebra.Module.LinearMapPiProd
import Mathlib.Topology.MetricSpace.Isometry

import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction

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

Time reflection Θ: (t, x̄) ↦ (−t, x̄) as an orthogonal involution on ℝ⁴.
Properties: self-inverse (Θ² = id), measure-preserving, isometric.

Induced actions on test functions: (Θf)(x) = f(Θx) = f(−t, x̄).
Foundation for the OS3 reflection positivity axiom.
-/

open MeasureTheory

namespace QFT

abbrev timeReflection (x : SpaceTime) : SpaceTime :=
  (WithLp.equiv 2 _).symm (Function.update x.ofLp 0 (-x.ofLp 0))

def timeReflectionMatrix : Matrix (Fin STDimension) (Fin STDimension) ℝ :=
  Matrix.diagonal (fun i => if i = 0 then -1 else 1)

lemma timeReflectionMatrix_is_orthogonal :
   timeReflectionMatrix ∈ Matrix.orthogonalGroup (Fin STDimension) ℝ := by
      simp [Matrix.mem_orthogonalGroup_iff, timeReflectionMatrix, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
      simp [Matrix.diagonal]
      ext i j
      simp [Matrix.one_apply]
      split_ifs <;> norm_num

def timeReflectionIsometry  : Matrix.orthogonalGroup (Fin STDimension) ℝ :=
  ⟨timeReflectionMatrix, timeReflectionMatrix_is_orthogonal⟩

def timeReflectionLinear : SpaceTime →ₗ[ℝ] SpaceTime :=
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

def timeReflectionCLM : SpaceTime →L[ℝ] SpaceTime :=
timeReflectionLinear.toContinuousLinearMap (E := SpaceTime) (F' := SpaceTime)

open InnerProductSpace

/-- Time reflection preserves inner products -/
lemma timeReflection_inner_map (x y : SpaceTime) :
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
def timeReflectionLE : SpaceTime ≃ₗᵢ[ℝ] SpaceTime :=
{ toFun := timeReflection
  invFun := timeReflection  -- Time reflection is self-inverse
  left_inv := by
    intro x
    apply PiLp.ext
    intro i
    simp only [timeReflection, WithLp.equiv_symm_apply]
    by_cases h : i = 0
    · subst h
      simp [Function.update_self]
    · simp [Function.update_of_ne h]
  right_inv := by
    intro x
    apply PiLp.ext
    intro i
    simp only [timeReflection, WithLp.equiv_symm_apply]
    by_cases h : i = 0
    · subst h
      simp [Function.update_self]
    · simp [Function.update_of_ne h]
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
    MeasurePreserving timeReflection volume volume := by
  -- Any linear isometry equivalence preserves the volume measure.
  simpa [timeReflection] using (timeReflectionLE).measurePreserving

example (x : SpaceTime) :
    timeReflectionCLM x =
      Function.update x (0 : Fin STDimension) (-x 0) := rfl

/-- Composition with time reflection as a continuous linear map on **complex-valued**
    test functions. This maps a test function `f` to the function `x ↦ f(timeReflection(x))`,
    where `timeReflection` negates the time coordinate (0th component) while
    preserving spatial coordinates. This version acts on complex test functions and
    is used to formulate the Osterwalder-Schrader star operation. -/
noncomputable def compTimeReflection : TestFunctionℂ →L[ℝ] TestFunctionℂ := by
  have hg_upper : ∃ (k : ℕ) (C : ℝ), ∀ (x : SpaceTime), ‖x‖ ≤ C * (1 + ‖timeReflectionCLM x‖) ^ k := by
    use 1; use 1; simp; intro x
    -- timeReflectionCLM is an isometry, so ‖timeReflectionCLM x‖ = ‖x‖
    have h_iso : ‖timeReflectionCLM x‖ = ‖x‖ := by
      -- Use the fact that timeReflection preserves norms (it's an isometry)
      have h_norm_preserved : ‖timeReflection x‖ = ‖x‖ := by
        exact LinearIsometryEquiv.norm_map timeReflectionLE x
      -- timeReflectionCLM x = timeReflection x by definition
      rw [← h_norm_preserved]
      -- timeReflectionCLM x = timeReflection x
      rfl
    rw [h_iso]
    -- Now we need ‖x‖ ≤ 1 + ‖x‖, which is always true
    linarith [norm_nonneg x]
  exact SchwartzMap.compCLM (𝕜 := ℝ) (hg := timeReflectionCLM.hasTemperateGrowth) (hg_upper := hg_upper)

/-- Composition with time reflection as a continuous linear map on **real-valued**
    test functions. This version will be used when working with positive-time
    subspaces defined over ℝ, so that reflection positivity can be formulated
    without passing through complex scalars. -/
noncomputable def compTimeReflectionReal : TestFunction →L[ℝ] TestFunction := by
  have hg_upper : ∃ (k : ℕ) (C : ℝ), ∀ (x : SpaceTime), ‖x‖ ≤ C * (1 + ‖timeReflectionCLM x‖) ^ k := by
    use 1; use 1; simp; intro x
    have h_iso : ‖timeReflectionCLM x‖ = ‖x‖ := by
      -- timeReflectionCLM coincides with the geometric time reflection, hence an isometry
      have h_norm_preserved : ‖timeReflection x‖ = ‖x‖ := by
        exact LinearIsometryEquiv.norm_map timeReflectionLE x
      -- Rewrite using the definition of timeReflectionCLM
      rw [← h_norm_preserved]
      rfl
    rw [h_iso]
    linarith [norm_nonneg x]
  exact SchwartzMap.compCLM (𝕜 := ℝ) (hg := timeReflectionCLM.hasTemperateGrowth) (hg_upper := hg_upper)

/-- Time reflection is linear on real test functions. -/
lemma compTimeReflectionReal_linear_combination {n : ℕ} (f : Fin n → TestFunction) (c : Fin n → ℝ) :
    compTimeReflectionReal (∑ i, c i • f i) = ∑ i, c i • compTimeReflectionReal (f i) := by
  -- This follows directly from the linearity of the continuous linear map compTimeReflectionReal
  simp only [map_sum, map_smul]

end QFT
