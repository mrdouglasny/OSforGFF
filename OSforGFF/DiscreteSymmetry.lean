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

import OSforGFF.Basic
import OSforGFF.Euclidean

/-!
## Discrete Symmetries for AQFT

This file implements discrete symmetries, particularly time reflection (T), which is fundamental
for the OS-3 (reflection positivity) axiom in the Osterwalder-Schrader framework. Time reflection
maps (t, x⃗) ↦ (-t, x⃗), reversing the time coordinate while preserving spatial coordinates.

### Key Definitions & Structures:

**Time Reflection Operation:**
- `timeReflection`: Point transformation (t, x⃗) ↦ (-t, x⃗) on spacetime
- `timeReflectionMatrix`: Diagonal matrix with -1 for time, +1 for spatial coordinates
- `timeReflectionMatrix_is_orthogonal`: Proof that the matrix is orthogonal (in O(d))

**Linear Algebraic Structure:**
- `timeReflectionIsometry`: Time reflection as element of orthogonal group O(d)
- `timeReflectionLinear`: Linear map version with additivity/homogeneity proofs
- `timeReflectionCLM`: Continuous linear map version for analysis

**Geometric Properties:**
- `timeReflection_inner_map`: Time reflection preserves inner products ⟨Θx, Θy⟩ = ⟨x, y⟩
- `timeReflection_measurePreserving`: Time reflection preserves Lebesgue measure
- Self-inverse property: Θ² = Id (time reflection applied twice gives identity)
- Orthogonal transformation: preserves angles and distances

**Linear Isometry Structure:**
- `timeReflectionLE`: Complete linear isometry equivalence Θ: SpaceTime d ≃ₗᵢ[ℝ] SpaceTime d
- Includes proofs of:
  - `left_inv` and `right_inv`: Θ⁻¹ = Θ (self-inverse)
  - `map_add'` and `map_smul'`: Linearity
  - `norm_map'`: Isometry property ‖Θx‖ = ‖x‖

**Function Space Actions:**
- `compTimeReflection`: Action on complex test functions (f ↦ f ∘ Θ)
- `compTimeReflectionReal`: Action on real test functions (f ↦ f ∘ Θ)
- `compTimeReflectionReal_linear_combination`: Linearity on finite sums
- Maps test function f(x) to (Θ*f)(x) = f(Θx) = f(-t, x⃗)
- Continuous linear maps on Schwartz space
- Includes temperate growth and polynomial bound proofs

**Mathematical Foundation:**
Time reflection is the key discrete symmetry for QFT because:

1. **Geometric**: Reverses time flow while preserving spatial structure
2. **Orthogonal**: Preserves Euclidean metric ⟨x,y⟩ = ⟨Θx,Θy⟩
3. **Self-Inverse**: Θ² = Id, making it an involution
4. **Measure-Preserving**: Preserves Lebesgue measure (det Θ = -1, |det Θ| = 1)
5. **Function Space Compatible**: Extends to actions on test functions and distributions

**Connection to OS-3 (Reflection Positivity):**
This provides the mathematical foundation for OS-3 reflection positivity:
- Θ acts on test functions: (Θf)(x) = f(Θx)
- Generates the "star" operation for positive-time test functions
- Essential for the reflection positivity matrix formulation
- Enables analytic continuation from Euclidean to Minkowski QFT

**Integration with AQFT Framework:**
- Spacetime structure from `OSforGFF.Basic`
- Used in `OSforGFF.OS_Axioms` for OS-3 formulation
- Function space actions for Schwartz test functions
- Geometric foundation for positive-time test functions in `OSforGFF.PositiveTimeTestFunction`

**Technical Implementation:**
- Complete mathematical rigor with all linearity and isometry proofs
- Continuous linear map structure for functional analysis
- Temperate growth bounds for Schwartz space compatibility
- Matrix representation for computational applications

This enables the proper formulation of reflection positivity, which is crucial for proving
that Euclidean field theories can be analytically continued to relativistic quantum field theories.
-/

open MeasureTheory

namespace QFT

variable {d : ℕ} [NeZero d]

abbrev timeReflection (x : SpaceTime d) : SpaceTime d :=
  (WithLp.equiv 2 _).symm (Function.update x.ofLp 0 (-x.ofLp 0))

def timeReflectionMatrix : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.diagonal (fun i => if i = 0 then -1 else 1)

lemma timeReflectionMatrix_is_orthogonal :
   (timeReflectionMatrix (d := d)) ∈ Matrix.orthogonalGroup (Fin d) ℝ := by
      rw [Matrix.mem_orthogonalGroup_iff]
      ext i j
      simp [timeReflectionMatrix, Matrix.diagonal_apply, Matrix.one_apply]
      split_ifs <;> simp_all

def timeReflectionIsometry  : Matrix.orthogonalGroup (Fin d) ℝ :=
  ⟨timeReflectionMatrix, timeReflectionMatrix_is_orthogonal⟩

def timeReflectionLinear : SpaceTime d →ₗ[ℝ] SpaceTime d :=
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

noncomputable def timeReflectionCLM : SpaceTime d →L[ℝ] SpaceTime d :=
timeReflectionLinear.toContinuousLinearMap (E := SpaceTime d) (F' := SpaceTime d)

open InnerProductSpace

/-- Time reflection preserves inner products -/
lemma timeReflection_inner_map (x y : SpaceTime d) :
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
def timeReflectionLE : SpaceTime d ≃ₗᵢ[ℝ] SpaceTime d :=
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
    MeasurePreserving (timeReflection (d := d)) volume volume := by
  -- Any linear isometry equivalence preserves the volume measure.
  simpa [timeReflection] using (timeReflectionLE).measurePreserving

example (x : SpaceTime d) :
    timeReflectionCLM x =
      Function.update x (0 : Fin d) (-x 0) := rfl

/-- Composition with time reflection as a continuous linear map on **complex-valued**
    test functions. This maps a test function `f` to the function `x ↦ f(timeReflection(x))`,
    where `timeReflection` negates the time coordinate (0th component) while
    preserving spatial coordinates. This version acts on complex test functions and
    is used to formulate the Osterwalder-Schrader star operation. -/
noncomputable def compTimeReflection : TestFunctionℂ d →L[ℝ] TestFunctionℂ d := by
  have hg_upper : ∃ (k : ℕ) (C : ℝ), ∀ (x : SpaceTime d), ‖x‖ ≤ C * (1 + ‖timeReflectionCLM x‖) ^ k := by
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
noncomputable def compTimeReflectionReal : TestFunction d →L[ℝ] TestFunction d := by
  have hg_upper : ∃ (k : ℕ) (C : ℝ), ∀ (x : SpaceTime d), ‖x‖ ≤ C * (1 + ‖timeReflectionCLM x‖) ^ k := by
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
lemma compTimeReflectionReal_linear_combination {n : ℕ} (f : Fin n → TestFunction d) (c : Fin n → ℝ) :
    compTimeReflectionReal (∑ i, c i • f i) = ∑ i, c i • compTimeReflectionReal (f i) := by
  -- This follows directly from the linearity of the continuous linear map compTimeReflectionReal
  simp only [map_sum, map_smul]

end QFT
