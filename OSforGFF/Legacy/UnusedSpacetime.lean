/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Copyright (c) 2026 Sergey A. Cherkis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sergey A. Cherkis, Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/
import OSforGFF.Spacetime.Basic
import OSforGFF.Spacetime.DiscreteSymmetry
import OSforGFF.Spacetime.Euclidean
import OSforGFF.Spacetime.PositiveTimeTestFunction
import OSforGFF.Spacetime.ProdIntegrable
import OSforGFF.Schwinger.Defs

/-!
# LEGACY — unused spacetime-layer declarations (off the build graph)

**Status: legacy.** Proven declarations from the spacetime layer that no declaration on the
build graph consumes. Preserved here with full proofs; **not on the root import graph**.
Verify in isolation with

    lake env lean OSforGFF/Legacy/UnusedSpacetime.lean

Declarations keep their original namespaces; each block re-declares the `open`/`variable`
context of its source file.

## Supersession map

From `Spacetime/Basic.lean`:
- `schwartzMul` — pointwise multiplication lifted to the Schwartz space; the library's
  multiplication needs are served by `ContinuousLinearMap.mul` directly.
- `pointwiseMulCLM` (moved 2026-08-30) — the packaged `ContinuousLinearMap.mul ℂ ℂ`;
  consumed only by `schwartzMul` in this file.
- `SpatialL2` — L² space on spatial slices; the OS constructions work with `Lp` types
  spelled out explicitly.

From `Spacetime/DiscreteSymmetry.lean` (the matrix presentation of time reflection —
the library uses the linear-map presentation `timeReflection`/`timeReflectionCLM` and
`QFT.timeReflectionLE` instead):
- `timeReflectionMatrix`, `timeReflectionMatrix_is_orthogonal`, `timeReflectionIsometry` —
  a closed cluster: the matrix, its orthogonality, and its packaging as an element of the
  orthogonal group.

From `Spacetime/Euclidean.lean`:
- `euclidean_actions_unified` — the statement that the test-function and L² Euclidean
  actions are both instances of one abstract pattern; the OS2 proof uses the plain
  pullback action `euclidean_action`.
- `euclidean_action_real`, `euclidean_action_unified_basis`, `euclidean_action_L2`,
  `euclidean_action_CLM` (moved 2026-08-30) — the real, L², and CLM-packaged variants
  of the pullback action; the OS chain consumes only the complex `euclidean_action`.

From `Spacetime/ProdIntegrable.lean` (moved 2026-08-30):
- `spacetimeOfTimeSpace_norm_sq` — the time/space split of the squared norm; the OS3
  slice analysis bounds norms via `spacetimeOfTimeSpace_norm_ge` instead.
- `schwartz_time_slice_integrable` — integrability of a Schwartz function on a fixed
  time slice; the graph uses the `spatialNormIntegral` apparatus directly.

From `Measure/GaussianFreeField.lean` (moved 2026-08-30; kept here rather than in
`UnusedMeasureSchwinger` because it consumes `euclidean_action_real` above):
- `CovarianceEuclideanInvariant` — the real-test-function form of Euclidean invariance
  of the covariance; OS2 consumes only the complex form
  `CovarianceEuclideanInvariantℂ`.

From `Spacetime/PositiveTimeTestFunction.lean`:
- `is_open_positiveTimeSet` — openness of the positive-time region; the positive-time
  submodule is defined via `tsupport` inclusion and never needs openness.
-/

/-! ### From `Spacetime/Basic.lean` -/

section SpacetimeBasic

open MeasureTheory NNReal ENNReal Complex
open TopologicalSpace Measure
open DFunLike (coe)

noncomputable section

variable {d : ℕ}

/-- Pointwise multiplication of `ℂ` packaged as a continuous bilinear map. -/
def pointwiseMulCLM : ℂ →L[ℂ] ℂ →L[ℂ] ℂ := ContinuousLinearMap.mul ℂ ℂ

/-- Multiplication lifted to the Schwartz space. -/
def schwartzMul (g : (SchwartzTestFunctionℂ d)) : (SchwartzTestFunctionℂ d) →L[ℂ] (SchwartzTestFunctionℂ d) :=
  (SchwartzMap.bilinLeftCLM pointwiseMulCLM (SchwartzMap.hasTemperateGrowth_general g))

/-- L² space on spatial slices (real-valued) -/
abbrev SpatialL2 (d : ℕ) := Lp ℝ 2 (volume : Measure (SpatialCoords d))

end

end SpacetimeBasic

/-! ### From `Spacetime/DiscreteSymmetry.lean` -/

section DiscreteSymmetry

open MeasureTheory

namespace QFT

variable {d : ℕ} [Fact (2 ≤ d)]

def timeReflectionMatrix : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.diagonal (fun i => if i = 0 then -1 else 1)

lemma timeReflectionMatrix_is_orthogonal :
   timeReflectionMatrix ∈ Matrix.orthogonalGroup (Fin d) ℝ := by
      simp [Matrix.mem_orthogonalGroup_iff, timeReflectionMatrix, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
      ext i j
      simp [Matrix.one_apply]
      split_ifs <;> norm_num

def timeReflectionIsometry  : Matrix.orthogonalGroup (Fin d) ℝ :=
  ⟨timeReflectionMatrix, timeReflectionMatrix_is_orthogonal⟩

end QFT

end DiscreteSymmetry

/-! ### From `Spacetime/Euclidean.lean` -/

section Euclidean

open MeasureTheory NNReal ENNReal
open TopologicalSpace Measure
open scoped Real InnerProductSpace SchwartzMap

noncomputable section

namespace QFT

variable {d : ℕ}

/-- Action of Euclidean group on real test functions via pullback.
    For g ∈ (E d) and f ∈ (SchwartzTestFunction d), define (g • f)(x) = f(g⁻¹ • x).
    This is the real version of euclidean_action for (SchwartzTestFunction d) = SchwartzMap (SpaceTime d) ℝ. -/
noncomputable def euclidean_action_real (g : (E d)) (f : (SchwartzTestFunction d)) : (SchwartzTestFunction d) :=
  SchwartzMap.compCLM (𝕜 := ℝ)
    (hg := euclidean_pullback_temperate_growth g)
    (hg_upper := euclidean_pullback_polynomial_bounds g) f

/-- The measure preservation result enables both test function and L² actions. -/
lemma euclidean_action_unified_basis (g : (E d)) :
    MeasurePreserving (euclidean_pullback g) (volume : Measure (SpaceTime d)) volume := by
  unfold euclidean_pullback
  exact measurePreserving_act g⁻¹

/-- Action of Euclidean group on L² functions via pullback.
    For g ∈ (E d) and f ∈ Lp ℂ 2 (volume : Measure (SpaceTime d)), define (g • f)(x) = f(g⁻¹ • x).
    Uses measure preservation instead of temperate growth bounds. -/
noncomputable def euclidean_action_L2 (g : (E d))
    (f : Lp ℂ 2 (volume : Measure (SpaceTime d))) : Lp ℂ 2 (volume : Measure (SpaceTime d)) :=
  have h_meas_pres : MeasurePreserving (euclidean_pullback g) (volume : Measure (SpaceTime d)) volume :=
    euclidean_action_unified_basis g
  Lp.compMeasurePreserving (p := 2) (euclidean_pullback g) h_meas_pres f

/-- The Euclidean action as a continuous linear map on test functions. -/
noncomputable def euclidean_action_CLM (g : (E d)) : (SchwartzTestFunctionℂ d) →L[ℂ] (SchwartzTestFunctionℂ d) :=
  SchwartzMap.compCLM (𝕜 := ℂ)
    (hg := euclidean_pullback_temperate_growth g)
    (hg_upper := euclidean_pullback_polynomial_bounds g)

/-- Both actions are instances of the same abstract pattern. -/
lemma euclidean_actions_unified (g : (E d)) :
    (∃ (T_test : (SchwartzTestFunctionℂ d) →L[ℂ] (SchwartzTestFunctionℂ d)),
       ∀ f, euclidean_action g f = T_test f) ∧
    (∃ (T_L2 : Lp ℂ 2 (volume : Measure (SpaceTime d)) → Lp ℂ 2 (volume : Measure (SpaceTime d))),
       ∀ f, euclidean_action_L2 g f = T_L2 f) := by
  constructor
  · use euclidean_action_CLM g
    intro f
    rfl  -- by definition of euclidean_action
  · use euclidean_action_L2 g
    intro f
    rfl  -- by definition of euclidean_action_L2

end QFT

end

end Euclidean

/-! ### From `Spacetime/PositiveTimeTestFunction.lean` -/

section PositiveTimeTestFunction

open TopologicalSpace Function SchwartzMap QFT

noncomputable section

variable {d : ℕ} [Fact (2 ≤ d)]

/-- The positive time set is open -/
lemma is_open_positiveTimeSet : IsOpen (positiveTimeSet (d := d)) :=
  isOpen_lt continuous_const
    (PiLp.continuous_apply 2 (fun _ => ℝ) (⟨0, by have h : 2 ≤ d := Fact.out; omega⟩ : Fin d))

end

end PositiveTimeTestFunction

/-! ### From `Spacetime/ProdIntegrable.lean` (moved 2026-08-30) -/

section ProdIntegrableSlices

open MeasureTheory SchwartzMap Real Set Metric

noncomputable section

variable {d : ℕ} [Fact (2 ≤ d)]

/-- The squared norm splits into time and spatial parts:
    `‖(t, x)‖² = t² + ‖x‖²`. -/
lemma spacetimeOfTimeSpace_norm_sq (t : ℝ) (x : SpatialCoords d) :
    ‖spacetimeOfTimeSpace t x‖ ^ 2 = t ^ 2 + ‖x‖ ^ 2 := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by have h : 2 ≤ d := Fact.out; omega⟩
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ]
  congr 1
  · rw [show (spacetimeOfTimeSpace t x).ofLp 0 = t from spacetimeOfTimeSpace_time t x]
    simp [Real.norm_eq_abs, sq_abs]
  · rw [EuclideanSpace.norm_sq_eq]
    exact Finset.sum_congr rfl fun j _ => by
      rw [show (spacetimeOfTimeSpace t x).ofLp j.succ = x j from rfl]

/-- A Schwartz function restricted to a fixed time slice is integrable over the spatial slice.
    Uses decay transfer: d-dimensional Schwartz decay implies (d-1)-dimensional integrability
    via norm comparison. -/
lemma schwartz_time_slice_integrable (f : SchwartzTestFunctionℂ d) (t : ℝ) :
    Integrable (fun x : SpatialCoords d => f (spacetimeOfTimeSpace t x)) volume := by
  -- Strategy: Show the function has rapid decay and use integrability of decay functions
  --
  -- Key facts:
  -- 1. f is Schwartz, so |f(y)| ≤ C/(1 + ‖y‖)^N for any N
  -- 2. For fixed t, ‖spacetimeOfTimeSpace t x‖ ≥ ‖x‖
  -- 3. So |f(spacetimeOfTimeSpace t x)| ≤ C/(1 + ‖x‖)^N which is integrable for N > d - 1
  have h1d : 1 ≤ d := by have h : 2 ≤ d := Fact.out; omega
  have hST_dim : Module.finrank ℝ (SpaceTime d) < d + 1 := by
    rw [finrank_euclideanSpace_fin]; omega
  obtain ⟨C, hC_pos, hf_decay⟩ := schwartz_integrable_decay f (d + 1) hST_dim

  -- The dominator function: x ↦ C / (1 + ‖x‖)^(d+1)
  have h_dom_integrable : Integrable (fun x : SpatialCoords d => C / (1 + ‖x‖) ^ (d + 1)) volume := by
    have h_dim : (Module.finrank ℝ (SpatialCoords d) : ℝ) < ((d + 1 : ℕ) : ℝ) := by
      rw [finrank_euclideanSpace_fin]
      have : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by push_cast [h1d]; ring
      rw [this]; push_cast; linarith
    have h_int := integrable_one_add_norm (E := SpatialCoords d) (μ := volume)
      (r := ((d + 1 : ℕ) : ℝ)) h_dim
    have h_eq : ∀ x : SpatialCoords d,
        C / (1 + ‖x‖) ^ (d + 1) = C * (1 + ‖x‖) ^ (-((d + 1 : ℕ) : ℝ)) := by
      intro x
      have h_pos : 0 < 1 + ‖x‖ := by linarith [norm_nonneg x]
      have h1 : ((1 + ‖x‖) ^ (d + 1) : ℝ)⁻¹ = (1 + ‖x‖) ^ (-((d + 1 : ℕ) : ℝ)) := by
        rw [← Real.rpow_natCast (1 + ‖x‖) (d + 1), ← Real.rpow_neg (le_of_lt h_pos)]
      rw [div_eq_mul_inv, h1]
    simp_rw [h_eq]
    exact h_int.const_mul C

  -- Pointwise bound via the spacetime-vs-spatial norm comparison
  have h_bound : ∀ x : SpatialCoords d,
      ‖f (spacetimeOfTimeSpace t x)‖ ≤ C / (1 + ‖x‖) ^ (d + 1) := by
    intro x
    have h1 := hf_decay (spacetimeOfTimeSpace t x)
    have h_norm_ge : ‖spacetimeOfTimeSpace t x‖ ≥ ‖x‖ :=
      spacetimeOfTimeSpace_norm_ge t x
    have h_bracket_ge : 1 + ‖spacetimeOfTimeSpace t x‖ ≥ 1 + ‖x‖ := by linarith
    have h_bracket_pos : 0 < 1 + ‖x‖ := by linarith [norm_nonneg x]
    have h_pow_le : (1 + ‖x‖) ^ (d + 1) ≤ (1 + ‖spacetimeOfTimeSpace t x‖) ^ (d + 1) := by
      apply pow_le_pow_left₀ (by linarith [norm_nonneg x]) h_bracket_ge
    calc ‖f (spacetimeOfTimeSpace t x)‖
        ≤ C / (1 + ‖spacetimeOfTimeSpace t x‖) ^ (d + 1) := h1
      _ ≤ C / (1 + ‖x‖) ^ (d + 1) := by
          apply div_le_div_of_nonneg_left (le_of_lt hC_pos) (by positivity) h_pow_le

  -- Apply Integrable.mono
  apply Integrable.mono h_dom_integrable
    (f.continuous.comp (continuous_spacetimeOfTimeSpace_right t)).aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_of_nonneg (by positivity : 0 ≤ C / (1 + ‖x‖) ^ (d + 1))]
  exact h_bound x

/-- Assumption: The covariance is invariant under Euclidean transformations
    (real-test-function form; from `Measure/GaussianFreeField.lean`). -/
def CovarianceEuclideanInvariant (dμ_config : ProbabilityMeasure (FieldConfiguration d)) : Prop :=
  ∀ (g : QFT.E d) (f h : SchwartzTestFunction d),
    SchwingerFunction₂ dμ_config (QFT.euclidean_action_real g f) (QFT.euclidean_action_real g h) =
    SchwingerFunction₂ dμ_config f h

end

end ProdIntegrableSlices
