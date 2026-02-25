/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Topology.Algebra.Module.LinearMapPiProd

import OSforGFF.NuclearSpace.PhysHermiteSchwartz
import OSforGFF.NuclearSpace.RapidDecaySeqMultiIndex
import Batteries.Data.Fin.Lemmas

/-!
# Dimension-generic (multi-index) PhysLean Hermite data

This is a dimension-generic replacement for `PhysHermiteSpaceTime.lean`:

- ambient space: `E := EuclideanSpace ℝ (Fin d)`
- multi-index: `α : Fin d → ℕ`
- eigenfunctions: products of 1D `eigenfunctionRealSchwartz` along coordinates
- coefficient functionals: `𝓢(E,ℝ) →L[ℝ] ℝ` by integration against eigenfunctions

The existing `SpaceTime = ℝ⁴` development will remain as a specialization, but downstream
constructions should migrate to this file.
-/

open scoped BigOperators ENNReal InnerProductSpace RealInnerProductSpace

namespace PhysLean

noncomputable section

open MeasureTheory
open SchwartzMap

namespace MultiHermite

variable {d : ℕ}

abbrev E (d : ℕ) : Type := EuclideanSpace ℝ (Fin d)

abbrev TestFunction (d : ℕ) : Type := SchwartzMap (E d) ℝ

/-- Coordinate projection `E d →L[ℝ] ℝ`. -/
abbrev coordCLM (d : ℕ) (i : Fin d) : E d →L[ℝ] ℝ :=
  (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin d) i)

@[simp] lemma coordCLM_apply (d : ℕ) (i : Fin d) (x : E d) :
    coordCLM d i x = x i := by
  simp [coordCLM]

/-- The (unnormalized) `d`-dimensional harmonic-oscillator eigenfunction indexed by a multi-index `α`. -/
def eigenfunctionRealE (ξ : ℝ) (hξ : ξ ≠ 0) (α : Fin d → ℕ) (x : E d) : ℝ :=
  ∏ i : Fin d, PhysLean.eigenfunctionRealSchwartz ξ hξ (α i) (coordCLM d i x)

@[simp] lemma eigenfunctionRealE_apply (ξ : ℝ) (hξ : ξ ≠ 0) (α : Fin d → ℕ) (x : E d) :
    eigenfunctionRealE (d := d) ξ hξ α x =
      ∏ i : Fin d, PhysLean.eigenfunctionRealSchwartz ξ hξ (α i) (coordCLM d i x) := rfl

/-- The multi-index eigenfunction has temperate growth. -/
lemma eigenfunctionRealE_hasTemperateGrowth (ξ : ℝ) (hξ : ξ ≠ 0) (α : Fin d → ℕ) :
    Function.HasTemperateGrowth (eigenfunctionRealE (d := d) ξ hξ α) := by
  classical
  let g : Fin d → E d → ℝ := fun i x =>
    PhysLean.eigenfunctionRealSchwartz ξ hξ (α i) (coordCLM d i x)
  have hg : ∀ i : Fin d, (g i).HasTemperateGrowth := by
    intro i
    change Function.HasTemperateGrowth
      (fun x : E d => PhysLean.eigenfunctionRealSchwartz ξ hξ (α i) (coordCLM d i x))
    exact
      (SchwartzMap.hasTemperateGrowth (PhysLean.eigenfunctionRealSchwartz ξ hξ (α i))).comp
        (ContinuousLinearMap.hasTemperateGrowth (coordCLM d i))
  have hs :
      ∀ s : Finset (Fin d), (fun x : E d => ∏ i ∈ s, g i x).HasTemperateGrowth := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · exact (by fun_prop : (fun _ : E d => (1 : ℝ)).HasTemperateGrowth)
    · intro a s ha hs
      have hga : (g a).HasTemperateGrowth := hg a
      simpa [Finset.prod_insert, ha] using hga.mul hs
  change Function.HasTemperateGrowth (fun x : E d => ∏ i : Fin d, g i x)
  simpa [eigenfunctionRealE, g] using hs (Finset.univ : Finset (Fin d))

/-- The coefficient functional on `𝓢(E d, ℝ)` against `eigenfunctionRealE`. -/
noncomputable def coeffCLM_E (ξ : ℝ) (hξ : ξ ≠ 0) (α : Fin d → ℕ) :
    TestFunction d →L[ℝ] ℝ :=
  (SchwartzMap.integralCLM (𝕜 := ℝ) (μ := (volume : Measure (E d)))).comp
    (SchwartzMap.smulLeftCLM (F := ℝ) (eigenfunctionRealE (d := d) ξ hξ α))

@[simp] lemma coeffCLM_E_apply (ξ : ℝ) (hξ : ξ ≠ 0) (α : Fin d → ℕ) (f : TestFunction d) :
    coeffCLM_E (d := d) ξ hξ α f =
      ∫ x : E d, eigenfunctionRealE (d := d) ξ hξ α x * f x := by
  have hg : (eigenfunctionRealE (d := d) ξ hξ α).HasTemperateGrowth :=
    eigenfunctionRealE_hasTemperateGrowth (d := d) ξ hξ α
  simp [coeffCLM_E, SchwartzMap.integralCLM_apply,
    SchwartzMap.smulLeftCLM_apply_apply (F := ℝ) hg, smul_eq_mul]

/-- The coefficient map `𝓢(E d, ℝ) → (Fin d → ℕ) → ℝ`. -/
noncomputable def coeffCLM_E_pi (ξ : ℝ) (hξ : ξ ≠ 0) :
    TestFunction d →L[ℝ] ((Fin d → ℕ) → ℝ) :=
  ContinuousLinearMap.pi (fun α : (Fin d → ℕ) => coeffCLM_E (d := d) ξ hξ α)

@[simp] lemma coeffCLM_E_pi_apply (ξ : ℝ) (hξ : ξ ≠ 0) (f : TestFunction d) (α : Fin d → ℕ) :
    coeffCLM_E_pi (d := d) ξ hξ f α = coeffCLM_E (d := d) ξ hξ α f := rfl

lemma coeffCLM_E_pi_apply' (ξ : ℝ) (hξ : ξ ≠ 0) (α : Fin d → ℕ) :
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : (Fin d → ℕ) => ℝ) α).comp
      (coeffCLM_E_pi (d := d) ξ hξ)
      = coeffCLM_E (d := d) ξ hξ α := by
  ext f
  rfl

end MultiHermite

end

end PhysLean
