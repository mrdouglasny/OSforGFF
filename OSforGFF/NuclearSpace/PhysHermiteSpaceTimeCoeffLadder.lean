/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import OSforGFF.NuclearSpace.PhysHermiteSpaceTimeLadder

/-!
# Ladder relations for spacetime Hermite coefficient functionals

This file turns the coordinate-multiplication ladder identities for the 4D eigenfunctions
`eigenfunctionRealSpaceTime` into corresponding recurrences for the coefficient functionals
`coeffCLM_SpaceTime`.
-/

open scoped BigOperators

namespace PhysLean

noncomputable section

open MeasureTheory

namespace SpaceTimeHermite

/-! ## Multiplication by a coordinate as a continuous linear map -/

/-- Multiply a test function by the `i`-th coordinate. -/
noncomputable def mulCoordCLM (i : Fin STDimension) : TestFunction →L[ℝ] TestFunction :=
  SchwartzMap.smulLeftCLM (F := ℝ) (fun x : SpaceTime ↦ x.ofLp i)

@[simp]
lemma mulCoordCLM_apply (i : Fin STDimension) (f : TestFunction) (x : SpaceTime) :
    mulCoordCLM i f x = x.ofLp i * f x := by
  have hg : (fun x : SpaceTime ↦ x.ofLp i).HasTemperateGrowth := by
    simpa [coordCLM_apply] using (ContinuousLinearMap.hasTemperateGrowth (coordCLM i))
  simpa [mulCoordCLM, smul_eq_mul] using
    (SchwartzMap.smulLeftCLM_apply_apply (F := ℝ) (g := fun x : SpaceTime ↦ x.ofLp i) hg f x)

/-! ## Coefficient ladder for coordinate multiplication -/

lemma coeffCLM_SpaceTime_mulCoord (ξ : ℝ) (hξ : ξ ≠ 0) (i : Fin STDimension)
    (n : ℕ) (f : TestFunction) :
    coeffCLM_SpaceTime ξ hξ n (mulCoordCLM i f) =
      (ξ / 2) * coeffCLM_SpaceTime ξ hξ (raise i n) f
        + (((idx n i : ℕ) : ℝ) * ξ) * coeffCLM_SpaceTime ξ hξ (lower i n) f := by
  have hEigen : (eigenfunctionRealSpaceTime ξ hξ n).HasTemperateGrowth :=
    eigenfunctionRealSpaceTime_hasTemperateGrowth (ξ := ξ) (hξ := hξ) (n := n)
  have hEigenRaise : (eigenfunctionRealSpaceTime ξ hξ (raise i n)).HasTemperateGrowth :=
    eigenfunctionRealSpaceTime_hasTemperateGrowth (ξ := ξ) (hξ := hξ) (n := raise i n)
  have hEigenLower : (eigenfunctionRealSpaceTime ξ hξ (lower i n)).HasTemperateGrowth :=
    eigenfunctionRealSpaceTime_hasTemperateGrowth (ξ := ξ) (hξ := hξ) (n := lower i n)
  have hCoord : (fun x : SpaceTime ↦ x.ofLp i).HasTemperateGrowth := by
    simpa [coordCLM_apply] using (ContinuousLinearMap.hasTemperateGrowth (coordCLM i))
  have hDecomp :
      SchwartzMap.smulLeftCLM (F := ℝ)
          ((eigenfunctionRealSpaceTime ξ hξ n) * (fun x : SpaceTime ↦ x.ofLp i)) f =
        (ξ / 2) • SchwartzMap.smulLeftCLM (F := ℝ) (eigenfunctionRealSpaceTime ξ hξ (raise i n)) f
          + ((((idx n i : ℕ) : ℝ) * ξ) •
              SchwartzMap.smulLeftCLM (F := ℝ) (eigenfunctionRealSpaceTime ξ hξ (lower i n)) f) := by
    ext x
    have hL :
        (SchwartzMap.smulLeftCLM (F := ℝ)
            ((eigenfunctionRealSpaceTime ξ hξ n) * (fun y : SpaceTime ↦ y.ofLp i)) f) x =
          (eigenfunctionRealSpaceTime ξ hξ n x * x.ofLp i) * f x := by
      simpa [smul_eq_mul] using
        (SchwartzMap.smulLeftCLM_apply_apply (F := ℝ)
          (g := (eigenfunctionRealSpaceTime ξ hξ n) * (fun y : SpaceTime ↦ y.ofLp i))
          (hEigen.mul hCoord) f x)
    have hR :
        ((ξ / 2) • SchwartzMap.smulLeftCLM (F := ℝ) (eigenfunctionRealSpaceTime ξ hξ (raise i n)) f
          + ((((idx n i : ℕ) : ℝ) * ξ) •
              SchwartzMap.smulLeftCLM (F := ℝ) (eigenfunctionRealSpaceTime ξ hξ (lower i n)) f)) x =
          (ξ / 2) * (eigenfunctionRealSpaceTime ξ hξ (raise i n) x * f x)
            + ((((idx n i : ℕ) : ℝ) * ξ) *
                (eigenfunctionRealSpaceTime ξ hξ (lower i n) x * f x)) := by
      simp [smul_eq_mul,
        SchwartzMap.smulLeftCLM_apply_apply (F := ℝ)
          (g := eigenfunctionRealSpaceTime ξ hξ (raise i n)) hEigenRaise f x,
        SchwartzMap.smulLeftCLM_apply_apply (F := ℝ)
          (g := eigenfunctionRealSpaceTime ξ hξ (lower i n)) hEigenLower f x,
        mul_assoc]
    rw [hL, hR]
    calc
      (eigenfunctionRealSpaceTime ξ hξ n x * x.ofLp i) * f x
          = (x.ofLp i * eigenfunctionRealSpaceTime ξ hξ n x) * f x := by
              ring
      _ = ((ξ / 2) * eigenfunctionRealSpaceTime ξ hξ (raise i n) x
            + ((((idx n i : ℕ) : ℝ) * ξ) * eigenfunctionRealSpaceTime ξ hξ (lower i n) x)) * f x := by
            have hC :
                (x.ofLp i) * eigenfunctionRealSpaceTime ξ hξ n x =
                  (ξ / 2) * eigenfunctionRealSpaceTime ξ hξ (raise i n) x
                    + ((((idx n i : ℕ) : ℝ) * ξ) * eigenfunctionRealSpaceTime ξ hξ (lower i n) x) := by
              simpa [coordCLM_apply] using
                (coord_mul_eigenfunctionRealSpaceTime
                  (ξ := ξ) (hξ := hξ) (i := i) (n := n) (x := x))
            simpa [mul_assoc] using congrArg (fun t : ℝ => t * f x) hC
      _ = (ξ / 2) * (eigenfunctionRealSpaceTime ξ hξ (raise i n) x * f x)
            + ((((idx n i : ℕ) : ℝ) * ξ) *
                (eigenfunctionRealSpaceTime ξ hξ (lower i n) x * f x)) := by
              ring
  unfold coeffCLM_SpaceTime mulCoordCLM
  simp only [ContinuousLinearMap.comp_apply]
  rw [SchwartzMap.smulLeftCLM_smulLeftCLM_apply (F := ℝ) hEigen hCoord f]
  rw [hDecomp]
  simp only [map_add, ContinuousLinearMap.map_smul, smul_eq_mul, mul_assoc]

end SpaceTimeHermite

end

end PhysLean
