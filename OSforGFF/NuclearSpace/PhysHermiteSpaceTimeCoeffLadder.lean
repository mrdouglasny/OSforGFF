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
  -- We use the underlying `WithLp` coordinate `x.ofLp i` to keep rewriting stable under simp.
  SchwartzMap.smulLeftCLM (F := ℝ) (fun x : SpaceTime ↦ x.ofLp i)

@[simp] lemma mulCoordCLM_apply (i : Fin STDimension) (f : TestFunction) (x : SpaceTime) :
    mulCoordCLM i f x = x.ofLp i * f x := by
  have hg : (fun x : SpaceTime ↦ x.ofLp i).HasTemperateGrowth := by
    -- `x ↦ x.ofLp i` is (the coordinate projection), hence of temperate growth.
    -- We obtain it from the continuous linear map `coordCLM i` and simplify.
    simpa [coordCLM_apply] using (ContinuousLinearMap.hasTemperateGrowth (coordCLM i))
  -- unfold `mulCoordCLM` and evaluate `smulLeftCLM` pointwise
  simpa [mulCoordCLM, smul_eq_mul] using
    (SchwartzMap.smulLeftCLM_apply_apply (F := ℝ) (g := fun x : SpaceTime ↦ x.ofLp i) hg f x)

/-! ## Coefficient ladder for coordinate multiplication -/

lemma coeffCLM_SpaceTime_mulCoord0 (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) (f : TestFunction) :
    coeffCLM_SpaceTime ξ hξ n (mulCoordCLM 0 f) =
      (ξ / 2) * coeffCLM_SpaceTime ξ hξ (raise₀ n) f
        + (unpair₄₁ n * ξ) * coeffCLM_SpaceTime ξ hξ (lower₀ n) f := by
  -- abbreviate the relevant temperate-growth hypotheses
  have hEigen : (eigenfunctionRealSpaceTime ξ hξ n).HasTemperateGrowth :=
    eigenfunctionRealSpaceTime_hasTemperateGrowth (ξ := ξ) (hξ := hξ) (n := n)
  have hEigenRaise : (eigenfunctionRealSpaceTime ξ hξ (raise₀ n)).HasTemperateGrowth :=
    eigenfunctionRealSpaceTime_hasTemperateGrowth (ξ := ξ) (hξ := hξ) (n := raise₀ n)
  have hEigenLower : (eigenfunctionRealSpaceTime ξ hξ (lower₀ n)).HasTemperateGrowth :=
    eigenfunctionRealSpaceTime_hasTemperateGrowth (ξ := ξ) (hξ := hξ) (n := lower₀ n)
  have hCoord : (fun x : SpaceTime ↦ x.ofLp (0 : Fin STDimension)).HasTemperateGrowth := by
    simpa [coordCLM_apply] using
      (ContinuousLinearMap.hasTemperateGrowth (coordCLM (0 : Fin STDimension)))

  -- First, rewrite the Schwartz function inside the coefficient using the 4D ladder identity.
  have hDecomp :
      SchwartzMap.smulLeftCLM (F := ℝ)
          ((eigenfunctionRealSpaceTime ξ hξ n) * (fun x : SpaceTime ↦ x.ofLp 0)) f
        =
      (ξ / 2) •
          SchwartzMap.smulLeftCLM (F := ℝ) (eigenfunctionRealSpaceTime ξ hξ (raise₀ n)) f
        +
      (unpair₄₁ n * ξ) •
          SchwartzMap.smulLeftCLM (F := ℝ) (eigenfunctionRealSpaceTime ξ hξ (lower₀ n)) f := by
    ext x
    -- evaluate the `smulLeftCLM`s pointwise, then use the coordinate ladder lemma and ring arithmetic
    have hL :
        (SchwartzMap.smulLeftCLM (F := ℝ)
            ((eigenfunctionRealSpaceTime ξ hξ n) * (fun y : SpaceTime ↦ y.ofLp 0)) f) x
          =
        (eigenfunctionRealSpaceTime ξ hξ n x * x.ofLp 0) * f x := by
      simpa [smul_eq_mul] using
        (SchwartzMap.smulLeftCLM_apply_apply (F := ℝ)
          (g := (eigenfunctionRealSpaceTime ξ hξ n) * (fun y : SpaceTime ↦ y.ofLp 0))
          (hEigen.mul hCoord) f x)
    have hR :
        ((ξ / 2) • SchwartzMap.smulLeftCLM (F := ℝ) (eigenfunctionRealSpaceTime ξ hξ (raise₀ n)) f
            + (unpair₄₁ n * ξ) •
                SchwartzMap.smulLeftCLM (F := ℝ) (eigenfunctionRealSpaceTime ξ hξ (lower₀ n)) f) x
          =
        (ξ / 2) * (eigenfunctionRealSpaceTime ξ hξ (raise₀ n) x * f x)
          + (unpair₄₁ n * ξ) * (eigenfunctionRealSpaceTime ξ hξ (lower₀ n) x * f x) := by
      -- pointwise scalar/addition on Schwartz maps, then pointwise evaluation of the `smulLeftCLM`s
      simp [smul_eq_mul,
        SchwartzMap.smulLeftCLM_apply_apply (F := ℝ)
          (g := eigenfunctionRealSpaceTime ξ hξ (raise₀ n)) hEigenRaise f x,
        SchwartzMap.smulLeftCLM_apply_apply (F := ℝ)
          (g := eigenfunctionRealSpaceTime ξ hξ (lower₀ n)) hEigenLower f x,
        mul_assoc]
    -- reduce to an algebraic identity of real numbers
    rw [hL, hR]
    calc
      (eigenfunctionRealSpaceTime ξ hξ n x * x.ofLp 0) * f x
          = (x.ofLp 0 * eigenfunctionRealSpaceTime ξ hξ n x) * f x := by
              ring
      _ = ((ξ / 2) * eigenfunctionRealSpaceTime ξ hξ (raise₀ n) x
            + (unpair₄₁ n * ξ) * eigenfunctionRealSpaceTime ξ hξ (lower₀ n) x) * f x := by
            -- rewrite `coord0_mul_eigenfunctionRealSpaceTime` into the `x.ofLp 0` form
            have hC :
                (x.ofLp 0) * eigenfunctionRealSpaceTime ξ hξ n x =
                  (ξ / 2) * eigenfunctionRealSpaceTime ξ hξ (raise₀ n) x
                    + (unpair₄₁ n * ξ) * eigenfunctionRealSpaceTime ξ hξ (lower₀ n) x := by
              simpa using
                (coord0_mul_eigenfunctionRealSpaceTime (ξ := ξ) (hξ := hξ) (n := n) (x := x))
            simpa [mul_assoc] using congrArg (fun t : ℝ ↦ t * f x) hC
      _ = (ξ / 2) * (eigenfunctionRealSpaceTime ξ hξ (raise₀ n) x * f x)
            + (unpair₄₁ n * ξ) * (eigenfunctionRealSpaceTime ξ hξ (lower₀ n) x * f x) := by
            ring

  -- Now apply the linearity of the integral functional and fold back into `coeffCLM_SpaceTime`.
  -- (We intentionally stay in `SchwartzMap` land to avoid separate `Integrable` bookkeeping.)
  -- Unfold the three coefficient functionals and the coordinate-multiplication map (without unfolding integrals).
  unfold coeffCLM_SpaceTime mulCoordCLM
  -- Reduce compositions only.
  simp only [ContinuousLinearMap.comp_apply]
  -- combine the two multiplications inside the integral functional
  rw [SchwartzMap.smulLeftCLM_smulLeftCLM_apply (F := ℝ) hEigen hCoord f]
  -- rewrite by the ladder decomposition proved above
  rw [hDecomp]
  -- linearity of the integral functional
  -- (avoid `simp` here, since `integralCLM_apply` is a simp lemma and would unfold to raw integrals)
  -- `I (a • g + b • h) = a • I g + b • I h`
  simp only [map_add, ContinuousLinearMap.map_smul, smul_eq_mul, mul_assoc]

lemma coeffCLM_SpaceTime_mulCoord1 (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) (f : TestFunction) :
    coeffCLM_SpaceTime ξ hξ n (mulCoordCLM 1 f) =
      (ξ / 2) * coeffCLM_SpaceTime ξ hξ (raise₁ n) f
        + (unpair₄₂ n * ξ) * coeffCLM_SpaceTime ξ hξ (lower₁ n) f := by
  -- abbreviate the relevant temperate-growth hypotheses
  have hEigen : (eigenfunctionRealSpaceTime ξ hξ n).HasTemperateGrowth :=
    eigenfunctionRealSpaceTime_hasTemperateGrowth (ξ := ξ) (hξ := hξ) (n := n)
  have hEigenRaise : (eigenfunctionRealSpaceTime ξ hξ (raise₁ n)).HasTemperateGrowth :=
    eigenfunctionRealSpaceTime_hasTemperateGrowth (ξ := ξ) (hξ := hξ) (n := raise₁ n)
  have hEigenLower : (eigenfunctionRealSpaceTime ξ hξ (lower₁ n)).HasTemperateGrowth :=
    eigenfunctionRealSpaceTime_hasTemperateGrowth (ξ := ξ) (hξ := hξ) (n := lower₁ n)
  have hCoord : (fun x : SpaceTime ↦ x.ofLp (1 : Fin STDimension)).HasTemperateGrowth := by
    simpa [coordCLM_apply] using
      (ContinuousLinearMap.hasTemperateGrowth (coordCLM (1 : Fin STDimension)))

  have hDecomp :
      SchwartzMap.smulLeftCLM (F := ℝ)
          ((eigenfunctionRealSpaceTime ξ hξ n) * (fun x : SpaceTime ↦ x.ofLp 1)) f
        =
      (ξ / 2) •
          SchwartzMap.smulLeftCLM (F := ℝ) (eigenfunctionRealSpaceTime ξ hξ (raise₁ n)) f
        +
      (unpair₄₂ n * ξ) •
          SchwartzMap.smulLeftCLM (F := ℝ) (eigenfunctionRealSpaceTime ξ hξ (lower₁ n)) f := by
    ext x
    have hL :
        (SchwartzMap.smulLeftCLM (F := ℝ)
            ((eigenfunctionRealSpaceTime ξ hξ n) * (fun y : SpaceTime ↦ y.ofLp 1)) f) x
          =
        (eigenfunctionRealSpaceTime ξ hξ n x * x.ofLp 1) * f x := by
      simpa [smul_eq_mul] using
        (SchwartzMap.smulLeftCLM_apply_apply (F := ℝ)
          (g := (eigenfunctionRealSpaceTime ξ hξ n) * (fun y : SpaceTime ↦ y.ofLp 1))
          (hEigen.mul hCoord) f x)
    have hR :
        ((ξ / 2) • SchwartzMap.smulLeftCLM (F := ℝ) (eigenfunctionRealSpaceTime ξ hξ (raise₁ n)) f
            + (unpair₄₂ n * ξ) •
                SchwartzMap.smulLeftCLM (F := ℝ) (eigenfunctionRealSpaceTime ξ hξ (lower₁ n)) f) x
          =
        (ξ / 2) * (eigenfunctionRealSpaceTime ξ hξ (raise₁ n) x * f x)
          + (unpair₄₂ n * ξ) * (eigenfunctionRealSpaceTime ξ hξ (lower₁ n) x * f x) := by
      simp [smul_eq_mul,
        SchwartzMap.smulLeftCLM_apply_apply (F := ℝ)
          (g := eigenfunctionRealSpaceTime ξ hξ (raise₁ n)) hEigenRaise f x,
        SchwartzMap.smulLeftCLM_apply_apply (F := ℝ)
          (g := eigenfunctionRealSpaceTime ξ hξ (lower₁ n)) hEigenLower f x,
        mul_assoc]
    rw [hL, hR]
    calc
      (eigenfunctionRealSpaceTime ξ hξ n x * x.ofLp 1) * f x
          = (x.ofLp 1 * eigenfunctionRealSpaceTime ξ hξ n x) * f x := by
              ring
      _ = ((ξ / 2) * eigenfunctionRealSpaceTime ξ hξ (raise₁ n) x
            + (unpair₄₂ n * ξ) * eigenfunctionRealSpaceTime ξ hξ (lower₁ n) x) * f x := by
            have hC :
                (x.ofLp 1) * eigenfunctionRealSpaceTime ξ hξ n x =
                  (ξ / 2) * eigenfunctionRealSpaceTime ξ hξ (raise₁ n) x
                    + (unpair₄₂ n * ξ) * eigenfunctionRealSpaceTime ξ hξ (lower₁ n) x := by
              simpa using
                (coord1_mul_eigenfunctionRealSpaceTime (ξ := ξ) (hξ := hξ) (n := n) (x := x))
            simpa [mul_assoc] using congrArg (fun t : ℝ ↦ t * f x) hC
      _ = (ξ / 2) * (eigenfunctionRealSpaceTime ξ hξ (raise₁ n) x * f x)
            + (unpair₄₂ n * ξ) * (eigenfunctionRealSpaceTime ξ hξ (lower₁ n) x * f x) := by
            ring

  unfold coeffCLM_SpaceTime mulCoordCLM
  simp only [ContinuousLinearMap.comp_apply]
  rw [SchwartzMap.smulLeftCLM_smulLeftCLM_apply (F := ℝ) hEigen hCoord f]
  rw [hDecomp]
  simp only [map_add, ContinuousLinearMap.map_smul, smul_eq_mul, mul_assoc]

lemma coeffCLM_SpaceTime_mulCoord2 (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) (f : TestFunction) :
    coeffCLM_SpaceTime ξ hξ n (mulCoordCLM 2 f) =
      (ξ / 2) * coeffCLM_SpaceTime ξ hξ (raise₂ n) f
        + (unpair₄₃ n * ξ) * coeffCLM_SpaceTime ξ hξ (lower₂ n) f := by
  have hEigen : (eigenfunctionRealSpaceTime ξ hξ n).HasTemperateGrowth :=
    eigenfunctionRealSpaceTime_hasTemperateGrowth (ξ := ξ) (hξ := hξ) (n := n)
  have hEigenRaise : (eigenfunctionRealSpaceTime ξ hξ (raise₂ n)).HasTemperateGrowth :=
    eigenfunctionRealSpaceTime_hasTemperateGrowth (ξ := ξ) (hξ := hξ) (n := raise₂ n)
  have hEigenLower : (eigenfunctionRealSpaceTime ξ hξ (lower₂ n)).HasTemperateGrowth :=
    eigenfunctionRealSpaceTime_hasTemperateGrowth (ξ := ξ) (hξ := hξ) (n := lower₂ n)
  have hCoord : (fun x : SpaceTime ↦ x.ofLp (2 : Fin STDimension)).HasTemperateGrowth := by
    simpa [coordCLM_apply] using
      (ContinuousLinearMap.hasTemperateGrowth (coordCLM (2 : Fin STDimension)))

  have hDecomp :
      SchwartzMap.smulLeftCLM (F := ℝ)
          ((eigenfunctionRealSpaceTime ξ hξ n) * (fun x : SpaceTime ↦ x.ofLp 2)) f
        =
      (ξ / 2) •
          SchwartzMap.smulLeftCLM (F := ℝ) (eigenfunctionRealSpaceTime ξ hξ (raise₂ n)) f
        +
      (unpair₄₃ n * ξ) •
          SchwartzMap.smulLeftCLM (F := ℝ) (eigenfunctionRealSpaceTime ξ hξ (lower₂ n)) f := by
    ext x
    have hL :
        (SchwartzMap.smulLeftCLM (F := ℝ)
            ((eigenfunctionRealSpaceTime ξ hξ n) * (fun y : SpaceTime ↦ y.ofLp 2)) f) x
          =
        (eigenfunctionRealSpaceTime ξ hξ n x * x.ofLp 2) * f x := by
      simpa [smul_eq_mul] using
        (SchwartzMap.smulLeftCLM_apply_apply (F := ℝ)
          (g := (eigenfunctionRealSpaceTime ξ hξ n) * (fun y : SpaceTime ↦ y.ofLp 2))
          (hEigen.mul hCoord) f x)
    have hR :
        ((ξ / 2) • SchwartzMap.smulLeftCLM (F := ℝ) (eigenfunctionRealSpaceTime ξ hξ (raise₂ n)) f
            + (unpair₄₃ n * ξ) •
                SchwartzMap.smulLeftCLM (F := ℝ) (eigenfunctionRealSpaceTime ξ hξ (lower₂ n)) f) x
          =
        (ξ / 2) * (eigenfunctionRealSpaceTime ξ hξ (raise₂ n) x * f x)
          + (unpair₄₃ n * ξ) * (eigenfunctionRealSpaceTime ξ hξ (lower₂ n) x * f x) := by
      simp [smul_eq_mul,
        SchwartzMap.smulLeftCLM_apply_apply (F := ℝ)
          (g := eigenfunctionRealSpaceTime ξ hξ (raise₂ n)) hEigenRaise f x,
        SchwartzMap.smulLeftCLM_apply_apply (F := ℝ)
          (g := eigenfunctionRealSpaceTime ξ hξ (lower₂ n)) hEigenLower f x,
        mul_assoc]
    rw [hL, hR]
    calc
      (eigenfunctionRealSpaceTime ξ hξ n x * x.ofLp 2) * f x
          = (x.ofLp 2 * eigenfunctionRealSpaceTime ξ hξ n x) * f x := by
              ring
      _ = ((ξ / 2) * eigenfunctionRealSpaceTime ξ hξ (raise₂ n) x
            + (unpair₄₃ n * ξ) * eigenfunctionRealSpaceTime ξ hξ (lower₂ n) x) * f x := by
            have hC :
                (x.ofLp 2) * eigenfunctionRealSpaceTime ξ hξ n x =
                  (ξ / 2) * eigenfunctionRealSpaceTime ξ hξ (raise₂ n) x
                    + (unpair₄₃ n * ξ) * eigenfunctionRealSpaceTime ξ hξ (lower₂ n) x := by
              simpa using
                (coord2_mul_eigenfunctionRealSpaceTime (ξ := ξ) (hξ := hξ) (n := n) (x := x))
            simpa [mul_assoc] using congrArg (fun t : ℝ ↦ t * f x) hC
      _ = (ξ / 2) * (eigenfunctionRealSpaceTime ξ hξ (raise₂ n) x * f x)
            + (unpair₄₃ n * ξ) * (eigenfunctionRealSpaceTime ξ hξ (lower₂ n) x * f x) := by
            ring

  unfold coeffCLM_SpaceTime mulCoordCLM
  simp only [ContinuousLinearMap.comp_apply]
  rw [SchwartzMap.smulLeftCLM_smulLeftCLM_apply (F := ℝ) hEigen hCoord f]
  rw [hDecomp]
  simp only [map_add, ContinuousLinearMap.map_smul, smul_eq_mul, mul_assoc]

lemma coeffCLM_SpaceTime_mulCoord3 (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) (f : TestFunction) :
    coeffCLM_SpaceTime ξ hξ n (mulCoordCLM 3 f) =
      (ξ / 2) * coeffCLM_SpaceTime ξ hξ (raise₃ n) f
        + (unpair₄₄ n * ξ) * coeffCLM_SpaceTime ξ hξ (lower₃ n) f := by
  have hEigen : (eigenfunctionRealSpaceTime ξ hξ n).HasTemperateGrowth :=
    eigenfunctionRealSpaceTime_hasTemperateGrowth (ξ := ξ) (hξ := hξ) (n := n)
  have hEigenRaise : (eigenfunctionRealSpaceTime ξ hξ (raise₃ n)).HasTemperateGrowth :=
    eigenfunctionRealSpaceTime_hasTemperateGrowth (ξ := ξ) (hξ := hξ) (n := raise₃ n)
  have hEigenLower : (eigenfunctionRealSpaceTime ξ hξ (lower₃ n)).HasTemperateGrowth :=
    eigenfunctionRealSpaceTime_hasTemperateGrowth (ξ := ξ) (hξ := hξ) (n := lower₃ n)
  have hCoord : (fun x : SpaceTime ↦ x.ofLp (3 : Fin STDimension)).HasTemperateGrowth := by
    simpa [coordCLM_apply] using
      (ContinuousLinearMap.hasTemperateGrowth (coordCLM (3 : Fin STDimension)))

  have hDecomp :
      SchwartzMap.smulLeftCLM (F := ℝ)
          ((eigenfunctionRealSpaceTime ξ hξ n) * (fun x : SpaceTime ↦ x.ofLp 3)) f
        =
      (ξ / 2) •
          SchwartzMap.smulLeftCLM (F := ℝ) (eigenfunctionRealSpaceTime ξ hξ (raise₃ n)) f
        +
      (unpair₄₄ n * ξ) •
          SchwartzMap.smulLeftCLM (F := ℝ) (eigenfunctionRealSpaceTime ξ hξ (lower₃ n)) f := by
    ext x
    have hL :
        (SchwartzMap.smulLeftCLM (F := ℝ)
            ((eigenfunctionRealSpaceTime ξ hξ n) * (fun y : SpaceTime ↦ y.ofLp 3)) f) x
          =
        (eigenfunctionRealSpaceTime ξ hξ n x * x.ofLp 3) * f x := by
      simpa [smul_eq_mul] using
        (SchwartzMap.smulLeftCLM_apply_apply (F := ℝ)
          (g := (eigenfunctionRealSpaceTime ξ hξ n) * (fun y : SpaceTime ↦ y.ofLp 3))
          (hEigen.mul hCoord) f x)
    have hR :
        ((ξ / 2) • SchwartzMap.smulLeftCLM (F := ℝ) (eigenfunctionRealSpaceTime ξ hξ (raise₃ n)) f
            + (unpair₄₄ n * ξ) •
                SchwartzMap.smulLeftCLM (F := ℝ) (eigenfunctionRealSpaceTime ξ hξ (lower₃ n)) f) x
          =
        (ξ / 2) * (eigenfunctionRealSpaceTime ξ hξ (raise₃ n) x * f x)
          + (unpair₄₄ n * ξ) * (eigenfunctionRealSpaceTime ξ hξ (lower₃ n) x * f x) := by
      simp [smul_eq_mul,
        SchwartzMap.smulLeftCLM_apply_apply (F := ℝ)
          (g := eigenfunctionRealSpaceTime ξ hξ (raise₃ n)) hEigenRaise f x,
        SchwartzMap.smulLeftCLM_apply_apply (F := ℝ)
          (g := eigenfunctionRealSpaceTime ξ hξ (lower₃ n)) hEigenLower f x,
        mul_assoc]
    rw [hL, hR]
    calc
      (eigenfunctionRealSpaceTime ξ hξ n x * x.ofLp 3) * f x
          = (x.ofLp 3 * eigenfunctionRealSpaceTime ξ hξ n x) * f x := by
              ring
      _ = ((ξ / 2) * eigenfunctionRealSpaceTime ξ hξ (raise₃ n) x
            + (unpair₄₄ n * ξ) * eigenfunctionRealSpaceTime ξ hξ (lower₃ n) x) * f x := by
            have hC :
                (x.ofLp 3) * eigenfunctionRealSpaceTime ξ hξ n x =
                  (ξ / 2) * eigenfunctionRealSpaceTime ξ hξ (raise₃ n) x
                    + (unpair₄₄ n * ξ) * eigenfunctionRealSpaceTime ξ hξ (lower₃ n) x := by
              simpa using
                (coord3_mul_eigenfunctionRealSpaceTime (ξ := ξ) (hξ := hξ) (n := n) (x := x))
            simpa [mul_assoc] using congrArg (fun t : ℝ ↦ t * f x) hC
      _ = (ξ / 2) * (eigenfunctionRealSpaceTime ξ hξ (raise₃ n) x * f x)
            + (unpair₄₄ n * ξ) * (eigenfunctionRealSpaceTime ξ hξ (lower₃ n) x * f x) := by
            ring

  unfold coeffCLM_SpaceTime mulCoordCLM
  simp only [ContinuousLinearMap.comp_apply]
  rw [SchwartzMap.smulLeftCLM_smulLeftCLM_apply (F := ℝ) hEigen hCoord f]
  rw [hDecomp]
  simp only [map_add, ContinuousLinearMap.map_smul, smul_eq_mul, mul_assoc]

end SpaceTimeHermite

end

end PhysLean
