/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import OSforGFF.NuclearSpace.PhysHermiteSpaceTimeLadder

import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Distribution.DerivNotation
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Derivative ladder relations for spacetime Hermite coefficient functionals

We turn the **coordinate-derivative** ladder identities for the 4D eigenfunctions
`eigenfunctionRealSpaceTime` into corresponding recurrences for the coefficient functionals
`coeffCLM_SpaceTime`.
-/

open scoped BigOperators LineDeriv

namespace PhysLean

noncomputable section

open MeasureTheory

namespace SpaceTimeHermite

/-! ## Coordinate unit vectors and Schwartz directional derivatives -/

/-- The coordinate unit vector in spacetime. -/
def unitVec (i : Fin STDimension) : SpaceTime :=
  EuclideanSpace.single i (1 : ℝ)

@[simp]
lemma coordCLM_unitVec (i j : Fin STDimension) :
    coordCLM i (unitVec j) = if i = j then 1 else 0 := by
  simp [unitVec]

@[simp]
lemma unitVec_ofLp (i j : Fin STDimension) :
    (unitVec j).ofLp i = if i = j then 1 else 0 := by
  simpa [coordCLM_apply] using (coordCLM_unitVec (i := i) (j := j))

@[simp]
lemma coordCLM_add_smul_unitVec (i j : Fin STDimension) (x : SpaceTime) (t : ℝ) :
    coordCLM i (x + t • unitVec j) = coordCLM i x + if i = j then t else 0 := by
  calc
    coordCLM i (x + t • unitVec j)
        = coordCLM i x + coordCLM i (t • unitVec j) := by
            simp
    _ = coordCLM i x + t • coordCLM i (unitVec j) := by simp
    _ = coordCLM i x + t * (if i = j then 1 else 0) := by
            simp [smul_eq_mul]
    _ = coordCLM i x + if i = j then t else 0 := by
            by_cases h : i = j <;> simp [h]

/-- Directional derivative in the `i`-th coordinate direction, as a continuous linear map on
`TestFunction`. -/
noncomputable def derivCoordCLM (i : Fin STDimension) : TestFunction →L[ℝ] TestFunction :=
  LineDeriv.lineDerivOpCLM ℝ TestFunction (unitVec i)

@[simp]
lemma derivCoordCLM_apply (i : Fin STDimension) (f : TestFunction) :
    derivCoordCLM i f = ∂_{unitVec i} f := by
  simp [derivCoordCLM]

@[simp]
lemma derivCoordCLM_apply_apply (i : Fin STDimension) (f : TestFunction) (x : SpaceTime) :
    derivCoordCLM i f x = (∂_{unitVec i} f) x := by
  simp [derivCoordCLM]

/-! ## Line-derivative ladder for the spacetime eigenfunctions -/

private lemma lineDeriv_eigenfunctionRealSpaceTime_unitVec0 (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) (x : SpaceTime) :
    lineDeriv ℝ (eigenfunctionRealSpaceTime ξ hξ n) x (unitVec 0) =
      (unpair₄₁ n / ξ) * eigenfunctionRealSpaceTime ξ hξ (lower₀ n) x
        - (1 / (2 * ξ)) * eigenfunctionRealSpaceTime ξ hξ (raise₀ n) x := by
  -- abbreviate the three *constant* factors (coordinates 1,2,3 stay fixed along `unitVec 0`)
  set b : ℝ := eigenfunctionRealSchwartz ξ hξ (unpair₄₂ n) (coordCLM 1 x)
  set c : ℝ := eigenfunctionRealSchwartz ξ hξ (unpair₄₃ n) (coordCLM 2 x)
  set d : ℝ := eigenfunctionRealSchwartz ξ hξ (unpair₄₄ n) (coordCLM 3 x)
  let u : ℝ → ℝ := fun t : ℝ ↦ eigenfunctionRealSchwartz ξ hξ (unpair₄₁ n) (coordCLM 0 x + t)
  let k : ℝ := b * c * d
  have hcurve :
      (fun t : ℝ ↦ eigenfunctionRealSpaceTime ξ hξ n (x + t • unitVec (0 : Fin STDimension))) =
        fun t : ℝ ↦ u t * k := by
    funext t
    have h0 :
        coordCLM (0 : Fin STDimension) (x + t • unitVec (0 : Fin STDimension)) =
          coordCLM 0 x + t := by
      simp
    have h1 :
        coordCLM (1 : Fin STDimension) (x + t • unitVec (0 : Fin STDimension)) = coordCLM 1 x := by
      simp
    have h2 :
        coordCLM (2 : Fin STDimension) (x + t • unitVec (0 : Fin STDimension)) = coordCLM 2 x := by
      simp
    have h3 :
        coordCLM (3 : Fin STDimension) (x + t • unitVec (0 : Fin STDimension)) = coordCLM 3 x := by
      simp
    simp [eigenfunctionRealSpaceTime, u, k, b, c, d, h0, h1, h2, h3, mul_assoc,
      -eigenfunctionRealSchwartz_apply]
  have hline :
      lineDeriv ℝ (eigenfunctionRealSpaceTime ξ hξ n) x (unitVec 0) =
        deriv (fun t : ℝ ↦ u t * k) 0 := by
    simp [lineDeriv, hcurve]
  have hderiv_mul_const : deriv (fun t : ℝ ↦ u t * k) 0 = (deriv u 0) * k := by
    simp [deriv_mul_const_field]
  have hshift :
      deriv u 0 = deriv (eigenfunctionRealSchwartz ξ hξ (unpair₄₁ n)) (coordCLM 0 x) := by
    simpa [u] using
      (deriv_comp_const_add (f := eigenfunctionRealSchwartz ξ hξ (unpair₄₁ n)) (a := coordCLM 0 x) (x := (0 : ℝ)))
  have hderiv1D :
      deriv u 0 =
        (unpair₄₁ n / ξ) * eigenfunctionRealSchwartz ξ hξ (unpair₄₁ n - 1) (coordCLM 0 x)
          - (1 / (2 * ξ)) * eigenfunctionRealSchwartz ξ hξ (unpair₄₁ n + 1) (coordCLM 0 x) := by
    rw [hshift]
    simpa using
      (PhysLean.deriv_eigenfunctionRealSchwartz (ξ := ξ) (hξ := hξ)
        (n := unpair₄₁ n) (x := coordCLM 0 x))
  -- fold the products back into the 4D eigenfunctions at `lower₀` and `raise₀`
  set aM : ℝ := eigenfunctionRealSchwartz ξ hξ (unpair₄₁ n - 1) (coordCLM 0 x)
  set aP : ℝ := eigenfunctionRealSchwartz ξ hξ (unpair₄₁ n + 1) (coordCLM 0 x)
  have hkLower : eigenfunctionRealSpaceTime ξ hξ (lower₀ n) x = aM * b * c * d := by
    simp [eigenfunctionRealSpaceTime, aM, b, c, d, mul_assoc, -eigenfunctionRealSchwartz_apply]
  have hkRaise : eigenfunctionRealSpaceTime ξ hξ (raise₀ n) x = aP * b * c * d := by
    simp [eigenfunctionRealSpaceTime, aP, b, c, d, mul_assoc, -eigenfunctionRealSchwartz_apply]
  have hmain :
      lineDeriv ℝ (eigenfunctionRealSpaceTime ξ hξ n) x (unitVec 0)
        =
      ((unpair₄₁ n / ξ) * aM - (1 / (2 * ξ)) * aP) * k := by
    simp [hline, hderiv1D, aM, aP, k, mul_assoc, sub_eq_add_neg]
  calc
    lineDeriv ℝ (eigenfunctionRealSpaceTime ξ hξ n) x (unitVec 0)
        = ((unpair₄₁ n / ξ) * aM - (1 / (2 * ξ)) * aP) * k := hmain
    _ = (unpair₄₁ n / ξ) * (aM * k) - (1 / (2 * ξ)) * (aP * k) := by
          simp [sub_mul, mul_assoc]
    _ = (unpair₄₁ n / ξ) * eigenfunctionRealSpaceTime ξ hξ (lower₀ n) x
          - (1 / (2 * ξ)) * eigenfunctionRealSpaceTime ξ hξ (raise₀ n) x := by
          simp [hkLower, hkRaise, k, mul_assoc, -eigenfunctionRealSchwartz_apply]

private lemma lineDeriv_eigenfunctionRealSpaceTime_unitVec1 (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) (x : SpaceTime) :
    lineDeriv ℝ (eigenfunctionRealSpaceTime ξ hξ n) x (unitVec 1) =
      (unpair₄₂ n / ξ) * eigenfunctionRealSpaceTime ξ hξ (lower₁ n) x
        - (1 / (2 * ξ)) * eigenfunctionRealSpaceTime ξ hξ (raise₁ n) x := by
  -- constants: coordinates 0,2,3 stay fixed along `unitVec 1`
  set a0 : ℝ := eigenfunctionRealSchwartz ξ hξ (unpair₄₁ n) (coordCLM 0 x)
  set c : ℝ := eigenfunctionRealSchwartz ξ hξ (unpair₄₃ n) (coordCLM 2 x)
  set d : ℝ := eigenfunctionRealSchwartz ξ hξ (unpair₄₄ n) (coordCLM 3 x)
  let u : ℝ → ℝ := fun t : ℝ ↦ eigenfunctionRealSchwartz ξ hξ (unpair₄₂ n) (coordCLM 1 x + t)
  let k : ℝ := c * d
  have hcurve :
      (fun t : ℝ ↦ eigenfunctionRealSpaceTime ξ hξ n (x + t • unitVec (1 : Fin STDimension))) =
        fun t : ℝ ↦ a0 * u t * k := by
    funext t
    have h0 : coordCLM (0 : Fin STDimension) (x + t • unitVec (1 : Fin STDimension)) = coordCLM 0 x := by
      simp
    have h1 : coordCLM (1 : Fin STDimension) (x + t • unitVec (1 : Fin STDimension)) = coordCLM 1 x + t := by
      simp
    have h2 : coordCLM (2 : Fin STDimension) (x + t • unitVec (1 : Fin STDimension)) = coordCLM 2 x := by
      simp
    have h3 : coordCLM (3 : Fin STDimension) (x + t • unitVec (1 : Fin STDimension)) = coordCLM 3 x := by
      simp
    simp [eigenfunctionRealSpaceTime, a0, c, d, u, k, h0, h1, h2, h3, mul_assoc,
      -eigenfunctionRealSchwartz_apply]
  have hline :
      lineDeriv ℝ (eigenfunctionRealSpaceTime ξ hξ n) x (unitVec 1) =
        deriv (fun t : ℝ ↦ a0 * u t * k) 0 := by
    simp [lineDeriv, hcurve]
  have hderiv_const_mul :
      deriv (fun t : ℝ ↦ a0 * u t * k) 0 = a0 * (deriv u 0) * k := by
    have hk :
        deriv (fun t : ℝ ↦ (a0 * u t) * k) 0 = deriv (fun t : ℝ ↦ a0 * u t) 0 * k := by
      simp [deriv_mul_const_field]
    have ha : deriv (fun t : ℝ ↦ a0 * u t) 0 = a0 * deriv u 0 := by
      simp [deriv_const_mul_field]
    calc
      deriv (fun t : ℝ ↦ a0 * u t * k) 0
          = deriv (fun t : ℝ ↦ (a0 * u t) * k) 0 := by rfl
      _ = deriv (fun t : ℝ ↦ a0 * u t) 0 * k := hk
      _ = (a0 * deriv u 0) * k := by rw [ha]
      _ = a0 * (deriv u 0) * k := by simp [mul_assoc]
  have hshift :
      deriv u 0 = deriv (eigenfunctionRealSchwartz ξ hξ (unpair₄₂ n)) (coordCLM 1 x) := by
    simpa [u] using
      (deriv_comp_const_add (f := eigenfunctionRealSchwartz ξ hξ (unpair₄₂ n)) (a := coordCLM 1 x) (x := (0 : ℝ)))
  have hderiv1D :
      deriv u 0 =
        (unpair₄₂ n / ξ) * eigenfunctionRealSchwartz ξ hξ (unpair₄₂ n - 1) (coordCLM 1 x)
          - (1 / (2 * ξ)) * eigenfunctionRealSchwartz ξ hξ (unpair₄₂ n + 1) (coordCLM 1 x) := by
    rw [hshift]
    simpa using
      (PhysLean.deriv_eigenfunctionRealSchwartz (ξ := ξ) (hξ := hξ) (n := unpair₄₂ n) (x := coordCLM 1 x))
  set aM : ℝ := eigenfunctionRealSchwartz ξ hξ (unpair₄₂ n - 1) (coordCLM 1 x) with haM
  set aP : ℝ := eigenfunctionRealSchwartz ξ hξ (unpair₄₂ n + 1) (coordCLM 1 x) with haP
  have hkLower : eigenfunctionRealSpaceTime ξ hξ (lower₁ n) x = a0 * aM * c * d := by
    simp [eigenfunctionRealSpaceTime, a0, aM, c, d, mul_assoc, -eigenfunctionRealSchwartz_apply]
  have hkRaise : eigenfunctionRealSpaceTime ξ hξ (raise₁ n) x = a0 * aP * c * d := by
    simp [eigenfunctionRealSpaceTime, a0, aP, c, d, mul_assoc, -eigenfunctionRealSchwartz_apply]
  have : lineDeriv ℝ (eigenfunctionRealSpaceTime ξ hξ n) x (unitVec 1)
      =
      ((unpair₄₂ n / ξ) * (a0 * aM * c * d) - (1 / (2 * ξ)) * (a0 * aP * c * d)) := by
    -- unfold `lineDeriv` into a 1D derivative, then substitute the curve derivative and the 1D ladder
    rw [hline, hderiv_const_mul, hderiv1D]
    -- scalar/product algebra in `ℝ`
    simp [k, mul_assoc, sub_eq_add_neg]
    ring
  -- fold back the shifted products into `eigenfunctionRealSpaceTime`
  -- (use `hkLower`/`hkRaise` in the reverse direction).
  simpa [hkLower, hkRaise] using this

private lemma lineDeriv_eigenfunctionRealSpaceTime_unitVec2 (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) (x : SpaceTime) :
    lineDeriv ℝ (eigenfunctionRealSpaceTime ξ hξ n) x (unitVec 2) =
      (unpair₄₃ n / ξ) * eigenfunctionRealSpaceTime ξ hξ (lower₂ n) x
        - (1 / (2 * ξ)) * eigenfunctionRealSpaceTime ξ hξ (raise₂ n) x := by
  -- constants: coordinates 0,1,3 stay fixed along `unitVec 2`
  set a0 : ℝ := eigenfunctionRealSchwartz ξ hξ (unpair₄₁ n) (coordCLM 0 x)
  set b : ℝ := eigenfunctionRealSchwartz ξ hξ (unpair₄₂ n) (coordCLM 1 x)
  set d : ℝ := eigenfunctionRealSchwartz ξ hξ (unpair₄₄ n) (coordCLM 3 x)
  let u : ℝ → ℝ := fun t : ℝ ↦ eigenfunctionRealSchwartz ξ hξ (unpair₄₃ n) (coordCLM 2 x + t)
  have hcurve :
      (fun t : ℝ ↦ eigenfunctionRealSpaceTime ξ hξ n (x + t • unitVec (2 : Fin STDimension))) =
        fun t : ℝ ↦ a0 * b * u t * d := by
    funext t
    have h0 : coordCLM (0 : Fin STDimension) (x + t • unitVec (2 : Fin STDimension)) = coordCLM 0 x := by
      simp
    have h1 : coordCLM (1 : Fin STDimension) (x + t • unitVec (2 : Fin STDimension)) = coordCLM 1 x := by
      simp
    have h2 :
        coordCLM (2 : Fin STDimension) (x + t • unitVec (2 : Fin STDimension)) =
          coordCLM 2 x + t := by
      simp
    have h3 : coordCLM (3 : Fin STDimension) (x + t • unitVec (2 : Fin STDimension)) = coordCLM 3 x := by
      simp
    simp [eigenfunctionRealSpaceTime, a0, b, d, u, h0, h1, h2, h3, mul_assoc,
      -eigenfunctionRealSchwartz_apply]
  have hline :
      lineDeriv ℝ (eigenfunctionRealSpaceTime ξ hξ n) x (unitVec 2) =
        deriv (fun t : ℝ ↦ a0 * b * u t * d) 0 := by
    simp [lineDeriv, hcurve]
  have hderiv_const_mul :
      deriv (fun t : ℝ ↦ a0 * b * u t * d) 0 = a0 * b * (deriv u 0) * d := by
    have hd :
        deriv (fun t : ℝ ↦ (a0 * b * u t) * d) 0 = deriv (fun t : ℝ ↦ a0 * b * u t) 0 * d := by
      simp [deriv_mul_const_field]
    have hab : deriv (fun t : ℝ ↦ a0 * b * u t) 0 = (a0 * b) * deriv u 0 := by
      simp [mul_assoc, deriv_const_mul_field]
    calc
      deriv (fun t : ℝ ↦ a0 * b * u t * d) 0
          = deriv (fun t : ℝ ↦ (a0 * b * u t) * d) 0 := by rfl
      _ = deriv (fun t : ℝ ↦ a0 * b * u t) 0 * d := hd
      _ = ((a0 * b) * deriv u 0) * d := by rw [hab]
      _ = a0 * b * (deriv u 0) * d := by simp [mul_assoc]
  have hshift :
      deriv u 0 = deriv (eigenfunctionRealSchwartz ξ hξ (unpair₄₃ n)) (coordCLM 2 x) := by
    simpa [u] using
      (deriv_comp_const_add (f := eigenfunctionRealSchwartz ξ hξ (unpair₄₃ n)) (a := coordCLM 2 x) (x := (0 : ℝ)))
  have hderiv1D :
      deriv u 0 =
        (unpair₄₃ n / ξ) * eigenfunctionRealSchwartz ξ hξ (unpair₄₃ n - 1) (coordCLM 2 x)
          - (1 / (2 * ξ)) * eigenfunctionRealSchwartz ξ hξ (unpair₄₃ n + 1) (coordCLM 2 x) := by
    rw [hshift]
    simpa using
      (PhysLean.deriv_eigenfunctionRealSchwartz (ξ := ξ) (hξ := hξ) (n := unpair₄₃ n) (x := coordCLM 2 x))
  set aM : ℝ := eigenfunctionRealSchwartz ξ hξ (unpair₄₃ n - 1) (coordCLM 2 x)
  set aP : ℝ := eigenfunctionRealSchwartz ξ hξ (unpair₄₃ n + 1) (coordCLM 2 x)
  have hkLower : eigenfunctionRealSpaceTime ξ hξ (lower₂ n) x = a0 * b * aM * d := by
    simp [eigenfunctionRealSpaceTime, a0, b, aM, d, mul_assoc, -eigenfunctionRealSchwartz_apply]
  have hkRaise : eigenfunctionRealSpaceTime ξ hξ (raise₂ n) x = a0 * b * aP * d := by
    simp [eigenfunctionRealSpaceTime, a0, b, aP, d, mul_assoc, -eigenfunctionRealSchwartz_apply]
  have : lineDeriv ℝ (eigenfunctionRealSpaceTime ξ hξ n) x (unitVec 2)
      =
      ((unpair₄₃ n / ξ) * (a0 * b * aM * d) - (1 / (2 * ξ)) * (a0 * b * aP * d)) := by
    rw [hline, hderiv_const_mul]
    rw [hderiv1D]
    simp [aM, aP, mul_assoc, -eigenfunctionRealSchwartz_apply]
    ring
  simpa [hkLower, hkRaise, mul_assoc, -eigenfunctionRealSchwartz_apply] using this

private lemma lineDeriv_eigenfunctionRealSpaceTime_unitVec3 (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) (x : SpaceTime) :
    lineDeriv ℝ (eigenfunctionRealSpaceTime ξ hξ n) x (unitVec 3) =
      (unpair₄₄ n / ξ) * eigenfunctionRealSpaceTime ξ hξ (lower₃ n) x
        - (1 / (2 * ξ)) * eigenfunctionRealSpaceTime ξ hξ (raise₃ n) x := by
  -- constants: coordinates 0,1,2 stay fixed along `unitVec 3`
  set a0 : ℝ := eigenfunctionRealSchwartz ξ hξ (unpair₄₁ n) (coordCLM 0 x)
  set b : ℝ := eigenfunctionRealSchwartz ξ hξ (unpair₄₂ n) (coordCLM 1 x)
  set c : ℝ := eigenfunctionRealSchwartz ξ hξ (unpair₄₃ n) (coordCLM 2 x)
  let u : ℝ → ℝ := fun t : ℝ ↦ eigenfunctionRealSchwartz ξ hξ (unpair₄₄ n) (coordCLM 3 x + t)
  let k : ℝ := a0 * b * c
  have hcurve :
      (fun t : ℝ ↦ eigenfunctionRealSpaceTime ξ hξ n (x + t • unitVec (3 : Fin STDimension))) =
        fun t : ℝ ↦ k * u t := by
    funext t
    have h0 : coordCLM (0 : Fin STDimension) (x + t • unitVec (3 : Fin STDimension)) = coordCLM 0 x := by
      simp
    have h1 : coordCLM (1 : Fin STDimension) (x + t • unitVec (3 : Fin STDimension)) = coordCLM 1 x := by
      simp
    have h2 : coordCLM (2 : Fin STDimension) (x + t • unitVec (3 : Fin STDimension)) = coordCLM 2 x := by
      simp
    have h3 :
        coordCLM (3 : Fin STDimension) (x + t • unitVec (3 : Fin STDimension)) =
          coordCLM 3 x + t := by
      simp
    simp [eigenfunctionRealSpaceTime, a0, b, c, u, k, h0, h1, h2, h3, mul_assoc,
      -eigenfunctionRealSchwartz_apply]
  have hline :
      lineDeriv ℝ (eigenfunctionRealSpaceTime ξ hξ n) x (unitVec 3) =
        deriv (fun t : ℝ ↦ k * u t) 0 := by
    simp [lineDeriv, hcurve]
  have hderiv_const_mul :
      deriv (fun t : ℝ ↦ k * u t) 0 = k * (deriv u 0) := by
    simp [deriv_const_mul_field]
  have hshift :
      deriv u 0 = deriv (eigenfunctionRealSchwartz ξ hξ (unpair₄₄ n)) (coordCLM 3 x) := by
    simpa [u] using
      (deriv_comp_const_add (f := eigenfunctionRealSchwartz ξ hξ (unpair₄₄ n)) (a := coordCLM 3 x) (x := (0 : ℝ)))
  have hderiv1D :
      deriv u 0 =
        (unpair₄₄ n / ξ) * eigenfunctionRealSchwartz ξ hξ (unpair₄₄ n - 1) (coordCLM 3 x)
          - (1 / (2 * ξ)) * eigenfunctionRealSchwartz ξ hξ (unpair₄₄ n + 1) (coordCLM 3 x) := by
    rw [hshift]
    simpa using
      (PhysLean.deriv_eigenfunctionRealSchwartz (ξ := ξ) (hξ := hξ) (n := unpair₄₄ n) (x := coordCLM 3 x))
  set aM : ℝ := eigenfunctionRealSchwartz ξ hξ (unpair₄₄ n - 1) (coordCLM 3 x)
  set aP : ℝ := eigenfunctionRealSchwartz ξ hξ (unpair₄₄ n + 1) (coordCLM 3 x)
  have hkLower : eigenfunctionRealSpaceTime ξ hξ (lower₃ n) x = a0 * b * c * aM := by
    simp [eigenfunctionRealSpaceTime, a0, b, c, aM, mul_assoc, -eigenfunctionRealSchwartz_apply]
  have hkRaise : eigenfunctionRealSpaceTime ξ hξ (raise₃ n) x = a0 * b * c * aP := by
    simp [eigenfunctionRealSpaceTime, a0, b, c, aP, mul_assoc, -eigenfunctionRealSchwartz_apply]
  have : lineDeriv ℝ (eigenfunctionRealSpaceTime ξ hξ n) x (unitVec 3)
      =
      ((unpair₄₄ n / ξ) * (a0 * b * c * aM) - (1 / (2 * ξ)) * (a0 * b * c * aP)) := by
    rw [hline, hderiv_const_mul]
    rw [hderiv1D]
    simp [aM, aP, k, mul_assoc, -eigenfunctionRealSchwartz_apply]
    ring
  simpa [hkLower, hkRaise, k, mul_assoc, -eigenfunctionRealSchwartz_apply] using this

/-! ## Coordinate-uniform derivative ladders -/

/-- Coordinate-uniform line-derivative ladder on spacetime eigenfunctions. -/
lemma lineDeriv_eigenfunctionRealSpaceTime_unitVec (ξ : ℝ) (hξ : ξ ≠ 0)
    (i : Fin STDimension) (n : ℕ) (x : SpaceTime) :
    lineDeriv ℝ (eigenfunctionRealSpaceTime ξ hξ n) x (unitVec i) =
      ((((idx n i : ℕ) : ℝ) / ξ) * eigenfunctionRealSpaceTime ξ hξ (lower i n) x)
        - (1 / (2 * ξ)) * eigenfunctionRealSpaceTime ξ hξ (raise i n) x := by
  cases i using Fin.cases with
  | zero =>
      simpa [raise, lower, idx] using
        (lineDeriv_eigenfunctionRealSpaceTime_unitVec0 (ξ := ξ) (hξ := hξ) (n := n) (x := x))
  | succ i =>
      cases i using Fin.cases with
      | zero =>
          simpa [raise, lower, idx] using
            (lineDeriv_eigenfunctionRealSpaceTime_unitVec1 (ξ := ξ) (hξ := hξ) (n := n) (x := x))
      | succ i =>
          cases i using Fin.cases with
          | zero =>
              simpa [raise, lower, idx] using
                (lineDeriv_eigenfunctionRealSpaceTime_unitVec2 (ξ := ξ) (hξ := hξ) (n := n) (x := x))
          | succ i =>
              cases i using Fin.cases with
              | zero =>
                  simpa [raise, lower, idx] using
                    (lineDeriv_eigenfunctionRealSpaceTime_unitVec3 (ξ := ξ) (hξ := hξ) (n := n) (x := x))
              | succ i =>
                  exact (False.elim (Nat.not_lt_zero _ i.isLt))

/-! ## Coefficient ladder for coordinate derivatives -/

lemma coeffCLM_SpaceTime_derivCoord (ξ : ℝ) (hξ : ξ ≠ 0) (i : Fin STDimension)
    (n : ℕ) (f : TestFunction) :
    coeffCLM_SpaceTime ξ hξ n (derivCoordCLM i f) =
      (1 / (2 * ξ)) * coeffCLM_SpaceTime ξ hξ (raise i n) f
        - ((((idx n i : ℕ) : ℝ) / ξ) * coeffCLM_SpaceTime ξ hξ (lower i n) f) := by
  let μ : Measure SpaceTime := (volume : Measure SpaceTime)
  let v : SpaceTime := unitVec i

  have he_temp : (eigenfunctionRealSpaceTime ξ hξ n).HasTemperateGrowth :=
    eigenfunctionRealSpaceTime_hasTemperateGrowth (ξ := ξ) (hξ := hξ) (n := n)
  have heLower_temp : (eigenfunctionRealSpaceTime ξ hξ (lower i n)).HasTemperateGrowth :=
    eigenfunctionRealSpaceTime_hasTemperateGrowth (ξ := ξ) (hξ := hξ) (n := lower i n)
  have heRaise_temp : (eigenfunctionRealSpaceTime ξ hξ (raise i n)).HasTemperateGrowth :=
    eigenfunctionRealSpaceTime_hasTemperateGrowth (ξ := ξ) (hξ := hξ) (n := raise i n)

  have hfg : Integrable (fun x : SpaceTime ↦ eigenfunctionRealSpaceTime ξ hξ n x * f x) μ := by
    have h :
        Integrable (⇑(SchwartzMap.smulLeftCLM (F := ℝ) (eigenfunctionRealSpaceTime ξ hξ n) f)) μ :=
      (SchwartzMap.smulLeftCLM (F := ℝ) (eigenfunctionRealSpaceTime ξ hξ n) f).integrable (μ := μ)
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    simp [SchwartzMap.smulLeftCLM_apply_apply (F := ℝ) he_temp, smul_eq_mul]

  have hfg' :
      Integrable (fun x : SpaceTime ↦ eigenfunctionRealSpaceTime ξ hξ n x * fderiv ℝ f x v) μ := by
    have h :
        Integrable (⇑(SchwartzMap.smulLeftCLM (F := ℝ) (eigenfunctionRealSpaceTime ξ hξ n) (∂_{v} f))) μ :=
      (SchwartzMap.smulLeftCLM (F := ℝ) (eigenfunctionRealSpaceTime ξ hξ n) (∂_{v} f)).integrable (μ := μ)
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    simp [SchwartzMap.smulLeftCLM_apply_apply (F := ℝ) he_temp, smul_eq_mul,
      SchwartzMap.lineDerivOp_apply_eq_fderiv]

  have hLower : Integrable (fun x : SpaceTime ↦ eigenfunctionRealSpaceTime ξ hξ (lower i n) x * f x) μ := by
    have h :
        Integrable (⇑(SchwartzMap.smulLeftCLM (F := ℝ) (eigenfunctionRealSpaceTime ξ hξ (lower i n)) f)) μ :=
      (SchwartzMap.smulLeftCLM (F := ℝ) (eigenfunctionRealSpaceTime ξ hξ (lower i n)) f).integrable (μ := μ)
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    simp [SchwartzMap.smulLeftCLM_apply_apply (F := ℝ) heLower_temp, smul_eq_mul]

  have hRaise : Integrable (fun x : SpaceTime ↦ eigenfunctionRealSpaceTime ξ hξ (raise i n) x * f x) μ := by
    have h :
        Integrable (⇑(SchwartzMap.smulLeftCLM (F := ℝ) (eigenfunctionRealSpaceTime ξ hξ (raise i n)) f)) μ :=
      (SchwartzMap.smulLeftCLM (F := ℝ) (eigenfunctionRealSpaceTime ξ hξ (raise i n)) f).integrable (μ := μ)
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    simp [SchwartzMap.smulLeftCLM_apply_apply (F := ℝ) heRaise_temp, smul_eq_mul]

  have hdiffAt :
      ∀ x : SpaceTime, DifferentiableAt ℝ (eigenfunctionRealSpaceTime ξ hξ n) x := by
    intro x
    have hdiff :
        Differentiable ℝ (eigenfunctionRealSpaceTime ξ hξ n) :=
      (eigenfunctionRealSpaceTime_hasTemperateGrowth (ξ := ξ) (hξ := hξ) (n := n)).1.differentiable (by simp)
    exact hdiff x

  have hfderiv_form (x : SpaceTime) :
      fderiv ℝ (eigenfunctionRealSpaceTime ξ hξ n) x v =
        ((((idx n i : ℕ) : ℝ) / ξ) * eigenfunctionRealSpaceTime ξ hξ (lower i n) x)
          - (1 / (2 * ξ)) * eigenfunctionRealSpaceTime ξ hξ (raise i n) x := by
    have hfderiv_eq :
        fderiv ℝ (eigenfunctionRealSpaceTime ξ hξ n) x v =
          lineDeriv ℝ (eigenfunctionRealSpaceTime ξ hξ n) x v := by
      simpa using
        ((hdiffAt x).lineDeriv_eq_fderiv (f := eigenfunctionRealSpaceTime ξ hξ n) (x := x) (v := v)).symm
    simpa [hfderiv_eq, v] using
      (lineDeriv_eigenfunctionRealSpaceTime_unitVec
        (ξ := ξ) (hξ := hξ) (i := i) (n := n) (x := x))

  have hf'g :
      Integrable (fun x : SpaceTime ↦ fderiv ℝ (eigenfunctionRealSpaceTime ξ hξ n) x v * f x) μ := by
    have hLower' :
        Integrable
          (fun x : SpaceTime ↦ ((((idx n i : ℕ) : ℝ) / ξ) *
            (eigenfunctionRealSpaceTime ξ hξ (lower i n) x * f x))) μ :=
      hLower.const_mul (((idx n i : ℕ) : ℝ) / ξ)
    have hRaise' :
        Integrable (fun x : SpaceTime ↦ (1 / (2 * ξ)) * (eigenfunctionRealSpaceTime ξ hξ (raise i n) x * f x)) μ :=
      hRaise.const_mul (1 / (2 * ξ))
    have hcomb :
        Integrable
          (fun x : SpaceTime ↦ ((((idx n i : ℕ) : ℝ) / ξ) *
              (eigenfunctionRealSpaceTime ξ hξ (lower i n) x * f x))
            - (1 / (2 * ξ)) * (eigenfunctionRealSpaceTime ξ hξ (raise i n) x * f x)) μ :=
      hLower'.sub hRaise'
    have hEq :
        (fun x : SpaceTime ↦ fderiv ℝ (eigenfunctionRealSpaceTime ξ hξ n) x v * f x)
          =
        (fun x : SpaceTime ↦ ((((idx n i : ℕ) : ℝ) / ξ) *
              (eigenfunctionRealSpaceTime ξ hξ (lower i n) x * f x))
            - (1 / (2 * ξ)) * (eigenfunctionRealSpaceTime ξ hξ (raise i n) x * f x)) := by
      funext x
      rw [hfderiv_form x]
      ring
    simpa [hEq] using hcomb

  have he_diff : Differentiable ℝ (eigenfunctionRealSpaceTime ξ hξ n) :=
    (eigenfunctionRealSpaceTime_hasTemperateGrowth (ξ := ξ) (hξ := hξ) (n := n)).1.differentiable (by simp)
  have hf_diff : Differentiable ℝ (fun x : SpaceTime ↦ f x) :=
    (f.smooth ⊤).differentiable (by simp)

  have hIBP :
      (∫ x : SpaceTime, eigenfunctionRealSpaceTime ξ hξ n x * fderiv ℝ f x v ∂μ)
        =
      - ∫ x : SpaceTime, fderiv ℝ (eigenfunctionRealSpaceTime ξ hξ n) x v * f x ∂μ := by
    simpa using
      (integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := μ)
        (f := eigenfunctionRealSpaceTime ξ hξ n) (g := fun x : SpaceTime ↦ f x) (v := v)
        hf'g hfg' hfg he_diff hf_diff)

  have hLHS :
      coeffCLM_SpaceTime ξ hξ n (derivCoordCLM i f)
        =
      ∫ x : SpaceTime, eigenfunctionRealSpaceTime ξ hξ n x * fderiv ℝ f x v ∂μ := by
    simp [coeffCLM_SpaceTime_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv, v, μ]

  have hRHS :
      - ∫ x : SpaceTime, fderiv ℝ (eigenfunctionRealSpaceTime ξ hξ n) x v * f x ∂μ
        =
      (1 / (2 * ξ)) * (∫ x : SpaceTime, eigenfunctionRealSpaceTime ξ hξ (raise i n) x * f x ∂μ)
        - ((((idx n i : ℕ) : ℝ) / ξ) *
            (∫ x : SpaceTime, eigenfunctionRealSpaceTime ξ hξ (lower i n) x * f x ∂μ)) := by
    have hpoint :
        (fun x : SpaceTime ↦ fderiv ℝ (eigenfunctionRealSpaceTime ξ hξ n) x v * f x)
          =
        (fun x : SpaceTime ↦ ((((idx n i : ℕ) : ℝ) / ξ) *
              (eigenfunctionRealSpaceTime ξ hξ (lower i n) x * f x))
            - (1 / (2 * ξ)) * (eigenfunctionRealSpaceTime ξ hξ (raise i n) x * f x)) := by
      funext x
      rw [hfderiv_form x]
      ring
    rw [hpoint]
    have hInt :
        (∫ x : SpaceTime,
              ((((idx n i : ℕ) : ℝ) / ξ) * (eigenfunctionRealSpaceTime ξ hξ (lower i n) x * f x))
                - (1 / (2 * ξ)) * (eigenfunctionRealSpaceTime ξ hξ (raise i n) x * f x) ∂μ)
          =
        (∫ x : SpaceTime,
            (((idx n i : ℕ) : ℝ) / ξ) * (eigenfunctionRealSpaceTime ξ hξ (lower i n) x * f x) ∂μ)
          -
        (∫ x : SpaceTime, (1 / (2 * ξ)) * (eigenfunctionRealSpaceTime ξ hξ (raise i n) x * f x) ∂μ) := by
      simpa using
        (integral_sub (μ := μ)
          (hLower.const_mul (((idx n i : ℕ) : ℝ) / ξ)) (hRaise.const_mul (1 / (2 * ξ))))
    rw [hInt]
    simp [integral_const_mul]

  calc
    coeffCLM_SpaceTime ξ hξ n (derivCoordCLM i f)
        = ∫ x : SpaceTime, eigenfunctionRealSpaceTime ξ hξ n x * fderiv ℝ f x v ∂μ := hLHS
    _ = - ∫ x : SpaceTime, fderiv ℝ (eigenfunctionRealSpaceTime ξ hξ n) x v * f x ∂μ := hIBP
    _ = (1 / (2 * ξ)) * (∫ x : SpaceTime, eigenfunctionRealSpaceTime ξ hξ (raise i n) x * f x ∂μ)
          - ((((idx n i : ℕ) : ℝ) / ξ) *
              (∫ x : SpaceTime, eigenfunctionRealSpaceTime ξ hξ (lower i n) x * f x ∂μ)) := hRHS
    _ = (1 / (2 * ξ)) * coeffCLM_SpaceTime ξ hξ (raise i n) f
          - ((((idx n i : ℕ) : ℝ) / ξ) * coeffCLM_SpaceTime ξ hξ (lower i n) f) := by
          simp [coeffCLM_SpaceTime_apply, μ]

end SpaceTimeHermite

end

end PhysLean
