/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.Algebra.Module.WeakDual
import OSforGFF.Minlos
import OSforGFF.MinlosAxiomatic
import OSforGFF.MinlosGaussianProved
import OSforGFF.NuclearSpace.Std

/-!
# Abstract Gel'fand triples for Minlos

This file introduces a lightweight, reusable abstraction for a Gel'fand triple
`N ⊂ H ⊂ N'`:

- `N` is the test/nuclear space,
- `H` is a Hilbert pivot space,
- `N'` is represented by `WeakDual ℝ N`.

The purpose is to formulate Minlos and Gaussian characteristic-functional APIs
against this abstract interface, rather than a concrete choice such as
`TestFunction = 𝓢(SpaceTime, ℝ)`.
-/

open Complex MeasureTheory
open scoped BigOperators

namespace OSforGFF
namespace Minlos

noncomputable section

/-- A minimal Gel'fand triple package `N ⊂ H ⊂ N'`.

`toHilbert` is the canonical continuous embedding of test vectors into the
pivot Hilbert space. The dual `N'` is modeled by `WeakDual ℝ N`. -/
structure GelfandTriple where
  N : Type*
  H : Type*
  [instAddCommGroupN : AddCommGroup N]
  [instModuleN : Module ℝ N]
  [instTopologicalSpaceN : TopologicalSpace N]
  [instNormedAddCommGroupH : NormedAddCommGroup H]
  [instInnerProductSpaceH : InnerProductSpace ℝ H]
  [instNuclearN : OSforGFF.NuclearSpaceStd N]
  toHilbert : N →L[ℝ] H

attribute [instance] GelfandTriple.instAddCommGroupN
attribute [instance] GelfandTriple.instModuleN
attribute [instance] GelfandTriple.instTopologicalSpaceN
attribute [instance] GelfandTriple.instNormedAddCommGroupH
attribute [instance] GelfandTriple.instInnerProductSpaceH
attribute [instance] GelfandTriple.instNuclearN

namespace GelfandTriple

variable (T : GelfandTriple)

/-- The test/nuclear space `N`. -/
abbrev TestSpace := T.N

/-- The Hilbert pivot space `H`. -/
abbrev PivotSpace := T.H

/-- The distribution space `N'` represented by the weak dual. -/
abbrev DualSpace := WeakDual ℝ T.N

/-- Characteristic-functional diagonal covariance induced by the embedding `N → H`. -/
def covarianceDiagonal (f : T.N) : ℝ :=
  ‖T.toHilbert f‖ ^ (2 : ℕ)

lemma covarianceDiagonal_nonneg (f : T.N) : 0 ≤ T.covarianceDiagonal f := by
  simp [covarianceDiagonal]

end GelfandTriple

/-- Abstract Minlos statement on a Gel'fand triple.

This is an API boundary: downstream modules can use this class without
depending on any concrete proof strategy for nuclearity. -/
class MinlosOnGelfandTriple (T : GelfandTriple) : Prop where
  /-- Existence/uniqueness Minlos theorem on `T.N`. -/
  minlos_theorem
    (Φ : T.N → ℂ)
    (h_continuous : Continuous Φ)
    (h_positive_definite : IsPositiveDefinite Φ)
    (h_normalized : Φ 0 = 1) :
    ∃! μ : ProbabilityMeasure (WeakDual ℝ T.N),
      ∀ f : T.N, Φ f = ∫ ω, Complex.exp (I * (ω f)) ∂μ.toMeasure

namespace MinlosOnGelfandTriple

variable {T : GelfandTriple} [MinlosOnGelfandTriple T]

theorem minlosOnTriple
    (Φ : T.N → ℂ)
    (h_continuous : Continuous Φ)
    (h_positive_definite : IsPositiveDefinite Φ)
    (h_normalized : Φ 0 = 1) :
    ∃! μ : ProbabilityMeasure (WeakDual ℝ T.N),
      ∀ f : T.N, Φ f = ∫ ω, Complex.exp (I * (ω f)) ∂μ.toMeasure :=
  MinlosOnGelfandTriple.minlos_theorem
    (T := T) Φ h_continuous h_positive_definite h_normalized

end MinlosOnGelfandTriple

/-- Bridge: any `MinlosTheorem` instance on `T.N` induces `MinlosOnGelfandTriple T`. -/
instance instMinlosOnGelfandTriple_ofMinlosTheorem
    (T : GelfandTriple)
    [MinlosTheorem T.N] :
    MinlosOnGelfandTriple T where
  minlos_theorem Φ h_continuous h_positive_definite h_normalized :=
    minlos_theorem
      (E := T.N) Φ h_continuous h_positive_definite h_normalized

/-- Gaussian measure along a Gel'fand triple embedding `N → H`
obtained from the proved nuclear support route. -/
noncomputable def gaussianMeasureOfTriple
    (T : GelfandTriple)
    (h_sq : Continuous fun f : T.N => (‖T.toHilbert f‖ ^ 2 : ℝ)) :
    ProbabilityMeasure (WeakDual ℝ T.N) :=
  OSforGFF.MinlosGaussianProved.gaussianProcessWeakDual_of_nuclear
    (E := T.N) (H := T.H) (T := T.toHilbert) h_sq

/-- Characteristic-functional identity for `gaussianMeasureOfTriple`. -/
theorem integral_exp_eval_eq_gaussianMeasureOfTriple
    (T : GelfandTriple)
    (h_sq : Continuous fun f : T.N => (‖T.toHilbert f‖ ^ 2 : ℝ))
    (f : T.N) :
    (∫ ω, Complex.exp (I * ((ω f : ℝ) : ℂ))
        ∂(gaussianMeasureOfTriple T h_sq).toMeasure) =
      Complex.exp (-(1 / 2 : ℂ) * (‖T.toHilbert f‖ ^ 2 : ℝ)) := by
  simpa [gaussianMeasureOfTriple] using
    (OSforGFF.MinlosGaussianProved.integral_exp_eval_eq_gaussianProcessWeakDual_of_nuclear
      (E := T.N) (H := T.H) (T := T.toHilbert) (h_sq := h_sq) f)

end
end Minlos
end OSforGFF
