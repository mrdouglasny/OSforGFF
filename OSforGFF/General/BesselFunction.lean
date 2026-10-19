/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Copyright (c) 2026 Sergey A. Cherkis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sergey A. Cherkis, Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Modified Bessel function `K₁`

Defines the modified Bessel function of the second kind of order one through its cosh integral
representation. The radial profile of the free covariance in four dimensions is `(m/(4π²r)) K₁(mr)`
(`Instances/Dim4.lean`). The proper-time (Schwinger) evaluation
`∫₀^∞ (1/t²) e^{-m²t - r²/(4t)} dt = (4m/r) K₁(mr)` is the order-one case of the master identity
`schwingerIntegral_eq_besselK` (`General/BesselK`).

The `K₁` analytic lemmas (positivity, continuity, the asymptotic and near-origin bounds, radial
integrability) supported the original four-dimensional analysis and are preserved off the build
graph in `OSforGFF/Legacy/BesselK1Analytics.lean`.
-/

@[expose] public section

open MeasureTheory Set Filter Asymptotics Real

/-- The modified Bessel function `K₁(z)` via its cosh integral representation,
    `K₁(z) = ∫₀^∞ exp(-z cosh t) cosh t dt`. Well-defined and positive for `z > 0`. -/
noncomputable def besselK1 (z : ℝ) : ℝ :=
  ∫ t : ℝ in Ici 0, exp (-z * cosh t) * cosh t
