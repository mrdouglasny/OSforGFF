/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Copyright (c) 2026 Sergey A. Cherkis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sergey A. Cherkis, Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.MeasureTheory.Integral.ExpDecay
public import Mathlib.Analysis.Asymptotics.Defs

/-!
# Modified Bessel function `K₀`

The radial profile of the free covariance in two dimensions is `(1/(2π)) · K₀(m r)`, where `K₀` is
the modified Bessel function of the second kind of order zero. This file defines `K₀` through its
cosh integral representation. The proper-time (Schwinger) evaluation
`∫₀^∞ (1/t) e^{-m²t - r²/(4t)} dt = 2 K₀(m r)` is the order-zero case of the master identity
`schwingerIntegral_eq_besselK` and is provided as `schwingerIntegral_eq_besselK0`
(`OSforGFF.General.BesselK`).
-/

@[expose] public section

open MeasureTheory Set Filter Real Topology Asymptotics intervalIntegral

/-- The modified Bessel function `K₀(z)` via its cosh integral representation,
    `K₀(z) = ∫₀^∞ exp(-z cosh t) dt`. Well-defined and positive for `z > 0`. -/
noncomputable def besselK0 (z : ℝ) : ℝ :=
  ∫ t : ℝ in Ici 0, exp (-z * cosh t)
