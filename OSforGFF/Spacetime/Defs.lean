/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
# Generic spacetime/test-function aliases

This file provides lightweight, **dimension-agnostic** aliases for:

- the reference measure `μ` (typically Lebesgue/volume), and
- Schwartz test functions on an ambient space `E`.

They are placed in the namespace `OSforGFF.Spacetime` to avoid clashing with the existing
`OSforGFF.Basic` abbreviations specialized to `SpaceTime = ℝ⁴`.
-/

open MeasureTheory

namespace OSforGFF

namespace Spacetime

/-- The reference measure on `E` (by default, `volume`). -/
noncomputable def μ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] : Measure E :=
  (volume : Measure E)

/-- Real-valued Schwartz test functions on `E`. -/
abbrev TestFunction (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  SchwartzMap E ℝ

/-- `V`-valued Schwartz test functions on `E`. -/
abbrev TestFunctionV (E : Type*) (V : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] :=
  SchwartzMap E V

/-- Complex-valued Schwartz test functions on `E`. -/
abbrev TestFunctionℂ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  TestFunctionV E ℂ

end Spacetime

end OSforGFF
