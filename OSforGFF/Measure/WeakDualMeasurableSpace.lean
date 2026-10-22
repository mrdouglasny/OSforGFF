/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GaussianField.Construction
public import Minlos.NuclearSpace

/-!
# One σ-algebra on the weak dual

gaussian-field equips `Configuration E` (an `abbrev` for `WeakDual ℝ E`) with the cylinder
σ-algebra `GaussianField.instMeasurableSpaceConfiguration`, and BochnerMinlos equips every
`WeakDual ℝ E` with its cylinder σ-algebra. Neither host imports the other, so each declares the
instance; both have the same body, `MeasurableSpace.comap (fun ω f ↦ ω f) MeasurableSpace.pi`, the
σ-algebra induced by the product σ-algebra on `E → ℝ`. This is the lowest host importing both, and
here they are one σ-algebra by unfolding at instance transparency, the transparency of type class
resolution (`GaussianField.instMeasurableSpaceConfiguration_eq_weakDual`): measures, `BorelSpace`
instances and measurability lemmas of either host apply to the other's.
-/

@[expose] public section

namespace GaussianField

/-- **The two cylinder σ-algebras on the weak dual are the same**: gaussian-field's on
`Configuration E` and BochnerMinlos's on `WeakDual ℝ E` agree at instance transparency. -/
theorem instMeasurableSpaceConfiguration_eq_weakDual {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] :
    instMeasurableSpaceConfiguration (E := E) = instMeasurableSpaceWeakDualReal_minlos := by
  with_reducible_and_instances rfl

end GaussianField
