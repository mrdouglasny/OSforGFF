/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import OSforGFF.NuclearSpaceStd
import OSforGFF.MinlosGaussianSeminormBounds

/-!
# Seminorm bounds specialized to `NuclearSpaceStd`

This file specializes the general seminorm-control lemma for `‖T ·‖` to the chosen countable
seminorm family coming from `NuclearSpaceStd`.
-/

open scoped BigOperators NNReal

namespace OSforGFF

noncomputable section

namespace MinlosGaussianSeminormBoundsStd

open OSforGFF.MinlosGaussianSeminormBounds
open OSforGFF.NuclearSpaceStd

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [NuclearSpaceStd E]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- For a `NuclearSpaceStd`, any continuous Gaussian covariance seminorm `‖T ·‖`
is controlled by a single seminorm from the chosen countable family. -/
theorem exists_bound_seminormFamily
    (T : E →ₗ[ℝ] H)
    (h_sq : Continuous fun f : E => (‖T f‖ ^ 2 : ℝ)) :
    ∃ n : ℕ, ∃ C : ℝ≥0, C ≠ 0 ∧
      (normSeminorm ℝ H).comp T ≤ C • (seminormFamily (E := E) n) := by
  have hp : WithSeminorms (seminormFamily (E := E)) :=
    NuclearSpaceStd.seminormFamily_withSeminorms (E := E)
  have hpmono : Monotone (seminormFamily (E := E)) :=
    NuclearSpaceStd.seminormFamily_mono (E := E)
  simpa using
    (seminorm_norm_comp_le_single_nat (E := E) (H := H)
      (p := seminormFamily (E := E)) hp hpmono T h_sq)

end MinlosGaussianSeminormBoundsStd

end

end OSforGFF
