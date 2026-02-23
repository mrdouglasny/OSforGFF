import OSforGFF.GFFmaster
import OSforGFF.NuclearSpace.PhysHermiteSpaceTimeSchwartzNuclearInclusion

/-!
# Unconditional master theorem (spacetime Hermite model)

The master theorem `OSforGFF.gaussianFreeField_satisfies_all_OS_axioms` is stated with the standard
countable-seminorm nuclearity package `[OSforGFF.NuclearSpaceStd TestFunction]`.

In the spacetime Hermite model, this hypothesis is discharged by
`OSforGFF.NuclearSpace.PhysHermiteSpaceTimeSchwartzNuclearInclusion`, so we provide a convenience
wrapper with no additional hypotheses beyond `m > 0`.
-/

namespace OSforGFF

noncomputable section

theorem gaussianFreeField_satisfies_all_OS_axioms_proved (m : ℝ) [Fact (0 < m)] :
    SatisfiesAllOS (μ_GFF m) := by
  simpa using (gaussianFreeField_satisfies_all_OS_axioms (m := m))

end

end OSforGFF

