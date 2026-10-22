/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import OSforGFF

/-!
# Consuming the Gaussian free field from a module

Check that the public definitions, instances and unconditional all-dimensions theorem
survive the module boundary. The library's `Guardrails` checks the theorem types and axioms.
-/

public section

example (d : ℕ) [Fact (2 ≤ d)] (m : ℝ) [Fact (0 < m)] :
    letI := OSforGFF.GFFPropagator.ofProperTime d m
    SatisfiesAllOS (gaussianFreeField_free (d := d) m) :=
  OSforGFF.gaussianFreeField_satisfies_all_OS_axioms_of_dim d m

example (d : ℕ) [Fact (2 ≤ d)] (m : ℝ) [Fact (0 < m)] :
    letI := OSforGFF.GFFPropagator.ofProperTime d m
    OS3_ReflectionPositivity (gaussianFreeField_free (d := d) m) :=
  (OSforGFF.gaussianFreeField_satisfies_all_OS_axioms_of_dim d m).os3

example (m : ℝ) [Fact (0 < m)] : SatisfiesAllOS (μ_GFF 3 m) :=
  OSforGFF.gaussianFreeField_satisfies_all_OS_axioms_dim3 m
