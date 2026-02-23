import KolmogorovExtension4.KolmogorovExtension

/-!
# Kolmogorov extension theorem (re-export)

The repository already contains a standalone Kolmogorov extension development in `KolmogorovExtension4/`.
To avoid duplicating API/lemmas inside `OSforGFF/`, this module is just a thin layer that
re-exports the main theorem file.

Downstream `OSforGFF` code should import `OSforGFF.KolmogorovExtension` (stable path) and then use
the definitions/theorems provided in the `MeasureTheory` namespace (e.g. `projectiveLimit`,
`isProjectiveLimit_projectiveLimit`, ...), as defined in `KolmogorovExtension4.KolmogorovExtension`.
-/
