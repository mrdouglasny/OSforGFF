# `lakefile.lean` — Informal Summary

> **Source**: [`lakefile.lean`](../lakefile.lean)
> **Generated**: 2026-07-05 (regenerated from current source)

## Overview

Lake build configuration for the `OSforGFF` package. It is not part of the mathematical
development — it declares the package, its external git dependencies, and its libraries. This is
where the three external, dimension-agnostic dependencies consumed unchanged by the refactor are
pinned.

## Status

**Main result**: N/A — build configuration (no definitions or theorems).

**Length**: 22 lines, 0 definition(s) + 0 theorem(s)/lemma(s).

---

### [`package «OSforGFF»`](../lakefile.lean#L4) — Package declaration

Declares the `OSforGFF` Lake package. Sets one interactive/build `leanOption`:
`pp.unicode.fun := true` (pretty-prints `fun a ↦ b`).

---

### [`require` — external git dependencies](../lakefile.lean#L11)

Three dependencies fetched from git (never edited by this project):

- **`BochnerMinlos`** — `github.com/mrdouglasny/bochner` @ `main`: the Minlos theorem, nuclear-space,
  and Bochner/positive-definite machinery (imported as `Minlos.*` / `Bochner.*`).
- **`GaussianField`** — `github.com/mrdouglasny/gaussian-field` @ `main`: the Gaussian measure
  construction.
- **`mathlib`** — `github.com/leanprover-community/mathlib4`.

---

### [`lean_lib «OSforGFF»`](../lakefile.lean#L21) — Default target

The library itself, marked `@[default_target]`. Its root module is
[`OSforGFF.lean`](../OSforGFF.lean).

---

*This file declares no definitions or theorems; it is the Lake package configuration (0 with sorry).*
