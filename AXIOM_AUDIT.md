# Axiom audit

The build graph of this library declares **zero custom axioms**: `grep -rn '^ *axiom '
OSforGFF` is empty (as is `Legacy/`, which is off the import graph). Every headline theorem
depends on exactly Lean's three core axioms and nothing else:

```
propext, Classical.choice, Quot.sound
```

| Headline theorem | `#print axioms` |
|---|---|
| `gaussianFreeField_satisfies_all_OS_axioms_generic` | the 3 core axioms |
| `gaussianFreeField_satisfies_all_OS_axioms_of_dim` (every `d ≥ 2`) | the 3 core axioms |
| `gaussianFreeField_satisfies_all_OS_axioms_dim4` | the 3 core axioms |
| `gaussianFreeField_satisfies_all_OS_axioms_dim3` | the 3 core axioms |
| `gaussianFreeField_satisfies_all_OS_axioms_dim2` | the 3 core axioms |
| `gaussianFreeField_satisfies_all_OS_axioms_dim5` | the 3 core axioms |

In particular, the Minlos theorem and the nuclear-space structure of Schwartz space are consumed
from the external [bochner](https://github.com/mrdouglasny/bochner) and
[gaussian-field](https://github.com/mrdouglasny/gaussian-field) libraries as *proven theorems*,
not assumptions — the 3-core-axiom footprint above certifies this transitively.

## How this is enforced

- **Build-time (the hard gate):** `OSforGFF/Guardrails.lean` is part of the root import graph, so
  `lake build` compiles it. Its `#guard_msgs` blocks freeze both the axiom footprint and the exact
  statement type of all six headline theorems; any drift fails the build.
- **Source-level:** `bash scripts/check-guardrails.sh` greps the source for `axiom` declarations,
  escape hatches (`native_decide`, `unsafe`, `implemented_by`, `extern`), and `sorry`/`admit` —
  against the `pre-unfreeze-baseline` tag when present, or over the full tree in a clone without
  tags.
- **Manual spot-check:** run `#print axioms gaussianFreeField_satisfies_all_OS_axioms_of_dim`
  (and the other five names above) in a scratch file with `import OSforGFF.OS.Master` via
  `lake env lean`; each must report exactly `[propext, Classical.choice, Quot.sound]`.
