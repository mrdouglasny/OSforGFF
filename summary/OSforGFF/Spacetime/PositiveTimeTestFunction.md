# `PositiveTimeTestFunction.lean` — Informal Summary

> **Source**: [`OSforGFF/Spacetime/PositiveTimeTestFunction.lean`](../../../OSforGFF/Spacetime/PositiveTimeTestFunction.lean)
> **Generated**: 2026-07-05 (regenerated from current source)

## Overview

This file (generic in `d : ℕ` with `[Fact (2 ≤ d)]`) defines test functions supported in the
positive-time region and the star operation on complex test functions. It introduces the predicate
`HasPositiveTime` (positive time component), the open set `positiveTimeSet`, and the real and
complex submodules of Schwartz functions whose (topological) support lies in that region
(`PositiveTimeTestFunction d` / `PositiveTimeTestFunctionℂ d`), together with their additive group
structure and the fact that such functions vanish where the time component is $\le 0$. It then
defines the star operation `starTestFunction` — time reflection (`compTimeReflection`, from
`DiscreteSymmetry`) followed by pointwise complex conjugation — and registers it as a `Star`
instance on `SchwartzTestFunctionℂ d`, using a helper lemma that conjugation preserves iterated-derivative
norms. These are the building blocks for the OS3 (reflection positivity) axiom.

## Status

**Main result**: The positive-time test-function submodules (real and complex) and the star
operation (time reflection composed with conjugation) on complex test functions. Fully proven
(0 sorries; no `sorry`/`admit`).

**Length**: 181 lines, 12 definition(s) + 5 theorem(s)/lemma(s)

---

### [`HasPositiveTime`](../../../OSforGFF/Spacetime/PositiveTimeTestFunction.lean#L44) — Definition

**Lean signature**
```lean
def HasPositiveTime (x : (SpaceTime d)) : Prop := getTimeComponent x > 0
```

**Informal**: A spacetime point has positive time if its time component $x_0$ is positive.

---

### [`positiveTimeSet`](../../../OSforGFF/Spacetime/PositiveTimeTestFunction.lean#L47) — Definition

**Lean signature**
```lean
def positiveTimeSet : Set (SpaceTime d) := {x | HasPositiveTime x}
```

**Informal**: The set of all spacetime points with positive time component.

---

### [`is_open_positiveTimeSet`](../../../OSforGFF/Spacetime/PositiveTimeTestFunction.lean#L50) — Lemma

**Statement**: The positive-time set is open (as the preimage of $(0, \infty)$ under the
continuous time-coordinate projection).

**Proof uses**: `isOpen_lt`, `PiLp.continuous_apply`

---

### [`PositiveTimeTestFunctions.submodule`](../../../OSforGFF/Spacetime/PositiveTimeTestFunction.lean#L55) — Definition

**Lean signature**
```lean
def PositiveTimeTestFunctions.submodule : Submodule ℝ (SchwartzTestFunction d)
```

**Informal**: The $\mathbb{R}$-submodule of real test functions whose topological support is
contained in `positiveTimeSet`; closed under addition and scalar multiplication because support
behaves subadditively.

---

### [`PositiveTimeTestFunction`](../../../OSforGFF/Spacetime/PositiveTimeTestFunction.lean#L70) — Definition *(abbrev)*

**Lean signature**
```lean
abbrev PositiveTimeTestFunction (d : ℕ) [Fact (2 ≤ d)] : Type :=
  PositiveTimeTestFunctions.submodule (d := d)
```

**Informal**: The type of real-valued test functions supported in the positive-time region.

---

### [`instance : AddCommMonoid (PositiveTimeTestFunction d)`](../../../OSforGFF/Spacetime/PositiveTimeTestFunction.lean#L73) — Definition *(instance)*

**Lean signature**
```lean
instance : AddCommMonoid (PositiveTimeTestFunction d)
```

**Informal**: Additive commutative monoid structure, inherited from the submodule.

---

### [`instance : AddCommGroup (PositiveTimeTestFunction d)`](../../../OSforGFF/Spacetime/PositiveTimeTestFunction.lean#L74) — Definition *(instance)*

**Lean signature**
```lean
instance : AddCommGroup (PositiveTimeTestFunction d)
```

**Informal**: Additive commutative group structure, inherited from the submodule.

---

### [`PositiveTimeTestFunction.sum_smul_mem`](../../../OSforGFF/Spacetime/PositiveTimeTestFunction.lean#L77) — Lemma

**Statement**: Finite linear combinations of positive-time test functions stay in the submodule:
for $f : \mathrm{Fin}\, n \to$ positive-time functions and coefficients $c$, there is a $g$ with
$g = \sum_i c_i\, f_i$ (as underlying test functions).

---

### [`PositiveTimeTestFunctionsℂ.submodule`](../../../OSforGFF/Spacetime/PositiveTimeTestFunction.lean#L87) — Definition

**Lean signature**
```lean
def PositiveTimeTestFunctionsℂ.submodule : Submodule ℂ (SchwartzTestFunctionℂ d)
```

**Informal**: The $\mathbb{C}$-submodule of complex test functions whose support lies in
`positiveTimeSet`; a $\mathbb{C}$-submodule since $\mathbb{C}$-scalar multiplication preserves
support.

---

### [`PositiveTimeTestFunctionℂ`](../../../OSforGFF/Spacetime/PositiveTimeTestFunction.lean#L102) — Definition *(abbrev)*

**Lean signature**
```lean
abbrev PositiveTimeTestFunctionℂ (d : ℕ) [Fact (2 ≤ d)] : Type :=
  PositiveTimeTestFunctionsℂ.submodule (d := d)
```

**Informal**: The type of complex-valued test functions supported in the positive-time region.

---

### [`instance : AddCommMonoid (PositiveTimeTestFunctionℂ d)`](../../../OSforGFF/Spacetime/PositiveTimeTestFunction.lean#L105) — Definition *(instance)*

**Lean signature**
```lean
instance : AddCommMonoid (PositiveTimeTestFunctionℂ d)
```

**Informal**: Additive commutative monoid structure, inherited from the complex submodule.

---

### [`instance : AddCommGroup (PositiveTimeTestFunctionℂ d)`](../../../OSforGFF/Spacetime/PositiveTimeTestFunction.lean#L106) — Definition *(instance)*

**Lean signature**
```lean
instance : AddCommGroup (PositiveTimeTestFunctionℂ d)
```

**Informal**: Additive commutative group structure, inherited from the complex submodule.

---

### [`PositiveTimeTestFunctionℂ.zero_on_nonpositive`](../../../OSforGFF/Spacetime/PositiveTimeTestFunction.lean#L108) — Lemma

**Statement**: A complex positive-time test function vanishes off its support: if
$\mathrm{getTimeComponent}\, x \le 0$ then $f(x) = 0$.

**Proof uses**: `image_eq_zero_of_notMem_tsupport`

---

### [`starRingEnd_iteratedFDeriv_norm_eq`](../../../OSforGFF/Spacetime/PositiveTimeTestFunction.lean#L123) — Lemma

**Statement**: Complex conjugation commutes through iterated derivatives and preserves their norms
(the hypothesis `[Fact (2 ≤ d)]` is `omit`ted here):
$$\lVert D^n\bigl(x \mapsto \overline{g(x)}\bigr)(x)\rVert = \lVert D^n g(x)\rVert.$$

**Proof uses**: `RCLike.conjLIE_apply`, `LinearIsometryEquiv.norm_iteratedFDeriv_comp_left`

---

### [`starTestFunction`](../../../OSforGFF/Spacetime/PositiveTimeTestFunction.lean#L136) — Definition

**Lean signature**
```lean
noncomputable def starTestFunction (f : (SchwartzTestFunctionℂ d)) : (SchwartzTestFunctionℂ d)
```

**Informal**: The star operation on complex test functions: apply time reflection
([`compTimeReflection`](../../../OSforGFF/Spacetime/DiscreteSymmetry.lean#L177)) and then pointwise
complex conjugation, $x \mapsto \overline{(\theta f)(x)}$. Smoothness and Schwartz decay are
preserved because conjugation is a linear isometry.

---

### [`instance : Star (SchwartzTestFunctionℂ d)`](../../../OSforGFF/Spacetime/PositiveTimeTestFunction.lean#L165) — Definition *(instance)*

**Lean signature**
```lean
noncomputable instance : Star (SchwartzTestFunctionℂ d) where
  star f := starTestFunction f
```

**Informal**: The `Star` instance on complex test functions given by `starTestFunction`.

---

### [`PositiveTimeTestFunction.zero_on_nonpositive`](../../../OSforGFF/Spacetime/PositiveTimeTestFunction.lean#L168) — Lemma

**Statement**: A real positive-time test function vanishes off its support: if
$\mathrm{getTimeComponent}\, x \le 0$ then $f(x) = 0$.

**Proof uses**: `image_eq_zero_of_notMem_tsupport`

---

*This file has **12** definitions and **5** theorems/lemmas (0 with sorry).*
