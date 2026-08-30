# `Euclidean.lean` — Informal Summary

> **Source**: [`OSforGFF/Spacetime/Euclidean.lean`](../../OSforGFF/Spacetime/Euclidean.lean)
> **Generated**: 2026-07-05 (regenerated from current source)

## Overview

This file (in namespace `QFT`, generic in the dimension `d : ℕ`) defines the Euclidean group
`E d = ℝ^d ⋊ O(d)` of rigid motions of $\mathbb{R}^d$, with orthogonal part `O d` (linear
isometries) and translation part, acting on spacetime by $g \cdot x = R x + t$ via `act`. It
proves the group axioms (semidirect-product multiplication, identity, inverse via a helper
`LinearIsometry.inv`, associativity/cancellation) so that `E d` is a `Group`, and that `act` is a
genuine left action ($\mathrm{act}(gh) = \mathrm{act}\,g \circ \mathrm{act}\,h$ and
$\mathrm{act}\,g^{-1} \circ \mathrm{act}\,g = \mathrm{id}$). It then shows Lebesgue measure is
invariant under every motion (`measurePreserving_act`) and packages the common pullback map
$x \mapsto g^{-1} \cdot x$ (`euclidean_pullback`) — establishing its temperate growth and
polynomial bounds — to build the induced action `euclidean_action` on complex test functions. This is the geometric foundation for the OS2 (Euclidean
invariance) axiom.

## Status

**Main result**: The Euclidean group `E d`, its group structure and action on spacetime, measure
preservation of rigid motions, and the induced pullback action on complex test functions.
Fully proven (0 sorries; no `sorry`/`admit`).

**Length**: 360 lines, 14 definition(s) + 24 theorem(s)/lemma(s)

---

### [`O`](../../OSforGFF/Spacetime/Euclidean.lean#L54) — Definition *(abbrev)*

**Lean signature**
```lean
abbrev O (d : ℕ) : Type :=
  LinearIsometry (RingHom.id ℝ) (SpaceTime d) (SpaceTime d)
```

**Informal**: Orthogonal linear isometries of $\mathbb{R}^d$, i.e. the group $O(d)$.

---

### [`E`](../../OSforGFF/Spacetime/Euclidean.lean#L59) — Definition *(structure)*

**Lean signature**
```lean
structure E (d : ℕ) where
  R : (O d)
  t : (SpaceTime d)
```

**Informal**: A Euclidean motion = rotation/reflection `R` plus translation `t`; the group
$E(d) = \mathbb{R}^d \rtimes O(d)$.

---

### [`act`](../../OSforGFF/Spacetime/Euclidean.lean#L65) — Definition

**Lean signature**
```lean
def act (g : (E d)) (x : (SpaceTime d)) : (SpaceTime d) := g.R x + g.t
```

**Informal**: The action of $g \in E(d)$ on a spacetime point, $x \mapsto R x + t$.

---

### [`act_one`](../../OSforGFF/Spacetime/Euclidean.lean#L70) — Lemma *(simp)*

**Statement**: $\mathrm{act}\,\langle 1, 0\rangle\, x = x$.

---

### [`act_mul`](../../OSforGFF/Spacetime/Euclidean.lean#L73) — Lemma *(simp)*

**Statement**: $\mathrm{act}\,\langle g_R \circ h_R,\, g_R h_t + g_t\rangle\, x = g_R(h_R x + h_t) + g_t$.

---

### [`act_inv`](../../OSforGFF/Spacetime/Euclidean.lean#L77) — Lemma *(simp)*

**Statement**: $\mathrm{act}\,\langle g_R,\, -g_R g_t\rangle\, x = g_R(x - g_t)$.

---

### [`LinearIsometry.inv`](../../OSforGFF/Spacetime/Euclidean.lean#L89) — Definition

**Lean signature**
```lean
noncomputable def inv (g : (O d)) : (O d) :=
  ((g.toLinearIsometryEquiv rfl).symm).toLinearIsometry
```

**Informal**: The inverse of a linear isometry, obtained by passing to the canonical
finite-dimensional equivalence and taking its `symm` back to a `LinearIsometry`.

---

### [`LinearIsometry.comp_apply`](../../OSforGFF/Spacetime/Euclidean.lean#L92) — Lemma *(simp)*

**Statement**: $(g \circ h)(x) = g(h(x))$ (by `rfl`).

---

### [`LinearIsometry.inv_apply`](../../OSforGFF/Spacetime/Euclidean.lean#L95) — Lemma *(simp)*

**Statement**: $(\mathrm{inv}\, g)(g(x)) = x$.

---

### [`LinearIsometry.one_apply`](../../OSforGFF/Spacetime/Euclidean.lean#L101) — Lemma *(simp)*

**Statement**: $(1 : O(d))(x) = x$ (by `rfl`).

---

### [`LinearIsometry.one_comp`](../../OSforGFF/Spacetime/Euclidean.lean#L103) — Lemma *(simp)*

**Statement**: $1 \circ R = R$.

---

### [`LinearIsometry.comp_one`](../../OSforGFF/Spacetime/Euclidean.lean#L106) — Lemma *(simp)*

**Statement**: $R \circ 1 = R$.

---

### [`LinearIsometry.inv_comp`](../../OSforGFF/Spacetime/Euclidean.lean#L109) — Lemma *(simp)*

**Statement**: $(\mathrm{inv}\, R) \circ R = 1$.

---

### [`LinearIsometry.comp_inv`](../../OSforGFF/Spacetime/Euclidean.lean#L113) — Lemma *(simp)*

**Statement**: $R \circ (\mathrm{inv}\, R) = 1$.

---

### [`E.ext`](../../OSforGFF/Spacetime/Euclidean.lean#L125) — Lemma *(ext)*

**Statement**: Two Euclidean motions are equal when their rotation and translation components
agree: $g_R = h_R$ and $g_t = h_t$ imply $g = h$.

---

### [`instance : Mul (E d)`](../../OSforGFF/Spacetime/Euclidean.lean#L133) — Definition *(instance)*

**Lean signature**
```lean
instance : Mul (E d) where
  mul g h := ⟨g.R.comp h.R, g.R h.t + g.t⟩
```

**Informal**: Semidirect-product multiplication: compose rotations and translate the second
translation by the first rotation.

---

### [`instance : One (E d)`](../../OSforGFF/Spacetime/Euclidean.lean#L136) — Definition *(instance)*

**Lean signature**
```lean
instance : One (E d) where
  one := ⟨1, 0⟩
```

**Informal**: The identity motion (identity rotation, zero translation).

---

### [`instance : Inv (E d)`](../../OSforGFF/Spacetime/Euclidean.lean#L139) — Definition *(instance)*

**Lean signature**
```lean
instance : Inv (E d) where
  inv g := ⟨LinearIsometry.inv g.R, -(LinearIsometry.inv g.R) g.t⟩
```

**Informal**: The inverse motion, with inverted rotation and correspondingly transformed
translation.

---

### [`instance : Div (E d)`](../../OSforGFF/Spacetime/Euclidean.lean#L143) — Definition *(instance)*

**Lean signature**
```lean
instance : Div (E d) where
  div g h := g * h⁻¹
```

**Informal**: Division $g / h = g \cdot h^{-1}$, needed because `Group` extends `DivInvMonoid`.

---

### [`mul_R`](../../OSforGFF/Spacetime/Euclidean.lean#L149) — Lemma *(simp)*

**Statement**: $(g \cdot h)_R = g_R \circ h_R$ (by `rfl`).

---

### [`mul_t`](../../OSforGFF/Spacetime/Euclidean.lean#L150) — Lemma *(simp)*

**Statement**: $(g \cdot h)_t = g_R h_t + g_t$ (by `rfl`).

---

### [`one_R`](../../OSforGFF/Spacetime/Euclidean.lean#L151) — Lemma *(simp)*

**Statement**: $(1)_R = 1$ (by `rfl`).

---

### [`one_t`](../../OSforGFF/Spacetime/Euclidean.lean#L152) — Lemma *(simp)*

**Statement**: $(1)_t = 0$ (by `rfl`).

---

### [`inv_R`](../../OSforGFF/Spacetime/Euclidean.lean#L153) — Lemma *(simp)*

**Statement**: $(g^{-1})_R = \mathrm{inv}\, g_R$ (by `rfl`).

---

### [`inv_t`](../../OSforGFF/Spacetime/Euclidean.lean#L154) — Lemma *(simp)*

**Statement**: $(g^{-1})_t = -(\mathrm{inv}\, g_R)\, g_t$ (by `rfl`).

---

### [`instance : Group (E d)`](../../OSforGFF/Spacetime/Euclidean.lean#L158) — Definition *(instance)*

**Lean signature**
```lean
instance : Group (E d)
```

**Informal**: The full group structure on `E d`, with associativity, identity laws, and
left-inverse cancellation proved component-wise via `E.ext`.

---

### [`act_mul_general`](../../OSforGFF/Spacetime/Euclidean.lean#L198) — Lemma *(simp)*

**Statement**: `act` is a left group action:
$$\mathrm{act}(g \cdot h)\, x = \mathrm{act}\, g\,(\mathrm{act}\, h\, x).$$

---

### [`act_inv_general`](../../OSforGFF/Spacetime/Euclidean.lean#L224) — Lemma *(simp)*

**Statement**: The inverse law of the action:
$$\mathrm{act}\, g^{-1}\,(\mathrm{act}\, g\, x) = x.$$

---

### [`measurePreserving_act`](../../OSforGFF/Spacetime/Euclidean.lean#L241) — Lemma

**Statement**: Every rigid motion preserves Lebesgue measure: `act g` is measure-preserving for
`volume` on `SpaceTime d` (the push-forward of $\mu$ by $x \mapsto g \cdot x$ is $\mu$).

**Proof uses**: `LinearIsometryEquiv.measurePreserving`, `map_add_right_eq_self`

---

### [`contDiff_act_inv`](../../OSforGFF/Spacetime/Euclidean.lean#L253) — Lemma *(private)*

**Statement**: The map `act g⁻¹` is smooth ($C^\infty$), as a sum of a linear isometry and a
constant.

---

### [`fderiv_linear_add_const`](../../OSforGFF/Spacetime/Euclidean.lean#L260) — Lemma *(private)*

**Statement**: $D(y \mapsto L y + c)(x) = D L(x)$ for a continuous linear map $L$ and constant $c$.

**Proof uses**: `fderiv_add_const`

---

### [`fderiv_act_inv_eq_linear`](../../OSforGFF/Spacetime/Euclidean.lean#L265) — Definition *(private)*

**Lean signature**
```lean
private def fderiv_act_inv_eq_linear (g : (E d)) :
  (fun x => fderiv ℝ (act g⁻¹) x) = fun x => g⁻¹.R.toContinuousLinearMap
```

**Informal**: The Fréchet derivative of `act g⁻¹` is the constant map equal to the linear part
$g^{-1}_R$ everywhere.

---

### [`fderiv_has_temperate_growth`](../../OSforGFF/Spacetime/Euclidean.lean#L275) — Definition *(private)*

**Lean signature**
```lean
private def fderiv_has_temperate_growth (g : (E d)) :
    Function.HasTemperateGrowth (fun x => fderiv ℝ (act g⁻¹) x)
```

**Informal**: The (constant) derivative map of `act g⁻¹` has temperate growth.

---

### [`act_inv_poly_bound`](../../OSforGFF/Spacetime/Euclidean.lean#L280) — Definition *(private)*

**Lean signature**
```lean
private def act_inv_poly_bound (g : (E d)) :
    ∃ k : ℕ, ∃ C : ℝ, ∀ x : (SpaceTime d), ‖act g⁻¹ x‖ ≤ C * (1 + ‖x‖) ^ k
```

**Informal**: A polynomial (in fact linear) growth bound $\lVert \mathrm{act}\, g^{-1}\, x\rVert \le (1 + \lVert g^{-1}_t\rVert)(1 + \lVert x\rVert)$, using that $g^{-1}_R$ is an isometry.

---

### [`euclidean_pullback`](../../OSforGFF/Spacetime/Euclidean.lean#L317) — Definition

**Lean signature**
```lean
noncomputable def euclidean_pullback (g : (E d)) : (SpaceTime d) → (SpaceTime d) := act g⁻¹
```

**Informal**: The fundamental pullback map $x \mapsto g^{-1} \cdot x$ underlying all Euclidean
actions on function spaces.

---

### [`euclidean_pullback_temperate_growth`](../../OSforGFF/Spacetime/Euclidean.lean#L320) — Lemma

**Statement**: The pullback map `euclidean_pullback g` has temperate growth (needed for the
Schwartz-space action).

**Proof uses**: [`fderiv_has_temperate_growth`](../../OSforGFF/Spacetime/Euclidean.lean#L275), [`contDiff_act_inv`](../../OSforGFF/Spacetime/Euclidean.lean#L253), [`act_inv_poly_bound`](../../OSforGFF/Spacetime/Euclidean.lean#L280)

---

### [`euclidean_pullback_polynomial_bounds`](../../OSforGFF/Spacetime/Euclidean.lean#L332) — Lemma

**Statement**: The pullback map satisfies the reverse polynomial bound
$$\lVert x\rVert \le (1 + \lVert g^{-1}_t\rVert)\,(1 + \lVert \mathrm{euclidean\_pullback}\, g\, x\rVert)^1,$$
using the isometry property of $g^{-1}_R$.

---

### [`euclidean_action`](../../OSforGFF/Spacetime/Euclidean.lean#L354) — Definition

**Lean signature**
```lean
noncomputable def euclidean_action (g : (E d)) (f : (SchwartzTestFunctionℂ d)) : (SchwartzTestFunctionℂ d) :=
  SchwartzMap.compCLM (𝕜 := ℂ)
    (hg := euclidean_pullback_temperate_growth g)
    (hg_upper := euclidean_pullback_polynomial_bounds g) f
```

**Informal**: The Euclidean action on complex test functions via pullback,
$(g \bullet f)(x) = f(g^{-1} \cdot x)$.

---

*This file has **14** definitions and **24** theorems/lemmas (0 with sorry).*
