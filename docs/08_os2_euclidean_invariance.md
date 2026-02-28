# OS2 Euclidean Invariance

## Mathematical Background

OS2 (Euclidean Invariance) requires that the quantum field theory has no preferred direction or origin in Euclidean spacetime. The generating functional must be invariant under the Euclidean group $E(4) = \mathbb{R}^4 \rtimes O(4)$, which comprises translations, rotations, and reflections.

This axiom is essential because:

1. **Lorentz invariance**: After Wick rotation, Euclidean invariance becomes Poincare invariance of the Minkowski theory.
2. **Vacuum uniqueness**: The vacuum state respects all spacetime symmetries.
3. **Correlation functions**: $n$-point functions depend only on relative positions and orientations, not absolute coordinates.

**Theorem (OS2).** For all $g \in E(4)$ and $f \in \mathcal{S}(\mathbb{R}^4, \mathbb{C})$:

$$Z[g \cdot f] = Z[f]$$

where $(g \cdot f)(x) = f(g^{-1} x)$ is the pullback action.

The Euclidean group element $g = (R, t)$ with $R \in O(4)$ and $t \in \mathbb{R}^4$ acts on spacetime as $g \cdot x = Rx + t$, and on test functions by pullback: $(g \cdot f)(x) = f(R^{-1}(x - t))$.

## Proof Strategy

The proof factors into two parts:

1. **General Gaussian result**: For any Gaussian measure whose covariance is Euclidean-invariant, $Z[g \cdot f] = Z[f]$.
2. **GFF-specific**: The free GFF covariance depends only on $\|x - y\|$, which is preserved by Euclidean transformations.

For the GFF with $Z[f] = \exp(-\tfrac{1}{2}\langle f, Cf\rangle_{\mathbb{C}})$, the proof reduces to showing $\langle g \cdot f, C(g \cdot f)\rangle = \langle f, Cf\rangle$, which follows from a change of variables in the double integral using the fact that Euclidean transformations preserve Lebesgue measure and distances.

This is the cleanest OS axiom proof: it requires **zero project-specific axioms**.

**Literature**: Glimm-Jaffe Ch. 6  standard Euclidean field theory references.

## Key Declarations

| Declaration | Description |
|-------------|-------------|
| [`CovarianceEuclideanInvariantℂ_μ_GFF`](../OSforGFF/OS/OS2_Invariance.lean#L151) | $C(gx, gy) = C(x, y)$ for all $g \in E(4)$ (GFF covariance) |
| [`freeCovarianceℂ_bilinear_euclidean_invariant`](../OSforGFF/OS/OS2_Invariance.lean#L111) | $\langle g \cdot f, C(g \cdot h)\rangle = \langle f, Ch\rangle$ |
| [`euclidean_action_apply`](../OSforGFF/OS/OS2_Invariance.lean#L46) | $(g \cdot f)(x) = f(g^{-1} \cdot x)$ |
| [`euclidean_pullback_eq_inv_act`](../OSforGFF/OS/OS2_Invariance.lean#L53) | $g^{-1} \cdot x = \mathrm{act}(g^{-1}, x)$ |
| [`euclidean_pullback_act`](../OSforGFF/OS/OS2_Invariance.lean#L57) | $g^{-1} \cdot (g \cdot y) = y$ |
| [`act_euclidean_pullback`](../OSforGFF/OS/OS2_Invariance.lean#L62) | $g \cdot (g^{-1} \cdot x) = x$ |
| [`actEquiv`](../OSforGFF/OS/OS2_Invariance.lean#L70) | $x \mapsto g \cdot x$ is a measurable equivalence on $\mathbb{R}^4$ |
| [`measurePreserving_actEquiv`](../OSforGFF/OS/OS2_Invariance.lean#L79) | $(g_*)\lambda = \lambda$ for $g \in E(4)$ |

The master theorem `gaussian_satisfies_OS2` in `Measure/GaussianFreeField.lean` derives OS2 from Gaussianity and covariance invariance. The file `OS/OS2_Invariance.lean` proves the GFF-specific covariance invariance.

## Detailed Proof Outline

### Step 1: Euclidean group structure

The Euclidean group $E(4)$ is formalized as `QFT.E` with:
- A rotation/reflection $R \in O(4)$ (formalized as a `LinearIsometry`)
- A translation vector $t \in \mathbb{R}^4$

The group operations are:
- Multiplication: $(R_1, t_1) \cdot (R_2, t_2) = (R_1 R_2,\  R_1 t_2 + t_1)$
- Inverse: $(R, t)^{-1} = (R^{-1},\  -R^{-1} t)$
- Action: $(R, t) \cdot x = Rx + t$

The pullback action on test functions is defined as `euclidean_action g f`, where $(g \cdot f)(x) = f(\mathrm{euclidean\_pullback}\  g\  x)$ with $\mathrm{euclidean\_pullback}\  g\  x = g^{-1} \cdot x$.

### Step 2: Covariance kernel is radial

The free covariance kernel is:

$$C(x, y) = \frac{m}{4\pi^2 \|x - y\|} K_1(m\|x - y\|)$$

This depends only on $\|x - y\|$. Since Euclidean transformations preserve distances:

$$\|g \cdot x - g \cdot y\| = \|R(x - y)\| = \|x - y\|$$

we have $C(g \cdot x, g \cdot y) = C(x, y)$. This is the content of `freeCovariance_euclidean_invariant` from `Covariance/Position.lean`.

### Step 3: Measure preservation

Lebesgue measure on $\mathbb{R}^4$ is invariant under Euclidean transformations. For translations, this is translation invariance of Lebesgue measure. For $R \in O(4)$, this follows from $|\det R| = 1$.

The proof constructs a `MeasurableEquiv` (`actEquiv g`) for each group element and proves it is measure-preserving (`measurePreserving_actEquiv`). This enables the change of variables in integration.

### Step 4: Bilinear form invariance

The complex covariance bilinear form is:

$$\langle f, Ch\rangle_{\mathbb{C}} = \int \int \overline{f(x)}\  C(x,y)\  h(y)\  dx\  dy$$

The proof of $\langle g \cdot f, C(g \cdot h)\rangle = \langle f, Ch\rangle$ proceeds as follows:

1. **Substitute the pullback**: $\langle g \cdot f, C(g \cdot h)\rangle = \int\int \overline{f(g^{-1}x)}\  C(x,y)\  h(g^{-1}y)\  dx\  dy$.

2. **Rewrite the kernel**: Using `act_euclidean_pullback` (i.e., $g \cdot (g^{-1} \cdot x) = x$) and `freeCovariance_euclidean_invariant`:
$$C(x, y) = C(g \cdot (g^{-1} \cdot x),\  g \cdot (g^{-1} \cdot y)) = C(g^{-1} \cdot x,\  g^{-1} \cdot y)$$

3. **Recognize as composition**: The integrand is now $F(g^{-1} x, g^{-1} y)$ where $F(u, v) = \overline{f(u)}\  C(u,v)\  h(v)$.

4. **Change variables**: Apply `MeasurePreserving.integral_comp'` using `measurePreserving_actEquiv` for both integration variables: $\int\int F(g^{-1}x, g^{-1}y)\  dx\  dy = \int\int F(u,v)\  du\  dv = \langle f, Ch\rangle$.

**Lean theorem**: `freeCovarianceℂ_bilinear_euclidean_invariant`

### Step 5: Connect to the GFF measure

The theorem `CovarianceEuclideanInvariantℂ_μ_GFF` connects the abstract covariance of $\mu_{\mathrm{GFF}}$ to the free bilinear form using `gff_two_point_equals_covarianceℂ_free`, then applies `freeCovarianceℂ_bilinear_euclidean_invariant`.

### Step 6: Derive OS2

The general theorem `gaussian_satisfies_OS2` in `Measure/GaussianFreeField.lean` shows that for any Gaussian measure (`isGaussianGJ`) with Euclidean-invariant covariance (`CovarianceEuclideanInvariantℂ`), OS2 holds. The proof is essentially:

$$Z[g \cdot f] = \exp\left(-\tfrac{1}{2}\langle g \cdot f, C(g \cdot f)\rangle\right) = \exp\left(-\tfrac{1}{2}\langle f, Cf\rangle\right) = Z[f]$$

using `h_gaussian` to rewrite $Z[f]$ in Gaussian form and `h_euclidean_invariant` for the covariance equality.

### Axioms Used

**None.** The OS2 proof is fully formal with zero project-specific axioms. It uses only standard properties of the Euclidean group, measure preservation under isometries, and the radial structure of the free propagator.

## References

- J. Glimm and A. Jaffe, *Quantum Physics*, Springer, 2nd ed., Ch. 6.
- K. Osterwalder and R. Schrader, "Axioms for Euclidean Green's Functions I," Comm. Math. Phys. 31 (1973), 83-112.
- B. Simon, *The P(phi)_2 Euclidean (Quantum) Field Theory*, Princeton, 1974 (Euclidean invariance for free fields).
