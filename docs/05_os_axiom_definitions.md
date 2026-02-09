# OS Axiom Definitions

## Mathematical Background

The Osterwalder-Schrader (OS) axioms characterize Euclidean quantum field theories that admit analytic continuation to relativistic (Minkowski) QFTs via the Wick rotation. They were introduced by Osterwalder and Schrader in 1973-1975, building on earlier work of Nelson and Symanzik.

The axioms are stated in terms of the **generating functional** (or characteristic functional):

$$Z[f] = \int_{\Omega} e^{i\langle \omega, f \rangle} \  d\mu(\omega)$$

where $\Omega = \mathcal{S}'(\mathbb{R}^4)$ is the space of tempered distributions (field configurations), $\mu$ is a probability measure on $\Omega$, $f$ is a test function in the Schwartz space $\mathcal{S}(\mathbb{R}^4)$, and $\langle \omega, f \rangle$ denotes the distributional pairing.

This project follows the Glimm-Jaffe formulation (Quantum Physics, pp. 89-90) and proves the axioms for the Gaussian Free Field (GFF) with mass $m > 0$ in 4-dimensional Euclidean spacetime.

## Lean Infrastructure

The axiom definitions live in a single file: `OSforGFF/OS_Axioms.lean`. All definitions take a `ProbabilityMeasure FieldConfiguration` as their primary argument, where `FieldConfiguration` is a type alias for the topological dual of the Schwartz space (representing field configurations $\omega \in \mathcal{S}'(\mathbb{R}^4)$).

Key supporting types and functions:
- `GJGeneratingFunctionalℂ` -- the complex generating functional $Z[f] = \int e^{i\langle\omega, f\rangle} d\mu(\omega)$ for complex test functions
- `GJGeneratingFunctional` -- the real generating functional for real test functions
- `TestFunctionℂ` -- complex Schwartz functions $\mathcal{S}(\mathbb{R}^4, \mathbb{C})$
- `TestFunction` -- real Schwartz functions $\mathcal{S}(\mathbb{R}^4, \mathbb{R})$
- `QFT.E` -- the Euclidean group $E(4) = \mathbb{R}^4 \rtimes O(4)$
- `PositiveTimeTestFunction` -- real test functions supported in $\{t > 0\}$

## Key Declarations

| Declaration | Description |
|-------------|-------------|
| [`OS0_Analyticity`](../OSforGFF/OS_Axioms.lean#L73) | $z \mapsto Z[\sum z_i J_i]$ is analytic on $\mathbb{C}^n$ |
| [`TwoPointIntegrable`](../OSforGFF/OS_Axioms.lean#L79) | $S_2(x)$ is locally integrable |
| [`OS1_Regularity`](../OSforGFF/OS_Axioms.lean#L83) | $\lvert Z[f]\rvert \le e^{c(\lVert f\rVert_1 + \lVert f\rVert_p^p)}$ for some $p \in [1,2]$, $c > 0$ |
| [`OS2_EuclideanInvariance`](../OSforGFF/OS_Axioms.lean#L91) | $Z[g \cdot f] = Z[f]$ for all $g \in E(4)$ |
| [`OS3_ReflectionPositivity`](../OSforGFF/OS_Axioms.lean#L100) | $\sum_{ij} c_i c_j \mathrm{Re}\left(Z[f_i - \Theta f_j]\right) \ge 0$ |
| [`OS4_Clustering`](../OSforGFF/OS_Axioms.lean#L123) | $\lvert Z[f + T_a g] - Z[f]Z[g]\rvert \to 0$ as $\lVert a\rVert \to \infty$ |
| [`OS4_Ergodicity`](../OSforGFF/OS_Axioms.lean#L136) | $\frac{1}{T}\int_0^T A(T_s \varphi)\ ds \to \mathbb{E}_\mu[A]$ in $L^2(\mu)$ |
| [`OS4_PolynomialClustering`](../OSforGFF/OS_Axioms.lean#L158) | $\lvert\mathbb{E}[e^{\langle\varphi,f\rangle + \langle T_s\varphi,g\rangle}] - \mathbb{E}[e^{\langle\varphi,f\rangle}]\mathbb{E}[e^{\langle\varphi,g\rangle}]\rvert \le c(1+s)^{-\alpha}$ |

## Axiom Definitions

### OS0: Analyticity

**Mathematical statement.** For any finite collection of complex test functions $J_1, \ldots, J_n \in \mathcal{S}(\mathbb{R}^4, \mathbb{C})$, the map

$$z = (z_1, \ldots, z_n) \mapsto Z\left[\sum_{i=1}^n z_i J_i\right]$$

is analytic on $\mathbb{C}^n$.

**Lean definition.** `OS0_Analyticity` requires `AnalyticOn` over all of `Set.univ` for the map `z -> GJGeneratingFunctionalℂ dmu (sum i, z i * J i)`, for every `n` and every `J : Fin n -> TestFunctionℂ`.

**Physical meaning.** Analyticity ensures that the Schwinger functions (Euclidean $n$-point correlation functions) are well-defined as functional derivatives of $Z$, and that the theory can be analytically continued from Euclidean to Minkowski signature via the Wick rotation.

### OS1: Regularity

**Mathematical statement.** There exist $p \in [1, 2]$ and $c > 0$ such that for all $f \in \mathcal{S}(\mathbb{R}^4, \mathbb{C})$:

$$|Z[f]| \le \exp\left(c \cdot \left(\|f\|_{L^1} + \|f\|_{L^p}^p\right)\right)$$

When $p = 2$, the two-point Schwinger function $S_2(x)$ must be locally integrable.

**Lean definition.** `OS1_Regularity` is an existential over `p` and `c` with constraints `1 <= p`, `p <= 2`, `c > 0`, plus two conjuncts: (1) the exponential bound on `GJGeneratingFunctionalℂ`, and (2) the conditional `p = 2 -> TwoPointIntegrable dmu`. The auxiliary definition `TwoPointIntegrable` requires `LocallyIntegrable` of `SchwingerTwoPointFunction`.

**Physical meaning.** The generating functional has controlled growth, ensuring the field theory measure is well-defined and the Schwinger functions are tempered distributions. This bound is essential for the OS reconstruction theorem.

### OS2: Euclidean Invariance

**Mathematical statement.** For all $g \in E(4)$ and $f \in \mathcal{S}(\mathbb{R}^4, \mathbb{C})$:

$$Z[g \cdot f] = Z[f]$$

where $(g \cdot f)(x) = f(g^{-1} x)$ is the pullback action.

**Lean definition.** `OS2_EuclideanInvariance` requires equality of `GJGeneratingFunctionalℂ dmu f` and `GJGeneratingFunctionalℂ dmu (euclidean_action g f)` for all `g : QFT.E` and `f : TestFunctionℂ`.

**Physical meaning.** The vacuum state respects Euclidean symmetry: no preferred direction or origin in spacetime. After Wick rotation, this becomes Poincare invariance of the Minkowski theory.

### OS3: Reflection Positivity (Real Formulation)

**Mathematical statement.** Let $\Theta$ denote time reflection: $\Theta(t, \vec{x}) = (-t, \vec{x})$. For test functions $f_1, \ldots, f_n$ supported in the positive time half-space $\{t > 0\}$ and real coefficients $c_1, \ldots, c_n$:

$$\sum_{i,j} c_i\  c_j \cdot \mathrm{Re}\left(Z[f_i - \Theta f_j]\right) \ge 0$$

**Lean definition.** `OS3_ReflectionPositivity` quantifies over `n`, `f : Fin n -> PositiveTimeTestFunction`, and `c : Fin n -> R`, and asserts non-negativity of the double sum involving `GJGeneratingFunctional dmu (f_i.val - compTimeReflectionReal (f_j.val))`.

**Physical meaning.** This is the key axiom for the OS reconstruction theorem. The positive semi-definite form becomes an inner product after quotienting by null vectors, yielding the physical Hilbert space of the QFT.

### OS4: Clustering

**Mathematical statement.** For test functions $f, g$ and any $\varepsilon > 0$, there exists $R > 0$ such that for spatial separation $\|a\| > R$:

$$|Z[f + T_a g] - Z[f] \cdot Z[g]| < \varepsilon$$

where $T_a$ denotes translation by $a$.

**Lean definition.** `OS4_Clustering` quantifies over `f g : TestFunction`, `eps > 0`, and asserts existence of `R > 0` such that the norm of the difference is less than `eps` for all `a : SpaceTime` with `norm a > R`. Translation uses `SchwartzMap.translate`.

**Physical meaning.** Distant regions of spacetime become statistically independent. This is equivalent to uniqueness of the vacuum state.

### OS4: Ergodicity (Alternative Formulation)

**Mathematical statement.** For generating functions $A(\varphi) = \sum_j z_j e^{\langle\varphi, f_j\rangle}$, the time average converges to the expectation in $L^2(\mu)$:

$$\lim_{T \to \infty} \int_\Omega \left|\frac{1}{T}\int_0^T A(T_s \varphi)\  ds - \mathbb{E}_\mu[A]\right|^2 d\mu(\omega) = 0$$

**Lean definition.** `OS4_Ergodicity` expresses this as `Filter.Tendsto ... Filter.atTop (nhds 0)` for the $L^2$ norm of the time-averaged deviation.

### OS4: Polynomial Clustering (Quantitative Variant)

**Mathematical statement.** For any $f, g \in \mathcal{S}(\mathbb{R}^4, \mathbb{C})$ and exponent $\alpha > 0$, there exists $c \ge 0$ such that for all $s \ge 0$:

$$\left|\mathbb{E}_\mu\left[e^{\langle\varphi,f\rangle + \langle T_s\varphi, g\rangle}\right] - \mathbb{E}_\mu\left[e^{\langle\varphi,f\rangle}\right]\mathbb{E}_\mu\left[e^{\langle\varphi,g\rangle}\right]\right| \le c\ (1 + s)^{-\alpha}$$

**Lean definition.** `OS4_PolynomialClustering` takes the measure, exponent `alpha`, and proof `alpha > 0`, then quantifies over `f g : TestFunctionℂ` to assert existence of the constant `c`.

## References

- K. Osterwalder and R. Schrader, "Axioms for Euclidean Green's Functions I," Comm. Math. Phys. 31 (1973), 83-112.
- K. Osterwalder and R. Schrader, "Axioms for Euclidean Green's Functions II," Comm. Math. Phys. 42 (1975), 281-305.
- J. Glimm and A. Jaffe, *Quantum Physics: A Functional Integral Point of View*, Springer, 2nd ed., 1987, pp. 89-90.
