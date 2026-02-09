# Basic Definitions

Core type definitions and infrastructure for the AQFT formalization: spacetime geometry, symmetry groups, test function spaces, Schwartz space integration, and generating functionals.

## 1. Spacetime and Symmetries

### Mathematical Background

The spacetime is $\mathbb{R}^4$ with the standard Euclidean metric, modeled as `EuclideanSpace ℝ (Fin 4)`. The coordinate index 0 is the time direction. The Euclidean symmetry group $E(4) = O(4) \rtimes \mathbb{R}^4$ acts on spacetime by rotations and translations.

Key structures:
- **Spacetime:** $\mathbb{R}^4$ with the standard Euclidean inner product.
- **Time coordinate:** The projection $x \mapsto x_0$.
- **Euclidean group:** $E(4) = O(4) \rtimes \mathbb{R}^4$ acting on spacetime and test functions.
- **Time reflection:** $\Theta: (t,\mathbf{x}) \mapsto (-t,\mathbf{x})$, a distinguished involution in $E(4)$.
- **Spacetime decomposition:** The measurable equivalence $\mathbb{R}^4 \cong \mathbb{R} \times \mathbb{R}^3$ separating time and spatial coordinates.
- **Positive time set:** The open half-space $\{x \in \mathbb{R}^4 : x_0 > 0\}$.

### Key Declarations (`OSforGFF/Basic.lean`)

| Declaration | Description |
|-------------|-------------|
| [`STDimension`](../OSforGFF/Basic.lean#L111) | Spacetime dimension ($= 4$) |
| [`SpaceTime`](../OSforGFF/Basic.lean#L112) | $\mathbb{R}^4 =$ `EuclideanSpace ℝ (Fin 4)` |
| [`getTimeComponent`](../OSforGFF/Basic.lean#L116) | $x \mapsto x_0$ |

### Key Declarations (`OSforGFF/Euclidean.lean`)

| Declaration | Description |
|-------------|-------------|
| [`O4`](../OSforGFF/Euclidean.lean#L108) | Orthogonal group $O(4)$ |
| [`QFT.E`](../OSforGFF/Euclidean.lean#L113) | Euclidean group $E(4) = O(4) \rtimes \mathbb{R}^4$ |
| [`QFT.act`](../OSforGFF/Euclidean.lean#L119) | Group action of $E(4)$ on spacetime |
| [`measurePreserving_act`](../OSforGFF/Euclidean.lean#L295) | $E(4)$ preserves Lebesgue measure |

### Key Declarations (`OSforGFF/DiscreteSymmetry.lean`)

| Declaration | Description |
|-------------|-------------|
| [`QFT.timeReflection`](../OSforGFF/DiscreteSymmetry.lean#L120) | $\Theta: (t,\mathbf{x}) \mapsto (-t,\mathbf{x})$ |
| [`QFT.timeReflectionMatrix`](../OSforGFF/DiscreteSymmetry.lean#L123) | Matrix representation of $\Theta$ |
| [`QFT.timeReflectionLE`](../OSforGFF/DiscreteSymmetry.lean#L177) | $\Theta$ as a linear isometric equivalence |
| [`QFT.timeReflection_measurePreserving`](../OSforGFF/DiscreteSymmetry.lean#L216) | $\Theta$ preserves Lebesgue measure |
| [`QFT.compTimeReflection`](../OSforGFF/DiscreteSymmetry.lean#L230) | $f \mapsto f \circ \Theta$ on $\mathcal{S}(\mathbb{R}^4,\mathbb{C})$ |
| [`QFT.compTimeReflectionReal`](../OSforGFF/DiscreteSymmetry.lean#L251) | $f \mapsto f \circ \Theta$ on $\mathcal{S}(\mathbb{R}^4,\mathbb{R})$ |

### Key Declarations (`OSforGFF/Basic.lean` — Spatial Geometry)

| Declaration | Description |
|-------------|-------------|
| [`SpatialCoords`](../OSforGFF/Basic.lean#L323) | Spatial coordinates $\mathbb{R}^3$ |
| [`spatialPart`](../OSforGFF/Basic.lean#L329) | Spatial projection $\mathbb{R}^4 \to \mathbb{R}^3$ |
| [`E`](../OSforGFF/Euclidean.lean#L113) | Relativistic energy $E(m,k) = \sqrt{\lVert k\rVert^2 + m^2}$ |

### Key Declarations (`OSforGFF/SpacetimeDecomp.lean`)

| Declaration | Description |
|-------------|-------------|
| [`spacetimeDecomp`](../OSforGFF/SpacetimeDecomp.lean#L49) | Measurable equivalence $\mathbb{R}^4 \cong \mathbb{R} \times \mathbb{R}^3$ |
| [`spacetimeDecomp_measurePreserving`](../OSforGFF/SpacetimeDecomp.lean#L63) | The decomposition preserves Lebesgue measure |

### Key Declarations (`OSforGFF/PositiveTimeTestFunction_real.lean`)

| Declaration | Description |
|-------------|-------------|
| [`HasPositiveTime`](../OSforGFF/PositiveTimeTestFunction_real.lean#L42) | Predicate: $x_0 > 0$ |
| [`positiveTimeSet`](../OSforGFF/PositiveTimeTestFunction_real.lean#L45) | $\{x \in \mathbb{R}^4 : x_0 > 0\}$ |

### Euclidean Group Structure

The Euclidean group `QFT.E` is formalized as a structure containing an orthogonal matrix $R \in O(4)$ and a translation vector $t \in \mathbb{R}^4$. The group operations are:

- **Multiplication:** $(R_1, t_1) \cdot (R_2, t_2) = (R_1 R_2,\  R_1 t_2 + t_1)$
- **Identity:** $(I, 0)$
- **Inverse:** $(R, t)^{-1} = (R^{-1},\  -R^{-1} t)$
- **Action:** $g \cdot x = Rx + t$

The file proves that this forms a `Group` and that the action preserves the Lebesgue measure.

---

## 2. Test Function Spaces

### Mathematical Background

Test functions are Schwartz-class functions on $\mathbb{R}^4$, serving as the "smearing functions" that pair with distributional field configurations. The formalization uses Mathlib's `SchwartzMap` type.

Key types:
- **TestFunction:** $\mathcal{S}(\mathbb{R}^4, \mathbb{R})$
- **TestFunctionℂ:** $\mathcal{S}(\mathbb{R}^4, \mathbb{C})$
- **PositiveTimeTestFunction:** Real Schwartz functions supported in $\{x_0 > 0\}$
- **FieldConfiguration:** The dual space of TestFunction, representing distributional field configurations

The complex test function space carries additional structure: complex conjugation (`conjSchwartz`), a star operation (`starTestFunction`), and decomposition into real and imaginary parts.

### Key Declarations (`OSforGFF/Basic.lean`)

| Declaration | Description |
|-------------|-------------|
| [`TestFunction`](../OSforGFF/Basic.lean#L133) | $\mathcal{S}(\mathbb{R}^4, \mathbb{R})$ |
| [`TestFunctionℂ`](../OSforGFF/Basic.lean#L135) | $\mathcal{S}(\mathbb{R}^4, \mathbb{C})$ |
| [`FieldConfiguration`](../OSforGFF/Basic.lean#L166) | $\mathrm{WeakDual}\ \mathbb{R}\ \mathrm{TestFunction}$ |
| [`distributionPairing`](../OSforGFF/Basic.lean#L177) | $\langle\omega, f\rangle$ for $\omega :$ FieldConfiguration, $f :$ TestFunction |
| [`distributionPairingCLM`](../OSforGFF/Basic.lean#L192) | The pairing as CLM: $\mathrm{TestFunction} \to \mathrm{FieldConfiguration} \to_L \mathbb{R}$ |
| [`distributionPairingℂ_real`](../OSforGFF/Basic.lean#L304) | $\langle\omega, f\rangle_{\mathbb{C}}$ for $f : \mathcal{S}(\mathbb{R}^4,\mathbb{C})$ |
| [`complex_testfunction_decompose`](../OSforGFF/Basic.lean#L261) | $f = \mathrm{Re}(f) + i\ \mathrm{Im}(f)$ |

### Key Declarations (`OSforGFF/ComplexTestFunction.lean`)

| Declaration | Description |
|-------------|-------------|
| [`toComplex`](../OSforGFF/ComplexTestFunction.lean#L224) | $\mathcal{S}(\mathbb{R}^4,\mathbb{R}) \hookrightarrow \mathcal{S}(\mathbb{R}^4,\mathbb{C})$ |
| [`toComplexCLM`](../OSforGFF/ComplexTestFunction.lean#L270) | The embedding as CLM |
| [`conjSchwartz`](../OSforGFF/ComplexTestFunction.lean#L314) | $f \mapsto \bar{f}$ on $\mathcal{S}(\mathbb{R}^4,\mathbb{C})$ |
| [`pairing_linear_combo`](../OSforGFF/ComplexTestFunction.lean#L132) | $\langle\omega, tf + sg\rangle = t\langle\omega,f\rangle + s\langle\omega,g\rangle$ |

### Key Declarations (`OSforGFF/PositiveTimeTestFunction_real.lean`)

| Declaration | Description |
|-------------|-------------|
| [`PositiveTimeTestFunction`](../OSforGFF/PositiveTimeTestFunction_real.lean#L67) | Submodule of TestFunction supported in $\{t > 0\}$ |
| [`starTestFunction`](../OSforGFF/PositiveTimeTestFunction_real.lean#L96) | Star operation on complex test functions |

### Key Declarations (`OSforGFF/Euclidean.lean`)

| Declaration | Description |
|-------------|-------------|
| [`euclidean_action`](../OSforGFF/Euclidean.lean#L407) | $E(4)$ action on $\mathcal{S}(\mathbb{R}^4,\mathbb{C})$ |
| [`euclidean_action_real`](../OSforGFF/Euclidean.lean#L415) | $E(4)$ action on $\mathcal{S}(\mathbb{R}^4,\mathbb{R})$ |
| [`euclidean_action_CLM`](../OSforGFF/Euclidean.lean#L442) | Action as a continuous linear map |

### Time Translation (`OSforGFF/TimeTranslation.lean`)

Time translation is the one-parameter subgroup of the Euclidean group that shifts the time coordinate. It is formalized in detail because of its role in the ergodicity axiom (OS4).

| Declaration | Description |
|-------------|-------------|
| [`timeShift`](../OSforGFF/TimeTranslation.lean#L70) | $(s, x) \mapsto x + s\ e_0$ |
| [`timeTranslationSchwartz`](../OSforGFF/TimeTranslation.lean#L213) | $T_s$ on $\mathcal{S}(\mathbb{R}^4,\mathbb{R})$ |
| [`timeTranslationSchwartzℂ`](../OSforGFF/TimeTranslation.lean#L221) | $T_s$ on $\mathcal{S}(\mathbb{R}^4,\mathbb{C})$ |
| [`timeTranslationSchwartzCLM`](../OSforGFF/TimeTranslation.lean#L199) | $T_s$ as CLM |
| [`timeTranslationSchwartz_add`](../OSforGFF/TimeTranslation.lean#L239) | $T_{s+t} = T_s \circ T_t$ |
| [`timeTranslationSchwartz_zero`](../OSforGFF/TimeTranslation.lean#L252) | $T_0 = \mathrm{id}$ |
| [`continuous_timeTranslationSchwartz`](../OSforGFF/TimeTranslation.lean#L746) | $s \mapsto T_s f$ continuous $\mathbb{R} \to \mathcal{S}$ |
| [`schwartz_timeTranslation_lipschitz_seminorm`](../OSforGFF/TimeTranslation.lean#L358) | $\lVert T_h f - f\rVert_{k,n} \le \lvert h\rvert(1+\lvert h\rvert)^k 2^k(\lVert f\rVert_{k,n+1}+\lVert f\rVert_{0,n+1}+1)$ |
| [`timeTranslationDistribution`](../OSforGFF/TimeTranslation.lean#L874) | $T_s$ on field configurations |
| [`timeTranslationDistribution_add`](../OSforGFF/TimeTranslation.lean#L883) | $T_{s+t}^* = T_s^* \circ T_t^*$ |

The Lipschitz seminorm bound is a fully proved result (no axioms) that is central to proving continuity of the time translation in the Schwartz topology. The proof uses the mean value theorem, Peetre's inequality for polynomial weight shifting, and careful norm estimates on iterated derivatives.

---

## 3. Schwartz Space Integration

### Mathematical Background

Products of Schwartz functions with singular kernels arise throughout the construction. This section provides integrability results for such products, enabling the use of Fubini's theorem and change-of-variables.

The key technical result is the Tonelli-type identity for spacetime integrals: when $K(t_1, t_2)$ is a bounded measurable kernel depending only on time coordinates,

$$\iint \|f(x)\|\ \|g(y)\|\ K(x_0, y_0)\ dx\ dy = \iint K(t_1, t_2)\ G_f(t_1)\ G_g(t_2)\ dt_1\ dt_2$$

where $G_f(t) = \int_{\mathbb{R}^3} \|f(t, v)\|\ dv$ is the spatial marginal.

### Key Declarations (`OSforGFF/SchwartzProdIntegrable.lean`)

| Declaration | Description |
|-------------|-------------|
| [`schwartz_vanishing_linear_bound`](../OSforGFF/SchwartzProdIntegrable.lean#L39) | $f\mid_{t\le 0}=0 \implies \lvert f(t,x)\rvert \le Ct$ for $t > 0$ |
| [`schwartz_vanishing_ftc_decay`](../OSforGFF/SchwartzProdIntegrable.lean#L353) | $\lvert f(t,x)\rvert \le Ct/(1+\lVert x\rVert)^4$ for positive-time-supported $f$ |
| [`spatialNormIntegral`](../OSforGFF/SchwartzProdIntegrable.lean#L308) | $G_f(t) = \int_{\mathbb{R}^3}\lvert f(t,x)\rvert\ dx$ |
| [`spatialNormIntegral_linear_bound`](../OSforGFF/SchwartzProdIntegrable.lean#L607) | $G_f(t) \le Ct$ for positive-time-supported Schwartz $f$ |
| [`schwartz_time_slice_integrable`](../OSforGFF/SchwartzProdIntegrable.lean#L247) | Each time slice of a Schwartz function is integrable in spatial variables |

### Key Declarations (`OSforGFF/SchwartzTonelli.lean`)

| Declaration | Description |
|-------------|-------------|
| [`schwartz_tonelli_spacetime`](../OSforGFF/SchwartzTonelli.lean#L113) | Tonelli factorization of spacetime double integrals |

### Key Declarations (`OSforGFF/BesselFunction.lean`)

| Declaration | Description |
|-------------|-------------|
| [`besselK1`](../OSforGFF/BesselFunction.lean#L47) | $K_1(z) = \int_0^\infty e^{-z\cosh t}\cosh t\ dt$ |

---

## 4. Generating Functionals

### Mathematical Background

The generating functional $Z[J] = \int e^{i\langle\omega,J\rangle}\ d\mu(\omega)$ encodes all correlation functions of the field theory. For a Gaussian measure with covariance $C$, it takes the explicit form $Z[J] = e^{-\frac{1}{2}C(J,J)}$.

The Schwinger $n$-point functions are defined as

$$S_n(f_1, \ldots, f_n) = \int \langle\omega,f_1\rangle \cdots \langle\omega,f_n\rangle\ d\mu(\omega)$$

For the 2-point function, $S_2(f,g) = \int \langle\omega,f\rangle\ \langle\omega,g\rangle\ d\mu$.

The Gaussian property `IsGaussianMeasure` requires $Z[J] = e^{-\frac{1}{2}S_2(J,J)}$, i.e., all correlation functions are determined by the 2-point function via Wick's theorem.

### Key Declarations (`OSforGFF/Basic.lean`)

| Declaration | Description |
|-------------|-------------|
| [`GJGeneratingFunctional`](../OSforGFF/Basic.lean#L218) | $Z[J] = \int e^{i\langle\omega,J\rangle}\ d\mu$ for real $J$ |
| [`GJGeneratingFunctionalℂ`](../OSforGFF/Basic.lean#L311) | Complex generating functional for complex $J$ |
| [`GJMean`](../OSforGFF/Basic.lean#L316) | $\int \langle\omega,f\rangle\ d\mu$ |

### Key Declarations (`OSforGFF/Schwinger.lean`)

| Declaration | Description |
|-------------|-------------|
| [`SchwingerFunction`](../OSforGFF/Schwinger.lean#L128) | $S_n(f_1,\ldots,f_n)$ |
| [`SchwingerFunction₁`](../OSforGFF/Schwinger.lean#L133) | 1-point function (mean) |
| [`SchwingerFunction₂`](../OSforGFF/Schwinger.lean#L138) | $S_2(f,g)$ for real test functions |
| [`SchwingerFunctionℂ`](../OSforGFF/Schwinger.lean#L168) | Complex $n$-point function |
| [`SchwingerFunctionℂ₂`](../OSforGFF/Schwinger.lean#L174) | Complex $S_2(f,g)$ |
| [`CovarianceBilinear`](../OSforGFF/Schwinger.lean#L180) | All $\langle\omega,f\rangle\langle\omega,g\rangle$ integrable |
| [`IsGaussianMeasure`](../OSforGFF/Schwinger.lean#L329) | $Z[J] = e^{-\frac{1}{2}S_2(J,J)}$ |

### Key Declarations (`OSforGFF/SchwingerTwoPointFunction.lean`)

| Declaration | Description |
|-------------|-------------|
| [`SmearedTwoPointFunction`](../OSforGFF/SchwingerTwoPointFunction.lean#L80) | 2-point function smeared with bump functions |
| [`SchwingerTwoPointFunction`](../OSforGFF/SchwingerTwoPointFunction.lean#L115) | Distributional 2-point function (limit of smeared) |
| [`schwingerTwoPointFunction_eq_kernel`](../OSforGFF/SchwingerTwoPointFunction.lean#L180) | $S_2(f,g) = \iint f\ C\ g \implies$ SchwingerTwoPointFunction $= C$ |
| [`smearedTwoPoint_tendsto_schwingerTwoPoint`](../OSforGFF/SchwingerTwoPointFunction.lean#L144) | Smeared 2-point $\to$ kernel via double mollifier |

### Detailed Proof Outline

**Smeared to distributional 2-point function** (`smearedTwoPoint_tendsto_schwingerTwoPoint`): Given that $S_2(f,g) = \iint f(u)\ C(u-v)\ g(v)\ du\ dv$ for a kernel $C$ continuous away from the origin:

1. Express `SmearedTwoPointFunction` as a double convolution of bump functions with $C$.
2. Apply `double_mollifier_convergence` from FunctionalAnalysis.lean.
3. As the bump support shrinks to zero, the smeared function converges pointwise to $C(x)$ for $x \ne 0$.

This connects the abstract Schwinger 2-point functional to the concrete position-space kernel.

## References

- Glimm, J. and Jaffe, A. *Quantum Physics: A Functional Integral Point of View*, Springer (1987).
- Osterwalder, K. and Schrader, R. "Axioms for Euclidean Green's functions", *Comm. Math. Phys.* 31 (1973), 83-112.
- Simon, B. *The $P(\phi)_2$ Euclidean (Quantum) Field Theory*, Princeton University Press (1974).
