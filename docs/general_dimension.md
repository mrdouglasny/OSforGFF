# Toward general dimension `d ≥ 2` — lifting the OS3 `d ≤ 5` bound

> **Status: IMPLEMENTED (Stage H, August 2026).** The program below has been carried out:
> the `d ≤ 5` hypothesis is gone, and the free-field Osterwalder–Schrader theorems hold in
> *every* spacetime dimension `d ≥ 2`
> (`gaussianFreeField_satisfies_all_OS_axioms_of_dim`, see
> [`dimension_generic.md`](dimension_generic.md)). The note is kept as the mathematical
> record of the obstruction and its removal; the *Implementation notes* section at the end
> records where the formalization deviated from the plan.

## Summary

The library is already generic in `d`; every OS proof, the Minlos construction, and the
`gaussianFreeField_satisfies_all_OS_axioms_of_dim` corollary are parameterized by `d` with no
dimension-specific reasoning. Exactly **one** lemma carries the upper bound `d ≤ 5`: the Fubini
domination in the OS3 mixed-representation argument. Its cap is a *sharp* integrability coming from
using only **first-order** vanishing of positive-time test functions at the time boundary. Replacing
that with **higher-order (Hadamard/Malgrange) boundary vanishing** — and the correspondingly higher
Beta-function moment — removes the bound for all `d`. The mathematics is classical; the cost is the
Lean formalization of one uniform Taylor-type estimate plus mechanical rethreading. Rough estimate:
**1–3 weeks**, with negligible mathematical risk.

## Where the two dimension bounds come from

- **`2 ≤ d` — intrinsic, stays.** Reflection positivity reflects the time coordinate; the
  construction needs a time axis (`getTimeComponent`) and the time/space split `ℝ × ℝ^{d−1}`. This
  is structural to the OS framework and is not a target for removal.
- **`d ≤ 5` — a single, sharp integrability.** It enters only through the OS3 proper-time / spatial-
  momentum Fubini exchange. OS0, OS1, OS2, OS4, the Minlos measure construction, Parseval,
  positive-definiteness, and the UV-divergence driver are all unrestricted for `d ≥ 2`.

## The obstruction, precisely

The reflection-positive bilinear form is written in a mixed representation over proper time
`s ∈ (0, ∞)` and spatial momentum `k ∈ ℝ^{d−1}`; justifying the integration-order exchange
(`OS3_MixedRepInfra.fubini_s_ksp_swap`, whose domination is `integrable_dominate_G`) requires an
`s`-integrable dominator near `s = 0`. The `OS3_MixedRepInfra` module header flagged this, at the
time, as *the only place* `Fact (d ≤ 5)` was used (the hypothesis is gone from the library — see
"Implementation notes" below).

Positive-time test functions satisfy `tsupport f ⊆ {x | getTimeComponent x > 0}`, hence vanish on
the closed complement `{x₀ ≤ 0}` (in code: the "`getTimeComponent x ≤ 0 → f x = 0`" lemmas in
`Spacetime/PositiveTimeTestFunction.lean`). The current argument uses only the **first-order**
consequence `|f(x)| ≲ x₀`, which produces the time-boundary moment

    ∫₀^∞ ∫₀^∞ x₀ y₀ · e^{−(x₀+y₀)²/4s} dx₀ dy₀
      = ∫₀^∞ (u³/6) · e^{−u²/4s} du        (u = x₀ + y₀)
      ∝ s² ,

and with the one-dimensional time normalization `√(π/s) ∝ s^{−1/2}` the dominator is
`∝ s^{3/2} e^{−s(‖k‖²+m²)}` — a power **independent of `d`**, because the heat-kernel prefactor
`(4πs)^{−d/2}` cancels the spatial Fourier volume `(4πs)^{(d−1)/2}`, leaving the 1-D factor
`(4πs)^{−1/2}`. Integrating the momentum over `ℝ^{d−1}` contributes `∝ s^{−(d−1)/2}`, so the outer
`s`-integrand is

    ∝ s^{(4−d)/2} · e^{−s m²} ,

integrable near `s = 0` iff `(4 − d)/2 > −1`, i.e. **`d ≤ 5`**. For first-order vanishing this is
sharp — no choice of constants recovers it. (The moment `∫₀^u x₀(u−x₀) dx₀ = u³/6` is already
carried out in `OS3_MixedRepInfra`.)

## The fix: higher-order boundary vanishing

A Schwartz function that is identically zero on the open half-space `{x₀ < 0}` has all
`x₀`-derivatives zero there, and they extend by continuity to the boundary — so `f` is **flat to all
orders** at `{x₀ = 0}`. By the Hadamard/Malgrange flatness–factorization (equivalently, Taylor with
integral remainder), for every order `N` there is a bound

    |f(x)| ≤ C_N · x₀^N · ρ_N(x̄) ,     ρ_N(x̄) = Schwartz transverse decay from the seminorm of ∂₀^N f ,

uniform in the transverse coordinate `x̄ ∈ ℝ^{d−1}`. Feeding the order-`N` bound through the same
computation turns the boundary moment into an **Euler Beta integral**:

    ∫₀^u x₀^N (u − x₀)^N dx₀ = u^{2N+1} · B(N+1, N+1) ,
    ∫₀^∞ u^{2N+1} e^{−u²/4s} du ∝ s^{N+1} ,

so the dominator becomes `∝ s^{N+1/2}` and the outer `s`-integrand becomes

    ∝ s^{N + 1 − d/2} · e^{−s m²} ,

integrable near `s = 0` iff `N + 1 − d/2 > −1`, i.e. `N > d/2 − 2`. Taking `N = d` (or any
`N ≥ ⌈d/2⌉ − 1`) works for every `d`. The library takes `N = d`; the historical `N = 1` case
(valid through `d = 5`) survives as the order-one corollaries.

## Formalization plan

The ingredients live in mathlib, but the packaged estimate does not; the work is assembling them.

1. **[new — the main piece] Uniform order-`N` boundary bound.** A lemma of the shape
   `|f x| ≤ C_N · (getTimeComponent x)^N · (Schwartz transverse decay)` for
   `f : PositiveTimeTestFunction d`. Ingredients: the existing boundary-vanishing lemmas;
   `taylorWithinEval` / `taylor_mean_remainder` along the `e₀` direction; the `SchwartzMap` seminorm
   API and `iteratedFDeriv` bounds for the transverse decay of `∂₀^N f`, uniform in `x̄`. Note: the
   tidy factorization `f = x₀^N · g` is *harder* to formalize than the inequality (division lemmas),
   so prove the inequality directly.
2. **[moderate] Beta moment.** `∫₀^u x^N (u − x)^N dx = u^{2N+1} B(N+1, N+1)` via `Real.betaIntegral`
   (`B(N+1,N+1) = Γ(N+1)² / Γ(2N+2)`); generalizes the existing `u³/6`.
3. **[moderate] Re-derive the domination.** Generalize the moment computation in
   `OS3_MixedRepInfra`, then re-prove `integrable_dominate_G` and `fubini_s_ksp_swap` with the
   order-`N` dominator (`integrableOn_rpow_mul_exp_neg_mul_rpow` at exponent `s^{N+1−d/2}`).
4. **[mechanical] Rethread.** Remove `[Fact (d ≤ 5)]` from `integrable_dominate_G`,
   `fubini_s_ksp_swap`, `OS3_MixedRep` (`heatKernel_bilinear_to_mixed_rep`,
   `bessel_bilinear_eq_mixed_representation`, `bilinear_to_k0_inside` — the last has since
   moved to `Legacy/UnusedOS.lean`), `OS3_CovarianceRP`
   (`mixed_representation`, `freeCovariance_reflection_positive_*`), `OS3_ReflectionPositivity`, and
   `OS/Master.lean` (`..._generic`, `..._of_dim`). Delete the per-instance `Fact (n ≤ 5)` instances
   and update `Guardrails.lean` accordingly.

Estimated **1–3 weeks**, dominated by step 1; the mathematics carries no research risk.

## Implementation notes (Stage H, August 2026)

The four steps above were carried out, with three deviations:

1. **Step 1 (uniform order-`N` bound) — by induction, not Taylor.** Instead of an `N`-th
   order Taylor formula, `Spacetime/ProdIntegrable.lean` proves
   `schwartz_vanishing_pow_decay` by induction on `N` at the level of Schwartz functions:
   the time derivative `∂₀f` of a Schwartz function vanishing on `{x₀ ≤ 0}` is again such a
   function (`schwartz_vanishing_fderiv_time`, via one-sided derivative uniqueness on
   `Iic 0`), and one ODE-comparison step
   (`image_norm_le_of_norm_deriv_right_le_deriv_boundary`, boundary function
   `K·s^{N+1}/(N+1)`) upgrades order `N` to `N+1`; the `1/N!` constants accumulate silently
   in the existential constant. The transverse decay `ρ_N` is realized as the uniform
   `(1 + ‖x̄‖)^{-d}` weight.
2. **Step 2 (Beta moment) — a bound suffices.** The OS3 chain consumes only an upper bound,
   so `∫₀^u x^N(u−x)^N dx ≤ u^{2N+1}` (integrand ≤ `u^{2N}`) replaces the exact Beta value;
   the odd Gaussian moment `∫₀^∞ u^{2N+1}e^{−u²/4s}du = (N!/2)(4s)^{N+1}` is proved exactly
   (`integral_odd_pow_gaussian`), giving `heat_kernel_moment_integral_pow_bound`:
   the double moment is `≤ C_N·s^{N+1/2}`.
3. **Step 3/4 (domination and rethread) — at `N = d`.** `dominate_G` carries `s^{d+1/2}`;
   the outer proper-time integrand is `s^{(d+2)/2}e^{−sm²}`, integrable for every `d`
   (`integrable_dominate_G`, no dimension hypothesis). All twenty `[Fact (d ≤ 5)]` sites
   and the per-instance `Fact (n ≤ 5)` boilerplate were removed, and `Guardrails.lean`'s
   frozen statement of `_of_dim` was re-captured in its all-dimensions form.

## Payoff

Lifting the bound turns `gaussianFreeField_satisfies_all_OS_axioms_of_dim` into a genuine
all-dimensions theorem: OS0–OS4 for the free GFF in **every** `d ≥ 2`, via the canonical
`GFFPropagator.ofProperTime` — with no per-`d` closed form required.

A general-`d` closed-form kernel is an *independent, optional* addition: `General/BesselK.lean`'s
`besselK ν` and its master Schwinger identity are already `ν`-generic, so

    properTimeCovariance d m r = (4π)^{−d/2} · 2 · (r / 2m)^{1 − d/2} · K_{d/2 − 1}(m r)

follows for general `d` (order `ν = d/2 − 1`); but `_of_dim` needs none of it.

## References

- **Hadamard/Malgrange flatness–factorization**: a smooth function flat to order `N` on a
  hyperplane factors through `x₀^N`; only the resulting inequality is used here.
- The time-boundary moment is the Euler Beta function `B(N+1, N+1)`.
- The OS3 mixed-representation / reflection-positivity argument: the `OS3_MixedRepInfra.lean` module
  header and [`dimension_generic.md`](dimension_generic.md) ("OS3 and the order-`d` domination").
