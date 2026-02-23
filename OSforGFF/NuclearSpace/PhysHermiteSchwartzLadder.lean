/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Calculus.Deriv.Shift
import OSforGFF.NuclearSpace.PhysHermiteSchwartz

/-!
# Ladder relations for PhysLean harmonic-oscillator eigenfunctions (Schwartz form)

This file records the basic raising/lowering identities for the unnormalized 1D eigenfunctions
`eigenfunctionReal ξ n` and transports them to the `SchwartzMap` version
`eigenfunctionRealSchwartz ξ hξ n`.

These are the key algebraic inputs for relating Schwartz seminorms to weighted `ℓ²`-seminorms on
Hermite coefficients.
-/

open scoped BigOperators

namespace PhysLean

noncomputable section

open SchwartzMap

section OneDim

variable {ξ : ℝ}

/-! ## Function-level recurrences -/

lemma eigenfunctionReal_succ (n : ℕ) (x : ℝ) :
    eigenfunctionReal ξ (n + 1) x =
      2 * (x / ξ) * eigenfunctionReal ξ n x - (2 * n : ℝ) * eigenfunctionReal ξ (n - 1) x := by
  -- Evaluate the physicists' Hermite recurrence at `x/ξ`, then multiply by the common Gaussian factor.
  have hH :
      physHermite (n + 1) (x / ξ) =
        2 * (x / ξ) * physHermite n (x / ξ) - (2 * n : ℝ) * physHermite (n - 1) (x / ξ) := by
    -- apply the functional recurrence and simplify scalar multiplications
    have := congrArg (fun f : ℝ → ℝ => f (x / ξ)) (physHermite_succ_fun' (n := n))
    simpa [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using this
  -- now unfold `eigenfunctionReal` and use `hH`
  simp [PhysLean.eigenfunctionReal, hH, sub_eq_add_neg, mul_add, mul_assoc, mul_left_comm, mul_comm]

lemma x_mul_eigenfunctionReal (hξ : ξ ≠ 0) (n : ℕ) (x : ℝ) :
    x * eigenfunctionReal ξ n x =
      (ξ / 2) * eigenfunctionReal ξ (n + 1) x + (n * ξ) * eigenfunctionReal ξ (n - 1) x := by
  have h := eigenfunctionReal_succ (ξ := ξ) (n := n) (x := x)
  have h' :
      2 * (x / ξ) * eigenfunctionReal ξ n x =
        eigenfunctionReal ξ (n + 1) x + (2 * n : ℝ) * eigenfunctionReal ξ (n - 1) x := by
    linarith [h]
  have hξ' : (ξ : ℝ) ≠ 0 := hξ
  have hx : (ξ / 2) * (2 * (x / ξ)) = x := by
    field_simp [hξ']
  calc
    x * eigenfunctionReal ξ n x
        = ((ξ / 2) * (2 * (x / ξ))) * eigenfunctionReal ξ n x := by simp [hx]
    _ = (ξ / 2) * (2 * (x / ξ) * eigenfunctionReal ξ n x) := by
          simp [mul_assoc]
    _ = (ξ / 2) * (eigenfunctionReal ξ (n + 1) x + (2 * n : ℝ) * eigenfunctionReal ξ (n - 1) x) := by
          -- multiply the recurrence `h'` by the scalar `(ξ/2)`
          simpa [mul_assoc] using congrArg (fun t => (ξ / 2) * t) h'
    _ = (ξ / 2) * eigenfunctionReal ξ (n + 1) x +
          ((ξ / 2) * (2 * n : ℝ)) * eigenfunctionReal ξ (n - 1) x := by
          -- distribute the scalar across the sum
          simp [mul_add, mul_assoc]
    _ = (ξ / 2) * eigenfunctionReal ξ (n + 1) x + (n * ξ) * eigenfunctionReal ξ (n - 1) x := by
          -- rewrite the scalar coefficient `(ξ/2) * (2*n)` as `n*ξ`
          have hs : (ξ / 2) * (2 * (n : ℝ)) = (n : ℝ) * ξ := by ring
          -- both sides have the same first term, so it suffices to rewrite the coefficient in the second term
          -- (use `hs` after rewriting `((2*n : ℝ))` as `2 * (n : ℝ)`).
          -- `ring` is robust here (it treats the complicated `eigenfunctionReal ...` values as atoms).
          ring

/-! ## Derivative ladder for `eigenfunctionReal` -/

lemma deriv_gaussianHO (hξ : ξ ≠ 0) (x : ℝ) :
    deriv (fun y : ℝ ↦ gaussianHO ξ y) x = (-x / (ξ ^ 2)) * gaussianHO ξ x := by
  -- `gaussianHO ξ y = exp (-(y^2)/(2 ξ^2))`
  have hdiff : DifferentiableAt ℝ (fun y : ℝ ↦ - y ^ 2 / (2 * ξ ^ 2)) x := by fun_prop
  -- differentiate the exponential using the chain rule
  have h :=
    (deriv_exp (f := fun y : ℝ ↦ - y ^ 2 / (2 * ξ ^ 2)) (x := x) hdiff)
  -- compute the derivative of the exponent explicitly
  -- `d/dy [-(y^2)/(2ξ^2)] = -(y/(ξ^2))`
  have hexp :
      deriv (fun y : ℝ ↦ - y ^ 2 / (2 * ξ ^ 2)) x = -x / (ξ ^ 2) := by
    -- rewrite as a constant multiple of `y ↦ y^2`
    have hpow : DifferentiableAt ℝ (fun y : ℝ ↦ y ^ 2) x := by fun_prop
    have hfun :
        (fun y : ℝ ↦ - y ^ 2 / (2 * ξ ^ 2)) =
          (fun y : ℝ ↦ (-(1 / (2 * ξ ^ 2))) * (y ^ 2)) := by
      funext y
      ring
    calc
      deriv (fun y : ℝ ↦ - y ^ 2 / (2 * ξ ^ 2)) x
          = deriv (fun y : ℝ ↦ (-(1 / (2 * ξ ^ 2))) * (y ^ 2)) x := by
              simp [hfun]
      _ = (-(1 / (2 * ξ ^ 2))) * deriv (fun y : ℝ ↦ y ^ 2) x := by
              simp [hpow]
      _ = (-(1 / (2 * ξ ^ 2))) * ((2 : ℝ) * x) := by
              simp
      _ = -x / (ξ ^ 2) := by
              have hξ' : (ξ : ℝ) ≠ 0 := hξ
              field_simp [hξ']
  -- finish by rewriting `Real.exp` back to `gaussianHO`
  -- (note `h` is `deriv (exp ∘ exponent) = exp(exponent) * deriv exponent`)
  -- avoid `simp` changing the denominator shape before rewriting by `hexp`
  have h' :=
    (deriv_exp (f := fun y : ℝ ↦ - y ^ 2 / (2 * ξ ^ 2)) (x := x) hdiff)
  -- rewrite the exponent derivative using the closed form `hexp`
  -- and then fold back to `gaussianHO`.
  -- (`Real.exp (...) * (-x/ξ^2) = (-x/ξ^2) * Real.exp (...)` by commutativity.)
  have h'' :
      deriv (fun y : ℝ ↦ Real.exp (- y ^ 2 / (2 * ξ ^ 2))) x =
        Real.exp (- x ^ 2 / (2 * ξ ^ 2)) * (-x / (ξ ^ 2)) := by
    simpa using (by
      -- start from `h'` and rewrite its RHS
      simpa [hexp] using h')
  -- finish, rewriting `Real.exp` back to `gaussianHO` and commuting the scalar factor
  simpa [gaussianHO, mul_assoc, mul_left_comm, mul_comm] using h''

lemma deriv_eigenfunctionReal_aux (hξ : ξ ≠ 0) (n : ℕ) (x : ℝ) :
    deriv (fun y : ℝ ↦ eigenfunctionReal ξ n y) x =
      ((2 * n : ℝ) / ξ) * eigenfunctionReal ξ (n - 1) x
        + (physHermite n (x / ξ)) * ((-x / (ξ ^ 2)) * gaussianHO ξ x) := by
  -- product rule, then use the derivative of `physHermite` and `gaussianHO`
  have hdiff₁ : DifferentiableAt ℝ (fun y : ℝ ↦ physHermite n (y / ξ)) x := by fun_prop
  have hdiff₂ : DifferentiableAt ℝ (fun y : ℝ ↦ gaussianHO ξ y) x := by
    -- unfold the definition so `fun_prop` can see `Real.exp`
    simpa [gaussianHO] using
      (by
        fun_prop : DifferentiableAt ℝ (fun y : ℝ ↦ Real.exp (- y ^ 2 / (2 * ξ ^ 2))) x)
  -- derivative of the polynomial factor via `deriv_physHermite'`
  have hpoly :
      deriv (fun y : ℝ ↦ physHermite n (y / ξ)) x =
        (2 * n * physHermite (n - 1) (x / ξ)) * (1 / ξ) := by
    have hf : DifferentiableAt ℝ (fun y : ℝ ↦ y / ξ) x := by fun_prop
    -- `deriv_physHermite'` is a simp lemma; `simp` also evaluates `deriv (fun y => y / ξ) x`.
    simp [PhysLean.deriv_physHermite', hf]
  -- derivative of the Gaussian factor
  have hgauss :
      deriv (fun y : ℝ ↦ gaussianHO ξ y) x = (-x / (ξ ^ 2)) * gaussianHO ξ x :=
    deriv_gaussianHO (ξ := ξ) hξ x
  -- combine (keep everything expressed through `eigenfunctionReal` / `gaussianHO`)
  have hmul :=
    (deriv_fun_mul (c := fun y : ℝ ↦ physHermite n (y / ξ)) (d := fun y : ℝ ↦ gaussianHO ξ y)
      (x := x) hdiff₁ hdiff₂)
  -- rewrite with the derivative computations
  -- and repackage the first term as `((2*n)/ξ) * eigenfunctionReal ξ (n-1) x`.
  -- (the second term is exactly `f x * deriv g x`)
  -- The rest is scalar algebra in `ℝ`.
  have hmul' :
      deriv (fun y : ℝ ↦ eigenfunctionReal ξ n y) x =
        ((2 * n * physHermite (n - 1) (x / ξ)) * (1 / ξ)) * gaussianHO ξ x
          + physHermite n (x / ξ) * ((-x / (ξ ^ 2)) * gaussianHO ξ x) := by
    simpa [PhysLean.eigenfunctionReal, hpoly, hgauss, mul_assoc, mul_left_comm, mul_comm, add_assoc,
      add_left_comm, add_comm, -PhysLean.gaussianHO_def] using hmul
  -- now convert the first summand to `((2*n)/ξ) * eigenfunctionReal ξ (n-1) x`
  -- and finish by `ring`.
  simpa [PhysLean.eigenfunctionReal, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm,
    -PhysLean.gaussianHO_def] using hmul'

lemma deriv_eigenfunctionReal (hξ : ξ ≠ 0) (n : ℕ) (x : ℝ) :
    deriv (fun y : ℝ ↦ eigenfunctionReal ξ n y) x =
      ((n : ℝ) / ξ) * eigenfunctionReal ξ (n - 1) x
        - (1 / (2 * ξ)) * eigenfunctionReal ξ (n + 1) x := by
  -- start from the auxiliary formula and rewrite the `x`-term using the multiplication ladder
  have haux := deriv_eigenfunctionReal_aux (ξ := ξ) hξ n x
  -- convert the remaining Gaussian term back to `eigenfunctionReal` and rewrite `x * e_n`
  -- then solve by ring arithmetic
  have hxmul := x_mul_eigenfunctionReal (ξ := ξ) hξ (n := n) (x := x)
  -- `physHermite n (x/ξ) * gaussianHO ξ x` is `eigenfunctionReal ξ n x`
  -- and `(-x / ξ^2) * eigenfunctionReal ξ n x` can be rewritten via `hxmul`.
  -- The algebra is over `ℝ`, so `ring` can finish after rewriting.
  -- First, express the auxiliary formula in terms of `eigenfunctionReal`.
  -- Then rewrite the `x`-term using `hxmul`.
  -- Finally, simplify scalar coefficients.
  -- (We avoid `field_simp` to keep the proof robust and local.)
  have haux' :
      deriv (fun y : ℝ ↦ eigenfunctionReal ξ n y) x =
        ((2 * n : ℝ) / ξ) * eigenfunctionReal ξ (n - 1) x
          + (-x / (ξ ^ 2)) * eigenfunctionReal ξ n x := by
    -- rewrite the final summand of `haux` as `(-x/ξ^2) * eigenfunctionReal ξ n x`
    -- and simplify the first summand into the stated coefficient.
    simpa [PhysLean.eigenfunctionReal, mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm,
      add_comm, div_eq_mul_inv, -PhysLean.gaussianHO_def] using haux
  -- now use `hxmul` to eliminate `x * eigenfunctionReal ξ n x`
  -- by rewriting `(-x/ξ^2) * e_n` as a linear combination of `e_{n+1}` and `e_{n-1}`.
  -- `(-x/ξ^2) * e_n = -(1/ξ^2) * (x * e_n)`.
  -- and `x * e_n` is given by `hxmul`.
  have hrewrite :
      (-x / (ξ ^ 2)) * eigenfunctionReal ξ n x =
        - (1 / (2 * ξ)) * eigenfunctionReal ξ (n + 1) x
          - ((n : ℝ) / ξ) * eigenfunctionReal ξ (n - 1) x := by
    -- start from the `x`-ladder and scale appropriately
    -- `(-x / ξ^2) * e_n = -(1/ξ^2) * (x * e_n)`
    -- then use `hxmul` and simplify coefficients.
    have hξ' : (ξ : ℝ) ≠ 0 := hξ
    -- rewrite `x`-ladder in a form suitable for scaling
    -- `x * e_n = (ξ/2) e_{n+1} + (n*ξ) e_{n-1}`
    -- multiply both sides by `-(1/ξ^2)`
    calc
      (-x / (ξ ^ 2)) * eigenfunctionReal ξ n x
          = (-(1 / (ξ ^ 2))) * (x * eigenfunctionReal ξ n x) := by
              ring
      _ = (-(1 / (ξ ^ 2))) *
            ((ξ / 2) * eigenfunctionReal ξ (n + 1) x + (n * ξ) * eigenfunctionReal ξ (n - 1) x) := by
              rw [hxmul]
      _ = - (1 / (2 * ξ)) * eigenfunctionReal ξ (n + 1) x
            - ((n : ℝ) / ξ) * eigenfunctionReal ξ (n - 1) x := by
              field_simp [hξ']
              ring
  -- finish: substitute `hrewrite` into `haux'` and simplify coefficients
  -- `((2n)/ξ) e_{n-1} + [ - (1/(2ξ)) e_{n+1} - (n/ξ) e_{n-1}]`
  -- gives `((n)/ξ) e_{n-1} - (1/(2ξ)) e_{n+1}`.
  calc
    deriv (fun y : ℝ ↦ eigenfunctionReal ξ n y) x
        = ((2 * n : ℝ) / ξ) * eigenfunctionReal ξ (n - 1) x
            + (-x / (ξ ^ 2)) * eigenfunctionReal ξ n x := haux'
    _ = ((2 * n : ℝ) / ξ) * eigenfunctionReal ξ (n - 1) x
            + (- (1 / (2 * ξ)) * eigenfunctionReal ξ (n + 1) x
                - ((n : ℝ) / ξ) * eigenfunctionReal ξ (n - 1) x) := by
          rw [hrewrite]
    _ = ((n : ℝ) / ξ) * eigenfunctionReal ξ (n - 1) x
            - (1 / (2 * ξ)) * eigenfunctionReal ξ (n + 1) x := by
          ring

/-! ## SchwartzMap-level multiplication by `x` -/

lemma smulLeftCLM_id_eigenfunctionRealSchwartz (hξ : ξ ≠ 0) (n : ℕ) :
    SchwartzMap.smulLeftCLM (𝕜 := ℝ) (F := ℝ) (fun x : ℝ ↦ x)
        (eigenfunctionRealSchwartz ξ hξ n) =
      (ξ / 2) • eigenfunctionRealSchwartz ξ hξ (n + 1)
        + (n * ξ) • eigenfunctionRealSchwartz ξ hξ (n - 1) := by
  have hg : (fun x : ℝ ↦ x).HasTemperateGrowth := by fun_prop
  ext x
  -- reduce to the function-level identity `x * e_n = (ξ/2) e_{n+1} + (n ξ) e_{n-1}`
  simpa [SchwartzMap.smulLeftCLM_apply_apply (F := ℝ) hg,
    eigenfunctionRealSchwartz_apply, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm, add_assoc] using
    (x_mul_eigenfunctionReal (ξ := ξ) hξ n x)

lemma deriv_eigenfunctionRealSchwartz (hξ : ξ ≠ 0) (n : ℕ) (x : ℝ) :
    deriv (eigenfunctionRealSchwartz ξ hξ n) x =
      ((n : ℝ) / ξ) * eigenfunctionRealSchwartz ξ hξ (n - 1) x
        - (1 / (2 * ξ)) * eigenfunctionRealSchwartz ξ hξ (n + 1) x := by
  -- reduce to the function-level identity via `eigenfunctionRealSchwartz_apply`
  have hfun :
      (fun y : ℝ ↦ eigenfunctionRealSchwartz ξ hξ n y) =
        (fun y : ℝ ↦ eigenfunctionReal ξ n y) := by
    funext y
    simp [eigenfunctionRealSchwartz_apply]
  simpa [hfun, eigenfunctionRealSchwartz_apply] using
    (deriv_eigenfunctionReal (ξ := ξ) hξ (n := n) (x := x))

end OneDim

end

end PhysLean
