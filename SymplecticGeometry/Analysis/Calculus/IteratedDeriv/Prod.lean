/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import TauCeti.Analysis.Calculus.IteratedFDeriv.Parametric

/-!
# Iterated derivatives in the second variable of a function of two variables

* `ContDiffAt.continuousAt_iteratedDeriv_prod_right`: if `f : P × 𝕜 → F` is `Cⁿ` at `(p, x)`,
  then for `m ≤ n` the `m`-th iterated derivative of the slices `y ↦ f (q.1, y)`, evaluated at
  `q.2`, is continuous in `q` at `(p, x)`. It is Tau Ceti's `ContDiffAt.iteratedFDeriv_snd`
  with smoothness order `0` (continuity) and derivative order `i = m`, read through
  `iteratedDeriv_eq_iteratedFDeriv`.
* `ContinuousOn.uncurry_of_iteratedDeriv` and `ContinuousOn.deriv_of_iteratedDeriv`: if the
  iterated derivatives of orders up to `m` of the members `G p` of a family are jointly
  continuous in `(p, x)` on a set, then so are the values and, for `1 ≤ m`, the derivatives.
* `ContDiff.continuousOn_iteratedDeriv_snd`: the iterated derivatives of orders up to `m ≤ n`
  of a `Cⁿ` function `f`, seen as functions of `(p, x)` that do not depend on `p`, are
  continuous.
-/

public section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {P : Type*} [NormedAddCommGroup P]
  [NormedSpace 𝕜 P] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- If `f : P × 𝕜 → F` is `Cⁿ` at `(p, x)` and `m ≤ n`, then
`q ↦ iteratedDeriv m (fun y ↦ f (q.1, y)) q.2` is continuous at `(p, x)`. -/
theorem ContDiffAt.continuousAt_iteratedDeriv_prod_right {n : WithTop ℕ∞} {f : P × 𝕜 → F}
    {p : P} {x : 𝕜} (hf : ContDiffAt 𝕜 n f (p, x)) {m : ℕ} (hm : m ≤ n) :
    ContinuousAt (fun q : P × 𝕜 ↦ iteratedDeriv m (fun y ↦ f (q.1, y)) q.2) (p, x) := by
  simp only [iteratedDeriv_eq_iteratedFDeriv]
  rw [← Function.uncurry_curry f] at hf
  exact (continuous_eval_const _).continuousAt.comp
    (hf.iteratedFDeriv_snd (m := 0) (by simpa using hm)).continuousAt

section Family

variable {Q : Type*} [TopologicalSpace Q] {s : Set (Q × 𝕜)} {m : ℕ}

/-- If `(p, x) ↦ iteratedDeriv k (G p) x` is continuous on `s` for every `k ≤ m`, then so is
`(p, x) ↦ G p x`. -/
theorem ContinuousOn.uncurry_of_iteratedDeriv {G : Q → 𝕜 → F}
    (h : ∀ k ≤ m, ContinuousOn (fun q : Q × 𝕜 ↦ iteratedDeriv k (G q.1) q.2) s) :
    ContinuousOn (fun q : Q × 𝕜 ↦ G q.1 q.2) s := by
  simpa only [iteratedDeriv_zero] using h 0 m.zero_le

/-- If `(p, x) ↦ iteratedDeriv k (G p) x` is continuous on `s` for every `k ≤ m`, where
`1 ≤ m`, then so is `(p, x) ↦ deriv (G p) x`. -/
theorem ContinuousOn.deriv_of_iteratedDeriv {G : Q → 𝕜 → F}
    (h : ∀ k ≤ m, ContinuousOn (fun q : Q × 𝕜 ↦ iteratedDeriv k (G q.1) q.2) s) (hm : 1 ≤ m) :
    ContinuousOn (fun q : Q × 𝕜 ↦ deriv (G q.1) q.2) s := by
  simpa only [iteratedDeriv_one] using h 1 hm

/-- If `f` is `Cⁿ` and `m ≤ n`, then for every `k ≤ m` the function
`(p, x) ↦ iteratedDeriv k f x` is continuous on `s`. -/
theorem ContDiff.continuousOn_iteratedDeriv_snd {n : WithTop ℕ∞} {f : 𝕜 → F}
    (hf : ContDiff 𝕜 n f) (hm : m ≤ n) :
    ∀ k ≤ m, ContinuousOn (fun q : Q × 𝕜 ↦ iteratedDeriv k f q.2) s := fun k hk ↦
  ((hf.continuous_iteratedDeriv k ((Nat.cast_le.2 hk).trans hm)).comp continuous_snd).continuousOn

end Family
