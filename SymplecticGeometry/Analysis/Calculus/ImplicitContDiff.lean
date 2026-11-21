/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
# Smooth local solutions of `f (x, y) = z`

Let `f : E₁ × E₂ → F` be `C^n`, `n ≠ 0`, at `u`, with a partial derivative in the second variable
that is invertible at `u`. Then the equation `f (x, y) = z` has, near `(u.1, f u)`, a `C^n` solution
`y = g (x, z)` with `g (u.1, f u) = u.2`. This is the implicit function theorem of Mathlib
(`ContDiffAt.implicitFunction`), applied to `((x, z), y) ↦ f (x, y) - z`, so that the value `z`
varies as a parameter too.

## Main results

* `ContDiffAt.exists_contDiffAt_eventually_apply_eq`: the smooth local solution.
-/

public section

open Filter
open scoped Topology ContDiff

variable {𝕜 : Type*} [RCLike 𝕜]
  {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [CompleteSpace E₁]
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂] [CompleteSpace E₂]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

/-- If `f : E₁ × E₂ → F` is `C^n`, `n ≠ 0`, at `u`, and its partial derivative `y ↦ f' (0, y)` at
`u` is invertible, then there is a `g : E₁ × F → E₂`, `C^n` at `(u.1, f u)`, with
`g (u.1, f u) = u.2` and `f (x, g (x, z)) = z` for all `(x, z)` near `(u.1, f u)`. -/
theorem ContDiffAt.exists_contDiffAt_eventually_apply_eq {f : E₁ × E₂ → F} {u : E₁ × E₂}
    {n : ℕ∞ω} (hf : ContDiffAt 𝕜 n f u) (hn : n ≠ 0)
    (hinv : (fderiv 𝕜 f u ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
    ∃ g : E₁ × F → E₂, g (u.1, f u) = u.2 ∧ ContDiffAt 𝕜 n g (u.1, f u) ∧
      ∀ᶠ q in 𝓝 (u.1, f u), f (q.1, g q) = q.2 := by
  set G : (E₁ × F) × E₂ → F := fun w ↦ f (w.1.1, w.2) - w.1.2
  set w₀ : (E₁ × F) × E₂ := ((u.1, f u), u.2)
  have hGat : ContDiffAt 𝕜 n G w₀ :=
    (hf.comp w₀ (contDiffAt_fst.fst.prodMk contDiffAt_snd)).sub contDiffAt_fst.snd
  have hd : HasFDerivAt f (fderiv 𝕜 f u) u := (hf.differentiableAt hn).hasFDerivAt
  -- The partial derivative of `G` in its last variable is that of `f` in its second variable.
  have hpartial : fderiv 𝕜 G w₀ ∘L .inr 𝕜 (E₁ × F) E₂ = fderiv 𝕜 f u ∘L .inr 𝕜 E₁ E₂ :=
    ((hGat.differentiableAt hn).hasFDerivAt.comp u.2 (hasFDerivAt_prodMk_right w₀.1 u.2)).unique
      ((hd.comp u.2 (hasFDerivAt_prodMk_right u.1 u.2)).sub_const (f u))
  have hinv' : (fderiv 𝕜 G w₀ ∘L .inr 𝕜 (E₁ × F) E₂).IsInvertible := hpartial ▸ hinv
  have hGw₀ : G w₀ = 0 := sub_self _
  refine ⟨hGat.implicitFunction hn hinv', hGat.implicitFunction_apply_self hn hinv',
    hGat.contDiffAt_implicitFunction hn hinv', ?_⟩
  filter_upwards [hGat.eventually_apply_implicitFunction hn hinv'] with q hq
  rw [hGw₀] at hq
  exact sub_eq_zero.1 hq

end
