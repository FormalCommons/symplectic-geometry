/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import TauCeti.Analysis.Real.Sqrt

/-!
# Consequences of the mean value theorem on the real line

A real function that has a positive derivative at each point of a convex set `D ⊆ ℝ` is strictly
increasing on `D` (`StrictMonoOn.of_forall_hasDerivAt_pos`). The derivative is only asked to exist
pointwise, as `∃ d, 0 < d ∧ HasDerivAt f d x`, which is the form in which constructions by the
chain rule usually give it. This is Mathlib's mean value theorem `strictMonoOn_of_deriv_pos`, to
which the proof reduces.

A real function that is bounded below on `[a, ∞)`, and whose derivative there is at most `c`,
has `0 ≤ c` (`nonneg_of_bddBelow_of_hasDerivAt_le`): for `c < 0`, Mathlib's
`Convex.image_sub_le_mul_sub_of_deriv_le` makes it fall below every bound.

A function `f : ℝ → ℝ`, nonnegative on `[a, b]`, whose derivative there is at most `2 * K * √f`,
with `0 ≤ K`, has a square root that grows on `[a, b]` at most like `K` times the elapsed time
(`Real.sqrt_le_sqrt_add_mul_of_hasDerivAt_le`). Away from the zeros of `f` this is the chain
rule for `√f`; the proof applies the mean value theorem to `√(f + ε)` and lets `ε` tend to `0`.
-/

public section

/-- A function `f : ℝ → ℝ` that has a positive derivative at every point of a convex set `D` is
strictly increasing on `D`. -/
theorem StrictMonoOn.of_forall_hasDerivAt_pos {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (h : ∀ x ∈ D, ∃ d, 0 < d ∧ HasDerivAt f d x) : StrictMonoOn f D := by
  refine strictMonoOn_of_deriv_pos hD (fun x hx ↦ ?_) fun x hx ↦ ?_
  · obtain ⟨d, -, hd⟩ := h x hx
    exact hd.continuousAt.continuousWithinAt
  · obtain ⟨d, hd0, hd⟩ := h x (interior_subset hx)
    rwa [hd.deriv]

open Set in
/-- If `f : ℝ → ℝ` is bounded below on `[a, ∞)` and has a derivative `f' t ≤ c` at every
`t ≥ a`, then `0 ≤ c`. -/
theorem nonneg_of_bddBelow_of_hasDerivAt_le {f f' : ℝ → ℝ} {a c : ℝ}
    (hb : BddBelow (f '' Ici a)) (hf : ∀ t ∈ Ici a, HasDerivAt f (f' t) t)
    (hle : ∀ t ∈ Ici a, f' t ≤ c) : 0 ≤ c := by
  by_contra! hc
  obtain ⟨m, hm⟩ := hb
  -- On `[a, ∞)`, `f t ≤ f a + c * (t - a)`, which falls below `m` at the time `t` below.
  have hdec (t : ℝ) (ht : a ≤ t) : f t - f a ≤ c * (t - a) :=
    (convex_Ici a).image_sub_le_mul_sub_of_deriv_le
      (fun s hs ↦ (hf s hs).continuousAt.continuousWithinAt)
      (fun s hs ↦ (hf s (interior_subset hs)).differentiableAt.differentiableWithinAt)
      (fun s hs ↦ (hf s (interior_subset hs)).deriv ▸ hle s (interior_subset hs))
      a self_mem_Ici t ht ht
  have hma : m ≤ f a := hm (mem_image_of_mem f self_mem_Ici)
  set t := a + (f a - m + 1) / -c
  have hta : a ≤ t := le_add_of_nonneg_right (div_nonneg (by linarith) (by linarith))
  have hmt : m ≤ f t := hm (mem_image_of_mem f hta)
  have hct : c * (t - a) = -(f a - m + 1) := by
    simp only [t, add_sub_cancel_left]
    field_simp [hc.ne]
  linarith [hdec t hta]

open Set in
/-- If `f : ℝ → ℝ` is nonnegative on `[a, b]`, has a derivative `f' s` at every `s ∈ [a, b]`,
and `f' s ≤ 2 * K * √(f s)` there, with `0 ≤ K` and `a ≤ b`, then
`√(f b) ≤ √(f a) + K * (b - a)`. -/
theorem Real.sqrt_le_sqrt_add_mul_of_hasDerivAt_le {f f' : ℝ → ℝ} {K a b : ℝ}
    (hf : ∀ s ∈ Icc a b, 0 ≤ f s) (hd : ∀ s ∈ Icc a b, HasDerivAt f (f' s) s)
    (hle : ∀ s ∈ Icc a b, f' s ≤ 2 * K * √(f s)) (hK : 0 ≤ K) (hab : a ≤ b) :
    √(f b) ≤ √(f a) + K * (b - a) := by
  -- For `ε > 0`, `√(f + ε)` is differentiable on `[a, b]`, with derivative at most `K`.
  have key (ε : ℝ) (hε : 0 < ε) : √(f b + ε) ≤ √(f a + ε) + K * (b - a) := by
    have hpos (s : ℝ) (hs : s ∈ Icc a b) : 0 < f s + ε := add_pos_of_nonneg_of_pos (hf s hs) hε
    have hdε (s : ℝ) (hs : s ∈ Icc a b) :
        HasDerivAt (fun s ↦ √(f s + ε)) (f' s / (2 * √(f s + ε))) s :=
      ((hd s hs).add_const ε).sqrt (hpos s hs).ne'
    have hleε (s : ℝ) (hs : s ∈ Icc a b) : deriv (fun s ↦ √(f s + ε)) s ≤ K := by
      have h2 := Real.sqrt_pos.2 (hpos s hs)
      rw [(hdε s hs).deriv, div_le_iff₀ (by positivity)]
      have h1 : √(f s) ≤ √(f s + ε) := Real.sqrt_le_sqrt (by linarith)
      nlinarith [hle s hs]
    have := (convex_Icc a b).image_sub_le_mul_sub_of_deriv_le
      (fun s hs ↦ (hdε s hs).continuousAt.continuousWithinAt)
      (fun s hs ↦ (hdε s (interior_subset hs)).differentiableAt.differentiableWithinAt)
      (fun s hs ↦ hleε s (interior_subset hs)) a (left_mem_Icc.2 hab) b (right_mem_Icc.2 hab) hab
    linarith
  refine le_of_forall_pos_le_add fun δ hδ ↦ ?_
  calc √(f b) ≤ √(f b + δ ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
    _ ≤ √(f a + δ ^ 2) + K * (b - a) := key _ (by positivity)
    _ ≤ √(f a) + δ + K * (b - a) := by
      gcongr
      exact (Real.sqrt_add_le_add_sqrt _ _).trans_eq (by rw [Real.sqrt_sq hδ.le])
    _ = √(f a) + K * (b - a) + δ := by ring

end
