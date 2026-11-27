/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Normed.Operator.Bilinear
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# A quadratic lower bound transverse to a slice

Let `f : E × F → ℝ` be `C²` near `(a₀, 0)`, vanish to first order along the slice `E × {0}` near
`a₀`, and have a second derivative at `(a₀, 0)` that is positive definite on the fibre directions
`(0, w)`, with `F` finite-dimensional. Then `f (a, b)` is at least `c ‖b‖²` near `(a₀, 0)` for some
`c > 0`.

The proof restricts `f` to the segments `t ↦ (a, t • b)`, `t ∈ [0, 1]`: their second derivative
is the Hessian of `f` on `(0, b)`, which stays at least a positive multiple of `‖b‖²` near
`(a₀, 0)` by continuity, and a real function vanishing to first order at `0` with second derivative
at least `m` is at least `m t² / 2` (`SymplecticGeometry.mul_sq_div_two_le_of_hasDerivAt`). The
coercivity at `(a₀, 0)` is Tau Ceti's `IsCompact.exists_pos_forall_mul_norm_sq_le`, for a single
form.

## Main results

* `SymplecticGeometry.mul_sq_div_two_le_of_hasDerivAt`: if `h 0 = 0`, `h' 0 = 0` and `m ≤ h''` on
  `[0, x]`, then `m * x ^ 2 / 2 ≤ h x`.
* `ContDiffAt.exists_pos_eventually_mul_norm_snd_sq_le`: the quadratic lower bound
  `c * ‖p.2‖ ^ 2 ≤ f p` for `p` near `(a₀, 0)`.
-/

public section

open Set Filter Topology

namespace SymplecticGeometry

/-- A real function `h` with derivative `h'`, whose own derivative is `h''`, on `[0, x]`, and with
`h 0 = 0`, `h' 0 = 0` and `m ≤ h''` on `[0, x]`, satisfies `m * x ^ 2 / 2 ≤ h x`. -/
theorem mul_sq_div_two_le_of_hasDerivAt {h h' h'' : ℝ → ℝ} {m x : ℝ} (hx : 0 ≤ x)
    (hh : ∀ t ∈ Icc 0 x, HasDerivAt h (h' t) t) (hh' : ∀ t ∈ Icc 0 x, HasDerivAt h' (h'' t) t)
    (hm : ∀ t ∈ Icc 0 x, m ≤ h'' t) (h0 : h 0 = 0) (h'0 : h' 0 = 0) :
    m * x ^ 2 / 2 ≤ h x := by
  have hint : interior (Icc 0 x) ⊆ Icc 0 x := interior_subset
  -- First `t ↦ h' t - m t` is monotone, so `m t ≤ h' t` on `[0, x]`.
  have h1 : MonotoneOn (fun t ↦ h' t - m * t) (Icc 0 x) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 x)
      (fun t ht ↦ ((hh' t ht).continuousAt.sub (continuousAt_const.mul continuousAt_id))
        |>.continuousWithinAt)
      (fun t ht ↦ (((hh' t (hint ht)).sub ((hasDerivAt_id t).const_mul m)).hasDerivWithinAt))
      (fun t ht ↦ by simpa using hm t (hint ht))
  have hle : ∀ t ∈ Icc 0 x, m * t ≤ h' t := fun t ht ↦ by
    have := h1 ⟨le_rfl, hx⟩ ht ht.1
    simp only [h'0, mul_zero, sub_zero] at this
    linarith
  -- Then `t ↦ h t - m t² / 2` is monotone, and vanishes at `0`.
  have h2 : MonotoneOn (fun t ↦ h t - m * t ^ 2 / 2) (Icc 0 x) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 x)
      (fun t ht ↦ ((hh t ht).continuousAt.sub (by fun_prop)).continuousWithinAt)
      (fun t ht ↦ (((hh t (hint ht)).sub
        (((hasDerivAt_pow 2 t).const_mul m).div_const 2)).hasDerivWithinAt))
      (fun t ht ↦ by
        have := hle t (hint ht)
        norm_num
        linarith)
  have := h2 ⟨le_rfl, hx⟩ ⟨hx, le_rfl⟩ hx
  simp only [h0] at this
  linarith

end SymplecticGeometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- **A quadratic lower bound transverse to a slice.** Let `f : E × F → ℝ` be `C²` at `(a₀, 0)`,
with `F` finite-dimensional, such that `f (a, 0) = 0` and `fderiv ℝ f (a, 0) = 0` for `a` near
`a₀`, and such that the second derivative of `f` at `(a₀, 0)` is positive at `((0, w), (0, w))`
for every `w ≠ 0`. Then there is `c > 0` with `c * ‖p.2‖ ^ 2 ≤ f p` for every `p` near
`(a₀, 0)`. -/
theorem ContDiffAt.exists_pos_eventually_mul_norm_snd_sq_le {f : E × F → ℝ} {a₀ : E}
    (hf : ContDiffAt ℝ 2 f (a₀, 0)) (hzero : ∀ᶠ a in 𝓝 a₀, f (a, 0) = 0)
    (hcrit : ∀ᶠ a in 𝓝 a₀, fderiv ℝ f (a, 0) = 0)
    (hpos : ∀ w : F, w ≠ 0 → 0 < fderiv ℝ (fderiv ℝ f) (a₀, 0) (0, w) (0, w)) :
    ∃ c > 0, ∀ᶠ p in 𝓝 (a₀, 0), c * ‖p.2‖ ^ 2 ≤ f p := by
  set B₀ := fderiv ℝ (fderiv ℝ f) (a₀, 0)
  -- The Hessian is coercive on the fibre directions at `(a₀, 0)`.
  obtain ⟨c, hc, hcB⟩ := (isCompact_singleton (x := ())).exists_pos_forall_mul_norm_sq_le
    (b := fun _ ↦ B₀.bilinearComp (ContinuousLinearMap.inr ℝ E F)
      (ContinuousLinearMap.inr ℝ E F)) continuousOn_const fun _ _ w hw ↦ by simpa using hpos w hw
  have hc₀ (w : F) : c * ‖w‖ ^ 2 ≤ B₀ (0, w) (0, w) := by simpa using hcB () rfl w
  -- Near `(a₀, 0)`, `f` stays `C²` and its Hessian stays `c / 2`-coercive on the fibre.
  have hnear : ∀ᶠ q in 𝓝 ((a₀, 0) : E × F), ContDiffAt ℝ 2 f q ∧ ‖fderiv ℝ (fderiv ℝ f) q - B₀‖ <
      c / 2 :=
    (hf.eventually (by simp)).and <|
      (hf.continuousAt_fderiv_fderiv le_rfl).eventually
        (Metric.ball_mem_nhds B₀ (half_pos hc)) |>.mono fun q hq ↦ by
          -- `rw [dist_eq_norm]` does not find `dist` here, as the instance paths differ.
          exact (dist_eq_norm (fderiv ℝ (fderiv ℝ f) q) B₀).symm ▸ hq
  have hslice : ∀ᶠ q : E × F in 𝓝 (a₀, 0), f (q.1, 0) = 0 ∧ fderiv ℝ f (q.1, 0) = 0 :=
    (continuous_fst.tendsto ((a₀, 0) : E × F)).eventually (hzero.and hcrit)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hnear.and hslice)
  refine ⟨c / 4, by positivity, eventually_of_mem (Metric.ball_mem_nhds _ hr) fun p hp ↦ ?_⟩
  obtain ⟨a, b⟩ := p
  -- The segment from `(a, 0)` to `(a, b)` stays in the ball.
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, (a, t • b) ∈ Metric.ball ((a₀, 0) : E × F) r := by
    intro t ht
    rw [Metric.mem_ball, Prod.dist_eq] at hp ⊢
    refine lt_of_le_of_lt (max_le_max le_rfl ?_) hp
    simp only [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact mul_le_of_le_one_left (norm_nonneg _) ht.2
  have hline (t : ℝ) : HasDerivAt (fun s : ℝ ↦ (a, s • b)) ((0 : E), b) t := by
    simpa using (hasDerivAt_const t a).prodMk ((hasDerivAt_id t).smul_const b)
  -- Restrict `f` to that segment.
  have hh (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun s ↦ f (a, s • b)) (fderiv ℝ f (a, t • b) (0, b)) t :=
    ((hball _ (hseg t ht)).1.1.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t (hline t)
  have hh' (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun s ↦ fderiv ℝ f (a, s • b) (0, b))
        (fderiv ℝ (fderiv ℝ f) (a, t • b) (0, b) (0, b)) t := by
    have := ((hball _ (hseg t ht)).1.1.hasFDerivAt_fderiv le_rfl).comp_hasDerivAt t (hline t)
    simpa using this.clm_apply (hasDerivAt_const t ((0 : E), b))
  have hm (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      c / 2 * ‖b‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ f) (a, t • b) (0, b) (0, b) := by
    set B := fderiv ℝ (fderiv ℝ f) (a, t • b)
    have hB := (hball _ (hseg t ht)).1.2
    have hdiff : |(B - B₀) (0, b) (0, b)| ≤ c / 2 * ‖b‖ ^ 2 := by
      calc |(B - B₀) (0, b) (0, b)| ≤ ‖B - B₀‖ * ‖((0 : E), b)‖ * ‖((0 : E), b)‖ :=
            (Real.norm_eq_abs _ ▸ (B - B₀).le_opNorm₂ _ _)
        _ = ‖B - B₀‖ * ‖b‖ ^ 2 := by simp [Prod.norm_def, sq, mul_assoc]
        _ ≤ c / 2 * ‖b‖ ^ 2 := by gcongr
    have := hc₀ b
    simp only [sub_apply] at hdiff
    linarith [(abs_le.1 hdiff).1]
  have h0 := (hball _ (hseg 0 ⟨le_rfl, zero_le_one⟩)).2
  have key := SymplecticGeometry.mul_sq_div_two_le_of_hasDerivAt zero_le_one hh hh' hm
    (by simpa using h0.1) (by simp [h0.2])
  simp only [one_smul, one_pow, mul_one] at key
  linarith

end
