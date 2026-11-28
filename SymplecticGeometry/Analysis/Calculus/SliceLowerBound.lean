/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Normed.Operator.Bilinear
import SymplecticGeometry.Analysis.Calculus.Deriv.SecondOrderLowerBound
import TauCeti.Analysis.Calculus.ContDiff.Differentiable
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Calculus.Morse.Bott
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# A quadratic lower bound transverse to a slice

Let `f : E × F → ℝ` be `C²` at `(a₀, 0)`, with `F` finite-dimensional, be critical along the slice
`E × {0}` near `a₀`, and have a second derivative at `(a₀, 0)` that is positive definite on the
fibre directions `(0, w)`. Then `f (a, b) - f (a₀, 0)` is at least `c ‖b‖²` near `(a₀, 0)` for
some `c > 0`. This is a lower companion of Tau Ceti's upper bound
`TauCeti.exists_abs_sub_le_mul_norm_snd_sq`.

The critical value is constant along the slice near `a₀` (Tau Ceti's
`TauCeti.eventually_apply_mk_zero_eq`). The coercivity of the Hessian on the fibre at `(a₀, 0)` is
Tau Ceti's `IsCompact.exists_pos_forall_mul_norm_sq_le`, for a single form, and it persists, with
half the constant, near `(a₀, 0)` by continuity of the Hessian. The rest restricts `f` to the
segments `t ↦ (a, t • b)`, `t ∈ [0, 1]`, and bounds it from below with the second-order lower
bound `SymplecticGeometry.add_mul_sub_add_mul_sub_sq_div_two_le`. That segment argument adapts the
proof of Tau Ceti's second derivative test,
`ContDiffAt.eventually_lt_of_fderiv_eq_zero_of_fderiv_fderiv_pos`, from segments through a
critical point to segments leaving the slice.

## Main results

* `ContDiffAt.exists_pos_eventually_mul_norm_snd_sq_le_sub`: the quadratic lower bound
  `c * ‖p.2‖ ^ 2 ≤ f p - f (a₀, 0)` for `p` near `(a₀, 0)`.
-/

public section

open Set Filter Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- **A quadratic lower bound transverse to a slice.** Let `f : E × F → ℝ` be `C²` at `(a₀, 0)`,
with `F` finite-dimensional, such that `fderiv ℝ f (a, 0) = 0` for `a` near `a₀`, and such that
the second derivative of `f` at `(a₀, 0)` is positive at `((0, w), (0, w))` for every `w ≠ 0`.
Then there is `c > 0` with `c * ‖p.2‖ ^ 2 ≤ f p - f (a₀, 0)` for every `p` near `(a₀, 0)`. -/
theorem ContDiffAt.exists_pos_eventually_mul_norm_snd_sq_le_sub {f : E × F → ℝ} {a₀ : E}
    (hf : ContDiffAt ℝ 2 f (a₀, 0)) (hcrit : ∀ᶠ a in 𝓝 a₀, fderiv ℝ f (a, 0) = 0)
    (hpos : ∀ w : F, w ≠ 0 → 0 < fderiv ℝ (fderiv ℝ f) (a₀, 0) (0, w) (0, w)) :
    ∃ c > 0, ∀ᶠ p in 𝓝 (a₀, 0), c * ‖p.2‖ ^ 2 ≤ f p - f (a₀, 0) := by
  set B₀ := fderiv ℝ (fderiv ℝ f) (a₀, 0)
  -- The Hessian is coercive on the fibre directions at `(a₀, 0)`.
  obtain ⟨c, hc, hcB⟩ := (isCompact_singleton (x := ())).exists_pos_forall_mul_norm_sq_le
    (b := fun _ ↦ B₀.bilinearComp (ContinuousLinearMap.inr ℝ E F)
      (ContinuousLinearMap.inr ℝ E F)) continuousOn_const fun _ _ w hw ↦ by simpa using hpos w hw
  have hc₀ (w : F) : c * ‖w‖ ^ 2 ≤ B₀ (0, w) (0, w) := by simpa using hcB () rfl w
  -- Near `(a₀, 0)`, `f` stays `C²` and its Hessian stays `c / 2`-coercive on the fibre.
  have hC2 : ∀ᶠ q in 𝓝 ((a₀, 0) : E × F), ContDiffAt ℝ 2 f q := hf.eventually (by simp)
  have hnear : ∀ᶠ q in 𝓝 ((a₀, 0) : E × F), ContDiffAt ℝ 2 f q ∧ ‖fderiv ℝ (fderiv ℝ f) q - B₀‖ <
      c / 2 :=
    hC2.and <|
      (hf.continuousAt_fderiv_fderiv le_rfl).eventually
        (Metric.ball_mem_nhds B₀ (half_pos hc)) |>.mono fun q hq ↦ by
          -- `rw [dist_eq_norm]` does not find `dist` here, as the instance paths differ.
          exact (dist_eq_norm (fderiv ℝ (fderiv ℝ f) q) B₀).symm ▸ hq
  -- Along the slice, `f` is critical with constant value `f (a₀, 0)`.
  have hdiff : ∀ᶠ a in 𝓝 a₀, DifferentiableAt ℝ f (a, 0) :=
    ((continuous_id.prodMk continuous_const).tendsto a₀).eventually
      (hf.eventually_differentiableAt (by simp))
  have hslice : ∀ᶠ q : E × F in 𝓝 (a₀, 0), f (q.1, 0) = f (a₀, 0) ∧ fderiv ℝ f (q.1, 0) = 0 :=
    (continuous_fst.tendsto ((a₀, 0) : E × F)).eventually
      ((TauCeti.eventually_apply_mk_zero_eq hcrit hdiff).and hcrit)
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
    have hD := ((hball _ (hseg t ht)).1.1.hasFDerivAt_fderiv le_rfl).differentiableAt
    simpa using TauCeti.hasDerivAt_fderiv_apply_line (p := ((a, 0) : E × F))
      (q := ((0 : E), b)) (s := t) (by simpa using hD) ((0 : E), b)
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
  have key := SymplecticGeometry.add_mul_sub_add_mul_sub_sq_div_two_le zero_le_one
    (fun t ht ↦ (hh t ht).continuousAt.continuousWithinAt)
    (fun t ht ↦ (hh' t ht).continuousAt.continuousWithinAt)
    (fun t ht ↦ (hh t (Ioo_subset_Icc_self ht)).hasDerivWithinAt)
    (fun t ht ↦ (hh' t (Ioo_subset_Icc_self ht)).hasDerivWithinAt)
    (fun t ht ↦ hm t (Ioo_subset_Icc_self ht))
  simp only [zero_smul, one_smul, sub_zero, one_pow, mul_one, h0.1, h0.2,
    zero_apply] at key
  linarith

end
