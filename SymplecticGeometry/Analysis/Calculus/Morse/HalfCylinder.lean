/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import TauCeti.Analysis.Calculus.Morse.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Algebra.Support
import SymplecticGeometry.Analysis.Calculus.ConvexProfile
import SymplecticGeometry.Analysis.Calculus.FDeriv.Prod
import SymplecticGeometry.Analysis.Calculus.FDeriv.Radial
import SymplecticGeometry.Analysis.SpecialFunctions.SmoothTransition

/-!
# Removing critical points of top index on a half-cylinder

Let `V` be a finite-dimensional real inner product space and
`S = [-1, ∞) × closedBall 0 1 ⊆ ℝ × V`. For a smooth `f : ℝ × V → ℝ` whose only critical point
in `S` is a nondegenerate one at `0`, we construct a smooth `μ ≥ 0` supported in `S` such that at
every critical point of `f + μ` in `S` the Hessian of `f + μ` is positive on some vector. So
`f + μ` has no critical point in `S` of index `dim (ℝ × V)`.

## Main results

* `SymplecticGeometry.exists_nonneg_halfCylinder_hessian_pos`: the modification `μ`.

## Construction

`μ (t, y) = β ‖y‖ * Λ t`, where `β` is the radial cutoff of
`exists_contDiff_antitone_cutoff_mul_abs_deriv_le_deriv_deriv` (`1` up to `1/2`, `0` from `1`
on, with `β'' ≥ K |β'|` near `1`) and `Λ` is the convex profile of `exists_contDiff_profile`
(`0` up to `-3/4`, `Λ'' ≥ L Λ'`, `Λ' ≥ A` from `-1/2` on, `Λ ≤ (t + 3/4) Λ'`). On the compact
pieces `[-1, n] × closedBall 0 1` the Hessian of `f` is bounded by `C n`, and away from the box
`(-1/2, 1/2) × ball 0 (1/2)` the size of the differential of `f` is at least `ε n > 0`.
The function `L` is constant on each interval `(n - 1, n]` and is chosen from these bounds.

At a critical point of `f + μ`: in the box, the `t`-derivative of `μ` exceeds that of `f`,
so there is none; elsewhere either the `t`-derivative of `f` is large, and the Hessian is positive
along `(1, 0)` because `Λ''` dominates `Λ'`; or the radial derivative of `f` is large, and the
Hessian is positive along the radial unit vector (where `β''` dominates `β'`), or again along
`(1, 0)` (where `β` is bounded below and `Λ'` is bounded below by `Λ / (t + 3/4)`).

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Theorem 7.3.1.
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963.
-/

public section

open Set Filter Metric
open scoped Topology InnerProductSpace ContDiff

namespace SymplecticGeometry

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- **Removing critical points of top index on a half-cylinder.** Let `f : ℝ × V → ℝ` be smooth
with a nondegenerate critical point at `0` and no other critical point in
`S = [-1, ∞) × closedBall 0 1`. Then there is a smooth `μ ≥ 0` with topological support in `S`
such that at every critical point of `f + μ` in `S` the Hessian of `f + μ` is positive on some
vector. -/
theorem exists_nonneg_halfCylinder_hessian_pos {f : ℝ × V → ℝ} (hf : ContDiff ℝ ∞ f)
    (h0 : TauCeti.IsNondegenerateCriticalPoint f 0)
    (hcrit : ∀ x ∈ Set.Ici (-1 : ℝ) ×ˢ Metric.closedBall (0 : V) 1, fderiv ℝ f x = 0 → x = 0) :
    ∃ μ : ℝ × V → ℝ, ContDiff ℝ ∞ μ ∧ 0 ≤ μ ∧
      tsupport μ ⊆ Set.Ici (-1) ×ˢ Metric.closedBall 0 1 ∧
      ∀ x, fderiv ℝ (f + μ) x = 0 → x ∈ Set.Ici (-1) ×ˢ Metric.closedBall 0 1 →
        ∃ v, 0 < fderiv ℝ (fderiv ℝ (f + μ)) x v v := by
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.2 le_top
  have le_mul_of_div_le {c d M X : ℝ} (hc : 0 < c) (hd : 0 < d) (hdX : d ≤ X)
      (hM : c / d ≤ M) : c ≤ M * X :=
    ((div_le_iff₀ hd).1 hM).trans
      (mul_le_mul_of_nonneg_left hdX ((div_pos hc hd).le.trans hM))
  have hDf : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hDfc : Continuous (fderiv ℝ f) := hDf.continuous
  have hD2fc : Continuous (fderiv ℝ (fderiv ℝ f)) := hDf.continuous_fderiv (by simp)
  have hKc (n : ℕ) : IsCompact (Icc (-1) (n : ℝ) ×ˢ closedBall (0 : V) 1) :=
    isCompact_Icc.prod (isCompact_closedBall 0 1)
  have hUo : IsOpen (Ioo (-(1 / 2) : ℝ) (1 / 2) ×ˢ ball (0 : V) (1 / 2)) :=
    isOpen_Ioo.prod isOpen_ball
  have h0U : (0 : ℝ × V) ∈ Ioo (-(1 / 2) : ℝ) (1 / 2) ×ˢ ball (0 : V) (1 / 2) :=
    ⟨⟨by norm_num, by norm_num⟩, by simp⟩
  have hUK : Ioo (-(1 / 2) : ℝ) (1 / 2) ×ˢ ball (0 : V) (1 / 2) ⊆
      Icc (-1) ((1 : ℕ) : ℝ) ×ˢ closedBall (0 : V) 1 :=
    prod_mono (fun t ht ↦ ⟨by linarith [ht.1], by push_cast; linarith [ht.2]⟩)
      (ball_subset_closedBall.trans (closedBall_subset_closedBall (by norm_num)))
  -- Bounds on the Hessian of `f` on the compact pieces.
  have hHc : Continuous fun p : (ℝ × V) × (ℝ × V) ↦ fderiv ℝ (fderiv ℝ f) p.1 p.2 p.2 :=
    ((hD2fc.comp continuous_fst).clm_apply continuous_snd).clm_apply continuous_snd
  have hCex (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Icc (-1) (n : ℝ) ×ˢ closedBall (0 : V) 1,
      ∀ v : ℝ × V, ‖v‖ = 1 → -C ≤ fderiv ℝ (fderiv ℝ f) x v v := by
    obtain ⟨C, hC⟩ := ((hKc n).prod (isCompact_sphere (0 : ℝ × V) 1)).exists_bound_of_continuousOn
      hHc.continuousOn
    refine ⟨max C 0, le_max_right _ _, fun x hx v hv ↦ ?_⟩
    have := hC (x, v) ⟨hx, mem_sphere_zero_iff_norm.2 hv⟩
    rw [Real.norm_eq_abs] at this
    linarith [neg_abs_le (fderiv ℝ (fderiv ℝ f) x v v), le_max_left C 0]
  choose C hC0 hC using hCex
  -- A bound on the derivative of `∂_t f` on the piece containing the box.
  have hg₁ : ContDiff ℝ ∞ fun x ↦ fderiv ℝ f x (1, 0) := hDf.clm_apply contDiff_const
  obtain ⟨C₁, hC₁⟩ := (hKc 1).exists_bound_of_continuousOn
    (hg₁.continuous_fderiv (by simp)).continuousOn
  -- Lower bounds on the differential of `f` on the compact pieces, away from the box.
  have hεex (n : ℕ) : ∃ ε, 0 < ε ∧
      ∀ x ∈ Icc (-1) (n : ℝ) ×ˢ closedBall (0 : V) 1 \
        Ioo (-(1 / 2) : ℝ) (1 / 2) ×ˢ ball (0 : V) (1 / 2),
        ε ≤ |fderiv ℝ f x (1, 0)| + ‖(fderiv ℝ f x).comp (ContinuousLinearMap.inr ℝ ℝ V)‖ := by
    refine ((hKc n).diff hUo).exists_forall_le' (((hDfc.clm_apply continuous_const).abs).add
      (hDfc.clm_comp continuous_const).norm).continuousOn fun x hx ↦ ?_
    have hp := abs_nonneg (fderiv ℝ f x (1, 0))
    have hq := norm_nonneg ((fderiv ℝ f x).comp (ContinuousLinearMap.inr ℝ ℝ V))
    refine lt_of_le_of_ne (add_nonneg hp hq) fun h ↦ hx.2 ?_
    simp only [Pi.add_apply] at h
    have hx0 : x = 0 := hcrit x (prod_mono Icc_subset_Ici_self subset_rfl hx.1)
      (ContinuousLinearMap.prod_ext
        (ContinuousLinearMap.ext_ring (by simpa using abs_eq_zero.1 (by linarith : _ = (0 : ℝ))))
        (by simpa using norm_eq_zero.1 (by linarith : _ = (0 : ℝ))))
    exact hx0 ▸ h0U
  choose ε hε0 hε using hεex
  -- The radial cutoff `β`.
  obtain ⟨β, hβ, hβI, hβanti, hβ1, hβ0, hβpos, hβK⟩ :=
    exists_contDiff_antitone_cutoff_mul_abs_deriv_le_deriv_deriv (a := 1 / 2) (b := 1)
      (by norm_num)
  have hβ'c : Continuous (deriv β) := hβ.continuous_deriv (by simp)
  have hβ'zero {r : ℝ} (hr : r ≤ 1 / 2 ∨ 1 ≤ r) : deriv β r = 0 :=
    hr.elim
      (fun h ↦ IsLocalMax.deriv_eq_zero (.of_forall fun u ↦ (hβI u).2.trans_eq (hβ1 h).symm))
      fun h ↦ IsLocalMin.deriv_eq_zero (.of_forall fun u ↦ (hβ0 h).trans_le (hβI u).1)
  obtain ⟨B, hB, hβB⟩ : ∃ B : ℝ, 0 < B ∧ ∀ r ∈ Icc (0 : ℝ) 1, |deriv β r| ≤ B := by
    obtain ⟨B₀, hB₀⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
      hβ'c.continuousOn
    exact ⟨max B₀ 1, one_pos.trans_le (le_max_right _ _),
      fun r hr ↦ (hB₀ r hr).trans (le_max_left _ _)⟩
  choose s hs0 _ hsK using fun n : ℕ ↦ hβK ((C n + 1) / (ε n / 2))
  -- The lower bound `L` for `Λ'' / Λ'`, constant on the intervals `(n - 1, n]`.
  obtain ⟨D, hD⟩ : ∃ D : ℕ → ℝ, ∀ n, D n = β (1 - s n) * ε n / (2 * B * (n + 1)) :=
    ⟨_, fun _ ↦ rfl⟩
  have hDpos (n : ℕ) : 0 < D n := by
    have := hβpos (1 - s n) (by linarith [hs0 n])
    have := hε0 n
    rw [hD]; positivity
  obtain ⟨L, hL⟩ : ∃ L : ℝ → ℝ, ∀ t, L t =
      max ((C ⌈t⌉₊ + 1) / (ε ⌈t⌉₊ / 2)) ((C ⌈t⌉₊ + 1) / D ⌈t⌉₊) := ⟨_, fun _ ↦ rfl⟩
  have hLbdd (c d : ℝ) : BddAbove (L '' Icc c d) := by
    refine (((finite_Iic ⌈d⌉₊).image fun n : ℕ ↦
      max ((C n + 1) / (ε n / 2)) ((C n + 1) / D n)).bddAbove).mono ?_
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨⌈t⌉₊, Nat.ceil_mono ht.2, (hL t).symm⟩
  -- The profile `Λ`.
  obtain ⟨Λ, hΛ, hΛ0, hΛnn, hΛ'pos, hΛ'', hΛ'A, hΛle⟩ :=
    exists_contDiff_profile (t₀ := -3 / 4) (b := -1 / 2) (A := |C₁| + 1) (by norm_num) hLbdd
  have hΛ'zero {t : ℝ} (h : t ≤ -3 / 4) : deriv Λ t = 0 :=
    IsLocalMin.deriv_eq_zero (.of_forall fun u ↦ (hΛ0 h).trans_le (hΛnn u))
  have hΛ'nn (t : ℝ) : 0 ≤ deriv Λ t := by
    rcases le_or_gt t (-3 / 4) with h | h
    · rw [hΛ'zero h]
    · exact (hΛ'pos t h).le
  -- The modification `μ`.
  have hβnear : β =ᶠ[𝓝 0] fun _ ↦ β 0 :=
    eventually_of_mem (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)) fun r hr ↦
      (hβ1 (le_of_lt hr)).trans (hβ1 (by norm_num : (0 : ℝ) ≤ 1 / 2)).symm
  have hg : ContDiff ℝ ∞ fun z : V ↦ β ‖z‖ := hβ.comp_norm_of_eventuallyEq_const hβnear
  have hgnear : (fun z : V ↦ β ‖z‖) =ᶠ[𝓝 0] fun _ ↦ β 0 := by
    exact (tendsto_norm_zero (E := V)).eventually hβnear
  set μ : ℝ × V → ℝ := fun x ↦ β ‖x.2‖ * Λ x.1
  have hμ : ContDiff ℝ ∞ μ := (hg.comp contDiff_snd).mul (hΛ.comp contDiff_fst)
  refine ⟨μ, hμ, fun x ↦ mul_nonneg (hβI _).1 (hΛnn _), ?_, ?_⟩
  · refine (closure_minimal (fun x hx ↦ ?_) (isClosed_Ici.prod isClosed_closedBall)).trans
      (prod_mono (Ici_subset_Ici.2 (by norm_num : (-1 : ℝ) ≤ -3 / 4)) subset_rfl)
    obtain ⟨hx1, hx2⟩ := mul_ne_zero_iff.1 hx
    refine ⟨le_of_not_gt fun h ↦ hx2 (hΛ0 (le_of_lt h)), mem_closedBall_zero_iff.2 ?_⟩
    exact le_of_not_gt fun h ↦ hx1 (hβ0 (le_of_lt h))
  rintro ⟨t, y⟩ hcr ⟨ht, hy⟩
  rw [mem_Ici] at ht
  rw [mem_closedBall_zero_iff] at hy
  -- The derivatives of `f + μ` and of `μ` at `(t, y)`.
  have hDμ : ContDiff ℝ ∞ (fderiv ℝ μ) := hμ.fderiv_right (by simp)
  have hFD : fderiv ℝ (f + μ) = fderiv ℝ f + fderiv ℝ μ :=
    funext fun z ↦ fderiv_add (hf.differentiable (by simp) z) (hμ.differentiable (by simp) z)
  have hHess (v : ℝ × V) : fderiv ℝ (fderiv ℝ (f + μ)) (t, y) v v =
      fderiv ℝ (fderiv ℝ f) (t, y) v v + fderiv ℝ (fderiv ℝ μ) (t, y) v v := by
    rw [hFD, fderiv_add (hDf.differentiable (by simp) _) (hDμ.differentiable (by simp) _)]
    simp
  have hcrv (v : ℝ × V) : fderiv ℝ f (t, y) v = -fderiv ℝ μ (t, y) v := by
    have := congrArg (fun T ↦ T v) hcr
    simp only [hFD, Pi.add_apply, add_apply, zero_apply] at this
    linarith
  have hg2 : ContDiffAt ℝ 2 (fun z : V ↦ β ‖z‖) y := hg.contDiffAt.of_le h2
  have hΛ2 : ContDiffAt ℝ 2 Λ t := hΛ.contDiffAt.of_le h2
  have hμt : fderiv ℝ μ (t, y) (1, 0) = β ‖y‖ * deriv Λ t :=
    fderiv_comp_snd_mul_comp_fst_apply_one_zero (g := fun z : V ↦ β ‖z‖)
      (hg.differentiable (by simp) y) (hΛ.differentiable (by simp) t)
  have hμtt : fderiv ℝ (fderiv ℝ μ) (t, y) (1, 0) (1, 0) = β ‖y‖ * deriv (deriv Λ) t :=
    fderiv_fderiv_comp_snd_mul_comp_fst_apply_one_zero (g := fun z : V ↦ β ‖z‖) hg2 hΛ2
  have hμy (v : V) : fderiv ℝ μ (t, y) (0, v) = Λ t * fderiv ℝ (fun z : V ↦ β ‖z‖) y v :=
    fderiv_comp_snd_mul_comp_fst_apply_zero_mk (g := fun z : V ↦ β ‖z‖)
      (hg.differentiable (by simp) y) (hΛ.differentiable (by simp) t) v
  have hμyy (v : V) : fderiv ℝ (fderiv ℝ μ) (t, y) (0, v) (0, v) =
      Λ t * fderiv ℝ (fderiv ℝ fun z : V ↦ β ‖z‖) y v v :=
    fderiv_fderiv_comp_snd_mul_comp_fst_apply_zero_mk (g := fun z : V ↦ β ‖z‖) hg2 hΛ2 v v
  -- The bounds at `(t, y)`.
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = ⌈t⌉₊ := ⟨_, rfl⟩
  have hxK : (t, y) ∈ Icc (-1) (n : ℝ) ×ˢ closedBall (0 : V) 1 :=
    ⟨⟨ht, hn ▸ Nat.le_ceil t⟩, mem_closedBall_zero_iff.2 hy⟩
  have hHf (v : ℝ × V) (hv : ‖v‖ = 1) : -C n ≤ fderiv ℝ (fderiv ℝ f) (t, y) v v :=
    hC n _ hxK v hv
  have hLt : L t = max ((C n + 1) / (ε n / 2)) ((C n + 1) / D n) := by rw [hL t, ← hn]
  have hM1 : (C n + 1) / (ε n / 2) ≤ max (L t) 0 :=
    ((le_max_left _ _).trans_eq hLt.symm).trans (le_max_left _ _)
  have hM2 : (C n + 1) / D n ≤ max (L t) 0 :=
    ((le_max_right _ _).trans_eq hLt.symm).trans (le_max_left _ _)
  have hgI := hβI ‖y‖
  have hCn : 0 < C n + 1 := by linarith [hC0 n]
  -- Positivity of the Hessian along `(1, 0)` once `β Λ'` is bounded below suitably.
  have hpos_t {X : ℝ} (htt : -3 / 4 < t) (hX : 0 < X) (hβΛ : X ≤ β ‖y‖ * deriv Λ t)
      (hcX : (C n + 1) / X ≤ max (L t) 0) :
      0 < fderiv ℝ (fderiv ℝ (f + μ)) (t, y) (1, 0) (1, 0) := by
    rw [hHess, hμtt]
    have h1 := hHf (1, 0) (by simp)
    have h3 : max (L t) 0 * (β ‖y‖ * deriv Λ t) ≤ β ‖y‖ * deriv (deriv Λ) t := by
      rw [mul_left_comm]
      exact mul_le_mul_of_nonneg_left (hΛ'' t htt) hgI.1
    linarith [le_mul_of_div_le hCn hX hβΛ hcX]
  by_cases hU : (t, y) ∈ Ioo (-(1 / 2) : ℝ) (1 / 2) ×ˢ ball (0 : V) (1 / 2)
  · -- In the box there is no critical point: `Λ'` exceeds the `t`-derivative of `f`.
    exfalso
    obtain ⟨⟨ht1, ht2⟩, hy2⟩ := hU
    have hy2' : ‖y‖ < 1 / 2 := mem_ball_zero_iff.1 hy2
    have hmv : ‖fderiv ℝ f (t, y) (1, 0) - fderiv ℝ f 0 (1, 0)‖ ≤ C₁ * ‖(t, y) - 0‖ :=
      Convex.norm_image_sub_le_of_norm_fderiv_le (f := fun x ↦ fderiv ℝ f x (1, 0))
        (fun z _ ↦ hg₁.differentiable (by simp) z)
        (fun z hz ↦ hC₁ z (hUK hz)) ((convex_Ioo _ _).prod (convex_ball _ _)) h0U
        ⟨⟨ht1, ht2⟩, hy2⟩
    rw [h0.fderiv_eq_zero, zero_apply, sub_zero, sub_zero,
      Real.norm_eq_abs, hcrv, hμt, hβ1 hy2'.le, Pi.one_apply, one_mul, abs_neg,
      abs_of_nonneg (hΛ'nn t)] at hmv
    have hxn : ‖((t, y) : ℝ × V)‖ ≤ 1 / 2 :=
      max_le (by rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith) hy2'.le
    have := hΛ'A t (by linarith)
    linarith [mul_le_mul_of_nonneg_right (le_abs_self C₁) (norm_nonneg ((t, y) : ℝ × V)),
      mul_le_mul_of_nonneg_left hxn (abs_nonneg C₁), abs_nonneg C₁]
  have hεx := hε n (t, y) ⟨hxK, hU⟩
  rw [hcrv, hμt, abs_neg, abs_of_nonneg (mul_nonneg hgI.1 (hΛ'nn t))] at hεx
  by_cases hpε : ε n / 2 ≤ β ‖y‖ * deriv Λ t
  · -- The `t`-derivative of `f` is large: the Hessian is positive along `(1, 0)`.
    refine ⟨(1, 0), hpos_t (lt_of_not_ge fun h ↦ ?_) (half_pos (hε0 n)) hpε hM1⟩
    rw [hΛ'zero h, mul_zero] at hpε
    linarith [hε0 n]
  rw [not_le] at hpε
  -- Otherwise the radial derivative of `f` is large.
  have hq : ‖(fderiv ℝ f (t, y)).comp (ContinuousLinearMap.inr ℝ ℝ V)‖ ≤
      Λ t * |deriv β ‖y‖| := by
    refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (hΛnn t) (abs_nonneg _))
      fun v ↦ ?_
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply, hcrv, hμy, norm_neg,
      norm_mul, Real.norm_of_nonneg (hΛnn t), mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (hΛnn t)
    rcases eq_or_ne y 0 with rfl | hy0
    · rw [hgnear.fderiv_eq]
      simp only [fderiv_fun_const, Pi.zero_apply, zero_apply, norm_zero]
      positivity
    · rw [fderiv_comp_norm_apply hy0 (hβ.differentiable (by simp) _) v, smul_eq_mul, norm_mul,
        Real.norm_eq_abs, Real.norm_eq_abs, mul_comm, abs_div, abs_norm]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      rw [div_le_iff₀ (norm_pos_iff.2 hy0), mul_comm]
      exact abs_real_inner_le_norm y v
  have hq2 : ε n / 2 < Λ t * |deriv β ‖y‖| := by linarith
  have hε2 := half_pos (hε0 n)
  have hβ'ne : deriv β ‖y‖ ≠ 0 := fun h ↦ by
    rw [h, abs_zero, mul_zero] at hq2
    linarith
  have hΛpos : 0 < Λ t := lt_of_le_of_ne (hΛnn t) fun h ↦ by
    rw [← h, zero_mul] at hq2
    linarith
  have hy12 : 1 / 2 < ‖y‖ := lt_of_not_ge fun h ↦ hβ'ne (hβ'zero (Or.inl h))
  have hy1 : ‖y‖ < 1 := lt_of_le_of_ne hy fun h ↦ hβ'ne (hβ'zero (Or.inr h.ge))
  have hy0 : y ≠ 0 := by
    rintro rfl
    norm_num at hy12
  have htt : -3 / 4 < t := lt_of_not_ge fun h ↦ hΛpos.ne' (hΛ0 h)
  have hΛB : ε n / 2 < Λ t * B :=
    hq2.trans_le (mul_le_mul_of_nonneg_left (hβB _ ⟨norm_nonneg _, hy⟩) (hΛnn t))
  by_cases hys : 1 - s n ≤ ‖y‖
  · -- Near the boundary sphere `β''` dominates: the Hessian is positive radially.
    refine ⟨(0, ‖y‖⁻¹ • y), ?_⟩
    rw [hHess, hμyy, fderiv_fderiv_comp_norm_apply_inv_norm_smul hy0 (hβ.contDiffAt.of_le h2)]
    have h1 := hHf (0, ‖y‖⁻¹ • y) (by simp [norm_smul, hy0])
    have h4 : (C n + 1) / (ε n / 2) * (Λ t * |deriv β ‖y‖|) ≤
        Λ t * deriv (deriv β) ‖y‖ := by
      rw [mul_left_comm]
      exact mul_le_mul_of_nonneg_left (hsK n ‖y‖ ⟨hys, hy1⟩) (hΛnn t)
    linarith [le_mul_of_div_le hCn hε2 hq2.le le_rfl]
  · -- Further in, `β` is bounded below and `Λ' ≥ Λ / (t + 3/4)`: positive along `(1, 0)`.
    rw [not_le] at hys
    refine ⟨(1, 0), hpos_t htt (hDpos n) ?_ hM2⟩
    have hΛ' : ε n / (2 * B * (n + 1)) ≤ deriv Λ t := by
      have htn : t - -3 / 4 ≤ n + 1 := by linarith [hn ▸ Nat.le_ceil t]
      have a1 := mul_le_mul_of_nonneg_right (hΛle t htt) hB.le
      have a2 := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right htn (hΛ'nn t)) hB.le
      rw [div_le_iff₀ (by positivity)]
      linarith
    calc D n = β (1 - s n) * (ε n / (2 * B * (n + 1))) := by rw [hD]; ring
      _ ≤ β ‖y‖ * deriv Λ t :=
        mul_le_mul (hβanti hys.le) hΛ' (by have := hε0 n; positivity) hgI.1

end SymplecticGeometry

end
