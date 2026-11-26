/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Algebra.Support
import SymplecticGeometry.Analysis.Calculus.ConvexProfile
import SymplecticGeometry.Analysis.Calculus.FDeriv.Prod
import SymplecticGeometry.Analysis.Calculus.FDeriv.Radial
import SymplecticGeometry.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Analysis.Calculus.Morse.Index

/-!
# Removing critical points of top index on a half-cylinder

Let `V` be a finite-dimensional real inner product space and
`S = [-1, ∞) × closedBall 0 1 ⊆ ℝ × V`. For a `C²` function `f : ℝ × V → ℝ` with no critical
point in `S` other than `0`, we construct a smooth `μ ≥ 0` supported in `S` such that at
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

At a critical point of `f + μ`: in the box, the `t`-derivative of `μ` exceeds a bound for that
of `f` on `[-1, 1] × closedBall 0 1`, so there is none; elsewhere either the `t`-derivative of
`f` is large, and the Hessian is positive along `(1, 0)` because `Λ''` dominates `Λ'`; or the
radial derivative of `f` is large, and the Hessian is positive along the radial unit vector (where
`β''` dominates `β'`), or again along `(1, 0)` (where `β` is bounded below and `Λ'` is bounded
below by `Λ / (t + 3/4)`). This last case analysis is a statement about real numbers.

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

/-- The bounds on the compact piece `[-1, n] × closedBall 0 1`: a lower bound `-C` for the Hessian
of `f` on unit vectors, and a positive lower bound `ε` for `|∂_t f| + ‖∂_y f‖` outside the box
`(-1/2, 1/2) × ball 0 (1/2)`. -/
private lemma exists_bounds {f : ℝ × V → ℝ} (hf : ContDiff ℝ 2 f)
    (hcrit : ∀ x ∈ Set.Ici (-1 : ℝ) ×ˢ Metric.closedBall (0 : V) 1, fderiv ℝ f x = 0 → x = 0)
    (n : ℕ) : ∃ C ε : ℝ, 0 ≤ C ∧ 0 < ε ∧
      (∀ x ∈ Icc (-1) (n : ℝ) ×ˢ closedBall (0 : V) 1,
        ∀ v : ℝ × V, ‖v‖ = 1 → -C ≤ fderiv ℝ (fderiv ℝ f) x v v) ∧
      ∀ x ∈ Icc (-1) (n : ℝ) ×ˢ closedBall (0 : V) 1 \
        Ioo (-(1 / 2) : ℝ) (1 / 2) ×ˢ ball (0 : V) (1 / 2),
        ε ≤ |fderiv ℝ f x (1, 0)| + ‖(fderiv ℝ f x).comp (ContinuousLinearMap.inr ℝ ℝ V)‖ := by
  have hDf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hDfc : Continuous (fderiv ℝ f) := hDf.continuous
  have hK : IsCompact (Icc (-1) (n : ℝ) ×ˢ closedBall (0 : V) 1) :=
    isCompact_Icc.prod (isCompact_closedBall 0 1)
  obtain ⟨C, hC⟩ := (hK.prod (isCompact_sphere (0 : ℝ × V) 1)).exists_bound_of_continuousOn
    ((((hDf.continuous_fderiv (by simp)).comp continuous_fst).clm_apply continuous_snd).clm_apply
      continuous_snd).continuousOn
  have hUo : IsOpen (Ioo (-(1 / 2) : ℝ) (1 / 2) ×ˢ ball (0 : V) (1 / 2)) :=
    isOpen_Ioo.prod isOpen_ball
  obtain ⟨ε, hε0, hε⟩ := (hK.diff hUo).exists_forall_le'
    (((hDfc.clm_apply continuous_const).abs).add
      (hDfc.clm_comp continuous_const).norm).continuousOn fun x hx ↦ by
    have hp := abs_nonneg (fderiv ℝ f x (1, 0))
    have hq := norm_nonneg ((fderiv ℝ f x).comp (ContinuousLinearMap.inr ℝ ℝ V))
    refine lt_of_le_of_ne (add_nonneg hp hq) fun h ↦ hx.2 ?_
    simp only [Pi.add_apply] at h
    have hx0 : x = 0 := hcrit x (prod_mono Icc_subset_Ici_self subset_rfl hx.1)
      (ContinuousLinearMap.prod_ext
        (ContinuousLinearMap.ext_ring (by simpa using abs_eq_zero.1 (by linarith : _ = (0 : ℝ))))
        (by simpa using norm_eq_zero.1 (by linarith : _ = (0 : ℝ))))
    rw [hx0]
    exact ⟨⟨by norm_num, by norm_num⟩, by simp⟩
  refine ⟨max C 0, ε, le_max_right _ _, hε0, fun x hx v hv ↦ ?_, hε⟩
  have := hC (x, v) ⟨hx, mem_sphere_zero_iff_norm.2 hv⟩
  rw [Function.comp_apply, Real.norm_eq_abs] at this
  linarith [neg_abs_le (fderiv ℝ (fderiv ℝ f) x v v), le_max_left C 0]

/-- The case analysis at a critical point `(t, y)` of `f + μ` outside the box, in terms of numbers:
`p = ∂_t f`, `q = ‖∂_y f‖`, `Htt` and `Hrr` the Hessian of `f` along `(1, 0)` and along the unit
radial vector, `r = ‖y‖`, `b, b', b''` the values of `β` and its derivatives at `r`, and
`l, l', l''` those of `Λ` at `t`. Then the Hessian of `f + μ` is positive along `(1, 0)`, or
`r > 1/2` and it is positive along the unit radial vector. -/
private lemma hessian_pos_or {C ε B b₀ N M s t r p q Htt Hrr b b' b'' l l' l'' : ℝ}
    (hC0 : 0 ≤ C) (hε : 0 < ε) (hB : 0 < B) (hb₀ : 0 < b₀) (hN : 0 < N)
    (hHtt : -C ≤ Htt) (hHrr : 1 / 2 < r → -C ≤ Hrr)
    (hεx : ε ≤ |p| + q) (hp : p = -(b * l')) (hq : q ≤ l * |b'|)
    (hb : 0 ≤ b) (hl : 0 ≤ l) (hl' : 0 ≤ l')
    (hb'0 : r ≤ 1 / 2 ∨ 1 ≤ r → b' = 0) (hr : r ≤ 1) (hb'B : |b'| ≤ B)
    (hb'' : 1 - s ≤ r → r < 1 → (C + 1) / (ε / 2) * |b'| ≤ b'')
    (hbs : r < 1 - s → b₀ ≤ b)
    (hl0 : t ≤ -3 / 4 → l = 0) (hl'0 : t ≤ -3 / 4 → l' = 0)
    (hl'' : -3 / 4 < t → M * l' ≤ l'') (hlle : -3 / 4 < t → l ≤ (t - -3 / 4) * l')
    (htN : t - -3 / 4 ≤ N)
    (hM1 : (C + 1) / (ε / 2) ≤ M) (hM2 : (C + 1) / (b₀ * (ε / (2 * B * N))) ≤ M) :
    0 < Htt + b * l'' ∨ (1 / 2 < r ∧ 0 < Hrr + l * b'') := by
  have le_mul_of_div_le {c d X K : ℝ} (hc : 0 < c) (hd : 0 < d) (hdX : d ≤ X)
      (hM : c / d ≤ K) : c ≤ K * X :=
    ((div_le_iff₀ hd).1 hM).trans
      (mul_le_mul_of_nonneg_left hdX ((div_pos hc hd).le.trans hM))
  have hCn : 0 < C + 1 := by linarith
  have hε2 : 0 < ε / 2 := half_pos hε
  -- Positivity along `(1, 0)` once `b l'` is bounded below suitably.
  have hpos_t {X : ℝ} (htt : -3 / 4 < t) (hX : 0 < X) (hbl : X ≤ b * l')
      (hcX : (C + 1) / X ≤ M) : 0 < Htt + b * l'' := by
    have h3 : M * (b * l') ≤ b * l'' := by
      rw [mul_left_comm]
      exact mul_le_mul_of_nonneg_left (hl'' htt) hb
    linarith [le_mul_of_div_le hCn hX hbl hcX]
  rw [hp, abs_neg, abs_of_nonneg (mul_nonneg hb hl')] at hεx
  by_cases hpε : ε / 2 ≤ b * l'
  · -- The `t`-derivative of `f` is large.
    refine .inl (hpos_t (lt_of_not_ge fun h ↦ ?_) hε2 hpε hM1)
    rw [hl'0 h, mul_zero] at hpε
    linarith
  rw [not_le] at hpε
  -- Otherwise the radial derivative of `f` is large.
  have hq2 : ε / 2 < l * |b'| := by linarith
  have hb'ne : b' ≠ 0 := fun h ↦ by
    rw [h, abs_zero, mul_zero] at hq2
    linarith
  have hlpos : 0 < l := lt_of_le_of_ne hl fun h ↦ by
    rw [← h, zero_mul] at hq2
    linarith
  have hr12 : 1 / 2 < r := lt_of_not_ge fun h ↦ hb'ne (hb'0 (.inl h))
  have hr1 : r < 1 := lt_of_le_of_ne hr fun h ↦ hb'ne (hb'0 (.inr h.ge))
  have htt : -3 / 4 < t := lt_of_not_ge fun h ↦ hlpos.ne' (hl0 h)
  by_cases hrs : 1 - s ≤ r
  · -- Near the boundary sphere `β''` dominates: positive radially.
    refine .inr ⟨hr12, ?_⟩
    have h4 : (C + 1) / (ε / 2) * (l * |b'|) ≤ l * b'' := by
      rw [mul_left_comm]
      exact mul_le_mul_of_nonneg_left (hb'' hrs hr1) hl
    linarith [hHrr hr12, le_mul_of_div_le hCn hε2 hq2.le le_rfl]
  · -- Further in, `b ≥ b₀` and `l' ≥ l / (t + 3/4)`: positive along `(1, 0)`.
    rw [not_le] at hrs
    refine .inl (hpos_t htt (by positivity) ?_ hM2)
    have hl'ε : ε / (2 * B * N) ≤ l' := by
      have a1 := mul_le_mul_of_nonneg_right (hlle htt) hB.le
      have a2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right htN hl') hB.le
      have a3 := mul_le_mul_of_nonneg_left hb'B hl
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    exact mul_le_mul (hbs hrs) hl'ε (by positivity) hb

/-- **Removing critical points of top index on a half-cylinder.** Let `f : ℝ × V → ℝ` be `C²`
with no critical point in `S = [-1, ∞) × closedBall 0 1` other than `0`. Then there is a smooth
`μ ≥ 0` with topological support in `S` such that at every critical point of `f + μ` in `S` the
Hessian of `f + μ` is positive on some vector. -/
theorem exists_nonneg_halfCylinder_hessian_pos {f : ℝ × V → ℝ} (hf : ContDiff ℝ 2 f)
    (hcrit : ∀ x ∈ Set.Ici (-1 : ℝ) ×ˢ Metric.closedBall (0 : V) 1, fderiv ℝ f x = 0 → x = 0) :
    ∃ μ : ℝ × V → ℝ, ContDiff ℝ ∞ μ ∧ 0 ≤ μ ∧
      tsupport μ ⊆ Set.Ici (-1) ×ˢ Metric.closedBall 0 1 ∧
      ∀ x, fderiv ℝ (f + μ) x = 0 → x ∈ Set.Ici (-1) ×ˢ Metric.closedBall 0 1 →
        ∃ v, 0 < fderiv ℝ (fderiv ℝ (f + μ)) x v v := by
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.2 le_top
  choose C ε hC0 hε0 hC hε using exists_bounds hf hcrit
  -- A bound on `∂_t f` on the piece containing the box.
  obtain ⟨C₁, hC₁⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).prod
    (isCompact_closedBall (0 : V) 1) |>.exists_bound_of_continuousOn
    (((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const).continuousOn)
  -- The radial cutoff `β`.
  obtain ⟨β, hβ, hβI, hβanti, hβ1, hβ0, hβ'1, hβ'0, hβpos, hβK⟩ :=
    exists_contDiff_antitone_cutoff_mul_abs_deriv_le_deriv_deriv (a := 1 / 2) (b := 1)
      (by norm_num)
  obtain ⟨B, hB, hβB⟩ : ∃ B : ℝ, 0 < B ∧ ∀ r ∈ Icc (0 : ℝ) 1, |deriv β r| ≤ B := by
    obtain ⟨B₀, hB₀⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
      (hβ.continuous_deriv (by simp)).continuousOn
    exact ⟨max B₀ 1, one_pos.trans_le (le_max_right _ _),
      fun r hr ↦ (hB₀ r hr).trans (le_max_left _ _)⟩
  choose s hs0 _ hsK using fun n : ℕ ↦ hβK ((C n + 1) / (ε n / 2))
  -- The lower bound `L` for `Λ'' / Λ'`, constant on the intervals `(n - 1, n]`.
  obtain ⟨D, hD⟩ : ∃ D : ℕ → ℝ, ∀ n, D n = β (1 - s n) * (ε n / (2 * B * (n + 1))) :=
    ⟨_, fun _ ↦ rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : ℝ → ℝ, ∀ t, L t =
      max ((C ⌈t⌉₊ + 1) / (ε ⌈t⌉₊ / 2)) ((C ⌈t⌉₊ + 1) / D ⌈t⌉₊) := ⟨_, fun _ ↦ rfl⟩
  have hLbdd (c d : ℝ) : BddAbove (L '' Icc c d) := by
    refine (((finite_Iic ⌈d⌉₊).image fun n : ℕ ↦
      max ((C n + 1) / (ε n / 2)) ((C n + 1) / D n)).bddAbove).mono ?_
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨⌈t⌉₊, Nat.ceil_mono ht.2, (hL t).symm⟩
  -- The profile `Λ`.
  obtain ⟨Λ, hΛ, hΛ0, hΛ'zero, hΛnn, hΛ'nn, -, hΛ'', hΛ'A, hΛle⟩ :=
    exists_contDiff_profile (t₀ := -3 / 4) (b := -1 / 2) (A := |C₁| + 1) (by norm_num) hLbdd
  -- The modification `μ`.
  have hβnear : β =ᶠ[𝓝 0] fun _ ↦ β 0 :=
    eventually_of_mem (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)) fun r hr ↦
      (hβ1 (le_of_lt hr)).trans (hβ1 (by norm_num : (0 : ℝ) ≤ 1 / 2)).symm
  have hg : ContDiff ℝ ∞ fun z : V ↦ β ‖z‖ := hβ.comp_norm_of_eventuallyEq_const hβnear
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
  have hHess (v : ℝ × V) : fderiv ℝ (fderiv ℝ (f + μ)) (t, y) v v =
      fderiv ℝ (fderiv ℝ f) (t, y) v v + fderiv ℝ (fderiv ℝ μ) (t, y) v v := by
    simpa using congr($(TauCeti.hessianQuadraticForm_add hf.contDiffAt
      (hμ.contDiffAt.of_le h2) (x := (t, y))) v)
  have hcrv (v : ℝ × V) : fderiv ℝ f (t, y) v = -fderiv ℝ μ (t, y) v := by
    have := congrArg (fun T ↦ T v) hcr
    simp only [fderiv_add (hf.differentiable (by norm_num) _) (hμ.differentiable (by simp) _),
      add_apply, zero_apply] at this
    linarith
  have hg2 : ContDiffAt ℝ 2 (fun z : V ↦ β ‖z‖) y := hg.contDiffAt.of_le h2
  have hΛ2 : ContDiffAt ℝ 2 Λ t := hΛ.contDiffAt.of_le h2
  have hμt : fderiv ℝ μ (t, y) (1, 0) = β ‖y‖ * deriv Λ t :=
    fderiv_comp_snd_mul_comp_fst_apply_one_zero (g := fun z : V ↦ β ‖z‖)
      (hg.differentiable (by simp) y) (hΛ.differentiable (by simp) t)
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = ⌈t⌉₊ := ⟨_, rfl⟩
  have hxK : (t, y) ∈ Icc (-1) (n : ℝ) ×ˢ closedBall (0 : V) 1 :=
    ⟨⟨ht, hn ▸ Nat.le_ceil t⟩, mem_closedBall_zero_iff.2 hy⟩
  by_cases hU : (t, y) ∈ Ioo (-(1 / 2) : ℝ) (1 / 2) ×ˢ ball (0 : V) (1 / 2)
  · -- In the box there is no critical point: `Λ'` exceeds the `t`-derivative of `f`.
    exfalso
    obtain ⟨⟨ht1, ht2⟩, hy2⟩ := hU
    have hb := hC₁ (t, y) ⟨⟨ht, ht2.le.trans (by norm_num)⟩, mem_closedBall_zero_iff.2 hy⟩
    rw [hcrv, hμt, hβ1 (mem_ball_zero_iff.1 hy2).le, Pi.one_apply, one_mul, norm_neg,
      Real.norm_of_nonneg (hΛ'nn t)] at hb
    linarith [hΛ'A t (by linarith [show -(1 / 2 : ℝ) < t from ht1]), le_abs_self C₁]
  -- Outside the box, the case analysis on numbers.
  -- The `y`-derivative of `f` is bounded by `Λ |β'|`.
  have hq : ‖(fderiv ℝ f (t, y)).comp (ContinuousLinearMap.inr ℝ ℝ V)‖ ≤
      Λ t * |deriv β ‖y‖| := by
    refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (hΛnn t) (abs_nonneg _))
      fun v ↦ ?_
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply, hcrv,
      fderiv_comp_snd_mul_comp_fst_apply_zero_mk (g := fun z : V ↦ β ‖z‖)
        (hg.differentiable (by simp) y) (hΛ.differentiable (by simp) t), norm_neg, norm_mul,
      Real.norm_of_nonneg (hΛnn t), mul_assoc]
    refine mul_le_mul_of_nonneg_left ((ContinuousLinearMap.le_opNorm _ v).trans ?_) (hΛnn t)
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg v)
    exact (norm_fderiv_comp_norm_le β y).trans_eq (Real.norm_eq_abs _)
  -- The case analysis on numbers.
  have hLt : L t = max ((C n + 1) / (ε n / 2)) ((C n + 1) / D n) := by rw [hL t, ← hn]
  have hM2 : (C n + 1) / (β (1 - s n) * (ε n / (2 * B * (n + 1)))) ≤ max (L t) 0 := by
    rw [← hD n]
    exact ((le_max_right _ _).trans_eq hLt.symm).trans (le_max_left _ _)
  rcases hessian_pos_or (N := n + 1) (s := s n)
    (hC0 n) (hε0 n) hB (hβpos _ (by linarith [hs0 n])) (by positivity)
    (hC n _ hxK (1, 0) (by simp))
    (fun h ↦ hC n _ hxK (0, ‖y‖⁻¹ • y) (by simp [norm_smul, (by linarith : ‖y‖ ≠ 0)]))
    (hε n _ ⟨hxK, hU⟩) (by rw [hcrv, hμt]) hq (hβI _).1 (hΛnn t) (hΛ'nn t)
    (fun h ↦ h.elim (hβ'1 ·) (hβ'0 ·)) hy
    (hβB _ ⟨norm_nonneg _, hy⟩) (fun h1 h2 ↦ hsK n _ ⟨h1, h2⟩) (fun h ↦ hβanti h.le)
    (fun h ↦ hΛ0 h) (fun h ↦ hΛ'zero h) (hΛ'' t) (hΛle t) (by linarith [hn ▸ Nat.le_ceil t])
    (((le_max_left _ _).trans_eq hLt.symm).trans (le_max_left _ _)) hM2 with h | ⟨hy12, h⟩
  · refine ⟨(1, 0), ?_⟩
    rwa [hHess, fderiv_fderiv_comp_snd_mul_comp_fst_apply_one_zero (g := fun z : V ↦ β ‖z‖)
      hg2 hΛ2]
  · have hy0 : y ≠ 0 := norm_ne_zero_iff.1 (by linarith)
    refine ⟨(0, ‖y‖⁻¹ • y), ?_⟩
    rwa [hHess, fderiv_fderiv_comp_snd_mul_comp_fst_apply_zero_mk (g := fun z : V ↦ β ‖z‖) hg2
      hΛ2, fderiv_fderiv_comp_norm_apply_inv_norm_smul hy0 (hβ.contDiffAt.of_le h2)]

end SymplecticGeometry

end
