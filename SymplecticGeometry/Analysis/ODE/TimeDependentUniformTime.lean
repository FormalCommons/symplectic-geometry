/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.ODE.ExistUnique

/-!
# Local solutions of a time-dependent equation on a uniform time interval

Let `W : E → (V →L[ℝ] E)` be `C¹` at `x₀` and let `ξ : ℝ → V` be continuous. This file shows that
the time-dependent equation `y' = W y (ξ t)` has, for every initial time `t₀` in a compact
interval `[a, b]`, a solution with `y t₀ = x₀` on `(t₀ - ε, t₀ + ε)`, for one `ε > 0` that does
not depend on `t₀`, and that these solutions stay in any given neighbourhood of `x₀`.

`W` is Lipschitz and bounded on a small closed ball around `x₀`, and `ξ` is bounded on
`[a - 1, b + 1]`, so the field satisfies the hypotheses of Mathlib's Picard–Lindelöf theorem
(`IsPicardLindelof`) on that ball, with constants that do not depend on `t₀`. The proof takes the
solution as a fixed point of the Picard iteration, as Mathlib's
`IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt` does, to keep it in the ball.
Tau Ceti's `ContDiffAt.exists_forall_mem_ball_exists_eq_forall_mem_Ioo_hasDerivAt_and_mem` is the
autonomous counterpart, for a field `y ↦ g y` that does not depend on time.

## Main results

* `ContDiffAt.exists_pos_forall_mem_Icc_exists_eq_forall_mem_Ioo_hasDerivAt_and_mem`: the uniform
  local existence above.
-/

public section

open Set Metric
open scoped NNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- If `W : E → (V →L[ℝ] E)` is `C¹` at `x₀` and `ξ : ℝ → V` is continuous, then for every compact
interval `[a, b]` and every neighbourhood `s` of `x₀` there is `ε > 0` such that, for each
`t₀ ∈ [a, b]`, the equation `y' = W y (ξ t)` has a solution `y` with `y t₀ = x₀` that stays in `s`
on `(t₀ - ε, t₀ + ε)`. -/
theorem ContDiffAt.exists_pos_forall_mem_Icc_exists_eq_forall_mem_Ioo_hasDerivAt_and_mem
    {W : E → V →L[ℝ] E} {x₀ : E} (hW : ContDiffAt ℝ 1 W x₀) {ξ : ℝ → V} (hξ : Continuous ξ)
    (a b : ℝ) {s : Set E} (hs : s ∈ 𝓝 x₀) :
    ∃ ε > 0, ∀ t₀ ∈ Icc a b, ∃ y : ℝ → E, y t₀ = x₀ ∧
      ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt y (W (y t) (ξ t)) t ∧ y t ∈ s := by
  obtain ⟨K, U, hU, hK⟩ := hW.exists_lipschitzOnWith
  have hWx₀ : ∀ᶠ y in 𝓝 x₀, ‖W y‖ ≤ ‖W x₀‖ + 1 :=
    (hW.continuousAt.norm.eventually (gt_mem_nhds (lt_add_one ‖W x₀‖))).mono fun _ h ↦ h.le
  obtain ⟨ρ, hρ, hρU⟩ := nhds_basis_closedBall.mem_iff.mp
    (Filter.inter_mem (Filter.inter_mem hU hWx₀) hs)
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := a - 1) (b := b + 1)).exists_bound_of_continuousOn
    hξ.continuousOn
  let B₀ : ℝ≥0 := ⟨max B 0, le_max_right _ _⟩
  let M₀ : ℝ≥0 := ⟨‖W x₀‖ + 1, by positivity⟩
  let L : ℝ≥0 := M₀ * B₀ + 1
  have hL : (0 : ℝ) < L := by positivity
  refine ⟨min 1 (ρ / L), lt_min one_pos (div_pos hρ hL), fun t₀ ht₀ ↦ ?_⟩
  set ε := min 1 (ρ / L)
  have hε : 0 < ε := lt_min one_pos (div_pos hρ hL)
  let t₀' : Icc (t₀ - ε) (t₀ + ε) := ⟨t₀, by constructor <;> linarith⟩
  have hBt : ∀ t ∈ Icc (t₀ - ε) (t₀ + ε), ‖ξ t‖ ≤ B₀ := fun t ht ↦
    (hB t ⟨by linarith [ht.1, ht₀.1, min_le_left 1 (ρ / L)],
      by linarith [ht.2, ht₀.2, min_le_left 1 (ρ / L)]⟩).trans (le_max_left _ _)
  let ρ₀ : ℝ≥0 := ⟨ρ, hρ.le⟩
  have hPL : IsPicardLindelof (fun t y ↦ W y (ξ t)) t₀' x₀ ρ₀ 0 L (K * B₀) := by
    refine ⟨fun t ht ↦ LipschitzOnWith.of_dist_le_mul fun y hy y' hy' ↦ ?_, fun y _ ↦
      ((W y).continuous.comp hξ).continuousOn, fun t ht y hy ↦ ?_, ?_⟩
    · rw [dist_eq_norm, ← sub_apply]
      calc ‖(W y - W y') (ξ t)‖ ≤ ‖W y - W y'‖ * ‖ξ t‖ := (W y - W y').le_opNorm _
        _ ≤ (K * dist y y') * B₀ := by
          rw [← dist_eq_norm]
          exact mul_le_mul (hK.dist_le_mul y (hρU hy).1.1 y' (hρU hy').1.1) (hBt t ht)
            (norm_nonneg _) (by positivity)
        _ = ↑(K * B₀) * dist y y' := by push_cast; ring
    · calc ‖W y (ξ t)‖ ≤ ‖W y‖ * ‖ξ t‖ := (W y).le_opNorm _
        _ ≤ M₀ * B₀ := mul_le_mul (hρU hy).1.2 (hBt t ht) (norm_nonneg _) (by positivity)
        _ ≤ L := by simp [L]
    · have hmax : max (t₀ + ε - t₀) (t₀ - (t₀ - ε)) = ε := by simp
      simp only [t₀', hmax, ρ₀, NNReal.coe_zero, sub_zero]
      calc (L : ℝ) * ε ≤ L * (ρ / L) := by gcongr; exact min_le_right _ _
        _ = ρ := mul_div_cancel₀ _ hL.ne'
  -- As in `IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt`, the solution is a fixed
  -- point of the Picard iteration, which keeps it in the closed ball.
  obtain ⟨α, hα⟩ := ODE.FunSpace.exists_isFixedPt_next hPL (mem_closedBall_self (by simp))
  have hα₀ : α.compProj t₀ = x₀ := by
    rw [ODE.FunSpace.compProj_val (t := t₀')]
    exact α.apply_of_zero
  refine ⟨α.compProj, hα₀,
    fun t ht ↦ ⟨?_, (hρU (α.compProj_mem_closedBall hPL.mul_max_le)).2⟩⟩
  have ht' : t ∈ Icc (t₀ - ε) (t₀ + ε) := Ioo_subset_Icc_self ht
  refine (ODE.hasDerivWithinAt_picard_Icc t₀'.property hPL.continuousOn_uncurry
    α.continuous_compProj.continuousOn (fun _ _ ↦ α.compProj_mem_closedBall hPL.mul_max_le) x₀ ht'
    |>.congr_of_mem (fun t' ht' ↦ ?_) ht').hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  nth_rw 1 [← hα]
  rw [ODE.FunSpace.compProj_of_mem ht', ODE.FunSpace.next_apply]

end
