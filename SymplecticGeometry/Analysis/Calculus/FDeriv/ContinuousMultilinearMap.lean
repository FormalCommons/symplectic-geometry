/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# Derivatives of a varying multilinear map evaluated on the diagonal

For a map `R` into continuous `n`-multilinear maps and a map `y`, both differentiable at `x`,
`HasFDerivAt.norm_fderiv_continuousMultilinearMap_apply_le` bounds the derivative of
`x ↦ R x (y x, …, y x)` at `x` by `‖R'‖ ‖y x‖ ^ n + n ‖R x‖ ‖y x‖ ^ (n - 1) ‖y'‖`, where `R'`
and `y'` are the derivatives of `R` and `y`. It is the norm estimate that goes with Mathlib's
`HasFDerivAt.continuousMultilinearMap_apply`, which gives the derivative itself: the first term
comes from the derivative of `R`, and the other `n` from that of `y` in each of the slots.
-/

public section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {X E F : Type*} [NormedAddCommGroup X]
  [NormedSpace 𝕜 X] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] {n : ℕ}

/-- If `R : X → E [×n]→L[𝕜] F` and `y : X → E` have derivatives `R'` and `y'` at `x`, then the
derivative of `x ↦ R x (y x, …, y x)` at `x` has norm at most
`‖R'‖ ‖y x‖ ^ n + n ‖R x‖ ‖y x‖ ^ (n - 1) ‖y'‖`. -/
theorem HasFDerivAt.norm_fderiv_continuousMultilinearMap_apply_le
    {R : X → ContinuousMultilinearMap 𝕜 (fun _ : Fin n ↦ E) F}
    {R' : X →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin n ↦ E) F} {y : X → E} {y' : X →L[𝕜] E}
    {x : X} (hR : HasFDerivAt R R' x) (hy : HasFDerivAt y y' x) :
    ‖fderiv 𝕜 (fun x ↦ R x fun _ ↦ y x) x‖ ≤
      ‖R'‖ * ‖y x‖ ^ n + n * (‖R x‖ * ‖y x‖ ^ (n - 1) * ‖y'‖) := by
  rw [(hR.continuousMultilinearMap_apply fun _ ↦ hy).fderiv]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h ↦ ?_
  simp only [add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousMultilinearMap.apply_apply, FunLike.coe_sum, Finset.sum_apply,
    ContinuousMultilinearMap.toContinuousLinearMap_apply]
  refine (norm_add_le _ _).trans ?_
  rw [add_mul]
  gcongr
  · calc ‖R' h fun _ ↦ y x‖ ≤ ‖R' h‖ * ∏ _ : Fin n, ‖y x‖ := (R' h).le_opNorm _
      _ ≤ ‖R'‖ * ‖h‖ * ‖y x‖ ^ n := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          gcongr
          exact R'.le_opNorm h
      _ = _ := by ring
  · calc ‖∑ i, R x (Function.update (fun _ ↦ y x) i (y' h))‖
        ≤ ∑ i, ‖R x (Function.update (fun _ ↦ y x) i (y' h))‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin n, ‖R x‖ * ‖y x‖ ^ (n - 1) * ‖y'‖ * ‖h‖ := by
          refine Finset.sum_le_sum fun i _ ↦ ((R x).le_opNorm _).trans ?_
          rw [show (fun j ↦ ‖Function.update (fun _ ↦ y x) i (y' h) j‖) =
              Function.update (fun _ ↦ ‖y x‖) i ‖y' h‖ from
                funext fun j ↦ Function.apply_update (fun _ ↦ norm) _ i _ j,
            Finset.prod_update_of_mem (Finset.mem_univ i), Finset.prod_const,
            Finset.card_sdiff_of_subset (by simp), Finset.card_univ, Fintype.card_fin,
            Finset.card_singleton]
          have := y'.le_opNorm h
          calc ‖R x‖ * (‖y' h‖ * ‖y x‖ ^ (n - 1))
              ≤ ‖R x‖ * ((‖y'‖ * ‖h‖) * ‖y x‖ ^ (n - 1)) := by gcongr
            _ = _ := by ring
      _ = n * (‖R x‖ * ‖y x‖ ^ (n - 1) * ‖y'‖) * ‖h‖ := by simp; ring

end
