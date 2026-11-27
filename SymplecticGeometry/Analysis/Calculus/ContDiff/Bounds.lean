/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Bounds on iterated derivatives

Mathlib's `ContinuousLinearMap.norm_iteratedFDerivWithin_comp_left` and
`ContinuousLinearMap.norm_iteratedFDeriv_comp_left` bound the iterated derivatives of `L ∘ f`, for
a continuous linear map `L : F →L[𝕜] G`, by `‖L‖` times those of `f`. This file states the same
bounds with a constant `C ≥ 0` such that `‖L y‖ ≤ C * ‖y‖` for all `y` in place of `‖L‖`:
`ContinuousLinearMap.norm_iteratedFDerivWithin_comp_left_le_of_forall_norm_le` and
`ContinuousLinearMap.norm_iteratedFDeriv_comp_left_le_of_forall_norm_le`. The hypothesis never
mentions the norm of `F →L[𝕜] G`, which is useful when `F` and `G` are themselves spaces of
continuous linear maps, where Lean may fail to find the instance for that norm.

It also records that a `C^n` function has iterated derivatives of each order `≤ r ≤ n` bounded
by one constant on a compact set
(`ContDiff.exists_forall_norm_iteratedFDeriv_le_of_isCompact`).
-/

public section

open scoped ContDiff

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

namespace ContinuousLinearMap

/-- If `‖L y‖ ≤ C * ‖y‖` for all `y`, with `0 ≤ C`, then the `n`-th iterated derivative of
`L ∘ f` within `s` at `x` has norm at most `C` times that of `f`, for `f` that is `C^N` within `s`
at `x` and `n ≤ N`. -/
theorem norm_iteratedFDerivWithin_comp_left_le_of_forall_norm_le (L : F →L[𝕜] G) {C : ℝ}
    (hC : 0 ≤ C) (hL : ∀ y, ‖L y‖ ≤ C * ‖y‖) {f : E → F} {s : Set E} {x : E} {N : ℕ∞ω} {n : ℕ}
    (hf : ContDiffWithinAt 𝕜 N f s x) (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) (hn : n ≤ N) :
    ‖iteratedFDerivWithin 𝕜 n (L ∘ f) s x‖ ≤ C * ‖iteratedFDerivWithin 𝕜 n f s x‖ :=
  (L.norm_iteratedFDerivWithin_comp_left hf hs hx hn).trans <| by
    gcongr
    exact L.opNorm_le_bound hC hL

/-- If `‖L y‖ ≤ C * ‖y‖` for all `y`, with `0 ≤ C`, then the `n`-th iterated derivative of
`L ∘ f` at `x` has norm at most `C` times that of `f`, for `f` that is `C^N` at `x` and
`n ≤ N`. -/
theorem norm_iteratedFDeriv_comp_left_le_of_forall_norm_le (L : F →L[𝕜] G) {C : ℝ}
    (hC : 0 ≤ C) (hL : ∀ y, ‖L y‖ ≤ C * ‖y‖) {f : E → F} {x : E} {N : ℕ∞ω} {n : ℕ}
    (hf : ContDiffAt 𝕜 N f x) (hn : n ≤ N) :
    ‖iteratedFDeriv 𝕜 n (L ∘ f) x‖ ≤ C * ‖iteratedFDeriv 𝕜 n f x‖ :=
  (L.norm_iteratedFDeriv_comp_left hf hn).trans <| by
    gcongr
    exact L.opNorm_le_bound hC hL

end ContinuousLinearMap
/-- A `C^n` function has bounded iterated derivatives of each order `≤ r ≤ n` on a compact set:
there is one constant `M` with `‖iteratedFDeriv 𝕜 i f x‖ ≤ M` for all `x ∈ K` and `i ≤ r`. -/
theorem ContDiff.exists_forall_norm_iteratedFDeriv_le_of_isCompact {f : E → F} {n : ℕ∞ω} {r : ℕ}
    (hf : ContDiff 𝕜 n f) (hr : r ≤ n) {K : Set E} (hK : IsCompact K) :
    ∃ M, ∀ x ∈ K, ∀ i ≤ r, ‖iteratedFDeriv 𝕜 i f x‖ ≤ M := by
  have hc (i : ℕ) (hi : i ≤ r) : Continuous fun x ↦ ‖iteratedFDeriv 𝕜 i f x‖ :=
    (hf.continuous_iteratedFDeriv ((WithTop.coe_le_coe.2 (by exact_mod_cast hi)).trans hr)).norm
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
    (f := fun x ↦ ∑ i ∈ Finset.range (r + 1), ‖iteratedFDeriv 𝕜 i f x‖)
    (continuous_finsetSum _ fun i hi ↦
      hc i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))).continuousOn
  refine ⟨M, fun x hx i hi ↦ le_trans ?_ ((le_abs_self _).trans (hM x hx))⟩
  exact Finset.single_le_sum (f := fun i ↦ ‖iteratedFDeriv 𝕜 i f x‖)
    (fun _ _ ↦ norm_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hi))

end
