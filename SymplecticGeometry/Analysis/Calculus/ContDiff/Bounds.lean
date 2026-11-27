/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Bounds on iterated derivatives of `L ∘ f` from a pointwise bound on `L`

Mathlib's `ContinuousLinearMap.norm_iteratedFDerivWithin_comp_left` and
`ContinuousLinearMap.norm_iteratedFDeriv_comp_left` bound the iterated derivatives of `L ∘ f`, for
a continuous linear map `L : F →L[𝕜] G`, by `‖L‖` times those of `f`. This file states the same
bounds with a constant `C ≥ 0` such that `‖L y‖ ≤ C * ‖y‖` for all `y` in place of `‖L‖`:
`ContinuousLinearMap.norm_iteratedFDerivWithin_comp_left_le_of_forall_norm_le` and
`ContinuousLinearMap.norm_iteratedFDeriv_comp_left_le_of_forall_norm_le`. The hypothesis never
mentions the norm of `F →L[𝕜] G`, which is useful when `F` and `G` are themselves spaces of
continuous linear maps, where Lean may fail to find the instance for that norm.
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

end
