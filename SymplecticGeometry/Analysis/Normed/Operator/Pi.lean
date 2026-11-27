/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Operator norm of coordinate projections

For a finite family of seminormed spaces `φ i` over a nontrivially normed field, the product
`Π i, φ i` carries the sup norm, so each coordinate projection
`ContinuousLinearMap.proj i : (Π i, φ i) →L[𝕜] φ i` has operator norm at most `1`. This is the
analogue for finite Pi types of Mathlib's `ContinuousLinearMap.norm_fst_le` and
`ContinuousLinearMap.norm_snd_le` for binary products.

## Main results

* `ContinuousLinearMap.norm_proj_le`: `‖ContinuousLinearMap.proj i‖ ≤ 1`.
* `ContinuousLinearMap.coordProj`: the projection of `Π i, φ i` onto the coordinates in a
  finset `s`, with `ContinuousLinearMap.norm_coordProj_le`: `‖coordProj s‖ ≤ 1`.
-/

public section

namespace ContinuousLinearMap

variable {𝕜 ι : Type*} [NontriviallyNormedField 𝕜] {φ : ι → Type*}
  [∀ i, SeminormedAddCommGroup (φ i)] [∀ i, NormedSpace 𝕜 (φ i)]

/-- A coordinate projection of a finite product, with the sup norm, has operator norm at
most `1`. -/
theorem norm_proj_le [Fintype ι] (i : ι) : ‖proj (R := 𝕜) (φ := φ) i‖ ≤ 1 :=
  opNorm_le_bound _ zero_le_one fun v ↦ by simpa using norm_le_pi_norm v i

section coordProj

variable [DecidableEq ι]

/-- The coordinate projection of a product `Π i, φ i` onto the coordinates in `s`: it keeps the
coordinates `v i` for `i ∈ s` and sets the others to `0`. -/
def coordProj (s : Finset ι) : (Π i, φ i) →L[𝕜] Π i, φ i :=
  pi fun i ↦ if i ∈ s then proj i else 0

@[simp]
theorem coordProj_apply (s : Finset ι) (v : Π i, φ i) (i : ι) :
    coordProj (𝕜 := 𝕜) s v i = if i ∈ s then v i else 0 := by
  simp only [coordProj, pi_apply]
  split_ifs <;> simp

/-- The coordinate projection onto `s` fixes the vectors whose coordinates outside `s`
vanish. -/
theorem coordProj_apply_eq_self {s : Finset ι} {v : Π i, φ i} (hv : ∀ i ∉ s, v i = 0) :
    coordProj (𝕜 := 𝕜) s v = v := by
  ext i
  rw [coordProj_apply]
  split_ifs with h
  · rfl
  · exact (hv i h).symm

/-- The projection onto the coordinates in `s` does not increase the sup norm. -/
theorem norm_coordProj_apply_le [Fintype ι] (s : Finset ι) (v : Π i, φ i) :
    ‖coordProj (𝕜 := 𝕜) s v‖ ≤ ‖v‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg v)).2 fun i ↦ by
    rw [coordProj_apply]
    split_ifs
    · exact norm_le_pi_norm v i
    · simp

/-- The projection of a finite product, with the sup norm, onto the coordinates in `s` has
operator norm at most `1`. -/
theorem norm_coordProj_le [Fintype ι] (s : Finset ι) : ‖coordProj (𝕜 := 𝕜) (φ := φ) s‖ ≤ 1 :=
  opNorm_le_bound _ zero_le_one fun v ↦ by simpa using norm_coordProj_apply_le s v

end coordProj

end ContinuousLinearMap

end
