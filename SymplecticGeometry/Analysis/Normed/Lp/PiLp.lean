/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Normed.Lp.PiLp

/-!
# `Lᵖ` products

Mathlib's `LinearIsometryEquiv.piLpCongrLeft p 𝕜 E e` moves the coordinates of `Lᵖ(ι, E)` along an
equivalence `e : ι ≃ ι'`. Tau Ceti shows that the identity of `ι` gives the identity
(`LinearIsometryEquiv.piLpCongrLeft_refl`). This file adds the matching statement for
composition, and bounds the `Lᵖ` norm by the sum of the norms of the coordinates.

## Main results

* `LinearIsometryEquiv.piLpCongrLeft_trans`: reindexing along `e` and then along `f` is
  reindexing along `e.trans f`.
* `PiLp.norm_le_sum_norm`: for `1 ≤ p`, the `Lᵖ` norm of `x` is at most `∑ i, ‖x i‖`.
-/

public section

namespace LinearIsometryEquiv

variable {p : ENNReal} [Fact (1 ≤ p)] {𝕜 E : Type*} [Semiring 𝕜] [SeminormedAddCommGroup E]
  [Module 𝕜 E] {ι ι' ι'' : Type*} [Fintype ι] [Fintype ι'] [Fintype ι'']

/-- Reindexing the coordinates of `Lᵖ(ι, E)` along `e` and then along `f` is reindexing them
along `e.trans f`. -/
@[simp]
theorem piLpCongrLeft_trans (e : ι ≃ ι') (f : ι' ≃ ι'') :
    (piLpCongrLeft p 𝕜 E e).trans (piLpCongrLeft p 𝕜 E f) = piLpCongrLeft p 𝕜 E (e.trans f) := by
  ext z i
  simp [piLpCongrLeft_apply, Equiv.piCongrLeft'_apply]

end LinearIsometryEquiv

namespace PiLp

variable {p : ENNReal} [Fact (1 ≤ p)] {ι : Type*} [Fintype ι] {β : ι → Type*}
  [∀ i, SeminormedAddCommGroup (β i)]

/-- For `1 ≤ p`, the `Lᵖ` norm of `x` is at most the sum of the norms of its coordinates. -/
theorem norm_le_sum_norm (x : PiLp p β) : ‖x‖ ≤ ∑ i, ‖x i‖ := by
  classical
  calc ‖x‖ = ‖∑ i, PiLp.single p i (x i)‖ := by rw [PiLp.univ_sum_single]
    _ ≤ ∑ i, ‖PiLp.single p i (x i)‖ := norm_sum_le _ _
    _ = ∑ i, ‖x i‖ := by simp_rw [PiLp.norm_single]

end PiLp

end
