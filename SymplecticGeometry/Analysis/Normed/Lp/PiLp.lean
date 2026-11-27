/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Normed.Lp.PiLp.Basic

/-!
# `Lᵖ` products

Mathlib's `LinearIsometryEquiv.piLpCongrLeft p 𝕜 E e` moves the coordinates of `Lᵖ(ι, E)` along an
equivalence `e : ι ≃ ι'`. Tau Ceti shows that the identity of `ι` gives the identity
(`LinearIsometryEquiv.piLpCongrLeft_refl`). This file adds the matching statement for
composition.

## Main results

* `LinearIsometryEquiv.piLpCongrLeft_trans`: reindexing along `e` and then along `f` is
  reindexing along `e.trans f`.
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

end
