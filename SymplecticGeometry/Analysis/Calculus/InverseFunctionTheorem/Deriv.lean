/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv

/-!
# Open images of `C¹` functions of one variable

* `ContDiffOn.isOpen_image_of_deriv_ne_zero`: a function `f : 𝕜 → 𝕜` that is `C¹` on an open
  set `U`, with nonzero derivative at every point of `U`, maps `U` onto an open set.

Mathlib's `isOpenMap_of_hasStrictDerivAt` gives this for `U = 𝕜`; the proof here follows it,
applying the one-dimensional inverse function theorem `HasStrictDerivAt.map_nhds_eq` at each
point of `U`.
-/

public section

open Set Filter

variable {𝕜 : Type*} [RCLike 𝕜]

/-- A function `f : 𝕜 → 𝕜` that is `C¹` on an open set `U`, with nonzero derivative at every
point of `U`, maps `U` onto an open set. -/
theorem ContDiffOn.isOpen_image_of_deriv_ne_zero {f : 𝕜 → 𝕜} {U : Set 𝕜} (hU : IsOpen U)
    (hf : ContDiffOn 𝕜 1 f U) (hf' : ∀ x ∈ U, deriv f x ≠ 0) : IsOpen (f '' U) := by
  refine isOpen_iff_mem_nhds.2 ?_
  rintro _ ⟨x, hx, rfl⟩
  rw [← ((hf.contDiffAt (hU.mem_nhds hx)).hasStrictDerivAt_deriv one_ne_zero).map_nhds_eq
    (hf' x hx)]
  exact image_mem_map (hU.mem_nhds hx)

end
