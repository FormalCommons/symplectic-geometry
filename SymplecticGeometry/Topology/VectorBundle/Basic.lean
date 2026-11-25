/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.VectorBundle.Trivialization

/-!
# Linear trivializations and scaling in the fibre

Facts about the linear trivializations of a vector bundle, complementing Mathlib's
`Mathlib/Topology/VectorBundle/Basic.lean` and Tau Ceti's
`TauCeti/Topology/VectorBundle/Trivialization.lean`.

## Main results

* `Bundle.Trivialization.symm_smul_snd`: for a linear trivialization `e` and a point `y` over its
  base set, `e.symm y.proj (c • (e y).2) = c • y.snd`.
* `Bundle.Trivialization.isLinear_restrOpen`: the restriction of a linear trivialization to an
  open set (Mathlib's `Bundle.Trivialization.restrOpen`) is linear.
-/

public section

namespace Bundle.Trivialization

variable {R B F : Type*} {E : B → Type*} [Semiring R] [TopologicalSpace F] [TopologicalSpace B]
  [AddCommMonoid F] [Module R F] [∀ b, AddCommMonoid (E b)] [∀ b, Module R (E b)]
  [TopologicalSpace (TotalSpace F E)]

/-- For a linear trivialization `e` and a point `y` over its base set, the point of the fibre of
`y` with fibre coordinate `c` times that of `y` is `c • y`. -/
theorem symm_smul_snd (e : Trivialization F (π F E)) [e.IsLinear R] {y : TotalSpace F E}
    (hy : y.proj ∈ e.baseSet) (c : R) : e.symm y.proj (c • (e y).2) = c • y.snd := by
  rw [e.symm_apply_smul hy, e.symm_proj_apply y hy]

/-- The restriction of an `R`-linear trivialization to an open set is `R`-linear. -/
instance isLinear_restrOpen (e : Trivialization F (π F E)) [e.IsLinear R] (s : Set B)
    (hs : IsOpen s) : (e.restrOpen s hs).IsLinear R where
  linear _ hb := e.linear R hb.1

end Bundle.Trivialization

end
