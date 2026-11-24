/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Algebra.Support
public import TauCeti.Topology.Algebra.Support

/-!
# The topological support of a function restricted to a set

Complements to Mathlib's `Mathlib/Topology/Algebra/Support.lean`.

* `mulTSupport_mulIndicator_subset_of_eqOn`, `tsupport_indicator_subset_of_eqOn`: if a function
  `f` is trivial on `U` outside a closed set `K`, then the topological support of `f` restricted
  to `U` and extended by `1` (respectively `0`) lies in `K`. This is Tau Ceti's
  `TauCeti.mulTSupport_subset_of_forall_notMem_eq_one` (respectively
  `TauCeti.tsupport_subset_of_forall_notMem_eq_zero`) applied to the restricted function.
-/

public section

namespace SymplecticGeometry

open Set Function

variable {X α : Type*} [TopologicalSpace X] [One α]

/-- If `f` equals `1` on `U \ K` and `K` is closed, then the topological support of
`U.mulIndicator f` lies in `K`. -/
@[to_additive /-- If `f` equals `0` on `U \ K` and `K` is closed, then the topological support of
`U.indicator f` lies in `K`. -/]
theorem mulTSupport_mulIndicator_subset_of_eqOn {f : X → α} {U K : Set X} (hK : IsClosed K)
    (hf : EqOn f 1 (U \ K)) : mulTSupport (U.mulIndicator f) ⊆ K :=
  TauCeti.mulTSupport_subset_of_forall_notMem_eq_one
    (fun _ hx ↦ mulIndicator_apply_eq_one.2 fun hxU ↦ hf ⟨hxU, hx⟩) hK

end SymplecticGeometry

end
