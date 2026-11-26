/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.FiberBundle.Associated.Basic

/-!
# The preferred trivializations of an associated bundle on the preferred points

Let `P` be a principal `G`-bundle and `F` a space with a continuous action of `G`. For points `b'`
and `b` of the base, with `b` in the base set of the preferred trivialization of `P` at `b'`, let
`σ b` be the point of `P b` with coordinate `1` in that trivialization. This file shows that the
preferred trivialization of `P ×_G F` at `b'` gives the class `[σ b, v]` the coordinate `v`, so
that its inverse sends `v` to `[σ b, v]`. Both follow from Tau Ceti's
`TauCeti.AssociatedBundle.trivializationAt_mk`.

## Main results

* `TauCeti.AssociatedBundle.trivializationAt_mk_symm_one`,
  `TauCeti.AssociatedBundle.trivializationAt_symm_eq_mk`: the preferred trivialization of
  `P ×_G F` at `b'` and its inverse identify `[σ b, v]` with `v`.

## References

* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, volume I, Chapter I, §5
  (associated bundles).
-/

public section

noncomputable section

open Bundle

namespace TauCeti.AssociatedBundle

variable {B G F : Type*} [TopologicalSpace B] [Group G] [TopologicalSpace G]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]
  [TopologicalSpace F] [MulAction G F] [ContinuousSMul G F] [∀ b, Nonempty (P b)]

/-- In the preferred trivialization of `P ×_G F` at `b'`, the class `[σ b, v]` has coordinate `v`,
where `σ b` is the point of `P b` with coordinate `1` in the preferred trivialization of `P` at
`b'`. -/
theorem trivializationAt_mk_symm_one {b' b : B} (hb : b ∈ (trivializationAt G P b').baseSet)
    (v : F) :
    trivializationAt F (AssociatedBundle G P F) b'
        ⟨b, mk G ((trivializationAt G P b').symm b 1) v⟩ = (b, v) := by
  rw [trivializationAt_mk hb, (trivializationAt G P b').apply_mk_symm hb, one_smul]

/-- The inverse of the preferred trivialization of `P ×_G F` at `b'` sends `v` over `b` to the
class `[σ b, v]`, where `σ b` is the point of `P b` with coordinate `1` in the preferred
trivialization of `P` at `b'`. -/
theorem trivializationAt_symm_eq_mk [Nonempty F] {b' b : B}
    (hb : b ∈ (trivializationAt G P b').baseSet) (v : F) :
    (trivializationAt F (AssociatedBundle G P F) b').symm b v =
      mk G ((trivializationAt G P b').symm b 1) v := by
  have hb' : b ∈ (trivializationAt F (AssociatedBundle G P F) b').baseSet := by
    rwa [baseSet_trivializationAt]
  have h := (trivializationAt F (AssociatedBundle G P F) b').symm_apply_apply_mk hb'
    (mk G ((trivializationAt G P b').symm b 1) v)
  rwa [trivializationAt_mk_symm_one hb] at h

end TauCeti.AssociatedBundle

end
