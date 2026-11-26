/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Topology.FiberBundle.Principal.LocalSection
public import TauCeti.Topology.FiberBundle.Associated.Basic

/-!
# The preferred trivializations of an associated bundle on the preferred local section

Let `P` be a principal `G`-bundle and `F` a space with a continuous action of `G`. For points `b'`
and `b` of the base, with `b` in the base set of the preferred trivialization of `P` at `b'`, let
`σ b = TauCeti.PrincipalBundle.localSection G P b' b` be the value at `b` of the preferred local
section of `P` at `b'`, the point of `P b` with coordinate `1` in that trivialization. This file
shows that the preferred trivialization of `P ×_G F` at `b'` gives the class `[σ b, v]` the
coordinate `v`, so that its inverse sends `v` to `[σ b, v]`. Both follow from Tau Ceti's
`TauCeti.AssociatedBundle.trivializationAt_mk`.

## Main results

* `TauCeti.AssociatedBundle.trivializationAt_mk_localSection`,
  `TauCeti.AssociatedBundle.trivializationAt_symm_eq_mk`: the preferred trivialization of
  `P ×_G F` at `b'` and its inverse identify `[σ b, v]` with `v`.

## References

* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, volume I, Chapter I, §5
  (associated bundles).
-/

public section

noncomputable section

open Bundle TauCeti.PrincipalBundle

namespace TauCeti.AssociatedBundle

variable {B G F : Type*} [TopologicalSpace B] [Group G] [TopologicalSpace G]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]
  [TopologicalSpace F] [MulAction G F] [ContinuousSMul G F] [∀ b, Nonempty (P b)]

/-- In the preferred trivialization of `P ×_G F` at `b'`, the class `[σ b, v]` has coordinate `v`,
where `σ = localSection G P b'` is the preferred local section of `P` at `b'`. -/
theorem trivializationAt_mk_localSection {b' b : B}
    (hb : b ∈ (trivializationAt G P b').baseSet) (v : F) :
    trivializationAt F (AssociatedBundle G P F) b' ⟨b, mk G (localSection G P b' b) v⟩ =
      (b, v) := by
  rw [trivializationAt_mk hb, trivializationAt_localSection hb, one_smul]

/-- The inverse of the preferred trivialization of `P ×_G F` at `b'` sends `v` over `b` to the
class `[σ b, v]`, where `σ = localSection G P b'` is the preferred local section of `P` at
`b'`. -/
theorem trivializationAt_symm_eq_mk [Nonempty F] {b' b : B}
    (hb : b ∈ (trivializationAt G P b').baseSet) (v : F) :
    (trivializationAt F (AssociatedBundle G P F) b').symm b v =
      mk G (localSection G P b' b) v := by
  have hb' : b ∈ (trivializationAt F (AssociatedBundle G P F) b').baseSet := by
    rwa [baseSet_trivializationAt]
  have h := (trivializationAt F (AssociatedBundle G P F) b').symm_apply_apply_mk hb'
    (mk G (localSection G P b' b) v)
  rwa [trivializationAt_mk_localSection hb] at h

end TauCeti.AssociatedBundle

end
