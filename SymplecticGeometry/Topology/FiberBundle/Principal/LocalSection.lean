/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.FiberBundle.Basic

/-!
# The preferred local section of a principal bundle

Let `P` be a fibre bundle whose model fibre is a group `G`, such as a principal `G`-bundle. For a
point `b` of the base, `TauCeti.PrincipalBundle.localSection G P b` is the section of `P` that
takes at `y` the point of `P y` with fibre coordinate `1` in the preferred trivialization
`trivializationAt G P b`. Over the base set of that trivialization it is a continuous local
section of `P` (`TauCeti.PrincipalBundle.continuousOn_localSection`), which that trivialization
sends to the fibre coordinate `1` (`TauCeti.PrincipalBundle.trivializationAt_localSection`);
outside it, its value is the junk value of Mathlib's `Bundle.Trivialization.symm`.

The manifold version, read in Tau Ceti's charted total space, is in
`Geometry/Manifold/FiberBundle/Principal/LocalSection.lean`.

## Main definitions

* `TauCeti.PrincipalBundle.localSection G P b`: the preferred local section of `P` at `b`,
  `y ↦ (trivializationAt G P b).symm y 1`.

## Main results

* `TauCeti.PrincipalBundle.continuousOn_localSection`: as a map into the total space, it is
  continuous on the base set of `trivializationAt G P b`.

## References

* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, volume I, Chapter I, §5
  (local sections of a principal bundle and its local trivializations).
-/

public section

noncomputable section

open Bundle

namespace TauCeti.PrincipalBundle

variable (G : Type*) {B : Type*} [TopologicalSpace B] [One G] [TopologicalSpace G]
  (P : B → Type*) [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, Nonempty (P b)]

/-- The preferred local section of `P` at `b`: at `y`, the point of `P y` whose fibre coordinate
in the preferred trivialization `trivializationAt G P b` is `1`. It is a local section over the
base set of that trivialization. -/
def localSection (b y : B) : P y :=
  (trivializationAt G P b).symm y 1

/-- The value of the preferred local section at `b`. -/
theorem localSection_def (b y : B) :
    localSection G P b y = (trivializationAt G P b).symm y 1 :=
  (rfl)

variable {G P}

/-- Over the base set of the preferred trivialization at `b`, that trivialization sends the
preferred local section at `b` to the fibre coordinate `1`. -/
theorem trivializationAt_localSection {b y : B} (hy : y ∈ (trivializationAt G P b).baseSet) :
    trivializationAt G P b ⟨y, localSection G P b y⟩ = (y, 1) :=
  (trivializationAt G P b).apply_mk_symm hy 1

/-- The preferred local section at `b`, as a point of the total space, is the inverse of the
preferred trivialization at `b` applied to `(y, 1)`, for `y` in its base set. -/
theorem mk_localSection {b y : B} (hy : y ∈ (trivializationAt G P b).baseSet) :
    (⟨y, localSection G P b y⟩ : TotalSpace G P) =
      (trivializationAt G P b).toOpenPartialHomeomorph.symm (y, 1) :=
  (trivializationAt G P b).mk_symm hy 1

/-- The preferred local section at `b`, as a map into the total space, is continuous on the base
set of the preferred trivialization at `b`. -/
theorem continuousOn_localSection (b : B) :
    ContinuousOn (fun y ↦ (⟨y, localSection G P b y⟩ : TotalSpace G P))
      (trivializationAt G P b).baseSet :=
  ((trivializationAt G P b).continuousOn_symm.comp
    (continuous_id.prodMk (continuous_const (y := (1 : G)))).continuousOn
    fun _ hy ↦ ⟨hy, Set.mem_univ _⟩).congr fun _ _ ↦ by
    rw [Function.comp_apply, id, localSection_def]

end TauCeti.PrincipalBundle

end
