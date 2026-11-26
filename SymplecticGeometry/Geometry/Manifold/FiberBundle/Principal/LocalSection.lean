/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Topology.FiberBundle.Principal.LocalSection
public import TauCeti.Geometry.Manifold.FiberBundle.Basic

/-!
# The preferred local section of a principal bundle, in the charted total space

Let `P` be a fibre bundle over a manifold `B` whose model fibre is a group `G` that is a manifold,
such as a principal `G`-bundle. This file reads the preferred local section
`TauCeti.PrincipalBundle.localSection G P b` of `Topology/FiberBundle/Principal/LocalSection.lean`
as a map `B → TauCeti.ManifoldTotalSpace G P` into Tau Ceti's charted total space, through
`TauCeti.ManifoldTotalSpace.homeomorph G P`. This is the form in which forms on the total space
are pulled back along it.

## Main definitions

* `TauCeti.PrincipalBundle.manifoldLocalSection G P b`: the preferred local section of `P` at `b`,
  as a map into the charted total space.

## Main results

* `TauCeti.PrincipalBundle.contMDiffAt_manifoldLocalSection`: it is `C^n` at `b`, with no
  smoothness of the coordinate changes; this is Tau Ceti's
  `TauCeti.ManifoldTotalSpace.contMDiffAt_totalSpaceMk_trivializationAt_symm`.
* `TauCeti.PrincipalBundle.contMDiffOn_manifoldLocalSection`: for a `C^n` fibre bundle, it is
  `C^n` on the base set of the preferred trivialization at `b`, by Tau Ceti's
  `TauCeti.ManifoldTotalSpace.contMDiffOn_trivialization_symm`.

## References

* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, volume I, Chapter I, §5
  (local sections of a principal bundle and its local trivializations).
-/

public section

noncomputable section

open Bundle
open scoped ContDiff

namespace TauCeti.PrincipalBundle

variable {n : ℕ∞ω} {𝕜 B : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  (G : Type*) {EG : Type*} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG] {HG : Type*}
  [TopologicalSpace HG] {IG : ModelWithCorners 𝕜 EG HG} [One G] [TopologicalSpace G]
  [ChartedSpace HG G]
  (P : B → Type*) [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, Nonempty (P b)]

/-- The preferred local section of `P` at `b` (`TauCeti.PrincipalBundle.localSection`), read as a
map into the charted total space `TauCeti.ManifoldTotalSpace G P`. -/
def manifoldLocalSection (b y : B) : ManifoldTotalSpace G P :=
  ManifoldTotalSpace.homeomorph G P ⟨y, localSection G P b y⟩

/-- The preferred local section at `b` in the charted total space is the image of
`⟨y, localSection G P b y⟩` under `TauCeti.ManifoldTotalSpace.homeomorph`. -/
theorem manifoldLocalSection_def (b y : B) :
    manifoldLocalSection G P b y = ManifoldTotalSpace.homeomorph G P ⟨y, localSection G P b y⟩ :=
  (rfl)

/-- The preferred local section in the charted total space lies over the point it is taken
at. -/
@[simp]
theorem proj_homeomorph_symm_manifoldLocalSection (b y : B) :
    ((ManifoldTotalSpace.homeomorph G P).symm (manifoldLocalSection G P b y)).proj = y := by
  rw [manifoldLocalSection_def, Homeomorph.symm_apply_apply]

variable {G P} (IB IG n)

/-- The preferred local section of `P` at `b`, in the charted total space, is `C^n` at `b`. -/
theorem contMDiffAt_manifoldLocalSection (b : B) :
    ContMDiffAt IB (IB.prod IG) n (manifoldLocalSection G P b) b :=
  (ManifoldTotalSpace.contMDiffAt_totalSpaceMk_trivializationAt_symm b
    (1 : G)).congr_of_eventuallyEq
    (.of_forall fun y ↦ by rw [manifoldLocalSection_def, localSection_def])

/-- The preferred local section of a `C^n` fibre bundle `P` at `b`, in the charted total space,
is `C^n` on the base set of the preferred trivialization at `b`. -/
theorem contMDiffOn_manifoldLocalSection [ContMDiffFiberBundle n G P IB IG] (b : B) :
    ContMDiffOn IB (IB.prod IG) n (manifoldLocalSection G P b)
      (trivializationAt G P b).baseSet := by
  refine ((ManifoldTotalSpace.contMDiffOn_trivialization_symm (trivializationAt G P b)).comp
    (contMDiffOn_id.prodMk (contMDiffOn_const (c := (1 : G))))
    fun y hy ↦ (trivializationAt G P b).mem_target.2 hy).congr fun y hy ↦ ?_
  rw [manifoldLocalSection_def, mk_localSection hy, Function.comp_apply, id]

end TauCeti.PrincipalBundle

end
