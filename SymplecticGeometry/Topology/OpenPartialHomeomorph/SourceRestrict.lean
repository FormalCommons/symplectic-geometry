/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.OpenPartialHomeomorph.Basic
public import Mathlib.Topology.Algebra.Group.ContinuousDiv
import TauCeti.Data.Set.Image

/-!
# Fibres of the restriction of an open partial homeomorphism to its source

Tau Ceti's `OpenPartialHomeomorph.sourceRestrict` is the restriction of an open partial
homeomorphism `e : X → Y` to its source, as a continuous map `e.source → Y`. Since `e` is
injective on its source, the fibre of this map over `e a`, for `a ∈ e.source`, is the single point
`⟨a, ha⟩` of the subtype (`OpenPartialHomeomorph.sourceRestrict_preimage_singleton`). Tau Ceti's
`OpenPartialHomeomorph.sourceRestrict_preimage` gives the same inclusion read in `X`, through the
inclusion of the source.

For `Y` a topological additive group and `a : X`, `OpenPartialHomeomorph.centeredSourceRestrict`
is the restriction `x ↦ e x - e a` of `e`, translated so that `e a` goes to the origin, as a
continuous map `e.source → Y`. It is an open embedding
(`OpenPartialHomeomorph.isOpenEmbedding_centeredSourceRestrict`, from Tau Ceti's
`OpenPartialHomeomorph.isOpenEmbedding_sourceRestrict`), and for `a ∈ e.source` it vanishes at
`⟨a, ha⟩` only (`OpenPartialHomeomorph.centeredSourceRestrict_preimage_zero`).

The file also records how a point of the source is located by its image: if `e a = y` with
`a ∈ e.source`, and `e.symm` maps a set `S ∋ y` into `T`, then `a ∈ T`
(`OpenPartialHomeomorph.mem_of_mapsTo_symm`).
-/

public section

namespace OpenPartialHomeomorph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : OpenPartialHomeomorph X Y)

/-- For `a` in the source of `e`, the restriction of `e` to its source takes the value `e a` at
the point `⟨a, ha⟩` only. -/
theorem sourceRestrict_preimage_singleton {a : X} (ha : a ∈ e.source) :
    e.sourceRestrict ⁻¹' {e a} = {(⟨a, ha⟩ : e.source)} :=
  e.sourceRestrict_apply ⟨a, ha⟩ ▸ e.isOpenEmbedding_sourceRestrict.injective.preimage_singleton _

/-- If `e` sends a point `a` of its source to `y`, and `e.symm` maps a set `S` containing `y` into
`T`, then `a ∈ T`. -/
theorem mem_of_mapsTo_symm {a : X} (ha : a ∈ e.source) {y : Y} (hy : e a = y) {S : Set Y}
    {T : Set X} (hST : Set.MapsTo e.symm S T) (hyS : y ∈ S) : a ∈ T := by
  rw [← e.left_inv ha, hy]
  exact hST hyS

section Centered

variable [AddGroup Y] [IsTopologicalAddGroup Y]

/-- The restriction of `e` to its source, translated so that `e a` goes to the origin: the
continuous map `x ↦ e x - e a` on `e.source`. -/
def centeredSourceRestrict (a : X) : C(e.source, Y) :=
  ⟨fun x ↦ e x - e a, e.continuousOn.domRestrict.sub continuous_const⟩

/-- The centred restriction of `e` at `a` is the continuous map `x ↦ e x - e a` on the
source. -/
theorem centeredSourceRestrict_def (a : X) :
    e.centeredSourceRestrict a =
      ⟨fun x ↦ e x - e a, e.continuousOn.domRestrict.sub continuous_const⟩ :=
  (rfl)

/-- The centred restriction of `e` at `a` sends `x` to `e x - e a`. -/
@[simp]
theorem centeredSourceRestrict_apply (a : X) (x : e.source) :
    e.centeredSourceRestrict a x = e x - e a :=
  (rfl)

/-- The centred restriction of `e` at `a` is the restriction of `e` to its source followed by
the translation by `-e a`. -/
theorem centeredSourceRestrict_eq_comp (a : X) :
    e.centeredSourceRestrict a = (Homeomorph.subRight (e a) : C(Y, Y)).comp e.sourceRestrict :=
  ContinuousMap.ext fun x ↦ by simp

/-- The centred restriction of `e` at a point of its source vanishes at that point only. -/
theorem centeredSourceRestrict_preimage_zero {a : X} (ha : a ∈ e.source) :
    e.centeredSourceRestrict a ⁻¹' {0} = {(⟨a, ha⟩ : e.source)} := by
  rw [← e.sourceRestrict_preimage_singleton ha]
  ext x
  simp [sub_eq_zero]

/-- The centred restriction of `e` at any point is an open embedding. -/
theorem isOpenEmbedding_centeredSourceRestrict (a : X) :
    Topology.IsOpenEmbedding (e.centeredSourceRestrict a) := by
  rw [centeredSourceRestrict_eq_comp, ContinuousMap.coe_comp]
  exact (Homeomorph.subRight (e a)).isOpenEmbedding.comp e.isOpenEmbedding_sourceRestrict

end Centered

end OpenPartialHomeomorph

end
