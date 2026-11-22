/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-!
# An open partial homeomorphism restricted to its source

Every point lies in the source of the identity open partial homeomorphism
(`OpenPartialHomeomorph.mem_refl_source`). An open partial homeomorphism `e : X → Y` restricts to
a continuous map `e.sourceRestrict : C(e.source, Y)` (`OpenPartialHomeomorph.sourceRestrict`),
which is an open embedding (`OpenPartialHomeomorph.isOpenEmbedding_sourceRestrict`) and sends no
other point of the source to the image of a point of the source
(`OpenPartialHomeomorph.sourceRestrict_preimage`).

This file is a part of Tau Ceti's `TauCeti/Topology/OpenPartialHomeomorph/Basic.lean`, as of the
commit `55525ca744` (TauCetiProject/TauCeti#37381) of Tau Ceti's main branch, not yet in the
pinned release, which has only private copies of `sourceRestrict` and `mem_refl_source` in
`TauCeti/AlgebraicTopology/Singular/LocalHomology/Orientation/Smooth.lean`. It takes only
`OpenPartialHomeomorph.mem_refl_source`, `OpenPartialHomeomorph.sourceRestrict`,
`OpenPartialHomeomorph.sourceRestrict_apply`,
`OpenPartialHomeomorph.isOpenEmbedding_sourceRestrict` and
`OpenPartialHomeomorph.sourceRestrict_preimage`, under their Tau Ceti names, so that moving Tau
Ceti past them deletes this file without renames. Their statements, proofs and docstrings are Tau
Ceti's, unchanged; this module docstring is new, and the file imports only the two Mathlib
modules that these declarations use.
-/

public section

namespace OpenPartialHomeomorph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : OpenPartialHomeomorph X Y)

/-- Every point is in the source of the identity partial homeomorphism. -/
theorem mem_refl_source (x : X) : x ∈ (OpenPartialHomeomorph.refl X).source :=
  Set.mem_univ x

/-- The restriction of an open partial homeomorphism to its source, as a continuous map. -/
def sourceRestrict : C(e.source, Y) :=
  ⟨e.source.domRestrict e, e.continuousOn.domRestrict⟩

/-- Restricting to the source agrees pointwise with the partial homeomorphism. -/
@[simp]
theorem sourceRestrict_apply (x : e.source) : e.sourceRestrict x = e x :=
  (rfl)

/-- The restriction to the source is an open embedding. -/
theorem isOpenEmbedding_sourceRestrict : Topology.IsOpenEmbedding e.sourceRestrict :=
  e.isOpenEmbedding_restrict

/-- A point of the source is the only point of the source that `e` sends to its image. -/
theorem sourceRestrict_preimage {a : X} (ha : a ∈ e.source) :
    e.sourceRestrict ⁻¹' {e a} ⊆ ContinuousMap.subtypeVal e.source ⁻¹' {a} :=
  fun x hx ↦ e.injOn x.property ha hx

end OpenPartialHomeomorph
