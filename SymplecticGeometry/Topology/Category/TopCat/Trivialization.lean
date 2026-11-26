/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Topology.FiberBundle.Basic
public import TauCeti.Topology.Category.TopCat.Trivialization

/-!
# Fibre inclusions of trivializations of morphisms of `TopCat`

For a morphism `p : E ⟶ B` of `TopCat` and a trivialization `t` of `p` with model fibre `F`, the
library's continuous fibre inclusion `Bundle.Trivialization.fiberInclusionMap`, defined for any
projection between topological spaces, is Tau Ceti's fibre inclusion
`Bundle.Trivialization.fiberInclusion` in `TopCat`
(`Bundle.Trivialization.ofHom_fiberInclusionMap`). This lets results stated with Tau Ceti's
morphism apply to a fibre bundle `[FiberBundle F Z]`, whose trivializations are read through
`fiberInclusionMap`.
-/

public section

open CategoryTheory TopCat

universe u

namespace Bundle.Trivialization

variable {E B F : TopCat.{u}} {p : E ⟶ B}

/-- For a trivialization of a morphism of `TopCat`, the continuous fibre inclusion
`fiberInclusionMap`, as a morphism of `TopCat`, is Tau Ceti's fibre inclusion. -/
@[simp]
theorem ofHom_fiberInclusionMap (t : Bundle.Trivialization F p) {x : B} (hx : x ∈ t.baseSet) :
    ofHom (t.fiberInclusionMap hx) = t.fiberInclusion hx := by
  ext f
  rw [ConcreteCategory.hom_ofHom, fiberInclusionMap_apply, fiberInclusion_apply]

end Bundle.Trivialization

end
