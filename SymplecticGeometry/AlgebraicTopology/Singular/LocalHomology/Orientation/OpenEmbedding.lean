/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.OpenEmbedding
public import TauCeti.Topology.Category.TopCat.Opens
public import SymplecticGeometry.Geometry.Manifold.Opens

/-!
# Restricting an orientation to nested open sets

For opens `V ⊆ W` of a manifold `N` with a homological orientation `o`, restricting `o` to `W`
and then along the inclusion `V ⟶ W` of `Opens (TopCat.of N)` is restricting it to `V`
(`TauCeti.HomologicalOrientation.comap_comap_toTopCat_map`), a case of
`TauCeti.HomologicalOrientation.comap_comap_of_comp_eq`.

This lemma is from Tau Ceti's main branch
(`TauCeti/AlgebraicTopology/Singular/LocalHomology/Orientation/OpenEmbedding.lean`, same name),
not yet in the pinned release; it is stated here under its Tau Ceti name, so that moving Tau Ceti
past it deletes this file without renames.
-/

public section

open CategoryTheory Topology

universe w

namespace TauCeti.HomologicalOrientation

variable {N E : Type w} [TopologicalSpace N] [T2Space N] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [ChartedSpace E N] {d : ℕ}

/-- Restricting an orientation of `N` to an open `W` and then to an open `V ⊆ W`, along the
inclusion `V ⟶ W` in `Opens (TopCat.of N)`, is restricting it to `V`. -/
@[simp]
lemma comap_comap_toTopCat_map (o : HomologicalOrientation N E d)
    {V W : TopologicalSpace.Opens (TopCat.of N)} (f : V ⟶ W) :
    (o.comap W.isOpenEmbedding).comap (TopologicalSpace.Opens.isOpenEmbedding_toTopCat_map f) =
      o.comap V.isOpenEmbedding :=
  o.comap_comap_of_comp_eq _ _ _ (funext fun _ ↦ rfl)

end TauCeti.HomologicalOrientation

end
