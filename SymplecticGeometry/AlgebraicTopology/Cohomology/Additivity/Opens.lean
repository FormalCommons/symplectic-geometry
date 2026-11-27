/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Additivity.Basic
import SymplecticGeometry.Topology.Homeomorph.Sigma

/-!
# Singular cohomology of a union of disjoint open sets

The singular cohomology of a union of pairwise disjoint open sets `V i` is the product of the
cohomologies of the `V i`, with the restrictions as projections
(`TauCeti.isLimitFanSingularCohomologyIUnion`). The union is homeomorphic to the disjoint union
of the `V i` (`Set.isHomeomorph_sigma_inclusion`), so this is Tau Ceti's
`TauCeti.isLimitFanSingularCohomology`, stated for `Σ i, V i`, moved along that homeomorphism.

## Main results

* `TauCeti.isLimitFanSingularCohomologyIUnion`: the singular cohomology of a union of pairwise
  disjoint open sets is the product of their cohomologies.
-/

public section

noncomputable section

open CategoryTheory Limits Set Function

universe w v u

namespace TauCeti

variable {ι : Type w} {X : TopCat.{w}} {V : ι → Set X}
  (C : Type u) [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
  (k : Type*) [Ring k] [Linear k C] (M : C)

/-- **Additivity of singular cohomology over disjoint open sets.** In every degree, the singular
cohomology of a union of pairwise disjoint open sets `V i` is the product of the singular
cohomologies of the `V i`, with the restrictions to the `V i` as projections. -/
def isLimitFanSingularCohomologyIUnion [Small.{v} ι] (hV : ∀ i, IsOpen (V i))
    (hd : Pairwise (Disjoint on V)) (n : ℕ) :
    IsLimit (Fan.mk ((TopCat.of ↥(⋃ i, V i)).singularCohomology R k M n)
      (fun i ↦ TopCat.singularCohomologyMap
        (TopCat.ofHom (ContinuousMap.inclusion (subset_iUnion V i))) n) :
      Fan fun i ↦ (TopCat.of (V i)).singularCohomology R k M n) :=
  -- The disjoint union of the `V i` maps homeomorphically onto their union.
  let σ : TopCat.of (Σ i, V i) ≅ TopCat.of ↥(⋃ i, V i) := TopCat.isoOfHomeo
    (isHomeomorph_sigma_inclusion hV hd (subset_iUnion V) subset_rfl).homeomorph
  -- `singularCohomologyFunctor` is exposed and sends `σ.hom.op` to
  -- `singularCohomologyMap σ.hom n` by definition; its `simps` lemmas cannot rewrite here, since
  -- the source and target of the map depend on `obj`.
  have : IsIso (TopCat.singularCohomologyMap (R := R) (k := k) (M := M) σ.hom n) :=
    (inferInstance : IsIso ((singularCohomologyFunctor R k M n).map σ.hom.op))
  IsLimit.ofIsoLimit (isLimitFanSingularCohomology (fun i ↦ TopCat.of (V i)) C R k M n)
    (Fan.ext (asIso (TopCat.singularCohomologyMap σ.hom n)).symm fun i ↦ by
      rw [Iso.symm_hom, asIso_inv, IsIso.eq_inv_comp]
      exact (TopCat.singularCohomologyMap_comp _ _ n).symm)

end TauCeti
