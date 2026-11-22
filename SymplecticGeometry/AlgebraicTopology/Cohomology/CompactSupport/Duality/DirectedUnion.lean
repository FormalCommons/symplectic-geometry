/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Cohomology.CompactSupport.DirectedUnion
public import SymplecticGeometry.AlgebraicTopology.Cohomology.CompactSupport.Duality.Basic
public import SymplecticGeometry.AlgebraicTopology.Singular.DirectedUnion
public import SymplecticGeometry.Topology.Sets.Opens

/-!
# Injectivity and surjectivity of the duality map on a directed union of open sets

Fix a boundaryless `n`-manifold `M` with a homological orientation `o`, covered by a
directed family of open sets `U j`, each with the restricted orientation. Injectivity, and
surjectivity, of the duality maps `Hᵖ_c(U j; L) ⟶ H_q(U j; L)`, `p + q = n`, of all members pass
to the duality map of `M`
(`TauCeti.HomologicalOrientation.injective_dualityMap_of_iSup_eq_top`,
`TauCeti.HomologicalOrientation.surjective_dualityMap_of_iSup_eq_top`). This refines
`TauCeti.HomologicalOrientation.bijective_dualityMap_of_iSup_eq_top`, which needs both.

Both arguments use that every compact subset of `M` lies in some `U j`:

* a homology class of `M` comes from some `U j`
  (`TauCeti.exists_singularHomologyMap_inclusion'_eq_of_iSup_eq_top`); a preimage there under the
  duality map of `U j`, extended by zero to `M`, is a preimage under the duality map of `M`;
* a compactly supported class of `M` is extended from some `U i`
  (`TopCat.exists_compactSupportCohomologyExtend_eq_of_iSup_eq_top`). If the duality map of `M`
  kills it, its image in `H_q(U i)` dies in `H_q(M)`, hence in some larger `U j`
  (`TauCeti.exists_singularHomologyMap_toTopCat_map_eq_zero_of_iSup_eq_top`); by injectivity on
  `U j` the class already vanishes in `Hᵖ_c(U j)`, and so in `Hᵖ_c(M)`
  (`TopCat.compactSupportCohomologyExtend_toTopCat_map_comp_apply`).

An empty family covers only the empty manifold (`TopologicalSpace.Opens.isEmpty_of_iSup_eq_top`),
whose duality map is bijective (`TauCeti.HomologicalOrientation.bijective_dualityMap_of_isEmpty`).

## Provenance

The statements and proofs are those of Tau Ceti's main branch, in
`TauCeti/AlgebraicTopology/Cohomology/CompactSupport/Duality/DirectedUnion.lean`, under the same
names; no tagged release has them yet. They are stated here under their Tau Ceti names and
namespace, so that moving Tau Ceti past them deletes this file without renames.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.3, Lemma 3.36 and
  the proof of Theorem 3.35, the passage to increasing unions of open sets.
-/

public section

noncomputable section

open CategoryTheory Limits Module TopologicalSpace Topology

namespace TauCeti

attribute [local instance] MonoidalPreadditive.monoidalLinearInt

namespace HomologicalOrientation

variable {M E : Type} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  {n : ℕ} (o : HomologicalOrientation M E n) (hn : finrank ℝ E = n) (L : ModuleCat.{0} ℤ)

variable {J : Type} [Preorder J] [IsDirected J (· ≤ ·)] {U : J → Opens (TopCat.of M)}
  (hU : Monotone U) (hcover : ⨆ j, U j = ⊤) {p q : ℕ} (h : p + q = n)

include hU hcover

/-- **Surjectivity of the duality map passes to directed unions**: if `M` is covered by a directed
family of open sets `U j`, oriented by the pullbacks of `o`, whose duality maps
`Hᵖ_c(U j; L) ⟶ H_q(U j; L)` are surjective, then the duality map of `M` is surjective. -/
theorem surjective_dualityMap_of_iSup_eq_top
    (hD : ∀ j, Function.Surjective ((o.comap (U j).isOpenEmbedding).dualityMap hn L p q h)) :
    Function.Surjective (o.dualityMap hn L p q h) := fun x ↦ by
  rcases isEmpty_or_nonempty J with hJ | hJ
  · have : IsEmpty M := Opens.isEmpty_of_iSup_eq_top hcover
    exact (o.bijective_dualityMap_of_isEmpty hn L h).2 x
  obtain ⟨j, y, rfl⟩ := exists_singularHomologyMap_inclusion'_eq_of_iSup_eq_top L q hU hcover x
  obtain ⟨z, rfl⟩ := hD j y
  exact ⟨_, o.compactSupportCohomologyExtend_inclusion'_dualityMap_apply hn L (U j) h z⟩

/-- **Injectivity of the duality map passes to directed unions**: if `M` is covered by a directed
family of open sets `U j`, oriented by the pullbacks of `o`, whose duality maps
`Hᵖ_c(U j; L) ⟶ H_q(U j; L)` are injective, then the duality map of `M` is injective. -/
theorem injective_dualityMap_of_iSup_eq_top
    (hD : ∀ j, Function.Injective ((o.comap (U j).isOpenEmbedding).dualityMap hn L p q h)) :
    Function.Injective (o.dualityMap hn L p q h) := by
  rcases isEmpty_or_nonempty J with hJ | hJ
  · have : IsEmpty M := Opens.isEmpty_of_iSup_eq_top hcover
    exact (o.bijective_dualityMap_of_isEmpty hn L h).1
  refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
  obtain ⟨i, z, rfl⟩ :=
    TopCat.exists_compactSupportCohomologyExtend_eq_of_iSup_eq_top hU hcover x
  -- `D_M` on the extension of `z` is the pushforward of `D_{U i} z`, which therefore vanishes in
  -- `H_q(M)`, hence in some `H_q(U j)`.
  rw [compactSupportCohomologyExtend_inclusion'_dualityMap_apply] at hx
  obtain ⟨j, hij, hj⟩ :=
    exists_singularHomologyMap_toTopCat_map_eq_zero_of_iSup_eq_top L q hU hcover _ hx
  -- `D_{U j}` kills the extension of `z` to `U j`, which therefore vanishes.
  have hz : TopCat.compactSupportCohomologyExtend
      (Opens.isOpenEmbedding_toTopCat_map (homOfLE (hU hij))) p z = 0 :=
    (injective_iff_map_eq_zero _).1 (hD j) _
      ((o.compactSupportCohomologyExtend_toTopCat_map_dualityMap_apply hn L (homOfLE (hU hij)) h
        z).trans hj)
  -- So does its extension to `M`, which is the extension of `z`.
  rw [← TopCat.compactSupportCohomologyExtend_toTopCat_map_comp_apply (homOfLE (hU hij)), hz,
    map_zero]

end HomologicalOrientation

end TauCeti
