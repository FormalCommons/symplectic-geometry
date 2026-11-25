/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.MayerVietoris.Basic
public import TauCeti.Geometry.Manifold.SmoothSingular.MayerVietoris
public import TauCeti.Geometry.Manifold.SmoothSingular.Smoothing

/-!
# Small smooth singular cochains and the Mayer–Vietoris connecting map

Let `M` be a manifold and let `U`, `V` be open subsets with `U ⊔ V = ⊤`. Tau Ceti's
`TauCeti.smallSmoothSingularSubcomplex I ![U, V]` is the subcomplex of smooth singular simplices
of `M` whose image lies in `U` or in `V`. This file is the cohomological counterpart of the
homology statements of Tau Ceti's `Geometry/Manifold/SmoothSingular/MayerVietoris.lean`.

* For an affinely stable subcomplex `S` of the singular simplicial set of a space and an open
  cover, restricting cochains on `S` to the simplices of `S` subordinate to the cover is a
  quasi-isomorphism (`TauCeti.quasiIso_cochainComplexMap_homOfLE_inf_smallSingularSubcomplex`).
  This is `Hom(-, Y)` applied to the chain homotopy equivalence
  `TauCeti.subcomplexSmallChainHomotopyEquiv`, as Tau Ceti's
  `TauCeti.quasiIso_cochainComplexMap_smallSingularSubcomplex_ι` does for `S` the whole singular
  simplicial set.
* For a Hausdorff `σ`-compact smooth manifold with a finite-dimensional model and a projective
  coefficient object `R`, restricting singular cochains of `M` to the small smooth simplices is a
  quasi-isomorphism (`TauCeti.quasiIso_cochainComplexMap_smallSmoothSingularSubcomplex_ι`): it is
  restriction to smooth simplices, a quasi-isomorphism by the smoothing theorem, followed by the
  restriction of the previous point. The induced isomorphism on cohomology is
  `TauCeti.smallSmoothSingularCohomologyIso`.
* Under these restrictions, the singular Mayer–Vietoris connecting map
  `TopCat.singularCohomologyMayerVietorisδ` becomes the connecting map
  `SSet.mayerVietorisCochainδ` of the pushout square
  `TauCeti.isPushout_smoothSingularSubcomplex_inter_smallSmoothSingularSubcomplex` of smooth
  singular subcomplexes
  (`TauCeti.singularCohomologyMayerVietorisδ_comp_homologyMap_smallSmoothSingularSubcomplex_ι`).
  This needs no hypothesis on `M` beyond its charted space structure. The proof follows Tau
  Ceti's homology statement `TauCeti.smoothMayerVietorisδ_ι`: naturality of the cochain
  connecting map (`SSet.mayerVietorisCochainδ_naturality`) along the inclusion of the smooth
  square into the singular one.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 18 (smooth singular cohomology, Theorem 18.7).
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.1 (the
  Mayer–Vietoris sequences in cohomology).
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace SSet.Subcomplex
open scoped Manifold ContDiff

universe u v w

namespace TauCeti

section Subcomplex

variable {C : Type v} [Category.{w} C] [HasCoproducts.{u} C] [Abelian C] (R : C)
  (k : Type*) [Ring k] [Linear k C] (Y : C)
  {X : TopCat.{u}} (S : (TopCat.toSSet.obj X).Subcomplex) [S.IsAffineStable]
  {ι : Type*} (U : ι → Set X) (hU : ∀ i, IsOpen (U i)) (hcov : ⋃ i, U i = Set.univ)

include hU hcov in
/-- For an affinely stable subcomplex `S` of the singular simplicial set of `X` and an open cover
`U` of `X`, restricting cochains on `S` with values in `Y` to the simplices of `S` subordinate to
`U` is a quasi-isomorphism. -/
theorem quasiIso_cochainComplexMap_homOfLE_inf_smallSingularSubcomplex :
    QuasiIso (SSet.cochainComplexMap (R := R) (k := k) (M := Y)
      (homOfLE (inf_le_left : S ⊓ X.smallSingularSubcomplex U ≤ S))) := by
  have :=
    ((subcomplexSmallChainHomotopyEquiv R S U hU hcov).linearYonedaFunctorMap k Y).quasiIso_hom
  rwa [HomotopyEquiv.linearYonedaFunctorMap_hom, subcomplexSmallChainHomotopyEquiv_hom] at this

end Subcomplex

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  {C : Type v} [Category.{w} C] [HasCoproducts.{u} C] [Abelian C] (R : C)
  (k : Type*) [Ring k] [Linear k C] (Y : C) {U V : Opens M}

section Smoothing

variable [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M]
  [HasExactColimitsOfShape (Discrete ℕ) C] [Projective R]

/-- For open sets `U`, `V` of a Hausdorff `σ`-compact smooth manifold `M` with `U ⊔ V = ⊤`,
restricting singular cochains of `M` to the smooth singular simplices lying in `U` or in `V` is a
quasi-isomorphism, when the coefficient object `R` is projective. -/
theorem quasiIso_cochainComplexMap_smallSmoothSingularSubcomplex_ι (hUV : U ⊔ V = ⊤) :
    QuasiIso (SSet.cochainComplexMap (R := R) (k := k) (M := Y)
      (smallSmoothSingularSubcomplex I ![(U : Set M), (V : Set M)]).ι) := by
  -- The small smooth subcomplex is the meet of the smooth subcomplex with the small one.
  have key : ∀ {T : (TopCat.toSSet.obj (TopCat.of M)).Subcomplex}
      (hT : T ≤ smoothSingularSubcomplex I M),
      T = smoothSingularSubcomplex I M ⊓ (TopCat.of M).smallSingularSubcomplex
        ![(U : Set M), (V : Set M)] →
      QuasiIso (SSet.cochainComplexMap (R := R) (k := k) (M := Y) (homOfLE hT)) := by
    rintro _ _ rfl
    exact quasiIso_cochainComplexMap_homOfLE_inf_smallSingularSubcomplex R k Y
      (smoothSingularSubcomplex I M) ![(U : Set M), (V : Set M)] (U.isOpen.vecCons V.isOpen)
      (by rw [Set.iUnion_vecCons_pair, ← Opens.coe_sup, hUV, Opens.coe_top])
  have := key (smallSmoothSingularSubcomplex_le_smoothSingularSubcomplex I _)
    (smallSmoothSingularSubcomplex_eq _)
  rw [← homOfLE_ι (smallSmoothSingularSubcomplex_le_smoothSingularSubcomplex I _),
    SSet.cochainComplexMap_comp]
  infer_instance
/-- For open sets `U`, `V` of a Hausdorff `σ`-compact smooth manifold `M` with `U ⊔ V = ⊤` and a
projective coefficient object `R`, the isomorphism from the singular cohomology of `M` to the
cohomology of the cochains on the smooth singular simplices lying in `U` or in `V`, induced by
restriction. -/
def smallSmoothSingularCohomologyIso (hUV : U ⊔ V = ⊤) (n : ℕ) :
    (TopCat.of M).singularCohomology R k Y n ≅
      (((smallSmoothSingularSubcomplex I ![(U : Set M), (V : Set M)] : SSet).chainComplex
        R).linearYonedaObj k Y).homology n :=
  have := quasiIso_cochainComplexMap_smallSmoothSingularSubcomplex_ι I R k Y hUV
  asIso (HomologicalComplex.homologyMap
    (SSet.cochainComplexMap (smallSmoothSingularSubcomplex I ![(U : Set M), (V : Set M)]).ι) n)

/-- The forward map of `smallSmoothSingularCohomologyIso` is the map on cohomology induced by
restriction to the smooth singular simplices lying in `U` or in `V`. -/
@[simp]
theorem smallSmoothSingularCohomologyIso_hom (hUV : U ⊔ V = ⊤) (n : ℕ) :
    (smallSmoothSingularCohomologyIso I R k Y hUV n).hom =
      HomologicalComplex.homologyMap
        (SSet.cochainComplexMap (smallSmoothSingularSubcomplex I ![(U : Set M), (V : Set M)]).ι)
        n := by
  rw [smallSmoothSingularCohomologyIso, asIso_hom]

end Smoothing

/-- Restriction to the smooth singular simplices lying in `U` or in `V` carries the singular
Mayer–Vietoris connecting map `Hⁿ(U ∩ V) ⟶ Hᵐ(M)`, `n + 1 = m`, to the connecting map of the
pushout square of smooth singular subcomplexes, precomposed with restriction of the singular
cochains of `U ∩ V` to smooth simplices. -/
@[reassoc]
theorem singularCohomologyMayerVietorisδ_comp_homologyMap_smallSmoothSingularSubcomplex_ι
    (hUV : U ⊔ V = ⊤) (n m : ℕ) (h : n + 1 = m := by lia) :
    TopCat.singularCohomologyMayerVietorisδ R k Y U.isOpen V.isOpen
        (by rw [← Opens.coe_sup, hUV, Opens.coe_top]) n m h ≫
      HomologicalComplex.homologyMap
        (SSet.cochainComplexMap (smallSmoothSingularSubcomplex I ![(U : Set M), (V : Set M)]).ι)
        m =
    HomologicalComplex.homologyMap
        (SSet.cochainComplexMap (R := R) (k := k) (M := Y)
          (smoothSingularSubcomplex I ↥(U ⊓ V)).ι) n ≫
      SSet.mayerVietorisCochainδ R k Y
        (isPushout_smoothSingularSubcomplex_inter_smallSmoothSingularSubcomplex I U V) n m h := by
  rw [← homOfLE_ι (smallSmoothSingularSubcomplex_le_smallSingularSubcomplex I _),
    SSet.cochainComplexMap_comp, HomologicalComplex.homologyMap_comp,
    TopCat.singularCohomologyMayerVietorisδ_comp_homologyMap_assoc R k Y _ _ _ n m h]
  exact SSet.mayerVietorisCochainδ_naturality R k Y _ _ _ _
    (isPushout_smoothSingularSubcomplex_inter_smallSmoothSingularSubcomplex I U V)
    (TopCat.isPushout_toSSet_inter_smallSingularSubcomplex (X := TopCat.of M)
      (U : Set M) (V : Set M))
    (smoothSingularSubcomplexMap_inclusion_ι (inf_le_left : U ⊓ V ≤ U))
    (smoothSingularSubcomplexMap_inclusion_ι (inf_le_right : U ⊓ V ≤ V))
    (toSmallSmoothSingularSubcomplex_homOfLE_right _ _)
    (toSmallSmoothSingularSubcomplex_homOfLE_right _ _) n m h

end TauCeti

end
