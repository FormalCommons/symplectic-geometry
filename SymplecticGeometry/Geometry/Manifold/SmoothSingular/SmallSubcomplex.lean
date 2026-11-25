/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Basic
public import TauCeti.Geometry.Manifold.SmoothSingular.MayerVietoris

/-!
# Small smooth simplices of `M` as smooth simplices of `U ⊔ V`

Let `U` and `V` be open subsets of a smooth manifold `M`. A smooth singular simplex of `M` that
lies in `U` or in `V` lies in `U ⊔ V`, and is smooth there. This file builds the resulting map of
simplicial sets `TauCeti.smallSmoothSingularSubcomplexToSup`, from the smooth simplices of `M`
lying in `U` or in `V` (`TauCeti.smallSmoothSingularSubcomplex`) to the smooth singular simplices
of `U ⊔ V`, and shows how it meets the maps of smooth singular subcomplexes induced by the
inclusions of `U ⊔ V` in `M` and of `U` and `V` in `U ⊔ V`, and the restriction of singular
cochains.

The map `TauCeti.smallSmoothSingularSubcomplexToSup`, the lemma that it lands in the range of
`U ⊔ V`, `TauCeti.smallSmoothSingularSubcomplexToSup_smoothSingularSubcomplexMap` and
`TauCeti.toSmallSmoothSingularSubcomplex_smallSmoothSingularSubcomplexToSup` adapt Tau Ceti's
`TopCat.smallSingularSubcomplexToUnion`, its private `smallSubcomplex_le_range`,
`TopCat.smallSingularSubcomplexToUnion_comp` and its private
`toSmallSingularSubcomplex_comp_smallSingularSubcomplexToUnion`
(`TauCeti/AlgebraicTopology/Singular/MayerVietoris/Relative.lean`) from continuous to smooth
simplices.

## Main results

* `TauCeti.smallSmoothSingularSubcomplexToSup`: the map from the smooth simplices of `M` lying in
  `U` or in `V` to the smooth singular simplices of `U ⊔ V`.
* `TauCeti.smallSmoothSingularSubcomplexToSup_smoothSingularSubcomplexMap`: followed by the
  inclusion of `U ⊔ V` in `M`, it is the inclusion of the small smooth simplices among all
  smooth simplices of `M`.
* `TauCeti.toSmallSmoothSingularSubcomplex_smallSmoothSingularSubcomplexToSup`: on the smooth
  simplices of an open set contained in `U` or in `V`, it is induced by the inclusion of that set.
* `TauCeti.singularCohomologyMap_subtypeVal_comp_smallSmoothSingularSubcomplexToSup`: on singular
  cohomology, restriction to `U ⊔ V` followed by it is restriction to the small smooth simplices.
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace
open scoped Manifold ContDiff

namespace TauCeti

universe u v w

section Simplices

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) {M : Type u} [TopologicalSpace M] [ChartedSpace H M]

open SSet.Subcomplex

/-- The inclusion of the smooth singular simplices of an open set `W`, as simplices of `M`. -/
private abbrev smoothSingularSubcomplexToM (W : Opens M) :
    (smoothSingularSubcomplex I W : SSet) ⟶ TopCat.toSSet.obj (TopCat.of M) :=
  (smoothSingularSubcomplex I W).ι ≫
    TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal (W : Set M)))

/-- A smooth simplex of `M` lying in `U` or in `V` is the image of a smooth simplex of `U ⊔ V`. -/
private theorem smallSmoothSingularSubcomplex_le_range (U V : Opens M) :
    smallSmoothSingularSubcomplex I ![(U : Set M), (V : Set M)] ≤
      range (smoothSingularSubcomplexToM I (U ⊔ V)) := by
  rw [range_smoothSingularSubcomplex_ι_comp_subtypeVal]
  refine le_inf (smallSmoothSingularSubcomplex_le_smoothSingularSubcomplex I _) ?_
  intro n σ hσ
  rw [TopCat.mem_range_toSSet_subtypeVal_iff (X := TopCat.of M)]
  obtain ⟨-, i, hi⟩ := (mem_smallSmoothSingularSubcomplex_iff _ σ).1 hσ
  refine hi.trans ?_
  fin_cases i
  · exact (le_sup_left : U ≤ U ⊔ V)
  · exact (le_sup_right : V ≤ U ⊔ V)

/-- The map from the smooth singular simplices of `M` lying in `U` or in `V` to the smooth
singular simplices of `U ⊔ V`: such a simplex lies in `U ⊔ V`, and is smooth there. It is
determined by `TauCeti.smallSmoothSingularSubcomplexToSup_smoothSingularSubcomplexMap`. -/
def smallSmoothSingularSubcomplexToSup (U V : Opens M) :
    (smallSmoothSingularSubcomplex I ![(U : Set M), (V : Set M)] : SSet) ⟶
      (smoothSingularSubcomplex I (U ⊔ V : Opens M) : SSet) :=
  homOfLE (smallSmoothSingularSubcomplex_le_range I U V) ≫
    inv (toRange (smoothSingularSubcomplexToM I (U ⊔ V)))

/-- Followed by the map of smooth singular subcomplexes induced by `U ⊔ V ⊆ M`,
`TauCeti.smallSmoothSingularSubcomplexToSup` is the inclusion of the small smooth simplices
among all smooth simplices of `M`. -/
@[reassoc (attr := simp)]
theorem smallSmoothSingularSubcomplexToSup_smoothSingularSubcomplexMap (U V : Opens M) :
    smallSmoothSingularSubcomplexToSup I U V ≫
        smoothSingularSubcomplexMap (Subtype.val : (U ⊔ V : Opens M) → M)
          (contMDiff_subtypeVal (I := I)) =
      SSet.Subcomplex.homOfLE (smallSmoothSingularSubcomplex_le_smoothSingularSubcomplex I _) := by
  have hg : inv (toRange (smoothSingularSubcomplexToM I (U ⊔ V))) ≫
      smoothSingularSubcomplexToM I (U ⊔ V) =
        (range (smoothSingularSubcomplexToM I (U ⊔ V))).ι := by
    rw [IsIso.inv_comp_eq, toRange_ι]
  rw [← cancel_mono (smoothSingularSubcomplex I M).ι, Category.assoc,
    smoothSingularSubcomplexMap_subtypeVal_ι, smallSmoothSingularSubcomplexToSup, Category.assoc,
    hg, homOfLE_ι, homOfLE_ι]

/-- On the smooth simplices of an open set `W ≤ U ⊔ V` contained in `U` or in `V`,
`TauCeti.smallSmoothSingularSubcomplexToSup` is the map of smooth singular subcomplexes induced by
the inclusion of `W` in `U ⊔ V`. -/
theorem toSmallSmoothSingularSubcomplex_smallSmoothSingularSubcomplexToSup (U V : Opens M)
    {W : Opens M} (hW : W ≤ U ⊔ V) {i : Fin 2}
    (hi : (W : Set M) ⊆ ![(U : Set M), (V : Set M)] i) :
    toSmallSmoothSingularSubcomplex I ![(U : Set M), (V : Set M)] hi ≫
        smallSmoothSingularSubcomplexToSup I U V =
      smoothSingularSubcomplexMap (Opens.inclusion hW) (contMDiff_inclusion (I := I) hW) := by
  rw [← cancel_mono (smoothSingularSubcomplexMap (Subtype.val : (U ⊔ V : Opens M) → M)
    (contMDiff_subtypeVal (I := I))), Category.assoc,
    smallSmoothSingularSubcomplexToSup_smoothSingularSubcomplexMap,
    toSmallSmoothSingularSubcomplex_homOfLE_left, ← smoothSingularSubcomplexMap_comp]
  -- `Subtype.val ∘ Opens.inclusion hW` is `Subtype.val` by definition.
  rfl

/-- On the smooth simplices of `U`, `TauCeti.smallSmoothSingularSubcomplexToSup` is the map of
smooth singular subcomplexes induced by the inclusion of `U` in `U ⊔ V`. -/
@[reassoc (attr := simp)]
theorem toSmallSmoothSingularSubcomplex_smallSmoothSingularSubcomplexToSup_left (U V : Opens M) :
    toSmallSmoothSingularSubcomplex I ![(U : Set M), (V : Set M)] (i := 0)
        (Matrix.cons_val_zero (U : Set M) ![(V : Set M)]).superset ≫
      smallSmoothSingularSubcomplexToSup I U V =
    smoothSingularSubcomplexMap (Opens.inclusion (le_sup_left : U ≤ U ⊔ V))
      (contMDiff_inclusion (I := I) _) :=
  toSmallSmoothSingularSubcomplex_smallSmoothSingularSubcomplexToSup I U V le_sup_left _

/-- On the smooth simplices of `V`, `TauCeti.smallSmoothSingularSubcomplexToSup` is the map of
smooth singular subcomplexes induced by the inclusion of `V` in `U ⊔ V`. -/
@[reassoc (attr := simp)]
theorem toSmallSmoothSingularSubcomplex_smallSmoothSingularSubcomplexToSup_right
    (U V : Opens M) :
    toSmallSmoothSingularSubcomplex I ![(U : Set M), (V : Set M)] (i := 1)
        ((Matrix.cons_val_one (U : Set M) ![(V : Set M)]).trans
          (Matrix.cons_val_zero (V : Set M) ![])).superset ≫
      smallSmoothSingularSubcomplexToSup I U V =
    smoothSingularSubcomplexMap (Opens.inclusion (le_sup_right : V ≤ U ⊔ V))
      (contMDiff_inclusion (I := I) _) :=
  toSmallSmoothSingularSubcomplex_smallSmoothSingularSubcomplexToSup I U V le_sup_right _

section Cohomology

variable {C : Type v} [Category.{w} C] [HasCoproducts.{u} C] [Abelian C] (R : C)
  (k : Type*) [Ring k] [Linear k C] (Y : C)

/-- Restricting singular cochains of `M` to `U ⊔ V`, then to its smooth simplices, then to the
smooth simplices of `M` lying in `U` or in `V`, is restriction to the smooth simplices of `M` lying
in `U` or in `V`. -/
@[reassoc]
theorem singularCohomologyMap_subtypeVal_comp_smallSmoothSingularSubcomplexToSup
    (U V : Opens M) (n : ℕ) :
    TopCat.singularCohomologyMap (R := R) (k := k) (M := Y)
        (TopCat.ofHom (ContinuousMap.subtypeVal ((U ⊔ V : Opens M) : Set M))) n ≫
      HomologicalComplex.homologyMap (SSet.cochainComplexMap
        (smoothSingularSubcomplex I (U ⊔ V : Opens M)).ι) n ≫
      HomologicalComplex.homologyMap
        (SSet.cochainComplexMap (smallSmoothSingularSubcomplexToSup I U V)) n =
    HomologicalComplex.homologyMap (SSet.cochainComplexMap
      (smallSmoothSingularSubcomplex I ![(U : Set M), (V : Set M)]).ι) n := by
  rw [TopCat.singularCohomologyMap, TopCat.singularCochainComplexMap,
    ← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    ← SSet.cochainComplexMap_comp, ← SSet.cochainComplexMap_comp,
    Category.assoc, ← smoothSingularSubcomplexMap_subtypeVal_ι,
    smallSmoothSingularSubcomplexToSup_smoothSingularSubcomplexMap_assoc, homOfLE_ι]

end Cohomology

end Simplices

end TauCeti
