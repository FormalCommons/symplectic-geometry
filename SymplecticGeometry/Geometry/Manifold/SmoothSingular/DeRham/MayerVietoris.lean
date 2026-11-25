/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.MayerVietoris.Basic
public import TauCeti.Geometry.Manifold.DeRham.MayerVietoris
public import TauCeti.Geometry.Manifold.SmoothSingular.DeRham
public import TauCeti.Geometry.Manifold.SmoothSingular.MayerVietoris

/-!
# Integration and the Mayer–Vietoris sequences

Let `U` and `V` be open subsets of a smooth manifold `M`, and `W = U ⊔ V`. This file compares
the de Rham Mayer–Vietoris sequence `Ω^•(W) ⟶ Ω^•(U) ⊞ Ω^•(V) ⟶ Ω^•(U ⊓ V)`
(`TauCeti.mayerVietorisShortComplex`) with the cochain Mayer–Vietoris sequence
(`SSet.mayerVietorisCochainShortComplex`) of the pushout square of smooth singular subcomplexes
of `U ⊓ V`, `U`, `V` and of the smooth simplices of `M` lying in `U` or in `V`
(`TauCeti.isPushout_smoothSingularSubcomplex_inter_smallSmoothSingularSubcomplex`), with real
coefficients.

A smooth simplex of `M` lying in `U` or in `V` lies in `W`, and is smooth there; this gives a map
of simplicial sets `TauCeti.smallSmoothSingularSubcomplexToSup` from the corner of that pushout
square to the smooth singular simplices of `W`. On `U` (resp. `V`) it restricts to the map of
smooth singular subcomplexes induced by the inclusion of `U` (resp. `V`) in `W`.

Integration of forms over smooth simplices (`TauCeti.deRhamIntegration`) on `U`, `V` and `U ⊓ V`,
and on `W` followed by restriction along that map, is a morphism of short complexes
(`TauCeti.deRhamIntegrationMayerVietoris`). Both sequences take "restriction to `U` minus
restriction to `V`" for their second map, so no sign enters. The naturality of the connecting
morphism of the homology sequence then shows that integration intertwines the de Rham
Mayer–Vietoris connecting map `TauCeti.deRhamCohomology.mayerVietorisδ` with the cochain
Mayer–Vietoris connecting map `SSet.mayerVietorisCochainδ`, with sign `+1`
(`TauCeti.deRhamCohomology.ofHom_mayerVietorisδ_comp_homologyMap_deRhamIntegration`).

The map `TauCeti.smallSmoothSingularSubcomplexToSup`, the lemma that it lands in the range of
`U ⊔ V`, and `TauCeti.smallSmoothSingularSubcomplexToSup_smoothSingularSubcomplexMap` adapt Tau
Ceti's `TopCat.smallSingularSubcomplexToUnion`, its private `smallSubcomplex_le_range` and
`TopCat.smallSingularSubcomplexToUnion_comp` from continuous to smooth simplices. The proofs about
integration follow Tau Ceti's `TauCeti.smoothMayerVietorisδ_ι` and
`SSet.mayerVietorisCochainδ_naturality`, which build a morphism of short complexes and apply
`HomologicalComplex.HomologySequence.δ_naturality` in the same way.

## Main results

* `TauCeti.smallSmoothSingularSubcomplexToSup`: the map from the smooth simplices of `M` lying in
  `U` or in `V` to the smooth singular simplices of `U ⊔ V`.
* `TauCeti.deRhamIntegrationMayerVietoris`: integration as a morphism from the de Rham
  Mayer–Vietoris sequence to the cochain Mayer–Vietoris sequence of small smooth simplices.
* `TauCeti.deRhamCohomology.ofHom_mayerVietorisδ_comp_homologyMap_deRhamIntegration`: integration
  commutes with the two Mayer–Vietoris connecting maps.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 18, proof of Theorem 18.14.
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace
open scoped Manifold ContDiff

namespace TauCeti

section Simplices

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

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

end Simplices

variable {E H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) {M : Type} [TopologicalSpace M] [ChartedSpace H M]

section Integration

variable [IsManifold I 2 M]

/-- **Integration maps the de Rham Mayer–Vietoris sequence to small smooth cochains.** For open
sets `U` and `V` of `M`, integration over smooth simplices on `U`, on `V` and on `U ⊓ V`, and on
`U ⊔ V` followed by restriction along `TauCeti.smallSmoothSingularSubcomplexToSup`, is a morphism
from the Mayer–Vietoris short complex of de Rham complexes to the cochain Mayer–Vietoris short
complex, with real coefficients, of the pushout square
`TauCeti.isPushout_smoothSingularSubcomplex_inter_smallSmoothSingularSubcomplex`. -/
def deRhamIntegrationMayerVietoris (U V : Opens M) :
    mayerVietorisShortComplex I U V ⟶
      SSet.mayerVietorisCochainShortComplex (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ)
        (isPushout_smoothSingularSubcomplex_inter_smallSmoothSingularSubcomplex I U V).toCommSq
    where
  τ₁ := deRhamIntegration I (U ⊔ V : Opens M) ≫
    SSet.cochainComplexMap (smallSmoothSingularSubcomplexToSup I U V)
  τ₂ := biprod.map (deRhamIntegration I U) (deRhamIntegration I V)
  τ₃ := deRhamIntegration I (U ⊓ V : Opens M)
  comm₁₂ := by
    unfold mayerVietorisShortComplex
    apply biprod.hom_ext <;>
      simp [deRhamIntegration_naturality, ← SSet.cochainComplexMap_comp]
  comm₂₃ := by
    unfold mayerVietorisShortComplex
    apply biprod.hom_ext' <;>
      simp [deRhamIntegration_naturality]

/-- The first component of `TauCeti.deRhamIntegrationMayerVietoris` is integration on `U ⊔ V`
followed by restriction to the smooth simplices lying in `U` or in `V`. -/
@[simp]
theorem deRhamIntegrationMayerVietoris_τ₁ (U V : Opens M) :
    (deRhamIntegrationMayerVietoris I U V).τ₁ = deRhamIntegration I (U ⊔ V : Opens M) ≫
      SSet.cochainComplexMap (smallSmoothSingularSubcomplexToSup I U V) := (rfl)

/-- The second component of `TauCeti.deRhamIntegrationMayerVietoris` is integration on `U`
and on `V`. -/
@[simp]
theorem deRhamIntegrationMayerVietoris_τ₂ (U V : Opens M) :
    (deRhamIntegrationMayerVietoris I U V).τ₂ =
      biprod.map (deRhamIntegration I U) (deRhamIntegration I V) := (rfl)

/-- The third component of `TauCeti.deRhamIntegrationMayerVietoris` is integration on
`U ⊓ V`. -/
@[simp]
theorem deRhamIntegrationMayerVietoris_τ₃ (U V : Opens M) :
    (deRhamIntegrationMayerVietoris I U V).τ₃ = deRhamIntegration I (U ⊓ V : Opens M) := (rfl)

end Integration

namespace deRhamCohomology

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

/-- **Integration commutes with the Mayer–Vietoris connecting maps.** For open sets `U` and `V`
of `M`, the de Rham Mayer–Vietoris connecting map `H^n_dR(U ⊓ V) → H^{n+1}_dR(U ⊔ V)` followed by
integration on `U ⊔ V` and restriction to the smooth simplices lying in `U` or in `V` equals
integration on `U ⊓ V` followed by the cochain Mayer–Vietoris connecting map of the pushout square
`TauCeti.isPushout_smoothSingularSubcomplex_inter_smallSmoothSingularSubcomplex`. The sign is
`+1`. -/
theorem ofHom_mayerVietorisδ_comp_homologyMap_deRhamIntegration (U V : Opens M) (n : ℕ) :
    ModuleCat.ofHom (mayerVietorisδ I U V n) ≫
        HomologicalComplex.homologyMap (deRhamIntegration I (U ⊔ V : Opens M)) (n + 1) ≫
          HomologicalComplex.homologyMap
            (SSet.cochainComplexMap (R := ModuleCat.of ℝ ℝ) (k := ℝ) (M := ModuleCat.of ℝ ℝ)
              (smallSmoothSingularSubcomplexToSup I U V)) (n + 1) =
      HomologicalComplex.homologyMap (deRhamIntegration I (U ⊓ V : Opens M)) n ≫
        SSet.mayerVietorisCochainδ (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ)
          (isPushout_smoothSingularSubcomplex_inter_smallSmoothSingularSubcomplex I U V) n
          (n + 1) := by
  rw [← HomologicalComplex.homologyMap_comp, ← deRhamIntegrationMayerVietoris_τ₁,
    ← deRhamIntegrationMayerVietoris_τ₃, ofHom_mayerVietorisδ,
    SSet.mayerVietorisCochainδ_def (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ) _ n (n + 1)]
  exact HomologicalComplex.HomologySequence.δ_naturality (deRhamIntegrationMayerVietoris I U V)
    _ _ n (n + 1) rfl

end deRhamCohomology

end TauCeti
