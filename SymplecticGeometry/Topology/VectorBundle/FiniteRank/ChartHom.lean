/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Topology.VectorBundle.FiniteRank.SMul

/-!
# Bundle morphisms from an operator field supported in one chart

Let `Z` and `W` be vector bundle cores over `B` with model fibres `F` and `G`, and let `i` and
`j` be charts of `Z` and `W`. A continuous field of operators `g : B → F →L[𝕜] G` whose closed
support lies in `Z.baseSet i ∩ W.baseSet j` is the expression, in the charts `i` and `j`, of a
coordinate morphism `VectorBundleCore.CoordinateHom.ofChart i j g hg hgs : CoordinateHom Z W`.
Its fibre map at `x` is `g x` read from chart `i` to chart `j`, that is
`W.coordChange j (W.indexAt x) x ∘L g x ∘L Z.coordChange (Z.indexAt x) i x`, at every point of
`B`; off the closed support of `g` it is zero.

* `VectorBundleCore.CoordinateHom.fiberMap_ofChart`: the fibre map;
* `VectorBundleCore.CoordinateHom.fiberMap_ofChart_of_notMem_tsupport`: it vanishes off the
  closed support of `g`;
* `VectorBundleCore.CoordinateHom.operator_ofChart`,
  `VectorBundleCore.CoordinateHom.operator_ofChart_self`: its chart operators, which are `g` in
  the charts `i` and `j`;
* `VectorBundleCore.CoordinateHom.ofChart_zero`, `VectorBundleCore.CoordinateHom.ofChart_add`,
  `VectorBundleCore.CoordinateHom.ofChart_smul`: the construction is additive in `g` and commutes
  with multiplication by continuous scalar functions on the base;
* `TauCeti.FiniteRankBundleCore.fiberMap_ofChart`: for morphisms of Tau Ceti's finite-rank cores,
  where the chart at `x` is labelled by `x`, the fibre map at `x` is
  `D.core.coordChange j x x ∘L g x ∘L A.core.coordChange x i x`.

Together with partitions of unity subordinate to the chart domains, this patches operators given
in local charts into global bundle morphisms. Continuity is checked separately on the chart
domains and off the closed support of `g`, as in Tau Ceti's `ContinuousOn.smul_section_of_tsupport`.

## References

* [A. Hatcher, *Vector Bundles and K-Theory*][Hatcher2017], §1.1 (bundle maps).
-/

public section

open Bundle CategoryTheory

namespace VectorBundleCore.CoordinateHom

variable {𝕜 B F G ι κ : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {Z : VectorBundleCore 𝕜 B F ι} {W : VectorBundleCore 𝕜 B G κ}

/-- On the common domain of charts `k` and `l`, the field `g`, read from chart `i` to chart `j`
at each point, is expressed in the charts `k` and `l` by the transitions from `k` to `i` and from
`j` to `l`, provided the closed support of `g` lies in the domains of `i` and `j`. -/
private theorem inChartCoordinates_ofChart_eq {i : ι} {j : κ} {g : B → F →L[𝕜] G}
    (hgs : tsupport g ⊆ Z.baseSet i ∩ W.baseSet j) {k : ι} {l : κ} {x : B}
    (hx : x ∈ Z.baseSet k ∩ W.baseSet l) :
    Z.inChartCoordinates W k l x
        ((W.coordChange j (W.indexAt x) x).comp ((g x).comp (Z.coordChange (Z.indexAt x) i x))) =
      (W.coordChange j l x).comp ((g x).comp (Z.coordChange k i x)) := by
  by_cases hxg : x ∈ tsupport g
  · obtain ⟨hi, hj⟩ := hgs hxg
    ext v
    simp only [inChartCoordinates_apply, ContinuousLinearMap.comp_apply,
      Z.coordChange_comp k (Z.indexAt x) i x ⟨⟨hx.1, Z.mem_baseSet_at x⟩, hi⟩,
      W.coordChange_comp j (W.indexAt x) l x ⟨⟨hj, W.mem_baseSet_at x⟩, hx.2⟩]
  · simp [image_eq_zero_of_notMem_tsupport hxg, inChartCoordinates_def]

/-- The field `g`, read from chart `i` to chart `j` at each point, is a continuous section of the
Hom bundle when `g` is continuous with closed support in the domains of `i` and `j`. -/
private theorem continuous_ofChart_aux {i : ι} {j : κ} {g : B → F →L[𝕜] G} (hg : Continuous g)
    (hgs : tsupport g ⊆ Z.baseSet i ∩ W.baseSet j) :
    Continuous fun x ↦ TotalSpace.mk' (F →L[𝕜] G) (E := fun y ↦ Z.Fiber y →L[𝕜] W.Fiber y) x
      ((W.coordChange j (W.indexAt x) x).comp ((g x).comp (Z.coordChange (Z.indexAt x) i x))) := by
  refine continuous_hom_bundle_iff_forall_continuousOn.2 fun k l ↦ ?_
  set U : Set B := Z.baseSet k ∩ W.baseSet l ∩ (Z.baseSet i ∩ W.baseSet j)
  have hU : IsOpen U := ((Z.isOpen_baseSet k).inter (W.isOpen_baseSet l)).inter
    ((Z.isOpen_baseSet i).inter (W.isOpen_baseSet j))
  have hon : ContinuousOn
      (fun x ↦ (W.coordChange j l x).comp ((g x).comp (Z.coordChange k i x))) U :=
    ((W.continuousOn_coordChange j l).mono fun _ (hx : _ ∈ U) ↦ ⟨hx.2.2, hx.1.2⟩).clm_comp
      (hg.continuousOn.clm_comp
        ((Z.continuousOn_coordChange k i).mono fun _ (hx : _ ∈ U) ↦ ⟨hx.1.1, hx.2.1⟩))
  have hoff : ContinuousOn
      (fun x ↦ (W.coordChange j l x).comp ((g x).comp (Z.coordChange k i x))) (tsupport g)ᶜ :=
    (continuousOn_const (c := (0 : F →L[𝕜] G))).congr fun x (hx : x ∉ tsupport g) ↦ by
      simp [image_eq_zero_of_notMem_tsupport hx]
  refine ((hon.union_of_isOpen hoff hU (isClosed_tsupport g).isOpen_compl).mono
    fun x hx ↦ ?_).congr fun x hx ↦ inChartCoordinates_ofChart_eq hgs hx
  by_cases hxg : x ∈ tsupport g
  · exact Or.inl ⟨hx, hgs hxg⟩
  · exact Or.inr hxg

/-- The coordinate morphism `Z → W` given by a continuous field of operators `g` in the charts
`i` of `Z` and `j` of `W`, when the closed support of `g` lies in the domains of both charts: its
fibre map at `x` is `g x` read from chart `i` to chart `j`, and it vanishes off the support. -/
def ofChart (i : ι) (j : κ) (g : B → F →L[𝕜] G) (hg : Continuous g)
    (hgs : tsupport g ⊆ Z.baseSet i ∩ W.baseSet j) : CoordinateHom Z W :=
  ofContinuous _ (continuous_ofChart_aux hg hgs)

variable {i : ι} {j : κ} {g : B → F →L[𝕜] G} {hg : Continuous g}
  {hgs : tsupport g ⊆ Z.baseSet i ∩ W.baseSet j}

/-- The fibre map of `ofChart i j g hg hgs` at `x` is `g x` read from chart `i` to chart `j`. -/
@[simp]
theorem fiberMap_ofChart (x : B) :
    (ofChart i j g hg hgs).fiberMap x =
      (W.coordChange j (W.indexAt x) x).comp ((g x).comp (Z.coordChange (Z.indexAt x) i x)) :=
  congrFun (fiberMap_ofContinuous _ _) x

/-- The fibre map of `ofChart i j g hg hgs` vanishes off the closed support of `g`. -/
theorem fiberMap_ofChart_of_notMem_tsupport {x : B} (hx : x ∉ tsupport g) :
    (ofChart i j g hg hgs).fiberMap x = 0 := by
  rw [fiberMap_ofChart, image_eq_zero_of_notMem_tsupport hx, ContinuousLinearMap.zero_comp,
    ContinuousLinearMap.comp_zero]

/-- The chart operators of `ofChart i j g hg hgs` in charts `k` and `l` are `g` composed with the
transitions from `k` to `i` and from `j` to `l`. -/
theorem operator_ofChart (k : ι) (l : κ) (x : ↥(Z.baseSet k ∩ W.baseSet l)) :
    (ofChart i j g hg hgs).operator k l x =
      (W.coordChange j l x).comp ((g x).comp (Z.coordChange k i x)) := by
  rw [operator_eq, fiberMap_ofChart, inChartCoordinates_ofChart_eq hgs x.property]

/-- In the charts `i` and `j`, the chart operator of `ofChart i j g hg hgs` is `g`. -/
theorem operator_ofChart_self (x : ↥(Z.baseSet i ∩ W.baseSet j)) :
    (ofChart i j g hg hgs).operator i j x = g x := by
  ext v
  rw [operator_ofChart, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    Z.coordChange_self i x x.property.1, W.coordChange_self j x x.property.2]

/-- The zero operator field gives the zero morphism. -/
@[simp]
theorem ofChart_zero (h : tsupport (0 : B → F →L[𝕜] G) ⊆ Z.baseSet i ∩ W.baseSet j) :
    ofChart i j 0 continuous_zero h = 0 :=
  fiberMap_injective <| funext fun x ↦ by simp

/-- `ofChart` is additive in the operator field. -/
theorem ofChart_add {g' : B → F →L[𝕜] G} (hg' : Continuous g')
    (hgs' : tsupport g' ⊆ Z.baseSet i ∩ W.baseSet j) :
    ofChart i j (g + g') (hg.add hg')
        ((tsupport_add g g').trans (Set.union_subset hgs hgs')) =
      ofChart i j g hg hgs + ofChart i j g' hg' hgs' :=
  fiberMap_injective <| funext fun x ↦ by
    simp only [fiberMap_add, fiberMap_ofChart, Pi.add_apply, ContinuousLinearMap.add_comp,
      ContinuousLinearMap.comp_add]

/-- `ofChart` commutes with multiplication by a continuous scalar function on the base. -/
theorem ofChart_smul (c : C(B, 𝕜)) :
    ofChart i j (fun x ↦ c x • g x) (c.continuous.smul hg)
        ((tsupport_smul_subset_right (fun x ↦ c x) g).trans hgs) =
      c • ofChart i j g hg hgs :=
  fiberMap_injective <| funext fun x ↦ by
    simp only [fiberMap_smul, fiberMap_ofChart, ContinuousLinearMap.smul_comp,
      ContinuousLinearMap.comp_smul]

end VectorBundleCore.CoordinateHom

namespace TauCeti.FiniteRankBundleCore

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]
  {A D : FiniteRankBundleCore 𝕜 B}

/-- For finite-rank cores, the fibre map at `x` of the morphism given by an operator field `g` in
charts `i` and `j` is `g x` composed with the transitions from the chart at `x` to `i` and from `j`
to the chart at `x`. -/
@[simp high]
theorem fiberMap_ofChart (i j : B) (g : B → (Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜))
    (hg : Continuous g) (hgs : tsupport g ⊆ A.core.baseSet i ∩ D.core.baseSet j) (x : B) :
    (VectorBundleCore.CoordinateHom.ofChart i j g hg hgs : A ⟶ D).fiberMap x =
      (D.core.coordChange j x x).comp ((g x).comp (A.core.coordChange x i x)) := by
  rw [VectorBundleCore.CoordinateHom.fiberMap_ofChart, A.indexAt_eq, D.indexAt_eq]

end TauCeti.FiniteRankBundleCore

end
