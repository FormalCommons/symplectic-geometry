/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Boundary.Collar.Interior
public import SymplecticGeometry.Geometry.Manifold.Boundary.Collar.Local
public import SymplecticGeometry.Geometry.Manifold.IsManifold.InteriorBoundary
public import SymplecticGeometry.Geometry.Manifold.ModelTransport.InteriorModel
public import SymplecticGeometry.Geometry.Manifold.ModelTransport.Remodel
public import TauCeti.Geometry.Manifold.Boundary.Collar.Smooth
public import TauCeti.Geometry.Manifold.Gluing.GlueData
public import TauCeti.Geometry.Manifold.Immersion.Interior
public import TauCeti.Geometry.Manifold.Immersion.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.Immersion.ModelChange
public import TauCeti.Topology.Category.TopCat.GlueData
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.Basic
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.OpenSubset

/-!
# Attaching an end along a smooth collar

For a manifold `W` with boundary, modelled on the half-space, and a smooth collar `c` of its
boundary, `c.WithEnd` is `W` with the half-cylinder `[0, ∞) × ∂W` attached along `∂W`. It is the
open gluing (`TopCat.GlueData`) of two pieces over `ℝⁿ⁺¹`: the interior of `W`, re-modelled as
`SymplecticGeometry.InteriorModel`, and `(-1, ∞) × ∂W`, re-modelled along a linear equivalence
(`SymplecticGeometry.Remodel`), glued by `(s, x) ↦ c (x, -s)` for `s ∈ (-1, 0)`. The gluing
maps are read in the collar coordinates `TauCeti.SmoothCollar.interiorModelCoord`
(`Boundary/Collar/Interior.lean`). It is a boundaryless smooth manifold, Hausdorff when `W` is;
no compactness is assumed.

## Main definitions

* `TauCeti.SmoothCollar.WithEnd`: the manifold `W ∪ ([0, ∞) × ∂W)`.
* `TauCeti.SmoothCollar.WithEnd.inclusion`, `WithEnd.endMap`: the maps from `W` and `ℝ × ∂W`.
* `TauCeti.SmoothCollar.WithEnd.retraction`: the retraction onto `W` collapsing the end onto `∂W`.

## Main results

* `TauCeti.SmoothCollar.WithEnd.isSmoothEmbedding_inclusion`, `isClosedEmbedding_inclusion`.
* `TauCeti.SmoothCollar.WithEnd.isLocalDiffeomorphOn_endMap`, `injOn_endMap`,
  `endMap_neg_eq_inclusion`: on `(-1, 0]`, `endMap (s, x)` is `c (x, -s)`.
* `TauCeti.SmoothCollar.WithEnd.range_inclusion_union`, `disjoint_range_inclusion_endMap_image`,
  `isOpenCover`.

The retraction descends through `Multicoequalizer.desc` as in Tau Ceti's
`TopCat.GlueData.IsCompatible.descContMDiffMap`; the boundary immersion changes models as in
`isImmersionAt_chordDisc_of_mem` (Tau Ceti, `KnotTheory/Slice/ConnectedSum.lean`).

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §3.5, p. 148.
* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Springer GTM 218, 2013,
  Chapter 1 (the smooth manifold chart lemma).
-/

public section

open Set Function Topology Manifold TopologicalSpace CategoryTheory SymplecticGeometry
open scoped Manifold ContDiff

noncomputable section

namespace TauCeti.SmoothCollar
open _root_.TauCeti.EuclideanHalfSpace

/-- The open half-line `(-1, ∞)`, the range of the first coordinate of the end piece. -/
private def endInterval : Opens ℝ := ⟨Ioi (-1), isOpen_Ioi⟩

@[simp] private theorem mem_endInterval {s : ℝ} : s ∈ endInterval ↔ -1 < s := Iff.rfl

/-- The point `-t` of `(-1, ∞)` for a depth `t ∈ [0, 1)`. -/
private def negNormalCoord (t : normalIioOpens 1) : endInterval :=
  ⟨-(t : EuclideanHalfSpace 1).val 0, by
    have := mem_normalIioOpens.1 t.property
    rw [mem_endInterval]
    linarith⟩

@[simp] private theorem coe_negNormalCoord (t : normalIioOpens 1) :
    (negNormalCoord t : ℝ) = -(t : EuclideanHalfSpace 1).val 0 := rfl

/-- The linear form `u ↦ -u 0` on `ℝ¹`, as an equivalence. -/
private def negCoordEquiv : EuclideanSpace ℝ (Fin 1) ≃L[ℝ] ℝ :=
  ((EuclideanSpace.equiv (Fin 1) ℝ).trans (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ)).trans
    (ContinuousLinearEquiv.neg ℝ)

private theorem continuous_negNormalCoord : Continuous negNormalCoord :=
  Continuous.subtype_mk (by fun_prop) _

private theorem isImmersionAt_negNormalCoord (t : normalIioOpens 1) :
    IsImmersionAt (𝓡∂ 1) 𝓘(ℝ) ∞ negNormalCoord t := by
  have hf : ∀ t : normalIioOpens 1, -(t : EuclideanHalfSpace 1).val 0 ∈ endInterval :=
    fun t ↦ (negNormalCoord t).property
  refine (isImmersionAt_codRestrict_opens_iff (U := endInterval)
    (f := fun t : normalIioOpens 1 ↦ -(t : EuclideanHalfSpace 1).val 0) hf).2 ?_
  refine (isImmersionAt_comp_subtypeVal_iff
    (f := fun t : EuclideanHalfSpace 1 ↦ -t.val 0)).2 ?_
  refine (IsImmersionAtOfComplement.mk_of_continuousAt_of_extChartAt (F := PUnit.{1})
    (by fun_prop) ((ContinuousLinearEquiv.prodUnique ℝ _ _).trans negCoordEquiv)
    ?_).isImmersionAt
  intro u hu
  have h0 : 0 ≤ u 0 := by
    have := (extChartAt_target_subset_range (I := 𝓡∂ 1) (t : EuclideanHalfSpace 1)) hu
    rwa [range_modelWithCornersEuclideanHalfSpace] at this
  simp [modelWithCornersEuclideanHalfSpace_symm_apply_of_le h0, negCoordEquiv]

private theorem isLocalDiffeomorphAt_negNormalCoord {t : normalIioOpens 1}
    (ht : 0 < (t : EuclideanHalfSpace 1).val 0) :
    IsLocalDiffeomorphAt (𝓡∂ 1) 𝓘(ℝ) ∞ negNormalCoord t := by
  have hg : IsLocalDiffeomorphAt (𝓡∂ 1) 𝓘(ℝ) ∞
      (fun s : EuclideanHalfSpace 1 ↦ -s.val 0) t := by
    have := (isLocalDiffeomorphAt_val_zero ht).comp
      (hg := (ContinuousLinearEquiv.neg ℝ (M := ℝ)).toDiffeomorph.isLocalDiffeomorph _)
    simpa [comp_def] using this
  refine isLocalDiffeomorphAt_subtypeVal_comp_iff.1 ?_
  exact (isLocalDiffeomorph_subtype_val t).comp (hg := hg)

private def endModelEquiv (n : ℕ) :
    (ℝ × EuclideanSpace ℝ (Fin n)) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
  (ContinuousLinearEquiv.prodComm ℝ ℝ (EuclideanSpace ℝ (Fin n))).trans
    (euclideanHalfSpaceBoundaryNormalEquiv n)

private def endModelDiffeomorph (n : ℕ) :
    ModelProd ℝ (EuclideanSpace ℝ (Fin n)) ≃ₘ^∞⟮𝓘(ℝ).prod (𝓡 n), 𝓡 (n + 1)⟯
      EuclideanSpace ℝ (Fin (n + 1)) where
  toEquiv := (endModelEquiv n).toEquiv
  contMDiff_toFun := by
    rw [← modelWithCornersSelf_prod]
    exact (endModelEquiv n).contDiff.contMDiff
  contMDiff_invFun := by
    rw [← modelWithCornersSelf_prod]
    exact (endModelEquiv n).symm.contDiff.contMDiff

/-- The depth `max (-s) 0` as a point of `[0, 1)`. -/
private def collarDepth (s : endInterval) : normalIioOpens 1 :=
  normalIioRay ⟨-s, neg_lt.1 (mem_endInterval.1 s.property)⟩

private theorem continuous_collarDepth : Continuous collarDepth :=
  continuous_normalIioRay.comp ((continuous_neg.comp continuous_subtypeVal).subtype_mk _)

@[simp] private theorem collarDepth_negNormalCoord (t : normalIioOpens 1) :
    collarDepth (negNormalCoord t) = t :=
  Subtype.ext (by simp [collarDepth])

private theorem negNormalCoord_collarDepth {s : endInterval} (hs : (s : ℝ) ≤ 0) :
    negNormalCoord (collarDepth s) = s :=
  Subtype.ext (by simp [collarDepth, max_eq_left (neg_nonneg.2 hs)])

private theorem collarDepth_val_pos {s : endInterval} (hs : (s : ℝ) < 0) :
    0 < (collarDepth s : EuclideanHalfSpace 1).val 0 := by
  simp [collarDepth, hs]

universe u

variable {n : ℕ} {W : Type u} [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
  [IsManifold (𝓡∂ (n + 1)) ∞ W]

local instance : IsManifold (𝓡 n) ∞ ((𝓡∂ (n + 1)).boundary W) := isManifold_boundary W

variable (n W) in
/-- The interior of `W`, as a boundaryless manifold over `ℝⁿ⁺¹`. -/
private abbrev InteriorPiece : Type u :=
  InteriorModel (𝓡∂ (n + 1)) ((𝓡∂ (n + 1)).interiorOpens W)

variable (n W) in
/-- The end piece `(-1, ∞) × ∂W`, re-modelled on `ℝⁿ⁺¹`. -/
private abbrev EndPiece : Type u :=
  Remodel (endModelDiffeomorph n) (endInterval × (𝓡∂ (n + 1)).boundary W)

variable (c : SmoothCollar n ∞ W)

section

omit [IsManifold (𝓡∂ (n + 1)) ∞ W]

/-- The part of the end piece with negative first coordinate. -/
private def endOverlap : Opens (EndPiece n W) :=
  ⟨{q : endInterval × (𝓡∂ (n + 1)).boundary W | (q.1 : ℝ) < 0},
    isOpen_lt (continuous_subtypeVal.comp continuous_fst) continuous_const⟩

/-- The coordinates of a point of the end piece. -/
private def EndPiece.coord (q : EndPiece n W) : endInterval × (𝓡∂ (n + 1)).boundary W := q

private theorem EndPiece.coord_eq (q : EndPiece n W) : q.coord = q := rfl

private theorem mem_endOverlap {q : EndPiece n W} :
    q ∈ endOverlap ↔ (q.coord.1 : ℝ) < 0 := Iff.rfl

/-- The collar point of a point of the end piece, the boundary point for nonnegative `s`. -/
private def endRetract (q : EndPiece n W) : W := c (q.coord.2, collarDepth q.coord.1)

private theorem endRetract_def (q : EndPiece n W) :
    c.endRetract q = c (q.coord.2, collarDepth q.coord.1) := rfl

private theorem endRetract_mk (s : endInterval) (x : (𝓡∂ (n + 1)).boundary W) :
    c.endRetract ((s, x) : endInterval × (𝓡∂ (n + 1)).boundary W) = c (x, collarDepth s) := rfl

private theorem continuous_endRetract : Continuous c.endRetract :=
  c.continuous.comp (continuous_snd.prodMk (continuous_collarDepth.comp continuous_fst))

/-- The end coordinates `(-t, x)` of collar coordinates `(x, t)`. -/
private def collarToEnd (p : ↥((𝓡∂ (n + 1)).boundary W) × normalIioOpens 1) :
    endInterval × (𝓡∂ (n + 1)).boundary W :=
  (negNormalCoord p.2, p.1)

private theorem collarToEnd_mk (x : (𝓡∂ (n + 1)).boundary W) (t : normalIioOpens 1) :
    collarToEnd (x, t) = (negNormalCoord t, x) := rfl

private theorem endRetract_collarToEnd (p : ↥((𝓡∂ (n + 1)).boundary W) × normalIioOpens 1) :
    c.endRetract (collarToEnd p) = c p := by
  obtain ⟨x, t⟩ := p
  rw [collarToEnd_mk, endRetract_mk, collarDepth_negNormalCoord]

end

/-- The point of the interior piece glued to a point of the end overlap. -/
private def endToInteriorPt (q : endOverlap (n := n) (W := W)) : InteriorPiece n W :=
  InteriorModel.mk (𝓡∂ (n + 1)) (c.endRetract q.val) (by
    rw [endRetract_def, apply_mem_interior_iff_pos]
    exact collarDepth_val_pos (mem_endOverlap.1 q.property))

private theorem endToInteriorPt_val (q : endOverlap (n := n) (W := W)) :
    (c.endToInteriorPt q).val = c.endRetract q.val :=
  InteriorModel.val_mk _ _

/-- The gluing map from the end overlap to the interior overlap. -/
private def endToInterior : C(endOverlap (n := n) (W := W), c.interiorModelRange) where
  toFun q := ⟨c.endToInteriorPt q, c.mem_interiorModelRange.2
    ⟨_, ((c.endToInteriorPt_val q).trans (c.endRetract_def q.val)).symm⟩⟩
  continuous_toFun := Continuous.subtype_mk
    (InteriorModel.isOpenEmbedding_val.isInducing.continuous_iff.2 (by
      simpa only [Function.comp_def, endToInteriorPt_val] using
        c.continuous_endRetract.comp continuous_subtypeVal)) _

private theorem endToInterior_val (q : endOverlap (n := n) (W := W)) :
    (c.endToInterior q).val.val = c.endRetract q.val :=
  c.endToInteriorPt_val q

/-- The point of the end piece with the collar coordinates of a point of the interior overlap. -/
private def interiorToEndPt (q : c.interiorModelRange) : EndPiece n W :=
  collarToEnd (c.interiorModelCoord q)

private theorem interiorToEndPt_def (q : c.interiorModelRange) :
    c.interiorToEndPt q = collarToEnd (c.interiorModelCoord q) := rfl

private theorem continuous_interiorToEndPt : Continuous c.interiorToEndPt :=
  (continuous_negNormalCoord.comp (continuous_snd.comp c.continuous_interiorModelCoord)).prodMk
    (continuous_fst.comp c.continuous_interiorModelCoord)

/-- The gluing map from the interior overlap to the end overlap. -/
private def interiorToEnd : C(c.interiorModelRange, endOverlap (n := n) (W := W)) where
  toFun q := ⟨c.interiorToEndPt q, neg_neg_of_pos (c.interiorModelCoord_snd_pos q)⟩
  continuous_toFun := c.continuous_interiorToEndPt.subtype_mk _

private theorem interiorToEnd_val (q : c.interiorModelRange) :
    (c.interiorToEnd q).val = c.interiorToEndPt q := rfl

private theorem interiorModelCoord_endToInterior (q : endOverlap (n := n) (W := W)) :
    c.interiorModelCoord (c.endToInterior q) = (q.val.coord.2, collarDepth q.val.coord.1) := by
  refine c.injective ?_
  rw [apply_interiorModelCoord, endToInterior_val, endRetract_def]

private theorem interiorToEnd_endToInterior (q : endOverlap (n := n) (W := W)) :
    c.interiorToEnd (c.endToInterior q) = q := by
  have hq : ((q.val.coord.1 : endInterval) : ℝ) ≤ 0 := le_of_lt (mem_endOverlap.1 q.property)
  apply Subtype.ext
  rw [interiorToEnd_val, interiorToEndPt_def, interiorModelCoord_endToInterior, collarToEnd_mk,
    negNormalCoord_collarDepth hq]
  exact Prod.mk.eta.trans (EndPiece.coord_eq _)

private theorem endToInterior_interiorToEnd (q : c.interiorModelRange) :
    c.endToInterior (c.interiorToEnd q) = q := by
  apply Subtype.ext
  apply InteriorModel.val_injective
  rw [endToInterior_val, interiorToEnd_val, interiorToEndPt_def, endRetract_collarToEnd,
    apply_interiorModelCoord]

/-- The pieces of the gluing. -/
private def piece (i : ULift.{u} Bool) : TopCat.{u} :=
  bif i.down then TopCat.of (EndPiece n W) else TopCat.of (InteriorPiece n W)

/-- The overlaps of the gluing. -/
private def overlap : ∀ i : ULift.{u} Bool, ULift.{u} Bool → Opens (piece (n := n) (W := W) i)
  | ⟨false⟩, ⟨false⟩ => ⊤
  | ⟨false⟩, ⟨true⟩ => c.interiorModelRange
  | ⟨true⟩, ⟨false⟩ => endOverlap
  | ⟨true⟩, ⟨true⟩ => ⊤

/-- The transition maps of the gluing. -/
private def transition : ∀ i j : ULift.{u} Bool,
    (Opens.toTopCat _).obj (c.overlap i j) ⟶ (Opens.toTopCat _).obj (c.overlap j i)
  | ⟨false⟩, ⟨false⟩ => 𝟙 _
  | ⟨false⟩, ⟨true⟩ => TopCat.ofHom c.interiorToEnd
  | ⟨true⟩, ⟨false⟩ => TopCat.ofHom c.endToInterior
  | ⟨true⟩, ⟨true⟩ => 𝟙 _

/-- The gluing data of `c.WithEnd`: the interior of `W` and `(-1, ∞) × ∂W`, glued along
`(s, x) ↦ c (x, -s)` for `s ∈ (-1, 0)`. -/
def glueData : TopCat.GlueData.{u} :=
  TopCat.GlueData.mk'
    { J := ULift.{u} Bool
      U := piece
      V := c.overlap
      t := c.transition
      V_id := by rintro ⟨_ | _⟩ <;> rfl
      t_id := by rintro ⟨_ | _⟩ <;> rfl
      t_inter := by
        rintro ⟨_ | _⟩ ⟨_ | _⟩ ⟨_ | _⟩ x hx <;>
          first | exact hx | exact (c.transition _ _ x).property | trivial
      cocycle := by
        rintro ⟨_ | _⟩ ⟨_ | _⟩ ⟨_ | _⟩ x hx <;>
          first
          | rfl
          | exact congrArg Subtype.val (c.endToInterior_interiorToEnd x)
          | exact congrArg Subtype.val (c.interiorToEnd_endToInterior x) }

omit [IsManifold (𝓡∂ (n + 1)) ∞ W] in
private theorem isLocalDiffeomorphAt_collarToEnd {p : ↥((𝓡∂ (n + 1)).boundary W) × normalIioOpens 1}
    (hp : 0 < (p.2 : EuclideanHalfSpace 1).val 0) :
    IsLocalDiffeomorphAt ((𝓡 n).prod (𝓡∂ 1)) (𝓘(ℝ).prod (𝓡 n)) ∞ collarToEnd p := by
  exact ((Diffeomorph.prodComm (𝓡 n) (𝓡∂ 1) _ _ ∞).isLocalDiffeomorph p).comp
    (hg := (isLocalDiffeomorphAt_negNormalCoord hp).prodMap
      ((Diffeomorph.refl (𝓡 n) _ ∞).isLocalDiffeomorph p.1))

private instance instChartedSpacePiece :
    ∀ i : ULift.{u} Bool, ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) (piece (n := n) (W := W) i)
  | ⟨false⟩ => inferInstanceAs (ChartedSpace _ (InteriorPiece n W))
  | ⟨true⟩ => inferInstanceAs (ChartedSpace _ (EndPiece n W))

private instance instIsManifoldPiece :
    ∀ i : ULift.{u} Bool, IsManifold (𝓡 (n + 1)) ∞ (piece (n := n) (W := W) i)
  | ⟨false⟩ => inferInstanceAs (IsManifold _ ∞ (InteriorPiece n W))
  | ⟨true⟩ => inferInstanceAs (IsManifold _ ∞ (EndPiece n W))

private instance (i : c.glueData.J) :
    ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) (c.glueData.U i) :=
  instChartedSpacePiece i

private instance (i : c.glueData.J) : IsManifold (𝓡 (n + 1)) ∞ (c.glueData.U i) :=
  instIsManifoldPiece i

private instance (p : c.glueData.J × c.glueData.J) :
    ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) (c.glueData.V p) :=
  letI := instChartedSpacePiece (n := n) (W := W) p.1
  (c.overlap p.1 p.2).instChartedSpace

private theorem isLocalDiffeomorph_interiorToEndPt :
    IsLocalDiffeomorph (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ c.interiorToEndPt := fun q ↦ by
  have h := ((c.isLocalDiffeomorph_interiorModelCoord q).comp
    (hg := isLocalDiffeomorphAt_collarToEnd (c.interiorModelCoord_snd_pos q))).comp
    (hg := (remodelDiffeomorph (endModelDiffeomorph n)
      (endInterval × (𝓡∂ (n + 1)).boundary W)).isLocalDiffeomorph _)
  convert h using 1
  funext q
  rw [comp_apply, coe_remodelDiffeomorph, remodelHomeomorph_apply, interiorToEndPt_def,
    comp_apply]

private theorem isLocalDiffeomorph_interiorToEnd :
    IsLocalDiffeomorph (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ c.interiorToEnd := fun q ↦
  isLocalDiffeomorphAt_subtypeVal_comp_iff.1 (c.isLocalDiffeomorph_interiorToEndPt q)

private theorem isLocalDiffeomorph_endToInterior :
    IsLocalDiffeomorph (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ c.endToInterior := fun q ↦ by
  refine IsLocalDiffeomorphAt.of_comp_left (f := c.interiorToEnd) ?_
    (c.isLocalDiffeomorph_interiorToEnd _) c.endToInterior.continuous.continuousAt
  have h : (c.interiorToEnd ∘ c.endToInterior : endOverlap (n := n) (W := W) → _) = id :=
    funext c.interiorToEnd_endToInterior
  rw [h]
  exact (Diffeomorph.refl (𝓡 (n + 1)) _ ∞).isLocalDiffeomorph q

private theorem isCompatible_glueData : c.glueData.IsCompatible (𝓡 (n + 1)) ∞ := by
  refine .of_isLocalDiffeomorph_t (fun i j ↦ isLocalDiffeomorph_subtype_val) ?_
  rintro ⟨_ | _⟩ ⟨_ | _⟩
  · exact (Diffeomorph.refl (𝓡 (n + 1)) _ ∞).isLocalDiffeomorph
  · exact c.isLocalDiffeomorph_interiorToEnd
  · exact c.isLocalDiffeomorph_endToInterior
  · exact (Diffeomorph.refl (𝓡 (n + 1)) _ ∞).isLocalDiffeomorph

/-- The manifold `W ∪ ([0, ∞) × ∂W)` obtained from `W` by attaching the end `[0, ∞) × ∂W` along
the smooth collar `c`: the interior of `W` and `(-1, ∞) × ∂W`, glued along
`(s, x) ↦ c (x, -s)` for `s ∈ (-1, 0)`. -/
def WithEnd : Type u := c.glueData.toGlueData.glued

instance : TopologicalSpace c.WithEnd :=
  inferInstanceAs (TopologicalSpace c.glueData.toGlueData.glued)

/-- The atlas of `c.WithEnd`, transported from the atlases of its two pieces. -/
@[instance_reducible]
def chartedSpaceWithEnd : ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) c.WithEnd :=
  c.glueData.chartedSpace (EuclideanSpace ℝ (Fin (n + 1)))

instance : ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) c.WithEnd := c.chartedSpaceWithEnd

instance : IsManifold (𝓡 (n + 1)) ∞ c.WithEnd := c.isCompatible_glueData.isManifold

/-- The canonical map of the interior piece into `c.WithEnd`. -/
private def interiorIncl : InteriorPiece n W → c.WithEnd := c.glueData.toGlueData.ι ⟨false⟩

/-- The canonical map of the end piece into `c.WithEnd`. -/
private def endIncl : EndPiece n W → c.WithEnd := c.glueData.toGlueData.ι ⟨true⟩

private theorem isOpenEmbedding_interiorIncl : IsOpenEmbedding c.interiorIncl :=
  c.glueData.ι_isOpenEmbedding ⟨false⟩

private theorem isLocalDiffeomorph_interiorIncl :
    IsLocalDiffeomorph (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ c.interiorIncl :=
  c.isCompatible_glueData.isLocalDiffeomorph_ι ⟨false⟩

private theorem isLocalDiffeomorph_endIncl :
    IsLocalDiffeomorph (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ c.endIncl :=
  c.isCompatible_glueData.isLocalDiffeomorph_ι ⟨true⟩

private theorem interiorIncl_or_endIncl (z : c.WithEnd) :
    (∃ p, c.interiorIncl p = z) ∨ ∃ q, c.endIncl q = z := by
  obtain ⟨⟨_ | _⟩, y, rfl⟩ := c.glueData.ι_jointly_surjective z
  exacts [Or.inl ⟨y, rfl⟩, Or.inr ⟨y, rfl⟩]

private theorem endIncl_eq_interiorIncl_iff {q : EndPiece n W} {p : InteriorPiece n W} :
    c.endIncl q = c.interiorIncl p ↔
      ∃ h : q ∈ endOverlap, (c.endToInterior ⟨q, h⟩ : InteriorPiece n W) = p := by
  refine (c.glueData.ι_eq_iff_rel ⟨true⟩ ⟨false⟩ q p).trans ⟨?_, ?_⟩
  · rintro ⟨⟨x, hxm⟩, hx, h⟩
    have hx' : x = q := hx
    have hq : q ∈ endOverlap := hx' ▸ hxm
    refine ⟨hq, ?_⟩
    rw [show (⟨q, hq⟩ : endOverlap (n := n) (W := W)) = ⟨x, hxm⟩ from Subtype.ext hx'.symm]
    exact h
  · rintro ⟨h, rfl⟩
    exact ⟨⟨q, h⟩, rfl, rfl⟩

private theorem endRetract_interiorToEndPt (q : c.interiorModelRange) :
    c.endRetract (c.interiorToEndPt q) = q.val.val := by
  rw [interiorToEndPt_def, endRetract_collarToEnd, apply_interiorModelCoord]

private theorem endRetract_eq_val_endToInterior (q : endOverlap (n := n) (W := W)) :
    c.endRetract q.val = (c.endToInterior q : InteriorPiece n W).val :=
  (c.endToInterior_val q).symm

omit [IsManifold (𝓡∂ (n + 1)) ∞ W] in
private theorem endRetract_mem_boundary {q : EndPiece n W} (hq : q ∉ endOverlap) :
    c.endRetract q ∈ (𝓡∂ (n + 1)).boundary W := by
  have h0 : ((q.coord.1 : endInterval) : ℝ) ≥ 0 := not_lt.1 hq
  rw [endRetract_def, apply_mem_boundary_iff]
  apply Subtype.ext
  simp [collarDepth, h0]

private theorem exists_separation [T2Space W] (x : InteriorPiece n W) {y : EndPiece n W}
    (hy : y ∉ endOverlap) : ∃ A ∈ 𝓝 x, ∃ B ∈ 𝓝 y, ∀ z : InteriorPiece n W, z ∈ A →
      ∀ q : EndPiece n W, q ∈ B → c.endRetract q ≠ z.val := by
  have hne : x.val ≠ c.endRetract y := fun h ↦ by
    have hb := c.endRetract_mem_boundary hy
    rw [← h, ← ModelWithCorners.compl_interior] at hb
    exact hb x.val_mem_interior
  obtain ⟨A', B', hA', hB', hAB⟩ := t2_separation_nhds hne
  refine ⟨_, InteriorModel.continuous_val.continuousAt.preimage_mem_nhds hA', _,
    c.continuous_endRetract.continuousAt.preimage_mem_nhds hB', fun z hz q hq h ↦ ?_⟩
  exact Set.disjoint_left.1 hAB hz (h ▸ hq)

/-- `c.WithEnd` is Hausdorff when `W` is. -/
instance [T2Space W] : T2Space c.WithEnd := by
  refine c.glueData.t2Space_iff_forall_nhds.2 ⟨?_, ?_⟩
  · rintro ⟨_ | _⟩
    · exact inferInstanceAs (T2Space ((𝓡∂ (n + 1)).interiorOpens W))
    · exact inferInstanceAs (T2Space (endInterval × (𝓡∂ (n + 1)).boundary W))
  rintro ⟨_ | _⟩ ⟨_ | _⟩ x hx y hy
  · exact (hx ⟨⟨x, trivial⟩, rfl⟩).elim
  · have hy' : y ∉ endOverlap := fun h ↦ hy ⟨⟨y, h⟩, rfl⟩
    obtain ⟨A, hA, B, hB, hAB⟩ := c.exists_separation x hy'
    exact ⟨A, hA, B, hB, fun z hz hz' ↦
      hAB z.val hz _ hz' (c.endRetract_interiorToEndPt z)⟩
  · have hx' : x ∉ endOverlap := fun h ↦ hx ⟨⟨x, h⟩, rfl⟩
    obtain ⟨A, hA, B, hB, hAB⟩ := c.exists_separation y hx'
    exact ⟨B, hB, A, hA, fun z hz hz' ↦
      hAB _ hz' z.val hz (c.endRetract_eq_val_endToInterior z)⟩
  · exact (hx ⟨⟨x, trivial⟩, rfl⟩).elim

private theorem endIncl_collarToEnd_eq {p : ↥((𝓡∂ (n + 1)).boundary W) × normalIioOpens 1}
    (hp : 0 < (p.2 : EuclideanHalfSpace 1).val 0) (hint : c p ∈ (𝓡∂ (n + 1)).interior W) :
    c.endIncl (collarToEnd p) = c.interiorIncl (InteriorModel.mk (𝓡∂ (n + 1)) (c p) hint) := by
  refine c.endIncl_eq_interiorIncl_iff.2 ⟨neg_neg_of_pos hp, ?_⟩
  apply InteriorModel.val_injective
  rw [InteriorModel.val_mk]
  exact (c.endToInterior_val _).trans (c.endRetract_collarToEnd p)

omit [IsManifold (𝓡∂ (n + 1)) ∞ W] in
/-- A point outside the image of a collar is an interior point. -/
theorem mem_interior_of_notMem_range {p : W} (hp : p ∉ range c) :
    p ∈ (𝓡∂ (n + 1)).interior W := by
  rw [← ModelWithCorners.compl_boundary]
  exact fun h ↦ hp (c.boundary_subset_range h)

namespace WithEnd

open Classical in
/-- The inclusion of `W` in `c.WithEnd`. -/
def inclusion (p : W) : c.WithEnd :=
  if h : p ∈ range c then
    c.endIncl (collarToEnd (c.diffeomorphOpensRange.symm ⟨p, c.mem_opensRange.2 h⟩))
  else c.interiorIncl (InteriorModel.mk (𝓡∂ (n + 1)) p (c.mem_interior_of_notMem_range h))

private theorem inclusion_apply_collar (p : ↥((𝓡∂ (n + 1)).boundary W) × normalIioOpens 1) :
    inclusion c (c p) = c.endIncl (collarToEnd p) := by
  simp only [inclusion, mem_range_self, ↓reduceDIte]
  congr 2
  apply c.diffeomorphOpensRange.symm_apply_eq.2
  exact Subtype.ext (c.coe_diffeomorphOpensRange_apply p).symm

private theorem inclusion_apply_of_mem_interior {p : W} (hp : p ∈ (𝓡∂ (n + 1)).interior W) :
    inclusion c p = c.interiorIncl (InteriorModel.mk (𝓡∂ (n + 1)) p hp) := by
  by_cases h : p ∈ range c
  · obtain ⟨q, rfl⟩ := h
    rw [inclusion_apply_collar]
    exact c.endIncl_collarToEnd_eq ((c.apply_mem_interior_iff_pos q).1 hp) hp
  · simp only [inclusion, h, ↓reduceDIte]

/-- The point `(s, x)` of `(-1, ∞) × ∂W` in `c.WithEnd`; its values for `s ≤ -1` are junk. -/
def endMap (p : ℝ × (𝓡∂ (n + 1)).boundary W) : c.WithEnd :=
  if h : -1 < p.1 then c.endIncl ((⟨p.1, h⟩, p.2) : endInterval × (𝓡∂ (n + 1)).boundary W)
  else c.endIncl ((⟨0, by simp⟩, p.2) : endInterval × (𝓡∂ (n + 1)).boundary W)

private theorem endMap_of_lt {s : ℝ} (hs : -1 < s) (x : (𝓡∂ (n + 1)).boundary W) :
    endMap c (s, x) = c.endIncl ((⟨s, hs⟩, x) : endInterval × (𝓡∂ (n + 1)).boundary W) := by
  simp only [endMap, hs, ↓reduceDIte]

/-- For `s ∈ (-1, 0]`, the point `(s, x)` of the end is the collar point `c (x, -s)` of `W`. -/
theorem endMap_neg_eq_inclusion (x : (𝓡∂ (n + 1)).boundary W) (t : normalIioOpens 1) :
    endMap c (-(t : EuclideanHalfSpace 1).val 0, x) = inclusion c (c (x, t)) := by
  rw [inclusion_apply_collar, ← coe_negNormalCoord, endMap_of_lt c (negNormalCoord t).property,
    Subtype.coe_eta, collarToEnd_mk]

/-- The end is attached along `∂W`: `(0, x)` is the boundary point `x` of `W`. -/
theorem endMap_zero (x : (𝓡∂ (n + 1)).boundary W) : endMap c (0, x) = inclusion c x := by
  have := endMap_neg_eq_inclusion c x (normalIioOpensZero one_pos)
  rwa [coe_normalIioOpensZero, val_zero_apply, neg_zero, apply_zero] at this

/-- The retraction, as a morphism out of the glued space. -/
private def retractionHom : c.glueData.toGlueData.glued ⟶ TopCat.of W :=
  Limits.Multicoequalizer.desc c.glueData.toGlueData.diagram (TopCat.of W)
    (fun i ↦ match i with
      | ⟨false⟩ => TopCat.ofHom ⟨InteriorModel.val, InteriorModel.continuous_val⟩
      | ⟨true⟩ => TopCat.ofHom ⟨c.endRetract, c.continuous_endRetract⟩)
    (by
      rintro ⟨⟨_ | _⟩, ⟨_ | _⟩⟩ <;> ext x
      · rfl
      · exact (c.endRetract_interiorToEndPt x).symm
      · exact c.endRetract_eq_val_endToInterior x
      · rfl)

/-- The retraction of `c.WithEnd` onto `W`: the identity on `W`, and `(s, x) ↦ x` for `s ≥ 0`. -/
def retraction : C(c.WithEnd, W) := (retractionHom c).hom

private theorem retraction_interiorIncl (p : InteriorPiece n W) :
    retraction c (c.interiorIncl p) = p.val :=
  ConcreteCategory.congr_hom (Limits.Multicoequalizer.π_desc c.glueData.toGlueData.diagram
    (TopCat.of W) _ _ ⟨false⟩) p

private theorem retraction_endIncl (q : EndPiece n W) :
    retraction c (c.endIncl q) = c.endRetract q :=
  ConcreteCategory.congr_hom (Limits.Multicoequalizer.π_desc c.glueData.toGlueData.diagram
    (TopCat.of W) _ _ ⟨true⟩) q

/-- The retraction is a left inverse of the inclusion. -/
@[simp] theorem retraction_inclusion (p : W) : retraction c (inclusion c p) = p := by
  by_cases h : p ∈ range c
  · obtain ⟨q, rfl⟩ := h
    rw [inclusion_apply_collar]
    exact (retraction_endIncl c (collarToEnd q)).trans (c.endRetract_collarToEnd q)
  · rw [inclusion_apply_of_mem_interior c (c.mem_interior_of_notMem_range h),
      retraction_interiorIncl]
    exact InteriorModel.val_mk _ _

end WithEnd

private theorem isImmersionAt_endIncl_collarToEnd
    (q : ↥((𝓡∂ (n + 1)).boundary W) × normalIioOpens 1) :
    IsImmersionAt ((𝓡 n).prod (𝓡∂ 1)) (𝓡 (n + 1)) ∞
      (fun p ↦ c.endIncl (remodelDiffeomorph (endModelDiffeomorph n) _ (collarToEnd p))) q := by
  have h₁ : IsImmersionAt ((𝓡 n).prod (𝓡∂ 1)) ((𝓡 n).prod 𝓘(ℝ)) ∞
      (Prod.map id negNormalCoord) q :=
    ((IsImmersion.id (I := 𝓡 n) (n := ∞)
      (M := ↥((𝓡∂ (n + 1)).boundary W))).isImmersionAt q.1).prodMap
      (isImmersionAt_negNormalCoord q.2)
  let e := (Diffeomorph.prodComm (𝓡 n) 𝓘(ℝ) ↥((𝓡∂ (n + 1)).boundary W) endInterval ∞).trans
    (remodelDiffeomorph (endModelDiffeomorph n) (endInterval × (𝓡∂ (n + 1)).boundary W))
  have hB : ((ContinuousLinearEquiv.prodComm ℝ (EuclideanSpace ℝ (Fin n)) ℝ).trans
      (endModelEquiv n)) '' range ((𝓡 n).prod 𝓘(ℝ)) = range (𝓡 (n + 1)) := by
    simp
  have h₂ := isImmersionAt_diffeomorph_comp_of_image_range_eq _ hB e le_rfl h₁
  exact isImmersionAt_isLocalDiffeomorphAt_comp (c.isLocalDiffeomorph_endIncl _) h₂

namespace WithEnd

private theorem inclusion_comp_collar :
    inclusion c ∘ c =
      fun p ↦ c.endIncl (remodelDiffeomorph (endModelDiffeomorph n) _ (collarToEnd p)) :=
  funext fun p ↦ by
    rw [coe_remodelDiffeomorph, remodelHomeomorph_apply]; exact inclusion_apply_collar c p

private theorem inclusion_comp_subtypeVal :
    inclusion c ∘ Subtype.val =
      c.interiorIncl ∘ interiorModelDiffeomorph (𝓡∂ (n + 1)) ((𝓡∂ (n + 1)).interiorOpens W) ∞ := by
  funext q
  rw [comp_apply, inclusion_apply_of_mem_interior c
    (ModelWithCorners.coe_interiorOpens (I := 𝓡∂ (n + 1)) (M := W) ▸ SetLike.mem_coe.2 q.property),
    InteriorModel.mk_def, comp_apply, coe_interiorModelDiffeomorph]

/-- On the interior of `W`, the inclusion is an open embedding. -/
theorem isOpenEmbedding_inclusion_comp_subtypeVal :
    IsOpenEmbedding (inclusion c ∘ ((↑) : (𝓡∂ (n + 1)).interiorOpens W → W)) := by
  rw [inclusion_comp_subtypeVal]
  exact c.isOpenEmbedding_interiorIncl.comp (Diffeomorph.toHomeomorph
    (interiorModelDiffeomorph (𝓡∂ (n + 1)) ((𝓡∂ (n + 1)).interiorOpens W) ∞)).isOpenEmbedding

/-- The inclusion is a local diffeomorphism at interior points. -/
theorem isLocalDiffeomorphAt_inclusion {p : W} (hp : p ∈ (𝓡∂ (n + 1)).interior W) :
    IsLocalDiffeomorphAt (𝓡∂ (n + 1)) (𝓡 (n + 1)) ∞ (inclusion c) p := by
  have h : IsLocalDiffeomorphAt (𝓡∂ (n + 1)) (𝓡 (n + 1)) ∞ (inclusion c ∘ Subtype.val)
      (⟨p, SetLike.mem_coe.1 (ModelWithCorners.coe_interiorOpens (I := 𝓡∂ (n + 1)) (M := W) ▸ hp)⟩ :
        (𝓡∂ (n + 1)).interiorOpens W) := by
    rw [inclusion_comp_subtypeVal]
    exact (Diffeomorph.isLocalDiffeomorph
      (interiorModelDiffeomorph (𝓡∂ (n + 1)) ((𝓡∂ (n + 1)).interiorOpens W) ∞) _).comp
      (hg := c.isLocalDiffeomorph_interiorIncl _)
  exact h.of_comp_right (isLocalDiffeomorph_subtype_val _)

private theorem isImmersionAt_inclusion_collar
    (q : ↥((𝓡∂ (n + 1)).boundary W) × normalIioOpens 1) :
    IsImmersionAt (𝓡∂ (n + 1)) (𝓡 (n + 1)) ∞ (inclusion c) (c q) := by
  obtain ⟨A, hA⟩ := EuclideanHalfSpace.exists_continuousLinearEquiv_image_range_prod n
  have hA' : A.symm '' range (𝓡∂ (n + 1)) = range ((𝓡 n).prod (𝓡∂ 1)) := by
    rw [← hA, ← image_comp]
    simp
  let e := c.diffeomorphOpensRange
  have h₁ : IsImmersionAt ((𝓡 n).prod (𝓡∂ 1)) (𝓡 (n + 1)) ∞
      ((inclusion c ∘ Subtype.val) ∘ e) (e.symm (e q)) := by
    rw [e.symm_apply_apply]
    convert c.isImmersionAt_endIncl_collarToEnd q using 1
    rw [← inclusion_comp_collar]
    funext p
    simp [e]
  have h₂ := isImmersionAt_comp_diffeomorph_of_image_range_eq A.symm hA' e.symm le_rfl h₁
  have h₃ : (inclusion c ∘ Subtype.val) ∘ e ∘ e.symm = inclusion c ∘ Subtype.val := by
    funext w
    simp
  rw [comp_assoc, h₃] at h₂
  have h₄ := isImmersionAt_comp_subtypeVal_iff.1 h₂
  simpa [e] using h₄

/-- The inclusion is an immersion. -/
theorem isImmersionAt_inclusion (p : W) :
    IsImmersionAt (𝓡∂ (n + 1)) (𝓡 (n + 1)) ∞ (inclusion c) p := by
  by_cases hp : p ∈ (𝓡∂ (n + 1)).interior W
  · have hs : ContMDiffOn (𝓡∂ (n + 1)) (𝓡 (n + 1)) ∞ (inclusion c)
        ((𝓡∂ (n + 1)).interior W) := fun x hx ↦
      (isLocalDiffeomorphAt_inclusion c hx).contMDiffAt.contMDiffWithinAt
    obtain ⟨e, he⟩ := (isLocalDiffeomorphAt_inclusion c hp).isInvertible_mfderiv (by simp)
    exact ContMDiffOn.isImmersionAt_of_injective_mfderiv_of_isInteriorPoint hs
      (ModelWithCorners.coe_interiorOpens (I := 𝓡∂ (n + 1)) (M := W) ▸
        ((𝓡∂ (n + 1)).interiorOpens W).isOpen) hp (by simp) hp
      (BoundarylessManifold.isInteriorPoint) (he ▸ e.injective)
  · have hb : p ∈ (𝓡∂ (n + 1)).boundary W := by
      rwa [← ModelWithCorners.compl_interior]
    have := isImmersionAt_inclusion_collar c (⟨p, hb⟩, normalIioOpensZero one_pos)
    rwa [apply_zero] at this

/-- The inclusion of `W` in `c.WithEnd` is smooth. -/
theorem contMDiff_inclusion : ContMDiff (𝓡∂ (n + 1)) (𝓡 (n + 1)) ∞ (inclusion c) :=
  fun p ↦ (isImmersionAt_inclusion c p).contMDiffAt

/-- The inclusion of `W` in `c.WithEnd` is continuous. -/
theorem continuous_inclusion : Continuous (inclusion c) := (contMDiff_inclusion c).continuous

/-- The inclusion of `W` in `c.WithEnd` is a closed embedding: a retract of a Hausdorff space. -/
theorem isClosedEmbedding_inclusion [T2Space W] : IsClosedEmbedding (inclusion c) :=
  Function.LeftInverse.isClosedEmbedding (retraction_inclusion c) (retraction c).continuous
    (continuous_inclusion c)

/-- The inclusion of `W` in `c.WithEnd` is a smooth embedding. -/
theorem isSmoothEmbedding_inclusion :
    IsSmoothEmbedding (𝓡∂ (n + 1)) (𝓡 (n + 1)) ∞ (inclusion c) :=
  ⟨isImmersion_iff_forall_isImmersionAt.2 (isImmersionAt_inclusion c),
    Function.LeftInverse.isEmbedding (retraction_inclusion c) (retraction c).continuous
      (continuous_inclusion c)⟩

omit [IsManifold (𝓡∂ (n + 1)) ∞ W] in
/-- The inclusion of `endInterval × ∂W` into `ℝ × ∂W`. -/
private theorem isLocalDiffeomorph_endIntervalVal :
    IsLocalDiffeomorph (𝓘(ℝ).prod (𝓡 n)) (𝓘(ℝ).prod (𝓡 n)) ∞
      (Prod.map Subtype.val id : endInterval × (𝓡∂ (n + 1)).boundary W → _) :=
  isLocalDiffeomorph_subtype_val.prodMap (Diffeomorph.refl (𝓡 n) _ ∞).isLocalDiffeomorph

private theorem endMap_comp_endIntervalVal :
    endMap c ∘ (Prod.map Subtype.val id : endInterval × (𝓡∂ (n + 1)).boundary W → _) =
      fun q ↦ c.endIncl (remodelDiffeomorph (endModelDiffeomorph n) _ q) := by
  funext ⟨s, x⟩
  rw [coe_remodelDiffeomorph, remodelHomeomorph_apply]
  exact endMap_of_lt c s.property x

/-- On `(-1, ∞) × ∂W`, `endMap` is a local diffeomorphism. -/
theorem isLocalDiffeomorphOn_endMap :
    IsLocalDiffeomorphOn (𝓘(ℝ).prod (𝓡 n)) (𝓡 (n + 1)) ∞ (endMap c) (Ioi (-1) ×ˢ univ) := by
  rintro ⟨⟨s, x⟩, hs, -⟩
  have h : IsLocalDiffeomorphAt (𝓘(ℝ).prod (𝓡 n)) (𝓡 (n + 1)) ∞
      (endMap c ∘ (Prod.map Subtype.val id : endInterval × (𝓡∂ (n + 1)).boundary W → _))
      (⟨s, hs⟩, x) := by
    rw [endMap_comp_endIntervalVal]
    exact ((remodelDiffeomorph (endModelDiffeomorph n) _).isLocalDiffeomorph _).comp
      (hg := c.isLocalDiffeomorph_endIncl _)
  exact h.of_comp_right (isLocalDiffeomorph_endIntervalVal _)

/-- On `(-1, ∞) × ∂W`, `endMap` is smooth. -/
theorem contMDiffOn_endMap :
    ContMDiffOn (𝓘(ℝ).prod (𝓡 n)) (𝓡 (n + 1)) ∞ (endMap c) (Ioi (-1) ×ˢ univ) :=
  (isLocalDiffeomorphOn_endMap c).contMDiffOn

private theorem endIncl_injective : Injective c.endIncl := c.glueData.ι_injective ⟨true⟩

/-- On `(-1, ∞) × ∂W`, `endMap` is injective. -/
theorem injOn_endMap : InjOn (endMap c) (Ioi (-1) ×ˢ univ) := by
  rintro ⟨s, x⟩ ⟨hs, -⟩ ⟨s', x'⟩ ⟨hs', -⟩ h
  rw [endMap_of_lt c hs, endMap_of_lt c hs'] at h
  have := endIncl_injective c h
  have h1 := congrArg (fun q : EndPiece n W ↦ (q.coord.1 : ℝ)) this
  have h2 := congrArg (fun q : EndPiece n W ↦ q.coord.2) this
  simp only [EndPiece.coord] at h1 h2
  rw [h1, h2]

private theorem endMap_image_eq {U : Set (ℝ × (𝓡∂ (n + 1)).boundary W)}
    (hU : U ⊆ Ioi (-1) ×ˢ univ) :
    endMap c '' U = c.endIncl '' (Prod.map Subtype.val id ⁻¹' U) := by
  ext z
  constructor
  · rintro ⟨⟨s, x⟩, hp, rfl⟩
    exact ⟨((⟨s, (hU hp).1⟩ : endInterval), x), hp, (endMap_of_lt c (hU hp).1 x).symm⟩
  · rintro ⟨⟨s, x⟩, hp, rfl⟩
    exact ⟨(s, x), hp, endMap_of_lt c s.property x⟩

/-- `endMap` sends open subsets of `(-1, ∞) × ∂W` to open subsets of `c.WithEnd`. -/
theorem isOpen_endMap_image {U : Set (ℝ × (𝓡∂ (n + 1)).boundary W)} (hU : U ⊆ Ioi (-1) ×ˢ univ)
    (ho : IsOpen U) : IsOpen (endMap c '' U) := by
  rw [endMap_image_eq c hU]
  exact (c.glueData.ι_isOpenEmbedding ⟨true⟩).isOpenMap _
    (ho.preimage (continuous_subtypeVal.prodMap continuous_id))

/-- Every point of `c.WithEnd` is a point of `W` or a point `(s, x)` of the end with `0 < s`. -/
theorem exists_eq_inclusion_or_endMap (z : c.WithEnd) :
    (∃ p, inclusion c p = z) ∨ ∃ s x, 0 < s ∧ endMap c (s, x) = z := by
  rcases interiorIncl_or_endIncl c z with ⟨p, rfl⟩ | ⟨q, rfl⟩
  · refine Or.inl ⟨p.val, ?_⟩
    rw [inclusion_apply_of_mem_interior c p.val_mem_interior, InteriorModel.mk_val]
  · obtain ⟨⟨s, hs⟩, x⟩ := q
    by_cases h0 : s ≤ 0
    · refine Or.inl ⟨c (x, collarDepth ⟨s, hs⟩), ?_⟩
      rw [inclusion_apply_collar]
      rw [collarToEnd_mk, negNormalCoord_collarDepth h0]
    · exact Or.inr ⟨s, x, not_le.1 h0, endMap_of_lt c hs x⟩

/-- The retraction sends a point `(s, x)` of the end with `0 ≤ s` to `x`. -/
theorem retraction_endMap {s : ℝ} (hs : 0 ≤ s) (x : (𝓡∂ (n + 1)).boundary W) :
    retraction c (endMap c (s, x)) = x := by
  rw [endMap_of_lt c (by linarith)]
  refine (retraction_endIncl c _).trans ?_
  rw [endRetract_mk]
  convert c.apply_zero x using 3
  apply Subtype.ext
  simpa [collarDepth, EndPiece.coord] using hs

/-- `c.WithEnd` is the union of `W` and of the open end `(0, ∞) × ∂W`. -/
theorem range_inclusion_union :
    range (inclusion c) ∪ endMap c '' (Ioi 0 ×ˢ univ) = univ := by
  refine eq_univ_of_forall fun z ↦ ?_
  rcases exists_eq_inclusion_or_endMap c z with ⟨p, rfl⟩ | ⟨s, x, hs, rfl⟩
  · exact Or.inl (mem_range_self p)
  · exact Or.inr ⟨(s, x), ⟨hs, trivial⟩, rfl⟩

/-- `W` and the open end `(0, ∞) × ∂W` are disjoint in `c.WithEnd`. -/
theorem disjoint_range_inclusion_endMap_image :
    Disjoint (range (inclusion c)) (endMap c '' (Ioi 0 ×ˢ univ)) := by
  refine Set.disjoint_left.2 ?_
  rintro _ ⟨p, rfl⟩ ⟨⟨s, x⟩, ⟨hs, -⟩, h⟩
  have hs : (0 : ℝ) < s := hs
  have hp : p = x := by
    rw [← retraction_inclusion c p, ← h, retraction_endMap c hs.le]
  subst hp
  rw [← endMap_zero, endMap_of_lt c (show (-1 : ℝ) < 0 by norm_num),
    endMap_of_lt c (show (-1 : ℝ) < s by linarith)] at h
  have h1 := congrArg (fun q : EndPiece n W ↦ (q.coord.1 : ℝ)) (endIncl_injective c h)
  simp only [EndPiece.coord] at h1
  linarith

private theorem image_inclusion_interior :
    inclusion c '' (𝓡∂ (n + 1)).interior W = range c.interiorIncl := by
  ext z
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨_, (inclusion_apply_of_mem_interior c hp).symm⟩
  · rintro ⟨p, rfl⟩
    exact ⟨p.val, p.val_mem_interior, by
      rw [inclusion_apply_of_mem_interior c p.val_mem_interior, InteriorModel.mk_val]⟩

private theorem endMap_image_Ioi : endMap c '' (Ioi (-1) ×ˢ univ) = range c.endIncl := by
  rw [endMap_image_eq c subset_rfl]
  ext z
  exact ⟨fun ⟨q, _, h⟩ ↦ ⟨q, h⟩, fun ⟨q, h⟩ ↦ ⟨q, ⟨q.coord.1.property, trivial⟩, h⟩⟩

/-- The image of the interior of `W`, an open subset of `c.WithEnd`. -/
def interiorPart : Opens c.WithEnd :=
  ⟨inclusion c '' (𝓡∂ (n + 1)).interior W, by
    rw [image_inclusion_interior]
    exact c.isOpenEmbedding_interiorIncl.isOpen_range⟩

/-- The image of `(-1, ∞) × ∂W`, an open subset of `c.WithEnd`. -/
def endPart : Opens c.WithEnd :=
  ⟨endMap c '' (Ioi (-1) ×ˢ univ), isOpen_endMap_image c subset_rfl (isOpen_Ioi.prod isOpen_univ)⟩

/-- The underlying set of `interiorPart c`. -/
@[simp] theorem coe_interiorPart :
    (interiorPart c : Set c.WithEnd) = inclusion c '' (𝓡∂ (n + 1)).interior W := (rfl)

/-- The underlying set of `endPart c`. -/
@[simp] theorem coe_endPart : (endPart c : Set c.WithEnd) = endMap c '' (Ioi (-1) ×ˢ univ) :=
  (rfl)

/-- The image of the interior of `W` and the image of `(-1, ∞) × ∂W` cover `c.WithEnd`. -/
theorem isOpenCover : IsOpenCover ![interiorPart c, endPart c] := by
  refine IsOpenCover.mk (eq_top_iff.2 fun z _ ↦ ?_)
  rw [Opens.mem_iSup]
  rcases interiorIncl_or_endIncl c z with ⟨p, rfl⟩ | ⟨q, rfl⟩
  · refine ⟨0, ?_⟩
    rw [Matrix.cons_val_zero, ← SetLike.mem_coe, coe_interiorPart, image_inclusion_interior]
    exact mem_range_self p
  · refine ⟨1, ?_⟩
    rw [Matrix.cons_val_one, Matrix.cons_val_zero, ← SetLike.mem_coe, coe_endPart, endMap_image_Ioi]
    exact mem_range_self q

end WithEnd

end TauCeti.SmoothCollar

end
