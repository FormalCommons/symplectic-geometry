/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.IsManifold.InteriorBoundary
public import TauCeti.Geometry.Manifold.Boundary.Collar.Smooth
public import TauCeti.Geometry.Manifold.Immersion.Interior
public import TauCeti.Geometry.Manifold.Immersion.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.Immersion.ModelChange
import SymplecticGeometry.Geometry.Manifold.Boundary.Charts
import SymplecticGeometry.Geometry.Manifold.Boundary.Collar.Interior
import SymplecticGeometry.Geometry.Manifold.Boundary.Collar.Local
import SymplecticGeometry.Geometry.Manifold.Boundary.Interior
import SymplecticGeometry.Geometry.Manifold.ModelTransport.Remodel
import SymplecticGeometry.Geometry.Manifold.Gluing.Pair
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.Basic
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.OpenSubset

/-!
# Attaching an end along a smooth collar

For a manifold `W` with boundary, modelled on the half-space, and a smooth collar `c` of its
boundary, `c.WithEnd` is `W` with the half-cylinder `[0, ∞) × ∂W` attached along `∂W`. It is the
space `SymplecticGeometry.GluedAlong` (`Gluing/Pair.lean`) of two manifolds over `ℝⁿ⁺¹`, the
charted interior `(𝓡∂ (n + 1)).interior W` of `W` and `(-1, ∞) × ∂W`, re-modelled along a linear
equivalence (`SymplecticGeometry.Remodel`), glued along the diffeomorphism `(s, x) ↦ c (x, -s)`
for `s ∈ (-1, 0)` between open subsets of them. The gluing maps are read in the collar
coordinates `TauCeti.SmoothCollar.interiorCoord` (`Boundary/Collar/Interior.lean`), in which
they are local diffeomorphisms. So `c.WithEnd` takes its topology, atlas and smooth structure
from `GluedAlong`: it is a boundaryless smooth manifold, Hausdorff when `W` is; no compactness is
assumed.

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

The retraction is `SymplecticGeometry.GluedAlong.desc` of the inclusion of the interior and of
the map of the end piece into the collar; the boundary immersion changes models as in
`isImmersionAt_chordDisc_of_mem` (Tau Ceti, `KnotTheory/Slice/ConnectedSum.lean`).

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §3.5, p. 148.
* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Springer GTM 218, 2013,
  Chapter 1 (the smooth manifold chart lemma).
-/

public section

open Set Function Topology Manifold TopologicalSpace SymplecticGeometry
open scoped Manifold ContDiff

noncomputable section

namespace TauCeti.SmoothCollar
open _root_.TauCeti.EuclideanHalfSpace SymplecticGeometry.EuclideanHalfSpace

/-- The open half-line `(-1, ∞)`, the range of the first coordinate of the end piece. -/
private def endInterval : Opens ℝ := ⟨Ioi (-1), isOpen_Ioi⟩

@[simp] private theorem mem_endInterval {s : ℝ} : s ∈ endInterval ↔ -1 < s := Iff.rfl

private theorem endInterval_subset : (endInterval : Set ℝ) ⊆ Ioi (-1) :=
  fun _ ↦ mem_endInterval.1

private theorem Ioc_subset_endInterval : Ioc (-1) 0 ⊆ (endInterval : Set ℝ) :=
  fun _ h ↦ mem_endInterval.2 h.1

private def endModelEquiv (n : ℕ) :
    (ℝ × EuclideanSpace ℝ (Fin n)) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
  (ContinuousLinearEquiv.prodComm ℝ ℝ (EuclideanSpace ℝ (Fin n))).trans
    (euclideanHalfSpaceBoundaryNormalEquiv n)

/-- The identification of the model `ℝ × ℝⁿ` with `ℝⁿ⁺¹` that makes the first factor the first
coordinate, a linear diffeomorphism. -/
def endModelDiffeomorph (n : ℕ) :
    ModelProd ℝ (EuclideanSpace ℝ (Fin n)) ≃ₘ^∞⟮𝓘(ℝ).prod (𝓡 n), 𝓡 (n + 1)⟯
      EuclideanSpace ℝ (Fin (n + 1)) where
  toEquiv := (endModelEquiv n).toEquiv
  contMDiff_toFun := by
    rw [← modelWithCornersSelf_prod]
    exact (endModelEquiv n).contDiff.contMDiff
  contMDiff_invFun := by
    rw [← modelWithCornersSelf_prod]
    exact (endModelEquiv n).symm.contDiff.contMDiff

universe u

variable {n : ℕ} {W : Type u} [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace (n + 1)) W]

variable (n W) in
/-- The end piece `(-1, ∞) × ∂W`, re-modelled on `ℝⁿ⁺¹`. -/
private abbrev EndPiece : Type u :=
  Remodel (endModelDiffeomorph n) (endInterval × (𝓡∂ (n + 1)).boundary W)

variable (c : SmoothCollar n ∞ W)

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
private def endRetract (q : EndPiece n W) : W :=
  c (q.coord.2, negNormalIioRay endInterval_subset q.coord.1)

private theorem endRetract_def (q : EndPiece n W) :
    c.endRetract q = c (q.coord.2, negNormalIioRay endInterval_subset q.coord.1) := rfl

private theorem endRetract_mk (s : endInterval) (x : (𝓡∂ (n + 1)).boundary W) :
    c.endRetract ((s, x) : endInterval × (𝓡∂ (n + 1)).boundary W) =
      c (x, negNormalIioRay endInterval_subset s) := rfl

private theorem continuous_endRetract : Continuous c.endRetract :=
  c.continuous.comp
    (continuous_snd.prodMk ((continuous_negNormalIioRay endInterval_subset).comp continuous_fst))

/-- The end coordinates `(-t, x)` of collar coordinates `(x, t)`. -/
private def collarToEnd (p : ↥((𝓡∂ (n + 1)).boundary W) × normalIioOpens 1) :
    endInterval × (𝓡∂ (n + 1)).boundary W :=
  (negNormalCoord Ioc_subset_endInterval p.2, p.1)

private theorem collarToEnd_mk (x : (𝓡∂ (n + 1)).boundary W) (t : normalIioOpens 1) :
    collarToEnd (x, t) = (negNormalCoord Ioc_subset_endInterval t, x) := rfl

private theorem endRetract_collarToEnd (p : ↥((𝓡∂ (n + 1)).boundary W) × normalIioOpens 1) :
    c.endRetract (collarToEnd p) = c p := by
  obtain ⟨x, t⟩ := p
  rw [collarToEnd_mk, endRetract_mk, negNormalIioRay_negNormalCoord]

/-- The point of the interior piece glued to a point of the end overlap. -/
private def endToInteriorPt (q : endOverlap (n := n) (W := W)) : (𝓡∂ (n + 1)).interior W :=
  ⟨c.endRetract q.val, by
    rw [endRetract_def, apply_mem_interior_iff_pos]
    simpa using mem_endOverlap.1 q.property⟩

private theorem endToInteriorPt_val (q : endOverlap (n := n) (W := W)) :
    (c.endToInteriorPt q).val = c.endRetract q.val :=
  rfl

/-- The gluing map from the end overlap to the interior overlap. -/
private def endToInterior : C(endOverlap (n := n) (W := W), c.interiorRange) where
  toFun q := ⟨c.endToInteriorPt q, c.mem_interiorRange.2
    ⟨_, ((c.endToInteriorPt_val q).trans (c.endRetract_def q.val)).symm⟩⟩
  continuous_toFun := Continuous.subtype_mk
    ((c.continuous_endRetract.comp continuous_subtypeVal).subtype_mk _) _

private theorem endToInterior_val (q : endOverlap (n := n) (W := W)) :
    (c.endToInterior q).val.val = c.endRetract q.val :=
  c.endToInteriorPt_val q

/-- The point of the end piece with the collar coordinates of a point of the interior overlap. -/
private def interiorToEndPt (q : c.interiorRange) : EndPiece n W :=
  collarToEnd (c.interiorCoord q)

private theorem interiorToEndPt_def (q : c.interiorRange) :
    c.interiorToEndPt q = collarToEnd (c.interiorCoord q) := rfl

private theorem continuous_interiorToEndPt : Continuous c.interiorToEndPt :=
  ((continuous_negNormalCoord Ioc_subset_endInterval).comp
    (continuous_snd.comp c.continuous_interiorCoord)).prodMk
      (continuous_fst.comp c.continuous_interiorCoord)

/-- The gluing map from the interior overlap to the end overlap. -/
private def interiorToEnd : C(c.interiorRange, endOverlap (n := n) (W := W)) where
  toFun q := ⟨c.interiorToEndPt q, negNormalCoord_neg _ (c.interiorCoord_snd_pos q)⟩
  continuous_toFun := c.continuous_interiorToEndPt.subtype_mk _

private theorem interiorToEnd_val (q : c.interiorRange) :
    (c.interiorToEnd q).val = c.interiorToEndPt q := rfl

private theorem interiorCoord_endToInterior (q : endOverlap (n := n) (W := W)) :
    c.interiorCoord (c.endToInterior q) =
      (q.val.coord.2, negNormalIioRay endInterval_subset q.val.coord.1) := by
  refine c.injective ?_
  rw [apply_interiorCoord, endToInterior_val, endRetract_def]

private theorem interiorToEnd_endToInterior (q : endOverlap (n := n) (W := W)) :
    c.interiorToEnd (c.endToInterior q) = q := by
  have hq : ((q.val.coord.1 : endInterval) : ℝ) ≤ 0 := le_of_lt (mem_endOverlap.1 q.property)
  apply Subtype.ext
  rw [interiorToEnd_val, interiorToEndPt_def, interiorCoord_endToInterior, collarToEnd_mk,
    negNormalCoord_negNormalIioRay endInterval_subset Ioc_subset_endInterval hq]
  exact Prod.mk.eta.trans (EndPiece.coord_eq _)

private theorem endToInterior_interiorToEnd (q : c.interiorRange) :
    c.endToInterior (c.interiorToEnd q) = q := by
  apply Subtype.ext
  apply Subtype.val_injective
  rw [endToInterior_val, interiorToEnd_val, interiorToEndPt_def, endRetract_collarToEnd,
    apply_interiorCoord]

private theorem isLocalDiffeomorphAt_collarToEnd {p : ↥((𝓡∂ (n + 1)).boundary W) × normalIioOpens 1}
    (hp : 0 < (p.2 : EuclideanHalfSpace 1).val 0) :
    IsLocalDiffeomorphAt ((𝓡 n).prod (𝓡∂ 1)) (𝓘(ℝ).prod (𝓡 n)) ∞ collarToEnd p := by
  exact ((Diffeomorph.prodComm (𝓡 n) (𝓡∂ 1) _ _ ∞).isLocalDiffeomorph p).comp
    (hg := (isLocalDiffeomorphAt_negNormalCoord Ioc_subset_endInterval hp).prodMap
      (isLocalDiffeomorph_id p.1))

private theorem endRetract_interiorToEndPt (q : c.interiorRange) :
    c.endRetract (c.interiorToEndPt q) = q.val.val := by
  rw [interiorToEndPt_def, endRetract_collarToEnd, apply_interiorCoord]

private theorem endRetract_mem_boundary {q : EndPiece n W} (hq : q ∉ endOverlap) :
    c.endRetract q ∈ (𝓡∂ (n + 1)).boundary W := by
  have h0 : ((q.coord.1 : endInterval) : ℝ) ≥ 0 := not_lt.1 hq
  rw [endRetract_def, apply_mem_boundary_iff]
  exact (negNormalIioRay_eq_zero_iff endInterval_subset).2 h0

private theorem exists_separation [T2Space W] (x : (𝓡∂ (n + 1)).interior W) {y : EndPiece n W}
    (hy : y ∉ endOverlap) : ∃ A ∈ 𝓝 x, ∃ B ∈ 𝓝 y, ∀ z : (𝓡∂ (n + 1)).interior W, z ∈ A →
      ∀ q : EndPiece n W, q ∈ B → c.endRetract q ≠ z.val := by
  have hne : x.val ≠ c.endRetract y := fun h ↦ by
    have hb := c.endRetract_mem_boundary hy
    rw [← h, ← ModelWithCorners.compl_interior] at hb
    exact hb x.property
  obtain ⟨A', B', hA', hB', hAB⟩ := t2_separation_nhds hne
  refine ⟨_, continuous_subtypeVal.continuousAt.preimage_mem_nhds hA', _,
    c.continuous_endRetract.continuousAt.preimage_mem_nhds hB', fun z hz q hq h ↦ ?_⟩
  exact Set.disjoint_left.1 hAB hz (h ▸ hq)

variable [IsManifold (𝓡∂ (n + 1)) ∞ W]

private theorem isLocalDiffeomorph_interiorToEndPt :
    IsLocalDiffeomorph (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ c.interiorToEndPt := fun q ↦ by
  have h := ((c.isLocalDiffeomorph_interiorCoord q).comp
    (hg := isLocalDiffeomorphAt_collarToEnd (c.interiorCoord_snd_pos q))).comp
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
  exact isLocalDiffeomorph_id q

/-- The gluing diffeomorphism from the interior overlap to the end overlap, `c.interiorToEnd`
with inverse `c.endToInterior`. -/
private def interiorEndDiffeomorph :
    c.interiorRange ≃ₘ^∞⟮𝓡 (n + 1), 𝓡 (n + 1)⟯ endOverlap (n := n) (W := W) where
  toFun := c.interiorToEnd
  invFun := c.endToInterior
  left_inv := c.endToInterior_interiorToEnd
  right_inv := c.interiorToEnd_endToInterior
  contMDiff_toFun := c.isLocalDiffeomorph_interiorToEnd.contMDiff
  contMDiff_invFun := c.isLocalDiffeomorph_endToInterior.contMDiff

private theorem interiorEndDiffeomorph_apply (q : c.interiorRange) :
    c.interiorEndDiffeomorph q = c.interiorToEnd q := rfl

/-- The manifold `W ∪ ([0, ∞) × ∂W)` obtained from `W` by attaching the end `[0, ∞) × ∂W` along
the smooth collar `c`: the space `SymplecticGeometry.GluedAlong` glued from the interior of `W`
and `(-1, ∞) × ∂W` along the diffeomorphism `(s, x) ↦ c (x, -s)` for `s ∈ (-1, 0)`. -/
def WithEnd : Type u := GluedAlong c.interiorEndDiffeomorph.toHomeomorph

/-- The topology of `c.WithEnd`, that of the glued space. -/
@[instance_reducible]
def topologicalSpaceWithEnd : TopologicalSpace c.WithEnd :=
  inferInstanceAs (TopologicalSpace (GluedAlong c.interiorEndDiffeomorph.toHomeomorph))

instance : TopologicalSpace c.WithEnd := c.topologicalSpaceWithEnd

/-- The atlas of `c.WithEnd`, that of the glued space, transported from the atlases of its two
pieces. -/
@[instance_reducible]
def chartedSpaceWithEnd : ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) c.WithEnd :=
  inferInstanceAs (ChartedSpace _ (GluedAlong c.interiorEndDiffeomorph.toHomeomorph))

instance : ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) c.WithEnd := c.chartedSpaceWithEnd

instance : IsManifold (𝓡 (n + 1)) ∞ c.WithEnd :=
  inferInstanceAs (IsManifold _ ∞ (GluedAlong c.interiorEndDiffeomorph.toHomeomorph))

/-- The canonical map of the interior piece into `c.WithEnd`. -/
private abbrev interiorIncl : (𝓡∂ (n + 1)).interior W → c.WithEnd :=
  GluedAlong.inl c.interiorEndDiffeomorph.toHomeomorph

/-- The canonical map of the end piece into `c.WithEnd`. -/
private abbrev endIncl : EndPiece n W → c.WithEnd :=
  GluedAlong.inr c.interiorEndDiffeomorph.toHomeomorph

/-- `c.WithEnd` is Hausdorff when `W` is. -/
instance [T2Space W] : T2Space c.WithEnd := by
  refine (GluedAlong.t2Space_iff c.interiorEndDiffeomorph.toHomeomorph).2
    ⟨inferInstanceAs (T2Space ((𝓡∂ (n + 1)).interior W)),
      inferInstanceAs (T2Space (endInterval × (𝓡∂ (n + 1)).boundary W)), fun x _ y hy ↦ ?_⟩
  obtain ⟨A, hA, B, hB, hAB⟩ := c.exists_separation x hy
  exact ⟨A, hA, B, hB, fun z hz hz' ↦ hAB z.val hz _ hz' (c.endRetract_interiorToEndPt z)⟩

private theorem endIncl_collarToEnd_eq {p : ↥((𝓡∂ (n + 1)).boundary W) × normalIioOpens 1}
    (hint : c p ∈ (𝓡∂ (n + 1)).interior W) :
    c.endIncl (collarToEnd p) = c.interiorIncl ⟨c p, hint⟩ := by
  refine (GluedAlong.inr_eq_inl_iff _).2 ⟨c.mem_interiorRange.2 (mem_range_self p), ?_⟩
  rw [Diffeomorph.coe_toHomeomorph, interiorEndDiffeomorph_apply, interiorToEnd_val,
    interiorToEndPt_def, c.interiorCoord_eq_iff.2 rfl]

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
  else c.interiorIncl ⟨p, c.mem_interior_of_notMem_range h⟩

private theorem inclusion_apply_collar (p : ↥((𝓡∂ (n + 1)).boundary W) × normalIioOpens 1) :
    inclusion c (c p) = c.endIncl (collarToEnd p) := by
  simp only [inclusion, mem_range_self, ↓reduceDIte]
  congr 2
  apply c.diffeomorphOpensRange.symm_apply_eq.2
  exact Subtype.ext (c.coe_diffeomorphOpensRange_apply p).symm

private theorem inclusion_apply_of_mem_interior {p : W} (hp : p ∈ (𝓡∂ (n + 1)).interior W) :
    inclusion c p = c.interiorIncl ⟨p, hp⟩ := by
  by_cases h : p ∈ range c
  · obtain ⟨q, rfl⟩ := h
    rw [inclusion_apply_collar]
    exact c.endIncl_collarToEnd_eq hp
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
  rw [inclusion_apply_collar, ← coe_negNormalCoord Ioc_subset_endInterval,
    endMap_of_lt c (negNormalCoord Ioc_subset_endInterval t).property, Subtype.coe_eta,
    collarToEnd_mk]

/-- The end is attached along `∂W`: `(0, x)` is the boundary point `x` of `W`. -/
theorem endMap_zero (x : (𝓡∂ (n + 1)).boundary W) : endMap c (0, x) = inclusion c x := by
  have := endMap_neg_eq_inclusion c x (normalIioOpensZero one_pos)
  rwa [coe_normalIioOpensZero, val_zero_apply, neg_zero, apply_zero] at this

/-- The retraction of `c.WithEnd` onto `W`: the identity on `W`, and `(s, x) ↦ x` for `s ≥ 0`. -/
def retraction : C(c.WithEnd, W) :=
  GluedAlong.desc c.interiorEndDiffeomorph.toHomeomorph ⟨Subtype.val, continuous_subtypeVal⟩
    ⟨c.endRetract, c.continuous_endRetract⟩ fun q ↦ by
      rw [ContinuousMap.coe_mk, ContinuousMap.coe_mk, Diffeomorph.coe_toHomeomorph,
        interiorEndDiffeomorph_apply, interiorToEnd_val, endRetract_interiorToEndPt]

private theorem retraction_interiorIncl (p : (𝓡∂ (n + 1)).interior W) :
    retraction c (c.interiorIncl p) = p.val := by
  -- `c.WithEnd` is `GluedAlong c.interiorEndDiffeomorph.toHomeomorph` by definition, so the map
  -- out of the glued space applies.
  exact GluedAlong.desc_inl _ _ p

private theorem retraction_endIncl (q : EndPiece n W) :
    retraction c (c.endIncl q) = c.endRetract q := by
  -- As for `retraction_interiorIncl`.
  exact GluedAlong.desc_inr _ _ q

/-- The retraction is a left inverse of the inclusion. -/
@[simp] theorem retraction_inclusion (p : W) : retraction c (inclusion c p) = p := by
  by_cases h : p ∈ range c
  · obtain ⟨q, rfl⟩ := h
    rw [inclusion_apply_collar]
    exact (retraction_endIncl c (collarToEnd q)).trans (c.endRetract_collarToEnd q)
  · rw [inclusion_apply_of_mem_interior c (c.mem_interior_of_notMem_range h),
      retraction_interiorIncl]

end WithEnd

private theorem isImmersionAt_endIncl_collarToEnd
    (q : ↥((𝓡∂ (n + 1)).boundary W) × normalIioOpens 1) :
    IsImmersionAt ((𝓡 n).prod (𝓡∂ 1)) (𝓡 (n + 1)) ∞
      (fun p ↦ c.endIncl (remodelDiffeomorph (endModelDiffeomorph n) _ (collarToEnd p))) q := by
  have h₁ : IsImmersionAt ((𝓡 n).prod (𝓡∂ 1)) ((𝓡 n).prod 𝓘(ℝ)) ∞
      (Prod.map id (negNormalCoord Ioc_subset_endInterval)) q :=
    ((IsImmersion.id (I := 𝓡 n) (n := ∞)
      (M := ↥((𝓡∂ (n + 1)).boundary W))).isImmersionAt q.1).prodMap
      (isImmersionAt_negNormalCoord Ioc_subset_endInterval q.2)
  let e := (Diffeomorph.prodComm (𝓡 n) 𝓘(ℝ) ↥((𝓡∂ (n + 1)).boundary W) endInterval ∞).trans
    (remodelDiffeomorph (endModelDiffeomorph n) (endInterval × (𝓡∂ (n + 1)).boundary W))
  have hB : ((ContinuousLinearEquiv.prodComm ℝ (EuclideanSpace ℝ (Fin n)) ℝ).trans
      (endModelEquiv n)) '' range ((𝓡 n).prod 𝓘(ℝ)) = range (𝓡 (n + 1)) := by
    simp
  have h₂ := isImmersionAt_diffeomorph_comp_of_image_range_eq _ hB e le_rfl h₁
  exact isImmersionAt_isLocalDiffeomorphAt_comp (GluedAlong.isLocalDiffeomorph_inr _ _) h₂

namespace WithEnd

private theorem inclusion_comp_collar :
    inclusion c ∘ c =
      fun p ↦ c.endIncl (remodelDiffeomorph (endModelDiffeomorph n) _ (collarToEnd p)) :=
  funext fun p ↦ by
    rw [coe_remodelDiffeomorph, remodelHomeomorph_apply]; exact inclusion_apply_collar c p

private theorem inclusion_comp_subtypeVal :
    inclusion c ∘ Subtype.val =
      c.interiorIncl ∘ ((𝓡∂ (n + 1)).interiorOpensDiffeomorph W ∞) := by
  funext q
  rw [comp_apply, inclusion_apply_of_mem_interior c
    (ModelWithCorners.mem_interiorOpens_iff_mem_interior.1 q.property),
    comp_apply, ModelWithCorners.coe_interiorOpensDiffeomorph]

/-- On the interior of `W`, the inclusion is an open embedding. -/
theorem isOpenEmbedding_inclusion_comp_subtypeVal :
    IsOpenEmbedding (inclusion c ∘ ((↑) : (𝓡∂ (n + 1)).interiorOpens W → W)) := by
  rw [inclusion_comp_subtypeVal]
  exact (GluedAlong.isOpenEmbedding_inl _).comp
    ((𝓡∂ (n + 1)).interiorOpensDiffeomorph W ∞).toHomeomorph.isOpenEmbedding

/-- The inclusion is a local diffeomorphism at interior points. -/
theorem isLocalDiffeomorphAt_inclusion {p : W} (hp : p ∈ (𝓡∂ (n + 1)).interior W) :
    IsLocalDiffeomorphAt (𝓡∂ (n + 1)) (𝓡 (n + 1)) ∞ (inclusion c) p := by
  have h : IsLocalDiffeomorphAt (𝓡∂ (n + 1)) (𝓡 (n + 1)) ∞ (inclusion c ∘ Subtype.val)
      (⟨p, ModelWithCorners.mem_interiorOpens_iff_mem_interior.2 hp⟩ :
        (𝓡∂ (n + 1)).interiorOpens W) := by
    rw [inclusion_comp_subtypeVal]
    exact (((𝓡∂ (n + 1)).interiorOpensDiffeomorph W ∞).isLocalDiffeomorph _).comp
      (hg := GluedAlong.isLocalDiffeomorph_inl _ _)
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
      ((𝓡∂ (n + 1)).isOpen_interior one_ne_zero) hp (by simp) hp
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
  isLocalDiffeomorph_subtype_val.prodMap isLocalDiffeomorph_id

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
      (hg := GluedAlong.isLocalDiffeomorph_inr _ _)
  exact h.of_comp_right (isLocalDiffeomorph_endIntervalVal _)

/-- On `(-1, ∞) × ∂W`, `endMap` is smooth. -/
theorem contMDiffOn_endMap :
    ContMDiffOn (𝓘(ℝ).prod (𝓡 n)) (𝓡 (n + 1)) ∞ (endMap c) (Ioi (-1) ×ˢ univ) :=
  (isLocalDiffeomorphOn_endMap c).contMDiffOn

/-- On `(-1, ∞) × ∂W`, `endMap` is injective. -/
theorem injOn_endMap : InjOn (endMap c) (Ioi (-1) ×ˢ univ) := by
  rintro ⟨s, x⟩ ⟨hs, -⟩ ⟨s', x'⟩ ⟨hs', -⟩ h
  rw [endMap_of_lt c hs, endMap_of_lt c hs'] at h
  have := GluedAlong.inr_injective _ h
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
  exact (GluedAlong.isOpenEmbedding_inr _).isOpenMap _
    (ho.preimage (continuous_subtypeVal.prodMap continuous_id))

/-- Every point of `c.WithEnd` is a point of `W` or a point `(s, x)` of the end with `0 < s`. -/
theorem exists_eq_inclusion_or_endMap (z : c.WithEnd) :
    (∃ p, inclusion c p = z) ∨ ∃ s x, 0 < s ∧ endMap c (s, x) = z := by
  rcases GluedAlong.exists_inl_or_exists_inr _ z with ⟨p, rfl⟩ | ⟨q, rfl⟩
  · refine Or.inl ⟨p.val, ?_⟩
    rw [inclusion_apply_of_mem_interior c p.property]
  · obtain ⟨⟨s, hs⟩, x⟩ := q
    by_cases h0 : s ≤ 0
    · refine Or.inl ⟨c (x, negNormalIioRay endInterval_subset ⟨s, hs⟩), ?_⟩
      rw [inclusion_apply_collar, collarToEnd_mk,
        negNormalCoord_negNormalIioRay endInterval_subset Ioc_subset_endInterval h0]
    · exact Or.inr ⟨s, x, not_le.1 h0, endMap_of_lt c hs x⟩

/-- The inclusion of `W` in `c.WithEnd` is injective. -/
theorem inclusion_injective : Function.Injective (inclusion c) :=
  Function.LeftInverse.injective (retraction_inclusion c)

/-- The retraction sends a point `(s, x)` of the end with `0 ≤ s` to `x`. -/
theorem retraction_endMap {s : ℝ} (hs : 0 ≤ s) (x : (𝓡∂ (n + 1)).boundary W) :
    retraction c (endMap c (s, x)) = x := by
  rw [endMap_of_lt c (by linarith)]
  refine (retraction_endIncl c _).trans ?_
  rw [endRetract_mk]
  convert c.apply_zero x using 3
  exact (negNormalIioRay_eq_zero_iff endInterval_subset).2 hs

/-- A point of `W` equal to a point `(s, x)` of the end with `0 ≤ s` is the boundary point `x`. -/
theorem eq_of_inclusion_eq_endMap {p : W} {s : ℝ} (hs : 0 ≤ s) {x : (𝓡∂ (n + 1)).boundary W}
    (h : inclusion c p = endMap c (s, x)) : p = x := by
  rw [← retraction_inclusion c p, h, retraction_endMap c hs]

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
  have h1 := congrArg (fun q : EndPiece n W ↦ (q.coord.1 : ℝ)) (GluedAlong.inr_injective _ h)
  simp only [EndPiece.coord] at h1
  linarith

private theorem image_inclusion_interior :
    inclusion c '' (𝓡∂ (n + 1)).interior W = range c.interiorIncl := by
  ext z
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨_, (inclusion_apply_of_mem_interior c hp).symm⟩
  · rintro ⟨p, rfl⟩
    exact ⟨p.val, p.property, by
      rw [inclusion_apply_of_mem_interior c p.property]⟩

private theorem endMap_image_Ioi : endMap c '' (Ioi (-1) ×ˢ univ) = range c.endIncl := by
  rw [endMap_image_eq c subset_rfl]
  ext z
  exact ⟨fun ⟨q, _, h⟩ ↦ ⟨q, h⟩, fun ⟨q, h⟩ ↦ ⟨q, ⟨q.coord.1.property, trivial⟩, h⟩⟩

/-- The image of the interior of `W`, an open subset of `c.WithEnd`. -/
def interiorPart : Opens c.WithEnd :=
  ⟨inclusion c '' (𝓡∂ (n + 1)).interior W, by
    rw [image_inclusion_interior]
    exact (GluedAlong.isOpenEmbedding_inl _).isOpen_range⟩

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
  rcases GluedAlong.exists_inl_or_exists_inr _ z with ⟨p, hp⟩ | ⟨q, hq⟩
  · refine ⟨0, ?_⟩
    rw [Matrix.cons_val_zero, ← SetLike.mem_coe, coe_interiorPart, image_inclusion_interior]
    exact ⟨p, hp⟩
  · refine ⟨1, ?_⟩
    rw [Matrix.cons_val_one, Matrix.cons_val_zero, ← SetLike.mem_coe, coe_endPart, endMap_image_Ioi]
    exact ⟨q, hq⟩

end WithEnd

end TauCeti.SmoothCollar

end
