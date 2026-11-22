/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.CoordinateDisc
public import TauCeti.Geometry.Manifold.Boundary.Collar.Global
import Mathlib.Topology.MetricSpace.Thickening
import SymplecticGeometry.Analysis.Normed.Module.Ball.Collar
import TauCeti.Analysis.Complex.Circle

/-!
# The complement of disjoint coordinate discs

Let `φ i`, for `i` in a finite discrete type `ι`, be coordinate discs of a homologically oriented
surface `M` (`SymplecticGeometry.CoordinateDisc`) whose closed discs are pairwise disjoint.
Removing their open discs leaves the closed subset `X = discComplement φ` of `M`, a compact
surface with boundary when `M` is compact. Its interior is the open set
`discComplementInterior φ` of `M`, the complement of the closed discs, and its boundary is the
union of the boundary circles, parametrized by `discComplementBoundary φ hφ : ι × S¹ → X`.

This file puts `X` in the setting of Tau Ceti's relative fundamental class
(`TauCeti.HomologicalOrientation.fundamentalClassRel`): the inclusion of the interior into `X` is
an open embedding, its range is the complement of the boundary, and the boundary is collared
(`TauCeti.IsCollared`).

The collar of the boundary circle of `φ i` is the thin annulus `1 ≤ |z| < 1 + δᵢ` of the chart,
through `((i, z), t) ↦ φ i ((1 + δᵢ t) z)`. The widths `δᵢ ∈ (0, 1)` are chosen so that the
images `φ i (B(0, 1 + δᵢ))` are pairwise disjoint. They exist because the closed discs are
finitely many pairwise disjoint compact sets, so they have pairwise disjoint open neighbourhoods,
and each of these contains the image of a ball slightly larger than the unit ball. The map
`(z, t) ↦ (1 + δᵢ t) z` is a homeomorphism of `S¹ × [0, 1)` onto the annulus
(`homeomorphUnitSphereProdIcoAnnulus`); the analogous collar of the unit sphere in the closed unit
ball is `Metric.isCollared_inclusion_sphere_closedBall`. The collars of the
different discs are glued with `isOpenMap_prod_of_discrete_left`.

## Main definitions

* `SymplecticGeometry.discComplement φ`: the complement of the open discs.
* `SymplecticGeometry.discComplementInterior φ`: the complement of the closed discs, an open set.
* `SymplecticGeometry.discComplementBoundary φ hφ`: the boundary circles, as a map
  `ι × Circle → discComplement φ`.

## Main results

* `SymplecticGeometry.isClosed_discComplement`, and `CompactSpace (discComplement φ)` when `M` is
  compact.
* `SymplecticGeometry.isOpenEmbedding_inclusion_discComplementInterior`: the inclusion of the
  interior is an open embedding.
* `SymplecticGeometry.range_inclusion_discComplementInterior`: its range is the complement of the
  boundary.
* `SymplecticGeometry.isCollared_discComplementBoundary`: the boundary is collared.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.7,
  where the first Chern number of a bundle over a surface is computed from trivializations over
  discs and over their complement.
-/

public section

noncomputable section

open Set Topology Metric TauCeti Function

namespace SymplecticGeometry

variable {M : Type} [TopologicalSpace M] [T2Space M] {E : Type} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M] {o : HomologicalOrientation M E 2}
  {ι : Type*} (φ : ι → CoordinateDisc o)

/-! ### The complement of the open discs -/

/-- The complement of the open discs of a family of coordinate discs. -/
def discComplement : Set M :=
  (⋃ i, (φ i).openDisc)ᶜ

theorem discComplement_def : discComplement φ = (⋃ i, (φ i).openDisc)ᶜ :=
  (rfl)

@[simp]
theorem mem_discComplement_iff {x : M} : x ∈ discComplement φ ↔ ∀ i, x ∉ (φ i).openDisc := by
  simp [discComplement_def]

theorem isClosed_discComplement : IsClosed (discComplement φ) :=
  (isOpen_iUnion fun i ↦ (φ i).isOpen_openDisc).isClosed_compl

instance [CompactSpace M] : CompactSpace (discComplement φ) :=
  isCompact_iff_compactSpace.1 (isClosed_discComplement φ).isCompact

section Boundary

variable [TopologicalSpace ι] [DiscreteTopology ι]

/-- The boundary circles of coordinate discs with pairwise disjoint closed discs, as a map from
`ι × S¹` to the complement of the open discs. -/
def discComplementBoundary (hφ : Pairwise (Disjoint on fun i ↦ (φ i).disc)) :
    C(ι × Circle, discComplement φ) where
  toFun p := ⟨(φ p.1).boundaryCircle p.2, (mem_discComplement_iff φ).2 fun j hj ↦ by
    by_cases hij : j = p.1
    · exact (φ p.1).boundaryCircle_notMem_openDisc p.2 (hij ▸ hj)
    · exact (hφ hij).notMem_of_mem_left ((φ j).openDisc_subset_disc hj)
        ((φ p.1).boundaryCircle_mem_disc p.2)⟩
  continuous_toFun := (continuous_prod_of_discrete_left.2 fun i ↦
    (φ i).boundaryCircle.continuous).subtype_mk _

@[simp]
theorem coe_discComplementBoundary_apply (hφ : Pairwise (Disjoint on fun i ↦ (φ i).disc))
    (p : ι × Circle) : (discComplementBoundary φ hφ p : M) = (φ p.1).boundaryCircle p.2 :=
  (rfl)

end Boundary

/-! ### The complement of the closed discs -/

variable [Finite ι]

/-- The complement of the closed discs of finitely many coordinate discs, an open set: the
interior of `discComplement φ`. -/
def discComplementInterior : TopologicalSpace.Opens M :=
  ⟨(⋃ i, (φ i).disc)ᶜ,
    (isClosed_iUnion_of_finite fun i ↦ (φ i).isCompact_disc.isClosed).isOpen_compl⟩

@[simp]
theorem coe_discComplementInterior :
    (discComplementInterior φ : Set M) = (⋃ i, (φ i).disc)ᶜ :=
  (rfl)

@[simp]
theorem mem_discComplementInterior_iff {x : M} :
    x ∈ discComplementInterior φ ↔ ∀ i, x ∉ (φ i).disc := by
  simp [← SetLike.mem_coe]

theorem discComplementInterior_subset : (discComplementInterior φ : Set M) ⊆ discComplement φ :=
  compl_subset_compl.2 (iUnion_mono fun i ↦ (φ i).openDisc_subset_disc)

/-- The inclusion of the complement of the closed discs into the complement of the open discs is
an open embedding. -/
theorem isOpenEmbedding_inclusion_discComplementInterior :
    IsOpenEmbedding (inclusion (discComplementInterior_subset φ)) :=
  .inclusion (discComplementInterior_subset φ)
    ((discComplementInterior φ).isOpen.preimage continuous_subtypeVal)

variable [TopologicalSpace ι] [DiscreteTopology ι]

/-- The complement of the closed discs is the complement of the boundary circles in the
complement of the open discs. -/
theorem range_inclusion_discComplementInterior (hφ : Pairwise (Disjoint on fun i ↦ (φ i).disc)) :
    range (inclusion (discComplementInterior_subset φ)) =
      (range (discComplementBoundary φ hφ))ᶜ := by
  ext x
  simp only [mem_compl_iff, mem_range, Prod.exists, not_exists]
  constructor
  · rintro ⟨y, rfl⟩ i z h
    refine (mem_discComplementInterior_iff φ).1 y.property i ?_
    rw [← coe_inclusion (discComplementInterior_subset φ), ← h, coe_discComplementBoundary_apply]
    exact (φ i).boundaryCircle_mem_disc z
  · intro h
    refine ⟨⟨x, (mem_discComplementInterior_iff φ).2 fun i hi ↦ ?_⟩, rfl⟩
    obtain ⟨z, hz⟩ : (x : M) ∈ range (φ i).boundaryCircle :=
      (φ i).disc_diff_openDisc ▸ ⟨hi, (mem_discComplement_iff φ).1 x.property i⟩
    exact h i z (Subtype.ext hz)

/-! ### The collar of the boundary circles -/

/-- The point `(1 + δ t) z` of the ball of radius `2`, for `z` on the unit circle, `t ∈ [0, 1)`
and `δ ∈ (0, 1)`: the homeomorphism `homeomorphUnitSphereProdIcoAnnulus`, read in the ball. -/
private def annulusPoint {δ : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) 1) (q : Circle × Ico (0 : ℝ) 1) :
    CoordinateDisc.ball :=
  let w := homeomorphUnitSphereProdIcoAnnulus hδ.1 (Circle.homeomorphSphere q.1, q.2)
  ⟨w, CoordinateDisc.mem_ball_iff.2 (by linarith [w.property.2, hδ.2])⟩

private lemma coe_annulusPoint {δ : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) 1) (q : Circle × Ico (0 : ℝ) 1) :
    (annulusPoint hδ q : ℂ) = (1 + δ * q.2) • (q.1 : ℂ) := by
  simp [annulusPoint, Circle.coe_homeomorphSphere_apply]

private lemma isEmbedding_annulusPoint {δ : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) 1) :
    IsEmbedding (annulusPoint hδ) := by
  refine IsEmbedding.subtypeVal.of_comp_iff.1 ?_
  convert IsEmbedding.subtypeVal.comp ((homeomorphUnitSphereProdIcoAnnulus hδ.1).isEmbedding.comp
    (Circle.homeomorphSphere.isEmbedding.prodMap IsEmbedding.id)) using 1
  ext q
  simp [coe_annulusPoint, Circle.coe_homeomorphSphere_apply]

private lemma range_annulusPoint {δ : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) 1) :
    range (annulusPoint hδ) = {z : CoordinateDisc.ball | 1 ≤ ‖(z : ℂ)‖ ∧ ‖(z : ℂ)‖ < 1 + δ} := by
  ext w
  constructor
  · rintro ⟨q, rfl⟩
    exact (homeomorphUnitSphereProdIcoAnnulus hδ.1 (Circle.homeomorphSphere q.1, q.2)).property
  · intro hw
    obtain ⟨p, hp⟩ := (homeomorphUnitSphereProdIcoAnnulus hδ.1).surjective ⟨(w : ℂ), hw⟩
    exact ⟨(Circle.homeomorphSphere.symm p.1, p.2), Subtype.ext (by
      simpa [annulusPoint] using congrArg Subtype.val hp)⟩

omit [TopologicalSpace ι] [DiscreteTopology ι] in
/-- Widths `δ i ∈ (0, 1)` such that the images under the coordinate discs of the balls of radius
`1 + δ i` are pairwise disjoint. -/
private lemma exists_radius (hφ : Pairwise (Disjoint on fun i ↦ (φ i).disc)) :
    ∃ δ : ι → ℝ, (∀ i, δ i ∈ Ioo (0 : ℝ) 1) ∧
      Pairwise (Disjoint on fun i ↦ φ i '' {z | ‖(z : ℂ)‖ < 1 + δ i}) := by
  obtain ⟨U, hU, hUd⟩ := Pairwise.exists_mem_filter_basis_of_disjoint
    (hφ.mono fun i j h ↦ separatedNhds_iff_disjoint.1 <|
      SeparatedNhds.of_isCompact_isCompact (φ i).isCompact_disc (φ j).isCompact_disc h)
    fun i ↦ hasBasis_nhdsSet (φ i).disc
  have key : ∀ i, ∃ ε, 0 < ε ∧ ∀ z : CoordinateDisc.ball, ‖(z : ℂ)‖ < 1 + ε → φ i z ∈ U i := by
    intro i
    have ho : IsOpen (Subtype.val '' (φ i ⁻¹' U i) : Set ℂ) :=
      CoordinateDisc.ball.isOpen.isOpenMap_subtypeVal _ ((hU i).1.preimage (φ i).continuous)
    obtain ⟨ε, hε, hεU⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_thickening_subset_open ho
      fun z hz ↦ ⟨⟨z, CoordinateDisc.mem_ball_of_norm_le_one (mem_closedBall_zero_iff.1 hz)⟩,
        (hU i).2 ((φ i).apply_mem_disc_iff.2 (mem_closedBall_zero_iff.1 hz)), rfl⟩
    refine ⟨ε, hε, fun z hz ↦ ?_⟩
    rw [thickening_closedBall hε zero_le_one] at hεU
    obtain ⟨w, hw, hwz⟩ := hεU (mem_ball_zero_iff.2 (by linarith))
    rwa [Subtype.ext hwz] at hw
  choose ε hε hεU using key
  refine ⟨fun i ↦ min (ε i) (1 / 2), fun i ↦ ⟨lt_min (hε i) one_half_pos,
    (min_le_right _ _).trans_lt one_half_lt_one⟩, fun i j hij ↦ (hUd hij).mono ?_ ?_⟩ <;>
  · rintro _ ⟨z, hz, rfl⟩
    exact hεU _ z (hz.trans_le (by simp))

/-- **The boundary circles of disjoint coordinate discs are collared** in the complement of the
open discs. The collar of the circle of `φ i` is a thin annulus `1 ≤ |z| < 1 + δᵢ` of the chart. -/
theorem isCollared_discComplementBoundary (hφ : Pairwise (Disjoint on fun i ↦ (φ i).disc)) :
    IsCollared (discComplementBoundary φ hφ) := by
  obtain ⟨δ, hδ, hd⟩ := exists_radius φ hφ
  have hsub (i : ι) (q : Circle × Ico (0 : ℝ) 1) :
      φ i (annulusPoint (hδ i) q) ∈ φ i '' {z | ‖(z : ℂ)‖ < 1 + δ i} :=
    mem_image_of_mem _ (range_annulusPoint (hδ i) ▸ mem_range_self q).2
  have hX (i : ι) (q : Circle × Ico (0 : ℝ) 1) :
      φ i (annulusPoint (hδ i) q) ∈ discComplement φ := by
    have h1 := (range_annulusPoint (hδ i) ▸ mem_range_self q).1
    refine (mem_discComplement_iff φ).2 fun j hj ↦ ?_
    obtain rfl | hij := eq_or_ne j i
    · exact ((φ j).apply_mem_openDisc_iff.1 hj).not_ge h1
    · exact (hd hij).notMem_of_mem_right (hsub i q) (image_mono (ofPred_subset_ofPred.2 fun z hz ↦
        hz.trans_le (by linarith [(hδ j).1])) ((φ j).openDisc_def ▸ hj))
  let c : ι × (Circle × Ico (0 : ℝ) 1) → discComplement φ := fun p ↦
    ⟨φ p.1 (annulusPoint (hδ p.1) p.2), hX p.1 p.2⟩
  have hci (i : ι) : IsOpenEmbedding fun q ↦ c (i, q) := by
    refine ⟨IsEmbedding.subtypeVal.of_comp_iff.1
      ((φ i).isOpenEmbedding.isEmbedding.comp (isEmbedding_annulusPoint (hδ i))), ?_⟩
    convert ((φ i).isOpenEmbedding.isOpenMap _ (isOpen_lt continuous_subtypeVal.norm
      continuous_const : IsOpen {z : CoordinateDisc.ball | ‖(z : ℂ)‖ < 1 + δ i})).preimage
      continuous_subtypeVal using 1
    ext x
    constructor
    · rintro ⟨q, rfl⟩
      exact hsub i q
    · rintro ⟨w, hw, hwx⟩
      have h1 : 1 ≤ ‖(w : ℂ)‖ := not_lt.1 fun h ↦
        (mem_discComplement_iff φ).1 x.property i (hwx ▸ (φ i).apply_mem_openDisc_iff.2 h)
      obtain ⟨q, hq⟩ : w ∈ range (annulusPoint (hδ i)) := range_annulusPoint (hδ i) ▸ ⟨h1, hw⟩
      exact ⟨q, Subtype.ext (by simp [c, hq, hwx])⟩
  have hc : IsOpenEmbedding c := by
    refine .of_continuous_injective_isOpenMap
      (continuous_prod_of_discrete_left.2 fun i ↦ (hci i).continuous) ?_
      (isOpenMap_prod_of_discrete_left.2 fun i ↦ (hci i).isOpenMap)
    rintro ⟨i, q⟩ ⟨j, q'⟩ h
    obtain rfl | hij := eq_or_ne i j
    · exact congrArg _ ((hci i).injective h)
    · exact absurd (congrArg Subtype.val h) ((hd hij).ne_of_mem (hsub i q) (hsub j q'))
  refine isCollared_iff.2 ⟨c ∘ Homeomorph.prodAssoc _ _ _,
    ⟨hc.comp (Homeomorph.prodAssoc _ _ _).isOpenEmbedding, fun p ↦ Subtype.ext ?_⟩⟩
  simp only [c, comp_apply, ← Homeomorph.coe_toEquiv, Homeomorph.prodAssoc_toEquiv,
    Equiv.prodAssoc_apply, coe_discComplementBoundary_apply,
    CoordinateDisc.boundaryCircle_apply]
  congr 1
  ext
  simp [coe_annulusPoint]

end SymplecticGeometry
