/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import SymplecticGeometry.Geometry.Manifold.Instances.Surface.Genus
public import TauCeti.AlgebraicTopology.FundamentalGroup.HomotopyEquiv
import SymplecticGeometry.Topology.Instances.AddCircle.Icc
import TauCeti.Topology.Homotopy.PuncturedStarConvex

/-!
# The punctured torus retracts onto its two circles through `0`

The torus `SymplecticGeometry.EuclideanTorus`, punctured at the centre `([1 / 2], [1 / 2])` of the
coordinate ball `SymplecticGeometry.EuclideanTorus.ball` along which it is summed, deforms onto
the union `SymplecticGeometry.EuclideanTorus.circles` of its two circles `{x | x i = 0}` through
`0`, keeping these circles fixed. So the inclusion of the two circles is a homotopy equivalence,
and it induces an isomorphism of fundamental groups at `0`.

The torus is the image of the unit square `[0, 1]²` of `ℝ × ℝ` under `z ↦ ([z.1], [z.2])`, a
continuous surjection from a compact space onto a Hausdorff one; its centre `(1 / 2, 1 / 2)` goes
to the puncture, its boundary onto the two circles, and only boundary points are identified. In
the sup norm of `ℝ × ℝ` the boundary of the square is the sphere of radius `1 / 2` about the
centre, so Tau Ceti's `StarConvex.radialHomotopy` deforms the punctured square onto its boundary,
keeping the boundary fixed. Since it fixes the points that the map identifies, it descends to the
punctured torus, along the restriction of the map to the punctured square, which is closed and
hence a quotient map. The descent follows the private `deform` and `retraction` of Tau Ceti's
`TauCeti.TwoCellAttachment` (`AlgebraicTopology/FundamentalGroup/TwoCellAttachment.lean`), which
descend Tau Ceti's `unitInterval.radialPush` to the complement of the centres of attached
2-cells; here the deformation of the punctured square itself is used, so that the homotopy stays
in the punctured torus. The description of the boundary of the square as a sphere follows the
private `sphere_subset_Icc_prod_Icc` and `prodMap_val_mem_sphere_iff` of Tau Ceti's
`Topology/UnitInterval/OpenSquare.lean`.

## Main definitions

* `SymplecticGeometry.EuclideanTorus.circles`: the two circles of the torus through `0`.
* `SymplecticGeometry.EuclideanTorus.circlesInclusion`: their inclusion into the punctured torus.
* `SymplecticGeometry.EuclideanTorus.circlesRetraction`: the retraction of the punctured torus
  onto them.
* `SymplecticGeometry.EuclideanTorus.circlesHomotopyRel`: a homotopy, fixed on the two circles,
  from the retraction followed by the inclusion to the identity of the punctured torus.
* `SymplecticGeometry.EuclideanTorus.circlesHomotopyEquiv`: the inclusion, as a homotopy
  equivalence.
* `SymplecticGeometry.EuclideanTorus.circlesFundamentalGroupMulEquiv`: the isomorphism of
  fundamental groups at `0` induced by the inclusion.

## Main results

* `SymplecticGeometry.EuclideanTorus.circlesRetraction_comp_circlesInclusion`: the retraction is a
  left inverse of the inclusion.
* `SymplecticGeometry.EuclideanTorus.diffeomorph_circlesHomotopyRel_apply`,
  `SymplecticGeometry.EuclideanTorus.diffeomorph_circlesRetraction_apply`: the homotopy and the
  retraction in the coordinates of the square.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002 (the punctured torus
  deforms onto the wedge of two circles).
-/

public section

noncomputable section

open Set Metric Topology TauCeti unitInterval
open scoped ContinuousMap

namespace SymplecticGeometry

namespace EuclideanTorus

/-- The **two circles** `{x | x 0 = 0}` and `{x | x 1 = 0}` of the torus through its base point
`0`, a wedge of two circles. -/
def circles : Set EuclideanTorus := {x | diffeomorph x 0 = 0} ∪ {x | diffeomorph x 1 = 0}

/-- A point lies on the two circles when one of its coordinates is `0`. -/
theorem mem_circles_iff {x : EuclideanTorus} :
    x ∈ circles ↔ diffeomorph x 0 = 0 ∨ diffeomorph x 1 = 0 :=
  Iff.rfl

/-- The base point `0` lies on the two circles. -/
theorem zero_mem_circles : (0 : EuclideanTorus) ∈ circles :=
  Or.inl (by rw [mem_ofPred_eq, diffeomorph_zero, Pi.zero_apply])

/-- The two circles miss the puncture, the centre of the coordinate ball of the torus. -/
theorem circles_subset_puncture : circles ⊆ ConnectedSum.puncture ball := by
  intro x hx
  rw [SetLike.mem_coe, ConnectedSum.mem_puncture]
  rintro rfl
  rcases hx with hx | hx
  · exact disjoint_left.1 (disjoint_closure_range_ball 0) (subset_closure ⟨0, rfl⟩) hx
  · exact disjoint_left.1 (disjoint_closure_range_ball 1) (subset_closure ⟨0, rfl⟩) hx

/-- The base point `0` of the torus is not the puncture. -/
theorem zero_mem_puncture : (0 : EuclideanTorus) ∈ ConnectedSum.puncture ball :=
  circles_subset_puncture zero_mem_circles

/-! ### The unit square -/

/-- The centre `(1 / 2, 1 / 2)` of the unit square of `ℝ × ℝ`. -/
private def centre : ℝ × ℝ := (1 / 2, 1 / 2)

/-- The unit square of `ℝ × ℝ`. -/
private def square : Set (ℝ × ℝ) := Icc 0 1 ×ˢ Icc 0 1

private theorem starConvex_square : StarConvex ℝ centre square :=
  ((convex_Icc 0 1).prod (convex_Icc 0 1)).starConvex ⟨by norm_num [centre], by norm_num [centre]⟩

/-- A point of the square lies on the sphere of radius `1 / 2` about the centre, in the sup norm,
exactly when one of its coordinates is `0` or `1`. -/
private theorem mem_sphere_centre_iff {z : ℝ × ℝ} (hz : z ∈ square) :
    z ∈ sphere centre (1 / 2) ↔ (z.1 = 0 ∨ z.1 = 1) ∨ (z.2 = 0 ∨ z.2 = 1) := by
  obtain ⟨⟨h₁, h₂⟩, h₃, h₄⟩ := hz
  rw [mem_sphere, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  simp only [centre]
  have e₁ : |z.1 - 1 / 2| ≤ 1 / 2 := abs_le.2 ⟨by linarith, by linarith⟩
  have e₂ : |z.2 - 1 / 2| ≤ 1 / 2 := abs_le.2 ⟨by linarith, by linarith⟩
  have k (a : ℝ) (h₀ : 0 ≤ a) (h₁ : a ≤ 1) : |a - 1 / 2| = 1 / 2 ↔ a = 0 ∨ a = 1 := by
    rw [abs_eq (by norm_num)]
    constructor
    · rintro (h | h)
      · right; linarith
      · left; linarith
    · rintro (rfl | rfl) <;> norm_num
  rw [← k _ h₁ h₂, ← k _ h₃ h₄]
  constructor
  · intro h
    rcases max_choice |z.1 - 1 / 2| |z.2 - 1 / 2| with h' | h' <;> rw [h'] at h
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · rw [h, max_eq_left (h ▸ e₂)]
    · rw [h, max_eq_right (h ▸ e₁)]

/-- The map `z ↦ ([z.1], [z.2])` of `ℝ × ℝ` onto the torus. -/
private def squareMap (z : ℝ × ℝ) : EuclideanTorus :=
  diffeomorph.symm ![(z.1 : AddCircle (1 : ℝ)), z.2]

private theorem diffeomorph_squareMap_zero (z : ℝ × ℝ) :
    diffeomorph (squareMap z) 0 = z.1 := by
  rw [squareMap, Diffeomorph.apply_symm_apply, Matrix.cons_val_zero]

private theorem diffeomorph_squareMap_one (z : ℝ × ℝ) :
    diffeomorph (squareMap z) 1 = z.2 := by
  rw [squareMap, Diffeomorph.apply_symm_apply, Matrix.cons_val_one, Matrix.cons_val_zero]

private theorem continuous_squareMap : Continuous squareMap :=
  diffeomorph.symm.continuous.comp (continuous_pi fun i ↦ by
    fin_cases i
    · exact (AddCircle.continuous_mk' 1).comp continuous_fst
    · exact (AddCircle.continuous_mk' 1).comp continuous_snd)

/-- Two points of the torus with the same coordinates are equal. -/
private theorem ext_diffeomorph {x y : EuclideanTorus} (h₀ : diffeomorph x 0 = diffeomorph y 0)
    (h₁ : diffeomorph x 1 = diffeomorph y 1) : x = y := by
  rw [← diffeomorph.symm_apply_apply x, ← diffeomorph.symm_apply_apply y]
  exact congrArg diffeomorph.symm (funext (Fin.forall_fin_two.2 ⟨h₀, h₁⟩))

private theorem squareMap_eq_iff {z w : ℝ × ℝ} :
    squareMap z = squareMap w ↔
      (z.1 : AddCircle (1 : ℝ)) = w.1 ∧ (z.2 : AddCircle (1 : ℝ)) = w.2 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ext_diffeomorph ?_ ?_⟩
  · rw [← diffeomorph_squareMap_zero, ← diffeomorph_squareMap_one, h, diffeomorph_squareMap_zero,
      diffeomorph_squareMap_one]
    exact ⟨rfl, rfl⟩
  · rw [diffeomorph_squareMap_zero, diffeomorph_squareMap_zero, h.1]
  · rw [diffeomorph_squareMap_one, diffeomorph_squareMap_one, h.2]

/-- Every point of the torus is the image of a point of the square. -/
private theorem exists_mem_square_squareMap_eq (x : EuclideanTorus) :
    ∃ z ∈ square, squareMap z = x := by
  obtain ⟨a, ha⟩ := QuotientAddGroup.mk_surjective (diffeomorph x 0)
  obtain ⟨b, hb⟩ := QuotientAddGroup.mk_surjective (diffeomorph x 1)
  refine ⟨(Int.fract a, Int.fract b), ⟨⟨Int.fract_nonneg a, (Int.fract_lt_one a).le⟩,
    ⟨Int.fract_nonneg b, (Int.fract_lt_one b).le⟩⟩, ext_diffeomorph ?_ ?_⟩
  · rw [diffeomorph_squareMap_zero]
    exact (AddCircle.coe_fract a).trans ha
  · rw [diffeomorph_squareMap_one]
    exact (AddCircle.coe_fract b).trans hb

/-- The map sends the centre of the square, and no other point of it, to the puncture. -/
private theorem squareMap_eq_ball_zero_iff {z : ℝ × ℝ} (hz : z ∈ square) :
    squareMap z = ball 0 ↔ z = centre := by
  have hc : squareMap centre = ball 0 := ext_diffeomorph
    (by rw [diffeomorph_squareMap_zero, diffeomorph_ball_zero, centre])
    (by rw [diffeomorph_squareMap_one, diffeomorph_ball_zero, centre])
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ hc⟩
  have hm : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) (0 + 1) := ⟨by norm_num, by norm_num⟩
  obtain ⟨h₁, h₂⟩ := squareMap_eq_iff.1 (h.trans hc.symm)
  have k {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (h : (a : AddCircle (1 : ℝ)) = (1 / 2 : ℝ)) :
      a = 1 / 2 := by
    rcases (AddCircle.coe_eq_coe_iff_of_mem_Icc (by rwa [zero_add]) hm).1 h with
      h | ⟨-, h⟩ | ⟨-, h⟩ <;> norm_num at h
    exact h
  exact Prod.ext (k hz.1 h₁) (k hz.2 h₂)

/-- The map sends a point of the square to the two circles exactly when it lies on the boundary
of the square. -/
private theorem squareMap_mem_circles_iff {z : ℝ × ℝ} (hz : z ∈ square) :
    squareMap z ∈ circles ↔ z ∈ sphere centre (1 / 2) := by
  rw [mem_sphere_centre_iff hz, mem_circles_iff, diffeomorph_squareMap_zero,
    diffeomorph_squareMap_one, AddCircle.coe_eq_zero_iff_of_mem_Icc hz.1,
    AddCircle.coe_eq_zero_iff_of_mem_Icc hz.2]

/-- Two points of the square with the same image are equal, or both on its boundary. -/
private theorem eq_or_mem_sphere_of_squareMap_eq {z w : ℝ × ℝ} (hz : z ∈ square)
    (hw : w ∈ square) (h : squareMap z = squareMap w) :
    z = w ∨ (z ∈ sphere centre (1 / 2) ∧ w ∈ sphere centre (1 / 2)) := by
  obtain ⟨h₁, h₂⟩ := squareMap_eq_iff.1 h
  rw [mem_sphere_centre_iff hz, mem_sphere_centre_iff hw]
  have k {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1)
      (h : (a : AddCircle (1 : ℝ)) = b) : a = b ∨ ((a = 0 ∨ a = 1) ∧ (b = 0 ∨ b = 1)) := by
    rw [AddCircle.coe_eq_coe_iff_of_mem_Icc (a := 0) (by rwa [zero_add]) (by rwa [zero_add]),
      zero_add] at h
    tauto
  rcases k hz.1 hw.1 h₁ with e₁ | ⟨e₁, e₁'⟩
  · rcases k hz.2 hw.2 h₂ with e₂ | ⟨e₂, e₂'⟩
    · exact Or.inl (Prod.ext e₁ e₂)
    · exact Or.inr ⟨Or.inr e₂, Or.inr e₂'⟩
  · exact Or.inr ⟨Or.inl e₁, Or.inl e₁'⟩

/-! ### The deformation of the punctured square onto its boundary -/

private theorem sphere_subset_square : sphere centre (1 / 2) ⊆ square := by
  intro z hz
  rw [mem_sphere, Prod.dist_eq, Real.dist_eq, Real.dist_eq] at hz
  have h₁ := abs_le.1 ((le_max_left _ _).trans hz.le)
  have h₂ := abs_le.1 ((le_max_right _ _).trans hz.le)
  simp only [centre] at h₁ h₂
  exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

/-- The square punctured at its centre. -/
private abbrev PuncturedSquare : Type := ↥(square \ {centre})

/-- The radial deformation of the punctured square onto its boundary, Tau Ceti's
`StarConvex.radialHomotopy`, from the radial projection to the identity. -/
private def squareHomotopy :=
  starConvex_square.radialHomotopy (by norm_num : (0 : ℝ) < 1 / 2) sphere_subset_square

/-- The deformation fixes the boundary of the square. -/
private theorem squareHomotopy_apply_of_mem_sphere (t : I) {z : PuncturedSquare}
    (hz : (z : ℝ × ℝ) ∈ sphere centre (1 / 2)) : squareHomotopy (t, z) = z := by
  refine Subtype.ext ?_
  rw [squareHomotopy, StarConvex.coe_radialHomotopy_apply, ← dist_eq_norm, mem_sphere.1 hz,
    div_self (by norm_num)]
  simp

/-- At time `0` the deformation sends the punctured square to its boundary. -/
private theorem squareHomotopy_zero_mem_sphere (z : PuncturedSquare) :
    (squareHomotopy (0, z) : ℝ × ℝ) ∈ sphere centre (1 / 2) := by
  rw [ContinuousMap.Homotopy.apply_zero, ContinuousMap.comp_apply,
    coe_sphereInclusionDiffSingleton_apply]
  exact Subtype.property _

private theorem squareMap_mem_puncture (z : PuncturedSquare) :
    squareMap z ∈ ConnectedSum.puncture ball :=
  ConnectedSum.mem_puncture.2 fun h ↦ z.property.2 (mem_singleton_iff.2 ((squareMap_eq_ball_zero_iff
    z.property.1).1 h))

/-- The map `z ↦ ([z.1], [z.2])` of the punctured square onto the punctured torus. -/
private def puncturedSquareMap (z : PuncturedSquare) : ConnectedSum.puncture ball :=
  ⟨squareMap z, squareMap_mem_puncture z⟩

private theorem coe_puncturedSquareMap (z : PuncturedSquare) :
    (puncturedSquareMap z : EuclideanTorus) = squareMap z :=
  (rfl)

private theorem continuous_puncturedSquareMap : Continuous puncturedSquareMap :=
  (continuous_squareMap.comp continuous_subtypeVal).subtype_mk _

private theorem puncturedSquareMap_surjective : Function.Surjective puncturedSquareMap := by
  intro x
  obtain ⟨z, hz, hzx⟩ := exists_mem_square_squareMap_eq x
  refine ⟨⟨z, hz, fun h ↦ ConnectedSum.mem_puncture.1 x.property ?_⟩, Subtype.ext hzx⟩
  rw [← hzx, squareMap_eq_ball_zero_iff hz]
  exact h

/-- The map of the punctured square onto the punctured torus is closed: the image of a closed set
is the trace on the punctured torus of the image of a compact subset of the square. -/
private theorem isClosedMap_puncturedSquareMap : IsClosedMap puncturedSquareMap := by
  intro C hC
  obtain ⟨C', hC', rfl⟩ := IsInducing.subtypeVal.isClosed_iff.1 hC
  have hK : IsCompact (C' ∩ square) := (isCompact_Icc.prod isCompact_Icc).inter_left hC'
  refine IsInducing.subtypeVal.isClosed_iff.2
    ⟨squareMap '' (C' ∩ square), (hK.image continuous_squareMap).isClosed, ?_⟩
  ext x
  constructor
  · rintro ⟨w, ⟨hwC, hwK⟩, hw⟩
    refine ⟨⟨w, hwK, fun h ↦ ConnectedSum.mem_puncture.1 x.property ?_⟩, hwC, Subtype.ext hw⟩
    rw [← hw, squareMap_eq_ball_zero_iff hwK]
    exact h
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, ⟨hz, z.property.1⟩, rfl⟩

private theorem isQuotientMap_puncturedSquareMap : IsQuotientMap puncturedSquareMap :=
  isClosedMap_puncturedSquareMap.isQuotientMap continuous_puncturedSquareMap
    puncturedSquareMap_surjective

/-! ### The deformation of the punctured torus onto the two circles -/

/-- The radial deformation of the punctured square, carried to the punctured torus. -/
private def deform (t : I) (x : ConnectedSum.puncture ball) : ConnectedSum.puncture ball :=
  puncturedSquareMap (squareHomotopy (t, Function.surjInv puncturedSquareMap_surjective x))

/-- The deformation of the punctured torus is that of the punctured square: the points that the
map identifies lie on the boundary of the square, which the deformation fixes. -/
private theorem deform_puncturedSquareMap (t : I) (z : PuncturedSquare) :
    deform t (puncturedSquareMap z) = puncturedSquareMap (squareHomotopy (t, z)) := by
  rw [deform]
  have hw := Function.surjInv_eq puncturedSquareMap_surjective (puncturedSquareMap z)
  set w := Function.surjInv puncturedSquareMap_surjective (puncturedSquareMap z)
  rcases eq_or_mem_sphere_of_squareMap_eq w.property.1 z.property.1 (congrArg Subtype.val hw) with
    h | ⟨h₁, h₂⟩
  · rw [Subtype.ext h]
  · rw [squareHomotopy_apply_of_mem_sphere t h₁, squareHomotopy_apply_of_mem_sphere t h₂, hw]

private theorem continuous_deform :
    Continuous fun p : I × ConnectedSum.puncture ball ↦ deform p.1 p.2 :=
  isQuotientMap_puncturedSquareMap.continuous_lift_prod_right (by
    simp only [deform_puncturedSquareMap, Prod.mk.eta]
    exact continuous_puncturedSquareMap.comp squareHomotopy.continuous)

private theorem deform_zero_mem_circles (x : ConnectedSum.puncture ball) :
    (deform 0 x : EuclideanTorus) ∈ circles := by
  obtain ⟨z, rfl⟩ := puncturedSquareMap_surjective x
  rw [deform_puncturedSquareMap, coe_puncturedSquareMap,
    squareMap_mem_circles_iff (squareHomotopy (0, z)).property.1]
  exact squareHomotopy_zero_mem_sphere z

private theorem deform_one (x : ConnectedSum.puncture ball) : deform 1 x = x := by
  obtain ⟨z, rfl⟩ := puncturedSquareMap_surjective x
  rw [deform_puncturedSquareMap, ContinuousMap.Homotopy.apply_one, ContinuousMap.id_apply]

private theorem deform_of_mem_circles (t : I) {x : ConnectedSum.puncture ball}
    (hx : (x : EuclideanTorus) ∈ circles) : deform t x = x := by
  obtain ⟨z, rfl⟩ := puncturedSquareMap_surjective x
  rw [coe_puncturedSquareMap, squareMap_mem_circles_iff z.property.1] at hx
  rw [deform_puncturedSquareMap, squareHomotopy_apply_of_mem_sphere t hx]

/-- The inclusion of the two circles of the torus through `0` into the punctured torus. -/
-- Exposed so that its value `⟨0, _⟩` at `0`, the base point of the fundamental groups that it
-- relates, holds by `rfl` in the statements of this and other files.
@[expose] def circlesInclusion : C(circles, ConnectedSum.puncture ball) :=
  ⟨fun x ↦ ⟨x, circles_subset_puncture x.property⟩, continuous_subtypeVal.subtype_mk _⟩

/-- The inclusion does not move points. -/
@[simp]
theorem coe_circlesInclusion_apply (x : circles) :
    (circlesInclusion x : EuclideanTorus) = x :=
  (rfl)

/-- The **retraction of the punctured torus onto its two circles through `0`**: the radial
deformation of the punctured square `[0, 1]²` onto its boundary, at its end, carried to the
torus by `z ↦ ([z.1], [z.2])`. It is a left inverse of the inclusion
(`SymplecticGeometry.EuclideanTorus.circlesRetraction_comp_circlesInclusion`), and its composite
with the inclusion is homotopic to the identity relative to the two circles
(`SymplecticGeometry.EuclideanTorus.circlesHomotopyRel`). -/
def circlesRetraction : C(ConnectedSum.puncture ball, circles) :=
  ⟨fun x ↦ ⟨deform 0 x, deform_zero_mem_circles x⟩,
    (continuous_subtypeVal.comp (continuous_deform.comp
      (continuous_const.prodMk continuous_id))).subtype_mk _⟩

private theorem circlesInclusion_circlesRetraction (x : ConnectedSum.puncture ball) :
    circlesInclusion (circlesRetraction x) = deform 0 x :=
  (rfl)

private theorem coe_circlesRetraction (x : ConnectedSum.puncture ball) :
    (circlesRetraction x : EuclideanTorus) = deform 0 x :=
  (rfl)

/-- The retraction fixes the two circles. -/
@[simp]
theorem circlesRetraction_circlesInclusion (x : circles) :
    circlesRetraction (circlesInclusion x) = x :=
  Subtype.ext ((coe_circlesRetraction _).trans
    (congrArg Subtype.val (deform_of_mem_circles 0 (x := circlesInclusion x) x.property)))

/-- The retraction is a left inverse of the inclusion. -/
theorem circlesRetraction_comp_circlesInclusion :
    circlesRetraction.comp circlesInclusion = ContinuousMap.id circles :=
  ContinuousMap.ext circlesRetraction_circlesInclusion

/-- The **deformation of the punctured torus onto its two circles through `0`**: a homotopy from
the retraction onto the two circles, followed by their inclusion, to the identity of the
punctured torus, which fixes the points of the two circles. It is the radial deformation of the
punctured square `[0, 1]²` onto its boundary, carried to the torus by `z ↦ ([z.1], [z.2])`. -/
def circlesHomotopyRel :
    (circlesInclusion.comp circlesRetraction).HomotopyRel (ContinuousMap.id _)
      (Subtype.val ⁻¹' circles) where
  toFun p := deform p.1 p.2
  continuous_toFun := continuous_deform
  map_zero_left x := (circlesInclusion_circlesRetraction x).symm
  map_one_left := deform_one
  prop' t x hx := (deform_of_mem_circles t hx).trans
    ((circlesInclusion_circlesRetraction x).trans (deform_of_mem_circles 0 hx)).symm

private theorem circlesHomotopyRel_apply (p : I × ConnectedSum.puncture ball) :
    circlesHomotopyRel p = deform p.1 p.2 :=
  (rfl)

/-- The homotopy in coordinates: at time `t`, the point `([a], [b])` of the punctured torus, with
`a`, `b` in `[0, 1]`, moves to `([1 / 2 + c (a - 1 / 2)], [1 / 2 + c (b - 1 / 2)])` along the
ray from the centre of the square, where `c = (1 - t) / (2 m) + t` and `m` is the sup-norm
distance `max |a - 1 / 2| |b - 1 / 2|` from `(a, b)` to the centre. -/
theorem diffeomorph_circlesHomotopyRel_apply (t : I) (x : ConnectedSum.puncture ball) {a b : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1)
    (hx : diffeomorph (x : EuclideanTorus) = ![(a : AddCircle (1 : ℝ)), b]) :
    diffeomorph (circlesHomotopyRel (t, x) : EuclideanTorus) =
      ![((1 / 2 + ((1 - t) * (1 / 2 / max |a - 1 / 2| |b - 1 / 2|) + t) * (a - 1 / 2) : ℝ) :
          AddCircle (1 : ℝ)),
        ((1 / 2 + ((1 - t) * (1 / 2 / max |a - 1 / 2| |b - 1 / 2|) + t) * (b - 1 / 2) : ℝ) :
          AddCircle (1 : ℝ))] := by
  have hxz : (x : EuclideanTorus) = squareMap (a, b) := by
    rw [← diffeomorph.symm_apply_apply (x : EuclideanTorus), hx, squareMap]
  have hz : (a, b) ∈ square \ {centre} := ⟨⟨ha, hb⟩, fun h ↦ ConnectedSum.mem_puncture.1 x.property
    (hxz.trans ((squareMap_eq_ball_zero_iff ⟨ha, hb⟩).2 h))⟩
  obtain rfl : x = puncturedSquareMap ⟨(a, b), hz⟩ := Subtype.ext hxz
  rw [circlesHomotopyRel_apply, deform_puncturedSquareMap, coe_puncturedSquareMap, squareMap,
    Diffeomorph.apply_symm_apply, squareHomotopy, StarConvex.coe_radialHomotopy_apply]
  simp [centre, Prod.norm_def]

/-- The retraction in coordinates: the point `([a], [b])` of the punctured torus, with `a`, `b` in
`[0, 1]`, goes to `([1 / 2 + (a - 1 / 2) / (2 m)], [1 / 2 + (b - 1 / 2) / (2 m)])`, its radial
projection from the centre of the square onto its boundary, where `m` is the sup-norm distance
`max |a - 1 / 2| |b - 1 / 2|` from `(a, b)` to the centre. -/
theorem diffeomorph_circlesRetraction_apply (x : ConnectedSum.puncture ball) {a b : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1)
    (hx : diffeomorph (x : EuclideanTorus) = ![(a : AddCircle (1 : ℝ)), b]) :
    diffeomorph (circlesRetraction x : EuclideanTorus) =
      ![((1 / 2 + 1 / 2 / max |a - 1 / 2| |b - 1 / 2| * (a - 1 / 2) : ℝ) : AddCircle (1 : ℝ)),
        ((1 / 2 + 1 / 2 / max |a - 1 / 2| |b - 1 / 2| * (b - 1 / 2) : ℝ) : AddCircle (1 : ℝ))] := by
  rw [← coe_circlesInclusion_apply, ← ContinuousMap.comp_apply, ← circlesHomotopyRel.apply_zero,
    diffeomorph_circlesHomotopyRel_apply 0 x ha hb hx]
  simp

/-- The two circles of the torus through `0` are a strong deformation retract of the punctured
torus: their inclusion is a homotopy equivalence, with the retraction
`SymplecticGeometry.EuclideanTorus.circlesRetraction` as its inverse. -/
def circlesHomotopyEquiv : circles ≃ₕ ConnectedSum.puncture ball where
  toFun := circlesInclusion
  invFun := circlesRetraction
  left_inv := circlesRetraction_comp_circlesInclusion ▸ ContinuousMap.Homotopic.refl _
  right_inv := ⟨circlesHomotopyRel.toHomotopy⟩

@[simp]
theorem circlesHomotopyEquiv_toFun : circlesHomotopyEquiv.toFun = circlesInclusion :=
  (rfl)

@[simp]
theorem circlesHomotopyEquiv_invFun : circlesHomotopyEquiv.invFun = circlesRetraction :=
  (rfl)

/-- The **fundamental group of the punctured torus** at `0` is that of its two circles through
`0`: the isomorphism induced by their inclusion. -/
def circlesFundamentalGroupMulEquiv :
    FundamentalGroup circles ⟨0, zero_mem_circles⟩ ≃*
      FundamentalGroup (ConnectedSum.puncture ball) ⟨0, zero_mem_puncture⟩ :=
  MulEquiv.ofBijective (FundamentalGroup.map circlesInclusion ⟨0, zero_mem_circles⟩)
    (circlesHomotopyEquiv.fundamentalGroup_map_bijective _)

/-- The isomorphism maps the class of a loop in the two circles to that of the same loop in the
punctured torus. -/
@[simp]
theorem circlesFundamentalGroupMulEquiv_apply (a : FundamentalGroup circles ⟨0, zero_mem_circles⟩) :
    circlesFundamentalGroupMulEquiv a = FundamentalGroup.map circlesInclusion _ a :=
  (rfl)

end EuclideanTorus

end SymplecticGeometry

end
