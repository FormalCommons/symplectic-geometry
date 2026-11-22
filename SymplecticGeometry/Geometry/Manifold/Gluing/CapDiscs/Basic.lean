/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.CoordinateDisc
public import SymplecticGeometry.Geometry.Manifold.Boundary.Collar.Interior
public import TauCeti.Geometry.Manifold.Gluing.GlueData
public import TauCeti.Geometry.Manifold.Instances.AddCircle
public import TauCeti.Topology.Category.TopCat.GlueData
import SymplecticGeometry.Geometry.Manifold.Instances.AddCircle
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.Basic
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import SymplecticGeometry.Geometry.Manifold.ModelTransport.Remodel
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Deriv
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective

/-!
# Capping the boundary circles of a surface with discs

Let `S` be a surface with boundary, modelled on the half-plane `EuclideanHalfSpace 2`, with a
smooth collar `c` of its boundary, and let `γ i : AddCircle 1 → ∂S`, for `i` in an index type `ι`,
be smooth local diffeomorphisms whose images are disjoint (the map `(i, θ) ↦ γ i θ` is injective).
The capped surface `SymplecticGeometry.capDiscs c γ hγ hinj` is glued (`TopCat.GlueData`) from
the interior of `S`, re-modelled on `ℝ²` as `SymplecticGeometry.InteriorModel`, and one copy
of the ball `CoordinateDisc.ball` of radius `2` of `ℂ` for each `i`, re-modelled on `ℝ²` along the
orthonormal basis `1, i` of `ℂ` (`SymplecticGeometry.Remodel`). The point `z` of the annulus
`1 < ‖z‖ < 2` of the `i`-th disc is identified with the interior point
`c (γ i (arg z / 2π), ‖z‖ - 1)`, and distinct discs are not glued to each other. When the
`γ i` together parametrize the whole boundary, this closes up the boundary circles of `S` with
discs.

The transition from the interior to the `i`-th annulus sends `c (γ i θ, t)` to
`(1 + t) · toCircle θ`. It is a local diffeomorphism, as the composite of the collar
coordinates (`TauCeti.SmoothCollar.interiorModelCoord`, restricted), the inverse of `γ i` on its
image, and polar coordinates (`AddCircle.isLocalDiffeomorphAt_ofReal_mul_toCircle`), and it
is bijective, so it is a diffeomorphism (`IsLocalDiffeomorph.diffeomorphOfBijective`); the
transition in the other direction is its inverse. Tau Ceti's
`TopCat.GlueData.IsCompatible.isManifold` then makes the glued space a smooth manifold. The
construction follows the gluing of `TauCeti.SmoothCollar.WithEnd`
(`Geometry/Manifold/Boundary/Collar/End.lean`).

## Main definitions

* `SymplecticGeometry.capDiscs`: the capped surface, a smooth manifold modelled on `ℝ²`.
* `SymplecticGeometry.capDiscs.inl`, `SymplecticGeometry.capDiscs.inr`: the inclusions of the
  interior of `S` and of the `i`-th disc.
* `SymplecticGeometry.capDiscs.gluingCoord`: the collar coordinates `(γ i (arg z / 2π), ‖z‖ - 1)`
  of a point `z` of the `i`-th disc.

## Main results

* `SymplecticGeometry.capDiscs.isLocalDiffeomorph_inl`, `isLocalDiffeomorph_inr`: the inclusions
  are smooth local diffeomorphisms.
* `SymplecticGeometry.isOpenEmbedding_capDiscs_inl`, `isOpenEmbedding_capDiscs_inr`: they are open
  embeddings.
* `SymplecticGeometry.capDiscs.inr_eq_inl`: the gluing formula on the annuli.
* `SymplecticGeometry.capDiscs.range_inl_union_iUnion_range_inr`: the interior and the discs cover
  the capped surface; `disjoint_range_inr`: distinct discs are disjoint;
  `inr_mem_range_inl_iff`: a point of a disc lies in the interior exactly on the annulus.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §2.7 (the first Chern number of bundles over surfaces).
* M. W. Hirsch, *Differential Topology*, Springer GTM 33, 1976, Chapter 8, §2 (gluing manifolds
  along boundaries by collars).
* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Springer GTM 218, 2013,
  Chapter 1 (the smooth manifold chart lemma).
-/

public section

open Set Function Topology Manifold TopologicalSpace CategoryTheory Complex
open scoped Manifold ContDiff Real

noncomputable section

namespace SymplecticGeometry

open TauCeti TauCeti.EuclideanHalfSpace CoordinateDisc AddCircle

variable {S : Type} [TopologicalSpace S] [ChartedSpace (EuclideanHalfSpace 2) S]
  [IsManifold (𝓡∂ 2) ∞ S]

local instance : IsManifold (𝓡 1) ∞ ((𝓡∂ 2).boundary S) := isManifold_boundary S

namespace capDiscs

/-! ### The interior piece -/

variable (S) in
/-- The interior of `S`, as a boundaryless manifold over `ℝ²`. -/
private abbrev InteriorPiece : Type := InteriorModel (𝓡∂ 2) ((𝓡∂ 2).interiorOpens S)

/-! ### The disc pieces -/

/-- The identification of `ℂ` with `ℝ²` by the orthonormal basis `1, i`. -/
private def complexDiffeomorph : ℂ ≃ₘ^∞⟮𝓘(ℝ, ℂ), 𝓡 2⟯ EuclideanSpace ℝ (Fin 2) :=
  Complex.orthonormalBasisOneI.repr.toContinuousLinearEquiv.toDiffeomorph

/-- The ball of radius `2` of `ℂ`, re-modelled on `ℝ²`. -/
private abbrev DiscPiece : Type := Remodel complexDiffeomorph ball

/-- The point of `ℂ` underlying a point of a disc piece. -/
private def DiscPiece.val (z : DiscPiece) : ℂ :=
  ((remodelDiffeomorph complexDiffeomorph ball).symm z : ℂ)

private theorem DiscPiece.continuous_val : Continuous DiscPiece.val :=
  continuous_subtypeVal.comp (remodelDiffeomorph complexDiffeomorph ball).symm.continuous

private theorem DiscPiece.val_remodelDiffeomorph (z : ball) :
    DiscPiece.val (remodelDiffeomorph complexDiffeomorph ball z) = z := by
  simp only [DiscPiece.val, Diffeomorph.symm_apply_apply]

private theorem DiscPiece.norm_val_lt (z : DiscPiece) : ‖z.val‖ < 2 :=
  mem_ball_iff.1 ((remodelDiffeomorph complexDiffeomorph ball).symm z).property

/-- The annulus `1 < ‖z‖ < 2` of a disc piece, along which it is glued to the interior. -/
private def annulus : Opens DiscPiece :=
  ⟨{z | 1 < ‖z.val‖}, isOpen_lt continuous_const DiscPiece.continuous_val.norm⟩

private theorem mem_annulus {z : DiscPiece} : z ∈ annulus ↔ 1 < ‖z.val‖ := Iff.rfl

/-! ### Collar coordinates and the overlaps -/

/-- The depth `t ∈ [0, 1)` of a collar point, as a real number. -/
private def depth (t : normalIioOpens 1) : ℝ := (t : EuclideanHalfSpace 1).val 0

private theorem depth_def (t : normalIioOpens 1) : depth t = (t : EuclideanHalfSpace 1).val 0 :=
  rfl

private theorem depth_nonneg (t : normalIioOpens 1) : 0 ≤ depth t :=
  (t : EuclideanHalfSpace 1).property

private theorem depth_lt_one (t : normalIioOpens 1) : depth t < 1 :=
  mem_normalIioOpens.1 t.property

private theorem depth_injective : Function.Injective depth := fun s t h ↦ by
  apply Subtype.ext
  rw [← normalRay_normalCoord (s : EuclideanHalfSpace 1),
    ← normalRay_normalCoord (t : EuclideanHalfSpace 1)]
  exact congrArg normalRay h

/-- The depth of a collar point is a local diffeomorphism where it is positive. -/
private theorem isLocalDiffeomorphAt_depth {t : normalIioOpens 1} (ht : 0 < depth t) :
    IsLocalDiffeomorphAt (𝓡∂ 1) 𝓘(ℝ) ∞ depth t := by
  have h := (isLocalDiffeomorph_subtype_val (n := ∞) t).comp
    (hg := isLocalDiffeomorphAt_val_zero ht)
  convert h using 1
  funext s
  rw [depth_def, comp_apply]

variable (c : SmoothCollar 1 ∞ S)

variable {ι : Type} (γ : ι → AddCircle (1 : ℝ) → (𝓡∂ 2).boundary S)

/-- The part of the interior piece covered by the collar over the image of `γ i`: the points
`c (γ i θ, t)` with `t > 0`. -/
private def interiorOverlap (hγ : ∀ i, IsLocalDiffeomorph 𝓘(ℝ) (𝓡 1) ∞ (γ i)) (i : ι) :
    Opens (InteriorPiece S) :=
  ⟨InteriorModel.val ⁻¹' (c '' (range (γ i) ×ˢ univ)),
    (c.isOpenEmbedding.isOpenMap _ ((hγ i).isOpen_range.prod isOpen_univ)).preimage
      InteriorModel.continuous_val⟩

variable {c γ} (hγ : ∀ i, IsLocalDiffeomorph 𝓘(ℝ) (𝓡 1) ∞ (γ i))

private theorem mem_interiorOverlap {i : ι} {q : InteriorPiece S} :
    q ∈ interiorOverlap c γ hγ i ↔ ∃ θ t, c (γ i θ, t) = q.val := by
  simp [interiorOverlap, ← SetLike.mem_coe]

private theorem interiorOverlap_le (i : ι) : interiorOverlap c γ hγ i ≤ c.interiorModelRange :=
  fun q hq ↦ by
    obtain ⟨θ, t, h⟩ := (mem_interiorOverlap hγ).1 hq
    exact c.mem_interiorModelRange.2 ⟨_, h⟩

/-- The collar coordinates of a point of the interior piece covered by the collar over the image
of `γ i`: the restriction of `c.interiorModelCoord`. -/
private def collarCoord {i : ι} (q : interiorOverlap c γ hγ i) :
    ↥((𝓡∂ 2).boundary S) × normalIioOpens 1 :=
  c.interiorModelCoord (Opens.inclusion (interiorOverlap_le hγ i) q)

@[simp] private theorem apply_collarCoord {i : ι} (q : interiorOverlap c γ hγ i) :
    c (collarCoord hγ q) = q.val.val := by
  rw [collarCoord, c.apply_interiorModelCoord, Opens.inclusion, Set.coe_inclusion
    (h := interiorOverlap_le hγ i)]

private theorem collarCoord_eq {i : ι} {q : interiorOverlap c γ hγ i} {θ : AddCircle (1 : ℝ)}
    {t : normalIioOpens 1} (h : c (γ i θ, t) = q.val.val) : collarCoord hγ q = (γ i θ, t) :=
  c.injective (by rw [apply_collarCoord, h])

private theorem exists_collarCoord_eq {i : ι} (q : interiorOverlap c γ hγ i) :
    ∃ θ, (collarCoord hγ q).1 = γ i θ := by
  obtain ⟨θ, t, h⟩ := (mem_interiorOverlap hγ).1 q.property
  exact ⟨θ, by rw [collarCoord_eq hγ h]⟩

private theorem depth_collarCoord_pos {i : ι} (q : interiorOverlap c γ hγ i) :
    0 < depth (collarCoord hγ q).2 :=
  c.interiorModelCoord_snd_pos _

private theorem isLocalDiffeomorph_collarCoord (i : ι) :
    IsLocalDiffeomorph (𝓡 2) ((𝓡 1).prod (𝓡∂ 1)) ∞ (collarCoord (c := c) (i := i) hγ) :=
  fun q ↦ (isLocalDiffeomorph_inclusion (interiorOverlap_le hγ i) q).comp
    (hg := c.isLocalDiffeomorph_interiorModelCoord _)

/-! ### The angle of a boundary point -/

variable (hinj : Function.Injective fun p : ι × AddCircle (1 : ℝ) ↦ γ p.1 p.2)

section

omit [IsManifold (𝓡∂ 2) ∞ S]

variable (γ) in
/-- The angle of a point `x` of the image of `γ i`: the `θ` with `γ i θ = x`. -/
private def angle (i : ι) (x : (𝓡∂ 2).boundary S) : AddCircle (1 : ℝ) := invFunOn (γ i) univ x

include hinj in
private theorem injective_apply (i : ι) : Function.Injective (γ i) :=
  hinj.comp (Prod.mk_right_injective i)

include hinj in
private theorem angle_apply (i : ι) (θ : AddCircle (1 : ℝ)) : angle γ i (γ i θ) = θ :=
  injective_apply hinj i (invFunOn_eq ⟨θ, trivial, rfl⟩)

include hinj hγ in
private theorem isLocalDiffeomorphAt_angle (i : ι) (θ : AddCircle (1 : ℝ)) :
    IsLocalDiffeomorphAt (𝓡 1) 𝓘(ℝ) ∞ (angle γ i) (γ i θ) := by
  let Φ := ((hγ i).isLocalDiffeomorphOn univ).partialDiffeomorphOfInjOn isOpen_univ
    (injective_apply hinj i).injOn
  refine isLocalDiffeomorphAt_of_eqOn (Φ := Φ.symm) ?_ fun y _ ↦ ?_
  · simp [Φ]
  · simp [Φ, angle]

end

include hinj in
private theorem apply_angle_collarCoord {i : ι} (q : interiorOverlap c γ hγ i) :
    γ i (angle γ i (collarCoord hγ q).1) = (collarCoord hγ q).1 := by
  obtain ⟨θ, hθ⟩ := exists_collarCoord_eq hγ q
  rw [hθ, angle_apply hinj]

/-! ### The gluing map from the interior to the annuli -/

/-- The point `(1 + t) · toCircle θ` of the plane, for a point `c (γ i θ, t)` of the interior. -/
private def polarPoint {i : ι} (q : interiorOverlap c γ hγ i) : ℂ :=
  ((1 + depth (collarCoord hγ q).2 : ℝ) : ℂ) * (toCircle (angle γ i (collarCoord hγ q).1) : ℂ)

private theorem norm_polarPoint {i : ι} (q : interiorOverlap c γ hγ i) :
    ‖polarPoint hγ q‖ = 1 + depth (collarCoord hγ q).2 := by
  have := depth_nonneg (collarCoord hγ q).2
  rw [polarPoint, norm_mul, Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by linarith)]

private theorem one_lt_norm_polarPoint {i : ι} (q : interiorOverlap c γ hγ i) :
    1 < ‖polarPoint hγ q‖ := by
  rw [norm_polarPoint]
  linarith [depth_collarCoord_pos hγ q]

private theorem polarPoint_mem_ball {i : ι} (q : interiorOverlap c γ hγ i) :
    polarPoint hγ q ∈ ball := by
  rw [mem_ball_iff, norm_polarPoint]
  linarith [depth_lt_one (collarCoord hγ q).2]

/-- The point of the ball glued to a point of the interior. -/
private def toBall {i : ι} (q : interiorOverlap c γ hγ i) : ball :=
  ⟨polarPoint hγ q, polarPoint_mem_ball hγ q⟩

/-- The gluing map from the part of the interior covered by the collar over `γ i` to the
annulus of the `i`-th disc. -/
private def toAnnulus {i : ι} (q : interiorOverlap c γ hγ i) : annulus :=
  ⟨remodelDiffeomorph complexDiffeomorph ball (toBall hγ q), by
    rw [mem_annulus, DiscPiece.val_remodelDiffeomorph]
    exact one_lt_norm_polarPoint hγ q⟩

private theorem val_toAnnulus {i : ι} (q : interiorOverlap c γ hγ i) :
    (toAnnulus hγ q).val = remodelDiffeomorph complexDiffeomorph ball (toBall hγ q) :=
  rfl

private theorem val_toAnnulus_val {i : ι} (q : interiorOverlap c γ hγ i) :
    (toAnnulus hγ q).val.val = polarPoint hγ q :=
  DiscPiece.val_remodelDiffeomorph _

include hinj in
private theorem isLocalDiffeomorphAt_polarPoint {i : ι} (q : interiorOverlap c γ hγ i) :
    IsLocalDiffeomorphAt (𝓡 2) 𝓘(ℝ, ℂ) ∞ (polarPoint hγ) q := by
  obtain ⟨θ, hθ⟩ := exists_collarCoord_eq hγ q
  have hd := depth_collarCoord_pos hγ q
  have hr : 1 + depth (collarCoord hγ q).2 ≠ 0 := by linarith
  have hshift : IsLocalDiffeomorph 𝓘(ℝ) 𝓘(ℝ) ∞ (fun s : ℝ ↦ 1 + s) :=
    isLocalDiffeomorph_of_deriv_ne_zero (contDiff_const.add contDiff_id) (by simp) fun _ ↦ by
      simp
  have hangle := isLocalDiffeomorphAt_angle hγ hinj i θ
  rw [← hθ] at hangle
  have hpair : IsLocalDiffeomorphAt ((𝓡 1).prod (𝓡∂ 1)) (𝓘(ℝ).prod 𝓘(ℝ)) ∞
      (Prod.map (angle γ i) (fun t ↦ 1 + depth t)) (collarCoord hγ q) :=
    hangle.prodMap ((isLocalDiffeomorphAt_depth hd).comp (hg := hshift _))
  exact ((isLocalDiffeomorph_collarCoord hγ i q).comp (hg := hpair)).comp
    (hg := AddCircle.isLocalDiffeomorphAt_ofReal_mul_toCircle hr)

include hinj in
private theorem isLocalDiffeomorph_toAnnulus (i : ι) :
    IsLocalDiffeomorph (𝓡 2) (𝓡 2) ∞ (toAnnulus (c := c) (i := i) hγ) := fun q ↦ by
  refine isLocalDiffeomorphAt_subtypeVal_comp_iff.1 ?_
  have hball : IsLocalDiffeomorphAt (𝓡 2) 𝓘(ℝ, ℂ) ∞ (toBall hγ) q :=
    isLocalDiffeomorphAt_subtypeVal_comp_iff.1 (isLocalDiffeomorphAt_polarPoint hγ hinj q)
  exact hball.comp (hg := (remodelDiffeomorph complexDiffeomorph ball).isLocalDiffeomorph _)

include hinj in
private theorem injective_toAnnulus (i : ι) :
    Function.Injective (toAnnulus (c := c) (i := i) hγ) := fun q q' h ↦ by
  have hp : polarPoint hγ q = polarPoint hγ q' := by
    rw [← val_toAnnulus_val, ← val_toAnnulus_val, h]
  have hdepth : (collarCoord hγ q).2 = (collarCoord hγ q').2 := by
    have := congrArg norm hp
    rw [norm_polarPoint, norm_polarPoint, add_right_inj] at this
    exact depth_injective this
  have hangle : angle γ i (collarCoord hγ q).1 = angle γ i (collarCoord hγ q').1 := by
    refine injective_toCircle one_ne_zero (Subtype.ext ?_)
    have h1 : ((1 + depth (collarCoord hγ q).2 : ℝ) : ℂ) ≠ 0 := by
      have := depth_nonneg (collarCoord hγ q).2
      exact_mod_cast (show (1 + depth (collarCoord hγ q).2 : ℝ) ≠ 0 by linarith)
    rw [polarPoint, polarPoint, ← hdepth] at hp
    exact mul_left_cancel₀ h1 hp
  have hcoord : collarCoord hγ q = collarCoord hγ q' := by
    rw [Prod.ext_iff, ← apply_angle_collarCoord hγ hinj q, ← apply_angle_collarCoord hγ hinj q',
      hangle]
    exact ⟨rfl, hdepth⟩
  apply Subtype.ext
  apply InteriorModel.val_injective
  rw [← apply_collarCoord hγ q, ← apply_collarCoord hγ q', hcoord]

section

omit [IsManifold (𝓡∂ 2) ∞ S]

variable (γ) in
/-- The collar coordinates `(γ i (arg z / 2π), ‖z‖ - 1)` that the gluing assigns to a point `z` of
the `i`-th disc; the depth `‖z‖ - 1` is truncated at `0` for `‖z‖ ≤ 1`. -/
def gluingCoord (i : ι) (z : ball) : ↥((𝓡∂ 2).boundary S) × normalIioOpens 1 :=
  (γ i ((arg z / (2 * π) : ℝ) : AddCircle (1 : ℝ)), ⟨normalRay (‖(z : ℂ)‖ - 1), by
    rw [mem_normalIioOpens, normalRay_coe_apply]
    exact max_lt (by linarith [mem_ball_iff.1 z.property]) one_pos⟩)

@[simp] theorem gluingCoord_fst (i : ι) (z : ball) :
    (gluingCoord γ i z).1 = γ i ((arg z / (2 * π) : ℝ) : AddCircle (1 : ℝ)) :=
  (rfl)

@[simp] theorem coe_gluingCoord_snd (i : ι) (z : ball) :
    ((gluingCoord γ i z).2 : EuclideanHalfSpace 1) = normalRay (‖(z : ℂ)‖ - 1) :=
  (rfl)

private theorem depth_gluingCoord {i : ι} {z : ball} (hz : 1 < ‖(z : ℂ)‖) :
    depth (gluingCoord γ i z).2 = ‖(z : ℂ)‖ - 1 := by
  rw [depth_def, coe_gluingCoord_snd, normalRay_coe_apply, max_eq_left (by linarith)]

end

variable (c) in
/-- The point of `S` glued to a point `z` with `1 < ‖z‖` of a disc is an interior point. -/
theorem apply_gluingCoord_mem_interiorOpens {i : ι} {z : ball} (hz : 1 < ‖(z : ℂ)‖) :
    c (gluingCoord γ i z) ∈ (𝓡∂ 2).interiorOpens S := by
  rw [← SetLike.mem_coe, ModelWithCorners.coe_interiorOpens, c.apply_mem_interior_iff_pos,
    ← depth_def, depth_gluingCoord hz]
  linarith

/-- The point of the interior glued to a point `z` of the annulus of the `i`-th disc. -/
private def gluingPoint (i : ι) {z : ball} (hz : 1 < ‖(z : ℂ)‖) : interiorOverlap c γ hγ i :=
  ⟨interiorModelDiffeomorph (𝓡∂ 2) ((𝓡∂ 2).interiorOpens S) ∞
    ⟨c (gluingCoord γ i z), apply_gluingCoord_mem_interiorOpens c hz⟩, by
    rw [mem_interiorOverlap, coe_interiorModelDiffeomorph,
      InteriorModel.val_interiorModelHomeomorph]
    exact ⟨_, _, rfl⟩⟩

private theorem val_gluingPoint (i : ι) {z : ball} (hz : 1 < ‖(z : ℂ)‖) :
    (gluingPoint (c := c) hγ i hz).val =
      interiorModelDiffeomorph (𝓡∂ 2) ((𝓡∂ 2).interiorOpens S) ∞
        ⟨c (gluingCoord γ i z), apply_gluingCoord_mem_interiorOpens c hz⟩ :=
  rfl

include hinj in
private theorem polarPoint_gluingPoint (i : ι) {z : ball} (hz : 1 < ‖(z : ℂ)‖) :
    polarPoint hγ (gluingPoint (c := c) hγ i hz) = z := by
  have hcoord : collarCoord hγ (gluingPoint (c := c) hγ i hz) = gluingCoord γ i z :=
    c.injective (by
      rw [apply_collarCoord, val_gluingPoint, coe_interiorModelDiffeomorph,
        InteriorModel.val_interiorModelHomeomorph])
  rw [polarPoint, hcoord, depth_gluingCoord hz, gluingCoord_fst, angle_apply hinj,
    toCircle_apply_mk, Circle.coe_exp]
  conv_rhs => rw [← norm_mul_exp_arg_mul_I (z : ℂ)]
  congr 2
  · ring
  · field_simp

include hinj in
private theorem toAnnulus_gluingPoint (i : ι) {z : ball} (hz : 1 < ‖(z : ℂ)‖) :
    toAnnulus hγ (gluingPoint (c := c) hγ i hz) =
      ⟨remodelDiffeomorph complexDiffeomorph ball z, by
        rwa [mem_annulus, DiscPiece.val_remodelDiffeomorph]⟩ := by
  apply Subtype.ext
  rw [val_toAnnulus]
  exact congrArg (remodelDiffeomorph complexDiffeomorph ball)
    (Subtype.ext (polarPoint_gluingPoint hγ hinj i hz))

include hinj in
private theorem surjective_toAnnulus (i : ι) :
    Function.Surjective (toAnnulus (c := c) (i := i) hγ) := fun z ↦ by
  have hz : 1 < ‖(((remodelDiffeomorph complexDiffeomorph ball).symm z.val : ball) : ℂ)‖ :=
    mem_annulus.1 z.property
  refine ⟨gluingPoint hγ i hz, ?_⟩
  rw [toAnnulus_gluingPoint hγ hinj]
  exact Subtype.ext ((remodelDiffeomorph complexDiffeomorph ball).apply_symm_apply z.val)

/-- The gluing map from the part of the interior covered by the collar over `γ i` to the annulus
of the `i`-th disc, as a diffeomorphism. -/
private def annulusDiffeomorph (i : ι) :
    interiorOverlap c γ hγ i ≃ₘ^∞⟮𝓡 2, 𝓡 2⟯ annulus :=
  (isLocalDiffeomorph_toAnnulus hγ hinj i).diffeomorphOfBijective
    ⟨injective_toAnnulus hγ hinj i, surjective_toAnnulus hγ hinj i⟩

private theorem coe_annulusDiffeomorph (i : ι) :
    ⇑(annulusDiffeomorph hγ hinj i) = toAnnulus (c := c) hγ :=
  IsLocalDiffeomorph.coe_diffeomorphOfBijective _ _

include hinj in
/-- The interior and the discs overlap in distinct places for distinct discs. -/
private theorem eq_of_mem_interiorOverlap {i j : ι} {q : InteriorPiece S}
    (hi : q ∈ interiorOverlap c γ hγ i) (hj : q ∈ interiorOverlap c γ hγ j) : i = j := by
  obtain ⟨θ, t, hθ⟩ := (mem_interiorOverlap hγ).1 hi
  obtain ⟨θ', t', hθ'⟩ := (mem_interiorOverlap hγ).1 hj
  have h := c.injective (hθ.trans hθ'.symm)
  exact congrArg Prod.fst (hinj (a₁ := (i, θ)) (a₂ := (j, θ')) (congrArg Prod.fst h))

/-! ### The gluing data -/

variable (S ι) in
/-- The pieces of the gluing: the interior of `S`, and one disc for each `i : ι`. -/
private def piece : Option ι → TopCat
  | none => TopCat.of (InteriorPiece S)
  | some _ => TopCat.of DiscPiece

variable (c γ) in
/-- The overlaps of the gluing. -/
private def overlap : ∀ i : Option ι, Option ι → Opens (piece S ι i)
  | none, none => ⊤
  | none, some i => interiorOverlap c γ hγ i
  | some _, none => annulus
  | some i, some j => ⟨{_z | i = j}, isOpen_const⟩

private theorem mem_overlap_some_some {i j : ι} {z : DiscPiece} :
    z ∈ overlap c γ hγ (some i) (some j) ↔ i = j :=
  Iff.rfl

variable (c γ) in
/-- The transition maps of the gluing. -/
private def transition : ∀ i j : Option ι,
    (Opens.toTopCat _).obj (overlap c γ hγ i j) ⟶ (Opens.toTopCat _).obj (overlap c γ hγ j i)
  | none, none => 𝟙 _
  | none, some i =>
    TopCat.ofHom ⟨annulusDiffeomorph hγ hinj i, (annulusDiffeomorph hγ hinj i).continuous⟩
  | some i, none => TopCat.ofHom ⟨(annulusDiffeomorph hγ hinj i).symm,
      (annulusDiffeomorph hγ hinj i).symm.continuous⟩
  | some i, some j => TopCat.ofHom ⟨Opens.inclusion (U := overlap c γ hγ (some i) (some j))
      (V := overlap c γ hγ (some j) (some i))
      fun _ h ↦ (mem_overlap_some_some hγ).2 ((mem_overlap_some_some hγ).1 h).symm,
      continuous_inclusion _⟩

variable (c γ) in
/-- The gluing data of the capped surface: the interior of `S`, and for each `i : ι` the ball of
radius `2` of `ℂ`, glued along `z ↦ c (γ i (arg z / 2π), ‖z‖ - 1)` on the annulus `1 < ‖z‖ < 2`;
distinct discs are not glued to each other. -/
def glueData : TopCat.GlueData :=
  TopCat.GlueData.mk'
    { J := Option ι
      U := piece S ι
      V := overlap c γ hγ
      t := transition c γ hγ hinj
      V_id := by
        rintro (_ | i)
        · rfl
        · exact SetLike.coe_injective (eq_univ_of_forall fun _ ↦ rfl)
      t_id := by rintro (_ | i) <;> rfl
      t_inter := by
        rintro (_ | i) (_ | j) (_ | k) x hx
        · trivial
        · exact hx
        · exact (transition c γ hγ hinj _ _ x).property
        · exact (mem_overlap_some_some hγ).2 (eq_of_mem_interiorOverlap hγ hinj x.property hx)
        · trivial
        · obtain rfl := (mem_overlap_some_some hγ).1 hx
          exact (transition c γ hγ hinj _ _ x).property
        · exact hx
        · exact (mem_overlap_some_some hγ).2
            (((mem_overlap_some_some hγ).1 x.property).symm.trans
              ((mem_overlap_some_some hγ).1 hx))
      cocycle := by
        rintro (_ | i) (_ | j) (_ | k) x hx
        · rfl
        · rfl
        · exact congrArg Subtype.val ((annulusDiffeomorph hγ hinj j).symm_apply_apply x)
        · obtain rfl := eq_of_mem_interiorOverlap hγ hinj x.property hx
          rfl
        · rfl
        · obtain rfl := (mem_overlap_some_some hγ).1 hx
          exact congrArg Subtype.val ((annulusDiffeomorph hγ hinj i).apply_symm_apply x)
        · obtain rfl := (mem_overlap_some_some hγ).1 x.property
          rfl
        · rfl }

private instance instChartedSpacePiece :
    ∀ i : Option ι, ChartedSpace (EuclideanSpace ℝ (Fin 2)) (piece S ι i)
  | none => inferInstanceAs (ChartedSpace _ (InteriorPiece S))
  | some _ => inferInstanceAs (ChartedSpace _ DiscPiece)

private instance instIsManifoldPiece : ∀ i : Option ι, IsManifold (𝓡 2) ∞ (piece S ι i)
  | none => inferInstanceAs (IsManifold _ ∞ (InteriorPiece S))
  | some _ => inferInstanceAs (IsManifold _ ∞ DiscPiece)

private instance (i : (glueData c γ hγ hinj).J) :
    ChartedSpace (EuclideanSpace ℝ (Fin 2)) ((glueData c γ hγ hinj).U i) :=
  instChartedSpacePiece i

private instance (i : (glueData c γ hγ hinj).J) :
    IsManifold (𝓡 2) ∞ ((glueData c γ hγ hinj).U i) :=
  instIsManifoldPiece i

private instance (p : (glueData c γ hγ hinj).J × (glueData c γ hγ hinj).J) :
    ChartedSpace (EuclideanSpace ℝ (Fin 2)) ((glueData c γ hγ hinj).V p) :=
  letI := instChartedSpacePiece (S := S) p.1
  (overlap c γ hγ p.1 p.2).instChartedSpace

private theorem isCompatible_glueData : (glueData c γ hγ hinj).IsCompatible (𝓡 2) ∞ := by
  refine .of_isLocalDiffeomorph_t (fun i j ↦ isLocalDiffeomorph_subtype_val) ?_
  rintro (_ | i) (_ | j)
  · exact (Diffeomorph.refl (𝓡 2) _ ∞).isLocalDiffeomorph
  · exact (annulusDiffeomorph hγ hinj j).isLocalDiffeomorph
  · exact (annulusDiffeomorph hγ hinj i).symm.isLocalDiffeomorph
  · exact isLocalDiffeomorph_inclusion (U := overlap c γ hγ (some i) (some j))
      (W := overlap c γ hγ (some j) (some i)) fun _ h ↦
      (mem_overlap_some_some hγ).2 ((mem_overlap_some_some hγ).1 h).symm

include hinj in
private theorem annulusDiffeomorph_symm_apply (i : ι) {z : ball} (hz : 1 < ‖(z : ℂ)‖) :
    (annulusDiffeomorph hγ hinj i).symm
        ⟨remodelDiffeomorph complexDiffeomorph ball z, by
          rwa [mem_annulus, DiscPiece.val_remodelDiffeomorph]⟩ =
      gluingPoint (c := c) hγ i hz := by
  rw [← toAnnulus_gluingPoint hγ hinj i hz, ← coe_annulusDiffeomorph hγ hinj,
    Diffeomorph.symm_apply_apply]

end capDiscs

variable (c : SmoothCollar 1 ∞ S) {ι : Type} (γ : ι → AddCircle (1 : ℝ) → (𝓡∂ 2).boundary S)
  (hγ : ∀ i, IsLocalDiffeomorph 𝓘(ℝ) (𝓡 1) ∞ (γ i))
  (hinj : Function.Injective fun p : ι × AddCircle (1 : ℝ) ↦ γ p.1 p.2)

/-- **The surface `S` capped with discs.** Let `c` be a smooth collar of the boundary of the
surface `S`, and `γ i : AddCircle 1 → ∂S`, for `i : ι`, local diffeomorphisms whose images are
disjoint circles of the boundary (`hinj`). The surface `capDiscs c γ hγ hinj` is glued from the
interior of `S` and one copy of the ball of radius `2` of `ℂ` for each `i`: the point `z` of the
annulus `1 < ‖z‖ < 2` of the `i`-th disc is identified with the point
`c (γ i (arg z / 2π), ‖z‖ - 1)` of the interior (`capDiscs.inr_eq_inl`). It is a smooth manifold
without boundary modelled on `ℝ²`. -/
def capDiscs : Type :=
  (capDiscs.glueData c γ hγ hinj).toGlueData.glued

namespace capDiscs

instance : TopologicalSpace (capDiscs c γ hγ hinj) :=
  inferInstanceAs (TopologicalSpace (glueData c γ hγ hinj).toGlueData.glued)

/-- The atlas of `capDiscs c γ hγ hinj`, transported from the atlases of its pieces. -/
@[instance_reducible]
def chartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 2)) (capDiscs c γ hγ hinj) :=
  (glueData c γ hγ hinj).chartedSpace (EuclideanSpace ℝ (Fin 2))

instance : ChartedSpace (EuclideanSpace ℝ (Fin 2)) (capDiscs c γ hγ hinj) :=
  chartedSpace c γ hγ hinj

instance : IsManifold (𝓡 2) ∞ (capDiscs c γ hγ hinj) :=
  (isCompatible_glueData hγ hinj).isManifold

/-- The inclusion of the interior of `S` into the capped surface. -/
def inl (p : (𝓡∂ 2).interiorOpens S) : capDiscs c γ hγ hinj :=
  (glueData c γ hγ hinj).toGlueData.ι none
    (interiorModelDiffeomorph (𝓡∂ 2) ((𝓡∂ 2).interiorOpens S) ∞ p)

/-- The inclusion of the ball of radius `2` of `ℂ` into the capped surface as the `i`-th disc. -/
def inr (i : ι) (z : ball) : capDiscs c γ hγ hinj :=
  (glueData c γ hγ hinj).toGlueData.ι (some i) (remodelDiffeomorph complexDiffeomorph ball z)

private theorem range_inl :
    range (inl c γ hγ hinj) = range ((glueData c γ hγ hinj).toGlueData.ι none) :=
  ((interiorModelDiffeomorph (𝓡∂ 2) ((𝓡∂ 2).interiorOpens S) ∞).surjective.range_comp _)

private theorem range_inr (i : ι) :
    range (inr c γ hγ hinj i) = range ((glueData c γ hγ hinj).toGlueData.ι (some i)) :=
  ((remodelDiffeomorph complexDiffeomorph ball).surjective.range_comp _)

/-- The inclusion of the interior of `S` is a smooth local diffeomorphism. -/
theorem isLocalDiffeomorph_inl : IsLocalDiffeomorph (𝓡∂ 2) (𝓡 2) ∞ (inl c γ hγ hinj) := fun p ↦
  ((interiorModelDiffeomorph (𝓡∂ 2) ((𝓡∂ 2).interiorOpens S) ∞).isLocalDiffeomorph p).comp
    (hg := (isCompatible_glueData hγ hinj).isLocalDiffeomorph_ι none _)

/-- The inclusion of each disc is a smooth local diffeomorphism. -/
theorem isLocalDiffeomorph_inr (i : ι) :
    IsLocalDiffeomorph 𝓘(ℝ, ℂ) (𝓡 2) ∞ (inr c γ hγ hinj i) := fun z ↦
  ((remodelDiffeomorph complexDiffeomorph ball).isLocalDiffeomorph z).comp
    (hg := (isCompatible_glueData hγ hinj).isLocalDiffeomorph_ι (some i) _)

end capDiscs

/-- The interior of `S` is an open subset of the capped surface. -/
theorem isOpenEmbedding_capDiscs_inl : IsOpenEmbedding (capDiscs.inl c γ hγ hinj) :=
  ((capDiscs.glueData c γ hγ hinj).ι_isOpenEmbedding none).comp
    (interiorModelDiffeomorph (𝓡∂ 2) ((𝓡∂ 2).interiorOpens S) ∞).toHomeomorph.isOpenEmbedding

/-- Each disc is an open subset of the capped surface. -/
theorem isOpenEmbedding_capDiscs_inr (i : ι) : IsOpenEmbedding (capDiscs.inr c γ hγ hinj i) :=
  ((capDiscs.glueData c γ hγ hinj).ι_isOpenEmbedding (some i)).comp
    (remodelDiffeomorph capDiscs.complexDiffeomorph ball).toHomeomorph.isOpenEmbedding

namespace capDiscs

/-- **The gluing formula.** A point `z` of the `i`-th disc with `1 < ‖z‖` is the point
`c (γ i (arg z / 2π), ‖z‖ - 1)` of the interior of `S`. -/
theorem inr_eq_inl {i : ι} {z : ball} (hz : 1 < ‖(z : ℂ)‖) :
    inr c γ hγ hinj i z =
      inl c γ hγ hinj ⟨c (gluingCoord γ i z), apply_gluingCoord_mem_interiorOpens c hz⟩ := by
  have hw : remodelDiffeomorph complexDiffeomorph ball z ∈ annulus := by
    rwa [mem_annulus, DiscPiece.val_remodelDiffeomorph]
  -- The maps `f i j` of a glue data built by `TopCat.GlueData.mk'` are the inclusions of the
  -- overlaps, so the first condition of the relation holds by `rfl`.
  refine ((glueData c γ hγ hinj).ι_eq_iff_rel (some i) none _ _).2 ⟨⟨_, hw⟩, rfl, ?_⟩
  exact (congrArg Subtype.val (annulusDiffeomorph_symm_apply hγ hinj i hz)).trans
    (val_gluingPoint hγ i hz)

/-- The interior of `S` and the discs cover the capped surface. -/
theorem range_inl_union_iUnion_range_inr :
    range (inl c γ hγ hinj) ∪ ⋃ i, range (inr c γ hγ hinj i) = univ := by
  refine eq_univ_of_forall fun x ↦ ?_
  obtain ⟨_ | i, y, rfl⟩ := (glueData c γ hγ hinj).ι_jointly_surjective x
  · exact Or.inl (range_inl c γ hγ hinj ▸ mem_range_self y)
  · exact Or.inr (mem_iUnion.2 ⟨i, range_inr c γ hγ hinj i ▸ mem_range_self y⟩)

/-- Distinct discs are disjoint in the capped surface. -/
theorem disjoint_range_inr {i j : ι} (hij : i ≠ j) :
    Disjoint (range (inr c γ hγ hinj i)) (range (inr c γ hγ hinj j)) := by
  refine Set.disjoint_iff.2 ?_
  rintro _ ⟨⟨a, rfl⟩, ⟨b, hb⟩⟩
  obtain ⟨y⟩ := ((glueData c γ hγ hinj).range_ι_inter_range_ι_nonempty_iff (some i) (some j)).1
    ⟨inr c γ hγ hinj i a, ⟨_, rfl⟩, ⟨_, hb⟩⟩
  exact (hij ((mem_overlap_some_some (c := c) hγ).1 y.property)).elim

/-- A point `z` of a disc lies in the interior of `S` exactly when `1 < ‖z‖`. -/
theorem inr_mem_range_inl_iff {i : ι} {z : ball} :
    inr c γ hγ hinj i z ∈ range (inl c γ hγ hinj) ↔ 1 < ‖(z : ℂ)‖ := by
  refine ⟨fun ⟨p, hp⟩ ↦ ?_, fun hz ↦ ⟨_, (inr_eq_inl c γ hγ hinj hz).symm⟩⟩
  obtain ⟨x, hx, -⟩ := ((glueData c γ hγ hinj).ι_eq_iff_rel (some i) none _ _).1 hp.symm
  -- `f (some i) none` is the inclusion of the annulus into the disc piece.
  have hx' : (x.val : DiscPiece) = remodelDiffeomorph complexDiffeomorph ball z := hx
  have h : 1 < ‖(x.val : DiscPiece).val‖ := mem_annulus.1 x.property
  rwa [hx', DiscPiece.val_remodelDiffeomorph] at h

end capDiscs

end SymplecticGeometry
