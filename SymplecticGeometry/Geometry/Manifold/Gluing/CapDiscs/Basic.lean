/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.CoordinateDisc
public import TauCeti.Geometry.Manifold.Instances.AddCircle
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective
public import TauCeti.Geometry.Manifold.Boundary.Collar.Smooth
public import SymplecticGeometry.Geometry.Manifold.IsManifold.InteriorBoundary
import SymplecticGeometry.Geometry.Manifold.Boundary.Charts
import SymplecticGeometry.Geometry.Manifold.Boundary.Collar.Interior
import SymplecticGeometry.Geometry.Manifold.Gluing.Pair
import SymplecticGeometry.Geometry.Manifold.Boundary.Collar.Local
import SymplecticGeometry.Geometry.Manifold.Instances.AddCircle
import SymplecticGeometry.Geometry.Manifold.Instances.HalfLine.Basic
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import SymplecticGeometry.Geometry.Manifold.ModelTransport.Remodel
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Deriv
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Sigma
import TauCeti.Topology.Compactness.Normed
import SymplecticGeometry.Geometry.Manifold.Boundary.Interior

/-!
# Capping the boundary circles of a surface with discs

Let `S` be a surface with boundary, modelled on the half-plane `EuclideanHalfSpace 2`, with a
smooth collar `c` of its boundary, and let `γ i : AddCircle 1 → ∂S`, for `i` in an index type `ι`,
be smooth local diffeomorphisms whose images are disjoint (the map `(i, θ) ↦ γ i θ` is injective).
The capped surface `SymplecticGeometry.capDiscs c γ hγ hinj` is glued from the interior of `S`,
as Tau Ceti's charted interior `(𝓡∂ 2).interior S` over `ℝ²`, and one copy of the ball
`CoordinateDisc.ball` of radius `2` of `ℂ` for each `i`, re-modelled on `ℝ²` along the
orthonormal basis `1, i` of `ℂ` (`SymplecticGeometry.Remodel`). The point `z` of the annulus
`1 < ‖z‖ < 2` of the `i`-th disc is identified with the interior point
`c (γ i (arg z / 2π), ‖z‖ - 1)`, and distinct discs are not glued to each other. When the
`γ i` together parametrize the whole boundary, this closes up the boundary circles of `S` with
discs.

The transition from the interior to the `i`-th annulus sends `c (γ i θ, t)` to
`(1 + t) · toCircle θ`. It is a local diffeomorphism, as the composite of the collar
coordinates (`TauCeti.SmoothCollar.interiorCoord`, restricted), the inverse of `γ i` on its
image, and polar coordinates (`AddCircle.isLocalDiffeomorphAt_ofReal_mul_toCircle`), and it
is bijective, so it is a diffeomorphism (`IsLocalDiffeomorph.diffeomorphOfBijective`); the
transition in the other direction is its inverse.

The capped surface is `SymplecticGeometry.GluedAlong` (`Geometry/Manifold/Gluing/Pair.lean`) of
one diffeomorphism between open subsets of two pieces: the interior of `S`, and the disjoint
union of the discs, a `Sigma` type over `ι` charted by Tau Ceti's `ChartedSpace.sigma`. The
diffeomorphism goes from the union of the parts of the interior covered by the collars over the
`γ i` onto the union of the annuli, and is the transition to the `i`-th annulus on the part
covered by the collar over `γ i`; these parts are disjoint because the images of the `γ i` are.
Its topology, atlas and smooth structure are those of `GluedAlong`, and the inclusions of the
interior and of the discs are `GluedAlong.inl` and `GluedAlong.inr`, composed with the
identification of the interior with Tau Ceti's charted interior and with the inclusion of each
disc into the disjoint union, a local diffeomorphism (`TauCeti.isLocalDiffeomorph_sigmaMk`).

The capped surface is Hausdorff when `S` is, by the criterion `GluedAlong.t2Space_iff`, the
two-piece form of Tau Ceti's `TopCat.GlueData.t2Space_iff_forall_nhds`. Both pieces are
Hausdorff, so it remains to separate an interior point `p` from a point `z` of the `i`-th disc
with `‖z‖ ≤ 1`. The point `p` lies off the compact circle `γ i`, hence, by compactness, off the
collar points `c (γ i θ, t)` for every `θ` and every small enough `t`; these are the points of an
annulus `1 < ‖z‖ < 1 + ε`.

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
* `SymplecticGeometry.capDiscs.inr_eq_inl`: the gluing formula on the annuli;
  `inr_ofReal_mul_toCircle_eq_inl`: its converse, from a collar point to the disc.
* `SymplecticGeometry.capDiscs.ofReal_one_add_mul_toCircle_gluingCoord`: a point `z` with
  `1 < ‖z‖` is `(1 + t) · toCircle θ` for its collar coordinates `(θ, t)`.
* `SymplecticGeometry.capDiscs.range_inl_union_iUnion_range_inr`: the interior and the discs cover
  the capped surface, and `exists_inl_or_exists_inr` splits a point accordingly;
  `disjoint_range_inr`: distinct discs are disjoint;
  `inr_mem_range_inl_iff`: a point of a disc lies in the interior exactly on the annulus.
* `SymplecticGeometry.capDiscs.instT2Space`: the capped surface is Hausdorff when `S` is.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §2.7 (the first Chern number of bundles over surfaces).
* M. W. Hirsch, *Differential Topology*, Springer GTM 33, 1976, Chapter 8, §2 (gluing manifolds
  along boundaries by collars).
* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Springer GTM 218, 2013,
  Chapter 1 (the smooth manifold chart lemma, and the Hausdorff condition on a glued space).
-/

public section

open Set Function Topology Manifold TopologicalSpace CategoryTheory Complex
open scoped Manifold ContDiff Real

noncomputable section

namespace SymplecticGeometry

open TauCeti TauCeti.EuclideanHalfSpace CoordinateDisc AddCircle

variable {S : Type} [TopologicalSpace S] [ChartedSpace (EuclideanHalfSpace 2) S]
  [IsManifold (𝓡∂ 2) ∞ S]

namespace capDiscs

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

variable (c : SmoothCollar 1 ∞ S)

variable {ι : Type} (γ : ι → AddCircle (1 : ℝ) → (𝓡∂ 2).boundary S)

/-- The part of the interior piece covered by the collar over the image of `γ i`: the points
`c (γ i θ, t)` with `t > 0`. -/
private def interiorOverlap (hγ : ∀ i, IsLocalDiffeomorph 𝓘(ℝ) (𝓡 1) ∞ (γ i)) (i : ι) :
    Opens ((𝓡∂ 2).interior S) :=
  ⟨Subtype.val ⁻¹' (c '' (range (γ i) ×ˢ univ)),
    (c.isOpenEmbedding.isOpenMap _ ((hγ i).isOpen_range.prod isOpen_univ)).preimage
      continuous_subtypeVal⟩

variable {c γ} (hγ : ∀ i, IsLocalDiffeomorph 𝓘(ℝ) (𝓡 1) ∞ (γ i))

omit [IsManifold (𝓡∂ 2) ∞ S] in
private theorem mem_interiorOverlap {i : ι} {q : (𝓡∂ 2).interior S} :
    q ∈ interiorOverlap c γ hγ i ↔ ∃ θ t, c (γ i θ, t) = q.val := by
  simp [interiorOverlap, ← SetLike.mem_coe]

omit [IsManifold (𝓡∂ 2) ∞ S] in
private theorem interiorOverlap_le (i : ι) : interiorOverlap c γ hγ i ≤ c.interiorRange :=
  fun q hq ↦ by
    obtain ⟨θ, t, h⟩ := (mem_interiorOverlap hγ).1 hq
    exact c.mem_interiorRange.2 ⟨_, h⟩

/-- The collar coordinates of a point of the interior piece covered by the collar over the image
of `γ i`: the restriction of `c.interiorCoord`. -/
private def collarCoord {i : ι} (q : interiorOverlap c γ hγ i) :
    ↥((𝓡∂ 2).boundary S) × normalIioOpens 1 :=
  c.interiorCoord (Opens.inclusion (interiorOverlap_le hγ i) q)

omit [IsManifold (𝓡∂ 2) ∞ S] in
@[simp] private theorem apply_collarCoord {i : ι} (q : interiorOverlap c γ hγ i) :
    c (collarCoord hγ q) = q.val.val := by
  rw [collarCoord, c.apply_interiorCoord, Opens.inclusion, Set.coe_inclusion
    (h := interiorOverlap_le hγ i)]

omit [IsManifold (𝓡∂ 2) ∞ S] in
private theorem collarCoord_eq {i : ι} {q : interiorOverlap c γ hγ i} {θ : AddCircle (1 : ℝ)}
    {t : normalIioOpens 1} (h : c (γ i θ, t) = q.val.val) : collarCoord hγ q = (γ i θ, t) :=
  c.injective (by rw [apply_collarCoord, h])

omit [IsManifold (𝓡∂ 2) ∞ S] in
private theorem exists_collarCoord_eq {i : ι} (q : interiorOverlap c γ hγ i) :
    ∃ θ, (collarCoord hγ q).1 = γ i θ := by
  obtain ⟨θ, t, h⟩ := (mem_interiorOverlap hγ).1 q.property
  exact ⟨θ, by rw [collarCoord_eq hγ h]⟩

omit [IsManifold (𝓡∂ 2) ∞ S] in
private theorem depth_collarCoord_pos {i : ι} (q : interiorOverlap c γ hγ i) :
    0 < ((collarCoord hγ q).2 : EuclideanHalfSpace 1).val 0 :=
  c.interiorCoord_snd_pos _

private theorem isLocalDiffeomorph_collarCoord (i : ι) :
    IsLocalDiffeomorph (𝓡 2) ((𝓡 1).prod (𝓡∂ 1)) ∞ (collarCoord (c := c) (i := i) hγ) :=
  fun q ↦ (isLocalDiffeomorph_inclusion (interiorOverlap_le hγ i) q).comp
    (hg := c.isLocalDiffeomorph_interiorCoord _)

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
omit [IsManifold (𝓡∂ 2) ∞ S] in
private theorem apply_angle_collarCoord {i : ι} (q : interiorOverlap c γ hγ i) :
    γ i (angle γ i (collarCoord hγ q).1) = (collarCoord hγ q).1 := by
  obtain ⟨θ, hθ⟩ := exists_collarCoord_eq hγ q
  rw [hθ, angle_apply hinj]

/-! ### The gluing map from the interior to the annuli -/

/-- The point `(1 + t) · toCircle θ` of the plane, for a depth `t ∈ [0, 1)`, has norm `1 + t`. -/
theorem norm_ofReal_one_add_mul_toCircle (t : normalIioOpens 1) (θ : AddCircle (1 : ℝ)) :
    ‖((1 + (t : EuclideanHalfSpace 1).val 0 : ℝ) : ℂ) * (toCircle θ : ℂ)‖ =
      1 + (t : EuclideanHalfSpace 1).val 0 := by
  have h : 0 ≤ (t : EuclideanHalfSpace 1).val 0 := (t : EuclideanHalfSpace 1).property
  rw [norm_mul, Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by linarith)]

/-- The point `(1 + t) · toCircle θ` of the plane, for a depth `t ∈ [0, 1)`, lies in the ball of
radius `2`. -/
theorem ofReal_one_add_mul_toCircle_mem_ball (t : normalIioOpens 1) (θ : AddCircle (1 : ℝ)) :
    ((1 + (t : EuclideanHalfSpace 1).val 0 : ℝ) : ℂ) * (toCircle θ : ℂ) ∈ ball := by
  rw [mem_ball_iff, norm_ofReal_one_add_mul_toCircle]
  linarith [mem_normalIioOpens.1 t.property]

/-- The point `(1 + t) · toCircle θ` of the plane, for a point `c (γ i θ, t)` of the interior. -/
private def polarPoint {i : ι} (q : interiorOverlap c γ hγ i) : ℂ :=
  ((1 + ((collarCoord hγ q).2 : EuclideanHalfSpace 1).val 0 : ℝ) : ℂ) *
    (toCircle (angle γ i (collarCoord hγ q).1) : ℂ)

omit [IsManifold (𝓡∂ 2) ∞ S] in
private theorem norm_polarPoint {i : ι} (q : interiorOverlap c γ hγ i) :
    ‖polarPoint hγ q‖ = 1 + ((collarCoord hγ q).2 : EuclideanHalfSpace 1).val 0 := by
  rw [polarPoint]
  exact norm_ofReal_one_add_mul_toCircle _ _

omit [IsManifold (𝓡∂ 2) ∞ S] in
private theorem one_lt_norm_polarPoint {i : ι} (q : interiorOverlap c γ hγ i) :
    1 < ‖polarPoint hγ q‖ := by
  rw [norm_polarPoint]
  linarith [depth_collarCoord_pos hγ q]

omit [IsManifold (𝓡∂ 2) ∞ S] in
private theorem polarPoint_mem_ball {i : ι} (q : interiorOverlap c γ hγ i) :
    polarPoint hγ q ∈ ball := by
  rw [polarPoint]
  exact ofReal_one_add_mul_toCircle_mem_ball _ _

/-- The point of the ball glued to a point of the interior. -/
private def toBall {i : ι} (q : interiorOverlap c γ hγ i) : ball :=
  ⟨polarPoint hγ q, polarPoint_mem_ball hγ q⟩

omit [IsManifold (𝓡∂ 2) ∞ S] in
private theorem coe_toBall {i : ι} (q : interiorOverlap c γ hγ i) :
    (toBall hγ q : ℂ) = polarPoint hγ q :=
  rfl

/-- The gluing map from the part of the interior covered by the collar over `γ i` to the
annulus of the `i`-th disc. -/
private def toAnnulus {i : ι} (q : interiorOverlap c γ hγ i) : annulus :=
  ⟨remodelDiffeomorph complexDiffeomorph ball (toBall hγ q), by
    rw [mem_annulus, DiscPiece.val_remodelDiffeomorph]
    exact one_lt_norm_polarPoint hγ q⟩

omit [IsManifold (𝓡∂ 2) ∞ S] in
private theorem val_toAnnulus {i : ι} (q : interiorOverlap c γ hγ i) :
    (toAnnulus hγ q).val = remodelDiffeomorph complexDiffeomorph ball (toBall hγ q) :=
  rfl

omit [IsManifold (𝓡∂ 2) ∞ S] in
private theorem val_toAnnulus_val {i : ι} (q : interiorOverlap c γ hγ i) :
    (toAnnulus hγ q).val.val = polarPoint hγ q :=
  DiscPiece.val_remodelDiffeomorph _

include hinj in
private theorem isLocalDiffeomorphAt_polarPoint {i : ι} (q : interiorOverlap c γ hγ i) :
    IsLocalDiffeomorphAt (𝓡 2) 𝓘(ℝ, ℂ) ∞ (polarPoint hγ) q := by
  obtain ⟨θ, hθ⟩ := exists_collarCoord_eq hγ q
  have hd := depth_collarCoord_pos hγ q
  have hr : 1 + ((collarCoord hγ q).2 : EuclideanHalfSpace 1).val 0 ≠ 0 := by linarith
  have hshift : IsLocalDiffeomorph 𝓘(ℝ) 𝓘(ℝ) ∞ (fun s : ℝ ↦ 1 + s) :=
    isLocalDiffeomorph_of_deriv_ne_zero (contDiff_const.add contDiff_id) (by simp) fun _ ↦ by
      simp
  have hangle := isLocalDiffeomorphAt_angle hγ hinj i θ
  rw [← hθ] at hangle
  have hpair : IsLocalDiffeomorphAt ((𝓡 1).prod (𝓡∂ 1)) (𝓘(ℝ).prod 𝓘(ℝ)) ∞
      (Prod.map (angle γ i) fun t : normalIioOpens 1 ↦ 1 + (t : EuclideanHalfSpace 1).val 0)
        (collarCoord hγ q) :=
    hangle.prodMap ((isLocalDiffeomorphAt_opens_val_zero hd).comp (hg := hshift _))
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
omit [IsManifold (𝓡∂ 2) ∞ S] in
private theorem injective_toAnnulus (i : ι) :
    Function.Injective (toAnnulus (c := c) (i := i) hγ) := fun q q' h ↦ by
  have hp : polarPoint hγ q = polarPoint hγ q' := by
    rw [← val_toAnnulus_val, ← val_toAnnulus_val, h]
  have hdepth : (collarCoord hγ q).2 = (collarCoord hγ q').2 := by
    have := congrArg norm hp
    rw [norm_polarPoint, norm_polarPoint, add_right_inj] at this
    exact (homeomorphNormalIioOpens 1).injective
      (Subtype.ext (by rwa [coe_homeomorphNormalIioOpens, coe_homeomorphNormalIioOpens]))
  have hangle : angle γ i (collarCoord hγ q).1 = angle γ i (collarCoord hγ q').1 := by
    refine injective_toCircle one_ne_zero (Subtype.ext ?_)
    have h1 : ((1 + ((collarCoord hγ q).2 : EuclideanHalfSpace 1).val 0 : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (by
        linarith [((collarCoord hγ q).2 : EuclideanHalfSpace 1).property])
    rw [polarPoint, polarPoint, ← hdepth] at hp
    exact mul_left_cancel₀ h1 hp
  have hcoord : collarCoord hγ q = collarCoord hγ q' := by
    rw [Prod.ext_iff, ← apply_angle_collarCoord hγ hinj q, ← apply_angle_collarCoord hγ hinj q',
      hangle]
    exact ⟨rfl, hdepth⟩
  apply Subtype.ext
  apply Subtype.val_injective
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
    ((gluingCoord γ i z).2 : EuclideanHalfSpace 1).val 0 = ‖(z : ℂ)‖ - 1 := by
  rw [coe_gluingCoord_snd, normalRay_coe_apply, max_eq_left (by linarith)]

/-- A point `z` of the ball with `1 < ‖z‖` is `(1 + t) · toCircle θ` for its collar coordinates:
the depth `t = ‖z‖ - 1` of `gluingCoord γ i z` and the angle `θ = arg z / 2π`. -/
theorem ofReal_one_add_mul_toCircle_gluingCoord {i : ι} {z : ball} (hz : 1 < ‖(z : ℂ)‖) :
    ((1 + ((gluingCoord γ i z).2 : EuclideanHalfSpace 1).val 0 : ℝ) : ℂ) *
      (toCircle ((arg z / (2 * π) : ℝ) : AddCircle (1 : ℝ)) : ℂ) = z := by
  rw [depth_gluingCoord hz, toCircle_apply_mk, Circle.coe_exp]
  conv_rhs => rw [← norm_mul_exp_arg_mul_I (z : ℂ)]
  congr 2
  · ring
  · field_simp

end

variable (c) in
/-- The point of `S` glued to a point `z` with `1 < ‖z‖` of a disc is an interior point. -/
theorem apply_gluingCoord_mem_interiorOpens {i : ι} {z : ball} (hz : 1 < ‖(z : ℂ)‖) :
    c (gluingCoord γ i z) ∈ (𝓡∂ 2).interiorOpens S := by
  rw [ModelWithCorners.mem_interiorOpens_iff_mem_interior, c.apply_mem_interior_iff_pos,
    depth_gluingCoord hz]
  linarith

/-- The point of the interior glued to a point `z` of the annulus of the `i`-th disc. -/
private def gluingPoint (i : ι) {z : ball} (hz : 1 < ‖(z : ℂ)‖) : interiorOverlap c γ hγ i :=
  ⟨⟨c (gluingCoord γ i z),
    ModelWithCorners.mem_interiorOpens_iff_mem_interior.1
      (apply_gluingCoord_mem_interiorOpens c hz)⟩, by
    rw [mem_interiorOverlap]
    exact ⟨_, _, rfl⟩⟩

private theorem val_gluingPoint (i : ι) {z : ball} (hz : 1 < ‖(z : ℂ)‖) :
    (gluingPoint (c := c) hγ i hz).val.val = c (gluingCoord γ i z) :=
  rfl

include hinj in
private theorem polarPoint_gluingPoint (i : ι) {z : ball} (hz : 1 < ‖(z : ℂ)‖) :
    polarPoint hγ (gluingPoint (c := c) hγ i hz) = z := by
  have hcoord : collarCoord hγ (gluingPoint (c := c) hγ i hz) = gluingCoord γ i z :=
    c.injective (by
      rw [apply_collarCoord, val_gluingPoint])
  rw [polarPoint, hcoord, gluingCoord_fst, angle_apply hinj]
  exact ofReal_one_add_mul_toCircle_gluingCoord hz

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
omit [IsManifold (𝓡∂ 2) ∞ S] in
/-- The interior and the discs overlap in distinct places for distinct discs. -/
private theorem eq_of_mem_interiorOverlap {i j : ι} {q : (𝓡∂ 2).interior S}
    (hi : q ∈ interiorOverlap c γ hγ i) (hj : q ∈ interiorOverlap c γ hγ j) : i = j := by
  obtain ⟨θ, t, hθ⟩ := (mem_interiorOverlap hγ).1 hi
  obtain ⟨θ', t', hθ'⟩ := (mem_interiorOverlap hγ).1 hj
  have h := c.injective (hθ.trans hθ'.symm)
  exact congrArg Prod.fst (hinj (a₁ := (i, θ)) (a₂ := (j, θ')) (congrArg Prod.fst h))

/-! ### The gluing data -/

variable (c γ) in
/-- The part of the interior piece covered by the collar over the image of some `γ i`. -/
private def interiorOverlaps : Opens ((𝓡∂ 2).interior S) :=
  ⨆ i, interiorOverlap c γ hγ i

omit [IsManifold (𝓡∂ 2) ∞ S] in
private theorem mem_interiorOverlaps {q : (𝓡∂ 2).interior S} :
    q ∈ interiorOverlaps c γ hγ ↔ ∃ i, q ∈ interiorOverlap c γ hγ i :=
  Opens.mem_iSup

omit [IsManifold (𝓡∂ 2) ∞ S] in
private theorem interiorOverlap_le_interiorOverlaps (i : ι) :
    interiorOverlap c γ hγ i ≤ interiorOverlaps c γ hγ :=
  le_iSup (interiorOverlap c γ hγ) i

variable (ι) in
/-- The disjoint union of the discs, one for each `i : ι`. -/
private abbrev DiscsPiece : Type := Σ _ : ι, DiscPiece

variable (ι) in
/-- The annuli of the discs, along which they are glued to the interior. -/
private def annuli : Opens (DiscsPiece ι) :=
  ⟨{z | z.2 ∈ annulus}, isOpen_sigma_iff.2 fun _ ↦ annulus.isOpen⟩

private theorem mem_annuli {z : DiscsPiece ι} : z ∈ annuli ι ↔ z.2 ∈ annulus :=
  Iff.rfl

/-- The index of a disc whose collar covers a point of `interiorOverlaps`. -/
private def overlapIndex (q : interiorOverlaps c γ hγ) : ι :=
  ((mem_interiorOverlaps hγ).1 q.property).choose

omit [IsManifold (𝓡∂ 2) ∞ S] in
private theorem mem_interiorOverlap_overlapIndex (q : interiorOverlaps c γ hγ) :
    q.val ∈ interiorOverlap c γ hγ (overlapIndex hγ q) :=
  ((mem_interiorOverlaps hγ).1 q.property).choose_spec

/-- The gluing map from the part of the interior covered by the collars over the `γ i` to the
annuli of the discs: `annulusDiffeomorph` on the part covered by the collar over `γ i`. -/
private def toAnnuli (q : interiorOverlaps c γ hγ) : annuli ι :=
  ⟨⟨overlapIndex hγ q,
      (annulusDiffeomorph hγ hinj (overlapIndex hγ q)
        ⟨q.val, mem_interiorOverlap_overlapIndex hγ q⟩).val⟩,
    (annulusDiffeomorph hγ hinj _ _).property⟩

private theorem toAnnuli_eq {q : interiorOverlaps c γ hγ} {i : ι}
    (hi : q.val ∈ interiorOverlap c γ hγ i) :
    toAnnuli hγ hinj q =
      ⟨⟨i, (annulusDiffeomorph hγ hinj i ⟨q.val, hi⟩).val⟩,
        (annulusDiffeomorph hγ hinj i ⟨q.val, hi⟩).property⟩ := by
  obtain rfl := eq_of_mem_interiorOverlap hγ hinj (mem_interiorOverlap_overlapIndex hγ q) hi
  rfl

private theorem injective_toAnnuli : Function.Injective (toAnnuli (c := c) hγ hinj) := by
  intro q q' h
  obtain ⟨i, hi⟩ := (mem_interiorOverlaps hγ).1 q.property
  obtain ⟨j, hj⟩ := (mem_interiorOverlaps hγ).1 q'.property
  have h' := congrArg Subtype.val h
  rw [toAnnuli_eq hγ hinj hi, toAnnuli_eq hγ hinj hj] at h'
  obtain ⟨rfl, hz⟩ := Sigma.mk.inj_iff.1 h'
  have hq := (annulusDiffeomorph hγ hinj i).injective (Subtype.ext (eq_of_heq hz))
  have hq' := congrArg Subtype.val hq
  exact Subtype.ext hq'

private theorem surjective_toAnnuli : Function.Surjective (toAnnuli (c := c) hγ hinj) := by
  rintro ⟨⟨i, z⟩, hz⟩
  let q := (annulusDiffeomorph (c := c) hγ hinj i).symm ⟨z, hz⟩
  refine ⟨Opens.inclusion (interiorOverlap_le_interiorOverlaps hγ i) q, ?_⟩
  rw [toAnnuli_eq hγ hinj (i := i) q.property]
  have hq : (annulusDiffeomorph hγ hinj i q : DiscPiece) = z :=
    congrArg Subtype.val ((annulusDiffeomorph hγ hinj i).apply_symm_apply _)
  exact Subtype.ext (Sigma.ext rfl (heq_of_eq hq))

private theorem isLocalDiffeomorph_toAnnuli :
    IsLocalDiffeomorph (𝓡 2) (𝓡 2) ∞ (toAnnuli (c := c) hγ hinj) := fun q ↦ by
  obtain ⟨i, hi⟩ := (mem_interiorOverlaps hγ).1 q.property
  let incl := Opens.inclusion (interiorOverlap_le_interiorOverlaps (c := c) hγ i)
  have h : toAnnuli hγ hinj ∘ incl = fun w ↦
      ⟨⟨i, (annulusDiffeomorph hγ hinj i w).val⟩, (annulusDiffeomorph hγ hinj i w).property⟩ :=
    funext fun w ↦ toAnnuli_eq hγ hinj w.property
  have hmk : IsLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞
      ((Subtype.val ∘ toAnnuli hγ hinj) ∘ incl) ⟨q.val, hi⟩ := by
    rw [Function.comp_assoc, h]
    exact ((annulusDiffeomorph hγ hinj i).isLocalDiffeomorph _).comp
      (hg := (isLocalDiffeomorph_subtype_val _).comp (hg := isLocalDiffeomorph_sigmaMk i _))
  exact isLocalDiffeomorphAt_subtypeVal_comp_iff.1
    (hmk.of_comp_right (isLocalDiffeomorph_inclusion _ _))

/-- The gluing map from the part of the interior covered by the collars over the `γ i` to the
annuli of the discs, as a diffeomorphism. -/
private def annuliDiffeomorph : interiorOverlaps c γ hγ ≃ₘ^∞⟮𝓡 2, 𝓡 2⟯ annuli ι :=
  (isLocalDiffeomorph_toAnnuli hγ hinj).diffeomorphOfBijective
    ⟨injective_toAnnuli hγ hinj, surjective_toAnnuli hγ hinj⟩

private theorem annuliDiffeomorph_apply (q : interiorOverlaps c γ hγ) :
    annuliDiffeomorph hγ hinj q = toAnnuli hγ hinj q :=
  congrFun (IsLocalDiffeomorph.coe_diffeomorphOfBijective _ _) q

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
  GluedAlong (capDiscs.annuliDiffeomorph (c := c) hγ hinj)

namespace capDiscs

/-- The topology of `capDiscs c γ hγ hinj`, that of the space glued along the diffeomorphism of
the collar parts of the interior onto the annuli. -/
@[instance_reducible]
def topologicalSpace : TopologicalSpace (capDiscs c γ hγ hinj) :=
  inferInstanceAs (TopologicalSpace (GluedAlong (annuliDiffeomorph (c := c) hγ hinj)))

instance : TopologicalSpace (capDiscs c γ hγ hinj) := topologicalSpace c γ hγ hinj

/-- The atlas of `capDiscs c γ hγ hinj`, that of the space glued along the diffeomorphism of the
collar parts of the interior onto the annuli. -/
@[instance_reducible]
def chartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 2)) (capDiscs c γ hγ hinj) :=
  inferInstanceAs (ChartedSpace _ (GluedAlong (annuliDiffeomorph (c := c) hγ hinj)))

instance : ChartedSpace (EuclideanSpace ℝ (Fin 2)) (capDiscs c γ hγ hinj) :=
  chartedSpace c γ hγ hinj

instance : IsManifold (𝓡 2) ∞ (capDiscs c γ hγ hinj) :=
  inferInstanceAs (IsManifold (𝓡 2) ∞ (GluedAlong (annuliDiffeomorph (c := c) hγ hinj)))

/-- The inclusion of the interior of `S` into the capped surface. -/
def inl (p : (𝓡∂ 2).interiorOpens S) : capDiscs c γ hγ hinj :=
  GluedAlong.inl (annuliDiffeomorph hγ hinj) ((𝓡∂ 2).interiorOpensDiffeomorph S ∞ p)

/-- The inclusion of the ball of radius `2` of `ℂ` into the capped surface as the `i`-th disc. -/
def inr (i : ι) (z : ball) : capDiscs c γ hγ hinj :=
  GluedAlong.inr (annuliDiffeomorph hγ hinj)
    (⟨i, remodelDiffeomorph complexDiffeomorph ball z⟩ : DiscsPiece ι)

/-- The inclusion of the interior of `S` is a smooth local diffeomorphism. -/
theorem isLocalDiffeomorph_inl : IsLocalDiffeomorph (𝓡∂ 2) (𝓡 2) ∞ (inl c γ hγ hinj) := fun p ↦
  (((𝓡∂ 2).interiorOpensDiffeomorph S ∞).isLocalDiffeomorph p).comp
    (hg := GluedAlong.isLocalDiffeomorph_inl (annuliDiffeomorph (c := c) hγ hinj) _)

/-- The inclusion of each disc is a smooth local diffeomorphism. -/
theorem isLocalDiffeomorph_inr (i : ι) :
    IsLocalDiffeomorph 𝓘(ℝ, ℂ) (𝓡 2) ∞ (inr c γ hγ hinj i) := fun z ↦
  (((remodelDiffeomorph complexDiffeomorph ball).isLocalDiffeomorph z).comp
    (hg := isLocalDiffeomorph_sigmaMk (M := fun _ : ι ↦ DiscPiece) i _)).comp
      (hg := GluedAlong.isLocalDiffeomorph_inr (annuliDiffeomorph (c := c) hγ hinj) _)

end capDiscs

/-- The interior of `S` is an open subset of the capped surface. -/
theorem isOpenEmbedding_capDiscs_inl : IsOpenEmbedding (capDiscs.inl c γ hγ hinj) :=
  (GluedAlong.isOpenEmbedding_inl (capDiscs.annuliDiffeomorph (c := c) hγ hinj)).comp
    ((𝓡∂ 2).interiorOpensDiffeomorph S ∞).toHomeomorph.isOpenEmbedding

/-- Each disc is an open subset of the capped surface. -/
theorem isOpenEmbedding_capDiscs_inr (i : ι) : IsOpenEmbedding (capDiscs.inr c γ hγ hinj i) :=
  (GluedAlong.isOpenEmbedding_inr (capDiscs.annuliDiffeomorph (c := c) hγ hinj)).comp
    (IsOpenEmbedding.sigmaMk.comp
      (remodelDiffeomorph capDiscs.complexDiffeomorph ball).toHomeomorph.isOpenEmbedding)

namespace capDiscs

/-- **The gluing formula.** A point `z` of the `i`-th disc with `1 < ‖z‖` is the point
`c (γ i (arg z / 2π), ‖z‖ - 1)` of the interior of `S`. -/
theorem inr_eq_inl {i : ι} {z : ball} (hz : 1 < ‖(z : ℂ)‖) :
    inr c γ hγ hinj i z =
      inl c γ hγ hinj ⟨c (gluingCoord γ i z), apply_gluingCoord_mem_interiorOpens c hz⟩ := by
  let q := Opens.inclusion (interiorOverlap_le_interiorOverlaps hγ i)
    (gluingPoint (c := c) hγ i hz)
  have h := congrArg Subtype.val (toAnnulus_gluingPoint (c := c) hγ hinj i hz)
  rw [← coe_annulusDiffeomorph hγ hinj] at h
  have hq : (annuliDiffeomorph hγ hinj q : DiscsPiece ι) =
      ⟨i, remodelDiffeomorph complexDiffeomorph ball z⟩ := by
    rw [annuliDiffeomorph_apply, toAnnuli_eq hγ hinj (gluingPoint (c := c) hγ i hz).property]
    exact Sigma.ext rfl (heq_of_eq h)
  rw [inr, inl, ← hq, GluedAlong.inr_apply]
  congr 1
  apply Subtype.val_injective
  rw [Set.coe_inclusion (SetLike.coe_subset_coe.2 (interiorOverlap_le_interiorOverlaps hγ i)),
    val_gluingPoint, ModelWithCorners.coe_interiorOpensDiffeomorph_apply]

/-- A collar point `c (γ i θ, t)` of the interior of `S` is the point `(1 + t) · toCircle θ` of
the `i`-th disc. -/
theorem inr_ofReal_mul_toCircle_eq_inl {i : ι} {θ : AddCircle (1 : ℝ)} {t : normalIioOpens 1}
    (h : c (γ i θ, t) ∈ (𝓡∂ 2).interiorOpens S) :
    inr c γ hγ hinj i ⟨_, ofReal_one_add_mul_toCircle_mem_ball t θ⟩ =
      inl c γ hγ hinj ⟨c (γ i θ, t), h⟩ := by
  let q : interiorOverlap c γ hγ i :=
    ⟨(𝓡∂ 2).interiorOpensDiffeomorph S ∞ ⟨c (γ i θ, t), h⟩,
      (mem_interiorOverlap hγ).2 ⟨θ, t, by
        rw [ModelWithCorners.coe_interiorOpensDiffeomorph_apply]⟩⟩
  have hq : collarCoord hγ q = (γ i θ, t) :=
    collarCoord_eq hγ (by
      simp only [q, ModelWithCorners.coe_interiorOpensDiffeomorph_apply])
  have hz : toBall hγ q = ⟨_, ofReal_one_add_mul_toCircle_mem_ball t θ⟩ :=
    Subtype.ext (by rw [coe_toBall, polarPoint, hq, angle_apply hinj])
  refine ((GluedAlong.inl_eq_inr_iff _).2
    ⟨interiorOverlap_le_interiorOverlaps hγ i q.property, ?_⟩).symm
  rw [annuliDiffeomorph_apply, toAnnuli_eq hγ hinj q.property]
  have h' : (annulusDiffeomorph hγ hinj i q : DiscPiece) =
      remodelDiffeomorph complexDiffeomorph ball ⟨_, ofReal_one_add_mul_toCircle_mem_ball t θ⟩ := by
    rw [coe_annulusDiffeomorph, val_toAnnulus, hz]
  exact Sigma.ext rfl (heq_of_eq h')

/-- The interior of `S` and the discs cover the capped surface. -/
theorem range_inl_union_iUnion_range_inr :
    range (inl c γ hγ hinj) ∪ ⋃ i, range (inr c γ hγ hinj i) = univ := by
  refine eq_univ_of_forall fun x ↦ ?_
  obtain ⟨y, rfl⟩ | ⟨⟨i, w⟩, rfl⟩ :=
    GluedAlong.exists_inl_or_exists_inr (annuliDiffeomorph (c := c) hγ hinj) x
  · refine Or.inl ⟨((𝓡∂ 2).interiorOpensDiffeomorph S ∞).symm y, ?_⟩
    rw [inl, Diffeomorph.apply_symm_apply]
  · refine Or.inr (mem_iUnion.2 ⟨i, (remodelDiffeomorph complexDiffeomorph ball).symm w, ?_⟩)
    rw [inr, Diffeomorph.apply_symm_apply]

/-- Every point of the capped surface comes from the interior of `S` or from one of the discs. -/
theorem exists_inl_or_exists_inr (x : capDiscs c γ hγ hinj) :
    (∃ y, inl c γ hγ hinj y = x) ∨ ∃ i z, inr c γ hγ hinj i z = x := by
  simpa only [mem_union, mem_range, mem_iUnion] using
    (range_inl_union_iUnion_range_inr c γ hγ hinj).ge (mem_univ x)

/-- Distinct discs are disjoint in the capped surface. -/
theorem disjoint_range_inr {i j : ι} (hij : i ≠ j) :
    Disjoint (range (inr c γ hγ hinj i)) (range (inr c γ hγ hinj j)) := by
  refine Set.disjoint_iff.2 ?_
  rintro _ ⟨⟨a, rfl⟩, ⟨b, hb⟩⟩
  exact hij (congrArg Sigma.fst (GluedAlong.inr_injective _ hb)).symm

/-- A point `z` of a disc lies in the interior of `S` exactly when `1 < ‖z‖`. -/
theorem inr_mem_range_inl_iff {i : ι} {z : ball} :
    inr c γ hγ hinj i z ∈ range (inl c γ hγ hinj) ↔ 1 < ‖(z : ℂ)‖ := by
  refine ⟨fun ⟨p, hp⟩ ↦ ?_, fun hz ↦ ⟨_, (inr_eq_inl c γ hγ hinj hz).symm⟩⟩
  obtain ⟨hx, he⟩ := (GluedAlong.inl_eq_inr_iff _).1 hp
  have h : (⟨i, remodelDiffeomorph complexDiffeomorph ball z⟩ : DiscsPiece ι) ∈ annuli ι :=
    he ▸ (annuliDiffeomorph hγ hinj ⟨_, hx⟩).property
  rwa [mem_annuli, mem_annulus, DiscPiece.val_remodelDiffeomorph] at h

/-! ### The Hausdorff property -/

section T2

variable [T2Space S]

/-- An interior point `p` of `S` has a neighbourhood that the `i`-th disc meets only in a thin
annulus `1 < ‖z‖`, at distance `ε` from the boundary circle `‖z‖ = 1`. -/
private theorem exists_nhds_inr_ne_inl (i : ι) (p : (𝓡∂ 2).interiorOpens S) :
    ∃ ε > 0, ∃ V ∈ 𝓝 p, ∀ q ∈ V, ∀ z : ball, ‖(z : ℂ)‖ < 1 + ε →
      inr c γ hγ hinj i z ≠ inl c γ hγ hinj q := by
  -- Separate `p` from the compact boundary circle `γ i` by `A ∋ p` and an open `B ⊇ γ i`.
  have hC : IsCompact (range fun θ ↦ (γ i θ : S)) :=
    isCompact_range (continuous_subtypeVal.comp (hγ i).isLocalHomeomorph.continuous)
  have hp : (p : S) ∉ range fun θ ↦ (γ i θ : S) := by
    rintro ⟨θ, hθ⟩
    have hb : (p : S) ∈ (𝓡∂ 2).boundary S := hθ ▸ (γ i θ).property
    exact disjoint_left.1 ModelWithCorners.disjoint_interior_boundary
      (ModelWithCorners.mem_interiorOpens_iff_mem_interior.1 p.property) hb
  obtain ⟨B, hB, A, hA, hAB⟩ := Filter.disjoint_iff.1 (hC.disjoint_nhdsSet_nhds hp)
  obtain ⟨B', hB'o, hCB', hB'B⟩ := mem_nhdsSet_iff_exists.1 hB
  -- The collar coordinates `(γ i θ, t)` whose collar point lies in `B'`, read in `∂S × [0, ∞)`.
  let V : Set (↥((𝓡∂ 2).boundary S) × EuclideanHalfSpace 1) :=
    Prod.map id Subtype.val '' (c ⁻¹' B')
  have hV : IsOpen V :=
    (IsOpenEmbedding.id.prodMap (normalIioOpens 1).isOpen.isOpenEmbedding_subtypeVal).isOpenMap _
      (hB'o.preimage c.continuous)
  let F : ℝ × AddCircle (1 : ℝ) → ↥((𝓡∂ 2).boundary S) × EuclideanHalfSpace 1 :=
    fun x ↦ (γ i x.2, normalRay x.1)
  have hF : Continuous F :=
    ((hγ i).isLocalHomeomorph.continuous.comp continuous_snd).prodMk
      (continuous_normalRay.comp continuous_fst)
  obtain ⟨ε, hε, hεV⟩ := isCompact_univ.exists_pos_forall_norm_lt
    (Q := fun (r : ℝ) θ ↦ F (r, θ) ∈ V) fun θ _ ↦ by
      refine hF.continuousAt.preimage_mem_nhds (hV.mem_nhds ⟨(γ i θ, normalIioOpensZero one_pos),
        ?_, ?_⟩)
      · rw [mem_preimage, c.apply_zero]
        exact hCB' ⟨θ, rfl⟩
      · simp [F, normalRay_zero]
  refine ⟨ε, hε, Subtype.val ⁻¹' A, continuous_subtypeVal.continuousAt.preimage_mem_nhds hA,
    fun q hq z hzε hzq ↦ ?_⟩
  have hz : 1 < ‖(z : ℂ)‖ := (inr_mem_range_inl_iff c γ hγ hinj).1 ⟨q, hzq.symm⟩
  rw [inr_eq_inl c γ hγ hinj hz] at hzq
  obtain rfl := (isOpenEmbedding_capDiscs_inl c γ hγ hinj).injective hzq
  obtain ⟨w, hw, hwF⟩ := hεV (x := ‖(z : ℂ)‖ - 1)
    (by rw [Real.norm_eq_abs, abs_of_pos (by linarith)]; linarith)
    ((arg z / (2 * π) : ℝ) : AddCircle (1 : ℝ)) (mem_univ _)
  have hw' : w = gluingCoord γ i z :=
    Prod.ext ((congrArg Prod.fst hwF).trans (gluingCoord_fst i z).symm)
      (Subtype.ext ((congrArg Prod.snd hwF).trans (coe_gluingCoord_snd i z).symm))
  exact disjoint_left.1 hAB (hB'B (hw' ▸ hw)) hq

/-- The capped surface is Hausdorff when `S` is. -/
instance instT2Space : T2Space (capDiscs c γ hγ hinj) := by
  -- The criterion for a space glued from two pieces: the interior of `S` and the discs are
  -- Hausdorff, and it remains to separate a point of the interior from a point `w` of the
  -- `i`-th disc with `‖w‖ ≤ 1`.
  refine (GluedAlong.t2Space_iff _).2
    ⟨inferInstance, inferInstance, ?_⟩
  rintro x - ⟨i, w⟩ hw
  let φ := (𝓡∂ 2).interiorOpensDiffeomorph S ∞
  obtain ⟨ε, hε, V, hV, hsep⟩ := exists_nhds_inr_ne_inl c γ hγ hinj i (φ.symm x)
  let ψ := remodelDiffeomorph complexDiffeomorph ball
  have hW : IsOpen {w : DiscPiece | ‖(ψ.symm w : ℂ)‖ < 1 + ε} :=
    isOpen_lt (continuous_subtypeVal.comp ψ.symm.continuous).norm continuous_const
  refine ⟨φ.symm ⁻¹' V, φ.symm.continuous.continuousAt.preimage_mem_nhds hV,
    Sigma.mk i '' {w : DiscPiece | ‖(ψ.symm w : ℂ)‖ < 1 + ε},
    (isOpenMap_sigmaMk _ hW).mem_nhds ⟨w, ?_, rfl⟩, ?_⟩
  · rw [mem_annuli, mem_annulus, DiscPiece.val, not_lt] at hw
    exact hw.trans_lt (lt_add_of_pos_right _ hε)
  rintro q hq ⟨w', hw', he⟩
  refine hsep _ hq (ψ.symm w') hw' ?_
  rw [inr, inl, Diffeomorph.apply_symm_apply, φ.apply_symm_apply, he]
  exact GluedAlong.inr_apply _ q

end T2

end capDiscs

end SymplecticGeometry
