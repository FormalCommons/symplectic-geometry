/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.Glue
public import TauCeti.Geometry.Manifold.Boundary.InducedOrientation
public import TauCeti.Geometry.Manifold.Orientation.AddCircle
public import TauCeti.Geometry.Manifold.Orientation.OpenSubset
public import SymplecticGeometry.Geometry.Manifold.Gluing.CapDiscs.Basic
public import SymplecticGeometry.Geometry.Manifold.Boundary.Charts
import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.CoordinateDisc
import SymplecticGeometry.Geometry.Manifold.Gluing.CapDiscs.Topology
import SymplecticGeometry.Geometry.Manifold.Orientation.Glue
import SymplecticGeometry.Geometry.Manifold.Boundary.Collar.Orientation
import SymplecticGeometry.Geometry.Manifold.Orientation.AddCircle
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.Injective
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
import SymplecticGeometry.Geometry.Manifold.Boundary.Collar.Interior
import SymplecticGeometry.Geometry.Manifold.Boundary.Interior

/-!
# The orientation of a surface capped with discs

Let `S` be a surface with boundary, oriented by `o`, with a smooth collar `c` of its boundary, and
let `γ i : AddCircle 1 → ∂S` be the loops along which `SymplecticGeometry.capDiscs c γ hγ hinj`
caps the boundary circles of `S` with discs (`Gluing/CapDiscs/Basic.lean`). Suppose that every
`γ i` reverses orientation, from Tau Ceti's positive orientation `AddCircle.orientation 1` of the
circle to the boundary orientation `TauCeti.boundaryOrientation o` (outward vector first). Then the
capped surface has exactly one orientation, `SymplecticGeometry.capDiscs.orientation`, for which
the inclusion `inl` of the interior of `S` preserves orientation from `o` and every inclusion
`inr i` of the ball of radius `2` of `ℂ` preserves orientation from the standard orientation
`Complex.orientation` of `ℂ`.

The orientation is glued from the pieces by `TauCeti.Manifold.Orientation.iGlue`, and the pieces
agree on each annulus `1 < ‖z‖ < 2`. Parametrize it by `(θ, t)`, `t > 0`, in
`AddCircle 1 × [0, 1)`, with the product of the two standard orientations. The point `(θ, t)` is
`c (γ i θ, t)` in the interior and `(1 + t) · toCircle θ` in the disc
(`SymplecticGeometry.capDiscs.inr_ofReal_mul_toCircle_eq_inl`). Polar coordinates reverse
orientation (`AddCircle.isOrientationReversingAt_ofReal_mul_toCircle`). The map
`(θ, t) ↦ (γ i θ, t)` reverses it, by the hypothesis on `γ i`, and on a surface the collar
preserves it (`TauCeti.SmoothCollar.isOrientationPreservingAt_of_odd`). So both parametrizations
reverse orientation, and the two pieces carry their orientations to the same orientation of the
capped surface (`TauCeti.Manifold.Orientation.map_orientationAt_eq_of_comp_eventuallyEq`).
Geometrically, the outward direction of `S` points to the centre of the disc, which is why the
loops must run against the boundary orientation of `S`.

With this orientation, the `i`-th cap is a coordinate disc,
`SymplecticGeometry.capDiscs.coordinateDisc`, whose map is `inr i`. It comes from the chart
`(inr i)⁻¹` of the capped surface read in `ℝ²` (`SymplecticGeometry.CoordinateDisc.ofChart`),
which preserves orientation because `inr i` does
(`TauCeti.Manifold.Orientation.IsOrientationPreservingAt.partialDiffeomorph_symm`).

## Main definitions

* `SymplecticGeometry.capDiscs.orientation`: the orientation of the capped surface.
* `SymplecticGeometry.capDiscs.coordinateDisc`: the `i`-th cap, as a coordinate disc.

## Main results

* `SymplecticGeometry.capDiscs.isOrientationPreservingAt_inl`,
  `SymplecticGeometry.capDiscs.isOrientationPreservingAt_inr`: the inclusions of the interior of
  `S` and of the discs preserve orientation.
* `SymplecticGeometry.capDiscs.eq_orientation_iff`: these properties characterize the
  orientation.
* `SymplecticGeometry.capDiscs.coe_coordinateDisc`: the map of the `i`-th coordinate disc is
  `inr i`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §2.7 (the first Chern number of bundles over surfaces).
* M. W. Hirsch, *Differential Topology*, Springer GTM 33, 1976, Chapter 8, §2 (gluing manifolds
  along boundaries by collars).
* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Springer GTM 218, 2013,
  Chapter 15 (orientations, the induced orientation on the boundary, and gluing).
-/

public section

open Set Function Topology Manifold TopologicalSpace Complex
open scoped Manifold ContDiff Real

noncomputable section

namespace SymplecticGeometry

open TauCeti TauCeti.EuclideanHalfSpace SymplecticGeometry.EuclideanHalfSpace
  TauCeti.Manifold.Orientation CoordinateDisc AddCircle

variable {S : Type} [TopologicalSpace S] [ChartedSpace (EuclideanHalfSpace 2) S]
  [IsManifold (𝓡∂ 2) ∞ S]

namespace capDiscs

variable (c : SmoothCollar 1 ∞ S) {ι : Type} (γ : ι → AddCircle (1 : ℝ) → (𝓡∂ 2).boundary S)
  (hγ : ∀ i, IsLocalDiffeomorph 𝓘(ℝ) (𝓡 1) ∞ (γ i))
  (hinj : Function.Injective fun p : ι × AddCircle (1 : ℝ) ↦ γ p.1 p.2)
  (o : Manifold.Orientation (𝓡∂ 2) S (Fin 2))

/-! ### The pieces, modelled on `ℝ²` -/

/-- The ball of radius `2` of `ℝ²`, the image of the ball of `ℂ` under `z ↦ (re z, im z)`. -/
private def discOpens : Opens (EuclideanSpace ℝ (Fin 2)) :=
  ⟨Metric.ball 0 2, Metric.isOpen_ball⟩

private theorem mem_discOpens {v : EuclideanSpace ℝ (Fin 2)} : v ∈ discOpens ↔ ‖v‖ < 2 :=
  mem_ball_zero_iff

private instance : Nonempty discOpens :=
  ⟨⟨0, mem_discOpens.2 (by simp)⟩⟩

/-- The identification `z ↦ (re z, im z)` of the ball of `ℂ` with the ball of radius `2` of
`ℝ²`, the restriction of `orthonormalBasisOneI.repr` as a diffeomorphism. -/
private def ballDiffeomorph : ball ≃ₘ^∞⟮𝓘(ℝ, ℂ), 𝓡 2⟯ discOpens :=
  orthonormalBasisOneI.repr.toContinuousLinearEquiv.toDiffeomorph.subtype fun z ↦ by
    simp [mem_ball_iff, mem_discOpens]

private theorem coe_ballDiffeomorph (z : ball) :
    (ballDiffeomorph z : EuclideanSpace ℝ (Fin 2)) = orthonormalBasisOneI.repr z := by
  simp [ballDiffeomorph]

variable (S ι) in
/-- The pieces of the capped surface: the interior of `S`, and one disc for each `i : ι`. -/
private def piece : Option ι → Type
  | none => (𝓡∂ 2).interior S
  | some _ => discOpens

private instance instTopologicalSpacePiece : ∀ k : Option ι, TopologicalSpace (piece S ι k)
  | none => inferInstanceAs (TopologicalSpace ((𝓡∂ 2).interior S))
  | some _ => inferInstanceAs (TopologicalSpace discOpens)

private instance instChartedSpacePiece :
    ∀ k : Option ι, ChartedSpace (EuclideanSpace ℝ (Fin 2)) (piece S ι k)
  | none => inferInstanceAs (ChartedSpace _ ((𝓡∂ 2).interior S))
  | some _ => inferInstanceAs (ChartedSpace _ discOpens)

private instance instIsManifoldPiece : ∀ k : Option ι, IsManifold (𝓡 2) ∞ (piece S ι k)
  | none => inferInstanceAs (IsManifold _ ∞ ((𝓡∂ 2).interior S))
  | some _ => inferInstanceAs (IsManifold _ ∞ discOpens)

/-- The maps of the pieces into the capped surface. -/
private def pieceMap : ∀ k : Option ι, piece S ι k → capDiscs c γ hγ hinj
  | none => fun x ↦ inl c γ hγ hinj (((𝓡∂ 2).interiorOpensDiffeomorph S ∞).symm x)
  | some i => fun v ↦ inr c γ hγ hinj i (ballDiffeomorph.symm v)

private theorem isLocalDiffeomorph_inr_ballDiffeomorph_symm (i : ι) :
    IsLocalDiffeomorph (𝓡 2) (𝓡 2) ∞
      fun v : discOpens ↦ inr c γ hγ hinj i (ballDiffeomorph.symm v) :=
  fun v ↦ (ballDiffeomorph.symm.isLocalDiffeomorph v).comp
    (hg := isLocalDiffeomorph_inr c γ hγ hinj i _)

private theorem injective_inr_ballDiffeomorph_symm (i : ι) :
    Injective fun v : discOpens ↦ inr c γ hγ hinj i (ballDiffeomorph.symm v) :=
  (isOpenEmbedding_capDiscs_inr c γ hγ hinj i).injective.comp ballDiffeomorph.symm.injective

private theorem isLocalDiffeomorph_pieceMap :
    ∀ k : Option ι, IsLocalDiffeomorph (𝓡 2) (𝓡 2) ∞ (pieceMap c γ hγ hinj k)
  | none => fun x ↦ (((𝓡∂ 2).interiorOpensDiffeomorph S ∞).symm.isLocalDiffeomorph x).comp
      (hg := isLocalDiffeomorph_inl c γ hγ hinj _)
  | some i => isLocalDiffeomorph_inr_ballDiffeomorph_symm c γ hγ hinj i

private theorem iUnion_range_pieceMap : ⋃ k, range (pieceMap c γ hγ hinj k) = univ := by
  refine eq_univ_of_forall fun p ↦ ?_
  rcases exists_inl_or_exists_inr c γ hγ hinj p with ⟨q, rfl⟩ | ⟨i, z, rfl⟩
  · exact mem_iUnion.2 ⟨none, ((𝓡∂ 2).interiorOpensDiffeomorph S ∞) q, by simp [pieceMap]⟩
  · exact mem_iUnion.2 ⟨some i, ballDiffeomorph z, by simp [pieceMap]⟩

/-- The standard orientation of `ℝ²` on the ball of radius `2`. -/
private def discOrientation : Manifold.Orientation (𝓡 2) discOpens (Fin 2) :=
  (Manifold.Orientation.euclideanSpace 2).restrict discOpens

/-- The orientations of the pieces: `o` on the interior, and the standard orientation of `ℝ²` on
the discs. -/
private def pieceOrientation : ∀ k : Option ι, Manifold.Orientation (𝓡 2) (piece S ι k) (Fin 2)
  | none => (o.restrict ((𝓡∂ 2).interiorOpens S)).toInterior
  | some _ => discOrientation

/-- The coordinates `z ↦ (re z, im z)` of the ball of `ℂ` preserve orientation. -/
private theorem isOrientationPreservingAt_ballDiffeomorph (z : ball) :
    IsOrientationPreservingAt
      (Manifold.Orientation.complex.restrict ball)
      discOrientation ballDiffeomorph z := by
  have he : Subtype.val ∘ ballDiffeomorph = orthonormalBasisOneI.repr ∘ (Subtype.val : ball → ℂ) :=
    funext coe_ballDiffeomorph
  rw [discOrientation, isOrientationPreservingAt_restrict_iff_of_comp_eq he]
  exact Complex.isOrientationPreservingAt_orthonormalBasisOneI_repr _

/-- The inverse of the coordinates preserves orientation. -/
private theorem isOrientationPreservingAt_ballDiffeomorph_symm (v : discOpens) :
    IsOrientationPreservingAt discOrientation
      (Manifold.Orientation.complex.restrict ball)
      ballDiffeomorph.symm v :=
  (isOrientationPreservingAt_ballDiffeomorph _).diffeomorph_symm (by simp)

/-! ### The annuli -/

/-- The parameters `(θ, t)`, `t > 0`, of the annuli. -/
private def annulusParam : Opens (AddCircle (1 : ℝ) × normalIioOpens 1) :=
  ⟨{u | 0 < (u.2 : EuclideanHalfSpace 1).val 0}, isOpen_lt continuous_const (by fun_prop)⟩

private theorem mem_annulusParam {u : AddCircle (1 : ℝ) × normalIioOpens 1} :
    u ∈ annulusParam ↔ 0 < (u.2 : EuclideanHalfSpace 1).val 0 :=
  Iff.rfl

/-- The orientation of the parameters: the product of the standard orientations of the circle
and of `[0, 1)`. -/
private def annulusOrientation : Manifold.Orientation (𝓘(ℝ).prod (𝓡∂ 1)) annulusParam (Fin 2) :=
  ((AddCircle.orientation 1).prod (normalIioOpensOrientation 1)).restrict annulusParam

variable {c γ} in
/-- The point `c (γ i θ, t)` of the interior of `S`. -/
private def collarPoint (i : ι) (u : annulusParam) : (𝓡∂ 2).interiorOpens S :=
  ⟨c (γ i u.val.1, u.val.2), by
    rw [← SetLike.mem_coe, ModelWithCorners.coe_interiorOpens, c.apply_mem_interior_iff_pos]
    exact mem_annulusParam.1 u.property⟩

private theorem val_comp_collarPoint (i : ι) :
    Subtype.val ∘ collarPoint (c := c) (γ := γ) i =
      (c ∘ Prod.map (γ i) id) ∘ (Subtype.val : annulusParam → _) :=
  (rfl)

/-- The point `(1 + t) · toCircle θ` of the ball of `ℂ`. -/
private def polarPoint (u : annulusParam) : ball :=
  ⟨_, ofReal_one_add_mul_toCircle_mem_ball u.val.2 u.val.1⟩

private theorem val_comp_polarPoint :
    Subtype.val ∘ polarPoint =
      ((fun q : AddCircle (1 : ℝ) × ℝ ↦ (q.2 : ℂ) * (toCircle q.1 : ℂ)) ∘
        Prod.map id (fun s : normalIioOpens 1 ↦ 1 + (s : EuclideanHalfSpace 1).val 0)) ∘
        (Subtype.val : annulusParam → _) :=
  (rfl)

include hγ hinj in
/-- The two parametrizations of the `i`-th annulus give the same point of the capped surface. -/
private theorem inl_collarPoint (i : ι) (u : annulusParam) :
    inl c γ hγ hinj (collarPoint (c := c) (γ := γ) i u) = inr c γ hγ hinj i (polarPoint u) :=
  (inr_ofReal_mul_toCircle_eq_inl c γ hγ hinj _).symm

variable {o}
  (hrev : ∀ i θ, IsOrientationReversingAt (AddCircle.orientation 1) (boundaryOrientation o) (γ i) θ)

include hrev in
/-- In the parameters, the collar parametrization reverses orientation: `θ ↦ γ i θ` reverses it,
and on a surface the collar preserves it. -/
private theorem isOrientationPreservingAt_collarPoint (i : ι) (u : annulusParam) :
    IsOrientationPreservingAt (-annulusOrientation) (o.restrict ((𝓡∂ 2).interiorOpens S))
      (collarPoint (c := c) (γ := γ) i) u := by
  have hprod : IsOrientationPreservingAt
      ((AddCircle.orientation 1).prod (normalIioOpensOrientation 1))
      (-((boundaryOrientation o).prod (normalIioOpensOrientation 1))) (Prod.map (γ i) id)
      u.val := by
    rw [← prod_neg_left]
    exact ((isOrientationPreservingAt_neg_right _ _ _ _).2 (hrev i u.val.1)).prodMap
      (isOrientationPreservingAt_id _ u.val.2)
  have hc : IsOrientationPreservingAt
      (-((boundaryOrientation o).prod (normalIioOpensOrientation 1)))
      (-o) c (Prod.map (γ i) id u.val) := by
    simpa using c.isOrientationPreservingAt_of_odd o (by simp) odd_one _
  rw [annulusOrientation, ← restrict_neg,
    isOrientationPreservingAt_restrict_iff_of_comp_eq (val_comp_collarPoint (c := c) (γ := γ) i),
    ← isOrientationReversingAt_neg_right, isOrientationReversingAt_neg_left]
  exact hc.comp hprod

/-- In the parameters, the polar parametrization reverses orientation. -/
private theorem isOrientationPreservingAt_polarPoint (u : annulusParam) :
    IsOrientationPreservingAt (-annulusOrientation)
      (Manifold.Orientation.complex.restrict ball)
      polarPoint u := by
  have hd (s : normalIioOpens 1) : IsOrientationPreservingAt (normalIioOpensOrientation 1)
      real (fun s : normalIioOpens 1 ↦ 1 + (s : EuclideanHalfSpace 1).val 0) s := by
    have he : (fun s : normalIioOpens 1 ↦ 1 + (s : EuclideanHalfSpace 1).val 0) =
        (· + 1) ∘ fun s : normalIioOpens 1 ↦ (s : EuclideanHalfSpace 1).val 0 :=
      funext fun _ ↦ add_comm _ _
    rw [he]
    exact (isOrientationPreservingAt_add_const 1 _).comp
      (isOrientationPreservingAt_normalIioOpens_val_zero s)
  have hpol : IsOrientationReversingAt ((AddCircle.orientation 1).prod real)
      Manifold.Orientation.complex
      (fun q : AddCircle (1 : ℝ) × ℝ ↦ (q.2 : ℂ) * (toCircle q.1 : ℂ))
      (Prod.map id (fun s : normalIioOpens 1 ↦ 1 + (s : EuclideanHalfSpace 1).val 0) u.val) :=
    AddCircle.isOrientationReversingAt_ofReal_mul_toCircle _
      (by have := (u.val.2 : EuclideanHalfSpace 1).property; linarith)
  rw [annulusOrientation, ← restrict_neg,
    isOrientationPreservingAt_restrict_iff_of_comp_eq val_comp_polarPoint,
    isOrientationPreservingAt_neg_left]
  exact hpol.comp_preserving ((isOrientationPreservingAt_id _ u.val.1).prodMap (hd _))

include hrev in
/-- On the annuli, the interior piece and the `i`-th disc carry their orientations to the same
orientation of the capped surface. -/
private theorem map_orientationAt_eq (i : ι) {x : piece S ι none} {y : piece S ι (some i)}
    (u : annulusParam)
    (hx : (𝓡∂ 2).interiorOpensDiffeomorph S ∞ (collarPoint (c := c) (γ := γ) i u) = x)
    (hy : ballDiffeomorph (polarPoint u) = y) :
    _root_.Orientation.map (Fin 2)
        ((isLocalDiffeomorph_pieceMap c γ hγ hinj none x).mfderivToContinuousLinearEquiv
          (NeZero.ne _)).toLinearEquiv ((pieceOrientation o none).orientationAt x) =
      _root_.Orientation.map (Fin 2)
        ((isLocalDiffeomorph_pieceMap c γ hγ hinj (some i) y).mfderivToContinuousLinearEquiv
          (NeZero.ne _)).toLinearEquiv ((pieceOrientation o (some i)).orientationAt y) := by
  subst hx hy
  have hρ := (isOrientationPreservingAt_interiorOpensDiffeomorph _ ∞ _).comp
    (isOrientationPreservingAt_collarPoint c γ hrev i u)
  have hρ' := (isOrientationPreservingAt_ballDiffeomorph _).comp
    (isOrientationPreservingAt_polarPoint u)
  refine map_orientationAt_eq_of_comp_eventuallyEq (isLocalDiffeomorph_pieceMap c γ hγ hinj none)
    (isLocalDiffeomorph_pieceMap c γ hγ hinj (some i)) (o₁ := pieceOrientation o none)
    (o₂ := pieceOrientation o (some i))
    (ρ₁ := fun u ↦
      ((𝓡∂ 2).interiorOpensDiffeomorph S ∞ (collarPoint (c := c) (γ := γ) i u) : piece S ι none))
    (ρ₂ := fun u ↦ (ballDiffeomorph (polarPoint u) : piece S ι (some i))) hρ hρ'
    (mdifferentiableAt_of_isInvertible_mfderiv hρ.isInvertible_mfderiv)
    (mdifferentiableAt_of_isInvertible_mfderiv hρ'.isInvertible_mfderiv)
    (Filter.Eventually.of_forall fun u ↦ ?_)
  -- On the two pieces, `pieceMap` is `inl ∘ ((𝓡∂ 2).interiorOpensDiffeomorph S ∞).symm` and
  -- `inr i ∘ ballDiffeomorph.symm`.
  exact (congrArg (inl c γ hγ hinj) (((𝓡∂ 2).interiorOpensDiffeomorph S ∞).symm_apply_apply _)
    ).trans
    ((inl_collarPoint c γ hγ hinj i u).trans
      (congrArg (inr c γ hγ hinj i) (ballDiffeomorph.symm_apply_apply _)).symm)

include hγ hinj in
/-- A point where the interior piece meets the `i`-th disc is given by parameters of the annulus. -/
private theorem exists_annulusParam (i : ι) {x : piece S ι none} {y : piece S ι (some i)}
    (h : pieceMap c γ hγ hinj none x = pieceMap c γ hγ hinj (some i) y) :
    ∃ u : annulusParam,
      (𝓡∂ 2).interiorOpensDiffeomorph S ∞ (collarPoint (c := c) (γ := γ) i u) = x ∧
      ballDiffeomorph (polarPoint u) = y := by
  set z := ballDiffeomorph.symm y with hzy
  have h' : inl c γ hγ hinj (((𝓡∂ 2).interiorOpensDiffeomorph S ∞).symm x) =
    inr c γ hγ hinj i z := h
  have hz : 1 < ‖(z : ℂ)‖ := (inr_mem_range_inl_iff c γ hγ hinj).1 ⟨_, h'⟩
  let u : annulusParam := ⟨(((arg z / (2 * π) : ℝ) : AddCircle (1 : ℝ)), (gluingCoord γ i z).2), by
    rw [mem_annulusParam, coe_gluingCoord_snd, normalRay_coe_apply]
    exact lt_max_of_lt_left (by linarith)⟩
  have hP : polarPoint u = z :=
    Subtype.ext (ofReal_one_add_mul_toCircle_gluingCoord (γ := γ) (i := i) hz)
  have hy : ballDiffeomorph (polarPoint u) = y := by
    rw [hP, hzy]
    exact ballDiffeomorph.apply_symm_apply y
  refine ⟨u, ?_, hy⟩
  have hc : collarPoint (c := c) (γ := γ) i u = ((𝓡∂ 2).interiorOpensDiffeomorph S ∞).symm x := by
    refine (isOpenEmbedding_capDiscs_inl c γ hγ hinj).injective ?_
    rw [inl_collarPoint c γ hγ hinj, hP, h']
  rw [hc]
  exact ((𝓡∂ 2).interiorOpensDiffeomorph S ∞).apply_symm_apply x

include hrev in
/-- The pieces carry their orientations to the same orientation wherever they meet. -/
private theorem map_orientationAt_pieceMap (k l : Option ι) (x : piece S ι k) (y : piece S ι l)
    (h : pieceMap c γ hγ hinj k x = pieceMap c γ hγ hinj l y) :
    _root_.Orientation.map (Fin 2)
        ((isLocalDiffeomorph_pieceMap c γ hγ hinj k x).mfderivToContinuousLinearEquiv
          (NeZero.ne _)).toLinearEquiv ((pieceOrientation o k).orientationAt x) =
      _root_.Orientation.map (Fin 2)
        ((isLocalDiffeomorph_pieceMap c γ hγ hinj l y).mfderivToContinuousLinearEquiv
          (NeZero.ne _)).toLinearEquiv ((pieceOrientation o l).orientationAt y) := by
  rcases k with _ | i <;> rcases l with _ | j
  · obtain rfl : x = y := ((𝓡∂ 2).interiorOpensDiffeomorph S ∞).symm.injective
      ((isOpenEmbedding_capDiscs_inl c γ hγ hinj).injective h)
    rfl
  · obtain ⟨u, hx, hy⟩ := exists_annulusParam c γ hγ hinj j h
    exact map_orientationAt_eq c γ hγ hinj hrev j u hx hy
  · obtain ⟨u, hx, hy⟩ := exists_annulusParam c γ hγ hinj i h.symm
    exact (map_orientationAt_eq c γ hγ hinj hrev i u hx hy).symm
  · obtain rfl : i = j := by_contra fun hij ↦
      (disjoint_range_inr c γ hγ hinj hij).ne_of_mem ⟨_, rfl⟩ ⟨_, rfl⟩ h
    obtain rfl : x = y := injective_inr_ballDiffeomorph_symm c γ hγ hinj i h
    rfl

/-! ### The orientation of the capped surface -/

variable (o) in
/-- **The orientation of the capped surface.** If every loop `γ i` reverses orientation, from the
positive orientation of the circle to the boundary orientation of `S` (outward vector first),
then the capped surface carries the orientation for which the inclusion of the interior of `S`
preserves orientation from `o` (`capDiscs.isOrientationPreservingAt_inl`) and the inclusion of
each disc preserves orientation from the standard orientation of `ℂ`
(`capDiscs.isOrientationPreservingAt_inr`). -/
def orientation : Manifold.Orientation (𝓡 2) (capDiscs c γ hγ hinj) (Fin 2) :=
  iGlue (isLocalDiffeomorph_pieceMap c γ hγ hinj) (iUnion_range_pieceMap c γ hγ hinj)
    (o := pieceOrientation o) (map_orientationAt_pieceMap c γ hγ hinj hrev)

private theorem orientation_def :
    orientation c γ hγ hinj o hrev =
      iGlue (isLocalDiffeomorph_pieceMap c γ hγ hinj) (iUnion_range_pieceMap c γ hγ hinj)
        (o := pieceOrientation o) (map_orientationAt_pieceMap c γ hγ hinj hrev) :=
  (rfl)

/-- The inclusion of the interior of `S` preserves orientation, from `o` to the orientation of the
capped surface. -/
theorem isOrientationPreservingAt_inl (p : (𝓡∂ 2).interiorOpens S) :
    IsOrientationPreservingAt (o.restrict ((𝓡∂ 2).interiorOpens S))
      (orientation c γ hγ hinj o hrev) (inl c γ hγ hinj) p := by
  have h := isOrientationPreservingAt_iGlue (isLocalDiffeomorph_pieceMap c γ hγ hinj)
    (iUnion_range_pieceMap c γ hγ hinj) (map_orientationAt_pieceMap c γ hγ hinj hrev) none
    (((𝓡∂ 2).interiorOpensDiffeomorph S ∞) p)
  have he : inl c γ hγ hinj = pieceMap c γ hγ hinj none ∘ ((𝓡∂ 2).interiorOpensDiffeomorph S ∞) :=
    funext fun q ↦ (congrArg (inl c γ hγ hinj)
      (((𝓡∂ 2).interiorOpensDiffeomorph S ∞).symm_apply_apply q)).symm
  rw [he]
  exact h.comp (isOrientationPreservingAt_interiorOpensDiffeomorph _ ∞ p)

/-- The inclusion of each disc preserves orientation, from the standard orientation of `ℂ` to the
orientation of the capped surface. -/
theorem isOrientationPreservingAt_inr (i : ι) (z : ball) :
    IsOrientationPreservingAt
      (Manifold.Orientation.complex.restrict ball)
      (orientation c γ hγ hinj o hrev) (inr c γ hγ hinj i) z := by
  have h := isOrientationPreservingAt_iGlue (isLocalDiffeomorph_pieceMap c γ hγ hinj)
    (iUnion_range_pieceMap c γ hγ hinj) (map_orientationAt_pieceMap c γ hγ hinj hrev) (some i)
    (ballDiffeomorph z)
  have he : inr c γ hγ hinj i = pieceMap c γ hγ hinj (some i) ∘ ballDiffeomorph :=
    funext fun q ↦ (congrArg (inr c γ hγ hinj i) (ballDiffeomorph.symm_apply_apply q)).symm
  rw [he]
  exact h.comp (isOrientationPreservingAt_ballDiffeomorph z)

/-- **The orientation of the capped surface is characterized by the pieces.** An orientation of the
capped surface is `capDiscs.orientation` exactly when the inclusion of the interior of `S`
preserves orientation from `o`, and the inclusion of each disc preserves orientation from the
standard orientation of `ℂ`, at every point. -/
theorem eq_orientation_iff {o' : Manifold.Orientation (𝓡 2) (capDiscs c γ hγ hinj) (Fin 2)} :
    o' = orientation c γ hγ hinj o hrev ↔
      (∀ p, IsOrientationPreservingAt (o.restrict ((𝓡∂ 2).interiorOpens S)) o'
        (inl c γ hγ hinj) p) ∧
      ∀ i z, IsOrientationPreservingAt
        (Manifold.Orientation.complex.restrict ball)
        o' (inr c γ hγ hinj i) z := by
  refine ⟨?_, fun ⟨hl, hr⟩ ↦ ?_⟩
  · rintro rfl
    exact ⟨isOrientationPreservingAt_inl c γ hγ hinj hrev,
      isOrientationPreservingAt_inr c γ hγ hinj hrev⟩
  refine (eq_iGlue_iff _ _ _).2 fun k x ↦ ?_
  rcases k with _ | i
  · exact (hl _).comp (isOrientationPreservingAt_interiorOpensDiffeomorph_symm _ ∞ x)
  · exact (hr i _).comp (isOrientationPreservingAt_ballDiffeomorph_symm x)

/-! ### The caps as coordinate discs -/

/-- The `i`-th disc, as a partial diffeomorphism from the ball of radius `2` of `ℝ²` onto its image
in the capped surface. -/
private def discPartialDiffeomorph (i : ι) :
    PartialDiffeomorph (𝓡 2) (𝓡 2) discOpens (capDiscs c γ hγ hinj) ∞ :=
  (isLocalDiffeomorph_inr_ballDiffeomorph_symm c γ hγ hinj i).partialDiffeomorphOfInjective
    (injective_inr_ballDiffeomorph_symm c γ hγ hinj i)

private theorem coe_discPartialDiffeomorph (i : ι) :
    ⇑(discPartialDiffeomorph c γ hγ hinj i) =
      fun v : discOpens ↦ inr c γ hγ hinj i (ballDiffeomorph.symm v) :=
  IsLocalDiffeomorph.coe_partialDiffeomorphOfInjective ..

private theorem discPartialDiffeomorph_source (i : ι) :
    (discPartialDiffeomorph c γ hγ hinj i).source = univ :=
  IsLocalDiffeomorph.partialDiffeomorphOfInjective_source ..

/-- The chart `(inr i)⁻¹` of the capped surface, read in `ℝ²` through `z ↦ (re z, im z)`. -/
private def discChart (i : ι) :
    OpenPartialHomeomorph (capDiscs c γ hγ hinj) (EuclideanSpace ℝ (Fin 2)) :=
  ((discPartialDiffeomorph c γ hγ hinj i).symm.trans
    (PartialDiffeomorph.subtypeVal (𝓡 2) ∞ discOpens inferInstance)).toOpenPartialHomeomorph

private theorem ball_subset_discChart_target (i : ι) :
    Metric.ball 0 2 ⊆ (discChart c γ hγ hinj i).target := by
  intro v hv
  simpa [discChart, discPartialDiffeomorph_source] using mem_discOpens.2 (mem_ball_zero_iff.1 hv)

private theorem coe_discChart (i : ι) :
    ⇑(discChart c γ hγ hinj i) = Subtype.val ∘ (discPartialDiffeomorph c γ hγ hinj i).symm := by
  simp [discChart]

private theorem mem_discPartialDiffeomorph_target {i : ι} {x : capDiscs c γ hγ hinj}
    (hx : x ∈ (discChart c γ hγ hinj i).source) :
    x ∈ (discPartialDiffeomorph c γ hγ hinj i).target := by
  simpa [discChart] using hx

include hrev in
private theorem isOrientationPreservingAt_discChart (i : ι) {x : capDiscs c γ hγ hinj}
    (hx : x ∈ (discChart c γ hγ hinj i).source) :
    IsOrientationPreservingAt (orientation c γ hγ hinj o hrev)
      (Manifold.Orientation.euclideanSpace 2) (discChart c γ hγ hinj i) x := by
  have h : IsOrientationPreservingAt discOrientation (orientation c γ hγ hinj o hrev)
      (discPartialDiffeomorph c γ hγ hinj i) ((discPartialDiffeomorph c γ hγ hinj i).symm x) := by
    rw [coe_discPartialDiffeomorph, orientation_def]
    exact isOrientationPreservingAt_iGlue (isLocalDiffeomorph_pieceMap c γ hγ hinj)
      (iUnion_range_pieceMap c γ hγ hinj) (map_orientationAt_pieceMap c γ hγ hinj hrev) (some i) _
  rw [coe_discChart]
  exact (isOrientationPreservingAt_restrict _ discOpens _).comp
    (h.partialDiffeomorph_symm (mem_discPartialDiffeomorph_target c γ hγ hinj hx) (by simp))

variable [T2Space S]

variable (o) in
/-- **The caps as coordinate discs.** The `i`-th disc of the capped surface, as a coordinate disc
for the orientation `capDiscs.orientation`: its map is the inclusion `inr i` of the ball of
radius `2` of `ℂ` (`capDiscs.coe_coordinateDisc`). -/
def coordinateDisc (i : ι) :
    CoordinateDisc ((orientation c γ hγ hinj o hrev).toHomologicalOrientation
      (finrank_euclideanSpace_fin : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 1 + 1)) :=
  ofChart (discChart c γ hγ hinj i) two_pos (ball_subset_discChart_target c γ hγ hinj i)
    fun _ hx ↦ isOrientationPreservingAt_discChart c γ hγ hinj hrev i hx

/-- The map of the `i`-th coordinate disc is the inclusion `inr i` of the `i`-th disc. -/
@[simp]
theorem coe_coordinateDisc (i : ι) :
    ⇑(coordinateDisc c γ hγ hinj o hrev i) = inr c γ hγ hinj i := by
  funext z
  rw [coordinateDisc, ofChart_apply, zero_add, div_self two_ne_zero, one_smul]
  simp [discChart, discPartialDiffeomorph, ← coe_ballDiffeomorph]

end capDiscs

end SymplecticGeometry
