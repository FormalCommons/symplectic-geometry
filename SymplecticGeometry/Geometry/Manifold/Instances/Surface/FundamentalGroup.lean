/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Instances.Surface.Puncture
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import TauCeti.GroupTheory.SurfaceGroup.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import SymplecticGeometry.Geometry.Manifold.ConnectedSum.FundamentalGroup
import SymplecticGeometry.Geometry.Manifold.ConnectedSum.Restrict
import SymplecticGeometry.Geometry.Manifold.Diffeomorph.NestedOpens
import SymplecticGeometry.Topology.Maps.Embedding
import SymplecticGeometry.Algebra.Category.Grp.Pushout
import SymplecticGeometry.AlgebraicTopology.FundamentalGroup.Basic
import SymplecticGeometry.AlgebraicTopology.FundamentalGroup.PuncturedPlane
import SymplecticGeometry.Geometry.Manifold.Instances.Surface.PuncturedTorus
import SymplecticGeometry.GroupTheory.SurfaceGroup.Basic
import TauCeti.AlgebraicTopology.FundamentalGroup.BasepointChange
import TauCeti.AlgebraicTopology.FundamentalGroup.Homeomorph
import TauCeti.Topology.Homeomorph.SetCongr
import TauCeti.GroupTheory.SurfaceGroup.Gluing
import SymplecticGeometry.Geometry.Manifold.Instances.Surface.PuncturedSphere
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset

/-!
# The fundamental groups of the punctured closed surfaces

The closed surface of genus `g + 1` is the connected sum of the torus with the closed surface of
genus `g` along its ball `0` (`ClosedSurface.succDiffeomorph`). This file computes the
fundamental group of `ClosedSurface.puncture (g + 1) n` as a pushout of those of its two pieces:
the punctured torus `TauCeti.ConnectedSum.puncture EuclideanTorus.ball` and
`ClosedSurface.puncture g (n + 1)`, glued along the neck `{0}ᶜ` of the plane, and from it proves
the step of the induction on the genus: an isomorphism of the fundamental group of
`puncture g (n + 1)` with `TauCeti.SurfaceGroup.Orientable g (n + 1)`, with given values on the
standard loops, gives one for `puncture (g + 1) n` and `Orientable (g + 1) n`. The induction,
started at the punctured spheres (`ClosedSurface.exists_puncturedFundamentalGroupMulEquiv_zero`),
then identifies the fundamental group of every `puncture g n` with `Orientable g n`, and, for
`n = 0`, that of the closed surface of genus `g` with `Orientable g 0`.

## Main definitions

* `SymplecticGeometry.ClosedSurface.puncturedSuccInl g n`: the punctured torus in
  `puncture (g + 1) n`, as its summand `0`.
* `SymplecticGeometry.ClosedSurface.puncturedSuccInr g n`: `puncture g (n + 1)` in
  `puncture (g + 1) n`, through the second summand of the connected sum.
* `SymplecticGeometry.ClosedSurface.puncturedNeckInr g n`: the neck `{0}ᶜ` in
  `puncture g (n + 1)`, by `v ↦ ball g 0 (inversion 0 1 v)`, the map
  `TauCeti.ConnectedSum.neckInr` of the ball `0` read in `puncture g (n + 1)`.
* `SymplecticGeometry.ClosedSurface.puncturedFundamentalGroupMulEquiv g n`: the isomorphism of
  the fundamental group of `puncture g n` with `Orientable g n` sending the standard circles to
  `a` and `b` and the peripheral loops to the peripheral generators.
* `SymplecticGeometry.ClosedSurface.fundamentalGroupMulEquiv g`: the isomorphism of the
  fundamental group of `ClosedSurface g` with `Orientable g 0`, its case `n = 0`.

## Main results

* `SymplecticGeometry.ClosedSurface.isPushout_fundamentalGroup_puncture_succ`: based at the neck
  point `neckIsometry.circleBasepoint one_pos`, the square of fundamental groups formed by
  `TauCeti.ConnectedSum.neckInl`, `puncturedNeckInr`, `puncturedSuccInl` and `puncturedSuccInr`
  is a pushout in `GrpCat`.
* `SymplecticGeometry.ClosedSurface.map_puncturedNeckInr_circleLoop`: the circle of the neck goes
  to the circle `puncturedBallCircle g (n + 1) 0` of the ball `0`.
* `SymplecticGeometry.ClosedSurface.puncturedSuccInr_puncturedCircleLoop_apply`,
  `SymplecticGeometry.ClosedSurface.puncturedSuccInr_peripheralLoop_apply`: `puncturedSuccInr`
  sends the circles of the summand `k` and the peripheral loop `Fin.castSucc i` of genus `g` to
  those of the summand `k + 1` and the peripheral loop `i` of genus `g + 1`.
* `SymplecticGeometry.ClosedSurface.exists_puncturedFundamentalGroupMulEquiv_succ`: the step from
  genus `g` with `n + 1` punctures to genus `g + 1` with `n` punctures, for an isomorphism with
  `Orientable` sending `puncturedCircleLoop` to `a` and `b` and `peripheralLoop` to `peripheral`.
* `SymplecticGeometry.ClosedSurface.exists_puncturedFundamentalGroupMulEquiv`: for all `g` and
  `n`, such an isomorphism exists, by induction on `g` for all `n` at once.
* `SymplecticGeometry.ClosedSurface.puncturedFundamentalGroup_hom_ext`,
  `SymplecticGeometry.ClosedSurface.eq_puncturedFundamentalGroupMulEquiv`: the classes of the
  standard circles and the peripheral loops generate, so the isomorphism is unique.
* `SymplecticGeometry.ClosedSurface.fundamentalGroupMulEquiv_circleLoop_zero`,
  `SymplecticGeometry.ClosedSurface.fundamentalGroupMulEquiv_circleLoop_one`: the standard
  circles of the torus summand `k` go to `a k` and `b k` under `fundamentalGroupMulEquiv g`.

## Implementation notes

The square is `TauCeti.ConnectedSum.isPushout_fundamentalGroup` for the connected sum of the
torus with the open set `tailPuncture g n`, along the ball `0` corestricted to it. That sum is
carried onto `puncture (g + 1) n` by `TauCeti.ConnectedSum.restrictRightHomeomorph`, whose target
is `succDiffeomorph '' puncture (g + 1) n` (`ClosedSurface.image_succDiffeomorph_puncture`), and
its punctured second summand onto `puncture g (n + 1)`
(`ClosedSurface.imageVal_puncture_codRestrict_ball`, `TopologicalSpace.Opens.diffeomorphImageVal`).
The transport along these homeomorphisms by `CategoryTheory.IsPushout.of_iso'` follows the proof of
`TauCeti.ConnectedSum.isPushout_fundamentalGroup`, which transports Tau Ceti's
`TauCeti.isPushout_fundamentalGroup` in the same way.

For the step, the pieces are read in surface groups at the neck point: the punctured torus by
`EuclideanTorus.puncturedFundamentalGroupMulEquiv`, moved along `EuclideanTorus.peripheralPath`,
and `puncture g (n + 1)` by the given isomorphism, moved along `ballPath g 0`. The neck circle
then goes to `peripheral 1 1 0` and to the inverse of the last peripheral generator, so the square
is one of the homomorphisms `TauCeti.SurfaceGroup.Orientable.gluingMaps 1 0 g n`, and is identified
with `Monoid.PushoutI` by `CategoryTheory.IsPushout.mulEquivPushoutI`. Tau Ceti's
`TauCeti.SurfaceGroup.Orientable.equivPushoutI 1 0 g n` and the renaming
`TauCeti.SurfaceGroup.Orientable.congr` give `Orientable (g + 1) n`, and the base point is moved
back along the image of `ballPath g 0`. Since the torus piece has no other peripheral generator,
no generator of genus `g` is conjugated.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §1.2 (the Seifert–van Kampen
  theorem).
-/

public section

noncomputable section

open Set Function Topology TopologicalSpace CategoryTheory TauCeti
open scoped Manifold

namespace SymplecticGeometry.ClosedSurface

open EuclideanTorus (neckIsometry)

variable (g n : ℕ)

/-! ### The maps of the square -/

/-- The punctured torus in `puncture (g + 1) n`, as the summand `0` of the closed surface of
genus `g + 1`: the first summand of the connected sum
(`ClosedSurface.succDiffeomorph_summand_zero`). -/
def puncturedSuccInl : C(ConnectedSum.puncture EuclideanTorus.ball, puncture (g + 1) n) where
  toFun x := ⟨summand 0 x, summand_mem_puncture 0 x⟩
  continuous_toFun := (continuous_summand 0).subtype_mk _

@[simp]
theorem coe_puncturedSuccInl_apply (x : ConnectedSum.puncture EuclideanTorus.ball) :
    (puncturedSuccInl g n x : ClosedSurface (g + 1)) = summand 0 x :=
  (rfl)

/-- The set `puncture g (n + 1)` in `puncture (g + 1) n`, through the second summand of the
connected sum: `y ↦ succDiffeomorph.symm (inr y)`. -/
def puncturedSuccInr : C(puncture g (n + 1), puncture (g + 1) n) :=
  letI := ConnectedSum.chartedSpace (H := EuclideanSpace ℝ (Fin 2))
    EuclideanTorus.isOpenEmbedding_ball (isOpenEmbedding_ball (g := g) 0)
  { toFun y := ⟨succDiffeomorph.symm (ConnectedSum.inr EuclideanTorus.ball (ball g 0)
        ⟨y.val, puncture_succ_le_puncture_ball_zero y.property⟩),
      mem_puncture_of_succDiffeomorph_eq_inr (puncture_succ_le_tailPuncture y.property)
        (Diffeomorph.apply_symm_apply _ _)⟩
    continuous_toFun := (succDiffeomorph.symm.continuous.comp
      ((ConnectedSum.continuous_inr _ _).comp (continuous_subtypeVal.subtype_mk _))).subtype_mk _ }

@[simp]
theorem succDiffeomorph_puncturedSuccInr_apply (y : puncture g (n + 1)) :
    succDiffeomorph (puncturedSuccInr g n y : ClosedSurface (g + 1)) =
      ConnectedSum.inr _ _ ⟨y.val, puncture_succ_le_puncture_ball_zero y.property⟩ := by
  let := ConnectedSum.chartedSpace (H := EuclideanSpace ℝ (Fin 2))
    EuclideanTorus.isOpenEmbedding_ball (isOpenEmbedding_ball (g := g) 0)
  exact Diffeomorph.apply_symm_apply _ _

/-- The neck `{0}ᶜ` of the plane in `puncture g (n + 1)`: the map
`TauCeti.ConnectedSum.neckInr` of the ball `0`, `v ↦ ball g 0 (inversion 0 1 v)`. -/
def puncturedNeckInr : C(({0}ᶜ : Set (EuclideanSpace ℝ (Fin 2))), puncture g (n + 1)) where
  toFun v := ⟨ConnectedSum.neckInr (isOpenEmbedding_ball (g := g) 0) v,
    coe_neckInr_ball_zero_mem_puncture v⟩
  continuous_toFun := (continuous_subtypeVal.comp (ConnectedSum.neckInr _).continuous).subtype_mk _

@[simp]
theorem coe_puncturedNeckInr_apply (v : ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 2)))) :
    (puncturedNeckInr g n v : ClosedSurface g) =
      ConnectedSum.neckInr (isOpenEmbedding_ball (g := g) 0) v :=
  (rfl)

variable {g n}

/-- The base point of genus `g` goes to the base point of genus `g + 1`. -/
@[simp]
theorem puncturedSuccInr_basePoint :
    puncturedSuccInr g n ⟨basePoint g, basePoint_mem_puncture⟩ =
      ⟨basePoint (g + 1), basePoint_mem_puncture⟩ :=
  Subtype.ext <| by
    have hinj : Injective (succDiffeomorph (g := g)) := succDiffeomorph.injective
    refine hinj ?_
    rw [succDiffeomorph_puncturedSuccInr_apply, succDiffeomorph_basePoint]

/-- The standard circle `i` of the torus summand `k` of genus `g` goes to the circle `i` of the
summand `k + 1` of genus `g + 1`. -/
theorem puncturedSuccInr_puncturedCircleLoop_apply (k : Fin g) (i : Fin 2) (t : unitInterval) :
    puncturedSuccInr g n (puncturedCircleLoop g (n + 1) k i t) =
      puncturedCircleLoop (g + 1) n k.succ i t :=
  Subtype.ext <| by
    have hinj : Injective (succDiffeomorph (g := g)) := succDiffeomorph.injective
    refine (hinj ?_).symm
    rw [succDiffeomorph_puncturedSuccInr_apply, coe_puncturedCircleLoop_apply,
      succDiffeomorph_circleLoop_succ_apply]
    exact congrArg _ (Subtype.ext (coe_puncturedCircleLoop_apply k i t).symm)

/-- The peripheral loop `Fin.castSucc i` of `puncture g (n + 1)` goes to the peripheral loop `i`
of `puncture (g + 1) n`. -/
theorem puncturedSuccInr_peripheralLoop_apply (i : Fin n) (t : unitInterval) :
    puncturedSuccInr g n (peripheralLoop g (n + 1) i.castSucc t) = peripheralLoop (g + 1) n i t :=
  Subtype.ext <| by
    have hinj : Injective (succDiffeomorph (g := g)) := succDiffeomorph.injective
    refine hinj ?_
    rw [succDiffeomorph_puncturedSuccInr_apply, succDiffeomorph_peripheralLoop_apply]

/-- The neck point goes to the start of the circle of the ball `0`. -/
theorem puncturedNeckInr_circleBasepoint :
    puncturedNeckInr g n (neckIsometry.circleBasepoint one_pos) =
      ⟨ball g 0 (neckIsometry 1), ball_neckIsometry_one_mem_puncture 0⟩ :=
  Subtype.ext <| by
    rw [coe_puncturedNeckInr_apply, ConnectedSum.coe_neckInr_circleBasepoint, inv_one,
      Complex.ofReal_one]

/-- The two pieces meet at the neck point. -/
theorem puncturedSuccInr_ball_neckIsometry_one :
    puncturedSuccInr g n ⟨ball g 0 (neckIsometry 1), ball_neckIsometry_one_mem_puncture 0⟩ =
      puncturedSuccInl g n (ConnectedSum.neckInl EuclideanTorus.isOpenEmbedding_ball
        (neckIsometry.circleBasepoint one_pos)) :=
  Subtype.ext <| by
    have hinj : Injective (succDiffeomorph (g := g)) := succDiffeomorph.injective
    refine hinj ?_
    rw [succDiffeomorph_puncturedSuccInr_apply, coe_puncturedSuccInl_apply,
      succDiffeomorph_summand_zero, inl_neckInl_circleBasepoint]

/-- The circle of the neck, `LinearIsometryEquiv.circleLoop` for `neckIsometry` and radius `1`,
goes to the circle `puncturedBallCircle g (n + 1) 0` of the ball `0`. -/
theorem map_puncturedNeckInr_circleLoop :
    (neckIsometry.circleLoop one_pos).map (puncturedNeckInr g n).continuous =
      (puncturedBallCircle g (n + 1) 0).cast puncturedNeckInr_circleBasepoint
        puncturedNeckInr_circleBasepoint := by
  ext t
  rw [Path.cast_coe, coe_puncturedBallCircle_apply, ballCircle_zero_apply]
  simp

/-! ### The square -/

/-- The punctured second summand of the sum of the torus with `tailPuncture g n` is
`puncture g (n + 1)`. -/
private def puncturedSummandHomeomorph :
    puncture g (n + 1) ≃ₜ ConnectedSum.puncture
      (codRestrict (ball g 0) (tailPuncture g n) ball_zero_mem_tailPuncture) :=
  (Homeomorph.setCongr (by rw [imageVal_puncture_codRestrict_ball])).trans
    (Opens.diffeomorphImageVal (I := 𝓡 2) (n := 0) _).symm.toHomeomorph

private theorem coe_coe_puncturedSummandHomeomorph_apply (y : puncture g (n + 1)) :
    ((puncturedSummandHomeomorph y : (tailPuncture g n : Set (ClosedSurface g))) :
      ClosedSurface g) = y := by
  rw [puncturedSummandHomeomorph, Homeomorph.trans_apply, Homeomorph.setCongr_apply]
  -- `Diffeomorph.coe_toHomeomorph` cannot rewrite here, as instance search does not find the
  -- charted space structure on `Opens.imageVal _` that this goal carries; `exact` unfolds the
  -- coercion of `Diffeomorph.toHomeomorph` instead.
  exact Opens.coe_diffeomorphImageVal_symm_apply (I := 𝓡 2) (n := 0) _ _

/-- The sum of the torus with `tailPuncture g n` is `puncture (g + 1) n`. -/
private def puncturedSumHomeomorph :
    puncture (g + 1) n ≃ₜ ConnectedSum EuclideanTorus.ball
      (codRestrict (ball g 0) (tailPuncture g n) ball_zero_mem_tailPuncture) :=
  letI := ConnectedSum.chartedSpace (H := EuclideanSpace ℝ (Fin 2))
    EuclideanTorus.isOpenEmbedding_ball (isOpenEmbedding_ball (g := g) 0)
  (succDiffeomorph.toHomeomorph.subtype fun x ↦ by
    rw [Diffeomorph.coe_toHomeomorph, ← image_succDiffeomorph_puncture]
    have hinj : Injective (succDiffeomorph (g := g)) := succDiffeomorph.injective
    exact hinj.mem_set_image.symm).trans
      (ConnectedSum.restrictRightHomeomorph EuclideanTorus.isOpenEmbedding_ball
        (isOpenEmbedding_ball 0) (tailPuncture g n).isOpen ball_zero_mem_tailPuncture).symm

private theorem coe_restrictRightHomeomorph_puncturedSumHomeomorph (x : puncture (g + 1) n) :
    (ConnectedSum.restrictRightHomeomorph EuclideanTorus.isOpenEmbedding_ball
      (isOpenEmbedding_ball 0) (tailPuncture g n).isOpen ball_zero_mem_tailPuncture
        (puncturedSumHomeomorph x) : ConnectedSum EuclideanTorus.ball (ball g 0)) =
      succDiffeomorph (x : ClosedSurface (g + 1)) := by
  let := ConnectedSum.chartedSpace (H := EuclideanSpace ℝ (Fin 2))
    EuclideanTorus.isOpenEmbedding_ball (isOpenEmbedding_ball (g := g) 0)
  rw [puncturedSumHomeomorph, Homeomorph.trans_apply, Homeomorph.apply_symm_apply,
    Homeomorph.subtype_apply_coe, Diffeomorph.coe_toHomeomorph]

private theorem puncturedSumHomeomorph_eq_iff (x : puncture (g + 1) n) (p) :
    puncturedSumHomeomorph x = p ↔
      succDiffeomorph (x : ClosedSurface (g + 1)) =
        (ConnectedSum.restrictRightHomeomorph EuclideanTorus.isOpenEmbedding_ball
          (isOpenEmbedding_ball 0) (tailPuncture g n).isOpen ball_zero_mem_tailPuncture p :
            ConnectedSum EuclideanTorus.ball (ball g 0)) := by
  rw [← coe_restrictRightHomeomorph_puncturedSumHomeomorph, Subtype.coe_inj,
    (Homeomorph.injective _).eq_iff]

variable (g n) in
/-- **Van Kampen for a punctured closed surface.** Read as the connected sum of the torus with the
closed surface of genus `g` along its ball `0`, the closed surface of genus `g + 1` with `n`
centres removed is the union of the punctured torus and of `puncture g (n + 1)`, which meet in
the neck `{0}ᶜ` of the plane. Based at the neck point `neckIsometry.circleBasepoint one_pos`, the
square of fundamental groups formed by `TauCeti.ConnectedSum.neckInl` and
`ClosedSurface.puncturedNeckInr` from the neck, and by the inclusions
`ClosedSurface.puncturedSuccInl` and `ClosedSurface.puncturedSuccInr` of the two pieces, is a
pushout of groups. -/
theorem isPushout_fundamentalGroup_puncture_succ :
    IsPushout
      (GrpCat.ofHom (FundamentalGroup.map
        (ConnectedSum.neckInl EuclideanTorus.isOpenEmbedding_ball)
        (neckIsometry.circleBasepoint one_pos)))
      (GrpCat.ofHom (FundamentalGroup.mapOfEq (puncturedNeckInr g n)
        puncturedNeckInr_circleBasepoint))
      (GrpCat.ofHom (FundamentalGroup.map (puncturedSuccInl g n)
        (ConnectedSum.neckInl EuclideanTorus.isOpenEmbedding_ball
          (neckIsometry.circleBasepoint one_pos))))
      (GrpCat.ofHom (FundamentalGroup.mapOfEq (puncturedSuccInr g n)
        puncturedSuccInr_ball_neckIsometry_one)) := by
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 2)) :=
    Module.one_lt_rank_of_one_lt_finrank (by simp)
  have h₂ := (isOpenEmbedding_ball (g := g) 0).codRestrict (tailPuncture g n)
    ball_zero_mem_tailPuncture
  set σ := puncturedSummandHomeomorph (g := g) (n := n)
  set τ := puncturedSumHomeomorph (g := g) (n := n)
  have hσ : σ ⟨ball g 0 (neckIsometry 1), ball_neckIsometry_one_mem_puncture 0⟩ =
      ConnectedSum.neckInr h₂ (neckIsometry.circleBasepoint one_pos) :=
    Subtype.ext <| Subtype.ext <| by
      rw [ConnectedSum.coe_neckInr_circleBasepoint h₂, coe_coe_puncturedSummandHomeomorph_apply]
      simp
  have hτ : τ (puncturedSuccInl g n (ConnectedSum.neckInl EuclideanTorus.isOpenEmbedding_ball
        (neckIsometry.circleBasepoint one_pos))) =
      ConnectedSum.inl _ _ (ConnectedSum.neckInl EuclideanTorus.isOpenEmbedding_ball
        (neckIsometry.circleBasepoint one_pos)) := by
    rw [puncturedSumHomeomorph_eq_iff, ConnectedSum.coe_restrictRightHomeomorph_inl,
      coe_puncturedSuccInl_apply, succDiffeomorph_summand_zero]
  let : ChartedSpace (EuclideanSpace ℝ (Fin 2)) (tailPuncture g n : Set (ClosedSurface g)) :=
    inferInstanceAs (ChartedSpace _ (tailPuncture g n))
  have : ConnectedSpace (tailPuncture g n : Set (ClosedSurface g)) :=
    inferInstanceAs (ConnectedSpace (tailPuncture g n))
  refine (ConnectedSum.isPushout_fundamentalGroup hrank EuclideanTorus.isOpenEmbedding_ball h₂
    (neckIsometry.circleBasepoint one_pos)).of_iso' (Iso.refl _) (Iso.refl _)
    (FundamentalGroup.homeomorphMulEquivOfEq σ hσ).toGrpIso
    (FundamentalGroup.homeomorphMulEquivOfEq τ hτ).toGrpIso ?_ ?_ ?_ ?_
  all_goals
    try rw [Iso.refl_hom, Category.id_comp]
    refine GrpCat.ext fun p ↦ ?_
    simp only [GrpCat.hom_comp, GrpCat.hom_ofHom, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.toGrpIso_hom, MulEquiv.coe_toMonoidHom,
      FundamentalGroup.homeomorphMulEquivOfEq_apply, ← FundamentalGroup.mapOfEq_rfl, Iso.refl_hom,
      Category.comp_id]
  · refine (FundamentalGroup.mapOfEq_mapOfEq_eq_mapOfEq ?_ _ _ _ p).symm
    refine ContinuousMap.ext fun w ↦ Subtype.ext <| Subtype.ext ?_
    simp only [σ, ContinuousMap.comp_apply, ContinuousMap.coe_ofClass]
    rw [coe_coe_puncturedSummandHomeomorph_apply, coe_puncturedNeckInr_apply,
      ConnectedSum.coe_neckInr_apply, ConnectedSum.coe_neckInr_apply, val_codRestrict_apply]
  · refine (FundamentalGroup.mapOfEq_mapOfEq_eq_mapOfEq ?_ _ _ _ p).symm
    refine ContinuousMap.ext fun x ↦ (puncturedSumHomeomorph_eq_iff _ _).2 ?_
    simp only [ContinuousMap.coe_mk, ConnectedSum.coe_restrictRightHomeomorph_inl]
    simp
  · refine FundamentalGroup.mapOfEq_mapOfEq_eq_mapOfEq_mapOfEq ?_ _ _ _ _ p
    refine ContinuousMap.ext fun y ↦ ((puncturedSumHomeomorph_eq_iff _ _).2 ?_).symm
    simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk,
      ConnectedSum.coe_restrictRightHomeomorph_inr, succDiffeomorph_puncturedSuccInr_apply]
    exact congrArg _ (Subtype.ext (by
      rw [ConnectedSum.coe_punctureMap, coe_coe_puncturedSummandHomeomorph_apply]))

/-! ### The step of the induction -/

/-- The fundamental group of the punctured torus at the neck point, moved there from `0` along
`EuclideanTorus.peripheralPath`, is `Orientable 1 1`. -/
private def torusNeckMulEquiv :
    FundamentalGroup (ConnectedSum.puncture EuclideanTorus.ball)
        (ConnectedSum.neckInl EuclideanTorus.isOpenEmbedding_ball
          (neckIsometry.circleBasepoint one_pos)) ≃* SurfaceGroup.Orientable 1 1 :=
  (FundamentalGroup.fundamentalGroupMulEquivOfPath EuclideanTorus.peripheralPath).symm.trans
    EuclideanTorus.puncturedFundamentalGroupMulEquiv

private theorem torusNeckMulEquiv_neckLoop :
    torusNeckMulEquiv (FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk EuclideanTorus.neckLoop)) =
      SurfaceGroup.Orientable.peripheral 1 1 0 := by
  rw [torusNeckMulEquiv, MulEquiv.trans_apply,
    FundamentalGroup.fundamentalGroupMulEquivOfPath_symm_fromPath_mk,
    ← EuclideanTorus.puncturedFundamentalGroupMulEquiv_peripheralLoop,
    EuclideanTorus.peripheralLoop_def]
  simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.trans_assoc]

variable (n) in
/-- The fundamental group of `puncture g (n + 1)` at the start of the circle of the ball `0`,
moved there from the base point along `ballPath g 0`, read through `e`. -/
private def neckMulEquiv
    (e : FundamentalGroup (puncture g (n + 1)) ⟨basePoint g, basePoint_mem_puncture⟩ ≃*
      SurfaceGroup.Orientable g (n + 1)) :
    FundamentalGroup (puncture g (n + 1))
        ⟨ball g 0 (neckIsometry 1), ball_neckIsometry_one_mem_puncture 0⟩ ≃*
      SurfaceGroup.Orientable g (n + 1) :=
  (FundamentalGroup.fundamentalGroupMulEquivOfPath (puncturedBallPath g (n + 1) 0)).symm.trans e

private theorem neckMulEquiv_puncturedBallCircle
    {e : FundamentalGroup (puncture g (n + 1)) ⟨basePoint g, basePoint_mem_puncture⟩ ≃*
      SurfaceGroup.Orientable g (n + 1)}
    (he : e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
      (peripheralLoop g (n + 1) (Fin.last n)))) =
        SurfaceGroup.Orientable.peripheral g (n + 1) (Fin.last n)) :
    neckMulEquiv n e (FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (puncturedBallCircle g (n + 1) 0))) =
      (SurfaceGroup.Orientable.peripheral g (n + 1) (Fin.last n))⁻¹ := by
  rw [neckMulEquiv, MulEquiv.trans_apply,
    FundamentalGroup.fundamentalGroupMulEquivOfPath_symm_fromPath_mk, ← he, ← map_inv,
    peripheralLoop_eq_puncturedBallPath_trans, Fin.rev_last, Fin.val_zero,
    ← FundamentalGroup.fromPath_symm, ← Path.Homotopic.Quotient.mk_symm]
  simp only [Path.trans_symm, Path.symm_symm, Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.mk_symm]

variable (n) in
/-- The square of fundamental groups of `ClosedSurface.isPushout_fundamentalGroup_puncture_succ`,
with its two pieces read through `torusNeckMulEquiv` and `neckMulEquiv n e`, and its neck through
`ℤ`: a pushout of the homomorphisms `gluingMaps 1 0 g n`. -/
private theorem isPushout_gluingMaps
    {e : FundamentalGroup (puncture g (n + 1)) ⟨basePoint g, basePoint_mem_puncture⟩ ≃*
      SurfaceGroup.Orientable g (n + 1)}
    (he : e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
      (peripheralLoop g (n + 1) (Fin.last n)))) =
        SurfaceGroup.Orientable.peripheral g (n + 1) (Fin.last n)) :
    IsPushout (GrpCat.ofHom (SurfaceGroup.Orientable.gluingMaps 1 0 g n false))
      (GrpCat.ofHom (SurfaceGroup.Orientable.gluingMaps 1 0 g n true))
      (GrpCat.ofHom ((FundamentalGroup.map (puncturedSuccInl g n)
        (ConnectedSum.neckInl EuclideanTorus.isOpenEmbedding_ball
          (neckIsometry.circleBasepoint one_pos))).comp torusNeckMulEquiv.symm.toMonoidHom))
      (GrpCat.ofHom ((FundamentalGroup.mapOfEq (puncturedSuccInr g n)
        puncturedSuccInr_ball_neckIsometry_one).comp (neckMulEquiv n e).symm.toMonoidHom)) := by
  refine (isPushout_fundamentalGroup_puncture_succ g n).of_iso
    (neckIsometry.fundamentalGroupComplSingletonMulEquivInt one_pos).toGrpIso
    torusNeckMulEquiv.toGrpIso (neckMulEquiv n e).toGrpIso (Iso.refl _) ?_ ?_ ?_ ?_
  · refine GrpCat.hom_ext (neckIsometry.fundamentalGroupComplSingleton_hom_ext one_pos ?_)
    simp only [GrpCat.hom_comp, GrpCat.hom_ofHom, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.toGrpIso_hom, MulEquiv.coe_toMonoidHom]
    rw [LinearIsometryEquiv.fundamentalGroupComplSingletonMulEquivInt_circleLoop,
      SurfaceGroup.Orientable.gluingMaps_false, zpowersHom_apply, toAdd_ofAdd, zpow_one,
      TauCeti.FundamentalGroup.map_fromPath,
      ← EuclideanTorus.neckLoop_def]
    -- `Fin.last 0` is `0`, and `peripheral 1 (0 + 1)` is `peripheral 1 1`, by `Nat` arithmetic.
    exact torusNeckMulEquiv_neckLoop
  · refine GrpCat.hom_ext (neckIsometry.fundamentalGroupComplSingleton_hom_ext one_pos ?_)
    simp only [GrpCat.hom_comp, GrpCat.hom_ofHom, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.toGrpIso_hom, MulEquiv.coe_toMonoidHom]
    rw [LinearIsometryEquiv.fundamentalGroupComplSingletonMulEquivInt_circleLoop,
      SurfaceGroup.Orientable.gluingMaps_true, zpowersHom_apply, toAdd_ofAdd, zpow_one,
      FundamentalGroup.mapOfEq_fromPath_mk, map_puncturedNeckInr_circleLoop]
    -- `Path.cast` keeps the underlying map, so the cast circle is `puncturedBallCircle` itself.
    exact neckMulEquiv_puncturedBallCircle he
  · refine GrpCat.ext fun x ↦ ?_
    simp
  · refine GrpCat.ext fun x ↦ ?_
    simp

variable (n) in
/-- The fundamental group of `puncture (g + 1) n` at the neck point is `Orientable (g + 1) n`:
the pushout of `isPushout_gluingMaps`, then Tau Ceti's `equivPushoutI 1 0 g n`, then the renaming
of `Orientable (1 + g) (0 + n)`. -/
private def neckSuccMulEquiv
    {e : FundamentalGroup (puncture g (n + 1)) ⟨basePoint g, basePoint_mem_puncture⟩ ≃*
      SurfaceGroup.Orientable g (n + 1)}
    (he : e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
      (peripheralLoop g (n + 1) (Fin.last n)))) =
        SurfaceGroup.Orientable.peripheral g (n + 1) (Fin.last n)) :
    FundamentalGroup (puncture (g + 1) n) (puncturedSuccInl g n
        (ConnectedSum.neckInl EuclideanTorus.isOpenEmbedding_ball
          (neckIsometry.circleBasepoint one_pos))) ≃* SurfaceGroup.Orientable (g + 1) n :=
  (isPushout_gluingMaps n he).mulEquivPushoutI.trans
    ((SurfaceGroup.Orientable.equivPushoutI 1 0 g n).symm.trans
      (SurfaceGroup.Orientable.congr (add_comm 1 g) (zero_add n)))

private theorem neckSuccMulEquiv_map_puncturedSuccInl
    {e : FundamentalGroup (puncture g (n + 1)) ⟨basePoint g, basePoint_mem_puncture⟩ ≃*
      SurfaceGroup.Orientable g (n + 1)}
    (he : e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
      (peripheralLoop g (n + 1) (Fin.last n)))) =
        SurfaceGroup.Orientable.peripheral g (n + 1) (Fin.last n)) (x) :
    neckSuccMulEquiv n he (FundamentalGroup.map (puncturedSuccInl g n) _ x) =
      SurfaceGroup.Orientable.congr (add_comm 1 g) (zero_add n)
        ((SurfaceGroup.Orientable.equivPushoutI 1 0 g n).symm
          (Monoid.PushoutI.of false (torusNeckMulEquiv x))) := by
  have := (isPushout_gluingMaps n he).mulEquivPushoutI_ofHom_inl (torusNeckMulEquiv x)
  simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    MulEquiv.symm_apply_apply] at this
  rw [neckSuccMulEquiv, MulEquiv.trans_apply, this, MulEquiv.trans_apply]

private theorem neckSuccMulEquiv_mapOfEq_puncturedSuccInr
    {e : FundamentalGroup (puncture g (n + 1)) ⟨basePoint g, basePoint_mem_puncture⟩ ≃*
      SurfaceGroup.Orientable g (n + 1)}
    (he : e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
      (peripheralLoop g (n + 1) (Fin.last n)))) =
        SurfaceGroup.Orientable.peripheral g (n + 1) (Fin.last n)) (x) :
    neckSuccMulEquiv n he
        (FundamentalGroup.mapOfEq (puncturedSuccInr g n) puncturedSuccInr_ball_neckIsometry_one x) =
      SurfaceGroup.Orientable.congr (add_comm 1 g) (zero_add n)
        ((SurfaceGroup.Orientable.equivPushoutI 1 0 g n).symm
          (Monoid.PushoutI.of true (neckMulEquiv n e x))) := by
  have := (isPushout_gluingMaps n he).mulEquivPushoutI_ofHom_inr (neckMulEquiv n e x)
  simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    MulEquiv.symm_apply_apply] at this
  rw [neckSuccMulEquiv, MulEquiv.trans_apply, this, MulEquiv.trans_apply]

variable (g n) in
/-- The path from the base point of `puncture (g + 1) n` to the neck point: the path to the
ball `0` of genus `g`, in the second summand. -/
private def neckPath :
    Path (⟨basePoint (g + 1), basePoint_mem_puncture⟩ : puncture (g + 1) n)
      (puncturedSuccInl g n (ConnectedSum.neckInl EuclideanTorus.isOpenEmbedding_ball
        (neckIsometry.circleBasepoint one_pos))) :=
  ((puncturedBallPath g (n + 1) 0).map (puncturedSuccInr g n).continuous).cast
    puncturedSuccInr_basePoint.symm puncturedSuccInr_ball_neckIsometry_one.symm

private theorem neckPath_apply (t : unitInterval) :
    neckPath g n t = puncturedSuccInr g n (puncturedBallPath g (n + 1) 0 t) :=
  (rfl)

private theorem succDiffeomorph_neckPath_apply (t : unitInterval) :
    succDiffeomorph (neckPath g n t : ClosedSurface (g + 1)) =
      ConnectedSum.inr _ _ ⟨ballPath g 0 t,
        ConnectedSum.mem_puncture.2 (ballPath_ne_ball 0 t 0)⟩ := by
  rw [neckPath_apply, succDiffeomorph_puncturedSuccInr_apply]
  exact congrArg _ (Subtype.ext (coe_puncturedBallPath_apply 0 t))

/-- The standard circle `i` of the torus summand `0` of genus `g + 1` is `neckPath`, then the
reverse of `EuclideanTorus.peripheralPath` and the circle `EuclideanTorus.circleLoop i` in the
punctured torus, and back. -/
private theorem puncturedCircleLoop_zero (i : Fin 2) :
    puncturedCircleLoop (g + 1) n 0 i =
      (((neckPath g n).trans (EuclideanTorus.peripheralPath.symm.map
        (puncturedSuccInl g n).continuous)).trans
          ((EuclideanTorus.circleLoop i).map (puncturedSuccInl g n).continuous)).trans
        ((neckPath g n).trans (EuclideanTorus.peripheralPath.symm.map
          (puncturedSuccInl g n).continuous)).symm := by
  have hinj : Injective (succDiffeomorph (g := g)) := succDiffeomorph.injective
  ext t
  rw [coe_puncturedCircleLoop_apply, circleLoop_def, summandPath_succ_zero]
  simp only [Path.trans_apply, Path.symm_apply, Path.map_coe, Function.comp_apply]
  -- On the torus pieces both sides are `summand 0` of the same point, by the definition of
  -- `puncturedSuccInl`; on the path to the ball, compare the images under `succDiffeomorph`.
  split_ifs <;> first
    | rfl
    | (refine hinj ?_; rw [succDiffeomorph_succPath_apply, succDiffeomorph_neckPath_apply])

/-- Moved to the neck point along `neckPath`, the standard circle `i` of the torus summand `0` of
genus `g + 1` is the image of the circle `EuclideanTorus.circleLoop i` of the punctured torus
moved to the neck point along `EuclideanTorus.peripheralPath`. -/
private theorem fundamentalGroupMulEquivOfPath_neckPath_puncturedCircleLoop_zero (i : Fin 2) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath (neckPath g n)
        (FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk (puncturedCircleLoop (g + 1) n 0 i))) =
      FundamentalGroup.map (puncturedSuccInl g n) _
        (FundamentalGroup.fundamentalGroupMulEquivOfPath EuclideanTorus.peripheralPath
          (FundamentalGroup.fromPath
            (Path.Homotopic.Quotient.mk (EuclideanTorus.circleLoop i)))) := by
  rw [FundamentalGroup.fundamentalGroupMulEquivOfPath_fromPath_mk,
    FundamentalGroup.fundamentalGroupMulEquivOfPath_fromPath_mk,
    TauCeti.FundamentalGroup.map_fromPath, puncturedCircleLoop_zero]
  simp only [Path.map_trans, Path.map_symm, Path.trans_symm, Path.symm_symm,
    Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
    Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.symm_trans_trans,
    Path.Homotopic.Quotient.trans_refl, Path.Homotopic.Quotient.symm_trans]

/-- **The induction step for the punctured closed surfaces.** If the fundamental group of the
closed surface of genus `g` with `n + 1` centres removed is `Orientable g (n + 1)`, by an
isomorphism sending the standard circles `circleLoop g k 0` and `circleLoop g k 1` to `a k` and
`b k` and the peripheral loops to the peripheral generators, then the same holds for genus
`g + 1` and `n` centres removed. -/
theorem exists_puncturedFundamentalGroupMulEquiv_succ
    (h : ∃ e : FundamentalGroup (puncture g (n + 1)) ⟨basePoint g, basePoint_mem_puncture⟩ ≃*
        SurfaceGroup.Orientable g (n + 1),
      (∀ k : Fin g, e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
          (puncturedCircleLoop g (n + 1) k 0))) = SurfaceGroup.Orientable.a g (n + 1) k) ∧
      (∀ k : Fin g, e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
          (puncturedCircleLoop g (n + 1) k 1))) = SurfaceGroup.Orientable.b g (n + 1) k) ∧
      ∀ i, e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
          (peripheralLoop g (n + 1) i))) = SurfaceGroup.Orientable.peripheral g (n + 1) i) :
    ∃ e : FundamentalGroup (puncture (g + 1) n) ⟨basePoint (g + 1), basePoint_mem_puncture⟩ ≃*
        SurfaceGroup.Orientable (g + 1) n,
      (∀ k : Fin (g + 1), e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
          (puncturedCircleLoop (g + 1) n k 0))) = SurfaceGroup.Orientable.a (g + 1) n k) ∧
      (∀ k : Fin (g + 1), e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
          (puncturedCircleLoop (g + 1) n k 1))) = SurfaceGroup.Orientable.b (g + 1) n k) ∧
      ∀ i, e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
          (peripheralLoop (g + 1) n i))) = SurfaceGroup.Orientable.peripheral (g + 1) n i := by
  obtain ⟨e, ha, hb, hp⟩ := h
  let E := (FundamentalGroup.fundamentalGroupMulEquivOfPath (neckPath g n)).trans
    (neckSuccMulEquiv n (hp (Fin.last n)))
  -- A loop of genus `g` carried into the second summand.
  have hinr : ∀ L L', (∀ t, puncturedSuccInr g n (L t) = L' t) →
      E (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk L')) =
        SurfaceGroup.Orientable.congr (add_comm 1 g) (zero_add n)
          ((SurfaceGroup.Orientable.equivPushoutI 1 0 g n).symm
            (Monoid.PushoutI.of true (e (FundamentalGroup.fromPath
              (Path.Homotopic.Quotient.mk L))))) := by
    intro L L' hL
    have hx : e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk L)) =
        neckMulEquiv n e (FundamentalGroup.fundamentalGroupMulEquivOfPath
          (puncturedBallPath g (n + 1) 0)
          (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk L))) := by
      rw [neckMulEquiv, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rw [hx, ← neckSuccMulEquiv_mapOfEq_puncturedSuccInr (hp (Fin.last n)),
      FundamentalGroup.mapOfEq_fundamentalGroupMulEquivOfPath _ puncturedSuccInr_basePoint,
      FundamentalGroup.mapOfEq_fromPath_mk, MulEquiv.trans_apply]
    congr 4
    ext t
    exact congrArg Subtype.val (hL t).symm
  have htorus : ∀ i : Fin 2, E (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
      (puncturedCircleLoop (g + 1) n 0 i))) =
        SurfaceGroup.Orientable.congr (add_comm 1 g) (zero_add n)
          ((SurfaceGroup.Orientable.equivPushoutI 1 0 g n).symm
            (Monoid.PushoutI.of false (EuclideanTorus.puncturedFundamentalGroupMulEquiv
              (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
                (EuclideanTorus.circleLoop i)))))) := by
    intro i
    rw [MulEquiv.trans_apply, fundamentalGroupMulEquivOfPath_neckPath_puncturedCircleLoop_zero,
      neckSuccMulEquiv_map_puncturedSuccInl,
      torusNeckMulEquiv, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  refine ⟨E, fun k ↦ ?_, fun k ↦ ?_, fun i ↦ ?_⟩
  · cases k using Fin.cases with
    | zero =>
      rw [htorus, EuclideanTorus.puncturedFundamentalGroupMulEquiv_circleLoop_zero]
      simp only [SurfaceGroup.Orientable.equivPushoutI_symm_of_false_a,
        SurfaceGroup.Orientable.congr_a]
      congr 1
    | succ k =>
      rw [hinr _ _ (puncturedSuccInr_puncturedCircleLoop_apply k 0), ha]
      simp
  · cases k using Fin.cases with
    | zero =>
      rw [htorus, EuclideanTorus.puncturedFundamentalGroupMulEquiv_circleLoop_one]
      simp only [SurfaceGroup.Orientable.equivPushoutI_symm_of_false_b,
        SurfaceGroup.Orientable.congr_b]
      congr 1
    | succ k =>
      rw [hinr _ _ (puncturedSuccInr_puncturedCircleLoop_apply k 1), hb]
      simp
  · rw [hinr _ _ (puncturedSuccInr_peripheralLoop_apply i), hp]
    simp

/-! ### The induction on the genus -/

variable (g n) in
/-- **The fundamental groups of the punctured closed surfaces.** The fundamental group of the
closed surface of genus `g` with the centres of its balls `0, …, n - 1` removed is isomorphic to
the surface group `Orientable g n`, by an isomorphism sending the standard circles
`puncturedCircleLoop g n k 0` and `puncturedCircleLoop g n k 1` to `a k` and `b k` and the
peripheral loop `i` to the peripheral generator `i`. -/
theorem exists_puncturedFundamentalGroupMulEquiv :
    ∃ e : FundamentalGroup (puncture g n) ⟨basePoint g, basePoint_mem_puncture⟩ ≃*
        SurfaceGroup.Orientable g n,
      (∀ k : Fin g, e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
          (puncturedCircleLoop g n k 0))) = SurfaceGroup.Orientable.a g n k) ∧
      (∀ k : Fin g, e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
          (puncturedCircleLoop g n k 1))) = SurfaceGroup.Orientable.b g n k) ∧
      ∀ i, e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (peripheralLoop g n i))) =
        SurfaceGroup.Orientable.peripheral g n i := by
  induction g generalizing n with
  | zero => exact exists_puncturedFundamentalGroupMulEquiv_zero n
  | succ g ih => exact exists_puncturedFundamentalGroupMulEquiv_succ (ih (n + 1))

variable (g n) in
/-- The isomorphism of the fundamental group of `puncture g n`, at the base point, with the
surface group `Orientable g n`, sending the standard circles to the generators `a` and `b` and the
peripheral loops to the peripheral generators. It is the only one with these values
(`ClosedSurface.eq_puncturedFundamentalGroupMulEquiv`). -/
def puncturedFundamentalGroupMulEquiv :
    FundamentalGroup (puncture g n) ⟨basePoint g, basePoint_mem_puncture⟩ ≃*
      SurfaceGroup.Orientable g n :=
  (exists_puncturedFundamentalGroupMulEquiv g n).choose

@[simp]
theorem puncturedFundamentalGroupMulEquiv_puncturedCircleLoop_zero (k : Fin g) :
    puncturedFundamentalGroupMulEquiv g n (FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (puncturedCircleLoop g n k 0))) =
        SurfaceGroup.Orientable.a g n k :=
  (exists_puncturedFundamentalGroupMulEquiv g n).choose_spec.1 k

@[simp]
theorem puncturedFundamentalGroupMulEquiv_puncturedCircleLoop_one (k : Fin g) :
    puncturedFundamentalGroupMulEquiv g n (FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (puncturedCircleLoop g n k 1))) =
        SurfaceGroup.Orientable.b g n k :=
  (exists_puncturedFundamentalGroupMulEquiv g n).choose_spec.2.1 k

@[simp]
theorem puncturedFundamentalGroupMulEquiv_peripheralLoop (i : Fin n) :
    puncturedFundamentalGroupMulEquiv g n (FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (peripheralLoop g n i))) =
        SurfaceGroup.Orientable.peripheral g n i :=
  (exists_puncturedFundamentalGroupMulEquiv g n).choose_spec.2.2 i

@[simp]
theorem puncturedFundamentalGroupMulEquiv_symm_a (k : Fin g) :
    (puncturedFundamentalGroupMulEquiv g n).symm (SurfaceGroup.Orientable.a g n k) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (puncturedCircleLoop g n k 0)) := by
  rw [MulEquiv.symm_apply_eq, puncturedFundamentalGroupMulEquiv_puncturedCircleLoop_zero]

@[simp]
theorem puncturedFundamentalGroupMulEquiv_symm_b (k : Fin g) :
    (puncturedFundamentalGroupMulEquiv g n).symm (SurfaceGroup.Orientable.b g n k) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (puncturedCircleLoop g n k 1)) := by
  rw [MulEquiv.symm_apply_eq, puncturedFundamentalGroupMulEquiv_puncturedCircleLoop_one]

@[simp]
theorem puncturedFundamentalGroupMulEquiv_symm_peripheral (i : Fin n) :
    (puncturedFundamentalGroupMulEquiv g n).symm (SurfaceGroup.Orientable.peripheral g n i) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (peripheralLoop g n i)) := by
  rw [MulEquiv.symm_apply_eq, puncturedFundamentalGroupMulEquiv_peripheralLoop]

/-- The classes of the standard circles and of the peripheral loops generate the fundamental group
of `puncture g n`: two homomorphisms out of it that agree on them are equal. -/
@[ext]
theorem puncturedFundamentalGroup_hom_ext {G : Type*} [Group G]
    {f f' : FundamentalGroup (puncture g n) ⟨basePoint g, basePoint_mem_puncture⟩ →* G}
    (ha : ∀ k : Fin g, f (FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (puncturedCircleLoop g n k 0))) =
        f' (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (puncturedCircleLoop g n k 0))))
    (hb : ∀ k : Fin g, f (FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (puncturedCircleLoop g n k 1))) =
        f' (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (puncturedCircleLoop g n k 1))))
    (hp : ∀ i : Fin n, f (FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (peripheralLoop g n i))) =
        f' (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (peripheralLoop g n i)))) :
    f = f' := by
  have h : f.comp (puncturedFundamentalGroupMulEquiv g n).symm.toMonoidHom =
      f'.comp (puncturedFundamentalGroupMulEquiv g n).symm.toMonoidHom :=
    SurfaceGroup.Orientable.hom_ext (by simpa using ha) (by simpa using hb) (by simpa using hp)
  ext x
  simpa using DFunLike.congr_fun h (puncturedFundamentalGroupMulEquiv g n x)

/-- An isomorphism of the fundamental group of `puncture g n` with `Orientable g n` sending the
standard circles to `a` and `b` and the peripheral loops to the peripheral generators is
`ClosedSurface.puncturedFundamentalGroupMulEquiv g n`. -/
theorem eq_puncturedFundamentalGroupMulEquiv
    {e : FundamentalGroup (puncture g n) ⟨basePoint g, basePoint_mem_puncture⟩ ≃*
      SurfaceGroup.Orientable g n}
    (ha : ∀ k : Fin g, e (FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (puncturedCircleLoop g n k 0))) =
        SurfaceGroup.Orientable.a g n k)
    (hb : ∀ k : Fin g, e (FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (puncturedCircleLoop g n k 1))) =
        SurfaceGroup.Orientable.b g n k)
    (hp : ∀ i : Fin n, e (FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (peripheralLoop g n i))) =
        SurfaceGroup.Orientable.peripheral g n i) :
    e = puncturedFundamentalGroupMulEquiv g n :=
  MulEquiv.toMonoidHom_injective <| puncturedFundamentalGroup_hom_ext
    (fun k ↦ by simpa using ha k) (fun k ↦ by simpa using hb k) (fun i ↦ by simpa using hp i)

/-! ### The closed surface -/

variable (g) in
/-- The inclusion of `puncture g 0`, which is the whole surface (`ClosedSurface.puncture_zero`),
read on fundamental groups at the base point. -/
private def punctureZeroMulEquiv :
    FundamentalGroup (puncture g 0) ⟨basePoint g, basePoint_mem_puncture⟩ ≃*
      FundamentalGroup (ClosedSurface g) (basePoint g) :=
  FundamentalGroup.homeomorphMulEquivOfEq
    (Diffeomorph.ofTop (I := 𝓡 2) (n := 0) _ (puncture_zero g)).toHomeomorph
    (by simp)

variable (g) in
/-- The isomorphism of the fundamental group of the closed surface of genus `g`, at its base
point, with the surface group `Orientable g 0`, sending the standard circles `circleLoop g k 0`
and `circleLoop g k 1` of the torus summand `k` to the generators `a k` and `b k`
(`ClosedSurface.fundamentalGroupMulEquiv_circleLoop_zero`,
`ClosedSurface.fundamentalGroupMulEquiv_circleLoop_one`). It is
`ClosedSurface.puncturedFundamentalGroupMulEquiv g 0`, read along `puncture g 0 = ⊤`. -/
def fundamentalGroupMulEquiv :
    FundamentalGroup (ClosedSurface g) (basePoint g) ≃* SurfaceGroup.Orientable g 0 :=
  (punctureZeroMulEquiv g).symm.trans (puncturedFundamentalGroupMulEquiv g 0)

private theorem fundamentalGroupMulEquiv_circleLoop (k : Fin g) (i : Fin 2) :
    fundamentalGroupMulEquiv g (FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (circleLoop g k i))) =
        puncturedFundamentalGroupMulEquiv g 0 (FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk (puncturedCircleLoop g 0 k i))) := by
  rw [fundamentalGroupMulEquiv, MulEquiv.trans_apply]
  congr 1
  rw [MulEquiv.symm_apply_eq, punctureZeroMulEquiv,
    FundamentalGroup.homeomorphMulEquivOfEq_fromPath_mk]
  congr 2
  ext t
  rw [Path.cast_coe, Path.map_coe, Function.comp_apply]
  simp

/-- The isomorphism `ClosedSurface.fundamentalGroupMulEquiv g` sends the class of the standard
circle `circleLoop g k 0` to the generator `a k`. -/
@[simp]
theorem fundamentalGroupMulEquiv_circleLoop_zero (k : Fin g) :
    fundamentalGroupMulEquiv g (FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (circleLoop g k 0))) = SurfaceGroup.Orientable.a g 0 k := by
  rw [fundamentalGroupMulEquiv_circleLoop,
    puncturedFundamentalGroupMulEquiv_puncturedCircleLoop_zero]

/-- The isomorphism `ClosedSurface.fundamentalGroupMulEquiv g` sends the class of the standard
circle `circleLoop g k 1` to the generator `b k`. -/
@[simp]
theorem fundamentalGroupMulEquiv_circleLoop_one (k : Fin g) :
    fundamentalGroupMulEquiv g (FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (circleLoop g k 1))) = SurfaceGroup.Orientable.b g 0 k := by
  rw [fundamentalGroupMulEquiv_circleLoop,
    puncturedFundamentalGroupMulEquiv_puncturedCircleLoop_one]

@[simp]
theorem fundamentalGroupMulEquiv_symm_a (k : Fin g) :
    (fundamentalGroupMulEquiv g).symm (SurfaceGroup.Orientable.a g 0 k) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (circleLoop g k 0)) := by
  rw [MulEquiv.symm_apply_eq, fundamentalGroupMulEquiv_circleLoop_zero]

@[simp]
theorem fundamentalGroupMulEquiv_symm_b (k : Fin g) :
    (fundamentalGroupMulEquiv g).symm (SurfaceGroup.Orientable.b g 0 k) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (circleLoop g k 1)) := by
  rw [MulEquiv.symm_apply_eq, fundamentalGroupMulEquiv_circleLoop_one]

end SymplecticGeometry.ClosedSurface

end
