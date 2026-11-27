/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Instances.Surface.Puncture
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import SymplecticGeometry.Geometry.Manifold.ConnectedSum.FundamentalGroup
import SymplecticGeometry.Geometry.Manifold.ConnectedSum.Restrict
import SymplecticGeometry.Topology.Maps.Embedding
import TauCeti.AlgebraicTopology.FundamentalGroup.Homeomorph

/-!
# The fundamental groups of the punctured closed surfaces

The closed surface of genus `g + 1` is the connected sum of the torus with the closed surface of
genus `g` along its ball `0` (`ClosedSurface.succDiffeomorph`). This file computes the
fundamental group of `ClosedSurface.puncture (g + 1) n` as a pushout of those of its two pieces:
the punctured torus `TauCeti.ConnectedSum.puncture EuclideanTorus.ball` and
`ClosedSurface.puncture g (n + 1)`, glued along the neck `{0}ᶜ` of the plane.

## Main definitions

* `SymplecticGeometry.ClosedSurface.puncturedSuccInl g n`: the punctured torus in
  `puncture (g + 1) n`, as its summand `0`.
* `SymplecticGeometry.ClosedSurface.puncturedSuccInr g n`: `puncture g (n + 1)` in
  `puncture (g + 1) n`, through the second summand of the connected sum.
* `SymplecticGeometry.ClosedSurface.puncturedNeckInr g n`: the neck `{0}ᶜ` in
  `puncture g (n + 1)`, by `v ↦ ball g 0 (inversion 0 1 v)`, the map
  `TauCeti.ConnectedSum.neckInr` of the ball `0` read in `puncture g (n + 1)`.

## Main results

* `SymplecticGeometry.ClosedSurface.isPushout_fundamentalGroup_puncture_succ`: based at the neck
  point `neckIsometry.circleBasepoint one_pos`, the square of fundamental groups formed by
  `TauCeti.ConnectedSum.neckInl`, `puncturedNeckInr`, `puncturedSuccInl` and `puncturedSuccInr`
  is a pushout in `GrpCat`.
* `SymplecticGeometry.ClosedSurface.map_puncturedNeckInr_circleLoop`: the circle of the neck goes
  to the circle `puncturedBallCircle g (n + 1) 0` of the ball `0`.

## Implementation notes

The square is `TauCeti.ConnectedSum.isPushout_fundamentalGroup` for the connected sum of the
torus with the open set `tailPuncture g n`, along the ball `0` corestricted to it. That sum is
carried onto `puncture (g + 1) n` by `TauCeti.ConnectedSum.restrictRightHomeomorph`, whose target
is `succDiffeomorph '' puncture (g + 1) n` (`ClosedSurface.image_succDiffeomorph_puncture`), and
its punctured second summand onto `puncture g (n + 1)`
(`ClosedSurface.imageVal_puncture_codRestrict_ball`). The transport along these homeomorphisms
by `CategoryTheory.IsPushout.of_iso'` follows the proof of
`TauCeti.ConnectedSum.isPushout_fundamentalGroup`, which transports Tau Ceti's
`TauCeti.isPushout_fundamentalGroup` in the same way.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §1.2 (the Seifert–van Kampen
  theorem).
-/

public section

noncomputable section

open Set Function Topology TopologicalSpace CategoryTheory TauCeti

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

/-- The neck of the connected sum along the ball `0` lies in `puncture g (n + 1)`. -/
theorem coe_neckInr_ball_zero_mem_puncture {g n : ℕ} (v : ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 2)))) :
    (ConnectedSum.neckInr (isOpenEmbedding_ball (g := g) 0) v : ClosedSurface g) ∈
      puncture g (n + 1) := by
  rw [puncture_succ_eq_tailPuncture_inf, Opens.mem_inf]
  refine ⟨?_, (ConnectedSum.neckInr _ v).property⟩
  rw [ConnectedSum.coe_neckInr_apply]
  exact ball_zero_mem_tailPuncture _

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

private theorem mem_puncture_codRestrict_of_mem_puncture_succ {y : ClosedSurface g}
    (hy : y ∈ puncture g (n + 1)) :
    (⟨y, puncture_succ_le_tailPuncture hy⟩ : (tailPuncture g n : Set (ClosedSurface g))) ∈
      ConnectedSum.puncture
        (codRestrict (ball g 0) (tailPuncture g n) ball_zero_mem_tailPuncture) := by
  rw [← imageVal_puncture_codRestrict_ball, Opens.mem_imageVal] at hy
  exact hy.2

private theorem val_val_mem_puncture_succ (z : ConnectedSum.puncture
      (codRestrict (ball g 0) (tailPuncture g n) ball_zero_mem_tailPuncture)) :
    z.val.val ∈ puncture g (n + 1) := by
  rw [← imageVal_puncture_codRestrict_ball]
  exact Opens.coe_mem_imageVal _ z

/-- The punctured second summand of the sum of the torus with `tailPuncture g n` is
`puncture g (n + 1)`. -/
private def puncturedSummandHomeomorph :
    puncture g (n + 1) ≃ₜ ConnectedSum.puncture
      (codRestrict (ball g 0) (tailPuncture g n) ball_zero_mem_tailPuncture) where
  toFun y := ⟨⟨y.val, puncture_succ_le_tailPuncture y.property⟩,
    mem_puncture_codRestrict_of_mem_puncture_succ y.property⟩
  invFun z := ⟨z.val.val, val_val_mem_puncture_succ z⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := ((continuous_subtypeVal).subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtypeVal.comp continuous_subtypeVal).subtype_mk _

@[simp]
private theorem coe_coe_puncturedSummandHomeomorph_apply (y : puncture g (n + 1)) :
    ((puncturedSummandHomeomorph y : (tailPuncture g n : Set (ClosedSurface g))) :
      ClosedSurface g) = y :=
  (rfl)

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

end SymplecticGeometry.ClosedSurface

end
