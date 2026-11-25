/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Topology.Instances.AddCircle.Real
public import SymplecticGeometry.Geometry.Manifold.ModelTransport.ModelPi
public import SymplecticGeometry.Geometry.Manifold.ModelTransport.Remodel
public import TauCeti.Geometry.Manifold.Instances.AddCircle
import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.UnivBall
import TauCeti.Geometry.Manifold.Instances.AddCircle.Torus
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Diffeomorph

/-!
# The torus summand of the closed surfaces

The closed oriented surface of genus `g` is the connected sum of `g` copies of the torus `T²`.
Tau Ceti's connected sums `TauCeti.ConnectedSum` glue manifolds modelled on a real inner product
space along coordinate balls, while Tau Ceti's torus `Fin 2 → AddCircle 1` is modelled on
`Fin 2 → ℝ`, whose sup norm comes from no inner product. This file re-models that torus on the
Euclidean plane `EuclideanSpace ℝ (Fin 2)` with `SymplecticGeometry.Remodel`, along
`EuclideanSpace.modelPiDiffeomorph`, and gives it the coordinate ball along which it is summed.

The ball `SymplecticGeometry.EuclideanTorus.ball` is the covering map `t ↦ ([t 0], [t 1])` of the
plane onto the torus, after Mathlib's `OpenPartialHomeomorph.univBall c (1 / 4)` of the plane onto
the disc of radius `1 / 4` about `c = (1 / 2, 1 / 2)`. That disc lies in the open square
`(0, 1)²`, a fundamental domain of `ℤ²`, so the ball is injective, and it is an open embedding
since the covering map is a local homeomorphism. It is a smooth local diffeomorphism since
`univBall` is one (`OpenPartialHomeomorph.isLocalDiffeomorph_univBall`) and so is the covering map
(Tau Ceti's `AddCircle.isLocalDiffeomorph_coe_pi`). The closed disc of radius `1 / 4` about `c`
has both coordinates in `[1 / 4, 3 / 4]`, so the closure of the range of the ball misses the two
circles `{x | x i = 0}` of the torus through its base point `0`.

## Main definitions

* `SymplecticGeometry.EuclideanTorus`: the torus `Fin 2 → AddCircle 1`, charted on
  `EuclideanSpace ℝ (Fin 2)`, with base point `0`.
* `SymplecticGeometry.EuclideanTorus.diffeomorph`: the identity, as a smooth diffeomorphism onto
  Tau Ceti's torus `Fin 2 → AddCircle 1`.
* `SymplecticGeometry.EuclideanTorus.ball`: the coordinate ball along which the torus is summed.

## Main results

* `SymplecticGeometry.EuclideanTorus.isOpenEmbedding_ball`,
  `SymplecticGeometry.EuclideanTorus.isLocalDiffeomorph_ball`: the ball is an open embedding and
  a smooth local diffeomorphism, as Tau Ceti's `TauCeti.ConnectedSum.isManifold` asks.
* `SymplecticGeometry.EuclideanTorus.disjoint_closure_range_ball`: the closure of its range misses
  the circles `{x | x i = 0}` through the base point.

## References

* [A. A. Kosinski, *Differential Manifolds*][Kosinski1993] (connected sums of manifolds).
* [R. E. Gompf, *A new construction of symplectic manifolds*][Gompf1995] (the closed
  surfaces of genus `g` used to realize finitely presented fundamental groups).
-/

public section

noncomputable section

open Set Metric Topology OpenPartialHomeomorph
open scoped Manifold ContDiff

namespace SymplecticGeometry

/-- The **torus** `T² = ℝ² / ℤ²`, as the product `Fin 2 → AddCircle 1` of two circles of
length `1`, charted on the Euclidean plane `EuclideanSpace ℝ (Fin 2)`: its product charts, with
values in `Fin 2 → ℝ`, are followed by `EuclideanSpace.modelPiDiffeomorph`. It has the same points
and topology as Tau Ceti's torus `Fin 2 → AddCircle 1`, and is diffeomorphic to it by the
identity (`SymplecticGeometry.EuclideanTorus.diffeomorph`). -/
abbrev EuclideanTorus : Type :=
  Remodel (EuclideanSpace.modelPiDiffeomorph ℝ (Fin 2) ∞) (Fin 2 → AddCircle (1 : ℝ))

namespace EuclideanTorus

/-- The base point `0` of the torus. -/
instance : Zero EuclideanTorus := inferInstanceAs (Zero (Fin 2 → AddCircle (1 : ℝ)))

/-- The torus, charted on the Euclidean plane, is diffeomorphic to Tau Ceti's torus
`Fin 2 → AddCircle 1`, with its product model, by the identity. -/
def diffeomorph :
    EuclideanTorus ≃ₘ^∞⟮𝓘(ℝ, EuclideanSpace ℝ (Fin 2)),
      ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)⟯
      (Fin 2 → AddCircle (1 : ℝ)) :=
  (remodelDiffeomorph _ _).symm

theorem diffeomorph_def : diffeomorph = (remodelDiffeomorph _ _).symm := (rfl)

/-- The diffeomorphism is the identity of the points of the torus. -/
@[simp]
theorem coe_diffeomorph : ⇑diffeomorph = (remodelHomeomorph _ _).symm := by
  rw [diffeomorph_def, coe_remodelDiffeomorph_symm]

/-- Its inverse is the identity of the points of the torus. -/
@[simp]
theorem coe_diffeomorph_symm : ⇑diffeomorph.symm = remodelHomeomorph _ _ :=
  coe_remodelDiffeomorph (EuclideanSpace.modelPiDiffeomorph ℝ (Fin 2) ∞)
    (Fin 2 → AddCircle (1 : ℝ))

/-- The diffeomorphism keeps the base point `0`. -/
@[simp]
theorem diffeomorph_zero : diffeomorph 0 = 0 := by
  rw [coe_diffeomorph, remodelHomeomorph_symm_apply]
  -- `rfl`: the zero of `EuclideanTorus` is that of `Fin 2 → AddCircle 1` (`inferInstanceAs`).
  rfl

/-- The covering map of the torus by the Euclidean plane, `t ↦ ([t 0], [t 1])`. -/
def cover (t : EuclideanSpace ℝ (Fin 2)) : EuclideanTorus :=
  diffeomorph.symm fun i ↦ (t i : AddCircle (1 : ℝ))

/-- The covering map sends `t` to the point `([t 0], [t 1])` of the torus. -/
@[simp]
theorem diffeomorph_cover (t : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) :
    diffeomorph (cover t) i = (t i : AddCircle (1 : ℝ)) := by
  simp only [cover, Diffeomorph.apply_symm_apply]

/-- The covering map is that of Tau Ceti's torus, `t ↦ ([t i])ᵢ` on `Fin 2 → ℝ`, read through
`EuclideanSpace.equiv` and `diffeomorph`. -/
theorem cover_eq_comp :
    cover = diffeomorph.symm ∘ (fun t : Fin 2 → ℝ ↦ fun i ↦ (t i : AddCircle (1 : ℝ))) ∘
      EuclideanSpace.equiv (Fin 2) ℝ :=
  (rfl)

/-- The covering map is a smooth local diffeomorphism. -/
theorem isLocalDiffeomorph_cover :
    IsLocalDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ cover := by
  rw [cover_eq_comp, Diffeomorph.isLocalDiffeomorph_diffeomorph_comp_iff _ le_rfl]
  exact fun t ↦ ((EuclideanSpace.equiv (Fin 2) ℝ).toDiffeomorph.isLocalDiffeomorph t).comp (hg :=
    AddCircle.isLocalDiffeomorph_coe_pi 1 ∞ _)

/-- The covering map is a local homeomorphism. -/
theorem isLocalHomeomorph_cover : IsLocalHomeomorph cover :=
  isLocalDiffeomorph_cover.isLocalHomeomorph

/-- The centre `(1 / 2, 1 / 2)` of the coordinate ball of the torus. -/
def ballCenter : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 fun _ ↦ 1 / 2

/-- Both coordinates of the centre are `1 / 2`. -/
@[simp]
theorem ballCenter_apply (i : Fin 2) : ballCenter i = 1 / 2 := (rfl)

/-- The **coordinate ball** of the torus along which it is summed: the plane, mapped onto the disc
of radius `1 / 4` about `(1 / 2, 1 / 2)` by Mathlib's `OpenPartialHomeomorph.univBall`, followed
by the covering map. -/
def ball : EuclideanSpace ℝ (Fin 2) → EuclideanTorus :=
  cover ∘ univBall ballCenter (1 / 4)

theorem ball_def : ball = cover ∘ univBall ballCenter (1 / 4) := (rfl)

/-- The centre of the coordinate ball is the point `([1 / 2], [1 / 2])` of the torus. -/
@[simp]
theorem diffeomorph_ball_zero (i : Fin 2) :
    diffeomorph (ball 0) i = ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) := by
  simp [ball_def, univBall_apply_zero]

/-- A point at distance at most `1 / 4` from `(1 / 2, 1 / 2)` has coordinates in
`[1 / 4, 3 / 4]`. -/
private theorem abs_sub_le_of_mem_closedBall {t : EuclideanSpace ℝ (Fin 2)}
    (ht : t ∈ closedBall ballCenter (1 / 4)) (i : Fin 2) : |t i - 1 / 2| ≤ 1 / 4 :=
  calc |t i - 1 / 2| = dist (t i) (ballCenter i) := by rw [Real.dist_eq, ballCenter_apply]
    _ ≤ dist t ballCenter := PiLp.dist_apply_le t ballCenter i
    _ ≤ 1 / 4 := ht

/-- The covering map is injective on the open disc of radius `1 / 4` about `(1 / 2, 1 / 2)`. -/
private theorem injOn_cover : InjOn cover (Metric.ball ballCenter (1 / 4)) := by
  intro s hs t ht hst
  ext i
  have hs' := abs_le.1 (abs_sub_le_of_mem_closedBall (Metric.ball_subset_closedBall hs) i)
  have ht' := abs_le.1 (abs_sub_le_of_mem_closedBall (Metric.ball_subset_closedBall ht) i)
  have h := congrFun (congrArg diffeomorph hst) i
  rw [diffeomorph_cover, diffeomorph_cover] at h
  exact (AddCircle.coe_eq_coe_iff_of_mem_Ico (a := 0) (p := (1 : ℝ))
    ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩).1 h

/-- The coordinate ball of the torus is injective. -/
theorem ball_injective : Function.Injective ball := by
  have hball (x) : univBall ballCenter (1 / 4) x ∈ Metric.ball ballCenter (1 / 4) :=
    (range_univBall ballCenter (by norm_num : (0 : ℝ) < 1 / 4)).subset (mem_range_self x)
  exact fun s t h ↦ ((univBall ballCenter (1 / 4)).isOpenEmbedding (univBall_source _ _)).injective
    (injOn_cover (hball s) (hball t) h)

/-- The coordinate ball of the torus is an open embedding. -/
theorem isOpenEmbedding_ball : IsOpenEmbedding ball :=
  .of_continuous_injective_isOpenMap
    (isLocalHomeomorph_cover.continuous.comp (continuous_univBall _ _)) ball_injective
    (isLocalHomeomorph_cover.isOpenMap.comp
      ((univBall ballCenter (1 / 4)).isOpenEmbedding (univBall_source _ _)).isOpenMap)

/-- The coordinate ball of the torus is a smooth local diffeomorphism. -/
theorem isLocalDiffeomorph_ball :
    IsLocalDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ ball :=
  fun v ↦ (isLocalDiffeomorph_univBall le_rfl v).comp (hg := isLocalDiffeomorph_cover _)

/-- The closure of the range of the coordinate ball misses each circle `{x | x i = 0}` of the
torus through its base point `0`: its points have coordinates in `[1 / 4, 3 / 4]`. -/
theorem disjoint_closure_range_ball (i : Fin 2) :
    Disjoint (closure (range ball)) {x | diffeomorph x i = 0} := by
  have hK : closure (range ball) ⊆ cover '' closedBall ballCenter (1 / 4) := by
    refine closure_minimal ?_ ((isCompact_closedBall _ _).image
      isLocalHomeomorph_cover.continuous).isClosed
    rintro _ ⟨x, rfl⟩
    exact ⟨univBall ballCenter (1 / 4) x, Metric.ball_subset_closedBall
      ((range_univBall ballCenter (by norm_num : (0 : ℝ) < 1 / 4)).subset (mem_range_self x)), rfl⟩
  refine disjoint_left.2 fun x hx hx0 ↦ ?_
  obtain ⟨t, ht, rfl⟩ := hK hx
  have h := abs_le.1 (abs_sub_le_of_mem_closedBall ht i)
  rw [mem_ofPred_eq, diffeomorph_cover] at hx0
  have := (AddCircle.coe_eq_coe_iff_of_mem_Ico (a := 0) (p := (1 : ℝ)) (y := 0)
    ⟨by linarith, by linarith⟩ ⟨le_rfl, by norm_num⟩).1 (by simpa using hx0)
  linarith

end EuclideanTorus

end SymplecticGeometry

end
