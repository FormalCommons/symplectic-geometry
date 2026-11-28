/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Topology.Instances.AddCircle.Real
public import SymplecticGeometry.Geometry.Manifold.ModelTransport.ModelPi
public import SymplecticGeometry.Geometry.Manifold.ModelTransport.Remodel
public import TauCeti.Geometry.Manifold.Instances.AddCircle
public import TauCeti.Geometry.Manifold.ConnectedSum.Prime
public import TauCeti.Geometry.Manifold.ConnectedSum.Topology
import SymplecticGeometry.Geometry.Manifold.ConnectedSum.Range
import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.UnivBall
import TauCeti.Analysis.Normed.Module.Ball
import TauCeti.Analysis.Normed.Module.Ball.Homeomorph
import TauCeti.Geometry.Manifold.Instances.AddCircle.Torus
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Diffeomorph
import TauCeti.Geometry.Sphere.Connected
import TauCeti.AlgebraicTopology.Sphere.SimplyConnected
import SymplecticGeometry.Analysis.Normed.Module.Ball.Homeomorph

/-!
# Closed surfaces of genus `g`

The closed surface of genus `g` is the connected sum of `g` copies of the torus `T²`.
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

The closed surface `SymplecticGeometry.ClosedSurface g` is built by recursion on `g`, as
`SymplecticGeometry.closedSurfaceData g`: a surface together with a sequence of coordinate balls
with pairwise disjoint ranges, a base point outside them, and the punctured torus summands. For
`g = 0` it is the unit sphere `S²` in `EuclideanSpace ℝ (Fin 3)`, with the base point
`v = (1, 0, 0)` and the explicit balls `TauCeti.sphereBall v ∘ univBall (j • e) (1 / 2)`, for
`e = (1, 0)`: Mathlib's `univBall` maps the plane onto the disc of radius `1 / 2` about `j • e`,
these discs are pairwise disjoint (Tau Ceti's `TauCeti.pairwise_disjoint_ball_add_natCast_smul`),
and Tau Ceti's coordinate ball `TauCeti.sphereBall v` is injective with range the complement of
`v`. Since the balls are given, and not chosen, later files can compare their orientations. The
surface of genus `g + 1` is the connected sum of the torus, along its ball,
with the surface of genus `g`, along its ball `0`. The other balls miss the centre of the ball
`0`, so they pass to the sum by Tau Ceti's `TauCeti.ConnectedSum.inrBall`. So do the base point
and the earlier summands, since a point of the surface of genus `g` is glued to the torus only if
it lies in the range of the ball `0`. Thus every torus is summed onto the sphere, each along a
ball of its own. The instances come from Tau Ceti's `TauCeti.ConnectedSum.t2Space`,
`compactSpace`, `connectedSpace`, `chartedSpace` and `isManifold`. Other files see the recursion
through `SymplecticGeometry.ClosedSurface.zeroDiffeomorph` and
`SymplecticGeometry.ClosedSurface.succDiffeomorph`, the identity of the points, and the lemmas that
say where they send the base point, the summands and the balls.

## Main definitions

* `SymplecticGeometry.EuclideanTorus`: the torus `Fin 2 → AddCircle 1`, charted on
  `EuclideanSpace ℝ (Fin 2)`, with base point `0`.
* `SymplecticGeometry.EuclideanTorus.diffeomorph`: the identity, as a smooth diffeomorphism onto
  Tau Ceti's torus `Fin 2 → AddCircle 1`.
* `SymplecticGeometry.EuclideanTorus.ball`: the coordinate ball along which the torus is summed.
* `SymplecticGeometry.ClosedSurface g`: the closed surface of genus `g`, a compact connected
  Hausdorff smooth surface charted on `EuclideanSpace ℝ (Fin 2)`.
* `SymplecticGeometry.ClosedSurface.basePoint`: its base point, on the sphere.
* `SymplecticGeometry.ClosedSurface.summand k`: the inclusion of its `k`-th torus summand,
  punctured at the centre of the ball of the torus.
* `SymplecticGeometry.ClosedSurface.ball j`: its coordinate balls, along which further tori are
  summed.
* `SymplecticGeometry.ClosedSurface.zeroDiffeomorph`: the surface of genus `0` is the sphere.
* `SymplecticGeometry.ClosedSurface.succDiffeomorph`: the surface of genus `g + 1` is the
  connected sum of the torus with the surface of genus `g`, along its ball `0`.

## Main results

* `SymplecticGeometry.EuclideanTorus.isOpenEmbedding_ball`,
  `SymplecticGeometry.EuclideanTorus.isLocalDiffeomorph_ball`: the ball is an open embedding and
  a smooth local diffeomorphism, as Tau Ceti's `TauCeti.ConnectedSum.isManifold` asks.
* `SymplecticGeometry.EuclideanTorus.disjoint_closure_range_ball`: the closure of its range misses
  the circles `{x | x i = 0}` through the base point.
* `SymplecticGeometry.ClosedSurface.isIteratedConnectedSum`: the closed surface of genus `g` is
  the connected sum (`TauCeti.IsIteratedConnectedSum`) of `g` tori.
* `SymplecticGeometry.ClosedSurface.isOpenEmbedding_summand`: each punctured torus summand is an
  open embedding into it.
* `SymplecticGeometry.ClosedSurface.zeroDiffeomorph_ball`: the balls of the surface of genus `0`
  are `TauCeti.sphereBall v ∘ univBall (j • e) (1 / 2)` on the sphere.
* The instance `SimplyConnectedSpace (ClosedSurface 0)`: the surface of genus `0` is simply
  connected, by Tau Ceti's
  `ContinuousMap.HomotopyEquiv.simplyConnectedSpace_of_sphere_euclideanSpace` along
  `zeroDiffeomorph`.

## References

* [A. A. Kosinski, *Differential Manifolds*][Kosinski1993] (connected sums of manifolds).
* [R. E. Gompf, *A new construction of symplectic manifolds*][Gompf1995] (the closed
  surfaces of genus `g` used to realize finitely presented fundamental groups).
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Proposition 1.14 (the simple connectivity of the sphere `S²`).
-/

public section

noncomputable section

open Set Metric Topology OpenPartialHomeomorph TauCeti Function
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
theorem coe_diffeomorph : ⇑diffeomorph = (remodelHomeomorph _ _).symm := by
  rw [diffeomorph_def, coe_remodelDiffeomorph_symm]

/-- Its inverse is the identity of the points of the torus. -/
theorem coe_diffeomorph_symm : ⇑diffeomorph.symm = remodelHomeomorph _ _ :=
  coe_remodelDiffeomorph (EuclideanSpace.modelPiDiffeomorph ℝ (Fin 2) ∞)
    (Fin 2 → AddCircle (1 : ℝ))

/-- The diffeomorphism keeps the base point `0`. -/
@[simp]
theorem diffeomorph_zero : diffeomorph 0 = 0 := by
  rw [coe_diffeomorph, remodelHomeomorph_symm_apply]
  -- `rfl`: the zero of `EuclideanTorus` is that of `Fin 2 → AddCircle 1` (`inferInstanceAs`).
  rfl

/-- Its inverse keeps the base point `0`. -/
@[simp]
theorem diffeomorph_symm_zero : diffeomorph.symm 0 = 0 :=
  (congrArg diffeomorph.symm diffeomorph_zero).symm.trans (diffeomorph.symm_apply_apply 0)

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
    AddCircle.isLocalDiffeomorph_coe_pi (fun _ ↦ 1) ∞ _)

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

/-- The coordinate ball in coordinates: it sends `v` to the point of the torus with coordinates
`[1 / 2 + v i / (4 √(1 + ‖v‖²))]`. -/
theorem diffeomorph_ball_apply (v : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) :
    diffeomorph (ball v) i =
      ((1 / 2 + 1 / 4 * (√(1 + ‖v‖ ^ 2))⁻¹ * v i : ℝ) : AddCircle (1 : ℝ)) := by
  rw [ball_def, Function.comp_apply, univBall_apply (by norm_num), diffeomorph_cover]
  simp only [vadd_eq_add, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, ballCenter_apply]
  congr 1
  ring

/-- The centre of the coordinate ball is the point `([1 / 2], [1 / 2])` of the torus. -/
@[simp]
theorem diffeomorph_ball_zero (i : Fin 2) :
    diffeomorph (ball 0) i = ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) := by
  simp [diffeomorph_ball_apply]

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

/-! ### The closed surfaces -/

/-- The data from which the closed surface of genus `g` is built, one torus at a time: a compact
connected Hausdorff smooth surface `carrier`, modelled on the Euclidean plane, which is the
connected sum of `g` tori; a sequence of coordinate balls of it with pairwise disjoint ranges,
along which further tori are summed; a base point outside all of them; and, for each `k : Fin g`,
the `k`-th torus summand, punctured at the centre of its ball, as an open embedding into
`carrier` whose range misses the base point and the balls. -/
structure ClosedSurfaceData (g : ℕ) where
  /-- The surface. -/
  carrier : Type
  [topologicalSpace : TopologicalSpace carrier]
  [t2Space : T2Space carrier]
  [compactSpace : CompactSpace carrier]
  [connectedSpace : ConnectedSpace carrier]
  [chartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 2)) carrier]
  [isManifold : IsManifold (𝓡 2) ∞ carrier]
  /-- The coordinate balls along which further tori are summed. -/
  ball : ℕ → EuclideanSpace ℝ (Fin 2) → carrier
  isOpenEmbedding_ball (j : ℕ) : IsOpenEmbedding (ball j)
  isLocalDiffeomorph_ball (j : ℕ) : IsLocalDiffeomorph (𝓡 2) (𝓡 2) ∞ (ball j)
  pairwise_disjoint_range_ball : Pairwise (Disjoint on fun j ↦ range (ball j))
  /-- The base point. -/
  basePoint : carrier
  basePoint_notMem_range_ball (j : ℕ) : basePoint ∉ range (ball j)
  /-- The `k`-th punctured torus summand. -/
  summand : Fin g → ConnectedSum.puncture EuclideanTorus.ball → carrier
  isOpenEmbedding_summand (k : Fin g) : IsOpenEmbedding (summand k)
  disjoint_range_summand_ball (k : Fin g) (j : ℕ) : Disjoint (range (summand k)) (range (ball j))
  basePoint_notMem_range_summand (k : Fin g) : basePoint ∉ range (summand k)
  isIteratedConnectedSum :
    IsIteratedConnectedSum 2 (fun _ : Fin g ↦ EuclideanTorus) carrier

namespace ClosedSurfaceData

attribute [local instance] topologicalSpace t2Space compactSpace connectedSpace chartedSpace
  isManifold

/-- The point `(1, 0, 0)` of the unit sphere `S²`. -/
private def spherePoint : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  ⟨EuclideanSpace.single 0 1, by simp⟩

/-- The sphere `S²`, the connected sum of no tori, with its base point `v = (1, 0, 0)` and the
coordinate balls `TauCeti.sphereBall v ∘ OpenPartialHomeomorph.univBall (j • e) (1 / 2)`, for
`e = (1, 0)`. Mathlib's `univBall` maps the plane onto the disc of radius `1 / 2` about `j • e`;
these discs are pairwise disjoint, and Tau Ceti's ball `sphereBall v` is injective with range the
complement of `v`. -/
def sphere : ClosedSurfaceData 0 :=
  haveI := Fact.mk (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 2 + 1))
  { carrier := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
    connectedSpace := connectedSpace_euclideanSphere (by simp)
    ball j := TauCeti.sphereBall spherePoint ∘ univBall (j • EuclideanSpace.single 0 1) (1 / 2)
    isOpenEmbedding_ball _ := (isOpenEmbedding_sphereBall _).comp
      ((univBall _ _).isOpenEmbedding (univBall_source _ _))
    isLocalDiffeomorph_ball _ x :=
      (isLocalDiffeomorph_univBall le_rfl x).comp (hg := isLocalDiffeomorph_sphereBall _ _ _)
    pairwise_disjoint_range_ball i j hij := by
      -- The discs of radius `1 / 2` about the points `j • e` are pairwise disjoint.
      have h := pairwise_disjoint_ball_add_natCast_smul 0
        (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) hij
      simp only [onFun, range_comp, range_univBall _ (by norm_num : (0 : ℝ) < 1 / 2)]
      rw [disjoint_image_iff (isOpenEmbedding_sphereBall _).injective]
      simpa [Nat.cast_smul_eq_nsmul] using h
    basePoint := spherePoint
    basePoint_notMem_range_ball j h := by
      have h' := range_comp_subset_range _ (TauCeti.sphereBall (n := 2) spherePoint) h
      rw [range_sphereBall] at h'
      exact h' rfl
    summand := Fin.elim0
    isOpenEmbedding_summand k := k.elim0
    disjoint_range_summand_ball k := k.elim0
    basePoint_notMem_range_summand k := k.elim0
    isIteratedConnectedSum := (isIteratedConnectedSum_zero_iff _).2 ⟨Diffeomorph.refl _ _ _⟩ }

variable {g : ℕ} (d : ClosedSurfaceData g)

/-- The centre of the ball `0` lies in the range of no other ball. -/
theorem ball_zero_zero_notMem_range_ball (j : ℕ) : d.ball 0 0 ∉ range (d.ball (j + 1)) :=
  disjoint_left.1 (d.pairwise_disjoint_range_ball (i := 0) (j := j + 1) (by omega)) ⟨0, rfl⟩

/-- The summands miss the centre of the ball `0`. -/
theorem summand_mem_puncture (k : Fin g) (x : ConnectedSum.puncture EuclideanTorus.ball) :
    d.summand k x ∈ ConnectedSum.puncture (d.ball 0) :=
  ConnectedSum.mem_puncture.2 fun h ↦
    disjoint_left.1 (d.disjoint_range_summand_ball k 0) ⟨x, rfl⟩ ⟨0, h.symm⟩

/-- The base point misses the centre of the ball `0`. -/
theorem basePoint_mem_puncture : d.basePoint ∈ ConnectedSum.puncture (d.ball 0) :=
  ConnectedSum.mem_puncture.2 fun h ↦ d.basePoint_notMem_range_ball 0 ⟨0, h.symm⟩

/-- The connected sum of the torus, along its ball, with `carrier`, along the ball `0`; the
balls `j + 1` of `carrier` become its balls `j`, and the torus becomes its summand `0`. -/
def succ : ClosedSurfaceData (g + 1) :=
  letI := ConnectedSum.chartedSpace EuclideanTorus.isOpenEmbedding_ball (d.isOpenEmbedding_ball 0)
  { carrier := ConnectedSum EuclideanTorus.ball (d.ball 0)
    chartedSpace := ‹_›
    t2Space := ConnectedSum.t2Space EuclideanTorus.isOpenEmbedding_ball (d.isOpenEmbedding_ball 0)
    compactSpace :=
      ConnectedSum.compactSpace EuclideanTorus.isOpenEmbedding_ball (d.isOpenEmbedding_ball 0)
    connectedSpace := ConnectedSum.connectedSpace (Module.one_lt_rank_of_one_lt_finrank (by simp))
      EuclideanTorus.isOpenEmbedding_ball (d.isOpenEmbedding_ball 0)
    isManifold := ConnectedSum.isManifold EuclideanTorus.isOpenEmbedding_ball
      (d.isOpenEmbedding_ball 0) EuclideanTorus.isLocalDiffeomorph_ball
      (d.isLocalDiffeomorph_ball 0)
    ball j := ConnectedSum.inrBall _ _ (d.ball (j + 1)) (d.ball_zero_zero_notMem_range_ball j)
    isOpenEmbedding_ball j := ConnectedSum.isOpenEmbedding_inrBall
      EuclideanTorus.isOpenEmbedding_ball (d.isOpenEmbedding_ball 0) _
      (d.isOpenEmbedding_ball (j + 1))
    isLocalDiffeomorph_ball j := ConnectedSum.isLocalDiffeomorph_inrBall
      EuclideanTorus.isOpenEmbedding_ball (d.isOpenEmbedding_ball 0)
      EuclideanTorus.isLocalDiffeomorph_ball (d.isLocalDiffeomorph_ball 0) _
      (d.isLocalDiffeomorph_ball (j + 1))
    pairwise_disjoint_range_ball i j hij := by
      simp only [onFun]
      refine disjoint_left.2 ?_
      rintro _ ⟨w, rfl⟩ hw
      rw [ConnectedSum.inrBall_apply,
        ConnectedSum.inr_mem_range_inrBall_iff EuclideanTorus.ball_injective,
        ConnectedSum.coe_punctureBall] at hw
      exact disjoint_left.1 (d.pairwise_disjoint_range_ball (by omega : i + 1 ≠ j + 1))
        ⟨w, rfl⟩ hw
    basePoint := ConnectedSum.inr _ _ ⟨d.basePoint, d.basePoint_mem_puncture⟩
    basePoint_notMem_range_ball j h := d.basePoint_notMem_range_ball (j + 1)
      ((ConnectedSum.inr_mem_range_inrBall_iff EuclideanTorus.ball_injective _).1 h)
    summand := Fin.cases (ConnectedSum.inl _ _)
      fun k x ↦ ConnectedSum.inr _ _ ⟨d.summand k x, d.summand_mem_puncture k x⟩
    isOpenEmbedding_summand k := by
      refine Fin.cases ?_ (fun k ↦ ?_) k
      · exact ConnectedSum.isOpenEmbedding_inl EuclideanTorus.isOpenEmbedding_ball
          (d.isOpenEmbedding_ball 0)
      · exact (ConnectedSum.isOpenEmbedding_inr EuclideanTorus.isOpenEmbedding_ball
          (d.isOpenEmbedding_ball 0)).comp
          ((IsOpenEmbedding.of_comp_iff _
            (ConnectedSum.puncture _).isOpen.isOpenEmbedding_subtypeVal).1
              (d.isOpenEmbedding_summand k))
    disjoint_range_summand_ball k j := by
      refine Fin.cases ?_ (fun k ↦ ?_) k
      · refine disjoint_left.2 ?_
        rintro _ ⟨x, rfl⟩ ⟨w, hw⟩
        rw [Fin.cases_zero, ConnectedSum.inrBall_apply] at hw
        exact disjoint_left.1 (d.pairwise_disjoint_range_ball (Nat.succ_ne_zero j).symm)
          (ConnectedSum.mem_range_right_of_inl_eq_inr EuclideanTorus.ball_injective hw.symm)
          ⟨w, (ConnectedSum.coe_punctureBall _ _).symm⟩
      · refine disjoint_left.2 ?_
        rintro _ ⟨x, rfl⟩ hw
        rw [Fin.cases_succ,
          ConnectedSum.inr_mem_range_inrBall_iff EuclideanTorus.ball_injective] at hw
        exact disjoint_left.1 (d.disjoint_range_summand_ball k (j + 1)) ⟨x, rfl⟩ hw
    basePoint_notMem_range_summand k := by
      refine Fin.cases ?_ (fun k ↦ ?_) k
      · rintro ⟨x, hx⟩
        rw [Fin.cases_zero] at hx
        exact d.basePoint_notMem_range_ball 0
          (ConnectedSum.mem_range_right_of_inl_eq_inr EuclideanTorus.ball_injective hx)
      · rintro ⟨x, hx⟩
        rw [Fin.cases_succ] at hx
        exact d.basePoint_notMem_range_summand k
          ⟨x, congrArg Subtype.val (ConnectedSum.inr_injective EuclideanTorus.ball_injective hx)⟩
    isIteratedConnectedSum := (isIteratedConnectedSum_succ_iff _).2
      ⟨d.carrier, d.topologicalSpace, d.t2Space, d.compactSpace, d.chartedSpace, d.isManifold,
        d.isIteratedConnectedSum,
        isConnectedSumOf_of_diffeomorph EuclideanTorus.isOpenEmbedding_ball
          (d.isOpenEmbedding_ball 0) EuclideanTorus.isLocalDiffeomorph_ball
          (d.isLocalDiffeomorph_ball 0) (Diffeomorph.refl _ _ _)⟩ }

end ClosedSurfaceData

/-- The data of the closed surface of genus `g`: the sphere for `g = 0`, and for `g + 1` the
connected sum of a torus with the surface of genus `g`. -/
def closedSurfaceData : (g : ℕ) → ClosedSurfaceData g
  | 0 => .sphere
  | g + 1 => (closedSurfaceData g).succ

theorem closedSurfaceData_zero : closedSurfaceData 0 = .sphere := (rfl)

theorem closedSurfaceData_succ (g : ℕ) :
    closedSurfaceData (g + 1) = (closedSurfaceData g).succ :=
  (rfl)

/-- The **closed surface of genus `g`**, as the connected sum of `g` tori: the unit
sphere `S²` for `g = 0`, and for `g + 1` the connected sum (`TauCeti.ConnectedSum`) of the torus
`SymplecticGeometry.EuclideanTorus`, along its coordinate ball, with the surface of genus `g`,
along a coordinate ball that misses the tori summed before. -/
abbrev ClosedSurface (g : ℕ) : Type := (closedSurfaceData g).carrier

namespace ClosedSurface

variable (g : ℕ)

instance : TopologicalSpace (ClosedSurface g) := (closedSurfaceData g).topologicalSpace

instance : T2Space (ClosedSurface g) := (closedSurfaceData g).t2Space

instance : CompactSpace (ClosedSurface g) := (closedSurfaceData g).compactSpace

instance : ConnectedSpace (ClosedSurface g) := (closedSurfaceData g).connectedSpace

instance : ChartedSpace (EuclideanSpace ℝ (Fin 2)) (ClosedSurface g) :=
  (closedSurfaceData g).chartedSpace

instance : IsManifold (𝓡 2) ∞ (ClosedSurface g) := (closedSurfaceData g).isManifold

/-- The closed surface of genus `g` is second countable, being compact and charted on the
plane. -/
instance : SecondCountableTopology (ClosedSurface g) :=
  ChartedSpace.secondCountable_of_sigmaCompact (EuclideanSpace ℝ (Fin 2)) _

/-- **The closed surface of genus `g` is the connected sum of `g` tori.** Its summand `0` is the
torus summed last. -/
theorem isIteratedConnectedSum :
    IsIteratedConnectedSum 2 (fun _ : Fin g ↦ EuclideanTorus) (ClosedSurface g) :=
  (closedSurfaceData g).isIteratedConnectedSum

/-- The base point of the closed surface of genus `g`, a point of the sphere onto which the tori
are summed; for `g = 0` it is the point `(1, 0, 0)`
(`ClosedSurface.coe_zeroDiffeomorph_basePoint`). -/
def basePoint : ClosedSurface g := (closedSurfaceData g).basePoint

/-- The `j`-th coordinate ball of the closed surface of genus `g`, along which a further torus can
be summed; the surface of genus `g + 1` is summed along the ball `0`
(`ClosedSurface.succDiffeomorph`). For `g = 0` the balls are explicit
(`ClosedSurface.zeroDiffeomorph_ball`). -/
def ball (j : ℕ) : EuclideanSpace ℝ (Fin 2) → ClosedSurface g := (closedSurfaceData g).ball j

variable {g}

/-- The inclusion of the `k`-th torus summand, punctured at the centre of its coordinate ball,
into the closed surface of genus `g`. Its summand `0` is the torus summed last. -/
def summand (k : Fin g) : ConnectedSum.puncture EuclideanTorus.ball → ClosedSurface g :=
  (closedSurfaceData g).summand k

/-- Each punctured torus summand is an open embedding into the closed surface. -/
theorem isOpenEmbedding_summand (k : Fin g) : IsOpenEmbedding (summand k) :=
  (closedSurfaceData g).isOpenEmbedding_summand k

/-- Each punctured torus summand is continuous. -/
theorem continuous_summand (k : Fin g) : Continuous (summand k) :=
  (isOpenEmbedding_summand k).continuous

/-- The base point lies on no punctured torus summand. -/
theorem basePoint_notMem_range_summand (k : Fin g) : basePoint g ∉ range (summand k) :=
  (closedSurfaceData g).basePoint_notMem_range_summand k

/-- Each coordinate ball is an open embedding. -/
theorem isOpenEmbedding_ball (j : ℕ) : IsOpenEmbedding (ball g j) :=
  (closedSurfaceData g).isOpenEmbedding_ball j

/-- Each coordinate ball is a smooth local diffeomorphism. -/
theorem isLocalDiffeomorph_ball (j : ℕ) : IsLocalDiffeomorph (𝓡 2) (𝓡 2) ∞ (ball g j) :=
  (closedSurfaceData g).isLocalDiffeomorph_ball j

/-- The coordinate balls have pairwise disjoint ranges. -/
theorem pairwise_disjoint_range_ball : Pairwise (Disjoint on fun j ↦ range (ball g j)) :=
  (closedSurfaceData g).pairwise_disjoint_range_ball

/-- Two points of coordinate balls agree exactly when they are the same point of the same
ball. -/
@[simp]
theorem ball_eq_ball_iff {i j : ℕ} {v w : EuclideanSpace ℝ (Fin 2)} :
    ball g i v = ball g j w ↔ i = j ∧ v = w := by
  refine ⟨fun h ↦ ?_, fun ⟨hij, hvw⟩ ↦ hij ▸ hvw ▸ rfl⟩
  obtain rfl : i = j := by_contra fun hij ↦
    disjoint_left.1 (pairwise_disjoint_range_ball hij) ⟨v, rfl⟩ ⟨w, h.symm⟩
  exact ⟨rfl, (isOpenEmbedding_ball i).injective h⟩

/-- The base point lies on no coordinate ball. -/
theorem basePoint_notMem_range_ball (j : ℕ) : basePoint g ∉ range (ball g j) :=
  (closedSurfaceData g).basePoint_notMem_range_ball j

/-- The punctured torus summands miss the coordinate balls. -/
theorem disjoint_range_summand_ball (k : Fin g) (j : ℕ) :
    Disjoint (range (summand k)) (range (ball g j)) :=
  (closedSurfaceData g).disjoint_range_summand_ball k j

/-- No point of a punctured torus summand is the centre of a ball. -/
theorem summand_ne_ball (k : Fin g) (x : ConnectedSum.puncture EuclideanTorus.ball) (j : ℕ) :
    summand k x ≠ ball g j 0 := fun h ↦
  disjoint_left.1 (disjoint_range_summand_ball k j) ⟨x, rfl⟩ ⟨0, h.symm⟩

/-- The centre of the ball `0` lies on no other ball. -/
theorem ball_zero_zero_notMem_range_ball (j : ℕ) : ball g 0 0 ∉ range (ball g (j + 1)) :=
  (closedSurfaceData g).ball_zero_zero_notMem_range_ball j

/-- The base point is not the centre of the ball `0`. -/
theorem basePoint_mem_puncture_ball_zero : basePoint g ∈ ConnectedSum.puncture (ball g 0) :=
  (closedSurfaceData g).basePoint_mem_puncture

/-- The punctured torus summands miss the centre of the ball `0`. -/
theorem summand_mem_puncture_ball_zero (k : Fin g)
    (x : ConnectedSum.puncture EuclideanTorus.ball) :
    summand k x ∈ ConnectedSum.puncture (ball g 0) :=
  (closedSurfaceData g).summand_mem_puncture k x

/-- The closed surface of genus `0` is the unit sphere `S²` of `EuclideanSpace ℝ (Fin 3)`: the
identity of its points, as a smooth diffeomorphism. -/
def zeroDiffeomorph :
    ClosedSurface 0 ≃ₘ^∞⟮𝓡 2, 𝓡 2⟯ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  Diffeomorph.refl _ _ _

/-- The sphere, the closed surface of genus `0`, is simply connected. -/
instance : SimplyConnectedSpace (ClosedSurface 0) :=
  zeroDiffeomorph.toHomeomorph.toHomotopyEquiv.simplyConnectedSpace_of_sphere_euclideanSpace le_rfl

/-- The base point of the closed surface of genus `0` is the point `(1, 0, 0)` of the sphere. -/
@[simp]
theorem coe_zeroDiffeomorph_basePoint :
    (zeroDiffeomorph (basePoint 0) : EuclideanSpace ℝ (Fin 3)) = EuclideanSpace.single 0 1 :=
  (rfl)

/-- The ball `j` of the closed surface of genus `0` is, on the sphere,
`TauCeti.sphereBall v ∘ OpenPartialHomeomorph.univBall (j • e) (1 / 2)`, for its base point
`v = (1, 0, 0)` and `e = (1, 0)`. -/
@[simp]
theorem zeroDiffeomorph_ball (j : ℕ) (w : EuclideanSpace ℝ (Fin 2)) :
    haveI := Fact.mk (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 2 + 1))
    zeroDiffeomorph (ball 0 j w) = TauCeti.sphereBall (zeroDiffeomorph (basePoint 0))
      (univBall (j • EuclideanSpace.single 0 1) (1 / 2) w) :=
  (rfl)

/-- The closed surface of genus `g + 1` is the connected sum of the torus, along its coordinate
ball, with the closed surface of genus `g`, along its ball `0`: the identity of its points, as a
smooth diffeomorphism. -/
def succDiffeomorph :
    letI := ConnectedSum.chartedSpace (H := EuclideanSpace ℝ (Fin 2))
      EuclideanTorus.isOpenEmbedding_ball (isOpenEmbedding_ball (g := g) 0)
    ClosedSurface (g + 1) ≃ₘ^∞⟮𝓡 2, 𝓡 2⟯ ConnectedSum EuclideanTorus.ball (ball g 0) :=
  Diffeomorph.refl _ _ _

/-- The base point of the closed surface of genus `g + 1` is that of genus `g`, in the second
summand. -/
@[simp]
theorem succDiffeomorph_basePoint :
    succDiffeomorph (basePoint (g + 1)) =
      ConnectedSum.inr _ _ ⟨basePoint g, basePoint_mem_puncture_ball_zero⟩ :=
  (rfl)

/-- The summand `0` of the closed surface of genus `g + 1` is the punctured torus, the first
summand of the connected sum. -/
@[simp]
theorem succDiffeomorph_summand_zero (x : ConnectedSum.puncture EuclideanTorus.ball) :
    succDiffeomorph (summand (g := g + 1) 0 x) = ConnectedSum.inl _ (ball g 0) x :=
  (rfl)

/-- The summand `k + 1` of the closed surface of genus `g + 1` is the summand `k` of genus `g`, in
the second summand of the connected sum. -/
@[simp]
theorem succDiffeomorph_summand_succ (k : Fin g) (x : ConnectedSum.puncture EuclideanTorus.ball) :
    succDiffeomorph (summand k.succ x) =
      ConnectedSum.inr _ _ ⟨summand k x, summand_mem_puncture_ball_zero k x⟩ :=
  (rfl)

/-- The ball `j` of the closed surface of genus `g + 1` is the ball `j + 1` of genus `g`, carried
to the connected sum by `TauCeti.ConnectedSum.inrBall`. -/
@[simp]
theorem succDiffeomorph_ball (j : ℕ) (v : EuclideanSpace ℝ (Fin 2)) :
    succDiffeomorph (ball (g + 1) j v) =
      ConnectedSum.inrBall _ _ (ball g (j + 1)) (ball_zero_zero_notMem_range_ball j) v :=
  (rfl)

end ClosedSurface

end SymplecticGeometry

end
