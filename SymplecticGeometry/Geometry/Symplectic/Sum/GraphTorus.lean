/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import TauCeti.AlgebraicTopology.FundamentalGroup.Product
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
public import TauCeti.Geometry.Symplectic.Lagrangian.SymplecticTangent
public import TauCeti.Geometry.Symplectic.Manifold.Prod
public import TauCeti.Geometry.Symplectic.Manifold.Torus.Basic
public import TauCeti.Topology.Homotopy.AddCircle
public import TauCeti.Topology.Instances.AddCircle.Torus
import SymplecticGeometry.AlgebraicTopology.FundamentalGroup.Basic
import SymplecticGeometry.AlgebraicTopology.FundamentalGroup.Prod.Basic
import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.Graph
import SymplecticGeometry.Geometry.Symplectic.Manifold.Prod
import TauCeti.AlgebraicTopology.FundamentalGroup.Basic

/-!
# Graph tori of circle maps

Let `Σ` be a finite-dimensional boundaryless manifold, let `T = ∀ i : ι ⊕ ι, AddCircle (p i)` be
the standard torus, let `i : ι ⊕ ι` be one of its coordinates and let `h : AddCircle (p i) → Σ` be
smooth. The **graph torus** of `h` is the map

`T → Σ × T`, `x ↦ (h (x i), x)`,

the graph of `h ∘ eval i` with its factors exchanged
(`SymplecticGeometry.graphTorus`). It is a smooth embedding by
`ContMDiff.isSmoothEmbedding_graph_swap`.

For a two-form `σ` on `Σ`, the graph torus pulls the product form `pr₁^* σ + pr₂^* ω_T` of
`Σ × T` back to exactly the standard form `ω_T = TauCeti.torusSymplecticForm p`: its second
component is the identity, and its first factors through the circle `AddCircle (p i)`, which has
dimension one, so it pulls every two-form back to zero
(`TauCeti.SmoothForm.eq_zero_of_finrank_lt`). In particular, for a nondegenerate `σ`, the graph
torus has symplectic tangent images for the product form.

The graph tori of `h` and `h'` have disjoint images exactly when `h t ≠ h' t` for every `t`,
since a point of `T` determines its coordinate `t = x i`.

On fundamental groups based at `0`, the graph torus sends the class of the straight loop
`TauCeti.torusLoop p (Pi.single j 1)` around the `j`-th circle, the `j`-th generator of `π₁(T, 0)`
by `AddCircle.piFundamentalGroupMulEquivZero_torusLoop`, to an element of
`π₁(Σ × T, (h 0, 0)) ≃* π₁(Σ, h 0) × π₁(T, 0)` (`FundamentalGroup.prodMulEquiv`) whose second
component is that generator again, since the second component of the graph torus is the identity.
Its first component is the class of the loop `t ↦ h t`, read at `h 0` by
`ContinuousMap.toLoop`, for `j = i`, and trivial for `j ≠ i`, where the first component of the
loop is constant.

These tori enter the realization of finitely presented groups as fundamental groups of closed
symplectic four-manifolds: the torus of a loop `h` in a surface `Σ` lies in `Σ × T²` and is
symplectic for the product form.

## Main definitions

* `SymplecticGeometry.graphTorus`: the graph torus `x ↦ (h (x i), x)` of a smooth circle map `h`,
  as a smooth embedding.

## Main results

* `SymplecticGeometry.mpullback_graphTorus_prod_torusSymplecticForm`: the graph torus pulls
  `pr₁^* σ + pr₂^* ω_T` back to `ω_T`.
* `SymplecticGeometry.hasSymplecticTangentImages_graphTorus`: it has symplectic tangent images for
  the product form.
* `SymplecticGeometry.disjoint_range_graphTorus_iff`: two graph tori are disjoint exactly when the
  circle maps differ at every point.
* `SymplecticGeometry.fst_prodMulEquiv_mapOfEq_graphTorus`,
  `SymplecticGeometry.snd_prodMulEquiv_mapOfEq_graphTorus`: the two components of the image of a
  class of `π₁(T, 0)`, the image of its `i`-th coordinate under `h` and the class itself.
* `SymplecticGeometry.prodMulEquiv_mapOfEq_graphTorus_torusLoop_single_self`,
  `SymplecticGeometry.prodMulEquiv_mapOfEq_graphTorus_torusLoop_single_of_ne`: the images of the
  generators of `π₁(T, 0)` in `π₁(Σ, h 0) × π₁(T, 0)`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  Theorem 7.2.8.
* [R. E. Gompf, *A new construction of symplectic manifolds*][Gompf1995].
-/

public section

noncomputable section

open Set Function TauCeti
open scoped Manifold ContDiff

namespace SymplecticGeometry

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [FiniteDimensional ℝ E] {I : ModelWithCorners ℝ E H} [I.Boundaryless] {M : Type*}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {ι : Type*} [Fintype ι] {p : ι ⊕ ι → ℝ} [∀ i, Fact (0 < p i)] {i : ι ⊕ ι}
  {h h' : AddCircle (p i) → M}

/-- The **graph torus** of a smooth map `h : AddCircle (p i) → M`: the smooth embedding
`x ↦ (h (x i), x)` of the torus `∀ i, AddCircle (p i)` into `M × ∀ i, AddCircle (p i)`. -/
def graphTorus (hh : ContMDiff 𝓘(ℝ) I ∞ h) :
    SmoothEmbedding (ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ))
      (I.prod (ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ))) ∞ (∀ i, AddCircle (p i))
      (M × ∀ i, AddCircle (p i)) :=
  .ofIsSmoothEmbedding _
    ((hh.comp (contMDiff_apply (i := i))).isSmoothEmbedding_graph_swap (by simp))

/-- The graph torus of `h` sends `x` to `(h (x i), x)`. -/
@[simp]
theorem graphTorus_apply (hh : ContMDiff 𝓘(ℝ) I ∞ h) (x : ∀ i, AddCircle (p i)) :
    graphTorus hh x = (h (x i), x) :=
  SmoothEmbedding.ofIsSmoothEmbedding_apply _ _ x

/-- The graph torus of `h` sends the base point `0` of the torus to `(h 0, 0)`. -/
theorem graphTorus_zero (hh : ContMDiff 𝓘(ℝ) I ∞ h) : graphTorus hh 0 = (h 0, 0) := by simp

/-- The graph torus of `h` is the map `x ↦ (h (x i), x)`. -/
theorem coe_graphTorus (hh : ContMDiff 𝓘(ℝ) I ∞ h) :
    ⇑(graphTorus hh) = fun x : ∀ i, AddCircle (p i) ↦ (h (x i), x) :=
  funext (graphTorus_apply hh)

/-- The first component of the graph torus of `h` is `h` after the coordinate `x ↦ x i`. -/
theorem fst_comp_graphTorus (hh : ContMDiff 𝓘(ℝ) I ∞ h) :
    Prod.fst ∘ graphTorus hh = h ∘ fun x : ∀ i, AddCircle (p i) ↦ x i :=
  funext fun x ↦ by simp

/-- The second component of the graph torus is the identity of the torus. -/
theorem snd_comp_graphTorus (hh : ContMDiff 𝓘(ℝ) I ∞ h) :
    Prod.snd ∘ graphTorus hh = id :=
  funext fun x ↦ by simp

/-- The range of the graph torus of `h` is the set of pairs `(h (x i), x)`. -/
theorem mem_range_graphTorus_iff (hh : ContMDiff 𝓘(ℝ) I ∞ h) {y : M × ∀ i, AddCircle (p i)} :
    y ∈ range (graphTorus hh) ↔ y.1 = h (y.2 i) := by
  simp only [mem_range, graphTorus_apply]
  exact ⟨fun ⟨x, hx⟩ ↦ hx ▸ rfl, fun hy ↦ ⟨y.2, Prod.ext hy.symm rfl⟩⟩

/-- The graph tori of `h` and `h'` are disjoint exactly when `h t ≠ h' t` for every `t`. -/
theorem disjoint_range_graphTorus_iff (hh : ContMDiff 𝓘(ℝ) I ∞ h)
    (hh' : ContMDiff 𝓘(ℝ) I ∞ h') :
    Disjoint (range (graphTorus hh)) (range (graphTorus hh')) ↔ ∀ t, h t ≠ h' t := by
  classical
  rw [Set.disjoint_left]
  refine ⟨fun hd t ht ↦ ?_, fun hne y hy hy' ↦ ?_⟩
  · -- A point of the torus with coordinate `t` at `i` gives a common point of the two tori.
    let x : ∀ j, AddCircle (p j) := Function.update 0 i t
    exact hd (mem_range_self x) ((mem_range_graphTorus_iff hh').2 (by simp [x, ht]))
  · rw [mem_range_graphTorus_iff] at hy hy'
    exact hne _ (hy.symm.trans hy')

/-- The graph torus pulls the product form `pr₁^* σ + pr₂^* ω_T` of `M × T` back to the standard
symplectic form `ω_T` of the torus `T`, whatever the two-form `σ` on `M`. -/
theorem mpullback_graphTorus_prod_torusSymplecticForm (hh : ContMDiff 𝓘(ℝ) I ∞ h)
    (σ : SmoothTwoForm I M) :
    SmoothForm.mpullback (graphTorus hh) (graphTorus hh).contMDiff
        (SmoothTwoForm.prod σ (torusSymplecticForm p)) =
      torusSymplecticForm p := by
  -- The first component factors through the circle, where every two-form vanishes, and the
  -- second is the identity.
  rw [SmoothTwoForm.mpullback_prod,
    SmoothForm.mpullback_congr _ (hh.comp contMDiff_apply) (fst_comp_graphTorus hh),
    ← SmoothForm.mpullback_mpullback _ _ contMDiff_apply hh,
    SmoothForm.eq_zero_of_finrank_lt (by simp) (SmoothForm.mpullback h hh σ), map_zero, zero_add,
    SmoothForm.mpullback_congr _ contMDiff_id (snd_comp_graphTorus hh)]
  exact LinearMap.congr_fun SmoothForm.mpullback_id _

/-- For a nondegenerate two-form `σ` on `M`, the graph torus has symplectic tangent images for the
product form `pr₁^* σ + pr₂^* ω_T`. -/
theorem hasSymplecticTangentImages_graphTorus {σ : SmoothTwoForm I M} (hσ : σ.IsNondegenerate)
    (hh : ContMDiff 𝓘(ℝ) I ∞ h) :
    (hσ.prod (isSymplectic_torusSymplecticForm p).isNondegenerate).HasSymplecticTangentImages
      (ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ)) (graphTorus hh) := by
  have hpull := (SmoothTwoForm.IsNondegenerate.isNondegenerate_mpullback_iff
    (hσ := hσ.prod (isSymplectic_torusSymplecticForm p).isNondegenerate)
    (graphTorus hh).contMDiff).1
  rw [mpullback_graphTorus_prod_torusSymplecticForm] at hpull
  exact (hpull (isSymplectic_torusSymplecticForm p).isNondegenerate).1

/-! ### Fundamental groups -/

/-- On fundamental groups based at `0`, the first component of the image of a loop class under
the graph torus of `h` is the image under `h` of its `i`-th coordinate. -/
theorem fst_prodMulEquiv_mapOfEq_graphTorus (hh : ContMDiff 𝓘(ℝ) I ∞ h)
    (γ : FundamentalGroup (∀ i, AddCircle (p i)) 0) :
    (FundamentalGroup.prodMulEquiv (h 0) 0
      (FundamentalGroup.mapOfEq (graphTorus hh).toContinuousMap (graphTorus_zero hh) γ)).1 =
      FundamentalGroup.mapOfEq (⟨h, hh.continuous⟩ : C(AddCircle (p i), M)) rfl
        (FundamentalGroup.mapOfEq (ContinuousMap.eval i) rfl γ) := by
  have hc : (⟨h, hh.continuous⟩ : C(AddCircle (p i), M)).comp (ContinuousMap.eval i) =
      ContinuousMap.fst.comp (graphTorus hh).toContinuousMap :=
    ContinuousMap.ext fun x ↦ by simp
  rw [FundamentalGroup.prodMulEquiv_mapOfEq]
  exact (FundamentalGroup.mapOfEq_mapOfEq_eq_mapOfEq hc rfl rfl _ γ).symm

/-- On fundamental groups based at `0`, the torus component of the image of a loop class under the
graph torus is that class again: the second component of the graph torus is the identity. -/
theorem snd_prodMulEquiv_mapOfEq_graphTorus (hh : ContMDiff 𝓘(ℝ) I ∞ h)
    (γ : FundamentalGroup (∀ i, AddCircle (p i)) 0) :
    (FundamentalGroup.prodMulEquiv (h 0) 0
      (FundamentalGroup.mapOfEq (graphTorus hh).toContinuousMap (graphTorus_zero hh) γ)).2 = γ := by
  have hc : ContinuousMap.snd.comp (graphTorus hh).toContinuousMap = ContinuousMap.id _ :=
    ContinuousMap.ext fun x ↦ by simp
  rw [FundamentalGroup.prodMulEquiv_mapOfEq]
  exact (FundamentalGroup.mapOfEq_congr hc _ rfl γ).trans (FundamentalGroup.mapOfEq_id rfl γ)

/-- The graph torus of `h : AddCircle (p i) → M` sends the class of the straight loop
`torusLoop p (Pi.single i 1)` around the `i`-th circle of the torus to the class of the loop
`(t ↦ h t, torusLoop p (Pi.single i 1))` in `π₁(M × T, (h 0, 0)) ≃* π₁(M, h 0) × π₁(T, 0)`, its
first component being the circle map `h` read as a loop at `h 0` by `ContinuousMap.toLoop`. -/
theorem prodMulEquiv_mapOfEq_graphTorus_torusLoop_single_self [DecidableEq (ι ⊕ ι)]
    (hh : ContMDiff 𝓘(ℝ) I ∞ h) :
    FundamentalGroup.prodMulEquiv (h 0) 0
        (FundamentalGroup.mapOfEq (graphTorus hh).toContinuousMap (graphTorus_zero hh)
          (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (torusLoop p (Pi.single i 1))))) =
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
          (⟨h, hh.continuous⟩ : C(AddCircle (p i), M)).toLoop),
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (torusLoop p (Pi.single i 1)))) := by
  refine Prod.ext ?_ (snd_prodMulEquiv_mapOfEq_graphTorus hh _)
  rw [fst_prodMulEquiv_mapOfEq_graphTorus, FundamentalGroup.mapOfEq_rfl,
    FundamentalGroup.mapOfEq_rfl, FundamentalGroup.map_fromPath, FundamentalGroup.map_fromPath]
  refine congrArg _ (congrArg _ (Path.ext (funext fun t ↦ ?_)))
  -- Neither `simp` nor `rw` can use `ContinuousMap.toLoop_apply` here: the goal reads `toLoop`
  -- as a path from `h (ContinuousMap.eval i 0)`, the lemma as one from `h 0`, and these endpoints
  -- agree only up to unfolding `ContinuousMap.eval`. So the lemma is applied by unification.
  refine Eq.trans ?_ (ContinuousMap.toLoop_apply _ t).symm
  simp

/-- For `j ≠ i`, the graph torus of `h : AddCircle (p i) → M` sends the class of the straight loop
`torusLoop p (Pi.single j 1)` around the `j`-th circle of the torus to the class of the loop
`(h 0, torusLoop p (Pi.single j 1))` in `π₁(M × T, (h 0, 0)) ≃* π₁(M, h 0) × π₁(T, 0)`, whose
first component is trivial. -/
theorem prodMulEquiv_mapOfEq_graphTorus_torusLoop_single_of_ne [DecidableEq (ι ⊕ ι)]
    (hh : ContMDiff 𝓘(ℝ) I ∞ h) {j : ι ⊕ ι} (hj : j ≠ i) :
    FundamentalGroup.prodMulEquiv (h 0) 0
        (FundamentalGroup.mapOfEq (graphTorus hh).toContinuousMap (graphTorus_zero hh)
          (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (torusLoop p (Pi.single j 1))))) =
      (1, FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (torusLoop p (Pi.single j 1)))) := by
  refine Prod.ext ?_ (snd_prodMulEquiv_mapOfEq_graphTorus hh _)
  -- The `i`-th coordinate of the loop is constant, so its class is trivial in `π₁(AddCircle, 0)`.
  have h₁ : FundamentalGroup.mapOfEq (ContinuousMap.eval i) rfl
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (torusLoop p (Pi.single j 1)))) = 1 :=
    have hq : (torusLoop p (Pi.single j 1)).map (ContinuousMap.eval i).continuous =
        Path.refl _ :=
      Path.ext (funext fun t ↦ by simp [hj.symm])
    (FundamentalGroup.mapOfEq_fromPath_eq_one_iff _ _ _).2 (hq ▸ Path.Homotopic.refl _)
  rw [fst_prodMulEquiv_mapOfEq_graphTorus, h₁, map_one]
  rfl

end SymplecticGeometry
