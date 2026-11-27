/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.Basic
public import TauCeti.Geometry.Symplectic.Lagrangian.SymplecticTangent
public import TauCeti.Geometry.Symplectic.Manifold.Prod
public import TauCeti.Geometry.Symplectic.Manifold.Torus.Basic
import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.Graph
import SymplecticGeometry.Geometry.Symplectic.Manifold.Prod
import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.Quotient
import TauCeti.Geometry.Manifold.VectorBundle.Pullback

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

A tangent vector `v` of `Σ` at `h (x i)` gives the horizontal vector `(v, 0)` of `Σ × T` at
`(h (x i), x)`, and so a normal class of the graph torus at `x`. For a family of vectors `v` that
depends smoothly on `x` and on a parameter, these classes form a smooth map into the normal bundle,
since the vectors `(v, 0)` form a smooth map into the pulled-back tangent bundle of `Σ × T` and
taking normal classes is smooth (`TauCeti.SmoothEmbedding.contMDiff_normalQuotientMap`).

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
* `SymplecticGeometry.contMDiff_normalClass_graphTorus_horizontal`: the normal classes of a smooth
  family of horizontal vectors `(v, 0)` form a smooth map into the normal bundle of the graph torus.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  Theorem 7.2.8.
* [R. E. Gompf, *A new construction of symplectic manifolds*][Gompf1995].
-/

public section

noncomputable section

open Set Function TauCeti Bundle Module
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
section NormalClass

variable {F H' Z : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
  {K : ModelWithCorners ℝ F H'} [TopologicalSpace Z] [ChartedSpace H' Z]
  {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- **Horizontal normal classes of a graph torus are smooth.** Let `(x, z) ↦ u x z` be a family of
tangent vectors `u x z ∈ T_{h (x i)} M`, parametrized by a point `x` of the torus and a point `z` of
a manifold `Z`, that is smooth as a map into the tangent bundle of `M`. Then the normal classes
`(x, z) ↦ [(u x z, 0)] ∈ N_x` of the horizontal vectors `(u x z, 0)` at `(h (x i), x)` form a
smooth map into the normal bundle of the graph torus. -/
theorem contMDiff_normalClass_graphTorus_horizontal (hh : ContMDiff 𝓘(ℝ) I ∞ h)
    (hP : finrank ℝ P = finrank ℝ (E × (ι ⊕ ι → ℝ)) - finrank ℝ (ι ⊕ ι → ℝ))
    {u : ∀ x : ∀ i, AddCircle (p i), Z → TangentSpace I (h (x i))}
    (hu : ContMDiff ((ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ)).prod K) I.tangent ∞
      fun y : (∀ i, AddCircle (p i)) × Z ↦ (⟨h (y.1 i), u y.1 y.2⟩ : TangentBundle I M)) :
    letI := (graphTorus hh).normalSpaceFiberBundle (WithTop.coe_ne_zero.2 ENat.top_ne_zero) hP
    ContMDiff ((ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ)).prod K)
      ((ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, P)) ∞
      fun y : (∀ i, AddCircle (p i)) × Z ↦ (⟨y.1, (graphTorus hh).isImmersion.normalClass y.1
          (WithTop.coe_ne_zero.2 ENat.top_ne_zero) (u y.1 y.2, 0)⟩ :
        TotalSpace P fun x ↦ (graphTorus hh).isImmersion.NormalSpace x
          (WithTop.coe_ne_zero.2 ENat.top_ne_zero)) := by
  let f := graphTorus hh
  let := f.normalSpaceFiberBundle (WithTop.coe_ne_zero.2 ENat.top_ne_zero) hP
  -- The ambient vectors `(u x z, 0)` along the graph torus form a smooth map into the pulled-back
  -- tangent bundle, and taking normal classes is smooth.
  have hg : ContMDiff ((ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ)).prod K)
      ((ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, E × (ι ⊕ ι → ℝ))) ∞
      fun y : (∀ i, AddCircle (p i)) × Z ↦ (⟨y.1, ((u y.1 y.2 : E), (0 : ι ⊕ ι → ℝ))⟩ :
        TotalSpace (E × (ι ⊕ ι → ℝ)) ((f : _ → M × ∀ i, AddCircle (p i)) *ᵖ
          (TangentSpace (I.prod (ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ)))))) := by
    refine (Pullback.contMDiff_iff f f.contMDiff).2 ⟨contMDiff_fst, ?_⟩
    refine (contMDiff_equivTangentBundleProd_symm.comp
      (hu.prodMk ((contMDiff_zeroSection ℝ (TangentSpace _)).comp contMDiff_fst))).congr
      fun y ↦ ?_
    -- The base points agree by `graphTorus_apply`; the fibres agree as the zero vector of a
    -- tangent space is the zero of its model space.
    exact TotalSpace.ext (by simp [Pullback.lift, f]) HEq.rfl
  exact ((f.contMDiff_normalQuotientMap (m := ∞) _ le_rfl hP).comp hg).congr fun y ↦ by
    rw [comp_apply, SmoothEmbedding.normalQuotientMap_apply]

end NormalClass

end SymplecticGeometry
