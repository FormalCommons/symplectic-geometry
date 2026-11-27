/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import SymplecticGeometry.Geometry.Symplectic.Sum.ProductNeighborhood
public import SymplecticGeometry.LinearAlgebra.Complex.Finrank
public import TauCeti.AlgebraicTopology.FundamentalGroup.Product
public import TauCeti.Geometry.Manifold.Immersion.NormalSpace.Basic
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.Basic
public import TauCeti.Geometry.Symplectic.Lagrangian.Embedding.Symplectic.Normal
public import TauCeti.Geometry.Symplectic.Lagrangian.SymplecticTangent
public import TauCeti.Geometry.Symplectic.Manifold.Prod
public import TauCeti.Geometry.Symplectic.Manifold.Torus.Basic
public import TauCeti.Topology.Homotopy.AddCircle
public import TauCeti.Topology.Instances.AddCircle.Torus
import SymplecticGeometry.AlgebraicTopology.FundamentalGroup.Basic
import SymplecticGeometry.AlgebraicTopology.FundamentalGroup.Prod.Basic
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Prod
import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.Graph
import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.FrameAlong
import SymplecticGeometry.Geometry.Symplectic.Manifold.Prod
import TauCeti.AlgebraicTopology.FundamentalGroup.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Pi
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

On the normal classes of horizontal vectors `(v, 0)`, `v ∈ T_{h (x i)} Σ`, the normal symplectic
form of the graph torus (`TauCeti.SmoothEmbedding.symplecticNormalForm`) is `σ` itself. The
symplectic representative of the class of `(w, 0)` is `(w, 0) - dι_h a_w`, where `a_w` is the
tangent vector of `T` dual, under the pulled-back form, to the covector `b ↦ σ (w, dh (b i))`
(`TauCeti.SmoothEmbedding.symplecticNormalRepresentative_normalClass_eq_sub_mfderiv_inverse`).
Each such covector is a multiple of the coordinate covector `b ↦ b i`, so each `a_w` is a multiple
of the one vector `a₀` dual to it, and `a₀` lies in the kernel of that covector since a two-form
vanishes on the diagonal. So the correction term pairs to zero with `(v, 0)`.

The graph tori of `h` and `h'` have disjoint images exactly when `h t ≠ h' t` for every `t`,
since a point of `T` determines its coordinate `t = x i`.

A tangent vector `v` of `Σ` at `h (x i)` gives the horizontal vector `(v, 0)` of `Σ × T` at
`(h (x i), x)`, and so a normal class of the graph torus at `x`. For a family of vectors `v` that
depends smoothly on `x` and on a parameter, these classes form a smooth map into the normal bundle,
since the vectors `(v, 0)` form a smooth map into the pulled-back tangent bundle of `Σ × T` and
taking normal classes is smooth (`TauCeti.SmoothEmbedding.contMDiff_normalQuotientMap`).

These horizontal vectors give the normal spaces of the graph torus: a tangent vector
`(dh (w i), w)` of the graph torus with torus component zero vanishes, so `(v, 0)` is tangent only
for `v = 0`, and the normal space has dimension `dim Σ`. So `v ↦ [(v, 0)]` is a linear isomorphism
onto the normal space at `x`.

When `M` is a surface with a nondegenerate `σ`, a frame `e t : ℂ ≃ T_{h t} M` along `h`, smooth in
`t` and with `σ (e t 1) (e t i) > 0`, followed by `v ↦ [(v, 0)]`, identifies `ℂ` with the normal
spaces of the graph torus, smoothly in `x`, and the normal symplectic form on these is `σ`, so it
is positive on `1, i`. Rescaling (`SymplecticGeometry.SymplecticFraming.ofPos`) gives a symplectic
framing of the graph torus. Such frames exist along every circle in a Hausdorff σ-compact surface
(`TauCeti.SmoothTwoForm.IsNondegenerate.exists_frame_along`).

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
* `SymplecticGeometry.graphTorusHorizontalNormalEquiv`: the isomorphism `v ↦ [(v, 0)]` from
  `T_{h (x i)} Σ` to the normal space of the graph torus at `x`.
* `SymplecticGeometry.graphTorusSymplecticFraming`: the symplectic framing of the graph torus of a
  circle map in a surface given by a positive frame along it.

## Main results

* `SymplecticGeometry.mpullback_graphTorus_prod_torusSymplecticForm`: the graph torus pulls
  `pr₁^* σ + pr₂^* ω_T` back to `ω_T`.
* `SymplecticGeometry.hasSymplecticTangentImages_graphTorus`: it has symplectic tangent images for
  the product form.
* `SymplecticGeometry.symplecticNormalForm_graphTorus_horizontal`: the normal symplectic form
  pairs the normal classes of horizontal vectors `(v, 0)` and `(w, 0)` to `σ (v, w)`.
* `SymplecticGeometry.disjoint_range_graphTorus_iff`: two graph tori are disjoint exactly when the
  circle maps differ at every point.
* `SymplecticGeometry.contMDiff_normalClass_graphTorus_horizontal`: the normal classes of a smooth
  family of horizontal vectors `(v, 0)` form a smooth map into the normal bundle of the graph torus.
* `SymplecticGeometry.normalClass_graphTorus_horizontal_eq_zero_iff`: a horizontal vector `(v, 0)`
  is tangent to the graph torus only for `v = 0`.
* `SymplecticGeometry.nonempty_symplecticFraming_graphTorus`: the graph torus of a circle map in a
  Hausdorff σ-compact symplectic surface has a symplectic framing for the product form.
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

/-! ### The normal symplectic form on horizontal vectors -/

/-- The `M`-component of the differential of the graph torus `x ↦ (h (x i), x)` at `x` sends a
tangent vector `b` of the torus to `dh_{x i} (b i)`, the differential of `h` on its `i`-th
coordinate. -/
theorem fst_tangentSpaceProdEquiv_mfderiv_graphTorus (hh : ContMDiff 𝓘(ℝ) I ∞ h)
    (x : ∀ i, AddCircle (p i)) (b : TangentSpace (ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ)) x) :
    (Manifold.tangentSpaceProdEquiv (graphTorus hh x)
      (mfderiv (ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ))
        (I.prod (ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ))) (graphTorus hh) x b)).1 =
      mfderiv 𝓘(ℝ) I h (x i) (b i) := by
  rw [Manifold.tangentSpaceProdEquiv_apply, coe_graphTorus, Manifold.mfderiv_graph_swap_fst_apply]
  refine (mfderiv_comp_apply (g := h) x (hh.mdifferentiableAt (by simp))
    (hasMFDerivAt_apply i x).mdifferentiableAt b).trans ?_
  rw [mfderiv_apply]
  -- `ContinuousLinearMap.proj_apply` cannot be rewritten here: the domain of `proj i` is the
  -- tangent space of the torus only by definition. So it is applied by unification.
  exact congrArg _ (ContinuousLinearMap.proj_apply i b)

/-- **The normal symplectic form of a graph torus on horizontal vectors.** Let `σ` be a
nondegenerate two-form on `M`, so that the graph torus `x ↦ (h (x i), x)` has symplectic tangent
images for the product form `pr₁^* σ + pr₂^* ω_T` of `M × T`. For tangent vectors `v`, `w` of `M`
at `h (x i)`, the normal symplectic form of the graph torus at `x` pairs the normal classes of the
horizontal vectors `(v, 0)` and `(w, 0)` to `σ (v, w)`. -/
theorem symplecticNormalForm_graphTorus_horizontal {σ : SmoothTwoForm I M}
    (hσ : σ.IsNondegenerate) (hh : ContMDiff 𝓘(ℝ) I ∞ h) (x : ∀ i, AddCircle (p i))
    (v w : TangentSpace I (h (x i))) :
    (graphTorus hh).symplecticNormalForm (hasSymplecticTangentImages_graphTorus hσ hh) x (by simp)
        ((graphTorus hh).isImmersion.normalClass x (by simp)
          ((Manifold.tangentSpaceProdEquiv (graphTorus hh x)).symm (v, 0)))
        ((graphTorus hh).isImmersion.normalClass x (by simp)
          ((Manifold.tangentSpaceProdEquiv (graphTorus hh x)).symm (w, 0))) =
      σ.eval₂ (h (x i)) v w := by
  set f := graphTorus hh
  set Ω := σ.prod (torusSymplecticForm p)
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  set d := mfderiv (ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ))
    (I.prod (ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ))) f x
  let a := (f.tangentPairing Ω x).comp d
  have ha := f.tangentPairing_comp_apply Ω x
  have hinv := SmoothEmbedding.isInvertible_of_eval₂_mfderiv f
    (hasSymplecticTangentImages_graphTorus hσ hh) x hn a ha
  let e : TangentSpace (ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ)) x →L[ℝ] ℝ :=
    ContinuousLinearMap.proj i
  have he_apply : ∀ b, e b = b i := fun b ↦ ContinuousLinearMap.proj_apply i b
  -- The base point `(f x).1` is `h (x i)` by `graphTorus_apply`; the tangent spaces of `M` at
  -- both points are `E`, so `σ` can be read at either.
  have hbase : ∀ u u' : TangentSpace I (h (x i)), σ.eval₂ (f x).1 u u' = σ.eval₂ (h (x i)) u u' :=
    fun u u' ↦ congrArg (fun q ↦ σ.eval₂ q u u') (congrArg Prod.fst (graphTorus_apply hh x))
  -- The pairing of a horizontal vector `(u, 0)` with the tangent space of the graph torus is a
  -- multiple of the `i`-th coordinate.
  have hφ : ∀ (u : TangentSpace I (h (x i))) b,
      Ω.eval₂ (f x) ((Manifold.tangentSpaceProdEquiv (f x)).symm (u, 0)) (d b) =
        σ.eval₂ (h (x i)) u (mfderiv 𝓘(ℝ) I h (x i) (1 : ℝ)) * e b := by
    intro u b
    have h1 := fst_tangentSpaceProdEquiv_mfderiv_graphTorus hh x b
    rw [Manifold.tangentSpaceProdEquiv_apply] at h1
    have h0 : SmoothBundleForm.eval₂ (torusSymplecticForm p) (f x).2 0 (d b).2 = 0 :=
      SmoothBundleForm.eval₂_zero_left _ _ _
    have hb : mfderiv 𝓘(ℝ) I h (x i) (b i) = b i • mfderiv 𝓘(ℝ) I h (x i) (1 : ℝ) := by
      rw [← (mfderiv 𝓘(ℝ) I h (x i)).map_smul (b i) (1 : ℝ)]
      -- In the tangent space `ℝ` of the circle, `b i • 1` is the product `b i * 1` of reals.
      exact congrArg _ (mul_one (b i)).symm
    rw [SmoothTwoForm.eval₂_prod_eq_add, Manifold.tangentSpaceProdEquiv_symm_apply]
    dsimp only
    rw [h0, add_zero, h1, hb, hbase, SmoothBundleForm.eval₂_smul_right, smul_eq_mul, mul_comm,
      he_apply]
  have hflat : ∀ u : TangentSpace I (h (x i)),
      (Ω.flat (f x) ((Manifold.tangentSpaceProdEquiv (f x)).symm (u, 0))).comp d =
        σ.eval₂ (h (x i)) u (mfderiv 𝓘(ℝ) I h (x i) (1 : ℝ)) • e := fun u ↦
    ContinuousLinearMap.ext fun b ↦ by
      rw [ContinuousLinearMap.comp_apply, SmoothTwoForm.flat_apply, hφ,
        smul_apply, smul_eq_mul]
  -- The vector `a₀` of the torus dual to the `i`-th coordinate under the pulled-back form lies in
  -- the kernel of that coordinate, since a two-form vanishes on the diagonal.
  have he : e (a.inverse e) = 0 := by
    rw [← DFunLike.congr_fun (hinv.self_apply_inverse e) (a.inverse e), ha,
      SmoothBundleForm.eval₂_self]
  rw [SmoothEmbedding.symplecticNormalForm_normalClass,
    SmoothEmbedding.symplecticNormalRepresentative_normalClass_eq_sub_mfderiv_inverse f
      (hasSymplecticTangentImages_graphTorus hσ hh) x hn a ha, hflat w, map_smul, map_smul,
    SmoothBundleForm.eval₂_sub_right, SmoothBundleForm.eval₂_smul_right, hφ, he, mul_zero,
    smul_zero, sub_zero]
  rw [SmoothTwoForm.eval₂_prod_eq_add, Manifold.tangentSpaceProdEquiv_symm_apply,
    Manifold.tangentSpaceProdEquiv_symm_apply]
  dsimp only
  rw [SmoothBundleForm.eval₂_zero_left, add_zero, hbase]

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

/-- The torus component of the differential of the graph torus is the identity: the differential
sends a tangent vector `w` of the torus to a vector whose torus component is `w`. -/
theorem snd_tangentSpaceProdEquiv_mfderiv_graphTorus (hh : ContMDiff 𝓘(ℝ) I ∞ h)
    (x : ∀ i, AddCircle (p i)) (w : TangentSpace (ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ)) x) :
    (Manifold.tangentSpaceProdEquiv (graphTorus hh x)
      (mfderiv (ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ))
        (I.prod (ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ))) (graphTorus hh) x w)).2 = w := by
  rw [Manifold.tangentSpaceProdEquiv_apply, coe_graphTorus]
  exact Manifold.mfderiv_graph_swap_snd_apply
    ((hh.comp (contMDiff_apply (i := i))).mdifferentiable (by simp) x) w

/-- A horizontal tangent vector `(v, 0)` at a point of the graph torus has zero normal class
exactly when `v = 0`, since a tangent vector of the graph torus with torus component zero
vanishes. -/
theorem normalClass_graphTorus_horizontal_eq_zero_iff (hh : ContMDiff 𝓘(ℝ) I ∞ h)
    (x : ∀ i, AddCircle (p i)) (v : TangentSpace I (h (x i))) :
    (graphTorus hh).isImmersion.normalClass x (by simp)
        ((Manifold.tangentSpaceProdEquiv (graphTorus hh x)).symm (v, 0)) = 0 ↔ v = 0 := by
  refine ⟨fun hv ↦ ?_, fun hv ↦ ?_⟩
  · obtain ⟨w, hw⟩ := ((graphTorus hh).isImmersion.normalClass_eq_zero_iff x _ _).1 hv
    rw [ContinuousLinearMap.coe_coe] at hw
    have hw₂ := congrArg (fun u ↦ (Manifold.tangentSpaceProdEquiv (graphTorus hh x) u).2) hw
    simp only [snd_tangentSpaceProdEquiv_mfderiv_graphTorus,
      ContinuousLinearEquiv.apply_symm_apply] at hw₂
    -- `hw₂` lives in the tangent space of the torus at `(graphTorus hh x).2`, which is the tangent
    -- space at `x` once `TangentSpace` is unfolded.
    have hw₀ : w = 0 := hw₂
    rw [hw₀, map_zero] at hw
    have hv₁ := congrArg (fun u ↦ (Manifold.tangentSpaceProdEquiv (graphTorus hh x) u).1) hw
    simp only [ContinuousLinearEquiv.apply_symm_apply, map_zero, Prod.fst_zero] at hv₁
    exact hv₁.symm
  · subst hv
    exact (congrArg _ ((congrArg _ Prod.mk_zero_zero).trans (map_zero _))).trans (map_zero _)

/-- The **horizontal normal equivalence** of the graph torus `x ↦ (h (x i), x)` at `x`: the real
linear isomorphism from `T_{h (x i)} M` to the normal space of the graph torus at `x` that sends
`v` to the normal class of the horizontal vector `(v, 0)`. -/
def graphTorusHorizontalNormalEquiv (hh : ContMDiff 𝓘(ℝ) I ∞ h) (x : ∀ i, AddCircle (p i)) :
    TangentSpace I (h (x i)) ≃L[ℝ] (graphTorus hh).isImmersion.NormalSpace x (by simp) :=
  -- The normal class of the horizontal vector `(v, 0)`, as a continuous linear map of `v`.
  let L : TangentSpace I (h (x i)) →L[ℝ] (graphTorus hh).isImmersion.NormalSpace x (by simp) :=
    ((graphTorus hh).isImmersion.normalClassL x (by simp)).comp
      ((Manifold.tangentSpaceProdEquiv (graphTorus hh x)).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.inl ℝ _ _))
  -- This holds by unfolding `L`, since the tangent spaces at `h (x i)` and at
  -- `(graphTorus hh x).1` agree once `TangentSpace` is unfolded.
  have hL : ∀ v, L v = (graphTorus hh).isImmersion.normalClass x (by simp)
      ((Manifold.tangentSpaceProdEquiv (graphTorus hh x)).symm (v, 0)) := fun v ↦
    (graphTorus hh).isImmersion.normalClassL_apply x _
      ((Manifold.tangentSpaceProdEquiv (graphTorus hh x)).symm (v, 0))
  have hinj : Function.Injective L := (injective_iff_map_eq_zero L).2 fun v hv ↦
    (normalClass_graphTorus_horizontal_eq_zero_iff hh x v).1 ((hL v).symm.trans hv)
  have hdim : Module.finrank ℝ (TangentSpace I (h (x i))) =
      Module.finrank ℝ ((graphTorus hh).isImmersion.NormalSpace x (by simp)) := by
    rw [(graphTorus hh).isImmersion.finrank_normalSpace x _, TauCeti.finrank_tangentSpace,
      TauCeti.finrank_tangentSpace, TauCeti.finrank_tangentSpace, Module.finrank_prod]
    omega
  (L.toLinearMap.linearEquivOfInjective hinj hdim).toContinuousLinearEquiv

/-- The horizontal normal equivalence sends `v` to the normal class of `(v, 0)`. -/
@[simp]
theorem graphTorusHorizontalNormalEquiv_apply (hh : ContMDiff 𝓘(ℝ) I ∞ h)
    (x : ∀ i, AddCircle (p i)) (v : TangentSpace I (h (x i))) :
    graphTorusHorizontalNormalEquiv hh x v =
      (graphTorus hh).isImmersion.normalClass x (by simp)
        ((Manifold.tangentSpaceProdEquiv (graphTorus hh x)).symm (v, 0)) := by
  rw [graphTorusHorizontalNormalEquiv, LinearEquiv.coe_toContinuousLinearEquiv',
    LinearMap.linearEquivOfInjective_apply, ContinuousLinearMap.coe_coe]
  -- What remains is the value of the composite map, as in `hL` of the definition.
  exact (graphTorus hh).isImmersion.normalClassL_apply x _
    ((Manifold.tangentSpaceProdEquiv (graphTorus hh x)).symm (v, 0))

/-! ### Symplectic framings -/

/-- **The symplectic framing of a graph torus given by a positive frame along `h`.** Let `σ` be a
nondegenerate two-form on a surface `M`, and let `e t : ℂ ≃L[ℝ] T_{h t} M` be real linear
isomorphisms, smooth as the map `(t, z) ↦ e t z` into the tangent bundle, with
`σ (e t 1) (e t i) > 0` for every `t`. Composing `e (x i)` with the horizontal normal equivalence
`v ↦ [(v, 0)]` gives isomorphisms of `ℂ` with the normal spaces of the graph torus at `x`, on which
the normal symplectic form is `σ`; `SymplecticFraming.ofPos` turns them into a symplectic framing
of the graph torus for the product form `pr₁^* σ + pr₂^* ω_T`. -/
def graphTorusSymplecticFraming {σ : SmoothTwoForm I M} (hσ : σ.IsNondegenerate)
    (hh : ContMDiff 𝓘(ℝ) I ∞ h) (hE : finrank ℝ E = 2) {e : ∀ t, ℂ ≃L[ℝ] TangentSpace I (h t)}
    (he : ContMDiff (𝓘(ℝ).prod 𝓘(ℝ, ℂ)) I.tangent ∞
      fun y : AddCircle (p i) × ℂ ↦ (⟨h y.1, e y.1 y.2⟩ : TangentBundle I M))
    (hpos : ∀ t, 0 < σ.eval₂ (h t) (e t 1) (e t Complex.I)) :
    SymplecticFraming (hasSymplecticTangentImages_graphTorus hσ hh)
      (Complex.finrank_real_eq_finrank_prod_sub hE) :=
  SymplecticFraming.ofPos (fun x ↦ (e (x i)).trans (graphTorusHorizontalNormalEquiv hh x))
    (by
      let := (graphTorus hh).normalSpaceFiberBundle (WithTop.coe_ne_zero.2 ENat.top_ne_zero)
        (Complex.finrank_real_eq_finrank_prod_sub hE)
      -- The frame read at the `i`-th coordinate of a point of the torus.
      have hu : ContMDiff ((ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, ℂ)) I.tangent ∞
          fun y : (∀ i, AddCircle (p i)) × ℂ ↦
            (⟨h (y.1 i), e (y.1 i) y.2⟩ : TangentBundle I M) :=
        he.comp (f := fun y : (∀ i, AddCircle (p i)) × ℂ ↦ (y.1 i, y.2))
          ((contMDiff_apply.comp contMDiff_fst).prodMk contMDiff_snd)
      refine (contMDiff_normalClass_graphTorus_horizontal hh
        (Complex.finrank_real_eq_finrank_prod_sub hE) (u := fun x z ↦ e (x i) z)
        hu).congr fun y ↦ ?_
      rw [ContinuousLinearEquiv.trans_apply, graphTorusHorizontalNormalEquiv_apply,
        Manifold.tangentSpaceProdEquiv_symm_apply]
      -- The two sides differ only in the proofs of `∞ ≠ 0` that they pass to `normalClass`.
      rfl)
    fun x ↦ by
      simp only [ContinuousLinearEquiv.trans_apply, graphTorusHorizontalNormalEquiv_apply]
      exact (symplecticNormalForm_graphTorus_horizontal hσ hh x _ _).trans_gt (hpos (x i))

/-- The framing `graphTorusSymplecticFraming hσ hh hE he hpos` sends a normal vector `v` of the
zero slice at `x` to the normal class of the horizontal vector `(e (x i) ((√λ)⁻¹ • z), 0)`, where
`z ∈ ℂ` is the `ℂ`-component of `v` and `λ = σ (e (x i) 1) (e (x i) i)`. -/
@[simp]
theorem graphTorusSymplecticFraming_apply {σ : SmoothTwoForm I M} (hσ : σ.IsNondegenerate)
    (hh : ContMDiff 𝓘(ℝ) I ∞ h) (hE : finrank ℝ E = 2) {e : ∀ t, ℂ ≃L[ℝ] TangentSpace I (h t)}
    (he : ContMDiff (𝓘(ℝ).prod 𝓘(ℝ, ℂ)) I.tangent ∞
      fun y : AddCircle (p i) × ℂ ↦ (⟨h y.1, e y.1 y.2⟩ : TangentBundle I M))
    (hpos : ∀ t, 0 < σ.eval₂ (h t) (e t 1) (e t Complex.I)) (x : ∀ i, AddCircle (p i))
    (v : (zeroSlice (ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ))
      (∀ i, AddCircle (p i))).isImmersion.NormalSpace x (WithTop.coe_ne_zero.2 ENat.top_ne_zero)) :
    graphTorusSymplecticFraming hσ hh hE he hpos x v =
      (graphTorus hh).isImmersion.normalClass x (by simp)
        ((Manifold.tangentSpaceProdEquiv (graphTorus hh x)).symm
          (e (x i) ((√(σ.eval₂ (h (x i)) (e (x i) 1) (e (x i) Complex.I)))⁻¹ •
            zeroSliceNormalEquiv _ _ x v), 0)) := by
  rw [graphTorusSymplecticFraming, SymplecticFraming.ofPos_apply,
    ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.trans_apply, graphTorusHorizontalNormalEquiv_apply,
    graphTorusHorizontalNormalEquiv_apply, graphTorusHorizontalNormalEquiv_apply,
    symplecticNormalForm_graphTorus_horizontal hσ]

/-- **Graph tori are symplectically framed.** Let `σ` be a nondegenerate two-form on a Hausdorff
σ-compact surface `M`, and `h : AddCircle (p i) → M` smooth. Then the graph torus of `h` has a
symplectic framing for the product form `pr₁^* σ + pr₂^* ω_T` of `M × T`. -/
theorem nonempty_symplecticFraming_graphTorus [T2Space M] [SigmaCompactSpace M]
    {σ : SmoothTwoForm I M} (hσ : σ.IsNondegenerate) (hh : ContMDiff 𝓘(ℝ) I ∞ h)
    (hE : finrank ℝ E = 2) :
    Nonempty (SymplecticFraming (hasSymplecticTangentImages_graphTorus hσ hh)
      (Complex.finrank_real_eq_finrank_prod_sub hE)) := by
  obtain ⟨e, he, hpos⟩ := hσ.exists_frame_along hE (by simp) hh
  exact ⟨graphTorusSymplecticFraming hσ hh hE he hpos⟩

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
