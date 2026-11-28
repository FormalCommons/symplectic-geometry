/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.CoordinateDisc
public import SymplecticGeometry.Geometry.Manifold.DeRham.RadialAngularForm
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.OpenSubset
public import TauCeti.Geometry.Manifold.Orientation.OpenSubset
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Indicator
import SymplecticGeometry.Geometry.Manifold.Orientation.Preserving
import SymplecticGeometry.Topology.Algebra.Support


/-!
# Integrals of top forms in the coordinate disc of an oriented chart

Let `M` be a surface with a smooth orientation `o`, and let `e` be a smooth chart of `M`, in its
maximal atlas, that preserves orientation on its source, from `o` to the standard orientation of
`ℝ²`. For a ball `B(c, r)` in the target of `e`, `SymplecticGeometry.CoordinateDisc.ofChart`
gives the coordinate disc `φ z = e.symm (c + (r / 2) (re z, im z))` on the ball of radius `2`
of `ℂ`. This file shows that `φ` preserves the smooth orientations, from the standard orientation
of `ℂ` restricted to the ball to `o`, and so computes integrals of top forms of `M` supported in
the image of `φ` in the coordinates `z`: `∫_M f = ∫_{B(0, 2)} φ^* f`.

As a consequence, a `2`-form on `M` that reads `k • d(β(‖z‖) dθ)` in such a disc
(`SymplecticGeometry.radialAngularForm`) and vanishes outside its image integrates to `2πk`. More
generally, a form supported in the images of finitely many such discs with pairwise disjoint
images, reading `k i • d(β(‖z‖) dθ)` in the `i`-th one, integrates to `2π ∑ i, k i`: its pieces in
the discs, cut out with `Set.indicator`, are smooth
(`TauCeti.IsSmoothForm.indicator_of_isClosed`), and the integral is additive.
These are the curvature forms of the connections that the Chern–Weil
computation of the first Chern number builds from clutching data.

The change of variables is Tau Ceti's
`Topology.IsOpenEmbedding.integralTopForm_mpullback_of_isOrientationPreservingAt`, which applies
to any orientation-preserving open embedding, so no comparison with the charts of the atlas of
`M` is needed.

For a chart in the maximal `C^n` atlas, the formula of `φ` is `C^n` on the ball of radius `2`
(`SymplecticGeometry.CoordinateDisc.contMDiffOn_symm_add_smul_orthonormalBasisOneI_repr`), so `φ`
is `C^n` (`SymplecticGeometry.CoordinateDisc.contMDiff_ofChart`).

## Main results

* `SymplecticGeometry.CoordinateDisc.isOrientationPreservingAt_ofChart`: the coordinate disc of an
  oriented smooth chart preserves orientation.
* `SymplecticGeometry.CoordinateDisc.integralTopForm_mpullback_ofChart`: `∫_{B(0, 2)} φ^* f = ∫_M f`
  for a top form `f` supported in the image of `φ`.
* `SymplecticGeometry.CoordinateDisc.integralTopForm_eq_of_mpullback_ofChart_eq`: a form that
  reads `k • d(β(‖z‖) dθ)` in the disc and vanishes outside it integrates to `2πk`.
* `SymplecticGeometry.CoordinateDisc.integralTopForm_eq_sum_of_mpullback_ofChart_eq`: a form that
  reads `k i • d(β(‖z‖) dθ)` in the `i`-th of finitely many disjoint discs and vanishes outside
  them integrates to `2π ∑ i, k i`.
* `SymplecticGeometry.CoordinateDisc.contMDiffOn_symm_add_smul_orthonormalBasisOneI_repr`: the
  coordinate disc of a smooth chart extends smoothly to the ball of radius `2`.
* `SymplecticGeometry.CoordinateDisc.contMDiff_ofChart`: the coordinate disc of a smooth chart is
  smooth.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §2.7 (the first Chern number as the integral of a curvature form).
* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Proposition 16.6 (integration of top
  forms through orientation-preserving parametrizations).
-/

public section

noncomputable section

open Set TopologicalSpace TauCeti Manifold.Orientation
open scoped Manifold ContDiff Real

namespace SymplecticGeometry

namespace CoordinateDisc

variable {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) 1 M] {o : Manifold.Orientation (𝓡 2) M (Fin 2)}

variable (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)))
  {c : EuclideanSpace ℝ (Fin 2)} {r : ℝ} (hr : 0 < r) (hc : Metric.ball c r ⊆ e.target)
  (he : ∀ x ∈ e.source,
    o.IsOrientationPreservingAt (Manifold.Orientation.euclideanSpace 2) e x)

include hc he in
/-- **The coordinate disc of an oriented chart preserves orientation.** For a smooth chart `e`
of `M` that preserves orientation on its source, the coordinate disc `ofChart e hr hc he`
preserves orientation at every point of the ball of radius `2`, from the standard orientation of
`ℂ` restricted to the ball to `o`. -/
theorem isOrientationPreservingAt_ofChart (he' : e ∈ IsManifold.maximalAtlas (𝓡 2) 1 M)
    (z : ball) :
    IsOrientationPreservingAt
      (Manifold.Orientation.complex.restrict ball)
      o (ofChart e hr hc he) z := by
  have hφ : ⇑(ofChart e hr hc he) =
      e.symm ∘ fun w : ball ↦ c + (r / 2) • Complex.orthonormalBasisOneI.repr (w : ℂ) :=
    funext fun w ↦ ofChart_apply e hr hc he w
  have hy : c + (r / 2) • Complex.orthonormalBasisOneI.repr (z : ℂ) ∈ e.target :=
    hc (add_smul_orthonormalBasisOneI_repr_mem_ball c hr z)
  rw [hφ]
  exact IsOrientationPreservingAt.comp (g := e.symm)
    (f := fun w : ball ↦ c + (r / 2) • Complex.orthonormalBasisOneI.repr (w : ℂ))
    ((he _ (e.map_target hy)).symm_of_mem_maximalAtlas he' hy)
    (isOrientationPreservingAt_add_smul_orthonormalBasisOneI_repr c hr z)

include hc he in
/-- **Integration in the coordinate disc of an oriented chart.** For a smooth chart `e` of `M`
that preserves orientation on its source, and a top form `f` on `M` supported in the image of the
coordinate disc `φ = ofChart e hr hc he`, the integral of `f` over `M` is the integral of `φ^* f`
over the ball of radius `2` of `ℂ`, for the standard orientation of `ℂ`. -/
theorem integralTopForm_mpullback_ofChart (he' : e ∈ IsManifold.maximalAtlas (𝓡 2) 1 M)
    {f : RoughForm (𝓡 2) M ℝ 2}
    (hf : _root_.tsupport (α := EuclideanSpace ℝ (Fin 2) [⋀^Fin 2]→L[ℝ] ℝ) f ⊆
      range (ofChart e hr hc he)) :
    integralTopForm
        (Manifold.Orientation.complex.restrict ball)
        (mpullback 𝓘(ℝ, ℂ) (𝓡 2) (ofChart e hr hc he) f) =
      integralTopForm o f :=
  (ofChart e hr hc he).isOpenEmbedding.integralTopForm_mpullback_of_isOrientationPreservingAt
    (isOrientationPreservingAt_ofChart e hr hc he he') hf

include hc he in
/-- **The integral of a model curvature form in a coordinate disc.** Let `β` be `C¹`, `0` on
`(-∞, a]` and `1` on `[b, ∞)`, with `0 < a` and `b < 2`. Let `f` be a `2`-form on `M` supported in
the image of the coordinate disc `φ = ofChart e hr hc he` of a smooth chart `e` that preserves
orientation on its source, such that `φ^* f = k • d(β(‖z‖) dθ)` on the ball of radius `2`. Then
`∫_M f = 2πk`. -/
theorem integralTopForm_eq_of_mpullback_ofChart_eq
    (he' : e ∈ IsManifold.maximalAtlas (𝓡 2) 1 M) {β : ℝ → ℝ} {a b : ℝ} (hβ : ContDiff ℝ 1 β)
    (ha : 0 < a) (hb : b < 2) (hβa : ∀ t ≤ a, β t = 0) (hβb : ∀ t ≥ b, β t = 1)
    {f : RoughForm (𝓡 2) M ℝ 2}
    (hf : _root_.tsupport (α := EuclideanSpace ℝ (Fin 2) [⋀^Fin 2]→L[ℝ] ℝ) f ⊆
      range (ofChart e hr hc he))
    {k : ℝ} (hfk : mpullback 𝓘(ℝ, ℂ) (𝓡 2) (ofChart e hr hc he) f =
      k • mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : ball → ℂ)
        (mextDeriv (radialAngularForm β))) :
    integralTopForm o f = 2 * π * k := by
  have hsupp : _root_.tsupport (α := ℂ [⋀^Fin 2]→L[ℝ] ℝ) (mextDeriv (radialAngularForm β)) ⊆
      ball :=
    (tsupport_mextDeriv_radialAngularForm_subset (hβ.differentiable (by simp)) ha hβa hβb).trans
      fun z hz ↦ mem_ball_iff.2 (hz.2.trans_lt hb)
  rw [← integralTopForm_mpullback_ofChart e hr hc he he' hf, hfk, integralTopForm_smul,
    integralTopForm_mpullback_subtypeVal _ ball hsupp,
    integralTopForm_mextDeriv_radialAngularForm hβ ha hβa hβb, mul_comm]

/-! ### Smoothness of the coordinate disc of a chart -/

omit [T2Space M] [IsManifold (𝓡 2) 1 M] in
include hr hc in
/-- For a chart `e` of the maximal `C^n` atlas of `M` and a ball `B(c, r)` in its target, the map
`z ↦ e.symm (c + (r / 2) (re z, im z))` is `C^n` on the ball of radius `2` of `ℂ`. On that ball
it is the coordinate disc `ofChart e hr hc he` (`ofChart_apply`). -/
theorem contMDiffOn_symm_add_smul_orthonormalBasisOneI_repr {n : ℕ∞ω} [IsManifold (𝓡 2) n M]
    (he' : e ∈ IsManifold.maximalAtlas (𝓡 2) n M) :
    ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 2) n
      (fun z : ℂ ↦ e.symm (c + (r / 2) • Complex.orthonormalBasisOneI.repr z)) (ball : Set ℂ) :=
  (contMDiffOn_symm_of_mem_maximalAtlas he').comp
    (contDiff_const.add (Complex.orthonormalBasisOneI.repr.contDiff.const_smul
      (r / 2))).contMDiff.contMDiffOn
    fun z hz ↦ hc (add_smul_orthonormalBasisOneI_repr_mem_ball c hr ⟨z, hz⟩)

/-- The coordinate disc of a chart `e` of the maximal `C^n` atlas of `M` is `C^n`. -/
theorem contMDiff_ofChart {n : ℕ∞ω} [IsManifold (𝓡 2) n M]
    (he' : e ∈ IsManifold.maximalAtlas (𝓡 2) n M) :
    ContMDiff 𝓘(ℝ, ℂ) (𝓡 2) n (ofChart e hr hc he) := by
  have h : ⇑(ofChart e hr hc he) =
      (fun z : ℂ ↦ e.symm (c + (r / 2) • Complex.orthonormalBasisOneI.repr z)) ∘ Subtype.val :=
    funext fun z ↦ ofChart_apply e hr hc he z
  rw [h]
  exact (contMDiffOn_symm_add_smul_orthonormalBasisOneI_repr e hr hc he').comp_contMDiff
    contMDiff_subtypeVal fun z ↦ z.property

/-! ### Forms supported in finitely many coordinate discs -/

/-- **The integral of model curvature forms in finitely many coordinate discs.** Let `φ i` be the
coordinate discs of finitely many oriented smooth charts `e i`, with pairwise disjoint images. Let
`β` be `C¹`, `0` on `(-∞, a]` and `1` on `[b, ∞)`, with `0 < a` and `b < 2`. A continuous `2`-form
on `M` that vanishes off the images under the `φ i` of the closed disc of radius `b`, and whose
pull-back along each `φ i` is `k i • d(β(‖z‖) dθ)`, integrates to `2π ∑ i, k i`. -/
theorem integralTopForm_eq_sum_of_mpullback_ofChart_eq {ι : Type*} [Fintype ι]
    (e : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)))
    {c : ι → EuclideanSpace ℝ (Fin 2)} {r : ι → ℝ} (hr : ∀ i, 0 < r i)
    (hc : ∀ i, Metric.ball (c i) (r i) ⊆ (e i).target)
    (he : ∀ i, ∀ x ∈ (e i).source,
      o.IsOrientationPreservingAt (Manifold.Orientation.euclideanSpace 2) (e i) x)
    (he' : ∀ i, e i ∈ IsManifold.maximalAtlas (𝓡 2) 1 M)
    (hdisj : Pairwise fun i j ↦ Disjoint (range (ofChart (e i) (hr i) (hc i) (he i)))
      (range (ofChart (e j) (hr j) (hc j) (he j))))
    {β : ℝ → ℝ} {a b : ℝ} (hβ : ContDiff ℝ 1 β)
    (ha : 0 < a) (hb : b < 2) (hβa : ∀ t ≤ a, β t = 0) (hβb : ∀ t ≥ b, β t = 1)
    {f : RoughForm (𝓡 2) M ℝ 2} (hf : IsSmoothForm (𝓡 2) 0 f)
    (hf0 : ∀ x, (∀ i, x ∉ ofChart (e i) (hr i) (hc i) (he i) '' {z | ‖(z : ℂ)‖ ≤ b}) → f x = 0)
    {k : ι → ℝ} (hfk : ∀ i, mpullback 𝓘(ℝ, ℂ) (𝓡 2) (ofChart (e i) (hr i) (hc i) (he i)) f =
      k i • mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : ball → ℂ)
        (mextDeriv (radialAngularForm β))) :
    integralTopForm o f = 2 * π * ∑ i, k i := by
  classical
  set φ := fun i ↦ ofChart (e i) (hr i) (hc i) (he i)
  set K : ι → Set M := fun i ↦ φ i '' {z | ‖(z : ℂ)‖ ≤ b}
  have hKc (i : ι) : IsCompact (K i) := (φ i).isCompact_image_closedBall hb
  have hKr (i : ι) : K i ⊆ range (φ i) := image_subset_range _ _
  -- the part `g i` of `f` in the `i`-th disc
  let g : ι → RoughForm (𝓡 2) M ℝ 2 := fun i ↦
    (range (φ i)).indicator (M := EuclideanSpace ℝ (Fin 2) [⋀^Fin 2]→L[ℝ] ℝ) f
  have hf0' (i : ι) : ∀ x ∈ range (φ i), x ∉ K i → f x = 0 := fun x h hx ↦
    hf0 x fun j hj ↦ by
      by_cases hji : j = i
      · exact hx (hji ▸ hj)
      · exact (hdisj hji).ne_of_mem (hKr j hj) h rfl
  have htsupp (i : ι) : _root_.tsupport (α := EuclideanSpace ℝ (Fin 2) [⋀^Fin 2]→L[ℝ] ℝ) (g i) ⊆
      K i :=
    tsupport_indicator_subset_of_eqOn (hKc i).isClosed fun x hx ↦ hf0' i x hx.1 hx.2
  have hgs (i : ι) : IsSmoothForm (𝓡 2) 0 (g i) :=
    IsSmoothForm.indicator_of_isClosed (φ i).isOpenEmbedding.isOpen_range (hKc i).isClosed (hKr i)
      (fun x _ ↦ hf.contMDiff x) (hf0' i)
  have hsum : f = ∑ i, g i := by
    funext x
    rw [Finset.sum_apply]
    -- stated pointwise, since the sums in `M → E [⋀^Fin 2]→L[ℝ] ℝ` and in `RoughForm` differ in
    -- their instances; they agree by definition of the tangent space
    refine (congrFun ((Set.indicator_eq_self (M := EuclideanSpace ℝ (Fin 2) [⋀^Fin 2]→L[ℝ] ℝ)).2
      fun y hy ↦ ?_) x).symm.trans (Finset.indicator_biUnion_apply Finset.univ
        (fun i ↦ range (φ i)) (fun i _ j _ hij ↦ hdisj hij) x)
    refine by_contra fun h ↦ hy (hf0 y fun i hi ↦ h ?_)
    exact mem_iUnion₂.2 ⟨i, Finset.mem_univ i, hKr i hi⟩
  let bE := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
  rw [hsum, integralTopForm_sum o g Finset.univ
      (fun i _ ↦ (hgs i).integrableTopForm ((hKc i).of_isClosed_subset (isClosed_tsupport _)
        (htsupp i)) bE), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ integralTopForm_eq_of_mpullback_ofChart_eq (e i) (hr i)
    (hc i) (he i) (he' i) hβ ha hb hβa hβb ((htsupp i).trans (hKr i)) ?_
  rw [← hfk i]
  funext z
  exact mpullback_apply_congr
    (indicator_of_mem (M := EuclideanSpace ℝ (Fin 2) [⋀^Fin 2]→L[ℝ] ℝ) (mem_range_self z) f)

end CoordinateDisc

end SymplecticGeometry
