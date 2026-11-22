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
import SymplecticGeometry.Geometry.Manifold.Orientation.Preserving


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
(`SymplecticGeometry.radialAngularForm`) and vanishes outside its image integrates to `2πk`. These
are the curvature forms of the connections that the Chern–Weil computation of the first Chern
number builds from clutching data.

The change of variables is Tau Ceti's
`Topology.IsOpenEmbedding.integralTopForm_mpullback_of_isOrientationPreservingAt`, which applies
to any orientation-preserving open embedding, so no comparison with the charts of the atlas of
`M` is needed.

## Main results

* `SymplecticGeometry.CoordinateDisc.isOrientationPreservingAt_ofChart`: the coordinate disc of an
  oriented smooth chart preserves orientation.
* `SymplecticGeometry.CoordinateDisc.integralTopForm_mpullback_ofChart`: `∫_{B(0, 2)} φ^* f = ∫_M f`
  for a top form `f` supported in the image of `φ`.
* `SymplecticGeometry.CoordinateDisc.integralTopForm_eq_of_mpullback_ofChart_eq`: a form that
  reads `k • d(β(‖z‖) dθ)` in the disc and vanishes outside it integrates to `2πk`.

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
      ((Manifold.Orientation.model (I := 𝓘(ℝ, ℂ)) Complex.orientation (by simp)).restrict ball)
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
        ((Manifold.Orientation.model (I := 𝓘(ℝ, ℂ)) Complex.orientation (by simp)).restrict ball)
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

end CoordinateDisc

end SymplecticGeometry
