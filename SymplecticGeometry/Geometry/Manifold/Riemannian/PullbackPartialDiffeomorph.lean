/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Geometry.Manifold.Riemannian.Pullback.Basic

/-!
# Pulling back a metric along a partial diffeomorphism

Let `g` be a `C^n` Riemannian metric on `N` and `Ψ : M → N` a partial diffeomorphism of class
`C^m`, `n + 1 ≤ m`. On the source of `Ψ`, the forms `(v, w) ↦ g_{Ψ x}(dΨ_x v, dΨ_x w)` are a `C^n`
section of the bundle of bilinear forms on the tangent spaces of `M`, and they are positive
definite, since the differential of `Ψ` is invertible there. This is the local input that the
gluing of metrics by partitions of unity takes, for instance
`TauCeti.exists_contMDiffRiemannianMetric_inner_mem_of_local`. With `Ψ` the local inverse
`IsLocalDiffeomorphAt.localInverse` of a local diffeomorphism `Φ : N → M`, it is the metric `g`
pushed forward along `Φ` near a point.

Tau Ceti's `Bundle.ContMDiffRiemannianMetric.pullback` is the global version, for a map that is
smooth everywhere with injective differential everywhere; the smoothness here is its
`Bundle.ContMDiffRiemannianMetric.contMDiffAt_pullback` at each point of the source.

## Main results

* `PartialDiffeomorph.contMDiffOn_pullback`: the pulled-back forms are `C^n` on the source.
* `PartialDiffeomorph.pullback_apply_self_pos`: they are positive on nonzero vectors there.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 2
  (pullback metrics).
-/

public section

open Bundle
open scoped ContDiff Manifold

namespace PartialDiffeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] {n m : ℕ∞ω}

/-- The pull-back of a `C^n` Riemannian metric `g` on `N` along a partial diffeomorphism
`Ψ : M → N` of class `C^m`, `n + 1 ≤ m`, the forms `(v, w) ↦ g_{Ψ x}(dΨ_x v, dΨ_x w)`, is a `C^n`
section of the bundle of bilinear forms on the source of `Ψ`. -/
theorem contMDiffOn_pullback [IsManifold I 1 M] [IsManifold J 1 N]
    (g : ContMDiffRiemannianMetric J n F (fun y : N ↦ TangentSpace J y))
    (Ψ : PartialDiffeomorph I J M N m) (hm : n + 1 ≤ m) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) n
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) x
        ((ContinuousLinearMap.precomp ℝ (mfderiv I J Ψ x)).comp
          ((g.inner (Ψ x)).comp (mfderiv I J Ψ x)))) Ψ.source := fun _ hx ↦
  (g.contMDiffAt_pullback
    ((Ψ.contMDiffOn.contMDiffAt (Ψ.open_source.mem_nhds hx)).of_le hm)).contMDiffWithinAt

/-- The pull-back of a Riemannian metric `g` on `N` along a partial diffeomorphism `Ψ : M → N`
of class `C^m`, `m ≠ 0`, is positive on nonzero vectors at each point `x` of the source:
`0 < g_{Ψ x}(dΨ_x v, dΨ_x v)` for `v ≠ 0`. -/
theorem pullback_apply_self_pos [IsManifold J 1 N]
    (g : ContMDiffRiemannianMetric J n F (fun y : N ↦ TangentSpace J y))
    (Ψ : PartialDiffeomorph I J M N m) (hm : m ≠ 0) {x : M} (hx : x ∈ Ψ.source)
    {v : TangentSpace I x} (hv : v ≠ 0) :
    0 < (ContinuousLinearMap.precomp ℝ (mfderiv I J Ψ x)).comp
      ((g.inner (Ψ x)).comp (mfderiv I J Ψ x)) v v :=
  g.pos (Ψ x) _ ((map_ne_zero_iff _ (Ψ.isInvertible_mfderiv hm hx).injective).2 hv)

end PartialDiffeomorph

end
