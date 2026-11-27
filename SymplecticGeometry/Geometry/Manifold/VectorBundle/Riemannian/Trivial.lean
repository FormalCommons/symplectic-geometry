/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import TauCeti.Geometry.Manifold.VectorBundle.Hom.Basic
public import TauCeti.Analysis.Complex.Euclidean.Space
public import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# Constant metrics on trivial bundles

A symmetric, positive definite continuous bilinear form `b` on a finite-dimensional real normed
space `W` gives a metric on the trivial bundle `M × W` of every regularity, equal to `b` on every
fibre: `Bundle.ContMDiffRiemannianMetric.const b hb hpos`. Mathlib's instance
`IsContMDiffRiemannianBundle` on `Bundle.Trivial` is only a property; this is the metric as data,
for an arbitrary inner product `b` on the model fibre.

## Main definitions

* `Bundle.ContMDiffRiemannianMetric.const`: the constant metric `b` on `Bundle.Trivial M W`.
* `Bundle.ContMDiffRiemannianMetric.constComplexEuclidean ι`: the constant metric on
  `Bundle.Trivial M (ι → ℂ)` that `TauCeti.complexToRealEuclidean ι` carries to the Euclidean
  one, `g₀(u, v) = ⟪c u, c v⟫`, with `@[simp] constComplexEuclidean_inner`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.6
-/

public section

noncomputable section

open Bundle
open scoped Manifold

namespace Bundle.ContMDiffRiemannianMetric

variable {EB HB M : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [TopologicalSpace HB] {I : ModelWithCorners ℝ EB HB}
  [TopologicalSpace M] [ChartedSpace HB M] {n : WithTop ℕ∞}
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

/-- The constant metric on the trivial bundle `M × W` given by a symmetric bilinear form `b` on
`W` that is positive on nonzero vectors: its inner product on every fibre is `b`. -/
def const (b : W →L[ℝ] W →L[ℝ] ℝ) (hb : ∀ v w, b v w = b w v) (hpos : ∀ v, v ≠ 0 → 0 < b v v) :
    ContMDiffRiemannianMetric I n W (Trivial M W) where
  inner _ := b
  symm _ := hb
  pos _ := hpos
  isVonNBounded _ := b.isVonNBounded_setOf_lt_one_of_pos hpos
  contMDiff := TauCeti.contMDiff_const_bundlePairing b

/-- The constant metric is `b` on every fibre. -/
@[simp]
theorem const_inner (b : W →L[ℝ] W →L[ℝ] ℝ) (hb : ∀ v w, b v w = b w v)
    (hpos : ∀ v, v ≠ 0 → 0 < b v v) (x : M) :
    (const (I := I) (n := n) b hb hpos).inner x = b :=
  (rfl)

section Complex

variable (ι : Type*) [Fintype ι]

/-- The constant metric on the trivial bundle `M × (ι → ℂ)` that
`c = TauCeti.complexToRealEuclidean ι` carries to the Euclidean one, `g₀(u, v) = ⟪c u, c v⟫`:
the real part of the standard Hermitian product. -/
def constComplexEuclidean : ContMDiffRiemannianMetric I n (ι → ℂ) (Trivial M (ι → ℂ)) :=
  const ((innerSL ℝ).bilinearComp (TauCeti.complexToRealEuclidean ι).toContinuousLinearMap
      (TauCeti.complexToRealEuclidean ι).toContinuousLinearMap)
    (fun u v ↦ by simp only [ContinuousLinearMap.bilinearComp_apply, innerSL_apply_apply,
      real_inner_comm])
    (fun u hu ↦ by
      rw [ContinuousLinearMap.bilinearComp_apply, innerSL_apply_apply]
      exact real_inner_self_pos.2 ((TauCeti.complexToRealEuclidean ι).map_ne_zero_iff.2 hu))

/-- The metric `constComplexEuclidean ι` is `g₀(u, v) = ⟪c u, c v⟫` on every fibre, for
`c = TauCeti.complexToRealEuclidean ι`. -/
@[simp]
theorem constComplexEuclidean_inner (x : M) (u v : ι → ℂ) :
    (constComplexEuclidean (I := I) (n := n) ι).inner x u v =
      Inner.inner ℝ (TauCeti.complexToRealEuclidean ι u) (TauCeti.complexToRealEuclidean ι v) :=
  (rfl)

end Complex

end Bundle.ContMDiffRiemannianMetric

end
