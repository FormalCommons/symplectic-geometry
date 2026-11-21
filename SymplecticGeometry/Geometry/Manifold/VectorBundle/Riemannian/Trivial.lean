/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import TauCeti.Geometry.Manifold.VectorBundle.Hom
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

end Bundle.ContMDiffRiemannianMetric

end
