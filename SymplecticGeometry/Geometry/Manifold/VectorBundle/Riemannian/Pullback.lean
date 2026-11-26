/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import TauCeti.Topology.VectorBundle.Pullback
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Pullback

/-!
# Pulling back a smooth bundle metric along a map of bases

Let `V` be a real vector bundle over `B` with a `C^n` metric `g`, and let `f : X → B` be a `C^n`
map. The fibre of Tau Ceti's pull-back bundle `f *ᵖ V` over `x` is `V (f x)`, and giving it the
inner product `g.inner (f x)` defines a `C^n` metric on `f *ᵖ V`:
`Bundle.ContMDiffRiemannianMetric.pullbackBase g f hf`. Its smoothness is the library's
`Bundle.Pullback.contMDiff_bilinear_section_iff`, applied to the `C^n` map
`x ↦ ⟨f x, g.inner (f x)⟩`, which is the section `g.contMDiff` composed with `f`. No rank or
smooth-bundle assumption on `V` is needed. The construction follows that of Tau Ceti's
`Bundle.ContMDiffRiemannianMetric.pullbackBundleEquiv`, which pulls a metric back along a field of
fibre isomorphisms over the identity of the base.

## Main definitions and results

* `Bundle.ContMDiffRiemannianMetric.pullbackBase`: the metric `f^* g` on `f *ᵖ V`.
* `Bundle.ContMDiffRiemannianMetric.pullbackBase_inner`: on the fibre over `x`, the inner product
  of `f^* g` is `g.inner (f x)`.
* `Bundle.ContMDiffRiemannianMetric.pullbackBase_inner_smul_I`: for a complex bundle, if `g` is
  invariant under multiplication by `i`, so is `f^* g`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer (2013), Chapters 10 and 13.
-/

public section

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace Bundle.ContMDiffRiemannianMetric

variable {B X F K EB HB EX HX : Type*}
  [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
  {IX : ModelWithCorners ℝ EX HX} [TopologicalSpace X] [ChartedSpace HX X]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {V : B → Type*}
  [∀ b, AddCommGroup (V b)] [∀ b, Module ℝ (V b)] [∀ b, TopologicalSpace (V b)]
  [∀ b, IsTopologicalAddGroup (V b)] [∀ b, ContinuousConstSMul ℝ (V b)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  [FunLike K X B] [ContinuousMapClass K X B] {n : ℕ∞ω}

/-- The pull-back `f^* g` of a `C^n` metric `g` on `V` along a `C^n` map `f : X → B`: the `C^n`
metric on the pull-back bundle `f *ᵖ V` whose inner product on the fibre `V (f x)` over `x` is
`g.inner (f x)`. -/
def pullbackBase (g : ContMDiffRiemannianMetric IB n F V) (f : K) (hf : ContMDiff IX IB n f) :
    ContMDiffRiemannianMetric IX n F ((f : X → B) *ᵖ V) where
  inner x := g.inner (f x)
  symm x := g.symm (f x)
  pos x := g.pos (f x)
  isVonNBounded x := g.isVonNBounded (f x)
  contMDiff := (Pullback.contMDiff_bilinear_section_iff f hf fun x ↦ g.inner (f x)).2
    (g.contMDiff.comp hf)

omit [∀ b, IsTopologicalAddGroup (V b)] [∀ b, ContinuousConstSMul ℝ (V b)] in
/-- On the fibre of `f *ᵖ V` over `x`, which is `V (f x)`, the inner product of the pulled-back
metric `f^* g` is that of `g` at `f x`. -/
@[simp]
theorem pullbackBase_inner (g : ContMDiffRiemannianMetric IB n F V) (f : K)
    (hf : ContMDiff IX IB n f) (x : X) (v w : ((f : X → B) *ᵖ V) x) :
    (g.pullbackBase f hf).inner x v w = g.inner (f x) v w :=
  (rfl)

omit [∀ b, IsTopologicalAddGroup (V b)] [∀ b, ContinuousConstSMul ℝ (V b)] in
/-- For a complex vector bundle `V`, if the metric `g` is invariant under multiplication by `i`
on every fibre, then so is its pull-back `f^* g` along `f`. -/
theorem pullbackBase_inner_smul_I [∀ b, Module ℂ (V b)]
    (g : ContMDiffRiemannianMetric IB n F V)
    (hI : ∀ b (v w : V b), g.inner b (Complex.I • v) (Complex.I • w) = g.inner b v w)
    (f : K) (hf : ContMDiff IX IB n f) (x : X) (v w : ((f : X → B) *ᵖ V) x) :
    (g.pullbackBase f hf).inner x (Complex.I • v) (Complex.I • w) =
      (g.pullbackBase f hf).inner x v w := by
  rw [pullbackBase_inner, pullbackBase_inner]
  exact hI (f x) v w

end Bundle.ContMDiffRiemannianMetric
