/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.KempfNess.Basic
public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.NormSq

/-!
# The norm square of a moment map

Let `-μ` be a moment map for `σ` of the action of `G` on `M` by fundamental vector fields, let
`J` be an almost complex structure on `M`, and let the metric be `g(u, w) = σ(u, J w)`, as in
`KempfNess/Basic.lean`. For a nondegenerate symmetric bilinear form `B` on the Lie algebra, this
file studies the norm square `‖μ‖² = momentNormSq B hB μ`, whose negative gradient flow drives a
point of `M` towards the zero set of `μ` inside its orbit under the complexified group.

## Main results

* `SymplecticGeometry.mgradient_momentNormSq`: the gradient of `‖μ‖²` at `x` is
  `-2 J X_{μ♯ x}(x)`, with `X_ξ` the fundamental vector field of `ξ` and `μ♯ x` the vector dual
  to `μ x` under `B`.

The gradient is computed from the derivative `SymplecticGeometry.mvfderiv_momentNormSq`, twice
that of the component `y ↦ μ y (μ♯ x)`, and the gradient `-J X_ξ` of the component `y ↦ μ y ξ`
(`SymplecticGeometry.mgradient_moment_apply`), taken at `ξ = μ♯ x`. No `Ad`-invariance of `B`
and no nondegeneracy of `σ` are used. With the norm square normalized as `½ ‖μ‖²` instead, the
gradient is `-J X_{μ♯ x}(x)`.

## References

* [V. Georgoulas, J. W. Robbin and D. A. Salamon, *The Moment-Weight Inequality and the
  Hilbert–Mumford Criterion*][GeorgoulasRobbinSalamon2021].
-/

public section

noncomputable section

open _root_.Bundle Manifold TauCeti
open scoped Manifold ContDiff RealInnerProductSpace

namespace SymplecticGeometry

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M]
  [MulAction G M] [ContMDiffSMul I I' ∞ G M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I' x)]
  {σ : SmoothTwoForm I' M} {J : SmoothAlmostComplexStructure I' M}
  {B : LinearMap.BilinForm ℝ (GroupLieAlgebra I G)} {hB : B.Nondegenerate}
  {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}

/-- **The gradient of the norm square of a moment map.** Let `-μ` be a moment map for `σ` of the
action of `G` by fundamental vector fields, let the metric be `g(u, w) = σ(u, J w)`, and let `B`
be a nondegenerate symmetric form on the Lie algebra. Then the gradient of the norm square
`x ↦ ‖μ x‖²` is `-2 J X_{μ♯ x}`, where `μ♯ x` is the vector dual to `μ x` under `B` and `X_ξ` is
the fundamental vector field of `ξ`. -/
theorem mgradient_momentNormSq
    (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w)) (hBs : B.IsSymm)
    (x : M) :
    Manifold.mgradient I' (momentNormSq B hB μ) x =
      (-2 : ℝ) • J x (fundamentalVectorField I' (momentSharp B hB μ x) x) := by
  have hd (ξ : GroupLieAlgebra I G) : MDifferentiableAt I' 𝓘(ℝ) (fun y ↦ μ y ξ) x := by
    convert (hμ.mdifferentiableAt ξ x).neg using 1
    ext y
    simp
  rw [neg_smul, ← smul_neg, ← mgradient_moment_apply hμ hg]
  refine ext_inner_right ℝ fun v ↦ ?_
  rw [Manifold.inner_mgradient, mvfderiv_momentNormSq hBs hd, real_inner_smul_left,
    Manifold.inner_mgradient, smul_apply, smul_eq_mul]

end SymplecticGeometry

end
