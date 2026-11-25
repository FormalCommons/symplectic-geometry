/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Leibniz

/-!
# The Leibniz rule for the paired wedge of a zero-form and a one-form

For a continuous bilinear pairing `μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃`, a smooth `F₁`-valued zero-form `f`
and a smooth `F₂`-valued one-form `α`, the exterior derivative of the paired wedge `f ∧_μ α`,
evaluated on two tangent vectors, is

  `d (f ∧_μ α)(v, w) = μ (df v) (α w) - μ (df w) (α v) + μ (f x) (dα (v, w))`

(`TauCeti.SmoothForm.mextDeriv_wedgeWith_zero_one_apply`). This is Tau Ceti's Leibniz rule
`TauCeti.SmoothForm.mextDeriv_wedgeWith_apply` in degrees `0` and `1`, with the tuples of
tangent vectors that it reindexes by `Fin.cast` written as `![v, w]`.

The proof follows the one of Tau Ceti's `TauCeti.mextDeriv_fun_smul_apply`, which is the case of
real-valued forms paired by multiplication: it first rewrites the reindexed tuples to `![v, w]`
and then evaluates the two wedges.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Proposition 14.23.
-/

public section

open scoped ContDiff Manifold

namespace TauCeti.SmoothForm

variable {E H M F₁ F₂ F₃ : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  [NormedAddCommGroup F₃] [NormedSpace ℝ F₃] [IsManifold I 1 M]

/-- The Leibniz rule for the paired wedge `f ∧_μ α` of a smooth zero-form `f` and a smooth
one-form `α`, evaluated on two tangent vectors `v`, `w` at `x`:
`d (f ∧_μ α)(v, w) = μ (df v) (α w) - μ (df w) (α v) + μ (f x) (dα (v, w))`. -/
theorem mextDeriv_wedgeWith_zero_one_apply (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (f : SmoothForm I M F₁ 0) (α : SmoothForm I M F₂ 1) (x : M) (v w : TangentSpace I x) :
    mextDeriv (RoughForm.wedgeWith μ f.val α.val) x ![v, w] =
      μ (mextDeriv f.val x ![v]) (α.val x ![w]) - μ (mextDeriv f.val x ![w]) (α.val x ![v]) +
        μ (f.val x 0) (mextDeriv α.val x ![v, w]) := by
  have hvw : ∀ h : 0 + 1 + 1 = 0 + 1 + 1,
      (![v, w] ∘ Fin.cast h : Fin (0 + 1 + 1) → TangentSpace I x) = ![v, w] :=
    fun _ ↦ funext fun i ↦ by fin_cases i <;> rfl
  rw [mextDeriv_wedgeWith_apply, hvw, RoughForm.wedgeWith_apply_one_one, pow_zero, one_smul,
    RoughForm.wedgeWith_apply', ContinuousAlternatingMap.pairedWedge_apply_zero_left, hvw]

end TauCeti.SmoothForm

end
