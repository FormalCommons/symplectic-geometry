/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Trivial
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
public import TauCeti.Geometry.Manifold.DifferentialForm.VectorField
public import TauCeti.Geometry.Symplectic.Manifold.Flat

/-!
# The exterior derivative of a two-form through a connection

Let `∇` be a connection on the tangent bundle of a manifold, with torsion `T`, and let `σ` be a
smooth real two-form. Its covariant derivative `∇σ` is the derivative of the field of bilinear
maps `σ♭ = TauCeti.SmoothTwoForm.flat σ` for the connection induced by `∇` on
`Hom(TM, Hom(TM, ℝ))`, that is `covT.hom (covT.hom (CovariantDerivative.trivial ℝ)) σ.flat`.
This file expresses the exterior derivative through it:

`dσ(u, v, w) = (∇_u σ)(v, w) + (∇_v σ)(w, u) + (∇_w σ)(u, v)`
`  + σ(T(u, v), w) + σ(T(v, w), u) + σ(T(w, u), v)`.

## Main results

* `CovariantDerivative.mextDeriv_smoothTwoForm`: the formula above, for any connection.
* `CovariantDerivative.mextDeriv_smoothTwoForm_of_torsion_eq_zero`: at a point where the
  torsion vanishes, `dσ` is the cyclic sum of `∇σ`.

These are the two-form analogues of Tau Ceti's `CovariantDerivative.mextDeriv_ofSubsingleton`
and `CovariantDerivative.mextDeriv_ofSubsingleton_of_torsion_eq_zero` for one-forms, and their
proofs adapt those two proofs (in
`TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.ExteriorDerivative`) from one-forms to
two-forms: extend the tangent vectors to smooth vector fields, expand both sides through the
fields and the torsion, compare with the invariant formula
`TauCeti.SmoothForm.mextDeriv_apply_two`, and for the torsion-free case drop the torsion terms.
The general proof finishes as Tau Ceti's private `exteriorTwoValue_apply`, behind
`CovariantDerivative.exteriorCovariantDerivativeTwo_apply`, does: it swaps the arguments of the
terms `σ(·, ∇·)` and collects terms. It also follows the steps of
`CovariantDerivative.exteriorCovariantDerivativeTwo_apply` and of its private lemma
`hom_twoFormTensor_apply` (in
`TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Exterior.Two`), here for scalar
two-forms and the ordinary exterior derivative.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  proof of Lemma 4.1.14.
-/

public section

noncomputable section

open Bundle FiberBundle
open scoped ContDiff Manifold

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  (covT : CovariantDerivative I E (TangentSpace I : M → Type _))

/-- The exterior derivative of a smooth two-form `σ`, through a connection `∇` on the tangent
bundle with torsion `T`: `dσ(u, v, w)` is the cyclic sum of `(∇_u σ)(v, w) + σ(T(u, v), w)`. -/
theorem mextDeriv_smoothTwoForm (σ : TauCeti.SmoothTwoForm I M) (x : M)
    (u v w : TangentSpace I x) :
    TauCeti.mextDeriv σ.val x ![u, v, w] =
      covT.hom (covT.hom (trivial ℝ)) σ.flat x u v w +
        covT.hom (covT.hom (trivial ℝ)) σ.flat x v w u +
        covT.hom (covT.hom (trivial ℝ)) σ.flat x w u v +
        σ.eval₂ x (covT.torsion x u v) w + σ.eval₂ x (covT.torsion x v w) u +
        σ.eval₂ x (covT.torsion x w u) v := by
  have hs (y : M) (a b : TangentSpace I y) : σ.flat y a b = -σ.flat y b a := by
    simpa only [TauCeti.SmoothTwoForm.flat_apply] using σ.eval₂_swap y a b
  -- Extend the vectors to fields, and expand both sides through them.
  have hU := mdifferentiableAt_extend I E u
  have hV := mdifferentiableAt_extend I E v
  have hW := mdifferentiableAt_extend I E w
  have hσ := σ.contMDiff_flat.mdifferentiableAt (x := x) (by simp)
  have hd := TauCeti.SmoothForm.mextDeriv_apply_two (φ := σ) hU hV hW
  have h₁ := covT.hom_hom_apply covT (trivial ℝ) hσ hV hW u
  have h₂ := covT.hom_hom_apply covT (trivial ℝ) hσ hW hU v
  have h₃ := covT.hom_hom_apply covT (trivial ℝ) hσ hU hV w
  have hT₁ := covT.torsion_apply hU hV
  have hT₂ := covT.torsion_apply hV hW
  have hT₃ := covT.torsion_apply hW hU
  simp only [extend_apply_self] at hd h₁ h₂ h₃ hT₁ hT₂ hT₃
  rw [hd, h₁, h₂, h₃, hT₁, hT₂, hT₃]
  -- Write every term through `σ.flat`, with the fields and brackets in the same order.
  have hWU : (fun y ↦ σ.flat y (extend E w y) (extend E u y)) =
      -fun y ↦ σ.flat y (extend E u y) (extend E w y) := funext fun y ↦ hs y _ _
  rw [hWU, VectorField.mlieBracket_swap_apply (V := extend E w), hs x v (covT (extend E w) x u),
    hs x w (covT (extend E u) x v), hs x u (covT (extend E v) x w)]
  simp only [trivial_apply, mvfderiv_neg, ← TauCeti.SmoothBundleForm.eval₂_apply,
    ← TauCeti.SmoothTwoForm.flat_apply, map_sub, map_neg, sub_apply, neg_apply]
  abel

/-- At a point where a connection `∇` on the tangent bundle is torsion free, the exterior
derivative of a smooth two-form `σ` is the cyclic sum of its covariant derivative:
`dσ(u, v, w) = (∇_u σ)(v, w) + (∇_v σ)(w, u) + (∇_w σ)(u, v)`. -/
theorem mextDeriv_smoothTwoForm_of_torsion_eq_zero (σ : TauCeti.SmoothTwoForm I M) {x : M}
    (ht : covT.torsion x = 0) (u v w : TangentSpace I x) :
    TauCeti.mextDeriv σ.val x ![u, v, w] =
      covT.hom (covT.hom (trivial ℝ)) σ.flat x u v w +
        covT.hom (covT.hom (trivial ℝ)) σ.flat x v w u +
        covT.hom (covT.hom (trivial ℝ)) σ.flat x w u v := by
  simp only [covT.mextDeriv_smoothTwoForm, ht, zero_apply, ← TauCeti.SmoothTwoForm.flat_apply,
    map_zero, add_zero]

end CovariantDerivative
