/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Smooth.Basic

/-!
# The paired wedge for an antisymmetric pairing

Tau Ceti's `TauCeti.SmoothForm.wedgeWith_comm` says that the paired wedge of smooth forms is
graded-commutative when the coefficient pairing `μ` is symmetric. When `μ` is antisymmetric, as a
Lie bracket is, the same holds with one more sign
(`TauCeti.SmoothForm.wedgeWith_comm_of_anticomm`). In particular the paired wedge of two one-forms
is then symmetric (`TauCeti.SmoothForm.wedgeWith_one_one_comm_of_anticomm`).

The proof follows Tau Ceti's `TauCeti.SmoothForm.wedgeWith_comm`, through
`TauCeti.SmoothForm.wedgeWith_flip`, with `μ.flip = -μ` in place of `μ.flip = μ`.

## Main results

* `TauCeti.SmoothForm.wedgeWith_comm_of_anticomm`: for an antisymmetric pairing `μ`,
  `φ ∧_μ ψ = -(-1) ^ (k l) ψ ∧_μ φ`.
* `TauCeti.SmoothForm.wedgeWith_one_one_comm_of_anticomm`: for an antisymmetric pairing `μ` and
  one-forms `φ`, `ψ`, `φ ∧_μ ψ = ψ ∧_μ φ`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 14.
-/

public section

open scoped ContDiff Manifold

namespace TauCeti.SmoothForm

variable {E H M F₁ F₃ : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [NormedAddCommGroup F₃] [NormedSpace ℝ F₃]
  [IsManifold I 1 M] {k l : ℕ}

/-- For an antisymmetric pairing `μ`, such as a Lie bracket, the paired wedge is graded-commutative
up to one more sign: `φ ∧_μ ψ = -(-1) ^ (k l) ψ ∧_μ φ`, the arguments reordered by
`Fin.cast (Nat.add_comm l k)`. -/
theorem wedgeWith_comm_of_anticomm (μ : F₁ →L[ℝ] F₁ →L[ℝ] F₃)
    (hμ : ∀ a b, μ a b = -μ b a) (φ : SmoothForm I M F₁ k) (ψ : SmoothForm I M F₁ l)
    (x : M) (v : Fin (k + l) → TangentSpace I x) :
    (wedgeWith μ φ ψ).val x v =
      -((-1 : ℝ) ^ (k * l) • (wedgeWith μ ψ φ).val x (v ∘ Fin.cast (Nat.add_comm l k))) := by
  have hflip : μ.flip = -μ := by
    ext a b
    simp [hμ b a]
  rw [wedgeWith_flip, hflip, wedgeWith_apply, wedgeWith_apply]
  simp [Finset.smul_sum, Finset.sum_neg_distrib]

/-- For an antisymmetric pairing `μ`, such as a Lie bracket, the paired wedge of two one-forms is
symmetric: `φ ∧_μ ψ = ψ ∧_μ φ`. -/
theorem wedgeWith_one_one_comm_of_anticomm (μ : F₁ →L[ℝ] F₁ →L[ℝ] F₃)
    (hμ : ∀ a b, μ a b = -μ b a) (φ ψ : SmoothForm I M F₁ 1) :
    wedgeWith μ φ ψ = wedgeWith μ ψ φ := by
  refine Subtype.ext (funext fun x ↦ ContinuousAlternatingMap.ext fun v ↦ ?_)
  rw [wedgeWith_comm_of_anticomm μ hμ]
  simp

end TauCeti.SmoothForm

end
