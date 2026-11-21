/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Circle.NotSimplyConnected
public import TauCeti.Topology.Homotopy.Path

/-!
# Maps to the circle and the fundamental group

The fundamental group of the unit circle is nontrivial (`Circle.nontrivial_fundamentalGroup`,
from `π₁(S¹) ≅ ℤ`). So no continuous map `f : X → S¹` out of a space whose fundamental group at
`x` is trivial can be surjective on `π₁`, whatever `f` is.

This is how the isomorphisms `π₁(U(n)) ≅ π₁(S¹)`, induced by the determinant, and
`π₁(Sp(2n)) ≅ π₁(S¹)`, induced by the Maslov phase, fail for `n = 0`: there the groups are a
point.

Conversely, when `d : X → S¹` is injective on `π₁`, a path in `X` is determined up to homotopy
by the angle change (`Circle.angleChange`) of its image: if two paths with the same ends have
images with the same angle change, then one followed by the reverse of the other is a loop whose
image has degree zero, hence a null-homotopic loop.

## Main results

* `FundamentalGroup.not_surjective_map_circle_of_subsingleton`: if `π₁(X, x)` is trivial, then
  no continuous map `X → S¹` is surjective on `π₁` at `x`.
* `Circle.homotopic_iff_angleChange_map_eq`: if `d : X → S¹` is injective on `π₁` at `x`, then
  two paths from `x` with the same ends are homotopic iff their images have the same angle change.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Theorem 1.7
  (`π₁(S¹) ≅ ℤ`).
-/

public section

namespace FundamentalGroup

/-- If the fundamental group of `X` at `x` is trivial, then no continuous map `f : X → S¹`
induces a surjection `π₁(X, x) → π₁(S¹, f x)`, since `π₁(S¹) ≅ ℤ` is nontrivial. -/
theorem not_surjective_map_circle_of_subsingleton {X : Type*} [TopologicalSpace X] (x : X)
    [Subsingleton (FundamentalGroup X x)] (f : C(X, Circle)) :
    ¬ Function.Surjective (FundamentalGroup.map f x) := fun h ↦
  have := Circle.nontrivial_fundamentalGroup (f x)
  not_subsingleton _ h.subsingleton

end FundamentalGroup

namespace Circle

/-- **Paths are classified by the angle change of their image.** If a continuous map
`d : X → S¹` induces an injection `π₁(X, x) → π₁(S¹, d x)`, then two paths `δ`, `δ'` from `x` to
`y` are homotopic relative to their ends exactly when `d ∘ δ` and `d ∘ δ'` have the same angle
change. -/
theorem homotopic_iff_angleChange_map_eq {X : Type*} [TopologicalSpace X] {d : C(X, Circle)}
    {x y : X} (hd : Function.Injective (FundamentalGroup.map d x)) {δ δ' : Path x y} :
    δ.Homotopic δ' ↔
      angleChange (δ.map d.continuous) = angleChange (δ'.map d.continuous) := by
  refine ⟨fun h ↦ angleChange_eq_of_homotopic (h.map d), fun h ↦ ?_⟩
  -- The loop `δ δ'⁻¹` has image of degree zero, so it is null-homotopic.
  have hdeg : degree ((δ.trans δ'.symm).map d.continuous) =
      degree ((Path.refl x).map d.continuous) := by
    have h₁ := angleChange_eq_degree_mul
      ((δ.map d.continuous).trans (δ'.map d.continuous).symm)
    rw [angleChange_trans, angleChange_symm, h, add_neg_cancel, zero_eq_mul] at h₁
    rw [Path.map_trans, ← Path.map_symm, Path.map_refl, degree_refl]
    exact_mod_cast h₁.resolve_right (by positivity)
  refine .of_trans_symm ((homotopic_trans_of_degree_map_eq hd hdeg (.refl x)).trans ?_)
  exact (Path.Homotopic.refl_trans _).trans (Path.Homotopic.trans_symm _)

end Circle

end
