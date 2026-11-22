/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Circle.FreeLoop.Basic

/-!
# The degree of a composite of circle maps

The degree of a composite of self-maps of the circle is the product of their degrees
(`ContinuousMap.circleDegree_comp`). So the degree of the image of a loop `γ` in the circle under
a map `g : S¹ → S¹` is the degree of `g` times the degree of `γ` (`Circle.degree_map`).

The proof uses Tau Ceti's classification of free loops of the circle by their degree
(`Circle.joined_iff_circleDegree_eq`): each map is joined to `w ↦ z * w ^ n`, and composition
is continuous in both maps.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §1.1 (the fundamental
  group of the circle) and §2.2 (degree of a map of spheres).
-/

public section

open scoped unitInterval

namespace ContinuousMap

/-- **The degree is multiplicative under composition.** The degree of `g ∘ f` is the product of
the degrees of `g` and `f`. -/
theorem circleDegree_comp (g f : C(Circle, Circle)) :
    (g.comp f).circleDegree = g.circleDegree * f.circleDegree := by
  -- Each map is joined to its normal form `w ↦ z * w ^ n`.
  obtain ⟨γ⟩ : Joined g (Circle.freeLoopHomotopyEquiv.symm (g.circleDegree, g 1)) :=
    Circle.joined_iff_circleDegree_eq.2 (by simp)
  obtain ⟨δ⟩ : Joined f (Circle.freeLoopHomotopyEquiv.symm (f.circleDegree, 1)) :=
    Circle.joined_iff_circleDegree_eq.2 (by simp)
  have h := Circle.joined_iff_circleDegree_eq.1
    ⟨(δ.prod γ).map (continuous_comp' (X := Circle) (Y := Circle) (Z := Circle))⟩
  have hnf : (Circle.freeLoopHomotopyEquiv.symm (g.circleDegree, g 1)).comp
      (Circle.freeLoopHomotopyEquiv.symm (f.circleDegree, 1)) =
        Circle.freeLoopHomotopyEquiv.symm (g.circleDegree * f.circleDegree, g 1) := by
    ext w
    simp [← zpow_mul, mul_comm]
  simpa [hnf] using h

end ContinuousMap

namespace Circle

/-- The degree of the image of a loop `γ` in the circle under a map `g : S¹ → S¹` is the degree
of `g` times the degree of `γ`. -/
theorem degree_map {x : Circle} (γ : Path x x) (g : C(Circle, Circle)) :
    degree (γ.map g.continuous) = g.circleDegree * degree γ := by
  have h : (γ.map g.continuous).toCircle = g.comp γ.toCircle := by
    ext z
    obtain ⟨t, rfl⟩ := TauCeti.unitToCircle_surjective z
    simp [Path.toCircle_unitToCircle]
  rw [← ContinuousMap.circleDegree_toCircle, h, ContinuousMap.circleDegree_comp,
    ContinuousMap.circleDegree_toCircle]

end Circle

end
