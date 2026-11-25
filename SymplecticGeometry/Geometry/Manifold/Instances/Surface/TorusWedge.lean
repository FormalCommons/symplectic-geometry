/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Instances.AddCircle.Real
public import TauCeti.AlgebraicTopology.FundamentalGroup.Homeomorph
public import TauCeti.AlgebraicTopology.FundamentalGroup.WedgeSum
import SymplecticGeometry.Topology.WedgeSum

/-!
# The two circles of the torus through `0` form a wedge of two circles

On the torus `Fin 2 → AddCircle 1`, the set `SymplecticGeometry.torusCircles` is the union of the
two circles `{x | x 1 = 0}` and `{x | x 0 = 0}` through the base point `0`. This file identifies
it with Tau Ceti's wedge of two circles `TauCeti.WedgeSum fun _ : Fin 2 => (1 : Circle)`, the
`i`-th circle `Circle` going to the points `Pi.single i [s]`, along Mathlib's homeomorphism
`AddCircle.homeomorphCircle` of `AddCircle 1` with `Circle`. The map out of the wedge is
`TauCeti.WedgeSum.lift`; its coordinates are those of `TauCeti.WedgeSum.proj`, so it is injective
by `TauCeti.WedgeSum.proj_injective`. The wedge is compact
(`TauCeti.WedgeSum.compactSpace`) and the torus is Hausdorff, so this continuous bijection is a
homeomorphism (`Continuous.homeoOfEquivCompactToT2`).

Through Tau Ceti's `TauCeti.WedgeSum.circleFundamentalGroupMulEquiv`, the fundamental group of
`torusCircles` at `0` is then the free group on `Fin 2`, and the loop
`SymplecticGeometry.torusCircleLoop i`, `t ↦ Pi.single i [t]`, which goes once around the `i`-th
circle, is the generator `FreeGroup.of i`: it is the image of Tau Ceti's `Circle.expLoop` in the
`i`-th circle of the wedge, for which `TauCeti.WedgeSum.circleFundamentalGroupMulEquiv_expLoop`
gives that value.

## Main definitions

* `SymplecticGeometry.torusCircles`: the union of the two circles of the torus through `0`.
* `SymplecticGeometry.torusCircleLoop i`: the loop `t ↦ Pi.single i [t]` around its `i`-th
  circle.
* `SymplecticGeometry.torusCirclesHomeomorph`: the homeomorphism from the wedge of two circles
  onto `torusCircles`.
* `SymplecticGeometry.torusCirclesFundamentalGroupMulEquiv`: the fundamental group of
  `torusCircles` at `0` is the free group on `Fin 2`.

## Main results

* `SymplecticGeometry.torusCirclesFundamentalGroupMulEquiv_torusCircleLoop`: it sends the class
  of `torusCircleLoop i` to `FreeGroup.of i`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 1.2, Example 1.21: the fundamental group of a wedge of circles.
* [R. E. Gompf, *A new construction of symplectic manifolds*][Gompf1995] (the closed surfaces of
  genus `g`, whose tori these circles generate).
-/

public section

noncomputable section

open Set Topology TauCeti unitInterval

namespace SymplecticGeometry

/-- The union of the two circles `{x | x 0 = 0}` and `{x | x 1 = 0}` of the torus
`Fin 2 → AddCircle 1` through its base point `0`. -/
def torusCircles : Set (Fin 2 → AddCircle (1 : ℝ)) :=
  {x | x 0 = 0} ∪ {x | x 1 = 0}

@[simp]
theorem mem_torusCircles_iff {x : Fin 2 → AddCircle (1 : ℝ)} :
    x ∈ torusCircles ↔ x 0 = 0 ∨ x 1 = 0 :=
  Iff.rfl

/-- Every point `Pi.single i s`, with all coordinates but the `i`-th equal to `0`, lies in
`torusCircles`. -/
theorem single_mem_torusCircles (i : Fin 2) (s : AddCircle (1 : ℝ)) :
    Pi.single i s ∈ torusCircles := by
  fin_cases i <;> simp

/-- The base point `0` of the torus lies in `torusCircles`. -/
theorem zero_mem_torusCircles : (0 : Fin 2 → AddCircle (1 : ℝ)) ∈ torusCircles := by
  simp

/-- The loop `t ↦ Pi.single i [t]` of `torusCircles` at `0`, which goes once around its `i`-th
circle: for `i = 0` the loop `t ↦ ([t], 0)`, for `i = 1` the loop `t ↦ (0, [t])`. -/
def torusCircleLoop (i : Fin 2) :
    Path (⟨0, zero_mem_torusCircles⟩ : torusCircles) ⟨0, zero_mem_torusCircles⟩ where
  toFun t := ⟨Pi.single i ((t : ℝ) : AddCircle (1 : ℝ)), single_mem_torusCircles i _⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ((continuous_single i).comp ?_) _
    exact (AddCircle.continuous_mk' 1).comp continuous_subtypeVal
  source' := by ext1; simp
  target' := by ext1; simp [AddCircle.coe_period]

@[simp]
theorem coe_torusCircleLoop_apply (i : Fin 2) (t : I) :
    (torusCircleLoop i t : Fin 2 → AddCircle (1 : ℝ)) =
      Pi.single i ((t : ℝ) : AddCircle (1 : ℝ)) :=
  (rfl)

/-- The homeomorphism of `Circle` with `AddCircle 1`, used for the circles of the wedge. -/
private abbrev circleEquiv : Circle ≃ₜ AddCircle (1 : ℝ) :=
  (AddCircle.homeomorphCircle one_ne_zero).symm

/-- The inclusion of the `i`-th circle into the wedge of two circles. -/
local notation "inclW" => WedgeSum.incl (fun _ : Fin 2 => (1 : Circle))

/-- The map from the `i`-th circle of the wedge into `torusCircles`, `z ↦ Pi.single i [s]` for
`z = exp (2 π s)`. -/
private def circleIncl (i : Fin 2) : C(Circle, torusCircles) :=
  ⟨fun z => ⟨Pi.single i (circleEquiv z), single_mem_torusCircles i _⟩,
    ((continuous_single i).comp circleEquiv.continuous).subtype_mk _⟩

private theorem circleIncl_one (i : Fin 2) :
    circleIncl i 1 = ⟨0, zero_mem_torusCircles⟩ := by
  ext1
  simp [circleIncl]

/-- The map from the wedge of two circles into `torusCircles`. -/
private def wedgeToTorusCircles :
    C(WedgeSum fun _ : Fin 2 => (1 : Circle), torusCircles) :=
  WedgeSum.lift circleIncl _ circleIncl_one

/-- The `j`-th coordinate of the image of `w` is `circleEquiv` of the projection of `w` onto the
`j`-th circle. -/
private theorem coe_wedgeToTorusCircles_apply (w : WedgeSum fun _ : Fin 2 => (1 : Circle))
    (j : Fin 2) :
    (wedgeToTorusCircles w : Fin 2 → AddCircle (1 : ℝ)) j =
      circleEquiv (WedgeSum.proj _ j w) := by
  induction w using WedgeSum.ind with
  | base => simp [wedgeToTorusCircles, WedgeSum.proj_base]
  | incl i z =>
    simp only [wedgeToTorusCircles, WedgeSum.lift_incl, circleIncl, ContinuousMap.coe_mk]
    by_cases hij : j = i
    · subst hij
      simp [WedgeSum.proj_incl_self]
    · simp [Pi.single_eq_of_ne hij, WedgeSum.proj_incl_of_ne (Ne.symm hij)]

private theorem wedgeToTorusCircles_injective : Function.Injective wedgeToTorusCircles :=
  fun a b h => WedgeSum.proj_injective <| funext fun j => circleEquiv.injective <| by
    rw [← coe_wedgeToTorusCircles_apply, ← coe_wedgeToTorusCircles_apply, h]

private theorem wedgeToTorusCircles_surjective : Function.Surjective wedgeToTorusCircles := by
  rintro ⟨x, hx | hx⟩
  · refine ⟨inclW 1 (circleEquiv.symm (x 1)), ?_⟩
    ext1
    simp only [wedgeToTorusCircles, WedgeSum.lift_incl, circleIncl, ContinuousMap.coe_mk,
      Homeomorph.symm_symm, Homeomorph.symm_apply_apply]
    ext j
    fin_cases j <;> simp_all
  · refine ⟨inclW 0 (circleEquiv.symm (x 0)), ?_⟩
    ext1
    simp only [wedgeToTorusCircles, WedgeSum.lift_incl, circleIncl, ContinuousMap.coe_mk,
      Homeomorph.symm_symm, Homeomorph.symm_apply_apply]
    ext j
    fin_cases j <;> simp_all

/-- The homeomorphism from Tau Ceti's wedge of two circles onto `torusCircles`: the wedge point
goes to `0`, and the point `z = exp (2 π s)` of the `i`-th circle to `Pi.single i [s]`. -/
def torusCirclesHomeomorph : (WedgeSum fun _ : Fin 2 => (1 : Circle)) ≃ₜ torusCircles :=
  wedgeToTorusCircles.continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective _ ⟨wedgeToTorusCircles_injective, wedgeToTorusCircles_surjective⟩)

private theorem torusCirclesHomeomorph_apply (w : WedgeSum fun _ : Fin 2 => (1 : Circle)) :
    torusCirclesHomeomorph w = wedgeToTorusCircles w :=
  (rfl)

@[simp]
theorem torusCirclesHomeomorph_base :
    torusCirclesHomeomorph (WedgeSum.base _) = ⟨0, zero_mem_torusCircles⟩ := by
  simp [torusCirclesHomeomorph_apply, wedgeToTorusCircles]

/-- The homeomorphism sends the point `z` of the `i`-th circle to `Pi.single i s`, where
`AddCircle.toCircle s = z`. -/
@[simp]
theorem coe_torusCirclesHomeomorph_incl (i : Fin 2) (z : Circle) :
    (torusCirclesHomeomorph (inclW i z) : Fin 2 → AddCircle (1 : ℝ)) =
      Pi.single i ((AddCircle.homeomorphCircle one_ne_zero).symm z) := by
  simp [torusCirclesHomeomorph_apply, wedgeToTorusCircles, circleIncl]

/-- The **fundamental group of the two circles of the torus through `0`** is the free group on
`Fin 2`, through the homeomorphism `torusCirclesHomeomorph` with the wedge of two circles. -/
def torusCirclesFundamentalGroupMulEquiv :
    FundamentalGroup torusCircles ⟨0, zero_mem_torusCircles⟩ ≃* FreeGroup (Fin 2) :=
  (FundamentalGroup.homeomorphMulEquivOfEq torusCirclesHomeomorph
    torusCirclesHomeomorph_base).symm.trans (WedgeSum.circleFundamentalGroupMulEquiv (Fin 2))

/-- The isomorphism `torusCirclesFundamentalGroupMulEquiv` sends the class of the loop
`t ↦ Pi.single i [t]` around the `i`-th circle to the generator `i` of the free group. -/
@[simp]
theorem torusCirclesFundamentalGroupMulEquiv_torusCircleLoop (i : Fin 2) :
    torusCirclesFundamentalGroupMulEquiv
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (torusCircleLoop i))) =
      FreeGroup.of i := by
  rw [← WedgeSum.circleFundamentalGroupMulEquiv_expLoop i, torusCirclesFundamentalGroupMulEquiv,
    MulEquiv.trans_apply]
  congr 1
  rw [MulEquiv.symm_apply_eq, FundamentalGroup.homeomorphMulEquivOfEq_apply,
    FundamentalGroup.mapOfEq_comp, FundamentalGroup.mapOfEq_apply]
  rw [← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_cast]
  refine congrArg CategoryTheory.End.of (congrArg _ ?_)
  ext t
  simp [torusCirclesHomeomorph_apply, wedgeToTorusCircles, circleIncl]

end SymplecticGeometry

end
