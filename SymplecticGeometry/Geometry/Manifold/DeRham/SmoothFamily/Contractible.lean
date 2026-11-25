/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DeRham.DegreeZero
public import SymplecticGeometry.Geometry.Manifold.DeRham.GoodCover.Basic
public import SymplecticGeometry.Geometry.Manifold.DeRham.SmoothFamily.Basic
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.HomotopyOperator

/-!
# Smooth cohomology splittings of smoothly contractible manifolds

A smoothly contractible manifold `N` has a smooth cohomology splitting
(`SymplecticGeometry.SmoothCohomologySplitting.ofIsSmoothlyContractible`), one splitting that is
smooth over parameter manifolds in all universes. Let `Φ : N × [0, 1] → N` be a smooth
contraction, from the constant map at `c` to the identity, chosen once from
`IsSmoothlyContractible I N`.

* In degree zero, the space of the splitting is the space of all closed `0`-forms, which is
  finite-dimensional since `N` is connected
  (`SymplecticGeometry.IsSmoothlyContractible.connectedSpace` and the instance
  `TauCeti.finiteDimensional_closedForms_zero`), and the projection is the identity.
* In positive degree, the space is `0` and the projection is `0`.
* The primitive of a closed `(k + 1)`-form `z` is `h (Φ^* z)`, the homotopy operator after
  pullback along the contraction. By the homotopy formula, `d (h (Φ^* z)) = z - c^* z`, and the
  pullback `c^* z` along the constant map vanishes in positive degree
  (`TauCeti.SmoothForm.mpullback_const`); together they give
  `TauCeti.SmoothForm.mextDerivₗ_homotopyOperator_mpullback_of_contraction`. The primitive takes
  smooth families to smooth families by
  `SymplecticGeometry.preservesSmoothFamilies_homotopyOperator_mpullback`.

This is the base case of the Mayer–Vietoris induction over a good cover, and the smooth
dependence on families of the Poincaré lemma in the form Weil gives it [Weil1952, §2].

## Main definitions and results

* `SymplecticGeometry.SmoothCohomologySplitting.ofIsSmoothlyContractible`: the splitting of a
  smoothly contractible manifold.
* `SymplecticGeometry.SmoothCohomologySplitting.space_ofIsSmoothlyContractible_zero`,
  `space_ofIsSmoothlyContractible_succ`, `proj_ofIsSmoothlyContractible_zero`,
  `proj_ofIsSmoothlyContractible_succ` and `primitive_ofIsSmoothlyContractible`: its spaces,
  projections and primitives.
* `SymplecticGeometry.SmoothCohomologySplitting.isSmooth_ofIsSmoothlyContractible`: it is
  smooth.

## References

* [A. Weil, *Sur les théorèmes de de Rham*][Weil1952], §2 (the homotopy operator of a
  contraction).
* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], proof of
  Theorem 3.2.4.
-/

public section

open Set
open scoped Manifold ContDiff

namespace SymplecticGeometry

open TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
  [IsManifold I ∞ N]

universe uE uH uN

variable (I) in
/-- **The splitting of a contractible manifold.** The cohomology splitting of a smoothly
contractible manifold `N` given by a contraction `Φ` chosen from `h`: in degree zero its space
is that of all closed `0`-forms and its projection is the identity, in positive degree its space
and its projection are `0`, and the primitive of a closed `(k + 1)`-form `z` is `h (Φ^* z)`, the
homotopy operator after pullback along `Φ`. -/
noncomputable def SmoothCohomologySplitting.ofIsSmoothlyContractible
    (h : IsSmoothlyContractible I N) : SmoothCohomologySplitting I N :=
  have := h.connectedSpace
  have hΦ := (isSmoothlyContractible_def.mp h).choose_spec.choose_spec
  { space := fun
      | 0 => closedForms I N 0
      | _ + 1 => ⊥
    space_le_closedForms := fun
      | 0 => le_rfl
      | _ + 1 => bot_le
    finiteDimensional_space := fun
      | 0 => inferInstanceAs (FiniteDimensional ℝ (closedForms I N 0))
      | _ + 1 => inferInstanceAs (FiniteDimensional ℝ (⊥ : Submodule ℝ (SmoothForm I N ℝ _)))
    proj := fun
      | 0 => (closedForms I N 0).subtype
      | _ + 1 => 0
    proj_mem := fun
      | 0, z => z.property
      | _ + 1, _ => Submodule.zero_mem _
    proj_zero := fun _ ↦ rfl
    primitive := fun k ↦
      SmoothForm.homotopyOperator ∘ₗ SmoothForm.mpullback _ hΦ.1 ∘ₗ
        (closedForms I N (k + 1)).subtype
    mextDerivₗ_primitive := fun k z ↦ by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, Submodule.subtype_apply,
        SmoothForm.mextDerivₗ_homotopyOperator_mpullback_of_contraction hΦ.1 hΦ.2.1 hΦ.2.2
          ((mem_closedForms_iff_mextDerivₗ_eq_zero I _).mp z.property),
        LinearMap.zero_apply, sub_zero]
    eq_zero_of_mem_exactForms := by
      rintro (_ | k) s hs hex
      · rwa [exactForms_zero, Submodule.mem_bot] at hex
      · exact (Submodule.mem_bot ℝ).mp hs }

namespace SmoothCohomologySplitting

variable (I) (h : IsSmoothlyContractible I N)

/-- In degree zero, the space of `ofIsSmoothlyContractible I h` is that of all closed
`0`-forms. -/
theorem space_ofIsSmoothlyContractible_zero :
    (ofIsSmoothlyContractible I h).space 0 = closedForms I N 0 :=
  (rfl)

/-- In positive degree, the space of `ofIsSmoothlyContractible I h` is `0`. -/
theorem space_ofIsSmoothlyContractible_succ (k : ℕ) :
    (ofIsSmoothlyContractible I h).space (k + 1) = ⊥ :=
  (rfl)

/-- In degree zero, the projection of `ofIsSmoothlyContractible I h` is the inclusion of the
closed `0`-forms. -/
theorem proj_ofIsSmoothlyContractible_zero :
    (ofIsSmoothlyContractible I h).proj 0 = (closedForms I N 0).subtype :=
  (rfl)

/-- In positive degree, the projection of `ofIsSmoothlyContractible I h` is `0`. -/
theorem proj_ofIsSmoothlyContractible_succ (k : ℕ) :
    (ofIsSmoothlyContractible I h).proj (k + 1) = 0 :=
  (rfl)

/-- The primitive of `ofIsSmoothlyContractible I h` is `z ↦ h (Φ^* z)`, the homotopy operator
after pullback along the contraction `Φ` chosen from `h`. -/
theorem primitive_ofIsSmoothlyContractible (k : ℕ) :
    (ofIsSmoothlyContractible I h).primitive k =
      SmoothForm.homotopyOperator ∘ₗ
        SmoothForm.mpullback _ (isSmoothlyContractible_def.mp h).choose_spec.choose_spec.1 ∘ₗ
        (closedForms I N (k + 1)).subtype :=
  (rfl)

variable {I} in
/-- The splitting of a smoothly contractible manifold is smooth, over parameter manifolds in all
universes. -/
theorem isSmooth_ofIsSmoothlyContractible :
    (ofIsSmoothlyContractible I h).IsSmooth.{uE, uH, uN} where
  preservesSmoothFamilies_proj
    | 0 => by
      rw [proj_ofIsSmoothlyContractible_zero]
      exact preservesSmoothFamilies_subtype
    | k + 1 => by
      rw [proj_ofIsSmoothlyContractible_succ]
      exact preservesSmoothFamilies_zero
  preservesSmoothFamilies_primitive k := by
    rw [primitive_ofIsSmoothlyContractible]
    exact preservesSmoothFamilies_homotopyOperator_mpullback _ (closedForms I N (k + 1))

end SmoothCohomologySplitting

end SymplecticGeometry
