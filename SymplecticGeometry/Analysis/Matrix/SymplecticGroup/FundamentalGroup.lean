/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Matrix.SymplecticGroup.Maslov
public import TauCeti.Topology.Homotopy.HomotopyGroup.WeakHomotopyEquivalence
public import TauCeti.AlgebraicTopology.UniversalCover.Circle.FundamentalGroup
import SymplecticGeometry.Analysis.Matrix.Polar.GLSymplectic
import SymplecticGeometry.Analysis.Matrix.UnitaryGroup.FundamentalGroup
import SymplecticGeometry.AlgebraicTopology.FundamentalGroup.Circle

/-!
# The fundamental group of the real symplectic group

Write `Sp(2n) = TauCeti.GLSymplectic ι ℝ` for the real symplectic matrices of size `ι ⊕ ι`, and
`ρ = TauCeti.GLSymplectic.maslovPhase : Sp(2n) → S¹` for the complex determinant of the
orthogonal polar factor. For a nonempty finite index type `ι` this file shows that `ρ` induces an
isomorphism `π₁(Sp(2n), A) ≅ π₁(S¹, ρ A)` at every base point `A`, so that the fundamental group of
`Sp(2n)` is infinite cyclic.

The realification `TauCeti.GLSymplectic.ofUnitary : U(ι) → Sp(2n)` is a homotopy equivalence
(`TauCeti.GLSymplectic.ofUnitaryHomotopyEquiv`, built from the polar deformation retraction), hence
a weak homotopy equivalence, and `ρ ∘ ofUnitary` is the determinant
`Matrix.UnitaryGroup.detCircle`, which is bijective on `π₁` at every base point
(`Matrix.UnitaryGroup.bijective_fundamentalGroupMap_detCircle`). Comparing the two along this
square gives the statement for `ρ`.

For an empty index type `Sp(0)` is a point, so its fundamental group is trivial and `ρ` is not
surjective on `π₁`: the hypothesis `Nonempty ι` cannot be dropped.

## Main definitions

* `TauCeti.GLSymplectic.maslovPhaseMap`: `ρ` as a bundled continuous map `Sp(2n) → S¹`.

## Main results

* `TauCeti.GLSymplectic.bijective_fundamentalGroupMap_maslovPhase`: for nonempty `ι`, `ρ` induces
  a bijection `π₁(Sp(2n), A) → π₁(S¹, ρ A)`.
* `TauCeti.GLSymplectic.fundamentalGroupMulEquivCircle`,
  `TauCeti.GLSymplectic.fundamentalGroupMulEquiv`: the resulting isomorphisms
  `π₁(Sp(2n), A) ≃* π₁(S¹, ρ A)` and `π₁(Sp(2n), A) ≃* ℤ`.
* `TauCeti.GLSymplectic.fundamentalGroupMulEquiv_fromPath`: the second isomorphism sends a loop
  to its Maslov index `TauCeti.GLSymplectic.maslovIndex`.
* `TauCeti.GLSymplectic.not_bijective_fundamentalGroupMap_maslovPhase_of_isEmpty`: the statement
  fails for empty `ι`, where the fundamental group is trivial.
* `TauCeti.GLSymplectic.nonempty_fundamentalGroup_mulEquiv_int`: for nonempty `ι`,
  `π₁(Sp(2n), A) ≅ ℤ` at every base point.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Section 2.2, Proposition 2.2.4 and Proposition 2.2.6.
-/

public section

open Matrix Matrix.UnitaryGroup

namespace TauCeti.GLSymplectic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The phase `ρ = maslovPhase : Sp(2n) → S¹`, the complex determinant of the unitary polar
factor, as a bundled continuous map. -/
noncomputable def maslovPhaseMap : C(GLSymplectic ι ℝ, Circle) :=
  ⟨maslovPhase, continuous_maslovPhase⟩

@[simp]
theorem coe_maslovPhaseMap : ⇑(maslovPhaseMap : C(GLSymplectic ι ℝ, Circle)) = maslovPhase :=
  (rfl)

theorem maslovPhaseMap_apply (A : GLSymplectic ι ℝ) : maslovPhaseMap A = maslovPhase A :=
  (rfl)

/-- The square `id ∘ detCircle = maslovPhase ∘ ofUnitary`. -/
private theorem comp_detCircle_eq :
    (ContinuousMap.id Circle).comp ⟨detCircle, continuous_detCircle⟩ =
      maslovPhaseMap.comp (ofUnitaryHomotopyEquiv (n := ι)).toFun := by
  ext U
  simp

section Nonempty

variable [Nonempty ι]

/-- For a nonempty index type, `maslovPhase : Sp(2n) → S¹` induces a bijection on the first
homotopy group `π_ 1` at every base point. -/
theorem bijective_homotopyGroupMap_maslovPhase (A : GLSymplectic ι ℝ) :
    Function.Bijective (HomotopyGroup.map (N := Fin 1) maslovPhaseMap
      (rfl : maslovPhaseMap A = maslovPhaseMap A)) := by
  have hf := (ofUnitaryHomotopyEquiv (n := ι)).isWeakHomotopyEquivalence
  have hg := ContinuousMap.IsWeakHomotopyEquivalence.id (X := Circle)
  exact ⟨(hf.forall_injective_map_iff_of_comp_eq hg comp_detCircle_eq (Fin 1)).2
      (fun U ↦ (bijective_homotopyGroupMap_detCircle U).1) A,
    (hf.forall_surjective_map_iff_of_comp_eq hg comp_detCircle_eq (Fin 1)).2
      (fun U ↦ (bijective_homotopyGroupMap_detCircle U).2) A⟩

/-- For a nonempty index type, `maslovPhase : Sp(2n) → S¹` induces a bijection of fundamental
groups `π₁(Sp(2n), A) → π₁(S¹, maslovPhase A)` at every base point. -/
theorem bijective_fundamentalGroupMap_maslovPhase (A : GLSymplectic ι ℝ) :
    Function.Bijective (FundamentalGroup.map maslovPhaseMap A) := by
  rw [← FundamentalGroup.mapOfEq_rfl]
  exact (HomotopyGroup.bijective_map_iff_bijective_mapOfEq _ _).1
    (bijective_homotopyGroupMap_maslovPhase A)

variable (ι) in
/-- For a nonempty index type, the isomorphism `π₁(Sp(2n), A) ≃* π₁(S¹, maslovPhase A)` induced
by `maslovPhase`. -/
noncomputable def fundamentalGroupMulEquivCircle (A : GLSymplectic ι ℝ) :
    FundamentalGroup (GLSymplectic ι ℝ) A ≃* FundamentalGroup Circle (maslovPhaseMap A) :=
  MulEquiv.ofBijective _ (bijective_fundamentalGroupMap_maslovPhase A)

@[simp]
theorem fundamentalGroupMulEquivCircle_apply (A : GLSymplectic ι ℝ)
    (p : FundamentalGroup (GLSymplectic ι ℝ) A) :
    fundamentalGroupMulEquivCircle ι A p = FundamentalGroup.map maslovPhaseMap A p :=
  (rfl)

variable (ι) in
/-- For a nonempty index type, the fundamental group of `Sp(2n)` is infinite cyclic:
`π₁(Sp(2n), A) ≅ π₁(S¹, maslovPhase A) ≅ ℤ`, the first isomorphism induced by `maslovPhase` and
the second `Circle.fundamentalGroupMulEquiv`. -/
noncomputable def fundamentalGroupMulEquiv (A : GLSymplectic ι ℝ) :
    FundamentalGroup (GLSymplectic ι ℝ) A ≃* Multiplicative ℤ :=
  (fundamentalGroupMulEquivCircle ι A).trans (Circle.fundamentalGroupMulEquiv _)

theorem fundamentalGroupMulEquiv_apply (A : GLSymplectic ι ℝ)
    (p : FundamentalGroup (GLSymplectic ι ℝ) A) :
    fundamentalGroupMulEquiv ι A p = Circle.fundamentalGroupMulEquiv _
      (FundamentalGroup.map maslovPhaseMap A p) :=
  (rfl)

/-- The isomorphism `fundamentalGroupMulEquiv` sends the class of a loop `γ` in `Sp(2n)` to its
Maslov index `maslovIndex γ`. -/
@[simp]
theorem fundamentalGroupMulEquiv_fromPath {A : GLSymplectic ι ℝ} (γ : Path A A) :
    fundamentalGroupMulEquiv ι A (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)) =
      Multiplicative.ofAdd (maslovIndex γ) := by
  rw [fundamentalGroupMulEquiv_apply, FundamentalGroup.map_fromPath,
    Circle.fundamentalGroupMulEquiv_fromPath, maslovIndex_def]
  exact congrArg _ (Circle.degree_congr _ _ fun _ ↦ maslovPhaseMap_apply _)

/-- **The fundamental group of the symplectic group.** For a nonempty finite index type `ι` (that
is, `Sp(2n)` with `n ≥ 1`), the fundamental group of the real symplectic group is isomorphic to
`ℤ` at every base point; the isomorphism is induced by `maslovPhase`
(`fundamentalGroupMulEquiv`) and sends a loop to its Maslov index. For empty `ι` the group
`Sp(0)` is a point, so its fundamental group is trivial (instance search finds this), and
`maslovPhase` is not bijective on `π₁`
(`not_bijective_fundamentalGroupMap_maslovPhase_of_isEmpty`).

Milestone: *Fundamental group of the unitary group*. -/
theorem nonempty_fundamentalGroup_mulEquiv_int (A : GLSymplectic ι ℝ) :
    Nonempty (FundamentalGroup (GLSymplectic ι ℝ) A ≃* Multiplicative ℤ) :=
  ⟨fundamentalGroupMulEquiv ι A⟩

end Nonempty

section IsEmpty

variable [IsEmpty ι]

/-- The hypothesis `Nonempty ι` of `bijective_fundamentalGroupMap_maslovPhase` is needed: for an
empty index type `Sp(0)` is a point, so its trivial fundamental group cannot map onto
`π₁(S¹) ≅ ℤ`. -/
theorem not_bijective_fundamentalGroupMap_maslovPhase_of_isEmpty (A : GLSymplectic ι ℝ) :
    ¬ Function.Bijective (FundamentalGroup.map maslovPhaseMap A) :=
  fun h ↦ FundamentalGroup.not_surjective_map_circle_of_subsingleton A _ h.2

end IsEmpty

end TauCeti.GLSymplectic

end
