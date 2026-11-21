/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Analysis.Matrix.Polar.GLSymplectic
public import SymplecticGeometry.Analysis.Matrix.UnitaryGroup.FundamentalGroup
public import TauCeti.Analysis.Matrix.SymplecticGroup.Maslov
public import TauCeti.Topology.Homotopy.HomotopyGroup.WeakHomotopyEquivalence

/-!
# The fundamental group of the real symplectic group

Write `Sp(2n) = TauCeti.GLSymplectic ι ℝ` for the real symplectic matrices of size `ι ⊕ ι`, and
`ρ = TauCeti.GLSymplectic.maslovPhase : Sp(2n) → S¹` for the complex determinant of the
orthogonal polar factor. For a nonempty finite index type `ι` this file shows that `ρ` induces an
isomorphism `π₁(Sp(2n), A) ≅ π₁(S¹, ρ A)` at every base point `A`, so that the fundamental group of
`Sp(2n)` is infinite cyclic.

The realification `TauCeti.GLSymplectic.ofUnitary : U(ι) → Sp(2n)` is the composite of the
homeomorphism of `U(ι)` with the orthogonal symplectic matrices and of their inclusion in `Sp(2n)`,
which is a homotopy equivalence (`TauCeti.GLSymplectic.polarHomotopyEquiv`, the polar deformation
retraction). So it is a weak homotopy equivalence, and `ρ ∘ ofUnitary` is the determinant
`Matrix.UnitaryGroup.detCircle`, which is bijective on `π₁` at every base point
(`Matrix.UnitaryGroup.bijective_fundamentalGroupMap_detCircle`). Comparing the two along this
square gives the statement for `ρ`.

For an empty index type `Sp(0)` is a point, so its fundamental group is trivial and `ρ` is not
surjective on `π₁`: the hypothesis `Nonempty ι` cannot be dropped.

## Main results

* `TauCeti.GLSymplectic.isWeakHomotopyEquivalence_ofUnitary`: the realification
  `U(ι) → Sp(2n)` is a weak homotopy equivalence.
* `TauCeti.GLSymplectic.bijective_fundamentalGroupMap_maslovPhase`: for nonempty `ι`, `ρ` induces
  a bijection `π₁(Sp(2n), A) → π₁(S¹, ρ A)`.
* `TauCeti.GLSymplectic.fundamentalGroupMulEquivCircle`,
  `TauCeti.GLSymplectic.fundamentalGroupMulEquiv`: the resulting isomorphisms
  `π₁(Sp(2n), A) ≃* π₁(S¹, ρ A)` and `π₁(Sp(2n), A) ≃* ℤ`.
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

/-- The realification `ofUnitary : U(ι) → Sp(2n)`, as a continuous map. -/
private noncomputable abbrev ofUnitaryCM : C(unitaryGroup ι ℂ, GLSymplectic ι ℝ) :=
  ⟨ofUnitary, continuous_ofUnitary⟩

/-- The realification `ofUnitary : U(ι) → Sp(2n)` is a weak homotopy equivalence: it is a
homeomorphism onto the orthogonal symplectic matrices followed by their inclusion, a homotopy
equivalence. -/
theorem isWeakHomotopyEquivalence_ofUnitary :
    (⟨ofUnitary, continuous_ofUnitary⟩ :
      C(unitaryGroup ι ℂ, GLSymplectic ι ℝ)).IsWeakHomotopyEquivalence := by
  have h := polarHomotopyEquiv.isWeakHomotopyEquivalence.comp
    (unitaryGroupEquivSymplecticInfOrthogonal (n := ι)).toHomeomorph.isWeakHomotopyEquivalence
  convert h using 1
  ext U
  simp [ofUnitary_apply]

/-- The square `id ∘ detCircle = maslovPhase ∘ ofUnitary`. -/
private theorem comp_detCircle_eq :
    (ContinuousMap.id Circle).comp ⟨detCircle, continuous_detCircle⟩ =
      (⟨maslovPhase, continuous_maslovPhase⟩ : C(GLSymplectic ι ℝ, Circle)).comp
        ofUnitaryCM := by
  ext U
  simp

section Nonempty

variable [Nonempty ι]

/-- For a nonempty index type, `maslovPhase : Sp(2n) → S¹` induces a bijection on the first
homotopy group `π_ 1` at every base point. -/
theorem bijective_homotopyGroupMap_maslovPhase (A : GLSymplectic ι ℝ) :
    Function.Bijective (HomotopyGroup.map (N := Fin 1)
      (⟨maslovPhase, continuous_maslovPhase⟩ : C(GLSymplectic ι ℝ, Circle))
      (rfl : maslovPhase A = maslovPhase A)) := by
  have hf := isWeakHomotopyEquivalence_ofUnitary (ι := ι)
  have hg := ContinuousMap.IsWeakHomotopyEquivalence.id (X := Circle)
  exact ⟨(hf.forall_injective_map_iff_of_comp_eq hg comp_detCircle_eq (Fin 1)).2
      (fun U ↦ (bijective_homotopyGroupMap_detCircle U).1) A,
    (hf.forall_surjective_map_iff_of_comp_eq hg comp_detCircle_eq (Fin 1)).2
      (fun U ↦ (bijective_homotopyGroupMap_detCircle U).2) A⟩

/-- For a nonempty index type, `maslovPhase : Sp(2n) → S¹` induces a bijection of fundamental
groups `π₁(Sp(2n), A) → π₁(S¹, maslovPhase A)` at every base point. -/
theorem bijective_fundamentalGroupMap_maslovPhase (A : GLSymplectic ι ℝ) :
    Function.Bijective (FundamentalGroup.map
      (⟨maslovPhase, continuous_maslovPhase⟩ : C(GLSymplectic ι ℝ, Circle)) A) := by
  simpa using (HomotopyGroup.bijective_map_iff_bijective_mapOfEq _ _).1
    (bijective_homotopyGroupMap_maslovPhase A)

variable (ι) in
/-- For a nonempty index type, the isomorphism `π₁(Sp(2n), A) ≃* π₁(S¹, maslovPhase A)` induced
by `maslovPhase`. -/
noncomputable def fundamentalGroupMulEquivCircle (A : GLSymplectic ι ℝ) :
    FundamentalGroup (GLSymplectic ι ℝ) A ≃* FundamentalGroup Circle (maslovPhase A) :=
  MulEquiv.ofBijective _ (bijective_fundamentalGroupMap_maslovPhase A)

@[simp]
theorem fundamentalGroupMulEquivCircle_apply (A : GLSymplectic ι ℝ)
    (p : FundamentalGroup (GLSymplectic ι ℝ) A) :
    fundamentalGroupMulEquivCircle ι A p = FundamentalGroup.map
      (⟨maslovPhase, continuous_maslovPhase⟩ : C(GLSymplectic ι ℝ, Circle)) A p :=
  (rfl)

variable (ι) in
/-- For a nonempty index type, the fundamental group of `Sp(2n)` is infinite cyclic:
`π₁(Sp(2n), A) ≅ π₁(S¹, maslovPhase A) ≅ ℤ`, the first isomorphism induced by `maslovPhase` and
the second `Circle.fundamentalGroupMulEquiv`. -/
noncomputable def fundamentalGroupMulEquiv (A : GLSymplectic ι ℝ) :
    FundamentalGroup (GLSymplectic ι ℝ) A ≃* Multiplicative ℤ :=
  (fundamentalGroupMulEquivCircle ι A).trans (Circle.fundamentalGroupMulEquiv _)

@[simp]
theorem fundamentalGroupMulEquiv_apply (A : GLSymplectic ι ℝ)
    (p : FundamentalGroup (GLSymplectic ι ℝ) A) :
    fundamentalGroupMulEquiv ι A p = Circle.fundamentalGroupMulEquiv _
      (FundamentalGroup.map
        (⟨maslovPhase, continuous_maslovPhase⟩ : C(GLSymplectic ι ℝ, Circle)) A p) :=
  (rfl)

/-- **The fundamental group of the symplectic group.** For a nonempty finite index type `ι` (that
is, `Sp(2n)` with `n ≥ 1`), the fundamental group of the real symplectic group is isomorphic to
`ℤ` at every base point; the isomorphism is induced by `maslovPhase`
(`fundamentalGroupMulEquiv`). For empty `ι` the group `Sp(0)` is a point and its fundamental
group is trivial (`not_bijective_fundamentalGroupMap_maslovPhase_of_isEmpty`).

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
    ¬ Function.Bijective (FundamentalGroup.map
      (⟨maslovPhase, continuous_maslovPhase⟩ : C(GLSymplectic ι ℝ, Circle)) A) := fun h ↦ by
  have := h.2.subsingleton
  have := (Circle.fundamentalGroupMulEquiv (maslovPhase A)).symm.subsingleton
  exact not_subsingleton (Multiplicative ℤ) this

end IsEmpty

end TauCeti.GLSymplectic

end
