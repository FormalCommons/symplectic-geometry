/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cayley.Contractible
public import Mathlib.Topology.Homotopy.Equiv

/-!
# Tame complex structures

Let `ω` be a symplectic form on a finite-dimensional real normed space `V`. Every `ω`-compatible
complex structure is `ω`-tame, and both spaces carry the subspace topology of the operator-norm
topology. Tau Ceti shows that both are contractible, by the Cayley transform at a compatible
reference structure `J₀` (`TauCeti.SymplecticForm.Compatible.cayleyContraction`, which keeps
compatible structures compatible). This file records the consequence that the inclusion of the
compatible structures into the tame ones is a homotopy equivalence, with homotopy inverse the
constant map at `J₀`.

## Main definitions and results

* `TauCeti.SymplecticForm.Compatible.tamesHomotopyEquiv`: the inclusion of the compatible
  structures into the tame ones, as a homotopy equivalence whose inverse is constant at `J₀`.
* `TauCeti.SymplecticForm.contractibleSpace_tames_and_homotopyEquiv`: the tame structures form
  a contractible space, and the inclusion is a homotopy equivalence.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Proposition 2.5.13.
-/

public section

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J₀ : AlmostComplexStructure V}

/-- For an `ω`-compatible `J₀`, the inclusion of the `ω`-compatible complex structures into the
`ω`-tame ones is a homotopy equivalence, with homotopy inverse the constant map at `J₀`. Both
composites are homotopic to the identity through the Cayley contraction onto `J₀`
(`Compatible.compatibleCayleyContraction` and `Compatible.cayleyContraction`). -/
noncomputable def Compatible.tamesHomotopyEquiv (h₀ : ω.Compatible J₀) :
    ContinuousMap.HomotopyEquiv {J : AlmostComplexStructure V // ω.Compatible J}
      {J : AlmostComplexStructure V // ω.Tames J} where
  toFun := ⟨fun J ↦ ⟨J, J.property.tames⟩, continuous_subtypeVal.subtype_mk _⟩
  invFun := ContinuousMap.const _ ⟨J₀, h₀⟩
  left_inv := ⟨h₀.compatibleCayleyContraction.toHomotopy.symm⟩
  right_inv := ⟨h₀.cayleyContraction.toHomotopy.symm⟩

/-- The forward map of `Compatible.tamesHomotopyEquiv` is the inclusion. -/
@[simp]
theorem Compatible.tamesHomotopyEquiv_toFun (h₀ : ω.Compatible J₀)
    (J : {J : AlmostComplexStructure V // ω.Compatible J}) :
    h₀.tamesHomotopyEquiv.toFun J = ⟨J, J.property.tames⟩ :=
  (rfl)

/-- The homotopy inverse of `Compatible.tamesHomotopyEquiv` is the constant map at `J₀`. -/
@[simp]
theorem Compatible.tamesHomotopyEquiv_invFun (h₀ : ω.Compatible J₀) :
    h₀.tamesHomotopyEquiv.invFun = ContinuousMap.const _ ⟨J₀, h₀⟩ :=
  (rfl)

/-- The inverse of `Compatible.tamesHomotopyEquiv` sends every tame structure to `J₀`. -/
@[simp]
theorem Compatible.tamesHomotopyEquiv_symm_apply (h₀ : ω.Compatible J₀)
    (J : {J : AlmostComplexStructure V // ω.Tames J}) :
    h₀.tamesHomotopyEquiv.symm J = ⟨J₀, h₀⟩ :=
  (rfl)

variable (ω) in
/-- On a finite-dimensional symplectic vector space `(V, ω)`, the space of `ω`-tame complex
structures is contractible, and the inclusion of the `ω`-compatible complex structures into it is
a homotopy equivalence.

Milestone: *Contractibility of the space of tame complex structures*. -/
theorem contractibleSpace_tames_and_homotopyEquiv :
    ContractibleSpace {J : AlmostComplexStructure V // ω.Tames J} ∧
      ∃ e : ContinuousMap.HomotopyEquiv {J : AlmostComplexStructure V // ω.Compatible J}
          {J : AlmostComplexStructure V // ω.Tames J},
        ∀ J, (e J : AlmostComplexStructure V) = J := by
  obtain ⟨J₀, h₀⟩ := ω.exists_compatible
  exact ⟨inferInstance, h₀.tamesHomotopyEquiv, fun _ ↦ rfl⟩

end TauCeti.SymplecticForm

end
