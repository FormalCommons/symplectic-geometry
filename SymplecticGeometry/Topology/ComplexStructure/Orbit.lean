/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.LinearAlgebra.ComplexStructure.Standard
public import SymplecticGeometry.Topology.Algebra.GroupAction.Transitive
public import SymplecticGeometry.Topology.ComplexStructure.Basic
public import TauCeti.Topology.Algebra.Group.Units
public import TauCeti.Topology.Instances.Matrix
public import Mathlib.Topology.Baire.LocallyCompactRegular

/-!
# Complex structures as the homogeneous space GL(2n, ℝ)/GL(n, ℂ)

The invertible matrices act transitively on the complex structures of `StdSpace ι = ℝ²ⁿ`, and
the stabilizer of the standard structure `J₀` is the realified group `GL(n, ℂ)`. Since
`GL (ι ⊕ ι) ℝ` is σ-compact and the space of complex structures is locally compact and
Hausdorff, the orbit map `g ↦ g • J₀` is open, so the space of complex structures is
homeomorphic to the quotient `GL(2n, ℝ)/GL(n, ℂ)`.

The positively oriented structures are the image of the open set of matrices of positive
determinant, and the others the image of the matrices of negative determinant; so they form a
clopen set.

## Main definitions

* `SymplecticGeometry.quotientRealifyHomeomorph`: the homeomorphism
  `GL (ι ⊕ ι) ℝ ⧸ (Matrix.GeneralLinearGroup.realify ι ℂ).range ≃ₜ
  AlmostComplexStructure (StdSpace ι)`, the coset of `g` going to `g • J₀`.

## Main results

* `SymplecticGeometry.isClopen_setOf_isPositivelyOriented`: the positively oriented structures
  form a clopen set.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Proposition 2.5.2.
-/

public section

namespace SymplecticGeometry

open TauCeti

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

/-- The complex structures of `StdSpace ι = ℝ²ⁿ` form the homogeneous space
`GL(2n, ℝ)/GL(n, ℂ)`: the coset of an invertible matrix `g` modulo the realified complex
matrices goes to `g • J₀`. -/
noncomputable def quotientRealifyHomeomorph :
    GL (ι ⊕ ι) ℝ ⧸ (Matrix.GeneralLinearGroup.realify ι ℂ).range ≃ₜ
      AlmostComplexStructure (StdSpace ι) :=
  Homeomorph.trans
    { toEquiv := Subgroup.quotientEquivOfEq (stabilizer_stdComplexStructure (ι := ι)).symm
      continuous_toFun := by
        rw [QuotientGroup.isOpenQuotientMap_mk.isQuotientMap.continuous_iff]
        exact QuotientGroup.continuous_mk.congr fun g ↦ rfl
      continuous_invFun := by
        rw [QuotientGroup.isOpenQuotientMap_mk.isQuotientMap.continuous_iff]
        exact QuotientGroup.continuous_mk.congr fun g ↦ rfl }
    (MulAction.quotientStabilizerHomeomorphOfSigmaCompact _ (stdComplexStructure ι))

variable {ι}

@[simp]
theorem quotientRealifyHomeomorph_mk (g : GL (ι ⊕ ι) ℝ) :
    quotientRealifyHomeomorph ι (QuotientGroup.mk g) = g • stdComplexStructure ι := by
  rw [quotientRealifyHomeomorph, Homeomorph.trans_apply]
  exact MulAction.quotientStabilizerHomeomorphOfSigmaCompact_mk _ _ g

/-- The positively oriented complex structures on `StdSpace ι` form a clopen set: they and the
others are the images of the open sets `{det > 0}` and `{det < 0}` of `GL (ι ⊕ ι) ℝ` under the
open orbit map `g ↦ g • J₀`. -/
theorem isClopen_setOf_isPositivelyOriented :
    IsClopen {J : AlmostComplexStructure (StdSpace ι) | IsPositivelyOriented J} := by
  have hopen := isOpenMap_smul_of_sigmaCompact (G := GL (ι ⊕ ι) ℝ) (stdComplexStructure ι)
  have hdet : Continuous fun g : GL (ι ⊕ ι) ℝ ↦ (g : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ).det :=
    (continuous_id.matrix_det).comp Units.continuous_val
  -- If `q (g • J₀)` means `g ∈ s`, then `q` holds exactly on the image of `s`, since every
  -- structure is some `g • J₀`.
  have himage (q : AlmostComplexStructure (StdSpace ι) → Prop) (s : Set (GL (ι ⊕ ι) ℝ))
      (hs : ∀ g, q (g • stdComplexStructure ι) ↔ g ∈ s) :
      {J | q J} = (· • stdComplexStructure ι) '' s := by
    ext J
    obtain ⟨g, rfl⟩ := exists_generalLinearGroup_smul_stdComplexStructure_eq J
    refine ⟨fun h ↦ ⟨g, (hs g).1 h, rfl⟩, ?_⟩
    rintro ⟨h, hh, hgh⟩
    rw [← hgh]
    exact (hs h).2 hh
  refine ⟨⟨?_⟩, ?_⟩
  · rw [Set.compl_ofPred, himage _ {g | (g : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ).det < 0} fun g ↦ by
      rw [isPositivelyOriented_smul_stdComplexStructure_iff, not_lt]
      exact (g.det_ne_zero).le_iff_lt]
    exact hopen _ (isOpen_lt hdet continuous_const)
  · rw [himage _ {g | 0 < (g : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ).det}
      isPositivelyOriented_smul_stdComplexStructure_iff]
    exact hopen _ (isOpen_lt continuous_const hdet)

end SymplecticGeometry

end
