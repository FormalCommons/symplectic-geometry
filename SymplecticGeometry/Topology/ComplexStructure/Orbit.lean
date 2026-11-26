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

* `SymplecticGeometry.isClopen_setOfPred_isPositivelyOriented`: the positively oriented structures
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
  (Homeomorph.Quotient.congrRight fun _ _ ↦ by rw [stabilizer_stdComplexStructure]).trans
    (MulAction.quotientStabilizerHomeomorphOfSigmaCompact _ (stdComplexStructure ι))

variable {ι}

/-- The coset of `g` goes to `g • J₀`. -/
@[simp]
theorem quotientRealifyHomeomorph_mk (g : GL (ι ⊕ ι) ℝ) :
    quotientRealifyHomeomorph ι (QuotientGroup.mk g) = g • stdComplexStructure ι := by
  rw [quotientRealifyHomeomorph, Homeomorph.trans_apply]
  exact MulAction.quotientStabilizerHomeomorphOfSigmaCompact_mk _ _ g

/-- The positively oriented complex structures on `StdSpace ι` form a clopen set: the orbit
map `g ↦ g • J₀` is a quotient map, and the preimage of this set is the clopen set `{det > 0}`
of `GL (ι ⊕ ι) ℝ`. -/
theorem isClopen_setOfPred_isPositivelyOriented :
    IsClopen {J : AlmostComplexStructure (StdSpace ι) | IsPositivelyOriented J} := by
  have hq : Topology.IsQuotientMap fun g : GL (ι ⊕ ι) ℝ ↦ g • stdComplexStructure ι :=
    (isOpenMap_smul_of_sigmaCompact _).isQuotientMap (continuous_id.smul continuous_const)
      (MulAction.surjective_smul _ _)
  have hdet : Continuous fun g : GL (ι ⊕ ι) ℝ ↦ (g : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ).det :=
    (continuous_id.matrix_det).comp Units.continuous_val
  rw [← hq.isClopen_preimage, Set.preimage_ofPred_eq]
  simp_rw [isPositivelyOriented_smul_stdComplexStructure_iff]
  refine ⟨?_, isOpen_lt continuous_const hdet⟩
  convert isClosed_le continuous_const hdet using 1
  exact Set.ext fun g ↦ (g.det_ne_zero.symm.le_iff_lt).symm

end SymplecticGeometry

end
