/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import TauCeti.Topology.Algebra.Projectivization
import Mathlib.Topology.Algebra.MvPolynomial
import SymplecticGeometry.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# Bihomogeneous zero sets in a product of two complex projective spaces

A polynomial `f` in the variables `Fin (m + 1) ⊕ Fin (n + 1)` is bihomogeneous of bidegree
`(a, b)` when it is weighted homogeneous of weight `a` for the weights `Sum.elim 1 0` and of
weight `b` for the weights `Sum.elim 0 1`. For a family `p` of such polynomials,
`complexProjectiveProdZeroLocus p` is the set of points `(L, M)` of
`ℙ ℂ (Fin (m + 1) → ℂ) × ℙ ℂ (Fin (n + 1) → ℂ)` at which every `p k` vanishes on the chosen
representatives, `eval (Sum.elim L.rep M.rep) (p k) = 0`.

Scaling the first block of coordinates by `c` and the second by `e` multiplies the value of
`p k` by `c ^ a k * e ^ b k`, so for bihomogeneous equations the condition does not depend on the
representatives: the pair of classes of nonzero vectors `v` and `w` lies in the zero set exactly
when every `p k` vanishes at `Sum.elim v w`. The zero set is closed in the product, hence compact.
No manifold structure is used here.

## Main definitions

* `SymplecticGeometry.complexProjectiveProdZeroLocus p`: the common zero set of the family `p`
  in `ℙ ℂ (Fin (m + 1) → ℂ) × ℙ ℂ (Fin (n + 1) → ℂ)`, tested on representatives.

## Main results

* `SymplecticGeometry.mk_mem_complexProjectiveProdZeroLocus_iff`: for bihomogeneous equations,
  membership can be tested on any pair of nonzero representatives.
* `SymplecticGeometry.isClosed_complexProjectiveProdZeroLocus` and
  `SymplecticGeometry.isCompact_complexProjectiveProdZeroLocus`: for bihomogeneous equations, the
  zero set is closed and compact.

The proofs adapt those of Tau Ceti's `TauCeti.mem_complexProjectiveZeroLocus_iff_eval_rep` and
`TauCeti.complexProjectiveZeroLocus_mk_iff` (`LinearAlgebra/Projectivization/ZeroLocus.lean`),
and of `TauCeti.isClosed_complexProjectiveZeroLocus` and
`TauCeti.isCompact_complexProjectiveZeroLocus` (`Topology/Algebra/Projectivization/ZeroLocus.lean`),
from one projective space to a product of two.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  Example 7.1.7, where the rational elliptic surface is a bihomogeneous zero set in
  `ℂP² × ℂP¹`.
-/

public section

open MvPolynomial
open scoped LinearAlgebra.Projectivization

namespace SymplecticGeometry

variable {m n : ℕ} {ι : Type*}

/-- The common zero set of a family `p` of polynomials in the variables
`Fin (m + 1) ⊕ Fin (n + 1)`, in the product `ℙ ℂ (Fin (m + 1) → ℂ) × ℙ ℂ (Fin (n + 1) → ℂ)`: the
points `x` such that every `p k` vanishes at the pair of chosen representatives
`Sum.elim x.1.rep x.2.rep`. For bihomogeneous equations it does not depend on the representatives
(`SymplecticGeometry.mk_mem_complexProjectiveProdZeroLocus_iff`). -/
def complexProjectiveProdZeroLocus (p : ι → MvPolynomial (Fin (m + 1) ⊕ Fin (n + 1)) ℂ) :
    Set (ℙ ℂ (Fin (m + 1) → ℂ) × ℙ ℂ (Fin (n + 1) → ℂ)) :=
  {x | ∀ k, eval (Sum.elim x.1.rep x.2.rep) (p k) = 0}

variable {p : ι → MvPolynomial (Fin (m + 1) ⊕ Fin (n + 1)) ℂ}

/-- A point lies in the zero set when every equation vanishes at the pair of chosen
representatives. -/
theorem mem_complexProjectiveProdZeroLocus {x : ℙ ℂ (Fin (m + 1) → ℂ) × ℙ ℂ (Fin (n + 1) → ℂ)} :
    x ∈ complexProjectiveProdZeroLocus p ↔ ∀ k, eval (Sum.elim x.1.rep x.2.rep) (p k) = 0 :=
  Iff.rfl

variable {a b : ι → ℕ}

/-- For bihomogeneous equations, the pair of classes of nonzero vectors `v` and `w` lies in the
zero set exactly when every equation vanishes at `Sum.elim v w`. -/
theorem mk_mem_complexProjectiveProdZeroLocus_iff
    (hp₁ : ∀ k, (p k).IsWeightedHomogeneous (Sum.elim 1 0) (a k))
    (hp₂ : ∀ k, (p k).IsWeightedHomogeneous (Sum.elim 0 1) (b k))
    {v : Fin (m + 1) → ℂ} (hv : v ≠ 0) {w : Fin (n + 1) → ℂ} (hw : w ≠ 0) :
    (Projectivization.mk ℂ v hv, Projectivization.mk ℂ w hw) ∈ complexProjectiveProdZeroLocus p ↔
      ∀ k, eval (Sum.elim v w) (p k) = 0 := by
  obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v hv
  obtain ⟨e, he⟩ := Projectivization.exists_smul_eq_mk_rep ℂ w hw
  rw [mem_complexProjectiveProdZeroLocus, ← hc, ← he]
  refine forall_congr' fun k ↦ ?_
  rw [Units.smul_def, Units.smul_def, (hp₁ k).eval_sumElim_smul_left,
    (hp₂ k).eval_sumElim_smul_right]
  simp

/-- For bihomogeneous equations, the zero set is closed in the product of the two projective
spaces. -/
theorem isClosed_complexProjectiveProdZeroLocus
    (hp₁ : ∀ k, (p k).IsWeightedHomogeneous (Sum.elim 1 0) (a k))
    (hp₂ : ∀ k, (p k).IsWeightedHomogeneous (Sum.elim 0 1) (b k)) :
    IsClosed (complexProjectiveProdZeroLocus p) := by
  rw [← (Projectivization.isOpenQuotientMap_mk'.prodMap
    Projectivization.isOpenQuotientMap_mk').isQuotientMap.isClosed_preimage]
  have h : Prod.map (Projectivization.mk' ℂ) (Projectivization.mk' ℂ) ⁻¹'
      complexProjectiveProdZeroLocus p = ⋂ k, {x : {v : Fin (m + 1) → ℂ // v ≠ 0} ×
        {w : Fin (n + 1) → ℂ // w ≠ 0} | eval (Sum.elim x.1.val x.2.val) (p k) = 0} := by
    ext ⟨v, w⟩
    simp only [Set.mem_preimage, Prod.map_apply, Projectivization.mk'_eq_mk,
      mk_mem_complexProjectiveProdZeroLocus_iff hp₁ hp₂, Set.mem_iInter, Set.mem_ofPred_eq]
  have hc : Continuous fun x : {v : Fin (m + 1) → ℂ // v ≠ 0} × {w : Fin (n + 1) → ℂ // w ≠ 0} ↦
      Sum.elim x.1.val x.2.val :=
    continuous_pi fun
      | .inl i => (continuous_apply i).comp (continuous_subtypeVal.comp continuous_fst)
      | .inr j => (continuous_apply j).comp (continuous_subtypeVal.comp continuous_snd)
  rw [h]
  exact isClosed_iInter fun k ↦ isClosed_eq ((continuous_eval (p k)).comp hc) continuous_const

/-- For bihomogeneous equations, the zero set is compact, since the product of the two
projective spaces is compact. -/
theorem isCompact_complexProjectiveProdZeroLocus
    (hp₁ : ∀ k, (p k).IsWeightedHomogeneous (Sum.elim 1 0) (a k))
    (hp₂ : ∀ k, (p k).IsWeightedHomogeneous (Sum.elim 0 1) (b k)) :
    IsCompact (complexProjectiveProdZeroLocus p) :=
  (isClosed_complexProjectiveProdZeroLocus hp₁ hp₂).isCompact

end SymplecticGeometry

end
