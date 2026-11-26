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
import SymplecticGeometry.RingTheory.MvPolynomial.WeightedHomogeneous
import SymplecticGeometry.Topology.Algebra.MvPolynomial

/-!
# Bihomogeneous zero sets in a product of two complex projective spaces

A polynomial `f` in the variables `Fin (m + 1) ⊕ Fin (n + 1)` is bihomogeneous of bidegree
`(a, b)` when it is weighted homogeneous of weight `a` for the weights `Sum.elim 1 0` and of
weight `b` for the weights `Sum.elim 0 1`. For any family `p` of polynomials in these variables,
`complexProjectiveProdZeroLocus p` is the set of pairs `(L, M)` of points of
`ℙ ℂ (Fin (m + 1) → ℂ)` and `ℙ ℂ (Fin (n + 1) → ℂ)` such that every `p k` vanishes at
`Sum.elim v w` for every vector `v` of the line `L` and every vector `w` of the line `M`.

Since the condition is asked on the whole lines, the set involves no choice of representatives
and makes sense for every family: it is closed in the product, hence compact, with no hypothesis
on `p`. For bihomogeneous equations, scaling the first block of coordinates by `c` and the
second by `e` multiplies the value of `p k` by `c ^ a k * e ^ b k`, so membership can be tested
on one pair of nonzero representatives, for instance on the chosen ones `L.rep` and `M.rep`.
No manifold structure is used here.

## Main definitions

* `SymplecticGeometry.complexProjectiveProdZeroLocus p`: the common zero set of the family `p`
  in `ℙ ℂ (Fin (m + 1) → ℂ) × ℙ ℂ (Fin (n + 1) → ℂ)`.

## Main results

* `SymplecticGeometry.mk_mem_complexProjectiveProdZeroLocus_iff_forall_smul`: the pair of classes
  of nonzero vectors `v` and `w` lies in the zero set exactly when every equation vanishes at
  `Sum.elim (c • v) (e • w)` for all scalars `c` and `e`.
* `SymplecticGeometry.mk_mem_complexProjectiveProdZeroLocus_iff` and
  `SymplecticGeometry.mem_complexProjectiveProdZeroLocus_iff_eval_rep`: for bihomogeneous
  equations, membership can be tested on any pair of nonzero representatives, or on the chosen
  ones.
* `SymplecticGeometry.preimage_prodMap_mk'_complexProjectiveProdZeroLocus`: the preimage of the
  zero set in the product of the two spaces of nonzero vectors.
* `SymplecticGeometry.isClosed_complexProjectiveProdZeroLocus` and
  `SymplecticGeometry.isCompact_complexProjectiveProdZeroLocus`: the zero set is closed and
  compact; it is also a compact space.

The definition and the proofs adapt Tau Ceti's `TauCeti.complexProjectiveZeroLocus`,
`TauCeti.complexProjectiveZeroLocus_mk_iff_forall_smul`, `TauCeti.complexProjectiveZeroLocus_mk_iff`
and `TauCeti.mem_complexProjectiveZeroLocus_iff_eval_rep`
(`LinearAlgebra/Projectivization/ZeroLocus.lean`), and
`TauCeti.isClosed_complexProjectiveZeroLocus` and `TauCeti.isCompact_complexProjectiveZeroLocus`
(`Topology/Algebra/Projectivization/ZeroLocus.lean`), from one projective space to a product of
two.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  Example 7.1.7, for the rational elliptic surface, which these zero sets in
  `ℂP² × ℂP¹` are meant to model.
-/

public section

open MvPolynomial
open scoped LinearAlgebra.Projectivization

namespace SymplecticGeometry

variable {m n : ℕ} {ι : Type*}

/-- The common zero set of a family `p` of polynomials in the variables
`Fin (m + 1) ⊕ Fin (n + 1)`, in the product `ℙ ℂ (Fin (m + 1) → ℂ) × ℙ ℂ (Fin (n + 1) → ℂ)`: the
pairs of lines `x` such that every `p k` vanishes at `Sum.elim v w` for every vector `v` of the
line `x.1` and every vector `w` of the line `x.2`. -/
def complexProjectiveProdZeroLocus (p : ι → MvPolynomial (Fin (m + 1) ⊕ Fin (n + 1)) ℂ) :
    Set (ℙ ℂ (Fin (m + 1) → ℂ) × ℙ ℂ (Fin (n + 1) → ℂ)) :=
  {x | ∀ k, ∀ v ∈ x.1.submodule, ∀ w ∈ x.2.submodule, eval (Sum.elim v w) (p k) = 0}

variable {p : ι → MvPolynomial (Fin (m + 1) ⊕ Fin (n + 1)) ℂ}

/-- A pair of lines lies in the zero set when every equation vanishes at every pair of vectors of
the two lines. -/
@[simp]
theorem mem_complexProjectiveProdZeroLocus {x : ℙ ℂ (Fin (m + 1) → ℂ) × ℙ ℂ (Fin (n + 1) → ℂ)} :
    x ∈ complexProjectiveProdZeroLocus p ↔
      ∀ k, ∀ v ∈ x.1.submodule, ∀ w ∈ x.2.submodule, eval (Sum.elim v w) (p k) = 0 :=
  Iff.rfl

/-- The pair of classes of nonzero vectors `v` and `w` lies in the zero set exactly when every
equation vanishes at `Sum.elim (c • v) (e • w)` for all scalars `c` and `e`. No homogeneity is
needed. -/
theorem mk_mem_complexProjectiveProdZeroLocus_iff_forall_smul
    {v : Fin (m + 1) → ℂ} (hv : v ≠ 0) {w : Fin (n + 1) → ℂ} (hw : w ≠ 0) :
    (Projectivization.mk ℂ v hv, Projectivization.mk ℂ w hw) ∈ complexProjectiveProdZeroLocus p ↔
      ∀ k, ∀ c e : ℂ, eval (Sum.elim (c • v) (e • w)) (p k) = 0 := by
  simp only [mem_complexProjectiveProdZeroLocus, Projectivization.submodule_mk,
    Submodule.mem_span_singleton, forall_exists_index, forall_apply_eq_imp_iff]

variable {a b : ι → ℕ}

/-- For bihomogeneous equations, the pair of classes of nonzero vectors `v` and `w` lies in the
zero set exactly when every equation vanishes at `Sum.elim v w`. -/
theorem mk_mem_complexProjectiveProdZeroLocus_iff
    (hp₁ : ∀ k, (p k).IsWeightedHomogeneous (Sum.elim 1 0) (a k))
    (hp₂ : ∀ k, (p k).IsWeightedHomogeneous (Sum.elim 0 1) (b k))
    {v : Fin (m + 1) → ℂ} (hv : v ≠ 0) {w : Fin (n + 1) → ℂ} (hw : w ≠ 0) :
    (Projectivization.mk ℂ v hv, Projectivization.mk ℂ w hw) ∈ complexProjectiveProdZeroLocus p ↔
      ∀ k, eval (Sum.elim v w) (p k) = 0 := by
  rw [mk_mem_complexProjectiveProdZeroLocus_iff_forall_smul]
  refine forall_congr' fun k ↦ ⟨fun h ↦ by simpa using h 1 1, fun h c e ↦ ?_⟩
  rw [(hp₁ k).eval_sumElim_smul_left, (hp₂ k).eval_sumElim_smul_right, h, mul_zero, mul_zero]

/-- For bihomogeneous equations, membership in the zero set can be tested on the chosen
representatives `x.1.rep` and `x.2.rep`. -/
theorem mem_complexProjectiveProdZeroLocus_iff_eval_rep
    (hp₁ : ∀ k, (p k).IsWeightedHomogeneous (Sum.elim 1 0) (a k))
    (hp₂ : ∀ k, (p k).IsWeightedHomogeneous (Sum.elim 0 1) (b k))
    (x : ℙ ℂ (Fin (m + 1) → ℂ) × ℙ ℂ (Fin (n + 1) → ℂ)) :
    x ∈ complexProjectiveProdZeroLocus p ↔ ∀ k, eval (Sum.elim x.1.rep x.2.rep) (p k) = 0 := by
  obtain ⟨L, M⟩ := x
  conv_lhs => rw [← L.mk_rep, ← M.mk_rep]
  exact mk_mem_complexProjectiveProdZeroLocus_iff hp₁ hp₂ _ _

/-- The preimage of the zero set in the product of the two spaces of nonzero vectors is the set
of pairs `(v, w)` such that every equation vanishes at `Sum.elim (c • v) (e • w)` for all scalars
`c` and `e`. -/
theorem preimage_prodMap_mk'_complexProjectiveProdZeroLocus :
    Prod.map (Projectivization.mk' ℂ) (Projectivization.mk' ℂ) ⁻¹'
        complexProjectiveProdZeroLocus p =
      ⋂ k, ⋂ c : ℂ, ⋂ e : ℂ,
        {x : {v : Fin (m + 1) → ℂ // v ≠ 0} × {w : Fin (n + 1) → ℂ // w ≠ 0} |
          eval (Sum.elim (c • x.1.val) (e • x.2.val)) (p k) = 0} := by
  ext ⟨v, w⟩
  simp only [Set.mem_preimage, Prod.map_apply, Projectivization.mk'_eq_mk,
    mk_mem_complexProjectiveProdZeroLocus_iff_forall_smul, Set.mem_iInter, Set.mem_ofPred_eq]

/-- The zero set of any family of polynomials is closed in the product of the two projective
spaces. -/
theorem isClosed_complexProjectiveProdZeroLocus
    (p : ι → MvPolynomial (Fin (m + 1) ⊕ Fin (n + 1)) ℂ) :
    IsClosed (complexProjectiveProdZeroLocus p) := by
  rw [← (Projectivization.isOpenQuotientMap_mk'.prodMap
    Projectivization.isOpenQuotientMap_mk').isQuotientMap.isClosed_preimage,
    preimage_prodMap_mk'_complexProjectiveProdZeroLocus]
  refine isClosed_iInter fun k ↦ isClosed_iInter fun c ↦ isClosed_iInter fun e ↦ ?_
  have hc : Continuous fun x : {v : Fin (m + 1) → ℂ // v ≠ 0} × {w : Fin (n + 1) → ℂ // w ≠ 0} ↦
      Sum.elim (c • x.1.val) (e • x.2.val) :=
    continuous_pi fun
      | .inl i => (continuous_apply i).comp
          ((continuous_const_smul c).comp (continuous_subtypeVal.comp continuous_fst))
      | .inr j => (continuous_apply j).comp
          ((continuous_const_smul e).comp (continuous_subtypeVal.comp continuous_snd))
  exact isClosed_eq (hc.mvPolynomial_eval (p k)) continuous_const

/-- The zero set of any family of polynomials is compact, since the product of the two projective
spaces is compact. -/
theorem isCompact_complexProjectiveProdZeroLocus
    (p : ι → MvPolynomial (Fin (m + 1) ⊕ Fin (n + 1)) ℂ) :
    IsCompact (complexProjectiveProdZeroLocus p) :=
  (isClosed_complexProjectiveProdZeroLocus p).isCompact

/-- The zero set, with the subspace topology, is a compact space. -/
instance (p : ι → MvPolynomial (Fin (m + 1) ⊕ Fin (n + 1)) ℂ) :
    CompactSpace (complexProjectiveProdZeroLocus p) :=
  isCompact_iff_compactSpace.mp (isCompact_complexProjectiveProdZeroLocus p)

end SymplecticGeometry

end
