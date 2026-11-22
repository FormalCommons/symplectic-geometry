/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import SymplecticGeometry.LinearAlgebra.Determinant

/-!
# Determinants of conjugates of continuous linear equivalences

The determinant of an endomorphism does not change under conjugation by an equivalence
(Mathlib's `LinearMap.det_conj`). This file states that fact for automorphisms written as
composites `ContinuousLinearEquiv.trans` of continuous linear equivalences and read as linear
maps, the form in which they arise from frames and trivializations of vector bundles.

## Main results

* `ContinuousLinearEquiv.det_symm_trans_trans`: for `e : N ≃L[R] M` and `g : N ≃L[R] N`, the
  automorphism `e ∘ g ∘ e⁻¹` of `M` has the determinant of `g`;
* `ContinuousLinearEquiv.det_trans_symm`: for `e f : N ≃L[R] M`, the automorphisms `e⁻¹ ∘ f` of
  `N` and `f ∘ e⁻¹` of `M` have the same determinant.

Both are the lemmas of the same names for the underlying linear equivalences, in
`SymplecticGeometry.LinearAlgebra.Determinant`. Since `LinearEquiv.det_symm_trans_trans` is a
`simp` lemma, `simp` proves `ContinuousLinearEquiv.det_symm_trans_trans`, which is therefore not
one itself; it is kept for rewriting in its `≃L` form.
-/

public section

namespace ContinuousLinearEquiv

variable {R M N : Type*} [CommRing R] [TopologicalSpace M] [AddCommGroup M] [Module R M]
  [TopologicalSpace N] [AddCommGroup N] [Module R N]

/-- Conjugating an automorphism `g` of `N` by a continuous linear equivalence `e : N ≃L[R] M`
does not change its determinant: `det (e ∘ g ∘ e⁻¹) = det g`. -/
theorem det_symm_trans_trans (e : N ≃L[R] M) (g : N ≃L[R] N) :
    LinearMap.det ((e.symm.trans (g.trans e) : M ≃L[R] M) : M →ₗ[R] M) =
      LinearMap.det (g : N →ₗ[R] N) :=
  e.toLinearEquiv.det_symm_trans_trans g.toLinearEquiv

/-- For continuous linear equivalences `e f : N ≃L[R] M`, the automorphism `e⁻¹ ∘ f` of `N` and
the automorphism `f ∘ e⁻¹` of `M` have the same determinant. -/
theorem det_trans_symm (e f : N ≃L[R] M) :
    LinearMap.det ((f.trans e.symm : N ≃L[R] N) : N →ₗ[R] N) =
      LinearMap.det ((e.symm.trans f : M ≃L[R] M) : M →ₗ[R] M) :=
  e.toLinearEquiv.det_trans_symm f.toLinearEquiv

end ContinuousLinearEquiv

end
