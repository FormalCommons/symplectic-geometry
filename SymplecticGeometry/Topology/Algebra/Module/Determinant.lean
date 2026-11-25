/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import SymplecticGeometry.LinearAlgebra.Determinant
public import TauCeti.Topology.Algebra.Module.Determinant
public import TauCeti.Topology.Algebra.Module.Equiv.Fin

/-!
# Determinants of conjugates and of block-diagonal maps

The determinant of an endomorphism does not change under conjugation by an equivalence
(Mathlib's `LinearMap.det_conj`). This file states that fact for automorphisms written as
composites `ContinuousLinearEquiv.trans` of continuous linear equivalences and read as linear
maps, the form in which they arise from frames and trivializations of vector bundles.

## Main results

* `ContinuousLinearEquiv.det_coe_symm_trans_trans`: for `e : N ≃L[R] M` and `g : N ≃L[R] N`,
  the automorphism `e ∘ g ∘ e⁻¹` of `M` has the determinant of `g`;
* `ContinuousLinearEquiv.det_coe_trans_symm`: for `e f : N ≃L[R] M`, the automorphisms
  `e⁻¹ ∘ f` of `N` and `f ∘ e⁻¹` of `M` have the same determinant.

Both are the lemmas of the same names for the underlying linear equivalences, in
`SymplecticGeometry.LinearAlgebra.Determinant`. With the `simp` lemmas
`LinearEquiv.det_coe_conj` and `LinearEquiv.det_coe_symm_trans_trans`, `simp` proves the
statement of `ContinuousLinearEquiv.det_coe_symm_trans_trans` for either bracketing of the `≃L`
chain, so that lemma is not a `simp` lemma itself; it is kept for rewriting in its `≃L` form.

* `ContinuousLinearMap.det_eq_det_mul_det_of_splitCoords`: an endomorphism of
  `Fin (m + n) → M` that maps the two coordinate blocks of Tau Ceti's `TauCeti.splitCoords m n`
  by `g` and `h` has determinant `g.det * h.det`. It is Tau Ceti's
  `ContinuousLinearMap.det_conj` followed by `ContinuousLinearMap.det_prodMap`.
-/

public section

namespace ContinuousLinearEquiv

variable {R M N : Type*} [CommRing R] [TopologicalSpace M] [AddCommGroup M] [Module R M]
  [TopologicalSpace N] [AddCommGroup N] [Module R N]

/-- Conjugating an automorphism `g` of `N` by a continuous linear equivalence `e : N ≃L[R] M`
does not change its determinant: `det (e ∘ g ∘ e⁻¹) = det g`. -/
theorem det_coe_symm_trans_trans (e : N ≃L[R] M) (g : N ≃L[R] N) :
    LinearMap.det ((e.symm.trans (g.trans e) : M ≃L[R] M) : M →ₗ[R] M) =
      LinearMap.det (g : N →ₗ[R] N) :=
  e.toLinearEquiv.det_coe_symm_trans_trans g.toLinearEquiv

/-- For continuous linear equivalences `e f : N ≃L[R] M`, the automorphism `e⁻¹ ∘ f` of `N` and
the automorphism `f ∘ e⁻¹` of `M` have the same determinant. -/
theorem det_coe_trans_symm (e f : N ≃L[R] M) :
    LinearMap.det ((f.trans e.symm : N ≃L[R] N) : N →ₗ[R] N) =
      LinearMap.det ((e.symm.trans f : M ≃L[R] M) : M →ₗ[R] M) :=
  e.toLinearEquiv.det_coe_trans_symm f.toLinearEquiv

end ContinuousLinearEquiv

namespace ContinuousLinearMap

variable {R M : Type*} [CommRing R] [TopologicalSpace M] [AddCommGroup M] [Module R M]
  [Module.Free R M] [Module.Finite R M] {m n : ℕ}

/-- An endomorphism `f` of `Fin (m + n) → M` that acts on the two coordinate blocks given by
`TauCeti.splitCoords m n` as `g` on the first and `h` on the second has determinant
`det g * det h`. -/
theorem det_eq_det_mul_det_of_splitCoords (f : (Fin (m + n) → M) →L[R] (Fin (m + n) → M))
    (g : (Fin m → M) →L[R] (Fin m → M)) (h : (Fin n → M) →L[R] (Fin n → M))
    (hf : ∀ u w, f ((TauCeti.splitCoords (𝕜 := R) m n).symm (u, w)) =
      (TauCeti.splitCoords (𝕜 := R) m n).symm (g u, h w)) :
    f.det = g.det * h.det := by
  set e := TauCeti.splitCoords (𝕜 := R) (M := M) m n
  have hconj : (e : _ →L[R] _) ∘L f ∘L (e.symm : _ →L[R] _) = g.prodMap h :=
    ext fun ⟨u, w⟩ ↦ (congrArg e (hf u w)).trans (by simp)
  rw [← det_conj f e, hconj, det_prodMap]

end ContinuousLinearMap

end
