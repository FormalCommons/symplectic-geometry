/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Stabilizer

/-!
# Compactly supported form-preserving diffeotopies between two diffeomorphisms

Let `σ` be a smooth form on a manifold `M`. Say that a diffeomorphism `ψ` of `M` is reached from
a diffeomorphism `φ` if there are a diffeotopy `Φ` of `M` and a compact set `K ⊆ M` such that
every time slice of `Φ` preserves `σ`, `Φ` fixes every point outside `K` at all times, and
`Φ₁ ∘ φ = ψ`. This file shows that this relation is reflexive, symmetric and transitive: the
constant diffeotopy joins `φ` to itself, the pointwise inverse `Φ.symm` goes back from `ψ` to `φ`,
and the pointwise composite `Φ.trans Ψ`, with the union of the compact sets, composes two
steps. For a symplectic form these are compactly supported symplectic isotopies, the relation
under which Dehn twists are well defined.

## Main results

* `TauCeti.Diffeotopy.exists_isCompact_final_apply_eq_self`: every diffeomorphism is reached
  from itself.
* `TauCeti.Diffeotopy.exists_isCompact_final_apply_eq_symm`: if `ψ` is reached from `φ`, then
  `φ` is reached from `ψ`.
* `TauCeti.Diffeotopy.exists_isCompact_final_apply_eq_trans`: if `ψ` is reached from `φ` and `χ`
  from `ψ`, then `χ` is reached from `φ`.

## References

* [P. Seidel, *Lectures on four-dimensional Dehn twists*][Seidel2008], §1a.
-/

public section

noncomputable section

open Set
open scoped ContDiff Manifold

namespace TauCeti.Diffeotopy

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {J : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold J 1 M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ} {σ : SmoothForm J M F k}

/-- Every diffeomorphism `φ` is joined to itself by a compactly supported diffeotopy preserving
`σ`: the constant diffeotopy, supported in the empty set. -/
theorem exists_isCompact_final_apply_eq_self (σ : SmoothForm J M F k) (φ : M ≃ₘ⟮J, J⟯ M) :
    ∃ (Φ : Diffeotopy J ∞ M) (K : Set M), IsCompact K ∧
      (∀ t, Φ.timeSlice t ∈ SmoothForm.diffeomorphStabilizer σ) ∧
      (∀ t x, x ∉ K → Φ (t, x) = x) ∧ ∀ x, Φ.final (φ x) = φ x :=
  ⟨refl J ∞ M, ∅, isCompact_empty, SmoothForm.timeSlice_refl_mem_diffeomorphStabilizer,
    fun _ _ _ ↦ refl_apply _, fun _ ↦ by rw [final_refl, Diffeomorph.coe_refl, id_eq]⟩

/-- If `Φ₁ ∘ φ = ψ` for a diffeotopy `Φ` preserving `σ` and fixing every point outside a compact
set `K`, then the pointwise inverse of `Φ`, with the same `K`, satisfies `(Φ⁻¹)₁ ∘ ψ = φ`. -/
theorem exists_isCompact_final_apply_eq_symm {φ ψ : M ≃ₘ⟮J, J⟯ M}
    (h : ∃ (Φ : Diffeotopy J ∞ M) (K : Set M), IsCompact K ∧
      (∀ t, Φ.timeSlice t ∈ SmoothForm.diffeomorphStabilizer σ) ∧
      (∀ t x, x ∉ K → Φ (t, x) = x) ∧ ∀ x, Φ.final (φ x) = ψ x) :
    ∃ (Φ : Diffeotopy J ∞ M) (K : Set M), IsCompact K ∧
      (∀ t, Φ.timeSlice t ∈ SmoothForm.diffeomorphStabilizer σ) ∧
      (∀ t x, x ∉ K → Φ (t, x) = x) ∧ ∀ x, Φ.final (ψ x) = φ x := by
  obtain ⟨Φ, K, hK, hΦσ, hΦK, hΦ⟩ := h
  refine ⟨Φ.symm, K, hK, SmoothForm.timeSlice_symm_mem_diffeomorphStabilizer hΦσ,
    fun t x hx ↦ (Φ.symm_apply_eq_self_iff).2 (hΦK t x hx), fun x ↦ ?_⟩
  rw [final_symm, ← hΦ, Diffeomorph.symm_apply_apply]

/-- If `Φ₁ ∘ φ = ψ` and `Ψ₁ ∘ ψ = χ` for diffeotopies `Φ` and `Ψ` preserving `σ` and fixing every
point outside compact sets `K` and `L`, then their pointwise composite `Φ.trans Ψ`, which fixes
every point outside `K ∪ L`, satisfies `(Φ.trans Ψ)₁ ∘ φ = χ`. -/
theorem exists_isCompact_final_apply_eq_trans {φ ψ χ : M ≃ₘ⟮J, J⟯ M}
    (h₁ : ∃ (Φ : Diffeotopy J ∞ M) (K : Set M), IsCompact K ∧
      (∀ t, Φ.timeSlice t ∈ SmoothForm.diffeomorphStabilizer σ) ∧
      (∀ t x, x ∉ K → Φ (t, x) = x) ∧ ∀ x, Φ.final (φ x) = ψ x)
    (h₂ : ∃ (Ψ : Diffeotopy J ∞ M) (L : Set M), IsCompact L ∧
      (∀ t, Ψ.timeSlice t ∈ SmoothForm.diffeomorphStabilizer σ) ∧
      (∀ t x, x ∉ L → Ψ (t, x) = x) ∧ ∀ x, Ψ.final (ψ x) = χ x) :
    ∃ (Φ : Diffeotopy J ∞ M) (K : Set M), IsCompact K ∧
      (∀ t, Φ.timeSlice t ∈ SmoothForm.diffeomorphStabilizer σ) ∧
      (∀ t x, x ∉ K → Φ (t, x) = x) ∧ ∀ x, Φ.final (φ x) = χ x := by
  obtain ⟨Φ, K, hK, hΦσ, hΦK, hΦ⟩ := h₁
  obtain ⟨Ψ, L, hL, hΨσ, hΨL, hΨ⟩ := h₂
  refine ⟨Φ.trans Ψ, K ∪ L, hK.union hL,
    SmoothForm.timeSlice_trans_mem_diffeomorphStabilizer hΦσ hΨσ, fun t x hx ↦ ?_, fun x ↦ ?_⟩
  · rw [mem_union, not_or] at hx
    rw [trans_apply, hΦK t x hx.1, hΨL t x hx.2]
  · rw [final_trans, Diffeomorph.coe_trans, Function.comp_apply, hΦ, hΨ]

end TauCeti.Diffeotopy

end
