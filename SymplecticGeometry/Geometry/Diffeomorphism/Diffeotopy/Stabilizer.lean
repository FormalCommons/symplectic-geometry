/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Diffeomorphism.Diffeotopy.Support
public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Stabilizer

/-!
# Compactly supported form-preserving isotopies

Let `σ` be a smooth form on a manifold `M`. This file defines the subgroup
`TauCeti.SmoothForm.compactlySupportedIsotopyStabilizer σ` of the diffeomorphisms of `M`: the
final maps `Φ₁` of the diffeotopies `Φ` all of whose time slices preserve `σ` and which fix every
point outside some compact set `K` at all times. For a symplectic form these are the
symplectomorphisms joined to the identity by a compactly supported symplectic isotopy, the
equivalence under which Dehn twists are well defined.

It is the compactly supported analogue of Tau Ceti's `TauCeti.SmoothForm.isotopyStabilizer`, and
is built in the same way, from Tau Ceti's constant diffeotopy `TauCeti.Diffeotopy.refl`,
pointwise composite `TauCeti.Diffeotopy.trans` and pointwise inverse `TauCeti.Diffeotopy.symm`;
the composite of two diffeotopies supported in `K` and `L` is supported in `K ∪ L`
(`TauCeti.Diffeotopy.mul_apply_eq_self_of_notMem_union`).

Two diffeomorphisms `φ` and `ψ` are joined by such an isotopy, `Φ₁ ∘ φ = ψ`, exactly when
`ψ * φ⁻¹` lies in the subgroup
(`TauCeti.SmoothForm.mul_inv_mem_compactlySupportedIsotopyStabilizer_iff`). So the subgroup laws
say that this relation is reflexive, symmetric and transitive.

## Main definitions

* `TauCeti.SmoothForm.compactlySupportedIsotopyStabilizer σ`: the final maps of the compactly
  supported diffeotopies preserving `σ` at every time.

## Main results

* `TauCeti.SmoothForm.mem_compactlySupportedIsotopyStabilizer`: membership, unfolded.
* `TauCeti.SmoothForm.mul_inv_mem_compactlySupportedIsotopyStabilizer_iff`: `ψ * φ⁻¹` lies in the
  subgroup exactly when a compactly supported `σ`-preserving diffeotopy `Φ` has `Φ₁ ∘ φ = ψ`.
* `TauCeti.SmoothForm.compactlySupportedIsotopyStabilizer_le_isotopyStabilizer`: the subgroup
  lies in Tau Ceti's isotopy stabilizer.

## References

* [P. Seidel, *Lectures on four-dimensional Dehn twists*][Seidel2008], §1a.
-/

public section

noncomputable section

open Set
open scoped ContDiff Manifold

namespace TauCeti.SmoothForm

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {J : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold J 1 M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ} {σ : SmoothForm J M F k}

/-- The **compactly supported isotopy stabilizer** of a smooth form `σ`: the final maps `Φ₁` of
the smooth diffeotopies `Φ` all of whose time slices preserve `σ` and which fix every point
outside a compact set at all times. -/
def compactlySupportedIsotopyStabilizer (σ : SmoothForm J M F k) : Subgroup (M ≃ₘ⟮J, J⟯ M) where
  carrier := {χ | ∃ (Φ : Diffeotopy J ∞ M) (K : Set M), IsCompact K ∧
    (∀ t, Φ.timeSlice t ∈ diffeomorphStabilizer σ) ∧ (∀ t x, x ∉ K → Φ (t, x) = x) ∧
    Φ.final = χ}
  one_mem' := ⟨Diffeotopy.refl J ∞ M, ∅, isCompact_empty,
    timeSlice_refl_mem_diffeomorphStabilizer, fun _ _ _ ↦ Diffeotopy.refl_apply _,
    Diffeotopy.final_refl⟩
  mul_mem' := by
    rintro _ _ ⟨Φ, K, hK, hΦ, hΦK, rfl⟩ ⟨Ψ, L, hL, hΨ, hΨL, rfl⟩
    refine ⟨Ψ.trans Φ, L ∪ K, hL.union hK, timeSlice_trans_mem_diffeomorphStabilizer hΨ hΦ,
      fun t x hx ↦ ?_, by rw [Diffeotopy.final_trans, Diffeomorph.mul_def]⟩
    rw [← Diffeotopy.mul_def]
    exact Diffeotopy.mul_apply_eq_self_of_notMem_union hΨL hΦK t x hx
  inv_mem' := by
    rintro _ ⟨Φ, K, hK, hΦ, hΦK, rfl⟩
    exact ⟨Φ.symm, K, hK, timeSlice_symm_mem_diffeomorphStabilizer hΦ,
      fun t x hx ↦ Φ.symm_apply_eq_self_iff.2 (hΦK t x hx),
      by rw [Diffeotopy.final_symm, Diffeomorph.inv_def]⟩

/-- A diffeomorphism lies in the compactly supported isotopy stabilizer of `σ` exactly when it is
the final map of a diffeotopy all of whose time slices preserve `σ` and which fixes every point
outside a compact set at all times. -/
theorem mem_compactlySupportedIsotopyStabilizer {χ : M ≃ₘ⟮J, J⟯ M} :
    χ ∈ compactlySupportedIsotopyStabilizer σ ↔
      ∃ (Φ : Diffeotopy J ∞ M) (K : Set M), IsCompact K ∧
      (∀ t, Φ.timeSlice t ∈ diffeomorphStabilizer σ) ∧ (∀ t x, x ∉ K → Φ (t, x) = x) ∧
      Φ.final = χ :=
  Iff.rfl

/-- For diffeomorphisms `φ` and `ψ`, the quotient `ψ * φ⁻¹` lies in the compactly supported
isotopy stabilizer of `σ` exactly when there is a diffeotopy `Φ`, preserving `σ` at all times and
fixing every point outside a compact set at all times, with `Φ₁ ∘ φ = ψ`. -/
theorem mul_inv_mem_compactlySupportedIsotopyStabilizer_iff {φ ψ : M ≃ₘ⟮J, J⟯ M} :
    ψ * φ⁻¹ ∈ compactlySupportedIsotopyStabilizer σ ↔
      ∃ (Φ : Diffeotopy J ∞ M) (K : Set M), IsCompact K ∧
      (∀ t, Φ.timeSlice t ∈ diffeomorphStabilizer σ) ∧ (∀ t x, x ∉ K → Φ (t, x) = x) ∧
      ∀ x, Φ.final (φ x) = ψ x := by
  have h (Φ : Diffeotopy J ∞ M) : Φ.final = ψ * φ⁻¹ ↔ ∀ x, Φ.final (φ x) = ψ x := by
    rw [eq_mul_inv_iff_mul_eq, Diffeomorph.ext_iff]
    simp only [Diffeomorph.mul_apply]
  simp only [mem_compactlySupportedIsotopyStabilizer, h]

/-- A diffeomorphism joined to the identity by a compactly supported `σ`-preserving isotopy is
joined to it by a `σ`-preserving isotopy. -/
theorem compactlySupportedIsotopyStabilizer_le_isotopyStabilizer :
    compactlySupportedIsotopyStabilizer σ ≤ isotopyStabilizer σ := by
  rintro _ ⟨Φ, -, -, hΦ, -, rfl⟩
  exact final_mem_isotopyStabilizer hΦ

end TauCeti.SmoothForm

end
