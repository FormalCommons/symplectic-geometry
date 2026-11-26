/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Stabilizer

/-!
# Compactly supported form-preserving isotopies joining two diffeomorphisms

Let `σ` be a smooth form on a manifold `M`. Tau Ceti's subgroup
`TauCeti.SmoothForm.compactIsotopyStabilizer σ` consists of the final maps `Φ₁` of the
diffeotopies `Φ` all of whose time slices preserve `σ` and which are the identity outside one
compact set at all times. For a symplectic form these are the symplectomorphisms joined to the
identity by a compactly supported symplectic isotopy, the equivalence under which Dehn twists are
well defined.

Two diffeomorphisms `φ` and `ψ` are joined by such an isotopy, `Φ₁ ∘ φ = ψ`, exactly when
`ψ * φ⁻¹` lies in the subgroup
(`TauCeti.SmoothForm.mul_inv_mem_compactIsotopyStabilizer_iff`). So the subgroup laws say that
this relation is reflexive, symmetric and transitive.

## Main results

* `TauCeti.SmoothForm.mul_inv_mem_compactIsotopyStabilizer_iff`: `ψ * φ⁻¹` lies in the
  subgroup exactly when a compactly supported `σ`-preserving diffeotopy `Φ` has `Φ₁ ∘ φ = ψ`.

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

/-- For diffeomorphisms `φ` and `ψ`, the quotient `ψ * φ⁻¹` lies in the compactly supported
isotopy stabilizer of `σ` exactly when there is a diffeotopy `Φ`, preserving `σ` at all times and
fixing every point outside a compact set at all times, with `Φ₁ ∘ φ = ψ`. -/
theorem mul_inv_mem_compactIsotopyStabilizer_iff {φ ψ : M ≃ₘ⟮J, J⟯ M} :
    ψ * φ⁻¹ ∈ compactIsotopyStabilizer σ ↔
      ∃ (Φ : Diffeotopy J ∞ M) (K : Set M), IsCompact K ∧
      (∀ t, Φ.timeSlice t ∈ diffeomorphStabilizer σ) ∧ (∀ t x, x ∉ K → Φ (t, x) = x) ∧
      ∀ x, Φ.final (φ x) = ψ x := by
  have h (Φ : Diffeotopy J ∞ M) : Φ.final = ψ * φ⁻¹ ↔ ∀ x, Φ.final (φ x) = ψ x := by
    rw [eq_mul_inv_iff_mul_eq, Diffeomorph.ext_iff]
    simp only [Diffeomorph.mul_apply]
  simp only [mem_compactIsotopyStabilizer, h]
  constructor
  · rintro ⟨Φ, ⟨K, hK, hΦK⟩, hΦ, hfin⟩
    exact ⟨Φ, K, hK, hΦ, fun t x hx ↦ hΦK t (mem_compl hx), hfin⟩
  · rintro ⟨Φ, K, hK, hΦ, hΦK, hfin⟩
    exact ⟨Φ, ⟨K, hK, fun t x hx ↦ hΦK t x (notMem_of_mem_compl hx)⟩, hΦ, hfin⟩

end TauCeti.SmoothForm

end
