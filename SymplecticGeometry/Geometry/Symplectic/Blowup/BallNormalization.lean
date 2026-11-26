/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.IsotopyExtension.Ball.Basic
import SymplecticGeometry.Geometry.Symplectic.IsotopyExtension.Ball.GermFamily
import SymplecticGeometry.Geometry.Symplectic.IsotopyExtension.Ball.TransitionGerm
import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Basic

/-!
# Normalization of a family of symplectic ball embeddings

Let `ψ` be a smooth family over `[0, 1]` of symplectic embeddings of the closed ball `B(r)`,
`0 < r`, of `StdSpace (Fin n)` into a manifold `(M, σ)` of dimension `2n`, all centred at the
same point `p₀`, and with `ψ_1 = ψ_0` near `0`. We find a jointly smooth family `χ` of
symplectomorphisms of `B(r)` with `χ_0 = χ_1 = id` and `ψ_t ∘ χ_t = ψ_0` near `0` for every `t`
(`SymplecticGeometry.exists_family_comp_eqOn`). So, after reparametrizing each `ψ_t` by a
symplectomorphism of the ball, the family is constant near the centre. This is the second part
of McDuff–Salamon, Proposition 7.1.22; the first part, that any two ball embeddings are moved
onto each other near `0` by a Hamiltonian diffeotopy, is
`SymplecticGeometry.exists_hamiltonian_comp_eqOn`.

Here a symplectomorphism of `B(r)` is a symplectic ball embedding of radius `r` for the standard
form `ω₀` that maps `B(r)` onto itself.

The proof puts two earlier steps together:

1. The transition germs `κ_t = ψ_t⁻¹ ∘ ψ_0` near `0` form a smooth family of symplectic ball
   embeddings of `StdSpace (Fin n)` fixing `0`, which are the identity where `ψ_t = ψ_0`
   (`SymplecticGeometry.IsSymplecticBallFamily.exists_transitionGerm`). Since `ψ_1 = ψ_0` near
   `0`, both `κ_0` and `κ_1` are the identity on their ball.
2. Such a family of germs agrees near `0` with a smooth family `χ` of symplectomorphisms of
   `B(r)`, which is the identity wherever `κ_t` is
   (`SymplecticGeometry.IsSymplecticBallFamily.exists_symplectomorphism_family_eq_of_map_zero`,
   built from the polar decomposition of the loop of derivatives `dκ_t(0)`).

Then `ψ_t ∘ χ_t = ψ_t ∘ κ_t = ψ_0` near `0`, and `χ_0 = χ_1 = id`.

## Main results

* `SymplecticGeometry.exists_family_comp_eqOn`: the normalization of a family of ball embeddings
  with a fixed centre.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Proposition 7.1.22.
-/

public section

open Set Filter Metric
open scoped ContDiff Manifold Topology

namespace SymplecticGeometry

open TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {n : ℕ} {σ : SmoothTwoForm I M}

/-- **Normalization of a family of symplectic ball embeddings.** Let `ψ` satisfy
`IsSymplecticBallFamily σ r ψ` with `0 < r`, into a manifold of dimension `2n`, with
`ψ (t, 0) = p₀` for every `t` and `ψ (1, ·) = ψ (0, ·)` near `0`. Then there is a smooth map
`χ : [0, 1] × StdSpace (Fin n) → StdSpace (Fin n)` such that
* each `χ_t` is a symplectic embedding of `B(r)` for `ω₀` and maps `B(r)` onto itself;
* `χ_0` and `χ_1` are the identity;
* for some `ρ > 0`, `ψ (t, χ (t, z)) = ψ (0, z)` for every `t` and every `z ∈ B(ρ)`.

Together with `exists_hamiltonian_comp_eqOn`, which moves any ball embedding onto another near
`0` by a compactly supported Hamiltonian diffeotopy, this is McDuff–Salamon, Proposition 7.1.22.

Milestone: *Normalization of symplectic ball embeddings*. -/
theorem exists_family_comp_eqOn (hdim : Module.finrank ℝ E = 2 * n) {r : ℝ} (hr : 0 < r)
    {ψ : unitInterval × StdSpace (Fin n) → M} (hψ : IsSymplecticBallFamily σ r ψ) {p₀ : M}
    (hfix : ∀ t, ψ (t, 0) = p₀) (h₁ : (fun z ↦ ψ (1, z)) =ᶠ[𝓝 0] fun z ↦ ψ (0, z)) :
    ∃ χ : unitInterval × StdSpace (Fin n) → StdSpace (Fin n),
      ContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, StdSpace (Fin n))) 𝓘(ℝ, StdSpace (Fin n)) ∞ χ ∧
      (∀ t, IsSymplecticBallEmbedding (stdForm (Fin n)).constSmooth r fun z ↦ χ (t, z)) ∧
      (∀ t, (fun z ↦ χ (t, z)) '' closedBall 0 r = closedBall 0 r) ∧
      (∀ z, χ (0, z) = z) ∧ (∀ z, χ (1, z) = z) ∧
      ∃ ρ, 0 < ρ ∧ ∀ t, EqOn (fun z ↦ ψ (t, χ (t, z))) (fun z ↦ ψ (0, z)) (closedBall 0 ρ) := by
  obtain ⟨ε, hε, hε₁⟩ := (nhds_basis_closedBall.eventually_iff).1 h₁
  obtain ⟨δ, hδ, hδε, κ, hκ, hκ0, hκ₀, hψκ, hκid⟩ :=
    hψ.exists_transitionGerm (by rw [finrank_stdSpace, Fintype.card_fin, hdim]) hr
      (fun t ↦ (hfix t).trans (hfix 0).symm) hε
  obtain ⟨ε', hε', χ, hχ, hχemb, hχimg, hχκ, hχid⟩ :=
    hκ.exists_symplectomorphism_family_eq_of_map_zero hδ hr hκ0
  refine ⟨χ, hχ, hχemb, hχimg, hχid 0 hκ₀,
    hχid 1 fun z hz ↦ hκid 1 z hz (hε₁ (closedBall_subset_closedBall hδε hz)),
    min ε' δ, lt_min hε' hδ, fun t z hz ↦ ?_⟩
  have hz' : z ∈ closedBall (0 : StdSpace (Fin n)) δ :=
    closedBall_subset_closedBall (min_le_right _ _) hz
  exact (congrArg (fun w ↦ ψ (t, w))
    (hχκ t z (closedBall_subset_closedBall (min_le_left _ _) hz))).trans (hψκ t z hz')

end SymplecticGeometry

end
