/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Flux.CompactSupport
public import SymplecticGeometry.Geometry.Symplectic.IsotopyExtension.Ball.Basic
import SymplecticGeometry.Geometry.Symplectic.IsotopyExtension.Ball.Isotopy
import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Homogeneity

/-!
# Moving one symplectic ball onto another

On a connected symplectic manifold `(M, σ)` of dimension `2n`, without boundary, Hausdorff and
σ-compact, any two symplectic embeddings `ψ₀`, `ψ₁` of the closed ball `B(r)`, `0 < r`, agree
near `0` up to a compactly supported Hamiltonian diffeotopy: there are `0 < ρ` and such a
diffeotopy `Φ` with `Φ_1 ∘ ψ₀ = ψ₁` on `B(ρ)`
(`SymplecticGeometry.exists_hamiltonian_comp_eqOn`). If the two embeddings have the same centre,
`Φ` fixes that centre at all times. This is the first part of McDuff–Salamon, Proposition 7.1.22.

The proof joins the centres `ψ₀ 0` and `ψ₁ 0` by a smooth path: the constant path if they are
equal, and otherwise the path `t ↦ Ψ_t (ψ₀ 0)` along a diffeotopy `Ψ` with `Ψ_1 (ψ₀ 0) = ψ₁ 0`,
which Tau Ceti's homogeneity lemma `TauCeti.exists_diffeotopy_final_apply_eq` gives. A path of
centres is a smooth family of symplectic embeddings of `B(0)`
(`SymplecticGeometry.IsSymplecticBallFamily.of_path`), with ends `ψ₀` and `ψ₁` on `B(0)`.
The Hamiltonian extension of such a family with prescribed ends
(`SymplecticGeometry.IsSymplecticBallFamily.exists_hasHamiltonian_extension`, with `r₀ = 0`)
gives `Φ`, a radius `ρ > 0` with `Φ_1 ∘ ψ₀ = ψ₁` on `B(ρ)`, and `Φ_t (ψ₀ 0)` equal to the path at
time `t`. So no rescaling of the embeddings and no path in the symplectic group is needed here:
they are inside the extension theorem.

## Main results

* `SymplecticGeometry.exists_hamiltonian_comp_eqOn`: two symplectic embeddings of `B(r)` agree
  near `0` after a compactly supported Hamiltonian diffeotopy, which fixes a common centre.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Proposition 7.1.22 and Theorem 3.3.1.
-/

public section

noncomputable section

open Set Function Metric
open scoped ContDiff Manifold

namespace SymplecticGeometry

open TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {n : ℕ} {σ : SmoothTwoForm I M}

/-- **Moving one symplectic ball onto another.** Let `σ` be a symplectic form on a preconnected,
Hausdorff, σ-compact, boundaryless manifold `M` of dimension `2n`, and let `ψ₀`, `ψ₁` be
symplectic embeddings of the closed ball `B(r)` of `StdSpace (Fin n)`, `0 < r`. Then there are a
compactly supported Hamiltonian diffeotopy `Φ` of `M` and a radius `ρ > 0` such that
`Φ_1 ∘ ψ₀ = ψ₁` on `B(ρ)`; if `ψ₀ 0 = ψ₁ 0`, then `Φ_t` fixes this point for every `t`. -/
theorem exists_hamiltonian_comp_eqOn [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] [PreconnectedSpace M] (hσ : σ.IsSymplectic)
    (hdim : Module.finrank ℝ E = 2 * n) {r : ℝ} (hr : 0 < r) {ψ₀ ψ₁ : StdSpace (Fin n) → M}
    (hψ₀ : IsSymplecticBallEmbedding σ r ψ₀) (hψ₁ : IsSymplecticBallEmbedding σ r ψ₁) :
    ∃ (Φ : Diffeotopy I ∞ M) (ρ : ℝ), 0 < ρ ∧ Φ.IsCompactlySupportedHamiltonian σ ∧
      EqOn (Φ.final ∘ ψ₀) ψ₁ (closedBall 0 ρ) ∧ (ψ₀ 0 = ψ₁ 0 → ∀ t, Φ (t, ψ₀ 0) = ψ₀ 0) := by
  -- A smooth path `c` of centres from `ψ₀ 0` to `ψ₁ 0`, constant if they are equal.
  obtain ⟨c, hc, hc₀, hc₁, hconst⟩ : ∃ c : unitInterval → M, ContMDiff (𝓡∂ 1) I ∞ c ∧
      c 0 = ψ₀ 0 ∧ c 1 = ψ₁ 0 ∧ (ψ₀ 0 = ψ₁ 0 → ∀ t, c t = ψ₀ 0) := by
    by_cases h : ψ₀ 0 = ψ₁ 0
    · exact ⟨fun _ ↦ ψ₀ 0, contMDiff_const, rfl, h, fun _ _ ↦ rfl⟩
    obtain ⟨Ψ, -, -, -, hΨ⟩ :=
      exists_diffeotopy_final_apply_eq (I := I) (n := ∞) (m := ⊤) le_top le_rfl (ψ₀ 0) (ψ₁ 0)
    exact ⟨fun t ↦ Ψ (t, ψ₀ 0), Ψ.contMDiff.comp (contMDiff_id.prodMk contMDiff_const),
      Ψ.apply_zero _, by rw [← hΨ, Diffeotopy.final_apply], fun h' ↦ (h h').elim⟩
  -- The path is a family of balls of radius `0` with ends `ψ₀` and `ψ₁` on `B(0)`.
  have hend {ψ : StdSpace (Fin n) → M} {i : unitInterval} (hi : c i = ψ 0) :
      ∀ z ∈ closedBall (0 : StdSpace (Fin n)) 0, c (i, z).1 = ψ z := by
    intro z hz
    rw [closedBall_zero, mem_singleton_iff] at hz
    rw [hz, hi]
  obtain ⟨ρ, hρ, -, Φ, -, -, -, hΦ, -, -, -, hc', hfinal⟩ :=
    (IsSymplecticBallFamily.of_path (σ := σ) (n := n) hc).exists_hasHamiltonian_extension hσ
      hdim le_rfl hr hψ₀ hψ₁ (hend hc₀) (hend hc₁)
  refine ⟨Φ, ρ, hρ, hΦ, fun z hz ↦ hfinal z hz, fun h t ↦ ?_⟩
  rw [hc' t 0 (mem_closedBall_self le_rfl), hconst h t]

end SymplecticGeometry

end
