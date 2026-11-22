/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.IsotopyExtension.Ball.Basic
public import SymplecticGeometry.Geometry.Symplectic.IsotopyExtension.Flow
import SymplecticGeometry.Geometry.Manifold.DeRham.FamilyPrimitive
import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.Neighborhood
import TauCeti.Geometry.Manifold.Immersion.LocalDiffeomorph

/-!
# Hamiltonian extension of families of symplectic balls

Let `e : [0, 1] × StdSpace (Fin n) → M` be a family, smooth in both variables, of symplectic
embeddings of the closed ball `B(r)` (`SymplecticGeometry.IsSymplecticBallFamily σ r e`) into a
symplectic manifold of dimension `2n`. On every smaller closed ball `B(ρ)`, `ρ < r`, the family is
the restriction of a compactly supported Hamiltonian diffeotopy `Φ` of `M` that keeps its times:
`Φ_t (e_0 z) = e_t z` for `z ∈ B(ρ)` and every `t`
(`SymplecticGeometry.IsSymplecticBallFamily.exists_hasHamiltonian_forall_apply_eq`). This is the
last step of the proof of the ball extension of McDuff–Salamon, Theorem 3.3.1.

The proof:

1. The slices of `e` are injective immersions along `B(r)`
   (`SymplecticGeometry.IsSymplecticBallEmbedding.injective_mfderiv`), hence smooth embeddings of
   an open neighbourhood `V` of `B(r)` (`TauCeti.exists_isOpen_forall_isSmoothEmbedding_of_injOn`),
   and so of every open `P ⊆ V`. Thus `e` is a smooth isotopy of each such `P`
   (`TauCeti.SmoothIsotopy.ofForallIsSmoothEmbedding`;
   `SymplecticGeometry.IsSymplecticBallFamily.exists_smoothIsotopy`). For `ρ < ρ' < r`, take for
   `k` the isotopy of the open ball `P = ball 0 ρ'`; it is symplectic.
2. The velocity forms of `k` are closed
   (`TauCeti.SmoothIsotopy.IsSymplectic.mextDeriv_mpullback_prodMk_velocityForm`). Since `P` is
   convex, it is smoothly contractible (`Convex.isSmoothlyContractible`), and the forms have a
   jointly smooth family of primitives `h (t, ·)`
   (`IsSmoothlyContractible.exists_contMDiff_mextDeriv_eq_of_forall_mem_closedForms`).
3. `TauCeti.SmoothIsotopy.exists_hasHamiltonian_forall_apply_eq`, with the compact set `B(ρ)`,
   concludes.

## Main results

* `SymplecticGeometry.IsSymplecticBallFamily.exists_smoothIsotopy`: for `0 < r`, a smooth family
  of symplectic embeddings of `B(r)` is a smooth isotopy of every open set inside some open
  neighbourhood of `B(r)`.
* `SymplecticGeometry.IsSymplecticBallFamily.exists_hasHamiltonian_forall_apply_eq`: a smooth
  family of symplectic embeddings of `B(r)` is, on `B(ρ)` for `0 ≤ ρ < r`, the restriction of a
  compactly supported Hamiltonian diffeotopy.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Theorem 3.3.1.
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

/-- A smooth family of symplectic embeddings of `B(r)`, `0 < r`, is a smooth isotopy near
`B(r)`: there is an open neighbourhood `V` of `B(r)` such that on every open set `P ⊆ V` the
family `e` is a smooth isotopy `k` of `P` into `M`, with `k (t, z) = e (t, z)`. -/
theorem IsSymplecticBallFamily.exists_smoothIsotopy [FiniteDimensional ℝ E] [I.Boundaryless]
    [T2Space M] {r : ℝ} (hr : 0 < r)
    {e : unitInterval × StdSpace (Fin n) → M} (he : IsSymplecticBallFamily σ r e) :
    ∃ V : TopologicalSpace.Opens (StdSpace (Fin n)),
      closedBall 0 r ⊆ (V : Set (StdSpace (Fin n))) ∧
      ∀ P : TopologicalSpace.Opens (StdSpace (Fin n)), (P : Set (StdSpace (Fin n))) ⊆ V →
        ∃ (f₀ f₁ : C^∞⟮𝓘(ℝ, StdSpace (Fin n)), P; I, M⟯) (k : SmoothIsotopy f₀ f₁),
          ∀ p, k p = e (p.1, p.2) := by
  obtain ⟨U, hUo, hrU, heU⟩ := he.exists_contMDiffOn
  -- The slices of `e` are smooth embeddings of a neighbourhood `V` of `B(r)`.
  obtain ⟨V, hrV, hVU, hV⟩ := exists_isOpen_forall_isSmoothEmbedding_of_injOn hUo heU
    (isCompact_closedBall 0 r) hrU (fun t ↦ (he.isSymplecticBallEmbedding t).injOn)
    fun t z hz ↦ (he.isSymplecticBallEmbedding t).injective_mfderiv hr hz
  refine ⟨V, hrV, fun P hPV ↦ ?_⟩
  have heP : ContMDiffOn ((𝓡∂ 1).prod 𝓘(ℝ, StdSpace (Fin n))) I ∞ e
      (univ ×ˢ (P : Set (StdSpace (Fin n)))) :=
    heU.mono (prod_mono subset_rfl (hPV.trans hVU))
  -- Restricted to `P ⊆ V`, the slices are still smooth embeddings.
  have hemb (t : unitInterval) :
      Manifold.IsSmoothEmbedding 𝓘(ℝ, StdSpace (Fin n)) I ∞ (fun z : P ↦ e (t, z)) :=
    ⟨(isImmersion_comp_subtypeVal_iff (f := fun z ↦ e (t, z))).2 fun z hz ↦
      (isImmersion_comp_subtypeVal_iff (f := fun z ↦ e (t, z))).1 (hV t).isImmersion z (hPV hz),
      (hV t).isEmbedding.comp (Topology.IsEmbedding.inclusion hPV)⟩
  have hslice (t : unitInterval) :
      ContMDiff 𝓘(ℝ, StdSpace (Fin n)) I ∞ (fun z : P ↦ e (t, z)) :=
    (hemb t).isImmersion.contMDiff
  exact ⟨⟨_, hslice 0⟩, ⟨_, hslice 1⟩, SmoothIsotopy.ofForallIsSmoothEmbedding heP hemb
    (fun _ ↦ rfl) fun _ ↦ rfl, SmoothIsotopy.ofForallIsSmoothEmbedding_apply _ _ _ _⟩

/-- **Hamiltonian extension of a family of symplectic balls.** Let `σ` be a symplectic form on a
Hausdorff, σ-compact, boundaryless manifold `M` of dimension `2n`, and `e` a smooth family over
`[0, 1]` of symplectic embeddings of the closed ball `B(r)` of `StdSpace (Fin n)`. For
`0 ≤ ρ < r` there are a diffeotopy `Φ` of `M`, a function `F` on `M × [0, 1]` and a compact set
`K ⊆ M` such that `Φ` is a compactly supported Hamiltonian diffeotopy with Hamiltonian `F`, read
along the motion, `F` vanishes and `Φ_t` is the identity off `K`, and `Φ_t (e_0 z) = e_t z` for
every `t` and every `z ∈ B(ρ)`. -/
theorem IsSymplecticBallFamily.exists_hasHamiltonian_forall_apply_eq [FiniteDimensional ℝ E]
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] (hσ : σ.IsSymplectic)
    (hdim : Module.finrank ℝ E = 2 * n) {ρ r : ℝ} (hρ : 0 ≤ ρ) (hρr : ρ < r)
    {e : unitInterval × StdSpace (Fin n) → M} (he : IsSymplecticBallFamily σ r e) :
    ∃ (Φ : Diffeotopy I ∞ M) (F : M × unitInterval → ℝ) (K : Set M), IsCompact K ∧
      Φ.IsCompactlySupportedHamiltonian σ ∧ Φ.HasHamiltonian σ F ∧ (∀ p, p.1 ∉ K → F p = 0) ∧
      (∀ t, ∀ y ∉ K, Φ (t, y) = y) ∧ ∀ t, ∀ z ∈ closedBall 0 ρ, Φ (t, e (0, z)) = e (t, z) := by
  obtain ⟨ρ', hρρ', hρ'r⟩ := exists_between hρr
  have hr : 0 < r := by linarith
  obtain ⟨U, hUo, hrU, heU⟩ := he.exists_contMDiffOn
  obtain ⟨V, hrV, hV⟩ := he.exists_smoothIsotopy hr
  -- On the open ball `P = ball 0 ρ'`, the family `e` is a smooth isotopy `k`.
  let P : TopologicalSpace.Opens (StdSpace (Fin n)) := ⟨ball 0 ρ', isOpen_ball⟩
  have hPr : (P : Set (StdSpace (Fin n))) ⊆ closedBall 0 r :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall hρ'r.le)
  obtain ⟨f₀, f₁, k, hk⟩ := hV P (hPr.trans hrV)
  -- `k` is symplectic, so its velocity forms are closed.
  have hks : k.IsSymplectic (SmoothForm.mpullback (Subtype.val : P → StdSpace (Fin n))
      contMDiff_subtypeVal (stdForm (Fin n)).constSmooth) σ := by
    refine SmoothIsotopy.isSymplectic_def.2 fun t ↦ funext fun z ↦ ?_
    have hz : (z : StdSpace (Fin n)) ∈ closedBall 0 r := hPr z.property
    have hcomp : (fun x : P ↦ k (t, x)) = (fun y ↦ e (t, y)) ∘ Subtype.val :=
      funext fun x ↦ hk (t, x)
    have hslice : ContMDiffOn 𝓘(ℝ, StdSpace (Fin n)) I ∞ (fun y ↦ e (t, y)) U :=
      heU.comp (contMDiffOn_const.prodMk contMDiffOn_id) fun y hy ↦ ⟨mem_univ _, hy⟩
    rw [hcomp, mpullback_comp_at ((contMDiff_subtypeVal (n := 1) z).mdifferentiableAt one_ne_zero)
      ((hslice _ (hrU hz)).contMDiffAt (hUo.mem_nhds (hrU hz)) |>.mdifferentiableAt
        (by simp)), SmoothForm.coe_mpullback_subtype_val_apply, mpullback_subtype_val_apply,
      (he.isSymplecticBallEmbedding t).mpullback_eq_of_mem_closedBall hr hz]
  set α : unitInterval → SmoothForm 𝓘(ℝ, StdSpace (Fin n)) P ℝ 1 := fun t ↦
    SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) (k.velocityForm σ)
  have hcl (t : unitInterval) : α t ∈ closedForms 𝓘(ℝ, StdSpace (Fin n)) P 1 :=
    (mem_closedForms_iff_mextDerivₗ_eq_zero _ _).2 <| Subtype.ext <| by
      rw [mextDerivₗ_apply, ZeroMemClass.coe_zero]
      exact hks.mextDeriv_mpullback_prodMk_velocityForm hσ.isClosed t
  -- The ball `P` is smoothly contractible, so the velocity forms have smooth primitives.
  obtain ⟨h, hh, hdh⟩ :=
    (Convex.isSmoothlyContractible (convex_ball 0 ρ') ⟨0, mem_ball_self (by linarith)⟩
      ).exists_contMDiff_mextDeriv_eq_of_forall_mem_closedForms
      (isSmoothFamily_def.2 ⟨k.velocityForm σ, fun _ ↦ rfl⟩) hcl
  -- The compact set `B(ρ)`, seen in `P`.
  have hLP : closedBall (0 : StdSpace (Fin n)) ρ ⊆ P := closedBall_subset_ball hρρ'
  obtain ⟨Φ, F, K, hK, hΦ, hF, hFK, hΦK, happly⟩ :=
    k.exists_hasHamiltonian_forall_apply_eq hσ (by simp [hdim, two_mul])
      (Topology.IsInducing.subtypeVal.isCompact_preimage' (isCompact_closedBall 0 ρ)
        (by rwa [Subtype.range_coe])) hh fun t ↦ (hdh t).symm
  refine ⟨Φ, F, K, hK, hΦ, hF, hFK, hΦK, fun t z hz ↦ ?_⟩
  have h0 := hk (0, ⟨z, hLP hz⟩)
  rw [SmoothIsotopy.apply_zero] at h0
  simpa [h0, hk] using happly t ⟨z, hLP hz⟩ hz

end SymplecticGeometry

end
