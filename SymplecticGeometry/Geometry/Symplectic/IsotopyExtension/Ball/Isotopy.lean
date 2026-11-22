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
import TauCeti.Geometry.Manifold.Immersion.Differential
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

1. For `ρ < ρ' < r`, the slices of `e` are injective immersions along `B(ρ')`
   (`SymplecticGeometry.IsSymplecticBallEmbedding.injective_mfderiv`), hence smooth embeddings of
   a neighbourhood of `B(ρ')` (`TauCeti.exists_isOpen_forall_isSmoothEmbedding_of_injOn`), and so
   of the open ball `P = ball 0 ρ'`. Thus `e` is a smooth isotopy `k` of `P`
   (`TauCeti.SmoothIsotopy.ofForallIsSmoothEmbedding`), and `k` is symplectic.
2. The velocity forms of `k` are closed
   (`TauCeti.SmoothIsotopy.IsSymplectic.mextDeriv_mpullback_prodMk_velocityForm`). Since `P` is
   star-convex, they have a jointly smooth family of primitives `h (t, ·)` (`SymplecticGeometry.`
   `IsSmoothlyContractible.exists_contMDiff_mextDeriv_eq_of_forall_mem_closedForms`).
3. `TauCeti.SmoothIsotopy.exists_hasHamiltonian_forall_apply_eq`, with the compact set `B(ρ)`,
   concludes.

## Main results

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
  obtain ⟨U, hUo, hrU, heU⟩ := he.exists_contMDiffOn
  obtain ⟨ρ', hρρ', hρ'r⟩ := exists_between hρr
  have hr : 0 < r := by linarith
  have hBr : closedBall (0 : StdSpace (Fin n)) ρ' ⊆ closedBall 0 r :=
    closedBall_subset_closedBall (by linarith)
  -- The slices of `e` are smooth embeddings of a neighbourhood `V` of `B(ρ')`.
  obtain ⟨V, hKV, -, hV⟩ := exists_isOpen_forall_isSmoothEmbedding_of_injOn hUo heU
    (isCompact_closedBall 0 ρ') (hBr.trans hrU)
    (fun t ↦ (he.isSymplecticBallEmbedding t).injOn.mono hBr)
    fun t z hz ↦ (he.isSymplecticBallEmbedding t).injective_mfderiv hr (hBr hz)
  -- So they are smooth embeddings of the open ball `P = ball 0 ρ'`.
  let P : TopologicalSpace.Opens (StdSpace (Fin n)) := ⟨ball 0 ρ', isOpen_ball⟩
  have hPr : (P : Set (StdSpace (Fin n))) ⊆ closedBall 0 r := ball_subset_closedBall.trans hBr
  have hPV : (P : Set (StdSpace (Fin n))) ⊆ V := ball_subset_closedBall.trans hKV
  have heP : ContMDiffOn ((𝓡∂ 1).prod 𝓘(ℝ, StdSpace (Fin n))) I ∞ e
      (univ ×ˢ (P : Set (StdSpace (Fin n)))) :=
    heU.mono (prod_mono subset_rfl (hrU.trans' hPr))
  have hslice (t : unitInterval) : ContMDiffOn 𝓘(ℝ, StdSpace (Fin n)) I ∞ (fun z ↦ e (t, z)) U :=
    heU.comp (contMDiffOn_const.prodMk contMDiffOn_id) fun z hz ↦ ⟨mem_univ _, hz⟩
  have hemb (t : unitInterval) :
      Manifold.IsSmoothEmbedding 𝓘(ℝ, StdSpace (Fin n)) I ∞ (fun z : P ↦ e (t, z)) := by
    refine ⟨(isImmersion_comp_subtypeVal_iff (f := fun z ↦ e (t, z))).2 fun z hz ↦
      ((hslice t).isImmersionAt_iff_injective_mfderiv hUo (hrU (hPr hz)) (by simp)).2
        ((he.isSymplecticBallEmbedding t).injective_mfderiv hr (hPr hz)), ?_⟩
    exact (hV t).isEmbedding.comp (Topology.IsEmbedding.inclusion hPV)
  let f (t : unitInterval) : C^∞⟮𝓘(ℝ, StdSpace (Fin n)), P; I, M⟯ :=
    ⟨fun z ↦ e (t, z), (hslice t).comp_contMDiff contMDiff_subtypeVal fun z ↦ hrU (hPr z.property)⟩
  have hf (t : unitInterval) (z : P) : f t z = e (t, z) := by
    simp only [f, ContMDiffMap.coeFn_mk]
  let k := SmoothIsotopy.ofForallIsSmoothEmbedding heP hemb (f₀ := f 0) (f₁ := f 1)
    (fun z ↦ (hf 0 z).symm) fun z ↦ (hf 1 z).symm
  have hk (p : unitInterval × P) : k p = e (p.1, p.2) :=
    SmoothIsotopy.ofForallIsSmoothEmbedding_apply _ _ _ _ p
  -- `k` is symplectic, so its velocity forms are closed.
  have hks : k.IsSymplectic (SmoothForm.mpullback (Subtype.val : P → StdSpace (Fin n))
      contMDiff_subtypeVal (stdForm (Fin n)).constSmooth) σ := by
    refine SmoothIsotopy.isSymplectic_def.2 fun t ↦ funext fun z ↦ ?_
    have hz : (z : StdSpace (Fin n)) ∈ closedBall 0 r := hPr z.property
    have hcomp : (fun x : P ↦ k (t, x)) = (fun y ↦ e (t, y)) ∘ Subtype.val :=
      funext fun x ↦ hk (t, x)
    rw [hcomp, mpullback_comp_at ((contMDiff_subtypeVal (n := 1) z).mdifferentiableAt one_ne_zero)
      (((hslice t) _ (hrU hz)).contMDiffAt (hUo.mem_nhds (hrU hz)) |>.mdifferentiableAt
        (by simp)), SmoothForm.coe_mpullback,
      mpullback_apply_eq_compContinuousLinearMapCLM Subtype.val,
      (he.isSymplecticBallEmbedding t).mpullback_eq_of_mem_closedBall hr hz,
      ← mpullback_apply_eq_compContinuousLinearMapCLM]
  set α : unitInterval → SmoothForm 𝓘(ℝ, StdSpace (Fin n)) P ℝ 1 := fun t ↦
    SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) (k.velocityForm σ)
  have hcl (t : unitInterval) : α t ∈ closedForms 𝓘(ℝ, StdSpace (Fin n)) P 1 :=
    (mem_closedForms_iff_mextDerivₗ_eq_zero _ _).2 <| Subtype.ext <| by
      rw [mextDerivₗ_apply, ZeroMemClass.coe_zero]
      exact hks.mextDeriv_mpullback_prodMk_velocityForm hσ.isClosed t
  -- The ball `P` is smoothly contractible, so the velocity forms have smooth primitives.
  have hPc : IsSmoothlyContractible 𝓘(ℝ, StdSpace (Fin n)) P :=
    .of_starConvex_image (φ := id) (ψ := id) contMDiffOn_id contMDiffOn_id (fun _ _ ↦ rfl)
      (by rw [image_id]; exact (convex_ball 0 ρ').starConvex (mem_ball_self (by linarith)))
      ⟨0, mem_ball_self (by linarith)⟩
  obtain ⟨h, hh, hdh⟩ :=
    hPc.exists_contMDiff_mextDeriv_eq_of_forall_mem_closedForms
      (isSmoothFamily_def.2 ⟨k.velocityForm σ, fun _ ↦ rfl⟩)
      hcl
  -- The compact set `B(ρ)`, seen in `P`.
  have hLP : closedBall (0 : StdSpace (Fin n)) ρ ⊆ P := closedBall_subset_ball (by linarith)
  have hL : IsCompact (Subtype.val ⁻¹' closedBall 0 ρ : Set P) := by
    rw [Subtype.isCompact_iff, image_preimage_eq_of_subset (by rwa [Subtype.range_coe])]
    exact isCompact_closedBall 0 ρ
  obtain ⟨Φ, F, K, hK, hΦ, hF, hFK, hΦK, happly⟩ :=
    k.exists_hasHamiltonian_forall_apply_eq hσ (by simp [hdim, two_mul]) hL hh
      fun t ↦ (hdh t).symm
  refine ⟨Φ, F, K, hK, hΦ, hF, hFK, hΦK, fun t z hz ↦ ?_⟩
  simpa [hk, hf] using happly t ⟨z, hLP hz⟩ hz

end SymplecticGeometry

end
