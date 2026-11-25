/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.IsotopyExtension.Ball.Basic
public import SymplecticGeometry.Geometry.Symplectic.IsotopyExtension.Flow
import SymplecticGeometry.Geometry.Symplectic.IsotopyExtension.Ball.Interpolation
import SymplecticGeometry.Geometry.Symplectic.IsotopyExtension.Ball.Moser
import TauCeti.Topology.MetricSpace.SeparatedBalls
import SymplecticGeometry.Geometry.Manifold.DeRham.FamilyPrimitive
import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.Neighborhood

/-!
# The symplectic ball extension

This file proves the ball extension theorem of McDuff–Salamon, Theorem 3.3.1
(`SymplecticGeometry.exists_ballEmbedding_extension_and_hasHamiltonian_extension`).

Let `e : [0, 1] × StdSpace (Fin n) → M` be a family, smooth in both variables, of symplectic
embeddings of the closed ball `B(r)` (`SymplecticGeometry.IsSymplecticBallFamily σ r e`) into a
symplectic manifold of dimension `2n`. On every smaller closed ball `B(ρ)`, `ρ < r`, the family is
the restriction of a compactly supported Hamiltonian diffeotopy `Φ` of `M` that keeps its times:
`Φ_t (e_0 z) = e_t z` for `z ∈ B(ρ)` and every `t`
(`SymplecticGeometry.IsSymplecticBallFamily.exists_hasHamiltonian_forall_apply_eq`). The proof:

1. The slices of `e` are injective immersions along `B(r)`
   (`SymplecticGeometry.IsSymplecticBallEmbedding.injective_mfderiv`), hence smooth embeddings of
   an open neighbourhood `V` of `B(r)` (`TauCeti.exists_isOpen_forall_isSmoothEmbedding_of_injOn`).
   Thus `e` is a smooth isotopy of `V` (`TauCeti.SmoothIsotopy.ofForallIsSmoothEmbedding`;
   `SymplecticGeometry.IsSymplecticBallFamily.exists_smoothIsotopy`). For `ρ < ρ' < r`, take for
   `k` its restriction to the open ball `P = ball 0 ρ'` (`TauCeti.SmoothIsotopy.restrict`); it is
   symplectic (`SymplecticGeometry.IsSymplecticBallFamily.exists_smoothIsotopy_isSymplectic`).
2. The velocity forms of `k` are closed
   (`TauCeti.SmoothIsotopy.IsSymplectic.mextDeriv_mpullback_prodMk_velocityForm`). Since `P` is
   convex, it is smoothly contractible (`Convex.isSmoothlyContractible`), and the forms have a
   jointly smooth family of primitives `h (t, ·)`
   (`IsSmoothlyContractible.exists_contMDiff_mextDeriv_eq_of_forall_mem_closedForms`).
3. `TauCeti.SmoothIsotopy.exists_hasHamiltonian_forall_apply_eq`, with the compact set `B(ρ)`,
   concludes.

Given symplectic embeddings `j₀`, `j₁` of `B(r)` and a family `e` of symplectic embeddings of a
smaller ball `B(r₀)`, `0 ≤ r₀ < r`, with ends `j₀` and `j₁` on `B(r₀)`,
`SymplecticGeometry.IsSymplecticBallFamily.exists_hasHamiltonian_extension` combines three steps:

1. `SymplecticGeometry.IsSymplecticBallFamily.exists_contMDiffOn_eqOn_mpullback_eq` gives a family
   `k`, smooth near `[0, 1] × B(r₀)`, equal to `e` on `B(r₀)` and pulling `σ` back to `ω₀` there,
   whose ends are `j₀` and `j₁` on an open set `U ⊇ B(r₀)`.
2. On `U ∩ ball 0 r` its ends pull `σ` back to `ω₀`, as `j₀` and `j₁` do, so Moser's argument
   with a parameter (`SymplecticGeometry.exists_isSymplecticBallFamily_eqOn_of_mpullback_eq`)
   changes `k` away from `B(r₀)`, keeping both ends, into a family `k'` of symplectic embeddings
   of a ball `B(r₁)`, `r₀ < r₁`. Its forms are compared on `ℝ²ⁿ`, as the errata of McDuff–Salamon
   correct the source.
3. For `r₀ < ρ < r₁` with `B(ρ) ⊆ U ∩ ball 0 r`, the first theorem applied to `k'` on `B(ρ)` gives
   `Φ`; then `Φ_1 ∘ j₀ = k'_1 = j₁` on `B(ρ)`.

The milestone theorem is the conjunction of this extension and the enlargement of a single ball,
`SymplecticGeometry.IsSymplecticBallEmbedding.exists_lt_isSymplecticBallEmbedding_eqOn`.

## Main results

* `SymplecticGeometry.IsSymplecticBallFamily.exists_smoothIsotopy`: for `0 < r`, a smooth family
  of symplectic embeddings of `B(r)` is a smooth isotopy of some open neighbourhood of `B(r)`.
* `SymplecticGeometry.IsSymplecticBallFamily.exists_smoothIsotopy_isSymplectic`: on an open set
  `P ⊆ B(r)`, such a family is a symplectic isotopy of `P`.
* `SymplecticGeometry.IsSymplecticBallFamily.exists_hasHamiltonian_forall_apply_eq`: a smooth
  family of symplectic embeddings of `B(r)` is, on `B(ρ)` for `0 ≤ ρ < r`, the restriction of a
  compactly supported Hamiltonian diffeotopy.
* `SymplecticGeometry.IsSymplecticBallFamily.exists_hasHamiltonian_extension`: a family of
  symplectic balls of radius `r₀` with ends `j₀`, `j₁` extends to a compactly supported
  Hamiltonian diffeotopy that keeps its times and takes `j₀` to `j₁` on a ball `B(ρ)`, `r₀ < ρ`.
* `SymplecticGeometry.exists_ballEmbedding_extension_and_hasHamiltonian_extension`: the symplectic
  ball extension.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Theorem 3.3.1.
* [D. McDuff and D. Salamon, *Errata for Introduction to Symplectic Topology, Third
  Edition*][McDuffSalamon2019Errata], p. 114.
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
`B(r)`: there is an open neighbourhood `V` of `B(r)` on which the family `e` is a smooth isotopy
`k` of `V` into `M`, with `k (t, z) = e (t, z)`. -/
theorem IsSymplecticBallFamily.exists_smoothIsotopy [FiniteDimensional ℝ E] [I.Boundaryless]
    [T2Space M] {r : ℝ} (hr : 0 < r)
    {e : unitInterval × StdSpace (Fin n) → M} (he : IsSymplecticBallFamily σ r e) :
    ∃ V : TopologicalSpace.Opens (StdSpace (Fin n)),
      closedBall 0 r ⊆ (V : Set (StdSpace (Fin n))) ∧
      ∃ (f₀ f₁ : C^∞⟮𝓘(ℝ, StdSpace (Fin n)), V; I, M⟯) (k : SmoothIsotopy f₀ f₁),
        ∀ p, k p = e (p.1, p.2) := by
  obtain ⟨U, hUo, hrU, heU⟩ := he.exists_contMDiffOn
  -- The slices of `e` are smooth embeddings of a neighbourhood `V` of `B(r)`.
  obtain ⟨V, hrV, hVU, hV⟩ := exists_isOpen_forall_isSmoothEmbedding_of_injOn hUo heU
    (isCompact_closedBall 0 r) hrU (fun t ↦ (he.isSymplecticBallEmbedding t).injOn)
    fun t z hz ↦ (he.isSymplecticBallEmbedding t).injective_mfderiv hr hz
  exact ⟨V, hrV, ⟨_, (hV 0).isImmersion.contMDiff⟩, ⟨_, (hV 1).isImmersion.contMDiff⟩,
    SmoothIsotopy.ofForallIsSmoothEmbedding (heU.mono (prod_mono subset_rfl hVU)) hV
      (fun _ ↦ rfl) fun _ ↦ rfl, SmoothIsotopy.ofForallIsSmoothEmbedding_apply _ _ _ _⟩

/-- A smooth family `e` of symplectic embeddings of `B(r)`, `0 < r`, restricts on every open set
`P ⊆ B(r)` to a symplectic isotopy `k` of `P` with `k (t, z) = e (t, z)`: every slice of `k`
pulls `σ` back to the restriction to `P` of the standard form `ω₀`. -/
theorem IsSymplecticBallFamily.exists_smoothIsotopy_isSymplectic [FiniteDimensional ℝ E]
    [I.Boundaryless] [T2Space M] {r : ℝ} (hr : 0 < r)
    {e : unitInterval × StdSpace (Fin n) → M} (he : IsSymplecticBallFamily σ r e)
    {P : TopologicalSpace.Opens (StdSpace (Fin n))}
    (hPr : (P : Set (StdSpace (Fin n))) ⊆ closedBall 0 r) :
    ∃ (f₀ f₁ : C^∞⟮𝓘(ℝ, StdSpace (Fin n)), P; I, M⟯) (k : SmoothIsotopy f₀ f₁),
      (∀ p, k p = e (p.1, p.2)) ∧ k.IsSymplectic (SmoothForm.mpullback
        (Subtype.val : P → StdSpace (Fin n)) contMDiff_subtypeVal (stdForm (Fin n)).constSmooth)
        σ := by
  obtain ⟨U, hUo, hrU, heU⟩ := he.exists_contMDiffOn
  obtain ⟨V, hrV, f₀, f₁, kV, hkV⟩ := he.exists_smoothIsotopy hr
  let k := kV.restrict (V := P) (hPr.trans hrV)
  have hk (p : unitInterval × P) : k p = e (p.1, p.2) :=
    (SmoothIsotopy.restrict_apply _ _ p).trans (hkV _)
  refine ⟨_, _, k, hk, SmoothIsotopy.isSymplectic_def.2 fun t ↦ funext fun z ↦ ?_⟩
  have hz : (z : StdSpace (Fin n)) ∈ closedBall 0 r := hPr z.property
  have hcomp : (fun x : P ↦ k (t, x)) = (fun y ↦ e (t, y)) ∘ Subtype.val :=
    funext fun x ↦ hk (t, x)
  have hslice : ContMDiffOn 𝓘(ℝ, StdSpace (Fin n)) I ∞ (fun y ↦ e (t, y)) U :=
    heU.comp (contMDiffOn_const.prodMk contMDiffOn_id) fun y hy ↦ ⟨mem_univ _, hy⟩
  rw [hcomp, mpullback_comp_at ((contMDiff_subtypeVal (n := 1) z).mdifferentiableAt one_ne_zero)
    ((hslice _ (hrU hz)).contMDiffAt (hUo.mem_nhds (hrU hz)) |>.mdifferentiableAt
      (by simp)), SmoothForm.coe_mpullback_subtype_val_apply, mpullback_subtype_val_apply,
    (he.isSymplecticBallEmbedding t).mpullback_eq_of_mem_closedBall hr hz]

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
  -- On the open ball `P = ball 0 ρ'`, the family `e` is a symplectic isotopy `k`.
  let P : TopologicalSpace.Opens (StdSpace (Fin n)) := ⟨ball 0 ρ', isOpen_ball⟩
  obtain ⟨f₀, f₁, k, hk, hks⟩ := he.exists_smoothIsotopy_isSymplectic hr (P := P)
    (ball_subset_closedBall.trans (closedBall_subset_closedBall hρ'r.le))
  -- Its velocity forms are closed.
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
      (isSmoothFamily_mpullback_prodMk _) hcl
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

/-- **Hamiltonian extension of a family of symplectic balls with prescribed ends.** Let `σ` be a
symplectic form on a Hausdorff, σ-compact, boundaryless manifold `M` of dimension `2n`, let
`0 ≤ r₀ < r`, let `j₀`, `j₁` be symplectic embeddings of `B(r)`, and let `e` be a smooth family
over `[0, 1]` of symplectic embeddings of `B(r₀)` with `e_0 = j₀` and `e_1 = j₁` on `B(r₀)`. Then
there are a radius `ρ` with `r₀ < ρ < r`, a compactly supported Hamiltonian diffeotopy `Φ` of `M`
with Hamiltonian `F`, and a compact set `K ⊆ M` off which `F` vanishes and every `Φ_t` is the
identity, such that `Φ_t (j₀ z) = e_t z` for every `t` and `z ∈ B(r₀)`, and
`Φ_1 (j₀ z) = j₁ z` for `z ∈ B(ρ)`. -/
theorem IsSymplecticBallFamily.exists_hasHamiltonian_extension [FiniteDimensional ℝ E]
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] (hσ : σ.IsSymplectic)
    (hdim : Module.finrank ℝ E = 2 * n) {r₀ r : ℝ} (hr₀ : 0 ≤ r₀) (hr₀r : r₀ < r)
    {j₀ j₁ : StdSpace (Fin n) → M} (hj₀ : IsSymplecticBallEmbedding σ r j₀)
    (hj₁ : IsSymplecticBallEmbedding σ r j₁) {e : unitInterval × StdSpace (Fin n) → M}
    (he : IsSymplecticBallFamily σ r₀ e)
    (he₀ : ∀ z ∈ closedBall 0 r₀, e (0, z) = j₀ z)
    (he₁ : ∀ z ∈ closedBall 0 r₀, e (1, z) = j₁ z) :
    ∃ ρ, r₀ < ρ ∧ ρ < r ∧ ∃ (Φ : Diffeotopy I ∞ M) (F : M × unitInterval → ℝ) (K : Set M),
      IsCompact K ∧ Φ.IsCompactlySupportedHamiltonian σ ∧ Φ.HasHamiltonian σ F ∧
      (∀ p, p.1 ∉ K → F p = 0) ∧ (∀ t, ∀ y ∉ K, Φ (t, y) = y) ∧
      (∀ t, ∀ z ∈ closedBall 0 r₀, Φ (t, j₀ z) = e (t, z)) ∧
      ∀ z ∈ closedBall 0 ρ, Φ.final (j₀ z) = j₁ z := by
  -- Steps 1 and 2: a family `k` that is right along `B(r₀)`, with ends `j₀` and `j₁` near it.
  obtain ⟨k, U, hUo, hKU, hk, hke, hkK, hk₀, hk₁⟩ :=
    he.exists_contMDiffOn_eqOn_mpullback_eq hσ.isNondegenerate hdim hr₀ hr₀r hj₀ hj₁ he₀ he₁
  -- On `W = U ∩ ball 0 r`, the ends of `k` pull `σ` back to `ω₀`, as `j₀` and `j₁` do.
  set W := U ∩ ball (0 : StdSpace (Fin n)) r
  have hWo : IsOpen W := hUo.inter isOpen_ball
  have hKW : closedBall (0 : StdSpace (Fin n)) r₀ ⊆ W :=
    subset_inter hKU (closedBall_subset_ball hr₀r)
  have hend {j : StdSpace (Fin n) → M} (hj : IsSymplecticBallEmbedding σ r j) (i : unitInterval)
      (hki : ∀ z ∈ U, k (i, z) = j z) (z : StdSpace (Fin n)) (hz : z ∈ W) :
      mpullback 𝓘(ℝ, StdSpace (Fin n)) I (fun z ↦ k (i, z)) σ.val z =
        (stdForm (Fin n)).constSmooth.val z := by
    rw [Filter.EventuallyEq.mpullback_eq (Filter.eventuallyEq_of_mem (hUo.mem_nhds hz.1) hki)]
    exact hj.mpullback_eq hz.2
  -- Step 3: Moser's argument makes `k` a family of symplectic balls of a radius `r₁ > r₀`.
  obtain ⟨r₁, hr₁, k', hk', hk'K, hk'₀, hk'₁⟩ :=
    exists_isSymplecticBallFamily_eqOn_of_mpullback_eq hσ.isClosed hr₀ hWo hKW
      (hk.mono (prod_mono subset_rfl inter_subset_left))
      (fun t ↦ (he.isSymplecticBallEmbedding t).injOn.congr fun z hz ↦ (hke t z hz).symm) hkK
      (hend hj₀ 0 hk₀) (hend hj₁ 1 hk₁)
  -- Choose `ρ` with `B(ρ) ⊆ W` and `r₀ < ρ < min r₁ r`.
  obtain ⟨ρ', hρ', hρ'W⟩ := hWo.exists_gt_closedBall_subset hKW
  obtain ⟨ρ, hr₀ρ, hρ⟩ := exists_between (lt_min (lt_min hρ' hr₁) hr₀r)
  have hρW : closedBall (0 : StdSpace (Fin n)) ρ ⊆ W :=
    (closedBall_subset_closedBall (hρ.le.trans ((min_le_left _ _).trans (min_le_left _ _)))).trans
      hρ'W
  -- Step 4: the Hamiltonian extension of `k'` on `B(ρ)`.
  obtain ⟨Φ, F, K, hK, hΦ, hF, hFK, hΦK, happly⟩ :=
    hk'.exists_hasHamiltonian_forall_apply_eq hσ hdim (hr₀.trans hr₀ρ.le)
      (hρ.trans_le ((min_le_left _ _).trans (min_le_right _ _)))
  have hj₀k' (z : StdSpace (Fin n)) (hz : z ∈ closedBall 0 ρ) : j₀ z = k' (0, z) := by
    rw [hk'₀, hk₀ z (hρW hz).1]
  refine ⟨ρ, hr₀ρ, hρ.trans_le (min_le_right _ _), Φ, F, K, hK, hΦ, hF, hFK, hΦK,
    fun t z hz ↦ ?_, fun z hz ↦ ?_⟩
  · have hzρ : z ∈ closedBall 0 ρ := closedBall_subset_closedBall hr₀ρ.le hz
    rw [hj₀k' z hzρ, happly t z hzρ, hk'K t z hz, hke t z hz]
  · rw [Diffeotopy.final_apply, hj₀k' z hz, happly 1 z hz, hk'₁, hk₁ z (hρW hz).1]

/-- **Symplectic ball extension.** Let `σ` be a symplectic form on a Hausdorff, σ-compact,
boundaryless manifold `M` of dimension `2n`, and let `B(r)` be the closed ball of radius `r` in
`StdSpace (Fin n)`, with the standard form.

1. For `0 < r₀`, every symplectic embedding `j` of `B(r₀)` agrees on `B(r₀)` with a symplectic
   embedding `j'` of some `B(r)`, `r₀ < r`.
2. For `0 ≤ r₀ < r`, symplectic embeddings `j₀`, `j₁` of `B(r)` and a smooth family `e` over
   `[0, 1]` of symplectic embeddings of `B(r₀)` with `e_0 = j₀` and `e_1 = j₁` on `B(r₀)`, there
   are `ρ` with `r₀ < ρ < r` and a compactly supported Hamiltonian diffeotopy `Φ` of `M`, with
   Hamiltonian `F` and a compact set `K` off which `F` vanishes and every `Φ_t` is the identity,
   such that `Φ_t (j₀ z) = e_t z` for every `t` and `z ∈ B(r₀)`, and `Φ_1 (j₀ z) = j₁ z` for
   `z ∈ B(ρ)`.

Milestone: *Symplectic ball extension*. -/
theorem exists_ballEmbedding_extension_and_hasHamiltonian_extension [FiniteDimensional ℝ E]
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] (hσ : σ.IsSymplectic)
    (hdim : Module.finrank ℝ E = 2 * n) :
    (∀ r₀, 0 < r₀ → ∀ j : StdSpace (Fin n) → M, IsSymplecticBallEmbedding σ r₀ j →
      ∃ r, r₀ < r ∧ ∃ j', IsSymplecticBallEmbedding σ r j' ∧ EqOn j' j (closedBall 0 r₀)) ∧
    ∀ r₀ r, 0 ≤ r₀ → r₀ < r → ∀ (j₀ j₁ : StdSpace (Fin n) → M)
      (e : unitInterval × StdSpace (Fin n) → M), IsSymplecticBallEmbedding σ r j₀ →
      IsSymplecticBallEmbedding σ r j₁ → IsSymplecticBallFamily σ r₀ e →
      (∀ z ∈ closedBall 0 r₀, e (0, z) = j₀ z) → (∀ z ∈ closedBall 0 r₀, e (1, z) = j₁ z) →
      ∃ ρ, r₀ < ρ ∧ ρ < r ∧ ∃ (Φ : Diffeotopy I ∞ M) (F : M × unitInterval → ℝ) (K : Set M),
        IsCompact K ∧ Φ.IsCompactlySupportedHamiltonian σ ∧ Φ.HasHamiltonian σ F ∧
        (∀ p, p.1 ∉ K → F p = 0) ∧ (∀ t, ∀ y ∉ K, Φ (t, y) = y) ∧
        (∀ t, ∀ z ∈ closedBall 0 r₀, Φ (t, j₀ z) = e (t, z)) ∧
        ∀ z ∈ closedBall 0 ρ, Φ.final (j₀ z) = j₁ z :=
  ⟨fun _ hr₀ _ hj ↦ hj.exists_lt_isSymplecticBallEmbedding_eqOn hσ.isClosed hr₀,
    fun _ _ hr₀ hr₀r _ _ _ hj₀ hj₁ he he₀ he₁ ↦
      he.exists_hasHamiltonian_extension hσ hdim hr₀ hr₀r hj₀ hj₁ he₀ he₁⟩

end SymplecticGeometry

end
