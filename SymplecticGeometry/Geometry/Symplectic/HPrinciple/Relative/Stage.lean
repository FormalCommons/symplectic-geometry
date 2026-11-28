/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.HPrinciple.Relative.StagePath
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.Basic
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Symplectic.Topology
import SymplecticGeometry.Geometry.Symplectic.HPrinciple.Relative.CoreApproximation

/-!
# One stage of the relative h-principle

Let `c` be a band core of a continuous function `g : M → ℝ` on a manifold `M`, for the levels
`a₀`, `a`, `b` (`Morse/Core/Basic.lean`). A stage of the parametric relative h-principle starts
from families of two-forms `τ l`, nondegenerate for the parameters `l` of a compact set `K`, of
closed two-forms `α l` and of one-forms `β l`, such that `τ l = α l + d (β l)` on an open
neighbourhood `N` of `{g ≤ a}` for every `l`, and on all of `M` for `l` in a closed set `P₀`.
It returns a homotopy `H (l, ·)` of two-forms from `τ l`, nondegenerate for `l ∈ K`, and new
families `α' l = e_l^* α l` and `β' l`, for the end `e_l` of an isotopy from the identity, such
that

* nothing changes on a neighbourhood `V` of `{g ≤ a}`;
* `α' l` is closed, and `α' l - α l = d γ` for a one-form `γ` that vanishes on `V`;
* `H (l, 1) = α' l + d (β' l)` on an open neighbourhood of `{g ≤ b}`;
* for `l ∈ P₀`, the homotopy runs through closed forms cohomologous to `α l`, and
  `H (l, 1) = α' l + d (β' l)` on all of `M`.

The homotopy is `SymplecticGeometry.stagePath` (`Relative/StagePath.lean`), for the isotopy
and cutoff of `SymplecticGeometry.exists_stagePath`, applied to the displacements and corrected
one-forms of holonomic approximation over the cubes of `c` (`Relative/CoreApproximation.lean`).

## Main results

* `SymplecticGeometry.isSmoothFamily_stagePath`: the path of a stage is a smooth family over
  `L × [0, 1]` when its data are smooth families over normed spaces.
* `SymplecticGeometry.continuous_tangentEquiv_symm_stagePath`: the path of a stage is
  continuous into the frame topology of a covering frame system when `τ` and `α` are, the
  one-forms are a smooth family read through a continuous map, and the parameter space of the
  isotopy is finite-dimensional.
* `SymplecticGeometry.BandCore.exists_stage_family`: the stage for smooth families over a
  finite-dimensional normed space `L`, nondegenerate over a compact `K ⊆ L`.
* `SymplecticGeometry.BandCore.exists_stage_continuous_family`: the stage for families over a
  compact Hausdorff space `P`, with two-forms continuous into the frame topology of a covering
  frame system and one-forms `B (s l)` for a smooth family `B` over a finite-dimensional normed
  space `S` and a continuous `s : P → S`. The new one-forms have the same shape, over
  `S × ((i : c.ι) → Fin (n i) → ℝ)`.

Both forms use the lemmas of `Relative/StagePath.lean` for all conclusions but the regularity of
the homotopy in the parameter, which is the only place where they differ besides the call to
holonomic approximation. The family of two-forms is called `τ`, as in `Relative/StagePath.lean`,
since `ω` is notation in the scope `ContDiff`.

## References

* [Y. Eliashberg and N. Mishachev, *Introduction to the h-principle*][EliashbergMishachev2002],
  §10.2.
-/

public section

open Set Filter TauCeti
open scoped Manifold ContDiff Topology

namespace SymplecticGeometry

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]

section Smooth

variable {L : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L]

/-- The path of a stage is a smooth family over `L × [0, 1]` when `τ` and `α` are smooth families
over `L`, `B'` is a smooth family over `S` and `s : L → S` is smooth. -/
theorem isSmoothFamily_stagePath {e : (S × unitInterval) × M → M}
    (he : ContMDiff ((𝓘(ℝ, S).prod (𝓡∂ 1)).prod I) I ∞ e) {ρ : M → ℝ}
    (hρ : ContMDiff I 𝓘(ℝ) ∞ ρ) {s : L → S} (hs : ContMDiff 𝓘(ℝ, L) 𝓘(ℝ, S) ∞ s)
    {τ α : L → SmoothTwoForm I M} (hτ : IsSmoothFamily 𝓘(ℝ, L) τ)
    (hα : IsSmoothFamily 𝓘(ℝ, L) α) {B' : S → SmoothForm I M ℝ 1}
    (hB' : IsSmoothFamily 𝓘(ℝ, S) B') :
    IsSmoothFamily (𝓘(ℝ, L).prod (𝓡∂ 1)) (stagePath he hρ s τ α B') := by
  have hA := (collaredFirstHalf (n := ∞) le_rfl).contMDiff
  have hC : ContMDiff (𝓡∂ 1) 𝓘(ℝ) ∞ fun t ↦ (collaredSecondHalf (n := ∞) le_rfl t : ℝ) :=
    contMDiff_subtypeVal_Icc.comp (collaredSecondHalf (n := ∞) le_rfl).contMDiff
  have hs' : ContMDiff (𝓘(ℝ, L).prod (𝓡∂ 1)) 𝓘(ℝ, S) ∞ fun p : L × unitInterval ↦ s p.1 :=
    hs.comp contMDiff_fst
  -- The first term: `τ l` pulled back along the isotopy run at the speed `A`.
  have h₁ := (hτ.comp Prod.fst contMDiff_fst).mpullback_family
    (f := fun q : (L × unitInterval) × M ↦
      e ((s q.1.1, collaredFirstHalf (n := ∞) le_rfl q.1.2), q.2))
    (he.comp (((hs'.comp contMDiff_fst).prodMk
      (hA.comp (contMDiff_snd.comp contMDiff_fst))).prodMk contMDiff_snd))
  -- The second term: the correction pulled back along the end of the isotopy, cut off by `ρ`.
  have h₂ := ((((hα.comp Prod.fst contMDiff_fst).add
      (hB'.mextDeriv.comp (fun p : L × unitInterval ↦ s p.1) hs')).sub
      (hτ.comp Prod.fst contMDiff_fst)).mpullback_family
    (f := fun q : (L × unitInterval) × M ↦ e ((s q.1.1, 1), q.2))
    (he.comp (((hs'.comp contMDiff_fst).prodMk contMDiff_const).prodMk
      contMDiff_snd))).funSMul ⟨ρ, hρ⟩ |>.fun_smul (hC.comp contMDiff_snd)
  convert h₁.add h₂ using 1
  exact funext (stagePath_def he hρ s τ α B')

end Smooth

section Continuous

open _root_.Bundle

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ S] {Λ : Type*} [TopologicalSpace Λ]
  {ι : Type*}
  (fr : ι → Trivialization (E [⋀^Fin 2]→L[ℝ] ℝ)
    (π (E [⋀^Fin 2]→L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x [⋀^Fin 2]→L[ℝ] Trivial M ℝ x)))
  [∀ j, MemTrivializationAtlas (fr j)]
  (W : ι → TopologicalSpace.Opens M) (hW : ∀ j, (W j : Set M) ⊆ (fr j).baseSet)

/-- The path of a stage is continuous into the frame topology of a covering frame system of the
two-forms on `M`, when `τ` and `α` are, `s : Λ → S` is continuous, `S` is finite-dimensional and
`B'` is a smooth family over `S`. -/
theorem continuous_tangentEquiv_symm_stagePath (hcover : ∀ x, ∃ j, x ∈ W j)
    {e : (S × unitInterval) × M → M}
    (he : ContMDiff ((𝓘(ℝ, S).prod (𝓡∂ 1)).prod I) I ∞ e) {ρ : M → ℝ}
    (hρ : ContMDiff I 𝓘(ℝ) ∞ ρ) {s : Λ → S} (hs : Continuous s)
    {τ α : Λ → SmoothTwoForm I M}
    (hτ : let _ := ContMDiffSection.frameTopology (I := I) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) fr W hW
      Continuous fun l ↦ Bundle.ContMDiffTwoForm.tangentEquiv.symm (τ l))
    (hα : let _ := ContMDiffSection.frameTopology (I := I) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) fr W hW
      Continuous fun l ↦ Bundle.ContMDiffTwoForm.tangentEquiv.symm (α l))
    {B' : S → SmoothForm I M ℝ 1} (hB' : IsSmoothFamily 𝓘(ℝ, S) B') :
    let _ := ContMDiffSection.frameTopology (I := I) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) fr W hW
    Continuous fun p ↦ Bundle.ContMDiffTwoForm.tangentEquiv.symm (stagePath he hρ s τ α B' p) := by
  let _ := ContMDiffSection.frameTopology (I := I) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) fr W hW
  let _ := ContMDiffSection.isTopologicalAddGroup_frameTopology (I := I)
    (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) fr W hW
  let _ := ContMDiffSection.continuousSMul_frameTopology (𝕜 := ℝ) (I := I)
    (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) fr W hW
  let F : C^∞⟮(𝓘(ℝ, S).prod (𝓡∂ 1)).prod I, (S × unitInterval) × M; I, M⟯ := ⟨e, he⟩
  have hT := Bundle.ContMDiffTwoForm.continuous_tangentEquiv_symm_mpullback_prod fr W hW fr W hW
    F hcover
  have hA := (collaredFirstHalf (n := ∞) le_rfl).contMDiff.continuous
  have hC : Continuous fun t ↦ (collaredSecondHalf (n := ∞) le_rfl t : ℝ) :=
    continuous_subtypeVal.comp (collaredSecondHalf (n := ∞) le_rfl).contMDiff.continuous
  -- The first term, `τ l` pulled back along the isotopy run at the speed `A`.
  have h₁ := hT.comp ((hτ.comp continuous_fst).prodMk
    ((hs.comp continuous_fst).prodMk (hA.comp continuous_snd)))
  -- The correction `α l - τ l + d (B' (s l))`, pulled back along the end of the isotopy.
  have h₂ := hT.comp (((hα.sub hτ).comp continuous_fst).prodMk
    ((hs.comp continuous_fst).prodMk
      (continuous_const (X := Λ × unitInterval) (y := (1 : unitInterval)))))
  have he₁ : ContMDiff (𝓘(ℝ, S).prod I) I ∞ fun q : S × M ↦ e ((q.1, 1), q.2) :=
    he.comp ((contMDiff_fst.prodMk contMDiff_const).prodMk contMDiff_snd)
  have h₃ := ((hB'.mextDeriv.mpullback_family he₁).continuous_tangentEquiv_symm fr W hW).comp
    (hs.comp (continuous_fst (X := Λ) (Y := unitInterval)))
  refine (h₁.add ((hC.comp continuous_snd).smul
    ((Bundle.ContMDiffTwoForm.continuous_tangentEquiv_symm_smul fr W hW ⟨ρ, hρ⟩).comp
      (h₂.add h₃)))).congr fun p ↦ ?_
  simp only [Pi.add_apply, Pi.smul_apply', Pi.sub_apply, Function.comp_apply, stagePath_def,
    map_add, map_sub, map_smul, LinearEquiv.apply_symm_apply, F, ContMDiffMap.coeFn_mk]
  abel_nf

end Continuous

section Stage

variable [FiniteDimensional ℝ E] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]
  {g : M → ℝ} {a₀ a b : ℝ} {L : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L]
  [FiniteDimensional ℝ L]

/-- **One stage of the relative h-principle, for smooth families.** Let `c` be a band core of a
continuous `g : M → ℝ` for the levels `a₀`, `a`, `b`, let `K ⊆ L` be compact and `P₀ ⊆ L`
closed. Let `τ` and `α` be smooth families over `L` of two-forms on `M`, with every `α l`
closed and `τ l` nondegenerate for `l ∈ K`, and `β` a smooth family of one-forms, such that
`τ l = α l + d (β l)` on an open `N ⊇ {g ≤ a}` for every `l`, and on all of `M` for `l ∈ P₀`.
Then there are smooth families `H` over `L × [0, 1]` of two-forms, `α'` of two-forms and `β'` of
one-forms, a neighbourhood `V` of `{g ≤ a}` and an open `N' ⊇ {g ≤ b}` such that

* `H (l, 0) = τ l`, and `H (l, t)` is nondegenerate for `l ∈ K`;
* on `V`, `H (l, t) = τ l`, `α' l = α l` and `β' l = β l`;
* every `α' l` is closed, and `α' l = α l + d γ` for a one-form `γ` vanishing on `V`;
* on `N'`, `H (l, 1) = α' l + d (β' l)`;
* for `l ∈ P₀`, `H (l, 1) = α' l + d (β' l)` on all of `M`, and every `H (l, t)` is closed with
  `H (l, t) - α l` exact. -/
theorem BandCore.exists_stage_family (c : BandCore I g a₀ a b) (hg : Continuous g)
    {K P₀ : Set L} (hK : IsCompact K) (hP₀ : IsClosed P₀)
    {τ α : L → SmoothTwoForm I M} (hτ : IsSmoothFamily 𝓘(ℝ, L) τ)
    (hα : IsSmoothFamily 𝓘(ℝ, L) α) (hαc : ∀ l, mextDerivₗ I 2 (α l) = 0)
    (hnd : ∀ l ∈ K, (τ l).IsNondegenerate)
    {β : L → SmoothForm I M ℝ 1} (hβ : IsSmoothFamily 𝓘(ℝ, L) β)
    {N : Set M} (hN : IsOpen N) (haN : {x | g x ≤ a} ⊆ N)
    (hτN : ∀ l, ∀ x ∈ N, (τ l).val x = (α l + mextDerivₗ I 1 (β l)).val x)
    (hτP₀ : ∀ l ∈ P₀, τ l = α l + mextDerivₗ I 1 (β l)) :
    ∃ (H : L × unitInterval → SmoothTwoForm I M) (α' : L → SmoothTwoForm I M)
      (β' : L → SmoothForm I M ℝ 1) (V N' : Set M),
      IsSmoothFamily (𝓘(ℝ, L).prod (𝓡∂ 1)) H ∧ IsSmoothFamily 𝓘(ℝ, L) α' ∧
      IsSmoothFamily 𝓘(ℝ, L) β' ∧ (∀ l, H (l, 0) = τ l) ∧
      (∀ l ∈ K, ∀ t, (H (l, t)).IsNondegenerate) ∧
      V ∈ 𝓝ˢ {x | g x ≤ a} ∧ (∀ l t, ∀ x ∈ V, (H (l, t)).val x = (τ l).val x ∧
        (α' l).val x = (α l).val x ∧ (β' l).val x = (β l).val x) ∧
      (∀ l, mextDerivₗ I 2 (α' l) = 0 ∧
        ∃ γ : SmoothForm I M ℝ 1, α' l = α l + mextDerivₗ I 1 γ ∧ ∀ x ∈ V, γ.val x = 0) ∧
      IsOpen N' ∧ {x | g x ≤ b} ⊆ N' ∧
      (∀ l, ∀ x ∈ N', (H (l, 1)).val x = (α' l + mextDerivₗ I 1 (β' l)).val x) ∧
      ∀ l ∈ P₀, H (l, 1) = α' l + mextDerivₗ I 1 (β' l) ∧
        ∀ t, mextDerivₗ I 2 (H (l, t)) = 0 ∧ H (l, t) - α l ∈ exactForms I M 2 := by
  obtain ⟨Φ, B', N₁, U, hΦ, -, hΦd, hΦ₀, hB', hN₁, haN₁, hN₁N, hΦN₁, hB'N₁, -, hB'P₀, hU,
      hKU, hUc, hUnd⟩ :=
    c.exists_approximation_family hg hK hP₀ hτ hα hnd hβ hN haN hτN hτP₀
  obtain ⟨e, he, ρ, hρ, V, N', -, he₀, hV, hVa, hVN₁, heV, hN', hbN', -, hρN', hHnd⟩ :=
    exists_stagePath c hg hK continuous_id hnd hΦ hΦd hΦ₀ hN₁ haN₁ hΦN₁ hU hKU hUc hUnd
  -- The end of the isotopy, as a smooth family of maps over `L`.
  have he₁ : ContMDiff (𝓘(ℝ, L).prod I) I ∞ fun q : L × M ↦ e ((q.1, 1), q.2) :=
    he.comp ((contMDiff_fst.prodMk contMDiff_const).prodMk contMDiff_snd)
  refine ⟨stagePath he hρ id τ α B',
    fun l ↦ SmoothForm.mpullback (fun x ↦ e ((l, 1), x))
      (he.comp (contMDiff_const.prodMk contMDiff_id)) (α l),
    fun l ↦ SmoothForm.mpullback (fun x ↦ e ((l, 1), x))
      (he.comp (contMDiff_const.prodMk contMDiff_id)) (B' l), V, N',
    isSmoothFamily_stagePath he hρ contMDiff_id hτ hα hB', hα.mpullback_family he₁,
    hB'.mpullback_family he₁, fun l ↦ stagePath_zero he hρ id τ α B' (he₀ l),
    hHnd, hVa, fun l t x hx ↦ ?_, fun l ↦ ⟨?_, ?_⟩, hN', hbN',
    stagePath_one_eqOn he hρ id τ α B' hρN', fun l hl ↦ ?_⟩
  · -- Nothing changes on `V`, where the isotopy is the identity, `B' = β` and `τ = α + d β`.
    obtain ⟨h₁, h₂, h₃⟩ := stagePath_eqOn_nhdsSet he hρ id τ α B' hV (fun t ↦ heV (l, t))
      (B := β) (fun x hx ↦ hB'N₁ l x (hVN₁ hx)) fun x hx ↦ hτN l x (hN₁N (hVN₁ hx))
    exact ⟨h₁ t x hx, h₂ x hx, h₃ x hx⟩
  · rw [SmoothForm.mextDerivₗ_mpullback, hαc, map_zero]
  · obtain ⟨γ, hγ, hγV⟩ := exists_mextDerivₗ_eq_endPullback_sub he id α (he₀ l) (hαc l)
      (V := V) fun t ↦ heV (l, t)
    exact ⟨γ, eq_add_of_sub_eq' hγ.symm, hγV⟩
  · -- For `l ∈ P₀` the correction vanishes, since `B' l = β l` there.
    have hτl : τ l = α l + mextDerivₗ I 1 (B' (id l)) := by rw [id, hB'P₀ l hl, hτP₀ l hl]
    obtain ⟨h₁, h₂⟩ := stagePath_of_mem he hρ id τ α B' (he₀ l) (hαc l) hτl
    exact ⟨h₂, h₁⟩

end Stage

section ContinuousStage

open _root_.Bundle

variable [FiniteDimensional ℝ E] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]
  [FiniteDimensional ℝ S] {g : M → ℝ} {a₀ a b : ℝ}
  {P : Type*} [TopologicalSpace P] [CompactSpace P] [T2Space P] {ι : Type*}
  (fr : ι → Trivialization (E [⋀^Fin 2]→L[ℝ] ℝ)
    (π (E [⋀^Fin 2]→L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x [⋀^Fin 2]→L[ℝ] Trivial M ℝ x)))
  [∀ j, MemTrivializationAtlas (fr j)]
  (W : ι → TopologicalSpace.Opens M) (hW : ∀ j, (W j : Set M) ⊆ (fr j).baseSet)

/-- **One stage of the relative h-principle, for continuous families.** Let `c` be a band core of
a continuous `g : M → ℝ` for the levels `a₀`, `a`, `b`, let `P` be a compact Hausdorff space and
`P₀ ⊆ P` closed. Let `τ` and `α` be families over `P` of two-forms on `M`, continuous into the
frame topology of a covering frame system, with every `α l` closed and every `τ l`
nondegenerate, and let the one-forms be `B (s l)`, for a smooth family `B` over a
finite-dimensional normed space `S` and a continuous `s : P → S`, such that
`τ l = α l + d (B (s l))` on an open `N ⊇ {g ≤ a}` for every `l`, and on all of `M` for `l ∈ P₀`.
Then there are a family `H` over `P × [0, 1]` of two-forms and a family `α'` over `P` of
two-forms, both continuous into the frame topology, continuous maps `σ i : P → Fin (n i) → ℝ`,
one for each cube `i`, a smooth family `B''` of one-forms over
`S × ((i : c.ι) → Fin (n i) → ℝ)`, a neighbourhood `V` of `{g ≤ a}` and an open `N' ⊇ {g ≤ b}`
such that, with the new one-forms `β' l := B'' (s l, fun i ↦ σ i l)`,

* `H (l, 0) = τ l`, and every `H (l, t)` is nondegenerate;
* on `V`, `H (l, t) = τ l`, `α' l = α l` and `β' l = B (s l)`;
* every `α' l` is closed, and `α' l = α l + d γ` for a one-form `γ` vanishing on `V`;
* on `N'`, `H (l, 1) = α' l + d (β' l)`;
* for `l ∈ P₀`, `H (l, 1) = α' l + d (β' l)` on all of `M`, and every `H (l, t)` is closed with
  `H (l, t) - α l` exact. -/
theorem BandCore.exists_stage_continuous_family (c : BandCore I g a₀ a b) (hg : Continuous g)
    (hcover : ∀ x, ∃ j, x ∈ W j) {P₀ : Set P} (hP₀ : IsClosed P₀)
    {τ α : P → SmoothTwoForm I M}
    (hτ : let _ := ContMDiffSection.frameTopology (I := I) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) fr W hW
      Continuous fun l ↦ Bundle.ContMDiffTwoForm.tangentEquiv.symm (τ l))
    (hα : let _ := ContMDiffSection.frameTopology (I := I) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) fr W hW
      Continuous fun l ↦ Bundle.ContMDiffTwoForm.tangentEquiv.symm (α l))
    (hαc : ∀ l, mextDerivₗ I 2 (α l) = 0) (hnd : ∀ l, (τ l).IsNondegenerate)
    {B : S → SmoothForm I M ℝ 1} (hB : IsSmoothFamily 𝓘(ℝ, S) B) {s : P → S}
    (hs : Continuous s) {N : Set M} (hN : IsOpen N) (haN : {x | g x ≤ a} ⊆ N)
    (hτN : ∀ l, ∀ x ∈ N, (τ l).val x = (α l + mextDerivₗ I 1 (B (s l))).val x)
    (hτP₀ : ∀ l ∈ P₀, τ l = α l + mextDerivₗ I 1 (B (s l))) :
    ∃ (H : P × unitInterval → SmoothTwoForm I M) (α' : P → SmoothTwoForm I M)
      (n : c.ι → ℕ) (σ : ∀ i, P → Fin (n i) → ℝ)
      (B'' : S × ((i : c.ι) → Fin (n i) → ℝ) → SmoothForm I M ℝ 1) (V N' : Set M),
      (let _ := ContMDiffSection.frameTopology (I := I) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) fr W hW;
        Continuous fun p ↦ Bundle.ContMDiffTwoForm.tangentEquiv.symm (H p)) ∧
      (let _ := ContMDiffSection.frameTopology (I := I) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) fr W hW;
        Continuous fun l ↦ Bundle.ContMDiffTwoForm.tangentEquiv.symm (α' l)) ∧
      (∀ i, Continuous (σ i)) ∧ IsSmoothFamily 𝓘(ℝ, S × ((i : c.ι) → Fin (n i) → ℝ)) B'' ∧
      (∀ l, H (l, 0) = τ l) ∧ (∀ l t, (H (l, t)).IsNondegenerate) ∧
      V ∈ 𝓝ˢ {x | g x ≤ a} ∧ (∀ l t, ∀ x ∈ V, (H (l, t)).val x = (τ l).val x ∧
        (α' l).val x = (α l).val x ∧ (B'' (s l, fun i ↦ σ i l)).val x = (B (s l)).val x) ∧
      (∀ l, mextDerivₗ I 2 (α' l) = 0 ∧
        ∃ γ : SmoothForm I M ℝ 1, α' l = α l + mextDerivₗ I 1 γ ∧ ∀ x ∈ V, γ.val x = 0) ∧
      IsOpen N' ∧ {x | g x ≤ b} ⊆ N' ∧
      (∀ l, ∀ x ∈ N', (H (l, 1)).val x =
        (α' l + mextDerivₗ I 1 (B'' (s l, fun i ↦ σ i l))).val x) ∧
      ∀ l ∈ P₀, H (l, 1) = α' l + mextDerivₗ I 1 (B'' (s l, fun i ↦ σ i l)) ∧
        ∀ t, mextDerivₗ I 2 (H (l, t)) = 0 ∧ H (l, t) - α l ∈ exactForms I M 2 := by
  obtain ⟨n, σ, Φ, B', N₁, U, hσ, hΦ, -, hΦd, hΦ₀, hB', hN₁, haN₁, hN₁N, hΦN₁, hB'N₁, -, hB'P₀,
      hU, hKU, hUc, hUnd⟩ :=
    c.exists_approximation_continuous_family fr W hW hg hcover hP₀ hτ hα hnd hB hs hN haN hτN
      hτP₀
  -- The parameter of the approximation, `s' l = (s l, fun i ↦ σ i l)`.
  set s' : P → S × ((i : c.ι) → Fin (n i) → ℝ) := fun l ↦ (s l, fun i ↦ σ i l) with hs'_def
  have hs' : Continuous s' := hs.prodMk (continuous_pi hσ)
  obtain ⟨φ, hφ, ρ, hρ, V, N', -, hφ₀, hV, hVa, hVN₁, hφV, hN', hbN', -, hρN', hHnd⟩ :=
    exists_stagePath c hg isCompact_univ hs' (fun l _ ↦ hnd l) hΦ hΦd hΦ₀ hN₁ haN₁ hΦN₁ hU
      hKU (fun l _ ↦ hUc l) fun p hp _ ↦ hUnd p hp
  -- The end of the isotopy, as a smooth family of maps over the parameters of the approximation.
  have hφ₁ : ContMDiff (𝓘(ℝ, S × ((i : c.ι) → Fin (n i) → ℝ)).prod I) I ∞
      fun q : (S × ((i : c.ι) → Fin (n i) → ℝ)) × M ↦ φ ((q.1, 1), q.2) :=
    hφ.comp ((contMDiff_fst.prodMk contMDiff_const).prodMk contMDiff_snd)
  refine ⟨stagePath hφ hρ s' τ α B',
    fun l ↦ SmoothForm.mpullback (fun x ↦ φ ((s' l, 1), x))
      (hφ.comp (contMDiff_const.prodMk contMDiff_id)) (α l), n, σ,
    fun q ↦ SmoothForm.mpullback (fun x ↦ φ ((q, 1), x))
      (hφ.comp (contMDiff_const.prodMk contMDiff_id)) (B' q), V, N',
    continuous_tangentEquiv_symm_stagePath fr W hW hcover hφ hρ hs' hτ hα hB', ?_, hσ,
    hB'.mpullback_family hφ₁, fun l ↦ stagePath_zero hφ hρ s' τ α B' (hφ₀ (s' l)),
    fun l t ↦ hHnd l (mem_univ l) t, hVa, fun l t x hx ↦ ?_, fun l ↦ ⟨?_, ?_⟩, hN', hbN',
    stagePath_one_eqOn hφ hρ s' τ α B' hρN', fun l hl ↦ ?_⟩
  · -- `α' l` is `α l` pulled back along the end of the isotopy at the parameter `s' l`.
    let _ := ContMDiffSection.frameTopology (I := I) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) fr W hW
    have hT := Bundle.ContMDiffTwoForm.continuous_tangentEquiv_symm_mpullback_prod fr W hW fr W
      hW ⟨φ, hφ⟩ hcover
    refine (hT.comp (hα.prodMk (hs'.prodMk (continuous_const (y := (1 : unitInterval)))))).congr
      fun l ↦ ?_
    simp only [Function.comp_apply, LinearEquiv.apply_symm_apply, ContMDiffMap.coeFn_mk]
  · -- Nothing changes on `V`, where the isotopy is the identity, `B' = B` and `τ = α + d B`.
    obtain ⟨h₁, h₂, h₃⟩ := stagePath_eqOn_nhdsSet hφ hρ s' τ α B' hV (fun t ↦ hφV (s' l, t))
      (B := fun q ↦ B q.1) (fun x hx ↦ hB'N₁ (s' l) x (hVN₁ hx))
      fun x hx ↦ hτN l x (hN₁N (hVN₁ hx))
    exact ⟨h₁ t x hx, h₂ x hx, h₃ x hx⟩
  · rw [SmoothForm.mextDerivₗ_mpullback, hαc, map_zero]
  · obtain ⟨γ, hγ, hγV⟩ := exists_mextDerivₗ_eq_endPullback_sub hφ s' α (hφ₀ (s' l)) (hαc l)
      (V := V) fun t ↦ hφV (s' l, t)
    exact ⟨γ, eq_add_of_sub_eq' hγ.symm, hγV⟩
  · -- For `l ∈ P₀` the correction vanishes, since `B' (s' l) = B (s l)` there.
    have hτl : τ l = α l + mextDerivₗ I 1 (B' (s' l)) := by rw [hB'P₀ l hl, hτP₀ l hl]
    obtain ⟨h₁, h₂⟩ := stagePath_of_mem hφ hρ s' τ α B' (hφ₀ (s' l)) (hαc l) hτl
    exact ⟨h₂, h₁⟩

end ContinuousStage

end SymplecticGeometry

end
