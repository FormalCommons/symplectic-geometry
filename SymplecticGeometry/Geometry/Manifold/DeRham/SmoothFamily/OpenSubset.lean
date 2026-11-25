/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import SymplecticGeometry.Geometry.Manifold.DeRham.SmoothFamily.GoodCover
public import TauCeti.Geometry.Manifold.DeRham.ExtendByZero

/-!
# Smooth families of primitives near a compact subset of an open set

Let `U` be an open subset of a manifold `M` with a finite good cover, `A ⊆ U` compact, and `τ` a
smooth family of `(k + 1)`-forms on `M` over a parameter manifold `N` whose restrictions to `U`
are exact for the parameters in a set `K`. Then there are a smooth family `β` of `k`-forms on `M`
and an open set `W ⊇ A` with `dβ t = τ t` on `W` for `t ∈ K`
(`SymplecticGeometry.exists_isSmoothFamily_mextDerivₗ_eq_on_of_hasFiniteGoodCover`).

The proof takes a smooth cohomology splitting of `U`
(`HasFiniteGoodCover.nonempty_smoothCohomologySplitting`), which gives a smooth family of
primitives on `U` over `K`
(`SmoothCohomologySplitting.exists_isSmoothFamily_mextDerivₗ_eq_of_mem_exactForms`). A smooth
function that vanishes near the complement of `U` and is `1` near `A` cuts these off to forms on
`M` (`SymplecticGeometry.exists_isSmoothFamily_mextDerivₗ_eq_on_of_mpullback`), whose exterior
derivatives near `A` are given by Tau Ceti's
`TauCeti.mextDeriv_extendByZero_smul_apply_of_eventuallyEq_one`.

## Main results

* `SymplecticGeometry.exists_isSmoothFamily_mextDerivₗ_eq_on_of_mpullback`
* `SymplecticGeometry.exists_isSmoothFamily_mextDerivₗ_eq_on_of_hasFiniteGoodCover`

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], proof of
  Lemma 7.3.2.
-/

public section

noncomputable section

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology

namespace SymplecticGeometry

open TauCeti

universe uE uH uN

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  {EN : Type uE} [NormedAddCommGroup EN] [NormedSpace ℝ EN] {HN : Type uH} [TopologicalSpace HN]
  {N : Type uN} [TopologicalSpace N] [ChartedSpace HN N] {J : ModelWithCorners ℝ EN HN}
  [IsManifold J ∞ N]

/-- **Cutting off a smooth family of primitives on an open set.** Let `M` be a Hausdorff
σ-compact manifold modelled on a finite-dimensional space, `U` an open subset, `A ⊆ U` compact,
`τ` a family of `(k + 1)`-forms on `M` and `β₀` a smooth family of `k`-forms on `U` with
`d (β₀ t) = τ t` on `U` for every `t` in a set `K`. Then there are a smooth family `β` of `k`-forms
on `M` and an open set `W ⊇ A` such that `d (β t) = τ t` on `W` for every `t ∈ K`. -/
theorem exists_isSmoothFamily_mextDerivₗ_eq_on_of_mpullback {U : Opens M} {A : Set M}
    (hA : IsCompact A) (hAU : A ⊆ U) {k : ℕ} {τ : N → SmoothForm I M ℝ (k + 1)}
    {β₀ : N → SmoothForm I U ℝ k} (hβ₀ : IsSmoothFamily J β₀) {K : Set N}
    (hdβ₀ : ∀ t ∈ K, mextDerivₗ I k (β₀ t) =
      SmoothForm.mpullback (Subtype.val : U → M) contMDiff_subtypeVal (τ t)) :
    ∃ β : N → SmoothForm I M ℝ k, IsSmoothFamily J β ∧
      ∃ W : Set M, IsOpen W ∧ A ⊆ W ∧
        ∀ t ∈ K, ∀ x ∈ W, (mextDerivₗ I k (β t)).val x = (τ t).val x := by
  -- `M` is normal.
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  -- A cut-off function, `0` near the complement of `U` and `1` on an open `W ⊇ A`.
  obtain ⟨f, hf₀, hf₁, -⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed I
    (n := (⊤ : ℕ∞))
    (U.isOpen.isClosed_compl) hA.isClosed (disjoint_compl_left_iff_subset.mpr hAU)
  obtain ⟨W, hW, hAW, hWf⟩ := mem_nhdsSet_iff_exists.mp hf₁
  let ρ : (⊤ : Opens M) → ℝ := fun y ↦ f y
  have hρ : ContMDiff I 𝓘(ℝ) ∞ ρ := f.contMDiff.comp contMDiff_subtypeVal
  have hρ₀ : ∀ x : (⊤ : Opens M), (x : M) ∉ U → ∀ᶠ y in 𝓝 x, ρ y = 0 := fun x hx ↦
    continuous_subtypeVal.continuousAt.eventually (hf₀.filter_mono (nhds_le_nhdsSet hx))
  -- The cut-off primitives, on `⊤` and then on `M`.
  let βtop : N → SmoothForm I (⊤ : Opens M) ℝ k := fun t ↦
    ⟨RoughForm.extendByZero ⊤ fun y : U ↦ ρ (Opens.inclusion le_top y) • (β₀ t).val y,
      ((β₀ t).isSmoothForm.extendByZero_smul le_top hρ hρ₀).mem_smoothBundleForms⟩
  have hβtop : IsSmoothFamily J βtop := hβ₀.extendByZero_smul le_top hρ hρ₀ fun _ ↦ rfl
  let g : M → (⊤ : Opens M) := fun x ↦ ⟨x, trivial⟩
  have hg : ContMDiff I I ∞ g :=
    (ContMDiff.subtypeVal_comp_iff ⊤ _).mp contMDiff_id
  refine ⟨fun t ↦ SmoothForm.mpullback g hg (βtop t), hβtop.mpullback g hg, W, hW, hAW,
    fun t ht x hx ↦ ?_⟩
  -- Near `g x` the cut-off is `1`, so `d (βtop t) = τ t` at `g x`.
  have hρx : ρ =ᶠ[𝓝 (g x)] 1 :=
    (continuous_subtypeVal.continuousAt.eventually (hW.mem_nhds hx)).mono fun y hy ↦ hWf hy
  have key := mextDeriv_extendByZero_smul_apply_of_eventuallyEq_one le_top hρ₀
    (η := SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (τ t)) (θ := β₀ t)
    (by rw [hdβ₀ t ht, SmoothForm.mpullback_mpullback]; exact SmoothForm.mpullback_congr _ _ rfl _)
    hρx
  rw [SmoothForm.mextDerivₗ_mpullback, SmoothForm.coe_mpullback, mextDerivₗ_apply]
  calc mpullback I I g (mextDeriv (βtop t).val) x
      = mpullback I I g
          (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (τ t)).val x :=
        mpullback_apply_congr key
    _ = (τ t).val x := by
        rw [← SmoothForm.coe_mpullback g hg, SmoothForm.mpullback_mpullback,
          SmoothForm.mpullback_congr _ contMDiff_id (rfl : Subtype.val ∘ g = id),
          SmoothForm.mpullback_id, LinearMap.id_apply]

/-- **Smooth families of primitives near a compact set.** Let `M` be a Hausdorff σ-compact
manifold modelled on a finite-dimensional space, `U` an open subset of `M` with a finite good
cover, `A ⊆ U` compact, and `τ` a smooth family of `(k + 1)`-forms on `M` over a manifold `N`,
whose restriction to `U` is exact for every parameter in a set `K`. Then there are a smooth family
`β` of `k`-forms on `M` and an open set `W ⊇ A` such that `d (β t) = τ t` on `W` for every
`t ∈ K`. -/
theorem exists_isSmoothFamily_mextDerivₗ_eq_on_of_hasFiniteGoodCover {U : Opens M}
    (hU : HasFiniteGoodCover I U) {A : Set M} (hA : IsCompact A) (hAU : A ⊆ U) {k : ℕ}
    {τ : N → SmoothForm I M ℝ (k + 1)} (hτ : IsSmoothFamily J τ) {K : Set N}
    (hK : ∀ t ∈ K, SmoothForm.mpullback (Subtype.val : U → M) contMDiff_subtypeVal (τ t) ∈
      exactForms I U (k + 1)) :
    ∃ β : N → SmoothForm I M ℝ k, IsSmoothFamily J β ∧
      ∃ W : Set M, IsOpen W ∧ A ⊆ W ∧
        ∀ t ∈ K, ∀ x ∈ W, (mextDerivₗ I k (β t)).val x = (τ t).val x := by
  -- `U` is σ-compact, as an open subset of the metrizable σ-compact manifold `M`.
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  have := Manifold.metrizableSpace I M
  let := TopologicalSpace.metrizableSpaceMetric M
  obtain ⟨σ⟩ : Nonempty (SmoothCohomologySplitting.{uE, uH, uN} I U) :=
    hU.nonempty_smoothCohomologySplitting
  obtain ⟨β₀, hβ₀, hdβ₀⟩ :=
    σ.exists_isSmoothFamily_mextDerivₗ_eq_of_mem_exactForms (hτ.mpullback _ _) hK
  exact exists_isSmoothFamily_mextDerivₗ_eq_on_of_mpullback hA hAU hβ₀ hdβ₀

end SymplecticGeometry

end
