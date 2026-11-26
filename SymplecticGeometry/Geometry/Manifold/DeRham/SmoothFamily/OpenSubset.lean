/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DeRham.SmoothFamily.GoodCover
public import TauCeti.Geometry.Manifold.DeRham.ExtendByZero
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.Cutoff

/-!
# Smooth families of primitives near a compact subset of an open set

Let `U` be an open subset of a manifold `M` with a finite good cover, `A ⊆ U` compact, and `τ` a
smooth family of `(k + 1)`-forms on `M` over a parameter manifold `N` whose restrictions to `U`
are exact for the parameters in a set `K`. Then there are a smooth family `β` of `k`-forms on `M`
and an open set `W ⊇ A` with `dβ t = τ t` on `W` for `t ∈ K`
(`SymplecticGeometry.exists_isSmoothFamily_mextDerivₗ_eq_on_of_hasFiniteGoodCover`).

The proof takes a smooth cohomology splitting of `U`
(`HasFiniteGoodCover.isSmooth_smoothCohomologySplitting`), which gives a smooth family
of primitives on `U` over `K`
(`SmoothCohomologySplitting.IsSmooth.exists_isSmoothFamily_mextDerivₗ_eq_of_mem_exactForms`).
These are cut off to a smooth family of forms on `M` that agrees with them near `A`
(`SymplecticGeometry.IsSmoothFamily.exists_isSmoothFamily_eventuallyEq_nhdsSet`), so that near
`A` its exterior derivatives are those of the primitives
(`SymplecticGeometry.exists_isSmoothFamily_mextDerivₗ_eq_on_of_mpullback`). That theorem is the
family version of the first conclusion of Tau Ceti's `TauCeti.exists_eventuallyEq_mextDerivₗ`,
and, as in its proof, the last step is the locality of the exterior derivative.

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
  -- Cut `β₀` off to a smooth family on `M` that agrees with it near `A`.
  obtain ⟨β, hβ, hββ₀, -⟩ := hβ₀.exists_isSmoothFamily_eventuallyEq_nhdsSet hA.isClosed hAU
  obtain ⟨W, hW, hAW, hWβ⟩ := mem_nhdsSet_iff_exists.mp hββ₀
  refine ⟨β, hβ, (↑) '' W, U.isOpen.isOpenMap_subtypeVal W hW,
    fun x hx ↦ ⟨⟨x, hAU hx⟩, hAW hx, rfl⟩, ?_⟩
  rintro t ht _ ⟨x, hx, rfl⟩
  -- Near `x` the restriction of `β t` to `U` is `β₀ t`, whose exterior derivative is `τ t`.
  have hloc : mextDeriv (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (β t)).val x =
      mextDeriv (β₀ t).val x :=
    mextDeriv_congr_of_eventuallyEq (Filter.mem_of_superset (hW.mem_nhds hx) fun y hy ↦ hWβ hy t)
  rw [← SmoothForm.coe_mpullback_subtype_val_apply, ← SmoothForm.mextDerivₗ_mpullback,
    mextDerivₗ_apply, hloc, ← mextDerivₗ_apply, hdβ₀ t ht,
    SmoothForm.coe_mpullback_subtype_val_apply]

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
  obtain ⟨β₀, hβ₀, hdβ₀⟩ :=
    hU.isSmooth_smoothCohomologySplitting.exists_isSmoothFamily_mextDerivₗ_eq_of_mem_exactForms
      (hτ.mpullback _ _) hK
  exact exists_isSmoothFamily_mextDerivₗ_eq_on_of_mpullback hA hAU hβ₀ hdβ₀

end SymplecticGeometry

end
