/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DeRham.MayerVietoris
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.Basic
public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Cut-off extensions of smooth families

For a cut-off function `ρ` of a cover of `U ⊔ V` by two open sets
(`SymplecticGeometry.MayerVietorisCutoff`), multiplying a form on `U ⊓ V` by `ρ`, or by `1 - ρ`,
and extending it by zero to `U`, or to `V`, takes smooth families of forms to smooth families
(`MayerVietorisCutoff.isSmoothFamily_extendLeft`,
`MayerVietorisCutoff.isSmoothFamily_extendRight`).

On a finite-dimensional Hausdorff σ-compact manifold `M`, a smooth family of forms on an open
subset `U` agrees, near a closed set `K ⊆ U` and for all parameters at once, with the restriction
of a smooth family of forms on `M` that vanishes near the complement of `U`
(`SymplecticGeometry.IsSmoothFamily.exists_isSmoothFamily_eventuallyEq_nhdsSet`). The family on
`M` is the given one multiplied by a bump function that does not depend on the parameter and
extended by zero; this adapts the proof of Tau Ceti's
`TauCeti.RoughForm.exists_isSmoothForm_eventuallyEq_nhdsSet` to smooth families.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 2 (smooth bump
  functions).
-/

public section

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology

namespace SymplecticGeometry.MayerVietorisCutoff

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}
  {U V : Opens M} (c : MayerVietorisCutoff I U V)
  {EN HN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  [TopologicalSpace N] [ChartedSpace HN N] {J : ModelWithCorners ℝ EN HN} [IsManifold J 1 N]

/-- `extendLeft` takes smooth families to smooth families. -/
theorem isSmoothFamily_extendLeft {α : N → TauCeti.SmoothForm I (U ⊓ V : Opens M) F k}
    (hα : IsSmoothFamily J α) : IsSmoothFamily J (fun t ↦ c.extendLeft (α t)) :=
  hα.extendByZero_smul inf_le_left (c.contMDiff.comp (contMDiff_inclusion le_sup_left))
    (fun _ hx ↦ c.eventually_eq_zero hx) fun _ ↦ c.coe_extendLeft _

/-- `extendRight` takes smooth families to smooth families. -/
theorem isSmoothFamily_extendRight {α : N → TauCeti.SmoothForm I (U ⊓ V : Opens M) F k}
    (hα : IsSmoothFamily J α) : IsSmoothFamily J (fun t ↦ c.extendRight (α t)) :=
  hα.extendByZero_smul inf_le_right
    (contMDiff_const.sub (c.contMDiff.comp (contMDiff_inclusion le_sup_right)))
    (fun _ hx ↦ c.eventually_one_sub_eq_zero hx) fun _ ↦ c.coe_extendRight _

end SymplecticGeometry.MayerVietorisCutoff

namespace SymplecticGeometry.IsSmoothFamily

open TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}
  {EN HN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  [TopologicalSpace N] [ChartedSpace HN N] {J : ModelWithCorners ℝ EN HN} [IsManifold J 1 N]

/-- **Cutting off a smooth family of forms.** Let `M` be a Hausdorff σ-compact manifold modelled
on a finite-dimensional space, `U` an open subset, `K ⊆ U` closed and `α` a smooth family of forms
on `U` over `N`. There is a smooth family `β` of forms on `M` whose restriction to `U` agrees with
`α` near `K`, and which vanishes near the complement of `U`, both for all parameters at once. -/
theorem exists_isSmoothFamily_eventuallyEq_nhdsSet {U : Opens M} {K : Set M} (hK : IsClosed K)
    (hKU : K ⊆ U) {α : N → SmoothForm I U F k} (hα : IsSmoothFamily J α) :
    ∃ β : N → SmoothForm I M F k, IsSmoothFamily J β ∧
      (∀ᶠ x in 𝓝ˢ (Subtype.val ⁻¹' K : Set U), ∀ t,
        (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (β t)).val x = (α t).val x) ∧
      ∀ᶠ x in 𝓝ˢ (U : Set M)ᶜ, ∀ t, (β t).val x = 0 := by
  -- `M` is normal.
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  -- A bump function, `0` near the complement of `U` and `1` near `K`.
  obtain ⟨f, hf₀, hf₁, -⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed I (n := (⊤ : ℕ∞))
    U.isOpen.isClosed_compl hK (disjoint_compl_left_iff_subset.mpr hKU)
  let ρ : (⊤ : Opens M) → ℝ := fun y ↦ f y
  have hρ : ContMDiff I 𝓘(ℝ) ∞ ρ := f.contMDiff.comp contMDiff_subtypeVal
  have hρ₀ : ∀ x : (⊤ : Opens M), (x : M) ∉ U → ∀ᶠ y in 𝓝 x, ρ y = 0 := fun x hx ↦
    continuous_subtypeVal.continuousAt.eventually (hf₀.filter_mono (nhds_le_nhdsSet hx))
  -- The cut-off family, on `⊤` and then on `M`.
  let βtop : N → SmoothForm I (⊤ : Opens M) F k := fun t ↦
    ⟨RoughForm.extendByZero ⊤ fun y : U ↦ ρ (Opens.inclusion le_top y) • (α t).val y,
      ((α t).isSmoothForm.extendByZero_smul le_top hρ hρ₀).mem_smoothBundleForms⟩
  have hβtop : IsSmoothFamily J βtop := hα.extendByZero_smul le_top hρ hρ₀ fun _ ↦ rfl
  let g : M → (⊤ : Opens M) := fun x ↦ ⟨x, trivial⟩
  have hg : ContMDiff I I ∞ g := (ContMDiff.subtypeVal_comp_iff ⊤ _).mp contMDiff_id
  refine ⟨fun t ↦ SmoothForm.mpullback g hg (βtop t), hβtop.mpullback g hg, ?_, ?_⟩
  · -- Near `K` the bump function is `1`.
    filter_upwards [continuous_subtypeVal.tendsto_nhdsSet (mapsTo_preimage _ _) hf₁] with x hx t
    rw [SmoothForm.mpullback_mpullback,
      SmoothForm.mpullback_congr _ (contMDiff_inclusion le_top)
        (rfl : g ∘ Subtype.val = Opens.inclusion le_top), SmoothForm.coe_mpullback,
      mpullback_inclusion_apply]
    simp only [βtop, RoughForm.extendByZero_inclusion]
    rw [mem_preimage, mem_ofPred_eq] at hx
    simp [ρ, hx]
  · -- Near the complement of `U` the bump function is `0`.
    filter_upwards [hf₀.eventually_nhdsSet] with x hx t
    have h0 : (βtop t).val (g x) = 0 :=
      (RoughForm.eventually_extendByZero_smul_eq_zero le_top (α t).val
        ((continuous_subtypeVal.continuousAt (x := g x)).eventually hx)).self_of_nhds
    rw [SmoothForm.coe_mpullback, mpullback_apply_congr (η := 0) h0]
    simp

end SymplecticGeometry.IsSmoothFamily

end
