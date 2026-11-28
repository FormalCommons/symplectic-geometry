/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.Basic
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Opens

/-!
# Cutting off a smooth family of forms on an open subset

On a finite-dimensional Hausdorff σ-compact manifold `M`, a smooth family of forms on an open
subset `U` agrees, near a closed set `K ⊆ U` and for all parameters at once, with the restriction
of a smooth family of forms on `M` that vanishes near the complement of `U`
(`SymplecticGeometry.IsSmoothFamily.exists_isSmoothFamily_eventuallyEq_nhdsSet`). The family on
`M` is the given one multiplied by a bump function that does not depend on the parameter and
extended by zero. The statement is the family version of Tau Ceti's
`TauCeti.RoughForm.exists_isSmoothForm_eventuallyEq_nhdsSet`. The construction, which multiplies
the family on `U` by a bump function vanishing near the points outside `U` and equal to one near
`K` and then extends it by zero, adapts the proof of Tau Ceti's
`TauCeti.exists_eventuallyEq_mextDerivₗ` to smooth families.

The family on `M` is built with `TauCeti.RoughForm.extendByZeroOfOpens`. Multiplying a smooth
family on `U` by a smooth function on `M` with support in `U`, after extending it by zero to `M`,
gives a smooth family on `M` (`SymplecticGeometry.IsSmoothFamily.fun_smul_extendByZeroOfOpens`).
Its proof restricts the family to `⊤ : Opens M`, where it is Tau Ceti's extension by zero
(`TauCeti.RoughForm.mpullback_subtypeVal_extendByZeroOfOpens_eq_extendByZero`), and applies
`SymplecticGeometry.IsSmoothFamily.extendByZero_smul` there.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 2 (smooth bump
  functions).
-/

public section

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology

namespace SymplecticGeometry.IsSmoothFamily

open TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}
  {EN HN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  [TopologicalSpace N] [ChartedSpace HN N] {J : ModelWithCorners ℝ EN HN} [IsManifold J 1 N]

/-- **Cut-off and extension by zero of a smooth family to `M`.** Let `α` be a smooth family of
forms on an open subset `U` of `M`, and `f` a smooth function on `M` whose topological support
lies in `U`. A family `β` of smooth forms on `M` whose value at `t` is the product of `f` with the
extension by zero of `α t` is smooth. -/
theorem fun_smul_extendByZeroOfOpens {U : Opens M} {α : N → SmoothForm I U F k}
    (hα : IsSmoothFamily J α) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hfU : tsupport f ⊆ U)
    {β : N → SmoothForm I M F k}
    (hβ : ∀ t, (β t).val = fun x ↦ f x • RoughForm.extendByZeroOfOpens (α t).val x) :
    IsSmoothFamily J β := by
  -- Pull back to `⊤ : Opens M`, where Tau Ceti's extension by zero applies.
  have hs : ContMDiff I I ∞ (fun x : M ↦ (⟨x, trivial⟩ : (⊤ : Opens M))) :=
    (ContMDiff.subtypeVal_comp_iff ⊤ _).mp contMDiff_id
  refine of_mpullback contMDiff_subtypeVal
    (fun x ↦ ⟨univ, isOpen_univ, mem_univ x, _, hs.contMDiffOn, fun _ _ ↦ rfl⟩) ?_
  have hzero : ∀ x : (⊤ : Opens M), (x : M) ∉ U → ∀ᶠ y in 𝓝 x, (f ∘ Subtype.val) y = 0 :=
    fun x hx ↦ continuous_subtypeVal.continuousAt.eventually
      (notMem_tsupport_iff_eventuallyEq.mp fun h ↦ hx (hfU h))
  refine hα.extendByZero_smul le_top (hf.comp contMDiff_subtypeVal) hzero fun t ↦ ?_
  rw [SmoothForm.coe_mpullback, hβ, ← RoughForm.extendByZeroOfOpens_fun_smul,
    RoughForm.mpullback_subtypeVal_extendByZeroOfOpens_eq_extendByZero]
  simp only [Function.comp_apply]

variable [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]

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
  have hfU : tsupport f ⊆ U := fun x hx ↦ by_contra fun hxU ↦
    (notMem_tsupport_iff_eventuallyEq.mpr (hf₀.filter_mono (nhds_le_nhdsSet hxU))) hx
  -- The cut-off family on `M`.
  let β : N → SmoothForm I M F k := fun t ↦
    ⟨fun x ↦ f x • RoughForm.extendByZeroOfOpens (α t).val x,
      ((α t).isSmoothForm.fun_smul_extendByZeroOfOpens f.contMDiff hfU).mem_smoothBundleForms⟩
  refine ⟨β, hα.fun_smul_extendByZeroOfOpens f.contMDiff hfU fun _ ↦ rfl, ?_, ?_⟩
  · -- Near `K` the bump function is `1`.
    filter_upwards [continuous_subtypeVal.tendsto_nhdsSet (mapsTo_preimage _ _) hf₁] with x hx t
    rw [mem_preimage, mem_ofPred_eq] at hx
    simp only [β, SmoothForm.coe_mpullback, mpullback_subtype_val_apply,
      RoughForm.extendByZeroOfOpens_coe, hx]
    -- The fibres of `U` at `x` and of `M` at `x` are the same model fibre.
    exact one_smul ℝ _
  · -- Near the complement of `U` the bump function is `0`.
    filter_upwards [hf₀] with x hx t
    simp [β, hx]

end SymplecticGeometry.IsSmoothFamily

end
