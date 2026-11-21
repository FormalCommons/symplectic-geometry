/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.Family
import Mathlib.Topology.Compactness.Compact
import TauCeti.Topology.VectorBundle.Hom

/-!
# Openness of nondegeneracy for families of two-forms

For a smooth family of two-forms on `M`, given as a smooth two-form `σ` on `N × M` with slices
`σ_t = ι_t^* σ`, the points `(t, x)` at which `σ_t` has an invertible flat map
`T_x M → T_x^* M` form an open subset of `N × M`. When the model space is finite-dimensional,
having an invertible flat map at `x` is the same as being nondegenerate at `x`
(`TauCeti.SmoothTwoForm.isInvertible_flat_iff`). In that case, for two two-forms `σ₀`, `σ₁` on
`M`, the points at which every form `σ₀ + s (σ₁ - σ₀)`, `s ∈ [0, 1]`, is nondegenerate form an
open subset of `M`. These are the
open sets on which the Moser fields of Moser's argument are defined
([McDuffSalamon2017], §3.2).

## Main results

* `TauCeti.SmoothTwoForm.isOpen_setOf_isInvertible_flat_mpullback_prodMk`: the set of points of
  `N × M` at which the slice has an invertible flat map is open.
* `TauCeti.SmoothForm.coe_mpullback_prodMk_lineMapFamily`: the slices of
  `TauCeti.SmoothForm.lineMapFamily`, stated for the underlying rough forms.
* `TauCeti.SmoothTwoForm.isOpen_setOf_isInvertible_flat_add_smul_sub`: the same openness for the
  segment `σ₀ + s (σ₁ - σ₀)`, as a set of points `(s, x)` of `ℝ × M`.
* `TauCeti.SmoothTwoForm.isOpen_setOf_forall_mem_Icc_nondegenerate`: in finite dimensions, the
  set of points at which the whole segment from `σ₀` to `σ₁` is nondegenerate is open.

The proofs of `isOpen_setOf_isInvertible_flat_mpullback_prodMk` and
`isOpen_setOf_forall_mem_Icc_nondegenerate` follow Tau Ceti's private
`exists_isOpen_isInvertible_flat`
(`TauCeti/Geometry/Symplectic/Manifold/RelativeMoser.lean`): the flat maps form a continuous
section along a projection, the invertible ones form an open set, and the tube lemma passes to
the compact parameter interval.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017]
-/

public section

open Bundle Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The slices of `TauCeti.SmoothForm.lineMapFamily α₀ α₁ hc`, as rough forms: the pullback of
the underlying form along `x ↦ (t, x)` is the underlying form of `α₀ + c(t) (α₁ - α₀)`. -/
@[simp]
theorem SmoothForm.coe_mpullback_prodMk_lineMapFamily {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {k : ℕ} (α₀ α₁ : SmoothForm I M F k) {c : ℝ → ℝ} (hc : ContDiff ℝ ∞ c)
    (t : ℝ) :
    TauCeti.mpullback (F := F) I (𝓘(ℝ, ℝ).prod I) (Prod.mk t) (lineMapFamily α₀ α₁ hc).val =
      (α₀ + c t • (α₁ - α₀)).val :=
  (coe_mpullback _ _ _).symm.trans
    (congrArg Subtype.val (mpullback_prodMk_lineMapFamily α₀ α₁ hc t))

namespace SmoothTwoForm

/-- **Invertibility of the flat maps of a family is an open condition.** For a smooth two-form
`σ` on `N × M`, the set of points `(t, x)` at which the slice `σ_t = ι_t^* σ` has an invertible
flat map `T_x M → T_x^* M` is open in `N × M`. The model space of `M` is assumed complete. -/
theorem isOpen_setOf_isInvertible_flat_mpullback_prodMk [CompleteSpace E] {EN HN N : Type*}
    [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
    {J : ModelWithCorners ℝ EN HN} [TopologicalSpace N] [ChartedSpace HN N] [IsManifold J ∞ N]
    (σ : SmoothForm (J.prod I) (N × M) ℝ 2) :
    IsOpen {p : N × M |
      (flat (SmoothForm.mpullback (Prod.mk p.1) (contMDiff_const.prodMk contMDiff_id) σ)
        p.2).IsInvertible} :=
  -- The bundles and the base map are given explicitly: unification would otherwise read the
  -- section along the identity.
  Continuous.isOpen_setOf_clm_bundle_isInvertible (𝕜 := ℝ) (F₁ := E) (F₂ := E →L[ℝ] ℝ)
    (E₁ := TangentSpace I) (E₂ := fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) (b := Prod.snd)
    (ϕ := fun p : N × M ↦
      flat (SmoothForm.mpullback (Prod.mk p.1) (contMDiff_const.prodMk contMDiff_id) σ) p.2)
    (ContMDiff.continuous fun p ↦ contMDiffAt_sectionAlong_flat (b := Prod.snd)
      (σ := fun q : N × M ↦
        SmoothForm.mpullback (Prod.mk q.1) (contMDiff_const.prodMk contMDiff_id) σ)
      (SmoothForm.contMDiff_mpullback_prodMk σ p))

/-- **Invertibility of the flat maps along a segment is an open condition.** For two-forms `σ₀`,
`σ₁` on `M`, the set of points `(s, x)` of `ℝ × M` at which `σ₀ + s (σ₁ - σ₀)` has an invertible
flat map `T_x M → T_x^* M` is open. The model space of `M` is assumed complete. -/
theorem isOpen_setOf_isInvertible_flat_add_smul_sub [CompleteSpace E]
    (σ₀ σ₁ : SmoothTwoForm I M) :
    IsOpen {p : ℝ × M | ((σ₀ + p.1 • (σ₁ - σ₀)).flat p.2).IsInvertible} := by
  simpa only [SmoothForm.mpullback_prodMk_lineMapFamily, id_eq] using
    isOpen_setOf_isInvertible_flat_mpullback_prodMk
      (SmoothForm.lineMapFamily σ₀ σ₁ (contDiff_id (n := ∞)))

/-- **Nondegeneracy of a segment of two-forms is an open condition.** For two-forms `σ₀`, `σ₁`
on a finite-dimensional manifold, the set of points `x` at which every form
`σ₀ + s (σ₁ - σ₀)` with `s ∈ [0, 1]` is nondegenerate is open. -/
theorem isOpen_setOf_forall_mem_Icc_nondegenerate [FiniteDimensional ℝ E]
    (σ₀ σ₁ : SmoothTwoForm I M) :
    IsOpen {x : M | ∀ s ∈ Icc (0 : ℝ) 1,
      ((σ₀ + s • (σ₁ - σ₀)).bilinFormAt x).Nondegenerate} := by
  have hO := isOpen_setOf_isInvertible_flat_add_smul_sub σ₀ σ₁
  refine isOpen_iff_forall_mem_open.2 fun x hx ↦ ?_
  have hsub : Icc (0 : ℝ) 1 ×ˢ {x} ⊆
      {p : ℝ × M | ((σ₀ + p.1 • (σ₁ - σ₀)).flat p.2).IsInvertible} := by
    rintro ⟨s, y⟩ ⟨hs, rfl : y = x⟩
    exact isInvertible_flat_iff.2 (hx s hs)
  obtain ⟨u, V, -, hV, hu, hxV, huV⟩ :=
    generalized_tube_lemma isCompact_Icc isCompact_singleton hO hsub
  exact ⟨V, fun y hy s hs ↦ isInvertible_flat_iff.1 (huV (mk_mem_prod (hu hs) hy)), hV,
    hxV rfl⟩

end SmoothTwoForm

end TauCeti

end
