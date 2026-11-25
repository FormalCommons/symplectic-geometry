/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.Family
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Maps.Proper.Basic
import TauCeti.Geometry.Symplectic.Manifold.Opens
import TauCeti.Topology.Compactness.Compact
import TauCeti.Topology.VectorBundle.Hom

/-!
# Openness of nondegeneracy for families of two-forms

For a smooth family of two-forms on `M`, given as a smooth two-form `σ` on `N × M` with slices
`σ_t = ι_t^* σ`, the points `(t, x)` at which `σ_t` has an invertible flat map
`T_x M → T_x^* M` form an open subset of `N × M`. When the model space is finite-dimensional,
having an invertible flat map at `x` is the same as being nondegenerate at `x`
(`TauCeti.SmoothTwoForm.isInvertible_flat_iff`). In that case the points at which a single
two-form is nondegenerate form an open set, and, for two two-forms `σ₀`, `σ₁` on
`M`, the points at which every form `σ₀ + s (σ₁ - σ₀)`, `s ∈ [0, 1]`, is nondegenerate form an
open subset of `M`. The latter are the
open sets on which the Moser fields of Moser's argument are defined
([McDuffSalamon2017], §3.2).

## Main results

* `TauCeti.SmoothTwoForm.isOpen_setOf_isInvertible_flat_mpullback_prodMk`: the set of points of
  `N × M` at which the slice has an invertible flat map is open.
* `TauCeti.SmoothTwoForm.isOpen_setOf_forall_isInvertible_flat_mpullback_prodMk`: for compact
  `M`, the set of parameters whose slice has invertible flat maps everywhere is open.
* `TauCeti.SmoothTwoForm.isOpen_setOf_isInvertible_flat_add_smul_sub`: the same openness for the
  segment `σ₀ + s (σ₁ - σ₀)`, as a set of points `(s, x)` of `ℝ × M`.
* `TauCeti.SmoothTwoForm.isOpen_setOf_nondegenerate_bilinFormAt`: in finite dimensions, the set of
  points at which a two-form is nondegenerate is open.
* `TauCeti.SmoothTwoForm.isNondegenerate_mpullback_subtype_val_iff`,
  `TauCeti.SmoothForm.IsClosed.isSymplectic_mpullback_subtype_val`: a two-form restricted to an
  open set is nondegenerate exactly when the form is nondegenerate at each point of the set, and
  then symplectic if the form is closed.
* `TauCeti.SmoothTwoForm.isOpen_setOf_forall_mem_Icc_nondegenerate`: in finite dimensions, the
  set of points at which the whole segment from `σ₀` to `σ₁` is nondegenerate is open.
* `TauCeti.SmoothTwoForm.isOpen_setOf_forall_nondegenerate_bilinFormAt_add_smul`: in finite
  dimensions, for two-forms `σ₀`, `σ` on `M × N` with `M` compact, the set of pairs `(s, y)` of
  `ℝ × N` such that `σ₀ + s σ` is nondegenerate at every point of `M × {y}` is open.
* `TauCeti.SmoothTwoForm.bilinFormAt_add_smul_sub_of_eq`,
  `TauCeti.SmoothTwoForm.nondegenerate_bilinFormAt_add_smul_sub_of_eq`: at a point where `σ₀` and
  `σ₁` agree, every form `σ₀ + s (σ₁ - σ₀)` has the bilinear form of `σ₀`.

The proofs of `isOpen_setOf_isInvertible_flat_mpullback_prodMk` and
`isOpen_setOf_forall_mem_Icc_nondegenerate` follow Tau Ceti's private
`exists_isOpen_isInvertible_flat`
(`TauCeti/Geometry/Symplectic/Manifold/RelativeMoser.lean`): the flat maps form a continuous
section along a projection, the invertible ones form an open set, and the tube lemma passes to
the compact parameter interval. `bilinFormAt_add_smul_sub_of_eq` is Tau Ceti's private lemma of
the same name in that file, with the same proof.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017]
-/

public section

open Bundle Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

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

/-- **Nondegeneracy is an open condition.** For a two-form `σ` on a finite-dimensional manifold,
the set of points at which `σ` is nondegenerate is open. -/
theorem isOpen_setOf_nondegenerate_bilinFormAt [FiniteDimensional ℝ E] (σ : SmoothTwoForm I M) :
    IsOpen {x : M | (σ.bilinFormAt x).Nondegenerate} := by
  simp only [← isInvertible_flat_iff]
  -- The bundles and the base map are given explicitly, as in
  -- `isOpen_setOf_isInvertible_flat_mpullback_prodMk`.
  exact Continuous.isOpen_setOf_clm_bundle_isInvertible (𝕜 := ℝ) (F₁ := E) (F₂ := E →L[ℝ] ℝ)
    (E₁ := TangentSpace I) (E₂ := fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) (b := id)
    (ϕ := σ.flat) σ.contMDiff_flat.continuous

/-- The restriction of a two-form `σ` to an open set `U` is nondegenerate if and only if `σ` is
nondegenerate at every point of `U`. -/
theorem isNondegenerate_mpullback_subtype_val_iff {σ : SmoothTwoForm I M}
    {U : TopologicalSpace.Opens M} :
    IsNondegenerate (SmoothForm.mpullback (Subtype.val : U → M) contMDiff_subtypeVal σ) ↔
      ∀ x ∈ U, (σ.bilinFormAt x).Nondegenerate :=
  ⟨fun h x hx ↦ (nondegenerate_bilinFormAt_mpullback_subtype_val_iff ⟨x, hx⟩).1
      (h.nondegenerate_bilinFormAt _),
    fun h ↦ isNondegenerate_iff_forall_ker_bilinFormAt_eq_bot.2 fun x ↦
      ((nondegenerate_bilinFormAt_mpullback_subtype_val_iff (σ := σ) x).2
        (h x x.property)).ker_eq_bot⟩

/-- A closed two-form `σ` that is nondegenerate at every point of an open set `U` restricts to a
symplectic form on `U`. -/
theorem _root_.TauCeti.SmoothForm.IsClosed.isSymplectic_mpullback_subtype_val
    {σ : SmoothTwoForm I M} (hσ : σ.IsClosed) {U : TopologicalSpace.Opens M}
    (h : ∀ x ∈ U, (σ.bilinFormAt x).Nondegenerate) :
    IsSymplectic (SmoothForm.mpullback (Subtype.val : U → M) contMDiff_subtypeVal σ) :=
  ⟨hσ.mpullback _ _, isNondegenerate_mpullback_subtype_val_iff.2 h⟩

/-- **Nondegeneracy of whole slices is an open condition on the parameter.** For a smooth
two-form `σ` on `N × M` with `M` compact, the set of parameters `t` at which the slice
`σ_t = ι_t^* σ` has an invertible flat map at every point of `M` is open in `N`. The model space of
`M` is assumed complete. -/
theorem isOpen_setOf_forall_isInvertible_flat_mpullback_prodMk [CompleteSpace E] [CompactSpace M]
    {EN HN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
    {J : ModelWithCorners ℝ EN HN} [TopologicalSpace N] [ChartedSpace HN N] [IsManifold J ∞ N]
    (σ : SmoothForm (J.prod I) (N × M) ℝ 2) :
    IsOpen {t : N | ∀ x : M,
      (flat (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) σ)
        x).IsInvertible} := by
  -- Its complement is the projection of the closed set of points `(t, x)` with a non-invertible
  -- flat map, and the projection `N × M → N` is closed since `M` is compact.
  have h : {t : N | ∀ x : M,
      (flat (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) σ)
        x).IsInvertible} =
      (Prod.fst '' {p : N × M |
        (flat (SmoothForm.mpullback (Prod.mk p.1) (contMDiff_const.prodMk contMDiff_id) σ)
          p.2).IsInvertible}ᶜ)ᶜ := by
    ext t
    simp
  rw [h]
  exact (isClosedMap_fst_of_compactSpace _
    (isOpen_setOf_isInvertible_flat_mpullback_prodMk σ).isClosed_compl).isOpen_compl

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

/-- **Nondegeneracy on whole slices along a line of two-forms is an open condition.** For
two-forms `σ₀`, `σ` on `M × N`, with `M` compact and both model spaces finite-dimensional, the set
of pairs `(s, y)` of `ℝ × N` such that `σ₀ + s σ` is nondegenerate at every point `(x, y)`,
`x ∈ M`, is open in `ℝ × N`. -/
theorem isOpen_setOf_forall_nondegenerate_bilinFormAt_add_smul [FiniteDimensional ℝ E]
    [CompactSpace M] {EN HN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
    [FiniteDimensional ℝ EN] [TopologicalSpace HN] {J : ModelWithCorners ℝ EN HN}
    [TopologicalSpace N] [ChartedSpace HN N] [IsManifold J ∞ N]
    (σ₀ σ : SmoothTwoForm (I.prod J) (M × N)) :
    IsOpen {p : ℝ × N | ∀ x : M, ((σ₀ + p.1 • σ).bilinFormAt (x, p.2)).Nondegenerate} := by
  -- the points `(s, z)` of `ℝ × (M × N)` at which `σ₀ + s σ = σ₀ + s ((σ₀ + σ) - σ₀)` is
  -- nondegenerate form an open set, and the tube lemma passes to the compact factor `M`
  have hO := isOpen_setOf_isInvertible_flat_add_smul_sub σ₀ (σ₀ + σ)
  simp only [add_sub_cancel_left, isInvertible_flat_iff] at hO
  exact isOpen_forall_prodMk_mem continuous_id
    (hO.preimage (continuous_fst.fst.prodMk (continuous_snd.prodMk continuous_fst.snd)))

/-- At a point where `σ₀` and `σ₁` agree, every form `σ₀ + s (σ₁ - σ₀)` of the line through them
has the bilinear form of `σ₀`. -/
theorem bilinFormAt_add_smul_sub_of_eq {σ₀ σ₁ : SmoothTwoForm I M} {x : M}
    (h : (σ₁ - σ₀).val x = 0) (s : ℝ) :
    (σ₀ + s • (σ₁ - σ₀)).bilinFormAt x = σ₀.bilinFormAt x := by
  ext v w
  simp only [SmoothForm.bilinFormAt_apply, SmoothBundleForm.eval₂_apply,
    SmoothForm.add_toRoughForm, Pi.add_apply, SetLike.val_smul, Pi.smul_apply, h, smul_zero,
    add_zero]

/-- At a point where `σ₀` and `σ₁` agree and `σ₀` is nondegenerate, every form
`σ₀ + s (σ₁ - σ₀)` of the line through them is nondegenerate. -/
theorem nondegenerate_bilinFormAt_add_smul_sub_of_eq {σ₀ σ₁ : SmoothTwoForm I M} {x : M}
    (h : (σ₁ - σ₀).val x = 0) (hσ₀ : (σ₀.bilinFormAt x).Nondegenerate) (s : ℝ) :
    ((σ₀ + s • (σ₁ - σ₀)).bilinFormAt x).Nondegenerate := by
  rw [bilinFormAt_add_smul_sub_of_eq h s]
  exact hσ₀

end SmoothTwoForm

end TauCeti

end
