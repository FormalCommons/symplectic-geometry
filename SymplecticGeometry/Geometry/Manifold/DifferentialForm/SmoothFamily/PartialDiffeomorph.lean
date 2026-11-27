/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.Basic
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.PartialDiffeomorph
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Topology.Algebra.Support

/-!
# Extension by zero of a smooth family along a partial diffeomorphism

Let `ψ` be a smooth partial diffeomorphism from `M` to a real normed space `D`, and
`a : N × D → D [⋀^Fin k]→L[ℝ] F` a jointly smooth family of flat forms on `D`, indexed by a
parameter manifold `N`, whose slices `a (t, ·)` all vanish off one compact subset `K` of
`ψ.target`. Extending each slice by zero along `ψ`
(`TauCeti.RoughForm.extendByZeroAlong`, `TauCeti.SmoothForm.extendByZeroAlong`) gives a smooth
family of forms on `M` (`SymplecticGeometry.IsSmoothFamily.extendByZeroAlong`).

This is the family version of `TauCeti.IsSmoothForm.extendByZeroAlong`, and its proof follows
that one. Near a point of `ψ.source`, the family is the pullback along `y ↦ (t, ψ y)` of a smooth
form on `N × D` whose slices are the `a (t, ·)`, and is smooth there by
`SymplecticGeometry.contMDiffAt_sliceSection_of_eventually_eq_mpullback`. Off the compact set
`ψ.symm '' K`, which is closed since `M` is Hausdorff, every member of the family vanishes.
-/

public section

open Bundle Set Filter
open scoped Manifold Topology ContDiff

namespace SymplecticGeometry.IsSmoothFamily

open TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I 1 M] [T2Space M]
  {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}
  {EN HN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  [TopologicalSpace N] [ChartedSpace HN N] {J : ModelWithCorners ℝ EN HN} [IsManifold J 1 N]

/-- **Extension by zero of a smooth family along a partial diffeomorphism.** Let `ψ` be a smooth
partial diffeomorphism from `M` to `D`, and `a : N × D → D [⋀^Fin k]→L[ℝ] F` jointly smooth,
with `a (t, y) = 0` for every parameter `t` and every `y` outside a compact set `K ⊆ ψ.target`.
A family `β` of smooth forms on `M` whose value at `t` is the extension by zero of `a (t, ·)`
along `ψ` is smooth. -/
theorem extendByZeroAlong {ψ : PartialDiffeomorph I 𝓘(ℝ, D) M D ∞}
    {a : N × D → D [⋀^Fin k]→L[ℝ] F}
    (ha : ContMDiff (J.prod 𝓘(ℝ, D)) 𝓘(ℝ, D [⋀^Fin k]→L[ℝ] F) ∞ a)
    {K : Set D} (hK : IsCompact K) (hKψ : K ⊆ ψ.target) (haK : ∀ t, ∀ y ∉ K, a (t, y) = 0)
    {β : N → SmoothForm I M F k}
    (hβ : ∀ t, (β t).val = RoughForm.extendByZeroAlong ψ fun y ↦ a (t, y)) :
    IsSmoothFamily J β := by
  -- The slices of `a`, as a smooth family of forms on `D`, and a form `Ω` on `N × D` with these
  -- slices.
  have hslice : ∀ t, ContDiff ℝ ∞ fun y ↦ a (t, y) := fun t ↦
    contMDiff_iff_contDiff.mp (ha.comp (contMDiff_const.prodMk contMDiff_id))
  let α : N → SmoothForm 𝓘(ℝ, D) D F k := fun t ↦
    ⟨fun y ↦ a (t, y), (isSmoothForm_modelSpace_iff.mpr (hslice t)).mem_smoothBundleForms⟩
  obtain ⟨Ω, hΩ⟩ := isSmoothFamily_def.mp (of_contMDiff_val (α := α) ha)
  rw [isSmoothFamily_iff_contMDiff]
  rintro ⟨t, x⟩
  by_cases hx : x ∈ ψ.source
  · -- Near `x`, the family is the pullback of `Ω` along `y ↦ (s, ψ y)`.
    refine contMDiffAt_sliceSection_of_eventually_eq_mpullback (g := fun s y ↦ (s, ψ y))
      (Ω.contMDiff _) (contMDiffAt_fst.prodMk ((ψ.contMDiffAt hx).comp _ contMDiffAt_snd))
      (by simp) ?_
    filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
      (ψ.open_source.mem_nhds hx)] with q hq
    obtain ⟨s, y⟩ := q
    have hψ : MDifferentiableAt I 𝓘(ℝ, D) ψ y := (ψ.contMDiffAt hq).mdifferentiableAt (by simp)
    have hmk : MDifferentiableAt 𝓘(ℝ, D) (J.prod 𝓘(ℝ, D)) (Prod.mk s) (ψ y) :=
      (contMDiff_const.prodMk contMDiff_id (n := ∞)).mdifferentiableAt (by simp)
    have hcomp : (fun y ↦ (s, ψ y)) = Prod.mk s ∘ ψ := rfl
    have hslice := congrArg Subtype.val (hΩ s)
    simp only [SmoothForm.coe_mpullback] at hslice
    rw [hβ, RoughForm.extendByZeroAlong_apply_of_mem _ hq, hcomp, mpullback_comp_at hψ hmk,
      hslice]
  · -- Near `x`, every member of the family vanishes.
    have hKc : IsClosed (ψ.symm '' K) :=
      (ψ.symm.isCompact_image_of_subset_source hK hKψ).isClosed
    have hxK : x ∉ ψ.symm '' K := fun ⟨y, hy, hyx⟩ ↦ hx (hyx ▸ ψ.map_target (hKψ hy))
    refine contMDiffAt_sliceSection_of_eventually_eq_zero ?_
    filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
      (hKc.isOpen_compl.mem_nhds hxK)] with q hq
    rw [hβ]
    exact RoughForm.extendByZeroAlong_apply_of_notMem_image _ fun h ↦ hq (image_mono
      (tsupport_subset_of_forall_notMem_eq_zero (haK q.1) hK.isClosed) h)

end SymplecticGeometry.IsSmoothFamily

end
