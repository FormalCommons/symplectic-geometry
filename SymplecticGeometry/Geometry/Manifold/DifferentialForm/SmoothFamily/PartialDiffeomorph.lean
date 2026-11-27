/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.Basic
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.PartialDiffeomorph
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.Basic

/-!
# Extension by zero of a smooth family along a partial diffeomorphism

Let `ψ` be a smooth partial diffeomorphism from `M` to its model space `E`, and
`a : N × E → E [⋀^Fin k]→L[ℝ] F` a jointly smooth family of flat forms on `E`, indexed by a
parameter manifold `N`, whose slices `a (t, ·)` all vanish off one compact subset `K` of
`ψ.target`. Extending each slice by zero along `ψ`
(`TauCeti.RoughForm.extendByZeroAlong`, `TauCeti.SmoothForm.extendByZeroAlong`) gives a smooth
family of forms on `M` (`SymplecticGeometry.IsSmoothFamily.extendByZeroAlong`).

This is the family version of `TauCeti.IsSmoothForm.extendByZeroAlong`, and its proof follows
that one. Near a point of `ψ.source`, the family is the pullback along `y ↦ (t, ψ y)` of a smooth
form on `N × E` whose slices are the `a (t, ·)`, and is smooth there by Tau Ceti's
`ContMDiffAt.mpullback_form_family`, applied as in
`SymplecticGeometry.IsSmoothFamily.contMDiffAt_of_mpullback_family`. Off the compact set
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
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}
  {EN HN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  [TopologicalSpace N] [ChartedSpace HN N] {J : ModelWithCorners ℝ EN HN} [IsManifold J 1 N]

/-- **Extension by zero of a smooth family along a partial diffeomorphism.** Let `ψ` be a smooth
partial diffeomorphism from `M` to `E`, and `a : N × E → E [⋀^Fin k]→L[ℝ] F` jointly smooth,
with `a (t, y) = 0` for every parameter `t` and every `y` outside a compact set `K ⊆ ψ.target`.
A family `β` of smooth forms on `M` whose value at `t` is the extension by zero of `a (t, ·)`
along `ψ` is smooth. -/
theorem extendByZeroAlong {ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞}
    {a : N × E → E [⋀^Fin k]→L[ℝ] F}
    (ha : ContMDiff (J.prod 𝓘(ℝ, E)) 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F) ∞ a)
    {K : Set E} (hK : IsCompact K) (hKψ : K ⊆ ψ.target) (haK : ∀ t, ∀ y ∉ K, a (t, y) = 0)
    {β : N → SmoothForm I M F k}
    (hβ : ∀ t, (β t).val = RoughForm.extendByZeroAlong ψ fun y ↦ a (t, y)) :
    IsSmoothFamily J β := by
  -- The slices of `a`, as a smooth family of forms on `E`, and a form `Ω` on `N × E` with these
  -- slices.
  have hslice : ∀ t, ContDiff ℝ ∞ fun y ↦ a (t, y) := fun t ↦
    contMDiff_iff_contDiff.mp (ha.comp (contMDiff_const.prodMk contMDiff_id))
  let α : N → SmoothForm 𝓘(ℝ, E) E F k := fun t ↦
    ⟨fun y ↦ a (t, y), (isSmoothForm_modelSpace_iff.mpr (hslice t)).mem_smoothBundleForms⟩
  obtain ⟨Ω, hΩ⟩ := isSmoothFamily_def.mp (of_contMDiff_val (α := α) ha)
  rw [isSmoothFamily_iff_contMDiff]
  rintro ⟨t, x⟩
  by_cases hx : x ∈ ψ.source
  · -- Near `x`, the family is the pullback of `Ω` along `y ↦ (s, ψ y)`.
    have key := ContMDiffAt.mpullback_form_family (J := J.prod I) (I := I) (m := ∞) (n := ∞)
      (φ := Ω.val) (f := fun q y ↦ (q.1, ψ y)) (g := Prod.snd) (p₀ := (t, x))
      (Ω.contMDiff _)
      ((contMDiff_fst.comp contMDiff_fst).contMDiffAt.prodMk
        ((ψ.contMDiffAt hx).comp _ contMDiffAt_snd))
      contMDiffAt_snd (by simp)
    refine key.congr_of_eventuallyEq ?_
    filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
      (ψ.open_source.mem_nhds hx)] with q hq
    obtain ⟨s, y⟩ := q
    rw [sliceSection_apply]
    refine congrArg (TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F)
      (E := fun y : M ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] Trivial M F y) y) ?_
    have hψ : MDifferentiableAt I 𝓘(ℝ, E) ψ y := (ψ.contMDiffAt hq).mdifferentiableAt (by simp)
    have hmk : MDifferentiableAt 𝓘(ℝ, E) (J.prod 𝓘(ℝ, E)) (Prod.mk s) (ψ y) :=
      (contMDiff_const.prodMk contMDiff_id (n := ∞)).mdifferentiableAt (by simp)
    have hcomp : (fun y ↦ (s, ψ y)) = Prod.mk s ∘ ψ := rfl
    have hslice := congrArg Subtype.val (hΩ s)
    simp only [SmoothForm.coe_mpullback] at hslice
    dsimp only
    rw [hβ, RoughForm.extendByZeroAlong_apply_of_mem _ hq, hcomp, mpullback_comp_at hψ hmk,
      hslice]
  · -- Near `x`, every member of the family vanishes.
    have hKc : IsClosed (ψ.symm '' K) :=
      (ψ.symm.isCompact_image_of_subset_source hK hKψ).isClosed
    have hxK : x ∉ ψ.symm '' K := fun ⟨y, hy, hyx⟩ ↦ hx (hyx ▸ ψ.map_target (hKψ hy))
    have hev : ∀ᶠ q : N × M in 𝓝 (t, x), ∀ s, (β s).val q.2 = 0 := by
      filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
        (hKc.isOpen_compl.mem_nhds hxK)] with q hq s
      rw [hβ]
      refine RoughForm.extendByZeroAlong_apply_of_notMem_image _ fun ⟨y, hy, hyq⟩ ↦
        hq ⟨y, ?_, hyq⟩
      by_contra hyK
      exact notMem_tsupport_iff_eventuallyEq.mpr ((hK.isClosed.isOpen_compl.eventually_mem hyK).mono
        fun z hz ↦ haK s z hz) hy
    refine ((contMDiff_zeroSection ℝ (fun y : M ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] F)).comp
      contMDiff_snd (t, x)).congr_of_eventuallyEq ?_
    filter_upwards [hev] with q hq
    rw [sliceSection_apply, hq q.1]
    -- The zero section takes the value `0` at every point.
    rfl

end SymplecticGeometry.IsSmoothFamily

end
