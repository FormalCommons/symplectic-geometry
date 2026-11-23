/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.FiberBundle.Basic

/-!
# Smooth maps into the charted total space of a fibre bundle

Tau Ceti charts the total space of a fibre bundle whose model fibre is a manifold through a copy,
`TauCeti.ManifoldTotalSpace F E`, identified with `Bundle.TotalSpace F E` by the homeomorphism
`TauCeti.ManifoldTotalSpace.homeomorph`. Smoothness of a family of points of the bundle, such as a
local section, is stated for its composite with that homeomorphism, while continuity is usually
stated in `Bundle.TotalSpace F E` itself. This file relates the two, and pulls differential forms
on the total space back along such sections.

## Main results

* `TauCeti.ManifoldTotalSpace.continuousOn_of_contMDiffOn_homeomorph`: a map into the total space
  whose composite with `homeomorph F E` is `C^n` on a set is continuous on that set.
* `TauCeti.ManifoldTotalSpace.mpullback_add_mpullback_proj_apply`: the pull-back of `α + π^* a`
  along a section is the pull-back of `α` plus `a`.
-/

public section

open Bundle
open scoped ContDiff Manifold

namespace TauCeti.ManifoldTotalSpace

section Continuity

variable {n : ℕ∞ω} {𝕜 B F M : Type*} {E : B → Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM} [TopologicalSpace M] [ChartedSpace HM M]
  [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace 𝕜 EF] {HF : Type*}
  [TopologicalSpace HF] {IF : ModelWithCorners 𝕜 EF HF} [TopologicalSpace F] [ChartedSpace HF F]
  [FiberBundle F E]

/-- A map `f` into the total space of a fibre bundle whose composite with
`homeomorph F E`, into the copy charted through the fibre, is `C^n` on a set `s` is continuous on
`s` as a map into `Bundle.TotalSpace F E`. -/
theorem continuousOn_of_contMDiffOn_homeomorph {f : M → TotalSpace F E} {s : Set M}
    (h : ContMDiffOn IM (IB.prod IF) n (fun x ↦ homeomorph F E (f x)) s) : ContinuousOn f s :=
  ((homeomorph F E).comp_continuousOn_iff f s).1 h.continuousOn

end Continuity

/-! ### Pulling back forms along sections -/

section Pullback

variable {B F : Type*} {E : B → Type*}
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B]
  [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace ℝ EF] {HF : Type*}
  [TopologicalSpace HF] {IF : ModelWithCorners ℝ EF HF} [TopologicalSpace F] [ChartedSpace HF F]
  [IsManifold IF ∞ F] [FiberBundle F E] [ContMDiffFiberBundle ∞ F E IB IF]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {k : ℕ}

/-- The pull-back of `α + π^* a` along a section `τ` of a fibre bundle, differentiable at `x` as a
map into the charted total space, is `τ^* α + a` at `x`. -/
theorem mpullback_add_mpullback_proj_apply
    (α : SmoothForm (IB.prod IF) (ManifoldTotalSpace F E) G k) (a : SmoothForm IB B G k)
    {τ : ∀ b, E b} {x : B}
    (hτ : MDifferentiableAt IB (IB.prod IF) (fun b ↦ homeomorph F E ⟨b, τ b⟩) x) :
    TauCeti.mpullback IB (IB.prod IF) (fun b ↦ homeomorph F E ⟨b, τ b⟩)
        (α + SmoothForm.mpullback
          (fun y : ManifoldTotalSpace F E ↦ ((homeomorph F E).symm y).proj)
          (contMDiff_proj ∞ F E IB IF) a).val x =
      TauCeti.mpullback IB (IB.prod IF) (fun b ↦ homeomorph F E ⟨b, τ b⟩) α.val x + a.val x := by
  have hpt : (fun y : ManifoldTotalSpace F E ↦ ((homeomorph F E).symm y).proj) ∘
      (fun b ↦ homeomorph F E ⟨b, τ b⟩) = id :=
    funext fun b ↦ by simp
  rw [Submodule.coe_add, SmoothForm.coe_mpullback, mpullback_add, Pi.add_apply,
    ← mpullback_comp_at hτ ((contMDiff_proj 1 F E IB IF _).mdifferentiableAt one_ne_zero), hpt,
    mpullback_id]

end Pullback

end TauCeti.ManifoldTotalSpace

end
