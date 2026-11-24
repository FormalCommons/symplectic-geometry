/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.FiberBundle.Basic
public import TauCeti.Geometry.Manifold.FiberBundle.Principal

/-!
# Smooth maps into the charted total space of a fibre bundle

Tau Ceti charts the total space of a fibre bundle whose model fibre is a manifold through a copy,
`TauCeti.ManifoldTotalSpace F E`, identified with `Bundle.TotalSpace F E` by the homeomorphism
`TauCeti.ManifoldTotalSpace.homeomorph`. Smoothness of a family of points of the bundle, such as a
local section, is stated for its composite with that homeomorphism, while continuity is usually
stated in `Bundle.TotalSpace F E` itself. This file relates the two, pulls differential forms
on the total space back along such sections, and records the smoothness of the fibre coordinate of
the trivialization of a principal bundle given by a local section.

## Main results

* `TauCeti.ManifoldTotalSpace.continuousOn_of_contMDiffOn_homeomorph`: a map into the total space
  whose composite with `homeomorph F E` is `C^n` on a set is continuous on that set.
* `TauCeti.ManifoldTotalSpace.projContMDiffMap`: the projection to the base as a `C^n` map, along
  which bundles over the base pull back to the total space.
* `TauCeti.ManifoldTotalSpace.mfderiv_proj_mfderiv_section_apply`: the derivative of a section is
  a right inverse of the derivative of the projection.
* `TauCeti.ManifoldTotalSpace.mpullback_mpullback_proj_apply`: a section pulls `π^* a` back to
  `a`.
* `TauCeti.ManifoldTotalSpace.mpullback_add_mpullback_proj_apply`: the pull-back of `α + π^* a`
  along a section is the pull-back of `α` plus `a`.
* `TauCeti.PrincipalBundle.contMDiffAt_snd_trivializationOfSection`: the fibre coordinate of the
  trivialization that a `C^n` local section determines is `C^n` over the section's domain.
-/

public section

open Bundle
open scoped ContDiff Manifold

namespace TauCeti.ManifoldTotalSpace

section AnyField

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

variable (n F E IB IF) in
/-- The projection of the charted total space of a fibre bundle to its base, as a `C^n` map. -/
-- Exposed so that the fibre of a bundle pulled back along it over `x` is, by definition, the
-- fibre over the projection of `x`.
@[expose] def projContMDiffMap : C^n⟮IB.prod IF, ManifoldTotalSpace F E; IB, B⟯ :=
  ⟨fun x ↦ ((homeomorph F E).symm x).proj, contMDiff_proj n F E IB IF⟩

/-- The `C^n` projection is the projection, read through `homeomorph F E`. -/
@[simp]
theorem coe_projContMDiffMap :
    ⇑(projContMDiffMap n F E IB IF) = fun x ↦ ((homeomorph F E).symm x).proj := (rfl)

/-- A section `τ` of a fibre bundle, differentiable at `x` as a map into the charted total space, is
a right inverse of the projection to first order at `x`: `dπ (dτ v) = v`. -/
theorem mfderiv_proj_mfderiv_section_apply {τ : ∀ b, E b} {x : B}
    (hτ : MDifferentiableAt IB (IB.prod IF) (fun b ↦ homeomorph F E ⟨b, τ b⟩) x)
    (v : TangentSpace IB x) :
    mfderiv (IB.prod IF) IB (fun y : ManifoldTotalSpace F E ↦ ((homeomorph F E).symm y).proj)
        (homeomorph F E ⟨x, τ x⟩)
        (mfderiv IB (IB.prod IF) (fun b ↦ homeomorph F E ⟨b, τ b⟩) x v) = v := by
  have hpt : (fun y : ManifoldTotalSpace F E ↦ ((homeomorph F E).symm y).proj) ∘
      (fun b ↦ homeomorph F E ⟨b, τ b⟩) = id :=
    funext fun b ↦ by simp
  rw [← mfderiv_comp_apply x ((contMDiff_proj 1 F E IB IF _).mdifferentiableAt one_ne_zero) hτ,
    hpt, mfderiv_id, ContinuousLinearMap.id_apply]

end AnyField

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

omit [IsManifold IB ∞ B] [IsManifold IF ∞ F] [ContMDiffFiberBundle ∞ F E IB IF] in
/-- A section `τ` of a fibre bundle, differentiable at `x` as a map into the charted total space,
pulls the pull-back `π^* a` of a form on the base back to `a` at `x`. -/
theorem mpullback_mpullback_proj_apply (a : RoughForm IB B G k) {τ : ∀ b, E b} {x : B}
    (hτ : MDifferentiableAt IB (IB.prod IF) (fun b ↦ homeomorph F E ⟨b, τ b⟩) x) :
    TauCeti.mpullback IB (IB.prod IF) (fun b ↦ homeomorph F E ⟨b, τ b⟩)
        (TauCeti.mpullback (IB.prod IF) IB
          (fun y : ManifoldTotalSpace F E ↦ ((homeomorph F E).symm y).proj) a) x = a x := by
  have hpt : (fun y : ManifoldTotalSpace F E ↦ ((homeomorph F E).symm y).proj) ∘
      (fun b ↦ homeomorph F E ⟨b, τ b⟩) = id :=
    funext fun b ↦ by simp
  rw [← mpullback_comp_at hτ ((contMDiff_proj 1 F E IB IF _).mdifferentiableAt one_ne_zero), hpt,
    mpullback_id]

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
  rw [Submodule.coe_add, SmoothForm.coe_mpullback, mpullback_add, Pi.add_apply,
    mpullback_mpullback_proj_apply a.val hτ]

end Pullback

end TauCeti.ManifoldTotalSpace

/-! ### The fibre coordinate of the trivialization of a local section -/

namespace TauCeti.PrincipalBundle

variable {n : ℕ∞ω} {𝕜 B G : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  {EG : Type*} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG] {HG : Type*} [TopologicalSpace HG]
  {IG : ModelWithCorners 𝕜 EG HG} [Group G] [TopologicalSpace G] [ChartedSpace HG G]
  [IsTopologicalGroup G] [LieGroup IG n G]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]
  {σ : ∀ b, P b} {U : Set B} {hU : IsOpen U}
  {hσ : ContinuousOn (fun b ↦ TotalSpace.mk' G b (σ b)) U}

/-- Let `σ` be a section of a principal bundle that is `C^n` on an open set `U`, as a map into the
charted total space. The fibre coordinate of the trivialization that `σ` determines is `C^n` at
every point of the charted total space over `U`. -/
theorem contMDiffAt_snd_trivializationOfSection
    (hσ' : ContMDiffOn IB (IB.prod IG) n
      (fun b ↦ ManifoldTotalSpace.homeomorph G P ⟨b, σ b⟩) U)
    {x : ManifoldTotalSpace G P} (hx : ((ManifoldTotalSpace.homeomorph G P).symm x).proj ∈ U) :
    ContMDiffAt (IB.prod IG) IG n
      (fun y ↦ (trivializationOfSection σ hU hσ ((ManifoldTotalSpace.homeomorph G P).symm y)).2)
      x :=
  (contMDiff_snd.comp_contMDiffOn (contMDiffOn_trivializationOfSection hσ')).contMDiffAt
    ((hU.preimage (ManifoldTotalSpace.contMDiff_proj n G P IB IG).continuous).mem_nhds hx)

end TauCeti.PrincipalBundle

end
