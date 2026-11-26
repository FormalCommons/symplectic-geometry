/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.FiberBundle.Basic
public import TauCeti.Geometry.Manifold.FiberBundle.Principal
public import TauCeti.Geometry.Manifold.FiberBundle.Submersion
public import TauCeti.Topology.FiberBundle.Proper
public import TauCeti.Topology.FiberBundle.Separation
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Semibasic

/-!
# Smooth maps into the charted total space of a fibre bundle

Tau Ceti charts the total space of a fibre bundle whose model fibre is a manifold through a copy,
`TauCeti.ManifoldTotalSpace F E`, identified with `Bundle.TotalSpace F E` by the homeomorphism
`TauCeti.ManifoldTotalSpace.homeomorph`. Smoothness of a family of points of the bundle, such as a
local section, is stated for its composite with that homeomorphism, while continuity is usually
stated in `Bundle.TotalSpace F E` itself. This file relates the two, pulls differential forms
on the total space back along such sections, names the fibre coordinate of a trivialization as a
map on the charted total space, and records its smoothness, in particular for the trivialization
of a principal bundle given by a local section.

## Main results

* `TauCeti.ManifoldTotalSpace.continuousOn_of_contMDiffOn_homeomorph`: a map into the total space
  whose composite with `homeomorph F E` is `C^n` on a set is continuous on that set.
* `TauCeti.ManifoldTotalSpace.projContMDiffMap`: the projection to the base as a `C^n` map, along
  which bundles over the base pull back to the total space. Its coercion simplifies to the map
  `fun x ↦ ((homeomorph F E).symm x).proj` (`coe_projContMDiffMap`), the form in which Tau Ceti
  states its lemmas about the projection. Lemmas whose content does not depend on the smoothness
  index, such as those about derivatives, hold for `projContMDiffMap n` with any `n`.
* `TauCeti.ManifoldTotalSpace.mdifferentiable_projContMDiffMap`: the projection is differentiable.
* `TauCeti.ManifoldTotalSpace.isSemibasic_projContMDiffMap_iff`: whether a form is semibasic for
  `projContMDiffMap n` (`TauCeti.RoughForm.IsSemibasic`) does not depend on `n`.
* `TauCeti.ManifoldTotalSpace.surjective_projContMDiffMap`,
  `TauCeti.ManifoldTotalSpace.isSubmersion_projContMDiffMap`: the projection is a surjective
  submersion.
* `TauCeti.ManifoldTotalSpace.projContMDiffMap_comp_homeomorph_mk`: a section is a right inverse
  of the projection.
* `TauCeti.ManifoldTotalSpace.exists_contMDiffOn_section`: over a neighbourhood of every point of
  the base there is a `C^n` local section, the inverse of a trivialization at a constant fibre
  coordinate.
* `TauCeti.ManifoldTotalSpace.mfderiv_proj_mfderiv_section_apply`: the derivative of a section is
  a right inverse of the derivative of the projection.
* `TauCeti.ManifoldTotalSpace.mpullback_mpullback_proj_apply`: a section pulls `π^* a` back to
  `a`.
* `TauCeti.ManifoldTotalSpace.mpullback_add_mpullback_proj_apply`: the pull-back of `α + π^* a`
  along a section is the pull-back of `α` plus `a`.
* `TauCeti.ManifoldTotalSpace.compactSpace`: the charted total space is compact when the base and
  the model fibre are, as Tau Ceti's `FiberBundle.compactSpace_totalSpace` says of
  `Bundle.TotalSpace F E`.
* `TauCeti.ManifoldTotalSpace.t2Space`: the charted total space is Hausdorff when the base and
  the model fibre are, as Tau Ceti's `TauCeti.FiberBundle.t2Space_totalSpace` says of
  `Bundle.TotalSpace F E`.
* `Bundle.Trivialization.manifoldSnd`: the fibre coordinate of a trivialization, as a map on the
  charted total space; `Bundle.Trivialization.contMDiffOn_manifoldSnd`: it is `C^n` over the base
  set of a trivialization in the atlas.
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

/-- The `C^n` projection is the projection, read through `homeomorph F E`. This is the simp normal
form, so that `simp` can use Tau Ceti's lemmas about the projection, which are stated with the
map written out. -/
@[simp]
theorem coe_projContMDiffMap :
    ⇑(projContMDiffMap n F E IB IF) = fun x ↦ ((homeomorph F E).symm x).proj := (rfl)

/-- The projection of the charted total space is differentiable, whatever the smoothness index
`n` of `projContMDiffMap n` (which does not change the underlying map). -/
theorem mdifferentiable_projContMDiffMap :
    MDifferentiable (IB.prod IF) IB (projContMDiffMap n F E IB IF) := by
  rw [coe_projContMDiffMap]
  exact (contMDiff_proj 1 F E IB IF).mdifferentiable one_ne_zero

variable (n F E IB IF) in
/-- The projection of the charted total space of a fibre bundle with nonempty fibre is
surjective. -/
theorem surjective_projContMDiffMap [Nonempty F] :
    Function.Surjective (projContMDiffMap n F E IB IF) := by
  rw [coe_projContMDiffMap]
  exact (FiberBundle.surjective_proj F E).comp (homeomorph F E).symm.surjective

variable (n F E IB IF) in
/-- The projection of the charted total space of a `C^n` fibre bundle over a `C^n` manifold, with
a `C^n` manifold as fibre, is a `C^n` submersion (`TauCeti.ManifoldTotalSpace.isSubmersion_proj`,
stated for `projContMDiffMap n`). -/
theorem isSubmersion_projContMDiffMap [IsManifold IB n B] [IsManifold IF n F]
    [ContMDiffFiberBundle n F E IB IF] :
    Manifold.IsSubmersion (IB.prod IF) IB n (projContMDiffMap n F E IB IF) := by
  rw [coe_projContMDiffMap]
  exact isSubmersion_proj n F E IB IF

/-- A section `τ` of a fibre bundle, read as a map into the charted total space, is a right
inverse of the projection: `π ∘ τ = id`. -/
theorem projContMDiffMap_comp_homeomorph_mk (τ : ∀ b, E b) :
    projContMDiffMap n F E IB IF ∘ (fun b ↦ homeomorph F E ⟨b, τ b⟩) = id :=
  funext fun b ↦ by simp

/-- A section `τ` of a fibre bundle, differentiable at `x` as a map into the charted total space, is
a right inverse of the projection to first order at `x`: `dπ (dτ v) = v`. -/
theorem mfderiv_proj_mfderiv_section_apply {τ : ∀ b, E b} {x : B}
    (hτ : MDifferentiableAt IB (IB.prod IF) (fun b ↦ homeomorph F E ⟨b, τ b⟩) x)
    (v : TangentSpace IB x) :
    mfderiv (IB.prod IF) IB (projContMDiffMap n F E IB IF) (homeomorph F E ⟨x, τ x⟩)
        (mfderiv IB (IB.prod IF) (fun b ↦ homeomorph F E ⟨b, τ b⟩) x v) = v := by
  rw [← mfderiv_comp_apply x (mdifferentiable_projContMDiffMap _) hτ,
    projContMDiffMap_comp_homeomorph_mk, mfderiv_id, ContinuousLinearMap.id_apply]

variable (n F E IB IF) in
/-- **Local sections of a fibre bundle.** Over an open neighbourhood of every point of the base
of a `C^n` fibre bundle with nonempty model fibre, there is a map into the charted total space
that is `C^n` there and is a section of the projection there. It is the inverse of a
trivialization at a constant fibre coordinate. -/
theorem exists_contMDiffOn_section [ContMDiffFiberBundle n F E IB IF] [Nonempty F] (x : B) :
    ∃ U : Set B, IsOpen U ∧ x ∈ U ∧ ∃ s : B → ManifoldTotalSpace F E,
      ContMDiffOn IB (IB.prod IF) n s U ∧ ∀ y ∈ U, projContMDiffMap n F E IB IF (s y) = y := by
  set e := trivializationAt F E x
  let v : F := Classical.arbitrary F
  refine ⟨e.baseSet, e.open_baseSet, mem_baseSet_trivializationAt F E x,
    fun b ↦ homeomorph F E (e.toOpenPartialHomeomorph.symm (b, v)), ?_, fun y hy ↦ ?_⟩
  · exact (contMDiffOn_trivialization_symm e).comp (contMDiffOn_id.prodMk contMDiffOn_const)
      fun b hb ↦ e.mem_target.2 hb
  · simp only [coe_projContMDiffMap, Homeomorph.symm_apply_apply]
    exact e.proj_symm_apply' hy

end AnyField

/-! ### Forms semibasic for the projection -/

section Semibasic

variable {B F : Type*} {E : B → Type*}
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace ℝ EF] {HF : Type*}
  [TopologicalSpace HF] {IF : ModelWithCorners ℝ EF HF} [TopologicalSpace F] [ChartedSpace HF F]
  [FiberBundle F E] {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] {k : ℕ}

/-- Whether a form on the charted total space is semibasic for the projection
`projContMDiffMap n` does not depend on the smoothness index `n`. -/
theorem isSemibasic_projContMDiffMap_iff {n m : ℕ∞ω}
    {α : RoughForm (IB.prod IF) (ManifoldTotalSpace F E) V k} :
    RoughForm.IsSemibasic IB (projContMDiffMap n F E IB IF) α ↔
      RoughForm.IsSemibasic IB (projContMDiffMap m F E IB IF) α := by
  rw [coe_projContMDiffMap, coe_projContMDiffMap]

end Semibasic

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
theorem mpullback_mpullback_proj_apply {n : ℕ∞ω} (a : RoughForm IB B G k) {τ : ∀ b, E b} {x : B}
    (hτ : MDifferentiableAt IB (IB.prod IF) (fun b ↦ homeomorph F E ⟨b, τ b⟩) x) :
    TauCeti.mpullback IB (IB.prod IF) (fun b ↦ homeomorph F E ⟨b, τ b⟩)
        (TauCeti.mpullback (IB.prod IF) IB (projContMDiffMap n F E IB IF) a) x = a x := by
  rw [← mpullback_comp_at hτ (mdifferentiable_projContMDiffMap _),
    projContMDiffMap_comp_homeomorph_mk, mpullback_id]

/-- The pull-back of `α + π^* a` along a section `τ` of a fibre bundle, differentiable at `x` as a
map into the charted total space, is `τ^* α + a` at `x`. -/
theorem mpullback_add_mpullback_proj_apply
    (α : SmoothForm (IB.prod IF) (ManifoldTotalSpace F E) G k) (a : SmoothForm IB B G k)
    {τ : ∀ b, E b} {x : B}
    (hτ : MDifferentiableAt IB (IB.prod IF) (fun b ↦ homeomorph F E ⟨b, τ b⟩) x) :
    TauCeti.mpullback IB (IB.prod IF) (fun b ↦ homeomorph F E ⟨b, τ b⟩)
        (α + SmoothForm.mpullback (projContMDiffMap ∞ F E IB IF)
          (projContMDiffMap ∞ F E IB IF).contMDiff a).val x =
      TauCeti.mpullback IB (IB.prod IF) (fun b ↦ homeomorph F E ⟨b, τ b⟩) α.val x + a.val x := by
  rw [Submodule.coe_add, SmoothForm.coe_mpullback, mpullback_add, Pi.add_apply,
    mpullback_mpullback_proj_apply a.val hτ]

end Pullback

/-- The charted total space of a fibre bundle with compact model fibre over a compact base is
compact: it carries the topology of `Bundle.TotalSpace F E`, which is compact by
`FiberBundle.compactSpace_totalSpace`. -/
instance compactSpace {B F : Type*} {E : B → Type*} [TopologicalSpace B] [TopologicalSpace F]
    [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
    [CompactSpace B] [CompactSpace F] : CompactSpace (ManifoldTotalSpace F E) :=
  (homeomorph F E).compactSpace

/-- The charted total space of a fibre bundle with Hausdorff base and Hausdorff model fibre is
Hausdorff: it carries the topology of `Bundle.TotalSpace F E`, which is Hausdorff by
`TauCeti.FiberBundle.t2Space_totalSpace`. -/
instance t2Space {B F : Type*} {E : B → Type*} [TopologicalSpace B] [TopologicalSpace F]
    [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
    [T2Space B] [T2Space F] : T2Space (ManifoldTotalSpace F E) :=
  (homeomorph F E).t2Space

end TauCeti.ManifoldTotalSpace

/-! ### The fibre coordinate of a trivialization -/

namespace Bundle.Trivialization

section ManifoldSnd

variable {B F : Type*} {E : B → Type*} [TopologicalSpace B] [TopologicalSpace F]
  [TopologicalSpace (TotalSpace F E)] (e : Trivialization F (π F E))

/-- The fibre coordinate of a trivialization `e` of a fibre bundle with fibre `F`, as a map on
the charted total space `TauCeti.ManifoldTotalSpace F E`: the second component of `e`. -/
def manifoldSnd (x : TauCeti.ManifoldTotalSpace F E) : F :=
  (e ((TauCeti.ManifoldTotalSpace.homeomorph F E).symm x)).2

theorem manifoldSnd_def :
    e.manifoldSnd = fun x ↦ (e ((TauCeti.ManifoldTotalSpace.homeomorph F E).symm x)).2 :=
  (rfl)

theorem manifoldSnd_apply (x : TauCeti.ManifoldTotalSpace F E) :
    e.manifoldSnd x = (e ((TauCeti.ManifoldTotalSpace.homeomorph F E).symm x)).2 :=
  (rfl)

@[simp]
theorem manifoldSnd_homeomorph (p : TotalSpace F E) :
    e.manifoldSnd (TauCeti.ManifoldTotalSpace.homeomorph F E p) = (e p).2 := by
  rw [manifoldSnd_apply, Homeomorph.symm_apply_apply]

end ManifoldSnd

section Smooth

variable {n : ℕ∞ω} {𝕜 B F : Type*} {E : B → Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace 𝕜 EF] {HF : Type*}
  [TopologicalSpace HF] {IF : ModelWithCorners 𝕜 EF HF} [TopologicalSpace F] [ChartedSpace HF F]
  [FiberBundle F E] [TauCeti.ContMDiffFiberBundle n F E IB IF]

/-- The fibre coordinate of a trivialization `e` in the atlas of a `C^n` fibre bundle is `C^n`
over the base set of `e`. -/
theorem contMDiffOn_manifoldSnd (e : Trivialization F (π F E)) [MemTrivializationAtlas e] :
    ContMDiffOn (IB.prod IF) IF n e.manifoldSnd
      ((fun x ↦ ((TauCeti.ManifoldTotalSpace.homeomorph F E).symm x).proj) ⁻¹' e.baseSet) :=
  TauCeti.ManifoldTotalSpace.contMDiffOn_trivialization_snd_comp e contMDiffOn_id fun _ hx ↦ hx

end Smooth

end Bundle.Trivialization

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
    ContMDiffAt (IB.prod IG) IG n (trivializationOfSection σ hU hσ).manifoldSnd x :=
  (contMDiff_snd.comp_contMDiffOn (contMDiffOn_trivializationOfSection hσ')).contMDiffAt
    ((hU.preimage (ManifoldTotalSpace.contMDiff_proj n G P IB IG).continuous).mem_nhds hx)

end TauCeti.PrincipalBundle

end
