/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.Poincare
public import TauCeti.Geometry.Manifold.DeRham.Basic
import SymplecticGeometry.Geometry.Manifold.DeRham.Map
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Opens

/-!
# Smooth primitives of smooth families of one-forms

Let `α_t`, `t ∈ N`, be a smooth family of one-forms on a manifold `M` over a parameter manifold
`N` (`SymplecticGeometry.IsSmoothFamily`). If every `α_t` is exact, then the primitives can be
chosen to depend smoothly on `t`: there is a smooth `f : N × M → ℝ` with `d (f (t, ·)) = α_t` for
every `t`. Neither compactness of `M` nor finite dimension is needed.

The proof has two steps.

* *Local step.* Let `M` be smoothly contractible, through `G : M × [0, 1] → M` with
  `G (·, 0) = c` and `G (·, 1) = id`. By the parametric Poincaré lemma
  `SymplecticGeometry.IsSmoothlyContractible.exists_isSmoothFamily_mextDerivₗ_eq`, the
  primitives `h (G^* α_t)`, the homotopy operator after pullback along `G`, form a smooth
  family of `0`-forms over `N`, so they are the slices `f (t, ·)` of a smooth function `f` on
  `N × M`, explicitly `f (t, x) = ∫₀¹ α_t (G (x, s)) (∂ₛ G (x, s)) ds`.
* *Gluing.* Choose primitives `g_t` of the `α_t` and a point `r i` in each connected component
  `i`, and let `f (t, x) = g_t x - g_t (r i)` for `x` in the component `i`. Every point has a
  smoothly contractible, hence connected, open neighbourhood `U`, and on `U` the difference of
  `f (t, ·)` and the local primitive `P (t, ·)` is constant. So the set of points `x` at which
  `t ↦ f (t, x)` is smooth is open and closed, and it contains the `r i`, where `f` vanishes:
  it is all of `M`, and then `f = P + (f - P) (·, x₀)` is jointly smooth near every point.

## Main results

In the namespace `SymplecticGeometry`:

* `IsSmoothlyContractible.exists_contMDiff_mextDeriv_eq_of_forall_mem_closedForms`: on a smoothly
  contractible manifold, a smooth family of closed one-forms has a jointly smooth family of
  primitives (the parametric Poincaré lemma in degree one).
* `exists_contMDiff_mextDeriv_eq_of_forall_mem_exactForms`: on any manifold, a smooth family of
  exact one-forms has a jointly smooth family of primitives.

In the namespace `TauCeti`:

* `isLocallyConstant_sub_of_mextDeriv_ofFunction_eq`: two differentiable functions whose
  `0`-forms have the same exterior derivative differ by a locally constant function.

## References

* [R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §4 (the
  homotopy operator and the Poincaré lemma).
* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §3.1
  (the Hamiltonian of an isotopy, a smooth family of primitives of its velocity forms).
-/

public section

open Set TopologicalSpace TauCeti
open scoped Manifold ContDiff Topology

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Two differentiable functions whose `0`-forms have the same exterior derivative differ by a
locally constant function. The manifold may have boundary or corners. -/
theorem isLocallyConstant_sub_of_mextDeriv_ofFunction_eq [IsManifold I 1 M] {f g : M → F}
    (hf : MDifferentiable I 𝓘(ℝ, F) f) (hg : MDifferentiable I 𝓘(ℝ, F) g)
    (h : mextDeriv (RoughForm.ofFunction I f) = mextDeriv (RoughForm.ofFunction I g)) :
    IsLocallyConstant (f - g) :=
  (mextDeriv_ofFunction_eq_zero_iff (hf.sub hg)).1 <| add_eq_right.1 <| by
    rw [← mextDeriv_ofFunction_add (hf.sub hg) hg, sub_add_cancel, h]

end TauCeti

namespace SymplecticGeometry

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  {EN HN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  {K : ModelWithCorners ℝ EN HN} {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]
  [IsManifold K ∞ N]

/-- **The parametric Poincaré lemma in degree one.** On a smoothly contractible manifold `M`, a
smooth family `α_t`, `t ∈ N`, of closed one-forms has a jointly smooth family of primitives: there
is a smooth `f : N × M → ℝ` with `d (f (t, ·)) = α_t` for every `t`. -/
theorem IsSmoothlyContractible.exists_contMDiff_mextDeriv_eq_of_forall_mem_closedForms
    (hM : IsSmoothlyContractible I M) {α : N → SmoothForm I M ℝ 1} (hα : IsSmoothFamily K α)
    (hcl : ∀ t, α t ∈ closedForms I M 1) :
    ∃ f : N × M → ℝ, ContMDiff (K.prod I) 𝓘(ℝ) ∞ f ∧
      ∀ t, mextDeriv (RoughForm.ofFunction I fun x ↦ f (t, x)) = (α t : RoughForm I M ℝ 1) := by
  -- A smooth family `β_t` of primitives, as `0`-forms: the slices of `Ω`.
  obtain ⟨β, hβ, hdβ⟩ := hM.exists_isSmoothFamily_mextDerivₗ_eq hα
    fun t ↦ (mem_closedForms_iff_mextDerivₗ_eq_zero I _).1 (hcl t)
  obtain ⟨Ω, hΩ⟩ := isSmoothFamily_def.1 hβ
  refine ⟨fun p ↦ Ω.val p 0, ?_, fun t ↦ ?_⟩
  · have hΩs := Ω.isSmoothForm
    rw [RoughForm.eq_ofFunction Ω.val, isSmoothForm_ofFunction_iff] at hΩs
    exact hΩs
  have hslice : RoughForm.ofFunction I (fun x ↦ Ω.val (t, x) 0) = (β t).val := by
    rw [← hΩ t, SmoothForm.coe_mpullback]
    conv_rhs => rw [RoughForm.eq_ofFunction Ω.val, mpullback_ofFunction]
    -- Both sides are the `0`-form of `x ↦ Ω (t, x)`, written with and without `∘`.
    rfl
  rw [hslice, ← mextDerivₗ_apply, hdβ t]

/-- Near every point of `M`, a family `g_t` of primitives of a smooth family of closed one-forms
agrees, up to a function of the parameter, with a jointly smooth function `P` on `N × U`, where
`U` is an open neighbourhood of the point inside one connected component. -/
private theorem exists_contMDiff_sub_eq_of_mextDeriv_eq {α : N → SmoothForm I M ℝ 1}
    (hα : IsSmoothFamily K α) (hcl : ∀ t, α t ∈ closedForms I M 1) {g : N → M → ℝ}
    (hg : ∀ t, ContMDiff I 𝓘(ℝ) ∞ (g t))
    (hdg : ∀ t, mextDeriv (RoughForm.ofFunction I (g t)) = (α t : RoughForm I M ℝ 1)) (x₀ : M) :
    ∃ U : Opens M, x₀ ∈ U ∧
      (∀ y : U, ConnectedComponents.mk (y : M) = ConnectedComponents.mk x₀) ∧
      ∃ P : N × U → ℝ, ContMDiff (K.prod I) 𝓘(ℝ) ∞ P ∧
        ∀ t (y y' : U), g t y - P (t, y) = g t y' - P (t, y') := by
  obtain ⟨U, hx₀, hU⟩ := exists_mem_isSmoothlyContractible (I := I) x₀
  have := hU.connectedSpace
  obtain ⟨P, hP, hdP⟩ := hU.exists_contMDiff_mextDeriv_eq_of_forall_mem_closedForms
    (hα.mpullback Subtype.val contMDiff_subtypeVal) fun t ↦
      SmoothForm.mpullback_mem_closedForms Subtype.val contMDiff_subtypeVal (hcl t)
  have hmk (y y' : U) : ConnectedComponents.mk (y : M) = ConnectedComponents.mk (y' : M) :=
    ConnectedComponents.coe_eq_coe'.2 <|
      (isPreconnected_univ.image _ continuous_subtypeVal.continuousOn).subset_connectedComponent
        ⟨y', mem_univ _, rfl⟩ ⟨y, mem_univ _, rfl⟩
  refine ⟨U, hx₀, fun y ↦ hmk y ⟨x₀, hx₀⟩, P, hP, fun t y y' ↦ ?_⟩
  have hgU : ContMDiff I 𝓘(ℝ) ∞ fun z : U ↦ g t z := (hg t).comp contMDiff_subtypeVal
  have hPU : ContMDiff I 𝓘(ℝ) ∞ fun z : U ↦ P (t, z) :=
    hP.comp (contMDiff_const.prodMk contMDiff_id)
  have hd : mextDeriv (RoughForm.ofFunction I fun z : U ↦ g t z) =
      mextDeriv (RoughForm.ofFunction I fun z : U ↦ P (t, z)) := by
    rw [hdP t, SmoothForm.coe_mpullback, ← hdg t, mpullback_mextDeriv_ofFunction
      mdifferentiable_subtypeVal
      ((hg t).mdifferentiable (by simp))]
    -- Both sides are the `0`-form of `z ↦ g t z`, written with and without `∘`.
    rfl
  -- On the connected set `U`, the two primitives `g_t` and `P (t, ·)` differ by a constant.
  have hc := (isLocallyConstant_sub_of_mextDeriv_ofFunction_eq (hgU.mdifferentiable (by simp))
    (hPU.mdifferentiable (by simp)) hd).apply_eq_of_preconnectedSpace y y'
  simpa only [Pi.sub_apply] using hc

omit [IsManifold I ∞ M] [IsManifold K ∞ N] in
/-- A function `f` on `N × M` is smooth if every point has an open neighbourhood `U` on which `f`
is a smooth function on `N × U` plus a function of the parameter alone, and every connected
component of `M` has a point `r` at which `t ↦ f (t, r)` is smooth. -/
private theorem contMDiff_of_forall_sub_eq {f : N × M → ℝ} {U : M → Opens M}
    (hxU : ∀ x, x ∈ U x) {P : ∀ x, N × U x → ℝ} (hP : ∀ x, ContMDiff (K.prod I) 𝓘(ℝ) ∞ (P x))
    (hfP : ∀ x t (y y' : U x), f (t, y) - P x (t, y) = f (t, y') - P x (t, y'))
    (hr : ∀ x, ∃ r ∈ connectedComponent x, ContMDiff K 𝓘(ℝ) ∞ fun t ↦ f (t, r)) :
    ContMDiff (K.prod I) 𝓘(ℝ) ∞ f := by
  -- On `N × U x₀`, `f` is `P x₀` plus a function of the parameter.
  have hslice (x₀ y : M) (hy : y ∈ U x₀) (t : N) :
      f (t, y) = f (t, x₀) + (P x₀ (t, ⟨y, hy⟩) - P x₀ (t, ⟨x₀, hxU x₀⟩)) := by
    have := hfP x₀ t ⟨y, hy⟩ ⟨x₀, hxU x₀⟩
    linarith
  have hPs (x₀ : M) (y : U x₀) : ContMDiff K 𝓘(ℝ) ∞ fun t ↦ P x₀ (t, y) :=
    (hP x₀).comp (contMDiff_id.prodMk contMDiff_const)
  -- The points where `f` is smooth in the parameter form a clopen set meeting every component.
  let S : Set M := {x | ContMDiff K 𝓘(ℝ) ∞ fun t ↦ f (t, x)}
  have hS (x₀ y : M) (hy : y ∈ U x₀) : y ∈ S ↔ x₀ ∈ S := by
    simp only [S, mem_ofPred_eq, hslice x₀ y hy]
    refine ⟨fun h ↦ ?_, fun h ↦ h.add ((hPs x₀ _).sub (hPs x₀ _))⟩
    convert h.sub ((hPs x₀ ⟨y, hy⟩).sub (hPs x₀ ⟨x₀, hxU x₀⟩)) using 1
    funext t
    ring
  have hSc : IsClopen S :=
    ⟨⟨isOpen_iff_forall_mem_open.2 fun x₀ hx₀ ↦
        ⟨U x₀, fun y hy hyS ↦ hx₀ ((hS x₀ y hy).1 hyS), (U x₀).isOpen, hxU x₀⟩⟩,
      isOpen_iff_forall_mem_open.2 fun x₀ hx₀ ↦
        ⟨U x₀, fun y hy ↦ (hS x₀ y hy).2 hx₀, (U x₀).isOpen, hxU x₀⟩⟩
  have hSall (x : M) : x ∈ S := by
    obtain ⟨r, hrx, hrS⟩ := hr x
    exact hSc.connectedComponent_subset hrS (connectedComponent_eq hrx ▸ mem_connectedComponent)
  -- Near `p`, `f` is `P p.2` plus a smooth function of the parameter.
  intro p
  let W : Opens (N × M) := ⟨univ ×ˢ U p.2, isOpen_univ.prod (U p.2).isOpen⟩
  have hq : ContMDiff (K.prod I) (K.prod I) ∞
      fun w : W ↦ ((w : N × M).1, (⟨(w : N × M).2, w.property.2⟩ : U p.2)) :=
    (contMDiff_fst.comp contMDiff_subtypeVal).prodMk
      ((ContMDiff.subtypeVal_comp_iff (U p.2) _).1 (contMDiff_snd.comp contMDiff_subtypeVal))
  have hW : ContMDiff (K.prod I) 𝓘(ℝ) ∞ fun w : W ↦ f w := by
    refine (((hSall p.2).comp (contMDiff_fst.comp contMDiff_subtypeVal)).add
      (((hP p.2).comp hq).sub ((hPs p.2 ⟨p.2, hxU p.2⟩).comp
        (contMDiff_fst.comp contMDiff_subtypeVal)))).congr fun w ↦ ?_
    exact hslice p.2 (w : N × M).2 w.property.2 (w : N × M).1
  exact contMDiffAt_subtype_iff.1 (hW (⟨p, mem_univ _, hxU p.2⟩ : W))

/-- **Smooth primitives of a smooth family of exact one-forms.** On any manifold `M`, a smooth
family `α_t`, `t ∈ N`, of exact one-forms has a jointly smooth family of primitives: there is a
smooth `f : N × M → ℝ` with `d (f (t, ·)) = α_t` for every `t`. -/
theorem exists_contMDiff_mextDeriv_eq_of_forall_mem_exactForms {α : N → SmoothForm I M ℝ 1}
    (hα : IsSmoothFamily K α) (hex : ∀ t, α t ∈ exactForms I M 1) :
    ∃ f : N × M → ℝ, ContMDiff (K.prod I) 𝓘(ℝ) ∞ f ∧
      ∀ t, mextDeriv (RoughForm.ofFunction I fun x ↦ f (t, x)) = (α t : RoughForm I M ℝ 1) := by
  choose g hg hdg using fun t ↦ exists_contMDiff_mextDeriv_eq_of_mem_exactForms I (hex t)
  -- `f (t, ·)` is the primitive of `α_t` that vanishes at a chosen point `r i` of each
  -- connected component `i`.
  let r := Function.surjInv (ConnectedComponents.surjective_coe (α := M))
  have hr (i : ConnectedComponents M) : ConnectedComponents.mk (r i) = i :=
    Function.surjInv_eq _ i
  let f : N × M → ℝ := fun p ↦ g p.1 p.2 - g p.1 (r (ConnectedComponents.mk p.2))
  choose U hxU hmkU P hP hgP using
    exists_contMDiff_sub_eq_of_mextDeriv_eq hα (fun t ↦ exactForms_le_closedForms I 1 (hex t))
      hg hdg
  have hfP (x₀ : M) (t : N) (y y' : U x₀) : f (t, y) - P x₀ (t, y) = f (t, y') - P x₀ (t, y') := by
    have := hgP x₀ t y y'
    simp only [f, hmkU x₀ y, hmkU x₀ y']
    linarith
  refine ⟨f, contMDiff_of_forall_sub_eq hxU hP hfP fun x ↦
    ⟨r (ConnectedComponents.mk x), ConnectedComponents.coe_eq_coe'.1 (hr _), ?_⟩,
    fun t ↦ funext fun x ↦ ?_⟩
  · -- `f` vanishes at the base points.
    simp only [f, hr, sub_self]
    exact contMDiff_const
  · -- Near `x`, `f (t, ·)` is `g_t` plus a constant.
    rw [← hdg t]
    refine mextDeriv_ofFunction_eq_of_eventuallyEq_add_const
      (c := -g t (r (ConnectedComponents.mk x))) ?_
    filter_upwards [(U x).isOpen.mem_nhds (hxU x)] with y hy
    simp only [f, hmkU x ⟨y, hy⟩]
    ring

end SymplecticGeometry

end
