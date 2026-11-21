/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DeRham.GoodCover.Basic
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.Basic
public import TauCeti.Geometry.Manifold.DeRham.Basic
import TauCeti.Geometry.Manifold.DeRham.Map
import TauCeti.Geometry.Manifold.DifferentialForm.HomotopyOperator
import TauCeti.Geometry.Manifold.MFDeriv.Constancy

/-!
# Smooth primitives of smooth families of one-forms

Let `α_t`, `t ∈ N`, be a smooth family of one-forms on a manifold `M` over a parameter manifold
`N` (`SymplecticGeometry.IsSmoothFamily`). If every `α_t` is exact, then the primitives can be
chosen to depend smoothly on `t`: there is a smooth `f : N × M → ℝ` with `d (f (t, ·)) = α_t` for
every `t`. Neither compactness of `M` nor finite dimension is needed.

The proof has two steps.

* *Local step.* On a smoothly contractible manifold, with contraction `G` from a point `c`
  (`G (·, 0) = c`, `G (·, 1) = id`), a smooth family of closed one-forms has the jointly smooth
  primitive `f (t, x) = ∫₀¹ α_t (G (x, s)) (∂ₛ G (x, s)) ds`. This is the homotopy operator of
  the cylinder `(N × M) × [0, 1]` (Tau Ceti's `TauCeti.homotopyOperator`) applied to the pullback
  of the form on `N × M` with slices `α_t` along `((t, x), s) ↦ (t, G (x, s))`. On each slice the
  homotopy formula gives `d (f (t, ·)) = α_t - c^* α_t = α_t`, since a closed form has
  `d (h φ) = ι₁^* φ - ι₀^* φ`; only the closedness of the slices is used.
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

## References

* [R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §4 (the
  homotopy operator and the Poincaré lemma).
* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §3.1
  (the Hamiltonian of an isotopy, a smooth family of primitives of its velocity forms).
-/

public section

open Set TopologicalSpace TauCeti
open scoped Manifold ContDiff Topology

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
  obtain ⟨c, G, hG, hG₀, hG₁⟩ := isSmoothlyContractible_def.1 hM
  obtain ⟨Ω, hΩ⟩ := isSmoothFamily_def.1 hα
  have : IsManifold (K.prod I) ((⊤ : ℕ∞) + 1 : WithTop ℕ∞) (N × M) :=
    IsManifold.of_le (n := ∞) (by simp)
  -- The contraction, acting on the second factor of `N × M`.
  let Γ : (N × M) × unitInterval → N × M := fun p ↦ (p.1.1, G (p.1.2, p.2))
  have hΓ : ContMDiff ((K.prod I).prod (𝓡∂ 1)) (K.prod I) ∞ Γ :=
    (contMDiff_fst.comp contMDiff_fst).prodMk
      (hG.comp ((contMDiff_snd.comp contMDiff_fst).prodMk contMDiff_snd))
  let β := SmoothForm.mpullback Γ hΓ Ω
  have hh : IsSmoothForm (K.prod I) (⊤ : ℕ∞) (homotopyOperator β.val) :=
    IsSmoothForm.homotopyOperator β.isSmoothForm
  refine ⟨fun p ↦ homotopyOperator β.val p 0, ?_, fun t ↦ ?_⟩
  · rw [RoughForm.eq_ofFunction (homotopyOperator β.val), isSmoothForm_ofFunction_iff] at hh
    exact hh
  have hι : ContMDiff I (K.prod I) ∞ (Prod.mk t : M → N × M) :=
    contMDiff_const.prodMk contMDiff_id
  have hιG : ContMDiff (I.prod (𝓡∂ 1)) ((K.prod I).prod (𝓡∂ 1)) ∞
      (Prod.map (Prod.mk t) id : M × unitInterval → (N × M) × unitInterval) :=
    hι.prodMap contMDiff_id
  -- The slice at `t` is the homotopy operator of `G^* α_t`, by naturality of the operator.
  have hslice : RoughForm.ofFunction I (fun x ↦ homotopyOperator β.val (t, x) 0) =
      homotopyOperator (SmoothForm.mpullback G hG (α t)).val := by
    rw [← hΩ t, SmoothForm.mpullback_mpullback_of_comp_eq hG hι hιG hΓ rfl Ω,
      SmoothForm.coe_mpullback _ hιG β, homotopyOperator_mpullback_prodMap_id_of_isSmoothForm
        (hι.mdifferentiable (by simp)) (β.isSmoothForm.of_le (by simp))]
    conv_rhs => rw [RoughForm.eq_ofFunction (homotopyOperator β.val), mpullback_ofFunction]
    -- Both sides are the `0`-form of `x ↦ h β (t, x)`, written with and without `∘`.
    rfl
  have hclosed : mextDeriv (SmoothForm.mpullback G hG (α t)).val = 0 := by
    have := SmoothForm.mextDerivₗ_mpullback G hG 1 (α t)
    rw [(mem_closedForms_iff_mextDerivₗ_eq_zero I (α t)).1 (hcl t), map_zero] at this
    simpa only [mextDerivₗ_apply, ZeroMemClass.coe_zero] using congrArg Subtype.val this
  have hend (s : unitInterval) : mpullback I (I.prod (𝓡∂ 1)) (fun y ↦ (y, s))
      (SmoothForm.mpullback G hG (α t)).val = mpullback I I (fun y ↦ G (y, s)) (α t).val := by
    rw [SmoothForm.coe_mpullback]
    exact (mpullback_comp ((contMDiff_id.prodMk contMDiff_const :
      ContMDiff I (I.prod (𝓡∂ 1)) 1 fun y : M ↦ (y, s)).mdifferentiable one_ne_zero)
        (hG.mdifferentiable (by simp)) _).symm
  -- The homotopy formula: `d (h (G^* α_t)) = α_t - c^* α_t`, and `c^* α_t = 0`.
  funext x
  rw [hslice, mextDeriv_homotopyOperator ((SmoothForm.mpullback G hG (α t)).isSmoothForm.of_le
    (by simp)) hclosed x, hend, hend]
  simp only [hG₀, hG₁]
  rw [show (fun y : M ↦ y) = id from rfl, mpullback_id]
  ext v
  rw [ContinuousAlternatingMap.sub_apply, mpullback_apply, mfderiv_const, sub_eq_self]
  exact ((α t).val c).map_coord_zero 0 rfl

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
  -- Near every point `x₀` there are a connected open set `U` and a jointly smooth `P` on `N × U`
  -- such that `f - P` depends only on the parameter on `N × U`.
  have hloc (x₀ : M) : ∃ U : Opens M, x₀ ∈ U ∧
      (∀ y : U, ConnectedComponents.mk (y : M) = ConnectedComponents.mk x₀) ∧
      ∃ P : N × U → ℝ, ContMDiff (K.prod I) 𝓘(ℝ) ∞ P ∧
        ∀ t (y y' : U), f (t, y) - P (t, y) = f (t, y') - P (t, y') := by
    obtain ⟨U, hx₀, hU⟩ := exists_mem_isSmoothlyContractible (I := I) x₀
    have := hU.connectedSpace
    obtain ⟨P, hP, hdP⟩ := hU.exists_contMDiff_mextDeriv_eq_of_forall_mem_closedForms
      (hα.mpullback Subtype.val contMDiff_subtypeVal) fun t ↦
        closedForms.coe_mpullback Subtype.val contMDiff_subtypeVal 1 ⟨α t, _⟩ ▸
          (closedForms.mpullback Subtype.val contMDiff_subtypeVal 1
            ⟨α t, exactForms_le_closedForms I 1 (hex t)⟩).property
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
        ((contMDiff_subtypeVal (n := 1)).mdifferentiable one_ne_zero)
        ((hg t).mdifferentiable (by simp))]
      -- Both sides are the `0`-form of `z ↦ g t z`, written with and without `∘`.
      rfl
    -- On the connected set `U`, the two primitives `g_t` and `P (t, ·)` differ by a constant.
    have hlc : IsLocallyConstant fun z : U ↦ g t z - P (t, z) :=
      ((hgU.sub hPU).mdifferentiable (by simp)).isLocallyConstant_of_mfderiv_eq_zero fun z ↦
        mvfderiv_eq_zero_iff.1 <| by
          have := congrFun hd z
          rw [mextDeriv_ofFunction, mextDeriv_ofFunction] at this
          rw [mvfderiv_fun_sub (hgU.mdifferentiableAt (by simp)) (hPU.mdifferentiableAt (by simp)),
            (ContinuousAlternatingMap.ofSubsingleton ℝ _ ℝ (0 : Fin 1)).injective this, sub_self]
    have hc := hlc.apply_eq_of_preconnectedSpace y y'
    simp only [f, hmk y y'] at hc ⊢
    linarith
  choose U hxU hmkU P hP hfP using hloc
  -- On `N × U x₀`, `f` is `P x₀` plus a function of the parameter.
  have hslice (x₀ y : M) (hy : y ∈ U x₀) (t : N) :
      f (t, y) = f (t, x₀) + (P x₀ (t, ⟨y, hy⟩) - P x₀ (t, ⟨x₀, hxU x₀⟩)) := by
    have := hfP x₀ t ⟨y, hy⟩ ⟨x₀, hxU x₀⟩
    linarith
  have hPs (x₀ : M) (y : U x₀) : ContMDiff K 𝓘(ℝ) ∞ fun t ↦ P x₀ (t, y) :=
    (hP x₀).comp (contMDiff_id.prodMk contMDiff_const)
  -- The points where `f` is smooth in the parameter form a clopen set containing the `r i`.
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
    have hrx : r (ConnectedComponents.mk x) ∈ connectedComponent x :=
      ConnectedComponents.coe_eq_coe'.1 (hr _)
    have hrS : r (ConnectedComponents.mk x) ∈ S := by
      have h0 : (fun t ↦ f (t, r (ConnectedComponents.mk x))) = fun _ ↦ 0 := by
        funext t
        simp only [f, hr, sub_self]
      simp only [S, mem_ofPred_eq, h0]
      exact contMDiff_const
    exact hSc.connectedComponent_subset hrS (connectedComponent_eq hrx ▸ mem_connectedComponent)
  refine ⟨f, fun p ↦ ?_, fun t ↦ funext fun x ↦ ?_⟩
  · -- Near `p`, `f` is `P p.2` plus a smooth function of the parameter.
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
  · -- Near `x`, `f (t, ·)` is `g_t` plus a constant.
    rw [← hdg t]
    refine mextDeriv_ofFunction_eq_of_eventuallyEq_add_const
      (c := -g t (r (ConnectedComponents.mk x))) ?_
    filter_upwards [(U x).isOpen.mem_nhds (hxU x)] with y hy
    simp only [f, hmkU x ⟨y, hy⟩]
    ring

end SymplecticGeometry

end
