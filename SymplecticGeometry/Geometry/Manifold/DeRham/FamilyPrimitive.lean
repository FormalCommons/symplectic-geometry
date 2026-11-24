/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.Poincare
public import TauCeti.Geometry.Manifold.DeRham.Basic
import SymplecticGeometry.Geometry.Manifold.ContMDiff.Opens
import TauCeti.Geometry.Manifold.DifferentialForm.ParametricPrimitive
import TauCeti.Geometry.Manifold.Topology
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Opens
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Prod

/-!
# Smooth primitives of smooth families of one-forms

Let `α_t`, `t ∈ N`, be a smooth family of one-forms on a manifold `M` over a parameter manifold
`N` (`SymplecticGeometry.IsSmoothFamily`). If every `α_t` is exact, then the primitives can be
chosen to depend smoothly on `t`: there is a smooth `f : N × M → ℝ` with `d (f (t, ·)) = α_t` for
every `t`. Neither compactness of `M` nor finite dimension is needed.

The file has two results.

* *Smoothly contractible manifolds.* Let `M` be smoothly contractible, through
  `G : M × [0, 1] → M` with `G (·, 0) = c` and `G (·, 1) = id`. By the parametric Poincaré lemma
  `SymplecticGeometry.IsSmoothlyContractible.exists_isSmoothFamily_mextDerivₗ_eq`, the
  primitives `h (G^* α_t)`, the homotopy operator after pullback along `G`, form a smooth
  family of `0`-forms over `N`, so they are the slices `f (t, ·)` of a smooth function `f` on
  `N × M`, explicitly `f (t, x) = ∫₀¹ α_t (G (x, s)) (∂ₛ G (x, s)) ds`. Here the forms need only
  be closed.
* *Exact forms on any manifold.* Choose primitives `g_t` of the `α_t` and a point `r i` in each
  connected component `i`, and let `f (t, x) = g_t x - g_t (r i)` for `x` in the component `i`.
  Manifolds are locally path-connected, so the components are open. On the component `i`, Tau Ceti's
  `TauCeti.exists_contMDiff_mvfderiv_eq_of_forall_exists`, applied to the family restricted to
  the component and pulled back to `component × N` by the swap of the factors, gives a jointly
  smooth family of primitives vanishing at `r i`. Two primitives of the same form on a connected
  set differ by a constant, so this family is `f` there, and `f` is jointly smooth.

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
  · exact Ω.contMDiff_apply_zero
  have hslice : RoughForm.ofFunction I (fun x ↦ Ω.val (t, x) 0) = (β t).val := by
    rw [← hΩ t, SmoothForm.coe_mpullback]
    conv_rhs => rw [RoughForm.eq_ofFunction Ω.val, mpullback_ofFunction]
    -- Both sides are the `0`-form of `x ↦ Ω (t, x)`, written with and without `∘`.
    rfl
  rw [hslice, ← mextDerivₗ_apply, hdβ t]

/-- On a preconnected open subset `U` of `M`, the primitives `g_t` of a smooth family of one-forms,
normalized to vanish at a point `x₀` of `U`, form a jointly smooth function on `N × U`. This is
Tau Ceti's `TauCeti.exists_contMDiff_mvfderiv_eq_of_forall_exists`, applied to the family
restricted to `U`, with the factors turned around. -/
private theorem exists_contMDiff_eq_sub_of_preconnectedSpace {α : N → SmoothForm I M ℝ 1}
    (hα : IsSmoothFamily K α) {g : N → M → ℝ} (hg : ∀ t, ContMDiff I 𝓘(ℝ) ∞ (g t))
    (hdg : ∀ t, mextDeriv (RoughForm.ofFunction I (g t)) = (α t : RoughForm I M ℝ 1))
    (U : Opens M) [PreconnectedSpace U] (x₀ : U) :
    ∃ P : N × U → ℝ, ContMDiff (K.prod I) 𝓘(ℝ) ∞ P ∧ ∀ t (y : U), P (t, y) = g t y - g t x₀ := by
  obtain ⟨Ω, hΩ⟩ := isSmoothFamily_def.1 (hα.mpullback Subtype.val contMDiff_subtypeVal)
  have hψ : ContMDiff (I.prod K) (K.prod I) ∞ fun q : U × N ↦ (q.2, q.1) :=
    contMDiff_snd.prodMk contMDiff_fst
  have hgU (t : N) : ContMDiff I 𝓘(ℝ) ∞ fun z : U ↦ g t z := (hg t).comp contMDiff_subtypeVal
  -- The slices of the pullback `B` of `Ω` to `U × N` are the differentials of the `g_t` on `U`.
  have hB (t : N) (z : U) (v : E) :
      mvfderiv I (fun z : U ↦ g t z) z v =
        (SmoothForm.mpullback _ hψ Ω).val (z, t) ![(v, (0 : EN))] := by
    have hd : mextDeriv (RoughForm.ofFunction I fun z : U ↦ g t z) =
        (SmoothForm.mpullback _ contMDiff_subtypeVal (α t)).val := by
      rw [SmoothForm.coe_mpullback, ← hdg t, mpullback_mextDeriv_ofFunction
        mdifferentiable_subtypeVal ((hg t).mdifferentiable (by simp))]
      -- Both sides are the `0`-form of `z ↦ g t z`, written with and without `∘`.
      rfl
    have h1 : mvfderiv I (fun z : U ↦ g t z) z v =
        mextDeriv (RoughForm.ofFunction I fun z : U ↦ g t z) z ![v] :=
      ((mextDeriv_ofFunction_apply _ z v).trans (mvfderiv_apply_eq_mfderiv_apply ..).symm).symm
    rw [h1, hd, ← hΩ t, SmoothForm.mpullback_apply, SmoothForm.mpullback_apply]
    congr 1
    funext i
    rw [Subsingleton.elim i 0]
    exact ((hψ.mdifferentiable (by simp) (z, t)).mfderiv_curry_left_apply v).symm
  obtain ⟨F, hF, hF0, hFd⟩ := exists_contMDiff_mvfderiv_eq_of_forall_exists (r := ⊤)
    (SmoothForm.mpullback _ hψ Ω).isSmoothForm
    (fun t ↦ ⟨_, (hgU t).mdifferentiable (by simp), hB t⟩) x₀
  refine ⟨fun p ↦ F (p.2, p.1), hF.comp (contMDiff_snd.prodMk contMDiff_fst), fun t y ↦ ?_⟩
  have hFt : ContMDiff I 𝓘(ℝ) ∞ fun z : U ↦ F (z, t) := hF.comp (contMDiff_id.prodMk
    contMDiff_const)
  -- Two primitives of the same form on the preconnected `U` differ by a constant.
  have hd : mextDeriv (RoughForm.ofFunction I fun z : U ↦ F (z, t)) =
      mextDeriv (RoughForm.ofFunction I fun z : U ↦ g t z) := by
    funext z
    rw [mextDeriv_ofFunction, mextDeriv_ofFunction]
    congr 1
    ext v
    exact (hFd t z v).trans (hB t z v).symm
  have hc := (isLocallyConstant_sub_of_mextDeriv_ofFunction_eq (hFt.mdifferentiable (by simp))
    ((hgU t).mdifferentiable (by simp)) hd).apply_eq_of_preconnectedSpace y x₀
  simp only [Pi.sub_apply, hF0, zero_sub] at hc
  linarith

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
  -- Every connected component is open, as manifolds are locally path-connected.
  have : LocallyPathConnectedSpace M := I.locallyPathConnectedSpace_of_chartedSpace M
  have hCo (x : M) : IsOpen (connectedComponent x) := isOpen_connectedComponent
  let C (x : M) : Opens M := ⟨connectedComponent x, hCo x⟩
  have hmkC (x : M) (y : M) (hy : y ∈ C x) : ConnectedComponents.mk y = ConnectedComponents.mk x :=
    ConnectedComponents.coe_eq_coe'.2 hy
  have hxC (x : M) : x ∈ C x := mem_connectedComponent
  have (x : M) : PreconnectedSpace (C x) :=
    Subtype.preconnectedSpace isPreconnected_connectedComponent
  choose P hP hPg using fun x ↦
    exists_contMDiff_eq_sub_of_preconnectedSpace hα hg hdg (C x) ⟨x, hxC x⟩
  refine ⟨f, fun p ↦ ?_, fun t ↦ funext fun x ↦ ?_⟩
  · -- On `N × C x`, for `x` the base point of the component of `p.2`, `f` is `P x`.
    set x := r (ConnectedComponents.mk p.2)
    have hpx : p.2 ∈ C x := ConnectedComponents.coe_eq_coe'.1 (hr _).symm
    have hW : ContMDiffOn (K.prod I) 𝓘(ℝ) ∞ f (univ ×ˢ C x) :=
      ContMDiff.contMDiffOn_prod_opens_of_eq (hP x) fun t y hy ↦ by
        simp only [f, hPg, hmkC x y hy, x, hr]
    exact hW.contMDiffAt ((isOpen_univ.prod (C x).isOpen).mem_nhds ⟨mem_univ _, hpx⟩)
  · -- Near `x`, `f (t, ·)` is `g_t` plus a constant.
    rw [← hdg t]
    refine mextDeriv_ofFunction_eq_of_eventuallyEq_add_const
      (c := -g t (r (ConnectedComponents.mk x))) ?_
    filter_upwards [(C x).isOpen.mem_nhds (hxC x)] with y hy
    simp only [f, hmkC x y hy]
    ring

end SymplecticGeometry

end
