/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
public import SymplecticGeometry.Geometry.Manifold.DeRham.FamilyPrimitive
public import TauCeti.Geometry.Manifold.DeRham.HomologyPeriod
public import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance
public import SymplecticGeometry.AlgebraicTopology.Singular.ChainsDesc
import TauCeti.Geometry.Manifold.SmoothApprox.Basic

/-!
# Periods of smooth families of closed one-forms

Let `α_t`, `t ∈ N`, be a smooth family of closed one-forms on a manifold `M`
(`SymplecticGeometry.IsSmoothFamily`). Its periods depend smoothly on the parameter: along a
smooth curve, along a path class, and on a class of the first singular homology group
`H₁(M; ℤ)` (`TauCeti.homologyPeriodHom`).

Along a smooth curve `c : ℝ → M`, the forms `c^* α_t` are a smooth family of one-forms on `ℝ`,
closed since `ℝ` has dimension one. As `ℝ` is smoothly contractible, they have a jointly smooth
family of primitives `f` (the parametric Poincaré lemma of
`SymplecticGeometry.Geometry.Manifold.DeRham.FamilyPrimitive`), and
the line integral from `a` to `b` is `f (t, b) - f (t, a)`. No integral is differentiated
by hand. On a Hausdorff boundaryless manifold every path is homotopic, relative to its
endpoints, to one with a smooth extension to `ℝ` (Tau Ceti's
`Path.exists_homotopic_contMDiff_extend`), which gives the path classes. A class of `H₁(M; ℤ)`
is represented by a cycle, a finite combination of singular simplices, and the period of the
class is the same combination of the periods along the simplices.

The periods also commute with integration in the parameter. If a closed form `β` is, pointwise,
the time integral `∫ₐᵇ α_{u t} dt` along a continuous path `u` of parameters, then each period
of `β` is the time integral of the periods of the `α_{u t}`. Along a smooth curve this is
Fubini's theorem (`intervalIntegral_intervalIntegral_swap`) for the integrand
`(s, t) ↦ (c^* α_{u t})_s(1)`, continuous on the plane, once evaluation on the velocity has been
taken inside the time integral; that needs the continuity of `t ↦ α_t x`, which is smooth
(`SymplecticGeometry.IsSmoothFamily.contMDiff_val_apply`). The path classes and the homology
classes then follow as before, the periods along the simplices being continuous in the time.

## Main results

* `SymplecticGeometry.IsSmoothFamily.contMDiff_pathIntegral`: line integrals along a smooth curve.
* `SymplecticGeometry.IsSmoothFamily.contMDiff_pathClassIntegral`: integrals over a path class.
* `SymplecticGeometry.IsSmoothFamily.contMDiff_homologyPeriodHom`: periods on a class of
  `H₁(M; ℤ)`.
* `SymplecticGeometry.IsSmoothFamily.pathIntegral_eq_intervalIntegral`,
  `SymplecticGeometry.IsSmoothFamily.pathClassIntegral_eq_intervalIntegral`,
  `SymplecticGeometry.IsSmoothFamily.homologyPeriodHom_eq_intervalIntegral`: line integrals,
  integrals over path classes, and periods on `H₁(M; ℤ)` of a time integral of the family are the
  time integrals of those of its forms.
* `TauCeti.homologyPeriodHom_sub`: the periods of a difference of closed one-forms are the
  differences of their periods.
* `TauCeti.homologyPeriodHom_mpullback_eq_of_homotopic`: homotopic maps pull a closed one-form
  back to forms with the same periods.

## References

* M. Farber, *Topology of Closed One-Forms*, Section 1.1 (the homomorphism of periods
  `H₁(M; ℤ) → ℝ`).
-/

public section

open TauCeti TauCeti.HurewiczOne CategoryTheory TauCeti.TopCat MeasureTheory Set
open scoped Simplicial
open scoped Manifold ContDiff Interval

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M]
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The periods on `H₁(M; ℤ)` of the difference of two closed `C¹` one-forms are the differences
of their periods. -/
theorem homologyPeriodHom_sub {φ ψ : RoughForm I M F 1} (hφ : IsSmoothForm I 1 φ)
    (hφc : mextDeriv φ = 0) (hψ : IsSmoothForm I 1 ψ) (hψc : mextDeriv ψ = 0) :
    homologyPeriodHom (φ - ψ) = homologyPeriodHom φ - homologyPeriodHom ψ := by
  rw [sub_eq_add_neg, homologyPeriodHom_add hφ hφc hψ.neg (by rw [mextDeriv_neg, hψc, neg_zero]),
    ← neg_one_smul ℝ ψ, homologyPeriodHom_smul, neg_one_smul, sub_eq_add_neg]

/-- **Homotopic maps pull a closed one-form back to forms with the same periods.** If the `C²`
maps `f, g : P → M` are homotopic, then for every closed `C¹` one-form `θ` on `M` the pullbacks
`f^* θ` and `g^* θ` have the same periods on `H₁(P; ℤ)`. -/
theorem homologyPeriodHom_mpullback_eq_of_homotopic {E' H' : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [TopologicalSpace H']
    {J : ModelWithCorners ℝ E' H'} {P : Type} [TopologicalSpace P] [ChartedSpace H' P]
    [IsManifold J ∞ P] [T2Space P] {f g : P → M} (hf : ContMDiff J I 2 f)
    (hg : ContMDiff J I 2 g)
    (hfg : ContinuousMap.Homotopic ⟨f, hf.continuous⟩ ⟨g, hg.continuous⟩)
    {θ : RoughForm I M F 1} (hθ : IsSmoothForm I 1 θ) (hcl : mextDeriv θ = 0) :
    homologyPeriodHom (mpullback J I f θ) = homologyPeriodHom (mpullback J I g θ) := by
  ext c
  rw [← homologyPeriodHom_singularHomologyMap hf hθ hcl,
    ← homologyPeriodHom_singularHomologyMap hg hθ hcl,
    ContinuousMap.singularHomologyMap_eq_of_homotopic ℤ 1 hfg]

end TauCeti

namespace SymplecticGeometry

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  {EN HN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  {K : ModelWithCorners ℝ EN HN} {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]
  [IsManifold K ∞ N] {α : N → SmoothForm I M ℝ 1}

namespace IsSmoothFamily

/-- **Line integrals of a smooth family of one-forms along a smooth curve depend smoothly on the
parameter.** -/
theorem contMDiff_pathIntegral (hα : IsSmoothFamily K α) {c : ℝ → M}
    (hc : ContMDiff 𝓘(ℝ) I ∞ c) (a b : ℝ) :
    ContMDiff K 𝓘(ℝ) ∞ fun t ↦ pathIntegral (α t : RoughForm I M ℝ 1) c a b := by
  -- The pullbacks `c^* α_t` have a jointly smooth family of primitives `f` on `ℝ`.
  obtain ⟨f, hf, hdf⟩ :=
    (isSmoothlyContractible_self ℝ).exists_contMDiff_mextDeriv_eq_of_forall_mem_closedForms
      (hα.mpullback c hc) fun _ ↦
        mem_closedForms_of_finrank_le (I := 𝓘(ℝ, ℝ)) (by simp) _
  have key (t : N) : pathIntegral (α t : RoughForm I M ℝ 1) c a b = f (t, b) - f (t, a) := by
    have hfc : ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ fun x ↦ f (t, x) :=
      hf.comp (contMDiff_const.prodMk contMDiff_id)
    rw [← Function.comp_id c, ← pathIntegral_mpullback _
      (fun s _ ↦ hc.mdifferentiableAt (by simp)) (fun s _ ↦ mdifferentiableAt_id),
      ← SmoothForm.coe_mpullback c hc, ← hdf t,
      pathIntegral_mextDeriv_ofFunction (hfc.of_le (by simp)) contMDiff_id]
    rfl
  simp_rw [key]
  exact (hf.comp (contMDiff_id.prodMk contMDiff_const)).sub
    (hf.comp (contMDiff_id.prodMk contMDiff_const))

/-- **Line integrals of a time integral of a smooth family of one-forms.** If the form `β` is,
pointwise, the integral `∫ₐᵇ α_{u t} dt` of a smooth family of one-forms along a continuous path
`u` of parameters, then the line integral of `β` along a smooth curve is the integral over
`t ∈ [a, b]` of the line integrals of the `α_{u t}`. -/
theorem pathIntegral_eq_intervalIntegral {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] {α : N → SmoothForm I M F 1} (hα : IsSmoothFamily K α) {u : ℝ → N}
    (hu : Continuous u) {a b : ℝ} {β : RoughForm I M F 1}
    (h : ∀ x, β x = intervalIntegral (E := E [⋀^Fin 1]→L[ℝ] F)
      (fun t ↦ (α (u t) : RoughForm I M F 1) x) a b volume)
    {c : ℝ → M} (hc : ContMDiff 𝓘(ℝ) I ∞ c) (a' b' : ℝ) :
    pathIntegral β c a' b' = ∫ t in a..b, pathIntegral (α (u t) : RoughForm I M F 1) c a' b' := by
  -- The pullbacks of the forms of the family to the parameter line, on the unit vector.
  set G : ℝ → ℝ → F := fun s t ↦ mpullback (F := F) 𝓘(ℝ, ℝ) I c (α (u t)).val s fun _ ↦ 1
  have hG : Continuous (Function.uncurry G) := by
    simp only [G, ← SmoothForm.coe_mpullback c hc]
    exact (hα.mpullback c hc).continuous_apply_one.comp (f := fun p : ℝ × ℝ ↦ (u p.2, p.1))
      ((hu.comp continuous_snd).prodMk continuous_fst)
  have hβG (s : ℝ) : mpullback 𝓘(ℝ, ℝ) I c β s (fun _ ↦ 1) = ∫ t in a..b, G s t := by
    simp only [G, mpullback_apply, h]
    -- Evaluation on the velocity is a continuous linear map, so it commutes with the integral.
    exact (ContinuousLinearMap.intervalIntegral_comp_comm
      (ContinuousAlternatingMap.apply ℝ E F fun _ : Fin 1 ↦ mfderiv 𝓘(ℝ, ℝ) I c s 1)
      (((hα.contMDiff_val_apply (c s)).continuous.comp hu).intervalIntegrable a b)).symm
  -- `G` is continuous, so Fubini applies on the compact rectangle.
  have hint : IntegrableOn (Function.uncurry G) (Ι a' b' ×ˢ Ι a b) :=
    (hG.continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)).mono_set
      (prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)
  simp_rw [pathIntegral_eq_integral_mpullback, hβG]
  exact intervalIntegral_intervalIntegral_swap hint

variable [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M]

/-- **Integrals of a smooth family of closed one-forms over a path class depend smoothly on the
parameter**, on a Hausdorff boundaryless manifold. -/
theorem contMDiff_pathClassIntegral (hα : IsSmoothFamily K α)
    (hcl : ∀ t, α t ∈ closedForms I M 1) {x y : M} (q : Path.Homotopic.Quotient x y) :
    ContMDiff K 𝓘(ℝ) ∞ fun t ↦ pathClassIntegral (α t : RoughForm I M ℝ 1) q := by
  induction q using Path.Homotopic.Quotient.ind with | mk γ =>
  -- Replace `γ` by a homotopic path with a smooth extension to `ℝ`.
  obtain ⟨γ', hγγ', hγ'⟩ := γ.exists_homotopic_contMDiff_extend (J := I) ⊤
  have key (t : N) : pathClassIntegral (α t : RoughForm I M ℝ 1) (.mk γ) =
      pathIntegral (α t : RoughForm I M ℝ 1) γ'.extend 0 1 := by
    rw [Path.Homotopic.Quotient.eq.2 hγγ']
    exact pathClassIntegral_mk_eq_pathIntegral ((α t).isSmoothForm.of_le (by simp))
      ((mem_closedForms I _).mp (hcl t)) (hγ'.of_le (by simp))
      fun s ↦ (γ'.extend_extends' s).symm
  simp_rw [key]
  exact hα.contMDiff_pathIntegral hγ' 0 1

/-- **Integrals over a path class of a time integral of closed one-forms.** If the closed `C¹`
form `β` is, pointwise, the integral `∫ₐᵇ α_{u t} dt` of a smooth family of closed one-forms along
a continuous path `u` of parameters, then the integral of `β` over a path class is the integral
over `t ∈ [a, b]` of the integrals of the `α_{u t}` over it, on a Hausdorff boundaryless manifold.
-/
theorem pathClassIntegral_eq_intervalIntegral (hα : IsSmoothFamily K α)
    (hcl : ∀ t, α t ∈ closedForms I M 1) {u : ℝ → N} (hu : Continuous u) {a b : ℝ}
    {β : RoughForm I M ℝ 1} (hβ : IsSmoothForm I 1 β) (hβc : mextDeriv β = 0)
    (h : ∀ x, β x = intervalIntegral (E := E [⋀^Fin 1]→L[ℝ] ℝ)
      (fun t ↦ (α (u t) : RoughForm I M ℝ 1) x) a b volume)
    {x y : M} (q : Path.Homotopic.Quotient x y) :
    pathClassIntegral β q = ∫ t in a..b, pathClassIntegral (α (u t) : RoughForm I M ℝ 1) q := by
  induction q using Path.Homotopic.Quotient.ind with | mk γ =>
  -- Replace `γ` by a homotopic path with a smooth extension to `ℝ`.
  obtain ⟨γ', hγγ', hγ'⟩ := γ.exists_homotopic_contMDiff_extend (J := I) ⊤
  have hext (s : unitInterval) : γ' s = γ'.extend s := (γ'.extend_extends' s).symm
  rw [Path.Homotopic.Quotient.eq.2 hγγ',
    pathClassIntegral_mk_eq_pathIntegral hβ hβc (hγ'.of_le (by simp)) hext,
    hα.pathIntegral_eq_intervalIntegral hu h hγ']
  refine intervalIntegral.integral_congr fun t _ ↦ ?_
  exact (pathClassIntegral_mk_eq_pathIntegral ((α (u t)).isSmoothForm.of_le (by simp))
    ((mem_closedForms I _).mp (hcl (u t))) (hγ'.of_le (by simp)) hext).symm

/-- **The periods of a smooth family of closed one-forms on a class of `H₁(M; ℤ)` depend smoothly
on the parameter**, on a Hausdorff boundaryless manifold. -/
theorem contMDiff_homologyPeriodHom {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [T2Space M] {N : Type} [TopologicalSpace N] [ChartedSpace HN N]
    [IsManifold K ∞ N] {α : N → SmoothForm I M ℝ 1} (hα : IsSmoothFamily K α)
    (hcl : ∀ t, α t ∈ closedForms I M 1) (c : ((singularChains ℤ).obj (.of M)).homology 1) :
    ContMDiff K 𝓘(ℝ) ∞ fun t ↦ homologyPeriodHom (α t : RoughForm I M ℝ 1) c := by
  obtain ⟨z, rfl⟩ := (H₁AddEquivHomology ℤ (.of M)).surjective c
  obtain ⟨z, rfl⟩ := H₁.mk_surjective z
  simp_rw [homologyPeriodHom_H₁AddEquivHomology_mk]
  -- The periods along the simplices, as smooth functions of the parameter.
  let g : (TopCat.toSSet.obj (.of M)) _⦋1⦌ → C^∞⟮K, N; 𝓘(ℝ), ℝ⟯ := fun s ↦
    ⟨fun t ↦ pathClassIntegral (α t : RoughForm I M ℝ 1) (.mk (path₁ s)),
      hα.contMDiff_pathClassIntegral hcl _⟩
  have key (t : N) : (chainsDesc fun s ↦ pathClassIntegral (α t : RoughForm I M ℝ 1)
      (.mk (path₁ s))).toAddMonoidHom =
      (ContMDiffMap.evalRingHom t).toAddMonoidHom.comp (chainsDesc g).toAddMonoidHom :=
    singularChains_addMonoidHom_ext (RingEquiv.refl ℤ) fun s ↦ by
      simp only [LinearMap.toAddMonoidHom_coe, AddMonoidHom.coe_comp, Function.comp_apply,
        chainsDesc_simplexChain_one]
      rfl
  have hval (t : N) := DFunLike.congr_fun (key t) (z : ((singularChains ℤ).obj (.of M)).X 1)
  simp only [LinearMap.toAddMonoidHom_coe, AddMonoidHom.coe_comp, Function.comp_apply] at hval
  simp_rw [hval]
  exact (chainsDesc g (z : ((singularChains ℤ).obj (.of M)).X 1)).contMDiff

/-- **Periods of a time integral of closed one-forms.** If the closed `C¹` form `β` is, pointwise,
the integral `∫ₐᵇ α_{u t} dt` of a smooth family of closed one-forms along a continuous path `u`
of parameters, then the periods of `β` on `H₁(M; ℤ)` are the integrals over `t ∈ [a, b]` of the
periods of the `α_{u t}`, on a Hausdorff boundaryless manifold. -/
theorem homologyPeriodHom_eq_intervalIntegral {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [T2Space M] {α : N → SmoothForm I M ℝ 1} (hα : IsSmoothFamily K α)
    (hcl : ∀ t, α t ∈ closedForms I M 1) {u : ℝ → N} (hu : Continuous u) {a b : ℝ}
    {β : RoughForm I M ℝ 1} (hβ : IsSmoothForm I 1 β) (hβc : mextDeriv β = 0)
    (h : ∀ x, β x = intervalIntegral (E := E [⋀^Fin 1]→L[ℝ] ℝ)
      (fun t ↦ (α (u t) : RoughForm I M ℝ 1) x) a b volume)
    (c : ((singularChains ℤ).obj (.of M)).homology 1) :
    homologyPeriodHom β c = ∫ t in a..b, homologyPeriodHom (α (u t) : RoughForm I M ℝ 1) c := by
  obtain ⟨z, rfl⟩ := (H₁AddEquivHomology (.of M)).surjective c
  obtain ⟨z, rfl⟩ := H₁.mk_surjective z
  simp_rw [homologyPeriodHom_H₁AddEquivHomology_mk]
  -- The periods along the simplices, as continuous functions of the time.
  let g : (TopCat.toSSet.obj (.of M)) _⦋1⦌ → C(ℝ, ℝ) := fun s ↦
    ⟨fun t ↦ pathClassIntegral (α (u t) : RoughForm I M ℝ 1) (.mk (path₁ s)),
      (hα.contMDiff_pathClassIntegral hcl _).continuous.comp hu⟩
  -- The integral over `[a, b]` of continuous functions.
  let L : C(ℝ, ℝ) →+ ℝ :=
    { toFun f := ∫ t in a..b, f t
      map_zero' := by simp
      map_add' f₁ f₂ := intervalIntegral.integral_add (f₁.continuous.intervalIntegrable a b)
        (f₂.continuous.intervalIntegrable a b) }
  have hβg : (fun s ↦ pathClassIntegral β (.mk (path₁ s))) = fun s ↦ L (g s) :=
    funext fun s ↦ hα.pathClassIntegral_eq_intervalIntegral hcl hu hβ hβc h _
  rw [hβg, ← L.coe_toIntLinearMap, ← map_chainsDesc L.toIntLinearMap]
  exact intervalIntegral.integral_congr fun t _ ↦ map_chainsDesc
    ((Pi.evalAddMonoidHom (fun _ : ℝ ↦ ℝ) t).comp
      ContinuousMap.coeFnAddMonoidHom).toIntLinearMap g _

end IsSmoothFamily

end SymplecticGeometry

end
