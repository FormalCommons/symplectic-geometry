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

## Main results

* `SymplecticGeometry.IsSmoothFamily.contMDiff_pathIntegral`: line integrals along a smooth curve.
* `SymplecticGeometry.IsSmoothFamily.contMDiff_pathClassIntegral`: integrals over a path class.
* `SymplecticGeometry.IsSmoothFamily.contMDiff_homologyPeriodHom`: periods on a class of
  `H₁(M; ℤ)`.
* `TauCeti.homologyPeriodHom_sub`: the periods of a difference of closed one-forms are the
  differences of their periods.
* `TauCeti.homologyPeriodHom_mpullback_eq_of_homotopic`: homotopic maps pull a closed one-form
  back to forms with the same periods.

## References

* M. Farber, *Topology of Closed One-Forms*, Section 1.1 (the homomorphism of periods
  `H₁(M; ℤ) → ℝ`).
-/

public section

open TauCeti TauCeti.HurewiczOne CategoryTheory TauCeti.TopCat
open scoped Simplicial
open scoped Manifold ContDiff

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

end IsSmoothFamily

end SymplecticGeometry

end
