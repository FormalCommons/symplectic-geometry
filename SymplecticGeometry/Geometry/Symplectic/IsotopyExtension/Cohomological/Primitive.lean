/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothIsotopy.Basic
public import TauCeti.Geometry.Manifold.DeRham.HomologyPeriod
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.Basic
public import TauCeti.Topology.Homotopy.Extension.NDRPair
import SymplecticGeometry.AlgebraicTopology.Singular.NDRPair
import SymplecticGeometry.Geometry.Manifold.DeRham.HomologyPeriod
import SymplecticGeometry.Geometry.Manifold.DeRham.SmoothFamily.GoodCover
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.Map
import SymplecticGeometry.Geometry.Manifold.DeRham.Map
import SymplecticGeometry.Geometry.Manifold.DeRham.FamilyPrimitive
import SymplecticGeometry.Geometry.Manifold.ContMDiff.Dual

/-!
# Closed forms with prescribed periods, and primitives near a subset

This file collects the cohomological input of the symplectic isotopy extension theorem
(McDuff–Salamon, Theorem 3.3.2). Let `Q` be a subset of a manifold `M` and `U` an open set
containing it. The first cohomology of `Q` is read through singular homology: a class is an
additive map `H₁(Q; ℤ) → ℝ`, and a closed one-form on `U` or on `M` restricts to `Q` through its
periods (`TauCeti.homologyPeriodHom`) on the image of `H₁(Q; ℤ)`.

* `SymplecticGeometry.exists_closedForms_periods_eq`: if `M` is compact and every additive map
  `H₁(Q; ℤ) → ℝ` is the restriction of a de Rham class of `M`, then every smooth family `α_t` of
  closed one-forms on `U` has a smooth family `β_t` of closed one-forms on `M` with the same
  periods on `H₁(Q; ℤ)`. Since `H¹_dR(M)` is finite-dimensional, so is the space `W` of additive
  maps `H₁(Q; ℤ) → ℝ`. A linear right inverse of the restriction `H¹_dR(M) → W`, followed by a
  linear choice of closed representatives, sends the periods of `α_t` to `β_t`. The family is
  smooth because every linear functional on `W` is a finite combination of evaluations at
  classes of `H₁(Q; ℤ)`, and the periods of `α_t` on a fixed class are smooth in `t`
  (`SymplecticGeometry.IsSmoothFamily.contMDiff_homologyPeriodHom`).
* `TauCeti.NDRPair.exists_forall_exact`: if `Q` carries NDR data, there is an open `V` with
  `Q ⊆ V ⊆ U` on which every closed one-form on `U` whose periods vanish on `H₁(Q; ℤ)` is exact.
  Every class of `H₁(V; ℤ)` is carried into `U` by a class of `Q`
  (`TauCeti.NDRPair.exists_isOpen_range_singularHomologyMap_le`), and a closed one-form with
  vanishing periods is exact (`TauCeti.mem_exactForms_one_iff_homologyPeriodHom_eq_zero`).
* `TauCeti.SmoothIsotopy.homologyPeriodHom_mpullback_eq`: the slices of a smooth isotopy are
  homotopic to its start, so they pull a closed one-form back to forms with the same periods.
* `SymplecticGeometry.exists_contMDiff_primitive_of_periods`: for a smooth isotopy `φ_t` of `U`
  starting at the inclusion, and families `α_t` on `U`, `β_t` on `M` with the same periods on
  `H₁(Q; ℤ)`, the forms `α_t - φ_t^* β_t` restricted to such a `V` have a primitive that is
  jointly smooth on `[0, 1] × V`
  (`SymplecticGeometry.exists_contMDiff_mextDeriv_eq_of_forall_mem_exactForms`). With the
  velocity forms of a symplectic isotopy as `α_t`, this gives the Hamiltonians of the extension.

Neither of the last three results needs `M` to be compact.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §3.3
  (proof of Theorem 3.3.2).
* M. Farber, *Topology of Closed One-Forms*, Section 1.1 (the homomorphism of periods
  `H₁(M; ℤ) → ℝ`).
-/

public section

open Set TopologicalSpace TauCeti
open scoped Manifold ContDiff

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

namespace TauCeti

/-- **Closed forms with vanishing periods near the subset of an NDR pair.** Let `Q ⊆ U` carry NDR
data, with `U` open. There is an open `V` with `Q ⊆ V ⊆ U` such that every closed one-form on `U`
whose periods vanish on the image of `H₁(Q; ℤ)` restricts to an exact form on `V`. -/
theorem NDRPair.exists_forall_exact {Q : Set M} (hN : NDRPair Q) {U : Opens M}
    (hQU : Q ⊆ U) :
    ∃ V : Opens M, Q ⊆ V ∧ ∃ hVU : V ≤ U, ∀ φ : SmoothForm I U ℝ 1, φ ∈ closedForms I U 1 →
      (homologyPeriodHom (φ : RoughForm I U ℝ 1)).comp
          (ContinuousMap.singularHomologyMap ℤ 1 (ContinuousMap.inclusion hQU)).toAddMonoidHom =
        0 →
      SmoothForm.mpullback (Opens.inclusion hVU) (contMDiff_inclusion hVU) φ ∈
        exactForms I V 1 := by
  obtain ⟨V, hVo, hQV, hVU, hV⟩ := hN.exists_isOpen_range_singularHomologyMap_le U.isOpen hQU
  refine ⟨⟨V, hVo⟩, hQV, hVU, fun φ hφ hper ↦ ?_⟩
  have hi := contMDiff_inclusion (I := I) (n := ∞) (U := ⟨V, hVo⟩) hVU
  have hcl : SmoothForm.mpullback _ hi φ ∈ closedForms I (⟨V, hVo⟩ : Opens M) 1 :=
    SmoothForm.mpullback_mem_closedForms _ hi hφ
  refine (mem_exactForms_one_iff_homologyPeriodHom_eq_zero hcl).2 (AddMonoidHom.ext fun c ↦ ?_)
  -- The class pushed into `U` comes from `Q`, where the periods of `φ` vanish.
  obtain ⟨z, hz⟩ := hV 1 ⟨c, rfl⟩
  rw [SmoothForm.coe_mpullback, ← homologyPeriodHom_singularHomologyMap (hi.of_le (by simp))
    (φ.isSmoothForm.of_le (by simp)) ((mem_closedForms I _).mp hφ), AddMonoidHom.zero_apply]
  -- The inclusion `V → U` as a continuous map is `ContinuousMap.inclusion hVU`.
  change homologyPeriodHom (φ : RoughForm I U ℝ 1)
    (ContinuousMap.singularHomologyMap ℤ 1 (ContinuousMap.inclusion hVU) c) = 0
  rw [← hz]
  exact DFunLike.congr_fun hper z

variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {P : Type} [TopologicalSpace P] [ChartedSpace H' P] [IsManifold J ∞ P] [T2Space P]
  {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- **The slices of a smooth isotopy pull closed one-forms back to forms with the same periods.**
For a smooth isotopy `F` starting at `f₀` and a closed `C¹` one-form `θ`, the periods on
`H₁(P; ℤ)` of `F (t, ·)^* θ` are those of `f₀^* θ`, since the slice is homotopic to `f₀`. -/
theorem SmoothIsotopy.homologyPeriodHom_mpullback_eq {f₀ f₁ : C^∞⟮J, P; I, M⟯}
    (F : SmoothIsotopy f₀ f₁) {θ : RoughForm I M G 1} (hθ : IsSmoothForm I 1 θ)
    (hcl : mextDeriv θ = 0) (t : unitInterval) :
    homologyPeriodHom (mpullback J I (fun x ↦ F (t, x)) θ) =
      homologyPeriodHom (mpullback J I f₀ θ) := by
  have hFt : ContMDiff J I ∞ fun x ↦ F (t, x) :=
    F.contMDiff.comp (contMDiff_const.prodMk contMDiff_id)
  -- The homotopy `(s, x) ↦ F (s t, x)` from `f₀` to the slice at `t`.
  let K : _root_.ContinuousMap.Homotopy (⟨f₀, f₀.contMDiff.continuous⟩ : C(P, M))
      ⟨fun x ↦ F (t, x), hFt.continuous⟩ :=
    { toFun := fun p ↦ F (p.1 * t, p.2)
      continuous_toFun := F.contMDiff.continuous.comp (by fun_prop)
      map_zero_left := fun x ↦ by simp [F.apply_zero]
      map_one_left := fun x ↦ by simp }
  exact (homologyPeriodHom_mpullback_eq_of_homotopic (f₀.contMDiff.of_le (by simp))
    (hFt.of_le (by simp)) ⟨K⟩ hθ hcl).symm

end TauCeti

namespace SymplecticGeometry

/-- **Closed forms on `M` with the periods of a smooth family on `U`.** Let `M` be compact,
`Q ⊆ U` with `U` open, and suppose that every additive map `H₁(Q; ℤ) → ℝ` is the restriction of
the periods of a de Rham class of `M`. Then for every smooth family `α_t` of closed one-forms on
`U` there is a smooth family `β_t` of closed one-forms on `M` with the same periods on the image of
`H₁(Q; ℤ)`, at every `t`. -/
theorem exists_closedForms_periods_eq [I.Boundaryless] [CompactSpace M] {Q : Set M} {U : Opens M}
    (hQU : Q ⊆ U)
    (hsurj : ∀ f : ((singularChains ℤ).obj (.of Q)).homology 1 →+ ℝ,
      ∃ c : deRhamCohomology I M 1, (deRhamCohomology.homologyPeriod c).comp
        (ContinuousMap.singularHomologyMap ℤ 1
          (⟨Subtype.val, continuous_subtypeVal⟩ : C(Q, M))).toAddMonoidHom = f)
    {EN HN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
    {K : ModelWithCorners ℝ EN HN} {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]
    [IsManifold K ∞ N] {α : N → SmoothForm I U ℝ 1} (hα : IsSmoothFamily K α)
    (hcl : ∀ t, α t ∈ closedForms I U 1) :
    ∃ β : N → SmoothForm I M ℝ 1, IsSmoothFamily K β ∧ (∀ t, β t ∈ closedForms I M 1) ∧
      ∀ t, (homologyPeriodHom (α t : RoughForm I U ℝ 1)).comp
          (ContinuousMap.singularHomologyMap ℤ 1 (ContinuousMap.inclusion hQU)).toAddMonoidHom =
        (homologyPeriodHom (β t : RoughForm I M ℝ 1)).comp
          (ContinuousMap.singularHomologyMap ℤ 1
            (⟨Subtype.val, continuous_subtypeVal⟩ : C(Q, M))).toAddMonoidHom := by
  set W := ((singularChains ℤ).obj (.of Q)).homology 1 →+ ℝ
  set ιM := ContinuousMap.singularHomologyMap ℤ 1
    (⟨Subtype.val, continuous_subtypeVal⟩ : C(Q, M))
  -- Restriction of de Rham classes to `Q`, through their periods.
  let R : deRhamCohomology I M 1 →ₗ[ℝ] W :=
    { toFun c := (deRhamCohomology.homologyPeriod c).comp ιM.toAddMonoidHom
      map_add' c c' := by rw [map_add, AddMonoidHom.add_comp]
      map_smul' a c := by
        ext z
        simp only [map_smul, RingHom.id_apply]
        rfl }
  have hR : Function.Surjective R := hsurj
  have : FiniteDimensional ℝ W := Module.Finite.of_surjective R hR
  obtain ⟨S, hS⟩ := R.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hR)
  obtain ⟨L, hL⟩ := (deRhamCohomology.mk I (M := M) 1).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.2 (deRhamCohomology.mk_surjective I 1))
  -- The periods of `α_t` on `H₁(Q; ℤ)`.
  let p : N → W := fun t ↦ (homologyPeriodHom (α t : RoughForm I U ℝ 1)).comp
    (ContinuousMap.singularHomologyMap ℤ 1 (ContinuousMap.inclusion hQU)).toAddMonoidHom
  let T : W →ₗ[ℝ] SmoothForm I M ℝ 1 := (closedForms I M 1).subtype ∘ₗ L ∘ₗ S
  refine ⟨fun t ↦ T (p t), isSmoothFamily_of_contMDiff_dual T fun f ↦ ?_,
    fun t ↦ (L (S (p t))).property, fun t ↦ ?_⟩
  · -- Every functional on `W` is a combination of evaluations at classes of `Q`.
    let ev : ((singularChains ℤ).obj (.of Q)).homology 1 → Module.Dual ℝ W := fun z ↦
      { toFun g := g z
        map_add' _ _ := rfl
        map_smul' _ _ := rfl }
    refine contMDiff_dual_apply_of_separating (s := range ev) (fun g hg ↦ ?_) ?_ f
    · obtain ⟨z, hz⟩ : ∃ z, g z ≠ 0 := by
        by_contra! h
        exact hg (AddMonoidHom.ext h)
      exact ⟨ev z, ⟨z, rfl⟩, hz⟩
    rintro _ ⟨z, rfl⟩
    exact hα.contMDiff_homologyPeriodHom hcl _
  · -- The class `S (p t)` restricts to `p t`, and `L` picks a representative of it.
    have h₁ : deRhamCohomology.mk I 1 (L (S (p t))) = S (p t) := LinearMap.congr_fun hL _
    have h₂ : R (S (p t)) = p t := LinearMap.congr_fun hS _
    rw [← h₁] at h₂
    simp only [R, LinearMap.coe_mk, AddHom.coe_mk, deRhamCohomology.homologyPeriod_mk] at h₂
    exact h₂.symm

/-- **Smooth primitives near `Q` of the corrected forms.** Let `Q ⊆ U` carry NDR data, with `U`
open, and let `φ` be a smooth isotopy of `U` starting at the inclusion. Let `α_t` and `β_t` be
smooth families of closed one-forms on `U` and on `M` with the same periods on the image of
`H₁(Q; ℤ)`. Then there are an open `V` with `Q ⊆ V ⊆ U` and a smooth `h : [0, 1] × V → ℝ` such
that `h (t, ·)` is a primitive on `V` of `α_t - φ_t^* β_t`, for every `t`. -/
theorem exists_contMDiff_primitive_of_periods {Q : Set M} (hN : NDRPair Q) {U : Opens M}
    (hQU : Q ⊆ U) {f₀ f₁ : C^∞⟮I, U; I, M⟯} (φ : SmoothIsotopy f₀ f₁) (hf₀ : ∀ x, f₀ x = x)
    {α : unitInterval → SmoothForm I U ℝ 1} (hα : IsSmoothFamily (𝓡∂ 1) α)
    (hαcl : ∀ t, α t ∈ closedForms I U 1) {β : unitInterval → SmoothForm I M ℝ 1}
    (hβ : IsSmoothFamily (𝓡∂ 1) β) (hβcl : ∀ t, β t ∈ closedForms I M 1)
    (hper : ∀ t, (homologyPeriodHom (α t : RoughForm I U ℝ 1)).comp
        (ContinuousMap.singularHomologyMap ℤ 1 (ContinuousMap.inclusion hQU)).toAddMonoidHom =
      (homologyPeriodHom (β t : RoughForm I M ℝ 1)).comp
        (ContinuousMap.singularHomologyMap ℤ 1
          (⟨Subtype.val, continuous_subtypeVal⟩ : C(Q, M))).toAddMonoidHom) :
    ∃ V : Opens M, Q ⊆ V ∧ ∃ hVU : V ≤ U, ∃ h : unitInterval × V → ℝ,
      ContMDiff ((𝓡∂ 1).prod I) 𝓘(ℝ) ∞ h ∧ ∀ t : unitInterval,
        mextDeriv (RoughForm.ofFunction I fun x ↦ h (t, x)) =
          (SmoothForm.mpullback (Opens.inclusion hVU) (contMDiff_inclusion hVU)
            (α t - SmoothForm.mpullback (fun x : U ↦ φ (t, x))
              (φ.contMDiff.comp (contMDiff_const.prodMk contMDiff_id)) (β t)) :
            RoughForm I V ℝ 1) := by
  obtain ⟨V, hQV, hVU, hV⟩ := hN.exists_forall_exact (I := I) hQU
  have hφt (t : unitInterval) : ContMDiff I I ∞ fun x : U ↦ φ (t, x) :=
    φ.contMDiff.comp (contMDiff_const.prodMk contMDiff_id)
  have hψcl (t : unitInterval) : SmoothForm.mpullback _ (hφt t) (β t) ∈ closedForms I U 1 :=
    SmoothForm.mpullback_mem_closedForms _ (hφt t) (hβcl t)
  -- Each corrected form is exact on `V`.
  have hex (t : unitInterval) : SmoothForm.mpullback (Opens.inclusion hVU)
      (contMDiff_inclusion hVU) (α t - SmoothForm.mpullback _ (hφt t) (β t)) ∈
        exactForms I V 1 := by
    refine hV _ (sub_mem (hαcl t) (hψcl t)) (AddMonoidHom.ext fun z ↦ ?_)
    have hβc : mextDeriv (β t : RoughForm I M ℝ 1) = 0 := (mem_closedForms I _).mp (hβcl t)
    have hval : ContMDiff I I ∞ (Subtype.val : U → M) := contMDiff_subtypeVal
    -- The periods of `φ_t^* β_t` on `U` are those of `β_t` restricted to `U`.
    have hψ := congrArg (fun g ↦ g (ContinuousMap.singularHomologyMap ℤ 1
        (ContinuousMap.inclusion hQU) z))
      ((φ.homologyPeriodHom_mpullback_eq ((β t).isSmoothForm.of_le (by simp)) hβc t))
    rw [show (f₀ : U → M) = Subtype.val from funext hf₀] at hψ
    rw [← homologyPeriodHom_singularHomologyMap (hval.of_le (by simp))
      ((β t).isSmoothForm.of_le (by simp)) hβc,
      ← ContinuousMap.singularHomologyMap_comp] at hψ
    have hz := DFunLike.congr_fun (hper t) z
    simp only [AddMonoidHom.coe_comp, LinearMap.toAddMonoidHom_coe, Function.comp_apply] at hz
    rw [Submodule.coe_sub, homologyPeriodHom_sub ((α t).isSmoothForm.of_le (by simp))
      ((mem_closedForms I _).mp (hαcl t)) ((SmoothForm.mpullback _ (hφt t) (β t)).isSmoothForm.of_le
        (by simp)) ((mem_closedForms I _).mp (hψcl t))]
    simp only [AddMonoidHom.coe_comp, LinearMap.toAddMonoidHom_coe, Function.comp_apply,
      AddMonoidHom.sub_apply, AddMonoidHom.zero_apply, SmoothForm.coe_mpullback]
    rw [hψ, hz, sub_eq_zero]
    -- `Subtype.val ∘ inclusion hQU` is the inclusion of `Q` in `M`.
    rfl
  obtain ⟨h, hh, hdh⟩ := exists_contMDiff_mextDeriv_eq_of_forall_mem_exactForms
    ((hα.sub (hβ.mpullback_family φ.contMDiff)).mpullback _ (contMDiff_inclusion hVU)) hex
  exact ⟨V, hQV, hVU, h, hh, hdh⟩

end SymplecticGeometry

end
