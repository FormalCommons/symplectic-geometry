/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Symplectic.ComplexStructure.Basic
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import SymplecticGeometry.Geometry.Manifold.VectorBundle.BilinearForm
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Riemannian.PolarEnd
import SymplecticGeometry.Geometry.Symplectic.LinearMoser
import TauCeti.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Geometry.Symplectic.Cayley.Basic
import TauCeti.Topology.Algebra.Module.BilinearForm
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.FiniteDimensional

/-!
# Symplectic and complex isomorphisms of vector bundles

For `i = 1, 2`, let `ωᵢ` be a `Cⁿ` two-form on a real vector bundle `Vᵢ → M` of finite rank that
tames a `Cⁿ` complex structure `Jᵢ`. This file shows that `V₁` and `V₂` are isomorphic as
symplectic bundles exactly when they are isomorphic as complex bundles. Isomorphisms are families
of fibrewise continuous linear equivalences whose map of total spaces is `Cⁿ`, as in
`ContMDiffTwoForm.pushforward`. The base may have boundary or corners, and no hypothesis on it is
needed beyond being a manifold.

## Main results

* `ContMDiffTwoForm.Tames.exists_complex_bundleEquiv`: two complex structures tamed by the same
  form are isomorphic through the automorphism `1 - J' J` of the bundle.
* `ContMDiffTwoForm.exists_symplectic_bundleEquiv_of_forall_isNondegenerate`: two forms on one
  bundle, all of whose convex combinations are nondegenerate, are isomorphic through the fibrewise
  linear Moser flow from one to the other.
* `ContMDiffTwoForm.Tames.exists_symplectic_bundleEquiv`: in particular two forms that tame the
  same complex structure are isomorphic.
* `exists_symplectic_bundleEquiv_iff_exists_complex_bundleEquiv`: the classification.

## Implementation notes

Both directions follow McDuff–Salamon, Theorem 2.6.3. From symplectic to complex: transport `J₁`
along a symplectic isomorphism `Φ`; then `ω₂` tames both `J₂` and the transported `J₁'`, and
`1 - J₂ J₁'` is invertible (the argument of Tau Ceti's
`TauCeti.SymplecticForm.Tames.isUnit_one_sub_mul`)
and intertwines `J₁'` with `J₂`. From complex to symplectic: transport `ω₁` along a complex
isomorphism; then `ω₁'` and `ω₂` both tame `J₂`, so all their convex combinations are
nondegenerate, and the linear Moser flow of the segment from `ω₁'` to `ω₂` along
`Real.smoothTransition` (`SymplecticGeometry.segmentMoserFlow`), applied in each fibre, pulls
`ω₂` back to `ω₁'`.

The fibres carry no norm, so the Moser flow at `x` is computed on a Euclidean space through
`Bundle.euclideanEquivAt F V x`, as `SymplecticGeometry.Bundle.mapBilinPairAt`. The flow is
natural under linear isomorphisms (`SymplecticGeometry.segmentMoserFlow_conj`) and smooth in the
pair of forms on the open set `SymplecticGeometry.invertibleSegments`
(`SymplecticGeometry.contDiffOn_segmentMoserFlow`), so
`SymplecticGeometry.Bundle.contMDiffAt_mapBilinPairAt` shows that it is a `Cⁿ` section of the
endomorphism bundle.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Theorem 2.6.3 and Exercise 2.6.2
-/

public section

noncomputable section

open _root_.Bundle Set
open scoped Manifold

namespace SymplecticGeometry.Bundle

variable {EB HB M : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [TopologicalSpace HB] {I : ModelWithCorners ℝ EB HB}
  [TopologicalSpace M] [ChartedSpace HB M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V] {n m : ℕ∞}

namespace ContMDiffTwoForm

/-! ### From symplectic to complex -/

section Complex

variable {ω : ContMDiffTwoForm I n F V} {J J' : ContMDiffComplexStructure I m F V}

/-- For two complex structures tamed by the same form, `1 - J' J` is invertible on each fibre:
Tau Ceti's `TauCeti.SymplecticForm.Tames.isUnit_one_sub_mul` on the fibre. -/
private theorem Tames.isUnit_one_sub (h : ω.Tames J) (h' : ω.Tames J') (x : M) :
    IsUnit (1 - J' x * J x) := by
  have := (VectorBundle.continuousLinearEquivAt ℝ F V x).symm.finiteDimensional
  have hn := h.isNondegenerate
  have hu := TauCeti.SymplecticForm.Tames.isUnit_one_sub_mul (hn.tames_iff.1 h' x)
    (hn.tames_iff.1 h x)
  rw [J.almostComplexStructureAt_toLinearMap, J'.almostComplexStructureAt_toLinearMap] at hu
  exact ContinuousLinearMap.isUnit_of_isUnit_toLinearMap_of_finiteDimensional (by simpa using hu)

/-- **Complex structures tamed by one form are isomorphic.** If a two-form tames two complex
structures `J` and `J'` of class `Cᵐ`, some fibrewise linear equivalences `Ψ`, whose map of total
spaces is `Cᵐ`, carry `J` to `J'`. -/
theorem Tames.exists_complex_bundleEquiv [ContMDiffVectorBundle m F V I] (h : ω.Tames J)
    (h' : ω.Tames J') :
    ∃ Ψ : ∀ x, V x ≃L[ℝ] V x, ContMDiff (I.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F)) m
        (fun v : TotalSpace F V ↦ TotalSpace.mk' F v.proj (Ψ v.proj v.snd)) ∧
      ∀ x v, Ψ x (J x v) = J' x (Ψ x v) := by
  let Ψ x := ContinuousLinearEquiv.unitsEquiv ℝ (V x) (h.isUnit_one_sub h' x).unit
  have hΨ (x : M) (v : V x) : Ψ x v = v - J' x (J x v) := by
    simp [Ψ, ContinuousLinearEquiv.unitsEquiv_apply]
  refine ⟨Ψ, ?_, fun x v ↦ ?_⟩
  · have hsec : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] F)) m fun x ↦
        TotalSpace.mk' (F →L[ℝ] F) (E := fun x ↦ V x →L[ℝ] V x) x
          (ContinuousLinearMap.id ℝ (V x) - (J' x).comp (J x)) :=
      TauCeti.contMDiff_id_endomorphism.sub_section
        (J'.toEndomorphism.contMDiff.clm_bundle_comp J.toEndomorphism.contMDiff)
    refine ((TauCeti.contMDiff_hom_bundle_iff fun x ↦ (Ψ x : V x →L[ℝ] V x)).1 ?_)
    convert hsec using 3 with x
    ext v
    simp [hΨ]
  · rw [hΨ, hΨ]
    simp only [map_sub, map_neg, ContMDiffComplexStructure.apply_apply, sub_neg_eq_add]
    abel

end Complex

/-! ### From complex to symplectic: the fibrewise linear Moser flow -/

section Moser

variable {ω ω' : ContMDiffTwoForm I n F V}

omit [FiniteDimensional ℝ F] in
/-- If every convex combination of `ω` and `ω'` is nondegenerate, their flat maps at `x`, carried
to a finite-dimensional normed space, are a pair of `invertibleSegments`. -/
private theorem mem_invertibleSegments
    (h : ∀ s ∈ Icc (0 : ℝ) 1, ((1 - s) • ω + s • ω').IsNondegenerate) (x : M) {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (e : V x ≃L[ℝ] W) :
    (e.bilinearCongr (ω.flat x), e.bilinearCongr (ω'.flat x)) ∈ invertibleSegments W := by
  rw [mem_invertibleSegments_iff]
  intro s hs
  rw [ContinuousLinearMap.isInvertible_iff_separatingLeft]
  intro v hv
  have h0 := isNondegenerate_iff_separatingLeft.1 (h s hs) x (e.symm v) fun w ↦ by
    simpa [flat_apply] using hv (e w)
  simpa using congrArg e h0

/-- **Two-forms joined by nondegenerate forms are isomorphic.** If every convex combination
`(1 - s) • ω + s • ω'`, `0 ≤ s ≤ 1`, of two `Cⁿ` two-forms on a bundle of finite rank is
nondegenerate, some fibrewise linear equivalences `Ψ`, whose map of total spaces is `Cⁿ`, carry `ω`
to `ω'`: `ω'(Ψ v, Ψ w) = ω(v, w)`. -/
theorem exists_symplectic_bundleEquiv_of_forall_isNondegenerate
    (h : ∀ s ∈ Icc (0 : ℝ) 1, ((1 - s) • ω + s • ω').IsNondegenerate) :
    ∃ Ψ : ∀ x, V x ≃L[ℝ] V x, ContMDiff (I.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F)) n
        (fun v : TotalSpace F V ↦ TotalSpace.mk' F v.proj (Ψ v.proj v.snd)) ∧
      ∀ x v w, ω'.bilinFormAt x (Ψ x v) (Ψ x w) = ω.bilinFormAt x v w := by
  -- The linear Moser flow at `x`, computed through `Bundle.euclideanEquivAt F V x`.
  let E := _root_.Bundle.euclideanEquivAt F V
  let P (x : M) : V x →L[ℝ] V x :=
    mapBilinPairAt E (fun p ↦ segmentMoserFlow p.1 p.2) x (ω.flat x) (ω'.flat x)
  have hu (x : M) : IsUnit (P x) := by
    simp only [P, mapBilinPairAt_def]
    exact (isUnit_segmentMoserFlow (mem_invertibleSegments h x (E x))).map
      (E x).symm.conjContinuousAlgEquiv
  let Ψ x := ContinuousLinearEquiv.unitsEquiv ℝ (V x) (hu x).unit
  have hΨ (x : M) (v : V x) : Ψ x v = P x v := by
    simp [Ψ, ContinuousLinearEquiv.unitsEquiv_apply]
  refine ⟨Ψ, (TauCeti.contMDiff_hom_bundle_iff fun x ↦ (Ψ x : V x →L[ℝ] V x)).1 ?_,
    fun x v w ↦ ?_⟩
  · have hP : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] F)) n fun x ↦
        TotalSpace.mk' (F →L[ℝ] F) (E := fun x ↦ V x →L[ℝ] V x) x (P x) := fun x ↦
      contMDiffAt_mapBilinPairAt E isOpen_invertibleSegments contDiffOn_segmentMoserFlow
        (fun f _ hp ↦ segmentMoserFlow_conj f hp) (f := id) (ω.contMDiff_flat x)
        (ω'.contMDiff_flat x) (mem_invertibleSegments h x _)
    convert hP using 3 with x
    ext v
    simp [hΨ]
  · -- Read in the equivalence `E x`, this is the defining property of the Moser flow.
    let e := E x
    have hskew (η : ContMDiffTwoForm I n F V) (v w : EuclideanSpace ℝ (Fin (Module.finrank ℝ F))) :
        e.bilinearCongr (η.flat x) v w = -e.bilinearCongr (η.flat x) w v := by
      simp only [ContinuousLinearEquiv.bilinearCongr_apply, flat_apply, ← bilinFormAt_apply]
      exact ((η.isAlt_bilinFormAt x).neg_eq _ _).symm
    have key := apply_segmentMoserFlow (mem_invertibleSegments h x e) (hskew ω) (hskew ω')
      (e v) (e w)
    simp only [ContinuousLinearEquiv.bilinearCongr_apply] at key
    rw [hΨ, hΨ]
    simpa [P, mapBilinPairAt_def, e, bilinFormAt_apply, flat_apply] using key

end Moser

/-- **Two-forms taming one complex structure are isomorphic.** If two `Cⁿ` two-forms `ω`, `ω'`
on a bundle of finite rank tame the same complex structure, some fibrewise linear equivalences
`Ψ`, whose map of total spaces is `Cⁿ`, carry `ω` to `ω'`. -/
theorem Tames.exists_symplectic_bundleEquiv {ω ω' : ContMDiffTwoForm I n F V}
    {J : ContMDiffComplexStructure I m F V}
    (h : ω.Tames J) (h' : ω'.Tames J) :
    ∃ Ψ : ∀ x, V x ≃L[ℝ] V x, ContMDiff (I.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F)) n
        (fun v : TotalSpace F V ↦ TotalSpace.mk' F v.proj (Ψ v.proj v.snd)) ∧
      ∀ x v w, ω'.bilinFormAt x (Ψ x v) (Ψ x w) = ω.bilinFormAt x v w :=
  exists_symplectic_bundleEquiv_of_forall_isNondegenerate fun s hs ↦
    (convex_setOfPred_tames J h h' (sub_nonneg.2 hs.2) hs.1 (sub_add_cancel 1 s)).isNondegenerate

end ContMDiffTwoForm

/-! ### The classification -/

variable {F₁ F₂ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂] {V₁ V₂ : M → Type*}
  [∀ x, AddCommGroup (V₁ x)] [∀ x, Module ℝ (V₁ x)]
  [∀ x, TopologicalSpace (V₁ x)] [∀ x, IsTopologicalAddGroup (V₁ x)]
  [∀ x, ContinuousSMul ℝ (V₁ x)] [TopologicalSpace (TotalSpace F₁ V₁)]
  [FiberBundle F₁ V₁] [VectorBundle ℝ F₁ V₁]
  [∀ x, AddCommGroup (V₂ x)] [∀ x, Module ℝ (V₂ x)]
  [∀ x, TopologicalSpace (V₂ x)] [∀ x, IsTopologicalAddGroup (V₂ x)]
  [∀ x, ContinuousSMul ℝ (V₂ x)] [TopologicalSpace (TotalSpace F₂ V₂)]
  [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂] [ContMDiffVectorBundle n F₂ V₂ I]
  {ω₁ : ContMDiffTwoForm I n F₁ V₁} {ω₂ : ContMDiffTwoForm I n F₂ V₂}
  {J₁ : ContMDiffComplexStructure I n F₁ V₁} {J₂ : ContMDiffComplexStructure I n F₂ V₂}

/-- **Symplectic bundles are classified by their complex structures.** For `i = 1, 2`, let `ωᵢ`
be a `Cⁿ` two-form on a real vector bundle `Vᵢ` of finite rank over `M` that tames a `Cⁿ` complex
structure `Jᵢ`. Then `(V₁, ω₁)` and `(V₂, ω₂)` are isomorphic as symplectic bundles if and only if
`(V₁, J₁)` and `(V₂, J₂)` are isomorphic as complex bundles. An isomorphism is a family of
fibrewise continuous linear equivalences whose map of total spaces is `Cⁿ`. The base may have
boundary or corners.

Milestone: *Symplectic vector bundles are complex vector bundles*. -/
theorem exists_symplectic_bundleEquiv_iff_exists_complex_bundleEquiv (h₁ : ω₁.Tames J₁)
    (h₂ : ω₂.Tames J₂) :
    (∃ Φ : ∀ x, V₁ x ≃L[ℝ] V₂ x, ContMDiff (I.prod 𝓘(ℝ, F₁)) (I.prod 𝓘(ℝ, F₂)) n
        (fun v : TotalSpace F₁ V₁ ↦ TotalSpace.mk' F₂ v.proj (Φ v.proj v.snd)) ∧
      ∀ x v w, ω₂.bilinFormAt x (Φ x v) (Φ x w) = ω₁.bilinFormAt x v w) ↔
    (∃ Φ : ∀ x, V₁ x ≃L[ℝ] V₂ x, ContMDiff (I.prod 𝓘(ℝ, F₁)) (I.prod 𝓘(ℝ, F₂)) n
        (fun v : TotalSpace F₁ V₁ ↦ TotalSpace.mk' F₂ v.proj (Φ v.proj v.snd)) ∧
      ∀ x v, Φ x (J₁ x v) = J₂ x (Φ x v)) := by
  constructor
  · rintro ⟨Φ, hΦ, hω⟩
    -- `Φ` carries `ω₁` to `ω₂`, so `ω₂` tames the transport of `J₁`.
    have ht : ω₂.Tames (J₁.pushforward Φ hΦ) :=
      (ContMDiffTwoForm.pushforward_eq_iff Φ hΦ).2 hω ▸ h₁.pushforward Φ hΦ hΦ
    obtain ⟨Ψ, hΨ, hJ⟩ := ht.exists_complex_bundleEquiv h₂
    refine ⟨fun x ↦ (Φ x).trans (Ψ x), by simpa [Function.comp_def] using hΨ.comp hΦ,
      fun x v ↦ ?_⟩
    have := hJ x (Φ x v)
    simp only [ContMDiffComplexStructure.pushforward_apply,
      ContinuousLinearEquiv.symm_apply_apply] at this
    simpa using this
  · rintro ⟨Φ, hΦ, hJ⟩
    -- The transport of `J₁` along `Φ` is `J₂`, so the transport of `ω₁` tames `J₂`.
    have hJ₂ : J₁.pushforward Φ hΦ = J₂ := by
      ext x v
      rw [ContMDiffComplexStructure.pushforward_apply, hJ, ContinuousLinearEquiv.apply_symm_apply]
    have ht : (ContMDiffTwoForm.pushforward Φ hΦ ω₁).Tames J₂ :=
      hJ₂ ▸ h₁.pushforward Φ hΦ hΦ
    obtain ⟨Ψ, hΨ, hω⟩ := ht.exists_symplectic_bundleEquiv h₂
    refine ⟨fun x ↦ (Φ x).trans (Ψ x), by simpa [Function.comp_def] using hΨ.comp hΦ,
      fun x v w ↦ ?_⟩
    simp only [ContinuousLinearEquiv.trans_apply, hω,
      ContMDiffTwoForm.bilinFormAt_pushforward_apply, ContinuousLinearEquiv.symm_apply_apply]

end SymplecticGeometry.Bundle

end
