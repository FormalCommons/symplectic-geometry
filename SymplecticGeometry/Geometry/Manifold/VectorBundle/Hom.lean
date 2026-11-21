/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Hom

/-!
# Inverses of fibrewise equivalences as sections of hom bundles

Let `Φ x : V₁ x ≃L V₂ x` be fibrewise equivalences of vector bundles whose map of total spaces is
`C^n`, with `V₁` of finite rank. Then the fibrewise inverses `(Φ x)⁻¹` form a `C^n` section of the
bundle of continuous linear maps `V₂ x →L V₁ x` (`contMDiff_hom_bundle_symm`). The forward maps
`Φ x` form a `C^n` section by Tau Ceti's `TauCeti.contMDiff_hom_bundle_iff`, and inversion
preserves smoothness by Tau Ceti's `ContMDiff.clm_bundle_inverse`. As in
`TauCeti.contMDiff_bundle_symm`, only the source bundle `V₁` needs finite rank.
-/

public section

open Bundle
open scoped Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {EB HB M : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  [TopologicalSpace HB] {I : ModelWithCorners 𝕜 EB HB}
  [TopologicalSpace M] [ChartedSpace HB M]
  {F₁ F₂ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {V₁ V₂ : M → Type*} [∀ x, AddCommGroup (V₁ x)] [∀ x, Module 𝕜 (V₁ x)]
  [∀ x, TopologicalSpace (V₁ x)] [∀ x, IsTopologicalAddGroup (V₁ x)]
  [∀ x, ContinuousSMul 𝕜 (V₁ x)] [TopologicalSpace (TotalSpace F₁ V₁)]
  [FiberBundle F₁ V₁] [VectorBundle 𝕜 F₁ V₁]
  [∀ x, AddCommGroup (V₂ x)] [∀ x, Module 𝕜 (V₂ x)]
  [∀ x, TopologicalSpace (V₂ x)] [∀ x, IsTopologicalAddGroup (V₂ x)]
  [∀ x, ContinuousSMul 𝕜 (V₂ x)] [TopologicalSpace (TotalSpace F₂ V₂)]
  [FiberBundle F₂ V₂] [VectorBundle 𝕜 F₂ V₂] {n : WithTop ℕ∞}

/-- The fibrewise inverses of fibrewise equivalences `Φ x : V₁ x ≃L V₂ x` whose map of total
spaces is `C^n` form a `C^n` section of the bundle of continuous linear maps `V₂ x →L V₁ x`, when
`V₁` has finite rank. -/
theorem contMDiff_hom_bundle_symm (Φ : ∀ x, V₁ x ≃L[𝕜] V₂ x)
    (hΦ : ContMDiff (I.prod 𝓘(𝕜, F₁)) (I.prod 𝓘(𝕜, F₂)) n
      (fun p : TotalSpace F₁ V₁ ↦ TotalSpace.mk' F₂ p.proj (Φ p.proj p.snd))) :
    ContMDiff I (I.prod 𝓘(𝕜, F₂ →L[𝕜] F₁)) n
      (fun x ↦ TotalSpace.mk' (F₂ →L[𝕜] F₁) (E := fun x ↦ V₂ x →L[𝕜] V₁ x) x
        ((Φ x).symm : V₂ x →L[𝕜] V₁ x)) := by
  have := FiniteDimensional.completeSpace 𝕜 F₁
  simpa only [ContinuousLinearMap.inverse_equiv] using
    ((TauCeti.contMDiff_hom_bundle_iff fun x ↦ (Φ x : V₁ x →L[𝕜] V₂ x)).2 hΦ).clm_bundle_inverse
      fun _ ↦ ContinuousLinearMap.isInvertible_equiv

end
