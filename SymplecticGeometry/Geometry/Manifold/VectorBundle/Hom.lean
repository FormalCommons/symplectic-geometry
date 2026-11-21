/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.Trivial

/-!
# Fibrewise linear maps as sections of hom bundles

Let `Φ x : V₁ x ≃L V₂ x` be fibrewise equivalences of vector bundles whose map of total spaces is
`C^n`, with `V₁` of finite rank. Then the fibrewise inverses `(Φ x)⁻¹` form a `C^n` section of the
bundle of continuous linear maps `V₂ x →L V₁ x` (`contMDiff_hom_bundle_symm`). The forward maps
`Φ x` form a `C^n` section by Tau Ceti's `TauCeti.contMDiff_hom_bundle_iff`, and inversion
preserves smoothness by Tau Ceti's `ContMDiff.clm_bundle_inverse`. As in
`TauCeti.contMDiff_bundle_symm`, only the source bundle `V₁` needs finite rank.

For a family `Φ x : W →L V x` out of a fixed space `W` of finite dimension, the file also reads
the smoothness of `Φ` as a section of the hom bundle from the trivial bundle with fibre `W` on the
product `M × W` (`contMDiffAt_hom_trivial_iff`), through Tau Ceti's
`TauCeti.contMDiffAt_hom_bundle_iff` and `Bundle.Trivial.diffeomorphProd`.

Last, a fixed continuous linear map `f : W →L W'`, applied in each fibre, is a `C^n` map from the
total space of the trivial bundle with fibre `W` to that with fibre `W'`
(`Bundle.Trivial.contMDiff_totalSpaceMk_clm`).
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

section Trivial

omit [FiniteDimensional 𝕜 F₁]

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W] [FiniteDimensional 𝕜 W]

/-- A family of continuous linear maps `Φ x : W →L V₂ x` from a fixed space `W` of finite
dimension is a `C^n` section at `x` of the bundle of continuous linear maps from the trivial bundle
with fibre `W` to `V₂` exactly when `(y, v) ↦ Φ y v`, as a map from `M × W` to the total space of
`V₂`, is `C^n` at `(x, v)` for every `v`. -/
theorem contMDiffAt_hom_trivial_iff (Φ : ∀ x, W →L[𝕜] V₂ x) (x : M) :
    ContMDiffAt I (I.prod 𝓘(𝕜, W →L[𝕜] F₂)) n
        (fun y ↦ TotalSpace.mk' (W →L[𝕜] F₂) (E := fun y ↦ Trivial M W y →L[𝕜] V₂ y) y
          (Φ y : W →L[𝕜] V₂ y)) x ↔
      ∀ v : W, ContMDiffAt (I.prod 𝓘(𝕜, W)) (I.prod 𝓘(𝕜, F₂)) n
        (fun p : M × W ↦ TotalSpace.mk' F₂ p.1 (Φ p.1 p.2)) (x, v) := by
  rw [TauCeti.contMDiffAt_hom_bundle_iff]
  refine forall_congr' fun v ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hd : ContMDiffAt (I.prod 𝓘(𝕜, W)) (I.prod 𝓘(𝕜, W)) n
        (fun q : M × W ↦ (⟨q.1, q.2⟩ : TotalSpace W (Trivial M W))) (x, v) :=
      (Trivial.diffeomorphProd I M W n).symm.contMDiff.contMDiffAt.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun q ↦ by simp)
    exact h.comp (x, v) hd
  · have hd : ContMDiffAt (I.prod 𝓘(𝕜, W)) (I.prod 𝓘(𝕜, W)) n
        (fun p : TotalSpace W (Trivial M W) ↦ (p.proj, p.snd)) ⟨x, v⟩ :=
      (Trivial.diffeomorphProd I M W n).contMDiff.contMDiffAt.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun p ↦ by simp)
    exact h.comp (x := (⟨x, v⟩ : TotalSpace W (Trivial M W))) hd

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 W] in
/-- A fixed continuous linear map `f : W →L W'`, applied in each fibre, is a `C^n` map from the
total space of the trivial bundle with fibre `W` to that of the trivial bundle with fibre `W'`. -/
theorem Bundle.Trivial.contMDiff_totalSpaceMk_clm {W' : Type*} [NormedAddCommGroup W']
    [NormedSpace 𝕜 W'] (f : W →L[𝕜] W') :
    ContMDiff (I.prod 𝓘(𝕜, W)) (I.prod 𝓘(𝕜, W')) n
      (fun p : TotalSpace W (Trivial M W) ↦ TotalSpace.mk' W' (E := Trivial M W') p.proj
        (f p.snd)) :=
  Trivial.contMDiff_mk_iff.2
    ⟨contMDiff_proj _, f.contDiff.contMDiff.comp (Trivial.contMDiff_mk_iff.1 contMDiff_id).2⟩

end Trivial

end
