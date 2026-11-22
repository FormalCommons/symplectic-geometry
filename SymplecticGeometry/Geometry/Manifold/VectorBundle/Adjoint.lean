/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Topology.Algebra.Module.BilinearForm
public import TauCeti.Geometry.Manifold.VectorBundle.Hom

/-!
# Adjoints for fields of nondegenerate bilinear forms

For continuous bilinear forms `β₀`, `β₁` and a continuous linear map `T : V₁ →L V₀`, the adjoint
`ContinuousLinearMap.bilinAdjoint β₀ β₁ T : V₀ →L V₁` is `u ↦ β₁⁻¹ (β₀ u ∘ T)`
(`SymplecticGeometry/Topology/Algebra/Module/BilinearForm.lean`). This file shows that it
depends smoothly on smooth data.

Over a manifold, for `C^n` fields `β₀`, `β₁` of bilinear forms on vector bundles `E₀`, `E₁` along a
map `b`, with `β₁` invertible at every point, and a `C^n` section `T` of the bundle
`Hom(E₁, E₀)` along `b`, the adjoints form a `C^n` section of `Hom(E₀, E₁)` along `b`
(`ContMDiff.clm_bundle_bilinAdjoint`, and `ContMDiffAt.clm_bundle_bilinAdjoint` at a point). On a
fibre of finite dimension, a nondegenerate form is invertible
(`ContinuousLinearMap.isInvertible_iff_nondegenerate_toBilinForm` of Tau Ceti). The fibres carry
`IsNormableSpace` instances, which transposing the forms needs. On tangent spaces, instance search
finds them through `TangentSpace.instIsNormableSpace` of
`SymplecticGeometry/Geometry/Manifold/IsManifold/Basic.lean`, which a user imports.

The proof composes Tau Ceti's `ContMDiffWithinAt.clm_bundle_flip`, `ContMDiffAt.clm_bundle_comp`
and `ContMDiffAt.clm_bundle_inverse`, as Tau Ceti's
`TauCeti.SmoothTwoForm.IsNondegenerate.skewPart` does for the tangent bundle.
-/

public section

open Bundle
open scoped Manifold

section Bundle

variable {𝕜 B M F₀ F₁ EB HB EM HM : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM} [TopologicalSpace M] [ChartedSpace HM M]
  [NormedAddCommGroup F₀] [NormedSpace 𝕜 F₀] [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [CompleteSpace F₁] {E₀ E₁ : B → Type*}
  [∀ x, AddCommGroup (E₀ x)] [∀ x, Module 𝕜 (E₀ x)] [∀ x, TopologicalSpace (E₀ x)]
  [∀ x, IsTopologicalAddGroup (E₀ x)] [∀ x, ContinuousSMul 𝕜 (E₀ x)]
  [∀ x, IsNormableSpace 𝕜 (E₀ x)]
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [∀ x, TopologicalSpace (E₁ x)]
  [∀ x, IsTopologicalAddGroup (E₁ x)] [∀ x, ContinuousSMul 𝕜 (E₁ x)]
  [∀ x, IsNormableSpace 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₀ E₀)] [FiberBundle F₀ E₀] [VectorBundle 𝕜 F₀ E₀]
  [TopologicalSpace (TotalSpace F₁ E₁)] [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  {n : WithTop ℕ∞} {b : M → B}
  {β₀ : ∀ m, E₀ (b m) →L[𝕜] E₀ (b m) →L[𝕜] 𝕜} {β₁ : ∀ m, E₁ (b m) →L[𝕜] E₁ (b m) →L[𝕜] 𝕜}
  {T : ∀ m, E₁ (b m) →L[𝕜] E₀ (b m)}

/-- For `C^n` fields `β₀`, `β₁` of bilinear forms on `E₀`, `E₁` along `b`, with `β₁` invertible
at `m`, and a `C^n` section `T` of `Hom(E₁, E₀)` along `b`, the adjoints
`ContinuousLinearMap.bilinAdjoint (β₀ m) (β₁ m) (T m)` are `C^n` at `m` as a section of
`Hom(E₀, E₁)` along `b`. -/
theorem ContMDiffAt.clm_bundle_bilinAdjoint {m : M}
    (hβ₀ : ContMDiffAt IM (IB.prod 𝓘(𝕜, F₀ →L[𝕜] F₀ →L[𝕜] 𝕜)) n
      (fun y ↦ TotalSpace.mk' (F₀ →L[𝕜] F₀ →L[𝕜] 𝕜)
        (E := fun z ↦ E₀ z →L[𝕜] E₀ z →L[𝕜] 𝕜) (b y) (β₀ y)) m)
    (hβ₁ : ContMDiffAt IM (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₁ →L[𝕜] 𝕜)) n
      (fun y ↦ TotalSpace.mk' (F₁ →L[𝕜] F₁ →L[𝕜] 𝕜)
        (E := fun z ↦ E₁ z →L[𝕜] E₁ z →L[𝕜] 𝕜) (b y) (β₁ y)) m)
    (hT : ContMDiffAt IM (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₀)) n
      (fun y ↦ TotalSpace.mk' (F₁ →L[𝕜] F₀) (E := fun z ↦ E₁ z →L[𝕜] E₀ z) (b y) (T y)) m)
    (hinv : (β₁ m).IsInvertible) :
    ContMDiffAt IM (IB.prod 𝓘(𝕜, F₀ →L[𝕜] F₁)) n
      (fun y ↦ TotalSpace.mk' (F₀ →L[𝕜] F₁) (E := fun z ↦ E₀ z →L[𝕜] E₁ z) (b y)
        (ContinuousLinearMap.bilinAdjoint (β₀ y) (β₁ y) (T y))) m := by
  -- The scalar target is named as the trivial bundle `Trivial B 𝕜`, whose fibres are `𝕜` by
  -- definition, so that Tau Ceti's lemmas find its bundle structure; every bundle argument is
  -- given, since unification cannot see `𝕜` as a fibre of `Trivial B 𝕜`.
  have hflip := contMDiffWithinAt_univ.1
    (ContMDiffWithinAt.clm_bundle_flip (V₁ := E₀) (V₂ := E₀) (V₃ := Trivial B 𝕜) (b := b)
      (A := β₀) (s := Set.univ) hβ₀.contMDiffWithinAt)
  have hC := hflip.clm_bundle_comp (V₁ := E₁) (V₂ := E₀)
    (V₃ := fun z ↦ E₀ z →L[𝕜] Trivial B 𝕜 z) hT
  have hS := contMDiffWithinAt_univ.1
    (ContMDiffWithinAt.clm_bundle_flip (V₁ := E₁) (V₂ := E₀) (V₃ := Trivial B 𝕜) (b := b)
      (s := Set.univ) hC.contMDiffWithinAt)
  have hI := ContMDiffAt.clm_bundle_inverse (E₁ := E₁)
    (E₂ := fun z ↦ E₁ z →L[𝕜] Trivial B 𝕜 z) (b := b) (ϕ := β₁) hβ₁ hinv
  simp only [ContinuousLinearMap.bilinAdjoint_def]
  exact hI.clm_bundle_comp (V₂ := fun z ↦ E₁ z →L[𝕜] Trivial B 𝕜 z) hS

/-- For `C^n` fields `β₀`, `β₁` of bilinear forms on `E₀`, `E₁` along `b`, with `β₁` invertible
everywhere, and a `C^n` section `T` of `Hom(E₁, E₀)` along `b`, the adjoints
`ContinuousLinearMap.bilinAdjoint (β₀ m) (β₁ m) (T m)` form a `C^n` section of `Hom(E₀, E₁)`
along `b`. -/
theorem ContMDiff.clm_bundle_bilinAdjoint
    (hβ₀ : ContMDiff IM (IB.prod 𝓘(𝕜, F₀ →L[𝕜] F₀ →L[𝕜] 𝕜)) n
      (fun y ↦ TotalSpace.mk' (F₀ →L[𝕜] F₀ →L[𝕜] 𝕜)
        (E := fun z ↦ E₀ z →L[𝕜] E₀ z →L[𝕜] 𝕜) (b y) (β₀ y)))
    (hβ₁ : ContMDiff IM (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₁ →L[𝕜] 𝕜)) n
      (fun y ↦ TotalSpace.mk' (F₁ →L[𝕜] F₁ →L[𝕜] 𝕜)
        (E := fun z ↦ E₁ z →L[𝕜] E₁ z →L[𝕜] 𝕜) (b y) (β₁ y)))
    (hT : ContMDiff IM (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₀)) n
      (fun y ↦ TotalSpace.mk' (F₁ →L[𝕜] F₀) (E := fun z ↦ E₁ z →L[𝕜] E₀ z) (b y) (T y)))
    (hinv : ∀ m, (β₁ m).IsInvertible) :
    ContMDiff IM (IB.prod 𝓘(𝕜, F₀ →L[𝕜] F₁)) n
      (fun y ↦ TotalSpace.mk' (F₀ →L[𝕜] F₁) (E := fun z ↦ E₀ z →L[𝕜] E₁ z) (b y)
        (ContinuousLinearMap.bilinAdjoint (β₀ y) (β₁ y) (T y))) :=
  fun m ↦ (hβ₀ m).clm_bundle_bilinAdjoint (hβ₁ m) (hT m) (hinv m)

end Bundle

end
