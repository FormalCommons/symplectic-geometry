/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.IsManifold.Basic
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Pullback
public import SymplecticGeometry.Topology.Algebra.Module.BilinearForm
public import TauCeti.Geometry.Manifold.Riemannian.Pullback.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.Bilinear.Section

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
`SymplecticGeometry/Geometry/Manifold/IsManifold/Basic.lean`, which this file imports.

The proof composes Tau Ceti's `ContMDiffAt.clm_bundle_flip`, `ContMDiffAt.clm_bundle_comp`
and `ContMDiffAt.clm_bundle_inverse`, as Tau Ceti's
`TauCeti.SmoothTwoForm.IsNondegenerate.skewPart` does for the tangent bundle.

## Left inverses of derivatives of immersions

As an application, `Manifold.IsImmersion.exists_contMDiff_leftInverse_mfderiv` gives a smooth
left inverse of the derivative of a smooth immersion `f : Q → M`, with `Q` of finite dimension,
as a section of the bundle of linear maps from the pull-back `f *ᵖ TM` to `TQ`. Given a smooth
field `β` of bilinear forms on `TM`, definite at the points of the image, the left inverse at
`q` is the adjoint of `df_q` for `β` at `f q` and for its pull-back `β(df_q ·, df_q ·)`, which
is definite since `df_q` is injective. The pull-back is smooth by Tau Ceti's
`Bundle.contMDiffAt_bilinearForm_pullback`, and the pull-back bundle `f *ᵖ TM` with its smooth
sections comes from `SymplecticGeometry/Geometry/Manifold/VectorBundle/Pullback.lean`; only this
application uses these two imports.
-/

public section

open Bundle
open scoped Manifold ContDiff

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
  have hflip := ContMDiffAt.clm_bundle_flip (V₁ := E₀) (V₂ := E₀) (V₃ := Trivial B 𝕜) (b := b)
    (A := β₀) hβ₀
  have hC := hflip.clm_bundle_comp (V₁ := E₁) (V₂ := E₀)
    (V₃ := fun z ↦ E₀ z →L[𝕜] Trivial B 𝕜 z) hT
  have hS := ContMDiffAt.clm_bundle_flip (V₁ := E₁) (V₂ := E₀) (V₃ := Trivial B 𝕜) (b := b) hC
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

section Immersion

variable {E E' H H' M Q K : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace Q] [ChartedSpace H' Q]
  [IsManifold J ∞ Q]
  [FunLike K Q M] [ContinuousMapClass K Q M]

/-- **A smooth left inverse of the derivative of an immersion.** Let `f : Q → M` be a smooth
immersion, with `Q` of finite dimension, and `β` a smooth field of bilinear forms on `TM` such that
`β u u = 0` only for `u = 0` at the points `f q`. Then there is a smooth section `S` of the bundle
of linear maps from the pull-back `f *ᵖ TM` to `TQ` with `S_q ∘ df_q = id` at every `q`. -/
theorem Manifold.IsImmersion.exists_contMDiff_leftInverse_mfderiv {f : K}
    (hf : IsImmersion J I ∞ f) {β : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    (hβ : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) x (β x)))
    (hdef : ∀ q (u : TangentSpace I (f q)), β (f q) u u = 0 → u = 0) :
    ∃ S : ∀ q, TangentSpace I (f q) →L[ℝ] TangentSpace J q,
      ContMDiff J (J.prod 𝓘(ℝ, E →L[ℝ] E')) ∞ (fun q ↦ TotalSpace.mk' (E →L[ℝ] E')
        (E := fun q ↦ ((f : Q → M) *ᵖ (TangentSpace I)) q →L[ℝ] TangentSpace J q) q (S q)) ∧
      ∀ q, Function.LeftInverse (S q) (mfderiv J I f q) := by
  have : ContMDiffVectorBundle ∞ E ((f : Q → M) *ᵖ (TangentSpace I)) J :=
    Bundle.Pullback.contMDiffVectorBundle (E := TangentSpace I) hf.contMDiff
  -- `S` is the adjoint of `df` for `β` along `f` and its pull-back `h = β(df ·, df ·)` to `TQ`.
  set T : ∀ q, TangentSpace J q →L[ℝ] TangentSpace I (f q) := fun q ↦ mfderiv J I f q
  set h : ∀ q, TangentSpace J q →L[ℝ] TangentSpace J q →L[ℝ] ℝ :=
    fun q ↦ (ContinuousLinearMap.precomp ℝ (T q)).comp ((β (f q)).comp (T q))
  have hβf : ContMDiff J (J.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun q ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun q ↦ ((f : Q → M) *ᵖ (TangentSpace I)) q →L[ℝ]
          ((f : Q → M) *ᵖ (TangentSpace I)) q →L[ℝ] ℝ) q (β (f q))) :=
    (Bundle.Pullback.contMDiff_bilinear_section_iff f hf.contMDiff _).mpr (hβ.comp hf.contMDiff)
  have hh : ContMDiff J (J.prod 𝓘(ℝ, E' →L[ℝ] E' →L[ℝ] ℝ)) ∞
      (fun q ↦ TotalSpace.mk' (E' →L[ℝ] E' →L[ℝ] ℝ)
        (E := fun q ↦ TangentSpace J q →L[ℝ] TangentSpace J q →L[ℝ] ℝ) q (h q)) := fun q ↦
    Bundle.contMDiffAt_bilinearForm_pullback (hβ (f q)) (hf.contMDiff q)
  have hT : ContMDiff J (J.prod 𝓘(ℝ, E' →L[ℝ] E)) ∞ (fun q ↦ TotalSpace.mk' (E' →L[ℝ] E)
      (E := fun q ↦ TangentSpace J q →L[ℝ] ((f : Q → M) *ᵖ (TangentSpace I)) q) q (T q)) :=
    (TauCeti.contMDiff_hom_bundle_iff (E₂ := (f : Q → M) *ᵖ (TangentSpace I)) _).2
      (Bundle.Pullback.contMDiff_totalSpace_mfderiv f hf.contMDiff)
  -- `h` is definite, since `β` is definite on the image and `df` is injective.
  have hdef' (q : Q) (x : TangentSpace J q) (hx : h q x x = 0) : x = 0 :=
    hf.mfderiv_injective (by simp) q ((map_zero (T q)).symm ▸ hdef q _ hx)
  have hinv (q : Q) : (h q).IsInvertible := by
    rw [ContinuousLinearMap.isInvertible_iff_nondegenerate_toBilinForm]
    exact ⟨fun x hx ↦ hdef' q x (hx x), fun y hy ↦ hdef' q y (hy y)⟩
  refine ⟨fun q ↦ ContinuousLinearMap.bilinAdjoint (β (f q)) (h q) (T q), ?_, fun q v ↦ ?_⟩
  · exact ContMDiff.clm_bundle_bilinAdjoint (E₀ := (f : Q → M) *ᵖ (TangentSpace I))
      (E₁ := TangentSpace J) hβf hh hT hinv
  · refine (hinv q).injective (ContinuousLinearMap.ext fun y ↦ ?_)
    rw [ContinuousLinearMap.apply_bilinAdjoint_apply (hinv q)]
    simp only [h, T, ContinuousLinearMap.comp_apply, ContinuousLinearMap.precomp_apply]

end Immersion

end
