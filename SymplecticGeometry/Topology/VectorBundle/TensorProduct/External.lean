/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.VectorBundle.Pullback
public import TauCeti.Topology.VectorBundle.TensorProduct.Basic

/-!
# External tensor products of vector bundles

Let `E₁ → B₁` and `E₂ → B₂` be finite-rank vector bundles over a complete nontrivially normed
field `𝕜`, with model fibres `F₁` and `F₂`. Their external tensor product `E₁ ⊠ E₂` is the bundle
over `B₁ × B₂` whose fibre over `(x, y)` is `E₁ x ⊗[𝕜] E₂ y`: Tau Ceti's tensor product bundle
(`TauCeti/Topology/VectorBundle/TensorProduct/Basic.lean`) of the pull-backs of `E₁` and `E₂`
along the two projections, `ContinuousMap.fst` and `ContinuousMap.snd`, modelled on
`TauCeti.ProjectiveTensor 𝕜 F₁ F₂`.

This file restates Tau Ceti's instances `Bundle.TensorProduct.topologicalSpaceTotalSpace`,
`Bundle.TensorProduct.fiberBundle` and `Bundle.TensorProduct.vectorBundle` for this family. Tau
Ceti's instances apply to it, but instance search does not find them for concrete bundles such as
the tautological lines of two projective spaces: the instance term, which contains the
`FiberBundle` and `VectorBundle` instances of both pull-backs, exceeds the size limit of instance
search. The instances here take those of `E₁` and `E₂` themselves, so the terms stay small. Each
is Tau Ceti's instance, so nothing is changed up to definitional equality.

The rank of the model fibre is the product of the ranks (`TauCeti.ProjectiveTensor.finrank_eq_mul`).

As in Tau Ceti's file, the fibres `E₁ x ⊗[𝕜] E₂ y` are assumed to carry the `𝕜`-module topology;
opening `TauCeti.ModuleTopology` provides it.
-/

public section

noncomputable section

open Bundle Module
open scoped TensorProduct

/-- The projective tensor product `E ⊗ F` of two normed spaces has rank `finrank 𝕜 E * finrank 𝕜 F`,
as the algebraic one does. -/
theorem TauCeti.ProjectiveTensor.finrank_eq_mul (𝕜 E F : Type*) [NormedField 𝕜]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] :
    finrank 𝕜 (TauCeti.ProjectiveTensor 𝕜 E F) = finrank 𝕜 E * finrank 𝕜 F := by
  rw [(TauCeti.ProjectiveTensor.linearEquiv 𝕜 E F).finrank_eq, finrank_tensorProduct]

namespace Bundle.TensorProduct

variable {𝕜 B₁ B₂ : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [TopologicalSpace B₁] [TopologicalSpace B₂]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
  {E₁ : B₁ → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [∀ x, TopologicalSpace (E₁ x)] [TopologicalSpace (TotalSpace F₁ E₁)] [FiberBundle F₁ E₁]
  [VectorBundle 𝕜 F₁ E₁] [∀ x, Nonempty (E₁ x)]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]
  {E₂ : B₂ → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [∀ x, TopologicalSpace (E₂ x)] [TopologicalSpace (TotalSpace F₂ E₂)] [FiberBundle F₂ E₂]
  [VectorBundle 𝕜 F₂ E₂] [∀ x, Nonempty (E₂ x)]
  [∀ x : B₁ × B₂, TopologicalSpace (((ContinuousMap.fst : C(B₁ × B₂, B₁)) *ᵖ E₁) x ⊗[𝕜]
    ((ContinuousMap.snd : C(B₁ × B₂, B₂)) *ᵖ E₂) x)]
  [∀ x : B₁ × B₂, IsModuleTopology 𝕜 (((ContinuousMap.fst : C(B₁ × B₂, B₁)) *ᵖ E₁) x ⊗[𝕜]
    ((ContinuousMap.snd : C(B₁ × B₂, B₂)) *ᵖ E₂) x)]

/-- The total-space topology of the external tensor product `E₁ ⊠ E₂` over `B₁ × B₂`: Tau Ceti's
`Bundle.TensorProduct.topologicalSpaceTotalSpace` for the pull-backs of `E₁` and `E₂` along the
two projections. -/
instance topologicalSpaceTotalSpaceExternal :
    TopologicalSpace (TotalSpace (TauCeti.ProjectiveTensor 𝕜 F₁ F₂) fun x : B₁ × B₂ ↦
      ((ContinuousMap.fst : C(B₁ × B₂, B₁)) *ᵖ E₁) x ⊗[𝕜]
        ((ContinuousMap.snd : C(B₁ × B₂, B₂)) *ᵖ E₂) x) :=
  topologicalSpaceTotalSpace 𝕜 F₁ _ F₂ _

/-- The external tensor product `E₁ ⊠ E₂` over `B₁ × B₂` is a fibre bundle: Tau Ceti's
`Bundle.TensorProduct.fiberBundle` for the pull-backs of `E₁` and `E₂` along the two
projections. -/
instance fiberBundleExternal :
    FiberBundle (TauCeti.ProjectiveTensor 𝕜 F₁ F₂) fun x : B₁ × B₂ ↦
      ((ContinuousMap.fst : C(B₁ × B₂, B₁)) *ᵖ E₁) x ⊗[𝕜]
        ((ContinuousMap.snd : C(B₁ × B₂, B₂)) *ᵖ E₂) x :=
  fiberBundle 𝕜 F₁ _ F₂ _

/-- The external tensor product `E₁ ⊠ E₂` over `B₁ × B₂` is a vector bundle: Tau Ceti's
`Bundle.TensorProduct.vectorBundle` for the pull-backs of `E₁` and `E₂` along the two
projections. -/
instance vectorBundleExternal :
    VectorBundle 𝕜 (TauCeti.ProjectiveTensor 𝕜 F₁ F₂) fun x : B₁ × B₂ ↦
      ((ContinuousMap.fst : C(B₁ × B₂, B₁)) *ᵖ E₁) x ⊗[𝕜]
        ((ContinuousMap.snd : C(B₁ × B₂, B₂)) *ᵖ E₂) x :=
  vectorBundle 𝕜 F₁ _ F₂ _

end Bundle.TensorProduct

end
