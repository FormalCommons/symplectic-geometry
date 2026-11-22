/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.VectorBundle.TensorProduct.Basic
public import SymplecticGeometry.Topology.VectorBundle.Pullback

/-!
# Tensor products of pulled-back vector bundles

For finite-rank vector bundles `E₁` and `E₂` over `B` and a continuous map `f : B' → B`, the
fibres of Tau Ceti's tensor product bundle of the pull-backs `f *ᵖ E₁` and `f *ᵖ E₂` are those of
`E₁ ⊗ E₂` at the image points. This file shows that the identity of these fibres is continuous on
total spaces, as a map over `f`:

* `TensorProduct.inCoordinates_pullback`: for bundles `E₁` over `B₁` and `E₂` over `B₂` and maps
  `f : B₁' → B₁` and `g : B₂' → B₂`, the coordinate expression of a tensor of the pull-backs
  `f *ᵖ E₁` and `g *ᵖ E₂` is that of the same tensor of `E₁` and `E₂`, at the image points;
* `TauCeti.continuous_tensorProduct_pullback`: the map from the total space of
  `f *ᵖ E₁ ⊗ f *ᵖ E₂` to that of `E₁ ⊗ E₂` which keeps the vector and applies `f` to the base
  point is continuous.
-/

public section

noncomputable section

open Bundle Topology
open scoped TensorProduct

namespace TensorProduct

variable {𝕜 B₁ B₂ B₁' B₂' : Type*} [NontriviallyNormedField 𝕜]
  [TopologicalSpace B₁] [TopologicalSpace B₂] [TopologicalSpace B₁'] [TopologicalSpace B₂']
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] {E₁ : B₁ → Type*}
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [∀ x, TopologicalSpace (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] {E₂ : B₂ → Type*}
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)] [∀ x, TopologicalSpace (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]

/-- The coordinate expression of a tensor of the pull-backs `f *ᵖ E₁` and `g *ᵖ E₂`, centred at
`x₀` and `y₀`, is that of the same tensor of `E₁` and `E₂`, centred at `f x₀` and `g y₀`. -/
theorem inCoordinates_pullback (f : C(B₁', B₁)) (g : C(B₂', B₂)) (x₀ x : B₁') (y₀ y : B₂')
    (t : (f *ᵖ E₁) x ⊗[𝕜] (g *ᵖ E₂) y) :
    inCoordinates F₁ (f *ᵖ E₁) F₂ (g *ᵖ E₂) x₀ x y₀ y t =
      inCoordinates F₁ E₁ F₂ E₂ (f x₀) (f x) (g y₀) (g y) t := by
  induction t using _root_.TensorProduct.inductionOn with
  | tmul v w =>
    simp only [inCoordinates_tmul, trivializationAt, FiberBundle.pullback_trivializationAt',
      Bundle.Trivialization.linearMapAt_pullback]
    exact (inCoordinates_tmul (f x₀) (f x) (g y₀) (g y) v w).symm
  | add t t' ht ht' =>
    rw [map_add, ht, ht']
    exact (map_add (inCoordinates F₁ E₁ F₂ E₂ (f x₀) (f x) (g y₀) (g y)) t t').symm

end TensorProduct

namespace TauCeti

variable {𝕜 B B' : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B] [TopologicalSpace B']
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] {E₁ : B → Type*}
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [∀ x, TopologicalSpace (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] {E₂ : B → Type*}
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)] [∀ x, TopologicalSpace (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  (f : C(B', B))
  [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F₁] [FiniteDimensional 𝕜 F₂]
  [∀ x, TopologicalSpace (E₁ x ⊗[𝕜] E₂ x)] [∀ x, IsModuleTopology 𝕜 (E₁ x ⊗[𝕜] E₂ x)]
  [∀ x, TopologicalSpace ((f *ᵖ E₁) x ⊗[𝕜] (f *ᵖ E₂) x)]
  [∀ x, IsModuleTopology 𝕜 ((f *ᵖ E₁) x ⊗[𝕜] (f *ᵖ E₂) x)]

/-- **The tensor product of pull-backs maps to the tensor product.** The map from the total space
of `f *ᵖ E₁ ⊗ f *ᵖ E₂` to that of `E₁ ⊗ E₂` that keeps the vector of the fibre over `x`, a vector
of the fibre of `E₁ ⊗ E₂` over `f x`, is continuous. -/
theorem continuous_tensorProduct_pullback :
    Continuous fun p : TotalSpace (ProjectiveTensor 𝕜 F₁ F₂)
        (fun x ↦ (f *ᵖ E₁) x ⊗[𝕜] (f *ᵖ E₂) x) ↦
      TotalSpace.mk' (ProjectiveTensor 𝕜 F₁ F₂) (E := fun y ↦ E₁ y ⊗[𝕜] E₂ y) (f p.proj) p.snd := by
  refine continuous_iff_continuousAt.2 fun p₀ ↦ ?_
  have h := (continuousAt_tensorProduct_bundle (F₁ := F₁) (F₂ := F₂) id (x₀ := p₀)).1
    continuousAt_id
  rw [continuousAt_tensorProduct_bundle]
  refine ⟨(f.continuous.comp (FiberBundle.continuous_proj _ _)).continuousAt, ?_⟩
  simpa only [id, TensorProduct.inCoordinates_pullback] using h.2

end TauCeti
