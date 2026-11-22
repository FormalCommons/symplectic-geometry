/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.VectorBundle.TensorProduct.Basic
public import TauCeti.Topology.VectorBundle.Pullback

/-!
# Tensor products of pulled-back vector bundles

For finite-rank vector bundles `E₁` and `E₂` over `B` and a continuous map `f : B' → B`, the
fibres of Tau Ceti's tensor product bundle of the pull-backs `f *ᵖ E₁` and `f *ᵖ E₂` are those of
`E₁ ⊗ E₂` at the image points. This file shows that the identity of these fibres is continuous on
total spaces, as a map over `f`:

* `TensorProduct.inCoordinates_pullback`: the coordinate expression of a tensor of the pull-backs
  is that of the same tensor in `E₁ ⊗ E₂`, at the image points;
* `TauCeti.continuous_tensorProduct_pullback`: the map from the total space of
  `f *ᵖ E₁ ⊗ f *ᵖ E₂` to that of `E₁ ⊗ E₂` which keeps the vector and applies `f` to the base
  point is continuous.
-/

public section

noncomputable section

open Bundle Topology
open scoped TensorProduct

variable {𝕜 B B' : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B] [TopologicalSpace B']
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] {E₁ : B → Type*}
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [∀ x, TopologicalSpace (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] {E₂ : B → Type*}
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)] [∀ x, TopologicalSpace (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  (f : C(B', B))

namespace Bundle.Trivialization

omit [∀ x, TopologicalSpace (E₁ x)] [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁] in
/-- A pulled-back linear trivialization reads a vector of the fibre over `x` as the original
trivialization reads it over `f x`. -/
@[simp]
theorem linearMapAt_pullback (e : Trivialization F₁ (π F₁ E₁)) [e.IsLinear 𝕜] (x : B')
    (v : (f *ᵖ E₁) x) : (e.pullback f).linearMapAt 𝕜 x v = e.linearMapAt 𝕜 (f x) v := by
  rw [linearMapAt_apply (e.pullback f), linearMapAt_apply e (b := f x) (y := (v : E₁ (f x)))]
  -- `x ∈ f ⁻¹' e.baseSet` is `f x ∈ e.baseSet` and `Pullback.lift f ⟨x, v⟩` is `⟨f x, v⟩`, by
  -- definition; the fibre types differ by the synonym `*ᵖ`, so `simp` does not rewrite them.
  rfl

end Bundle.Trivialization

namespace TensorProduct

/-- The coordinate expression of a tensor of the pull-backs `f *ᵖ E₁` and `f *ᵖ E₂`, centred at
`x₀`, is that of the same tensor in `E₁ ⊗ E₂`, centred at `f x₀`. -/
theorem inCoordinates_pullback (x₀ x : B') (t : (f *ᵖ E₁) x ⊗[𝕜] (f *ᵖ E₂) x) :
    inCoordinates F₁ (f *ᵖ E₁) F₂ (f *ᵖ E₂) x₀ x x₀ x t =
      inCoordinates F₁ E₁ F₂ E₂ (f x₀) (f x) (f x₀) (f x) t := by
  induction t using _root_.TensorProduct.inductionOn with
  | tmul v w =>
    simp only [inCoordinates_tmul, trivializationAt, FiberBundle.pullback_trivializationAt',
      Bundle.Trivialization.linearMapAt_pullback]
    exact (inCoordinates_tmul (f x₀) (f x) (f x₀) (f x) v w).symm
  | add t t' ht ht' =>
    rw [map_add, ht, ht']
    exact (map_add (inCoordinates F₁ E₁ F₂ E₂ (f x₀) (f x) (f x₀) (f x)) t t').symm

end TensorProduct

namespace TauCeti

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F₁] [FiniteDimensional 𝕜 F₂]
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
