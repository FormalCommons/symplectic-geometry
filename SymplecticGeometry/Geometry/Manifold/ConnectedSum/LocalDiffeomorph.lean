/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.ConnectedSum.Smooth
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic

/-!
# Local diffeomorphisms out of a connected sum

A map `f` out of Tau Ceti's connected sum `TauCeti.ConnectedSum e₁ e₂`, with the charts of
`TauCeti.ConnectedSum.chartedSpace`, is a `C^n` local diffeomorphism as soon as its composites
with the inclusions `TauCeti.ConnectedSum.inl` and `TauCeti.ConnectedSum.inr` of the two punctured
summands are: every point of the connected sum comes from one of the summands, and both inclusions
are `C^n` local diffeomorphisms (`TauCeti.ConnectedSum.isLocalDiffeomorph_inl`,
`TauCeti.ConnectedSum.isLocalDiffeomorph_inr`).

## Main results

* `TauCeti.ConnectedSum.isLocalDiffeomorph_of_comp_inl_of_comp_inr`: the criterion above.

## References

* [A. Kosinski, *Differential Manifolds*][Kosinski1993], Chapter VI, Section 1.
-/

public section

open Topology
open scoped Manifold

namespace TauCeti.ConnectedSum

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T1Space M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [T1Space N] [ChartedSpace H N]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H' X]
  {e₁ : E → M} {e₂ : E → N} {n : ℕ∞} [IsManifold I n M] [IsManifold I n N]

/-- A map out of the connected sum along `e₁` and `e₂` is a `C^n` local diffeomorphism once its
composites with the inclusions of the two punctured summands are. -/
theorem isLocalDiffeomorph_of_comp_inl_of_comp_inr (h₁ : IsOpenEmbedding e₁)
    (h₂ : IsOpenEmbedding e₂) (d₁ : IsLocalDiffeomorph 𝓘(ℝ, E) I n e₁)
    (d₂ : IsLocalDiffeomorph 𝓘(ℝ, E) I n e₂) {f : ConnectedSum e₁ e₂ → X}
    (hl : letI := chartedSpace (H := H) h₁ h₂; IsLocalDiffeomorph I J n (f ∘ inl e₁ e₂))
    (hr : letI := chartedSpace (H := H) h₁ h₂; IsLocalDiffeomorph I J n (f ∘ inr e₁ e₂)) :
    letI := chartedSpace (H := H) h₁ h₂
    IsLocalDiffeomorph I J n f := by
  let := chartedSpace (H := H) h₁ h₂
  intro p
  obtain ⟨x | y, rfl⟩ := mk_surjective e₁ e₂ p
  · exact mk_inl e₁ e₂ x ▸ (hl x).of_comp_right (isLocalDiffeomorph_inl h₁ h₂ d₁ d₂ x)
  · exact mk_inr e₁ e₂ y ▸ (hr y).of_comp_right (isLocalDiffeomorph_inr h₁ h₂ d₁ d₂ y)

end TauCeti.ConnectedSum

end
