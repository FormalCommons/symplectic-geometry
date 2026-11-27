/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Topology.VectorBundle.Complex.FirstChernClass
import SymplecticGeometry.Geometry.Manifold.VectorBundle.FiniteTrivializingCover
import SymplecticGeometry.Topology.VectorBundle.Complex.ChernClass.FirstChernClass

/-!
# The Whitney formula for the first Chern class over manifolds

Over a Hausdorff, σ-compact space `B` charted on `H`, with a model with corners
`I : ModelWithCorners ℝ EB H` and `EB` finite-dimensional, the first Chern class
`TauCeti.firstChernClass` is additive on direct sums of complex vector bundles
(`SymplecticGeometry.Bundle.firstChernClass_prod_of_chartedSpace`). Neither smoothness nor
compactness is assumed, and the model may have corners.

It is a case of `SymplecticGeometry.Bundle.firstChernClass_prod_of_hasFiniteTrivializingCover`:
the bundles have finite trivializing covers by
`SymplecticGeometry.Bundle.HasFiniteTrivializingCover.of_chartedSpace`, and the base is normal
since it is locally compact, σ-compact and Hausdorff, hence paracompact.

## Main results

* `SymplecticGeometry.Bundle.firstChernClass_prod_of_chartedSpace`: `c₁(E₁ ⊕ E₂) = c₁(E₁) + c₁(E₂)`.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press (1974), §14 (the first Chern class through the determinant line).
* [A. Hatcher, *Vector Bundles and K-Theory*][Hatcher2017], version 2.2, Theorem 3.2 (the
  Whitney sum formula).
-/

public section

open Bundle
open TauCeti (firstChernClass)

namespace SymplecticGeometry.Bundle

variable {B : Type} [TopologicalSpace B]
  {EB H : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
  [TopologicalSpace H]
  {G₁ : Type*} [NormedAddCommGroup G₁] [NormedSpace ℂ G₁] [FiniteDimensional ℂ G₁]
  {E₁ : B → Type} [∀ b, AddCommGroup (E₁ b)] [∀ b, Module ℂ (E₁ b)]
  [∀ b, TopologicalSpace (E₁ b)] [TopologicalSpace (TotalSpace G₁ E₁)]
  [FiberBundle G₁ E₁] [VectorBundle ℂ G₁ E₁]
  {G₂ : Type*} [NormedAddCommGroup G₂] [NormedSpace ℂ G₂] [FiniteDimensional ℂ G₂]
  {E₂ : B → Type} [∀ b, AddCommGroup (E₂ b)] [∀ b, Module ℂ (E₂ b)]
  [∀ b, TopologicalSpace (E₂ b)] [TopologicalSpace (TotalSpace G₂ E₂)]
  [FiberBundle G₂ E₂] [VectorBundle ℂ G₂ E₂]

/-- **The Whitney formula for the first Chern class over manifolds.** Over a Hausdorff,
σ-compact space charted on `H`, with a model with corners `I : ModelWithCorners ℝ EB H` and `EB`
finite-dimensional, the first Chern class of `E₁ ⊕ E₂` is the sum of those of `E₁` and `E₂`.

Milestone: *First Chern class of a complex vector bundle*. -/
theorem firstChernClass_prod_of_chartedSpace (I : ModelWithCorners ℝ EB H)
    [ChartedSpace H B] [T2Space B] [SigmaCompactSpace B] :
    firstChernClass (G₁ × G₂) (E₁ ×ᵇ E₂) = firstChernClass G₁ E₁ + firstChernClass G₂ E₂ :=
  have : LocallyCompactSpace B := Manifold.locallyCompact_of_finiteDimensional I
  firstChernClass_prod_of_hasFiniteTrivializingCover (.of_chartedSpace I) (.of_chartedSpace I)

end SymplecticGeometry.Bundle

end
