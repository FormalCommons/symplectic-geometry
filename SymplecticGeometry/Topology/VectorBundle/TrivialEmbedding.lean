/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Topology.VectorBundle.TrivialEmbedding

/-!
# A chosen embedding of a vector bundle into a trivial bundle

Over a compact normal (for instance compact Hausdorff) base, Tau Ceti's
`TauCeti.exists_continuous_injective_fin_of_compactSpace` gives a fibrewise injection of a
finite-rank vector bundle `E` into some `𝕜ᴺ`, continuous on the total space. This file chooses
one, and reads it in the Euclidean space `EuclideanSpace 𝕜 (Fin N)`, so that orthogonal
projections in the trivial bundle are available.

## Main definitions

* `SymplecticGeometry.Bundle.trivialEmbeddingDim 𝕜 G E`: the dimension `N` of the target.
* `SymplecticGeometry.Bundle.trivialEmbedding 𝕜 G E b`: the chosen injection of `E b` into
  `EuclideanSpace 𝕜 (Fin (trivialEmbeddingDim 𝕜 G E))`.

## Main results

* `SymplecticGeometry.Bundle.continuous_trivialEmbedding`: it is continuous on the total space.
* `SymplecticGeometry.Bundle.injective_trivialEmbedding`: it is injective on each fibre.

## References

* A. Hatcher, *Vector Bundles and K-Theory*, Proposition 1.4, whose proof embeds a bundle over a
  compact Hausdorff base in a trivial bundle.
-/

public section

noncomputable section

open Bundle Function

namespace SymplecticGeometry.Bundle

variable {𝕜 : Type*} [RCLike 𝕜] {B : Type*} [TopologicalSpace B] [CompactSpace B] [NormalSpace B]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [FiniteDimensional 𝕜 G]
  {E : B → Type*} [∀ b, AddCommGroup (E b)] [∀ b, Module 𝕜 (E b)] [∀ b, TopologicalSpace (E b)]
  [TopologicalSpace (TotalSpace G E)] [FiberBundle G E] [VectorBundle 𝕜 G E]

variable (𝕜 G E) in
/-- The dimension `N` of the Euclidean space `EuclideanSpace 𝕜 (Fin N)` into which
`trivialEmbedding` embeds the fibres of a vector bundle over a compact normal base. -/
def trivialEmbeddingDim : ℕ :=
  (TauCeti.exists_continuous_injective_fin_of_compactSpace (𝕜 := 𝕜) (F := G) (E := E)).choose

variable (𝕜 G E) in
/-- A chosen fibrewise injection of a vector bundle `E` over a compact normal base into a
Euclidean space `EuclideanSpace 𝕜 (Fin N)`, continuous on the total space: Tau Ceti's
`TauCeti.exists_continuous_injective_fin_of_compactSpace`, read in the Euclidean structure. -/
def trivialEmbedding (b : B) : E b →L[𝕜] EuclideanSpace 𝕜 (Fin (trivialEmbeddingDim 𝕜 G E)) :=
  (EuclideanSpace.equiv _ 𝕜).symm.toContinuousLinearMap ∘L
    (TauCeti.exists_continuous_injective_fin_of_compactSpace (𝕜 := 𝕜) (F := G)
      (E := E)).choose_spec.choose b

variable (𝕜 G E) in
/-- The chosen embedding `trivialEmbedding` is continuous on the total space of `E`. -/
theorem continuous_trivialEmbedding :
    Continuous fun v : TotalSpace G E ↦ trivialEmbedding 𝕜 G E v.proj v.snd :=
  (EuclideanSpace.equiv _ 𝕜).symm.continuous.comp
    (TauCeti.exists_continuous_injective_fin_of_compactSpace (𝕜 := 𝕜) (F := G)
      (E := E)).choose_spec.choose_spec.1

variable (𝕜 G E) in
/-- The chosen embedding `trivialEmbedding` is injective on each fibre. -/
theorem injective_trivialEmbedding (b : B) : Injective (trivialEmbedding 𝕜 G E b) :=
  (EuclideanSpace.equiv _ 𝕜).symm.injective.comp
    ((TauCeti.exists_continuous_injective_fin_of_compactSpace (𝕜 := 𝕜) (F := G)
      (E := E)).choose_spec.choose_spec.2 b)

end SymplecticGeometry.Bundle

end
