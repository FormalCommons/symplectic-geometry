/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.Grassmannian.Plucker
public import TauCeti.Topology.Grassmannian.Tautological

/-!
# Orthogonal projections on the finite Grassmannian

For `RCLike 𝕜`, Tau Ceti sends a point `V` of `finiteGrassmannian 𝕜 r N` to the orthogonal
projection of `EuclideanSpace 𝕜 (Fin N)` onto `V`, a continuous and injective map. Since the
finite Grassmannian is compact and Hausdorff, this map is a closed embedding: the topology of
`finiteGrassmannian 𝕜 r N`, defined through orthonormal frames, is the topology of orthogonal
projections.

## Main results

* `TauCeti.finiteGrassmannian.isClosedEmbedding_starProjection_toEuclidean`: the map
  `V ↦ V.toEuclidean.starProjection` is a closed embedding.

## References

* J. Milnor and J. Stasheff, *Characteristic Classes*, Princeton University Press, 1974, §5.
-/

public section

open Topology

namespace TauCeti.finiteGrassmannian

variable {𝕜 : Type*} [RCLike 𝕜] {r N : ℕ}

/-- The orthogonal projection onto a point of the finite Grassmannian `finiteGrassmannian 𝕜 r N`
is a closed embedding of the Grassmannian into the continuous linear operators of
`EuclideanSpace 𝕜 (Fin N)`. -/
theorem isClosedEmbedding_starProjection_toEuclidean :
    IsClosedEmbedding fun V : finiteGrassmannian 𝕜 r N ↦ V.toEuclidean.starProjection :=
  continuous_starProjection_toEuclidean.isClosedEmbedding
    fun _ _ h ↦ toEuclidean_injective (Submodule.starProjection_inj.mp h)

end TauCeti.finiteGrassmannian

end
