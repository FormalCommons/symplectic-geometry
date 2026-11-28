/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Sphere
import TauCeti.Topology.Algebra.UnitaryGroup

/-!
# The orthogonal group as a group of diffeomorphisms of the sphere

Tau Ceti's `TauCeti.orthogonalToDiffSphere n m` restricts an orthogonal transformation of `ℝⁿ⁺¹`
to a `C^m` diffeomorphism of the unit sphere `Sⁿ`. It is continuous for the weak Whitney topology
and injective. Since `O(n + 1)` is compact and the diffeomorphism group is Hausdorff, it is a
closed embedding.

* `TauCeti.isClosedEmbedding_orthogonalToDiffSphere`: `O(n + 1)` is a closed subspace of the
  diffeomorphism group of `Sⁿ`.
* `TauCeti.isEmbedding_orthogonalToDiffSphere` and
  `TauCeti.isEmbedding_orthogonalToDiffSphere_comp_inclusion`: the embeddings of `O(n + 1)` and
  of `SO(n + 1)`.
-/

public section

open Metric Matrix
open scoped Manifold ContDiff TauCeti.DiffeomorphWeakWhitney

namespace TauCeti

/-- The restriction of orthogonal transformations of `ℝⁿ⁺¹` to the unit sphere is a closed
embedding of `O(n + 1)` in the diffeomorphism group of `Sⁿ` with the weak Whitney topology. -/
theorem isClosedEmbedding_orthogonalToDiffSphere (n : ℕ) (m : ℕ∞ω) :
    Topology.IsClosedEmbedding (orthogonalToDiffSphere n m) :=
  (continuous_orthogonalToDiffSphere n m).isClosedEmbedding (orthogonalToDiffSphere_injective n m)

/-- The restriction of orthogonal transformations of `ℝⁿ⁺¹` to the unit sphere embeds `O(n + 1)`
in the diffeomorphism group of `Sⁿ` with the weak Whitney topology. -/
theorem isEmbedding_orthogonalToDiffSphere (n : ℕ) (m : ℕ∞ω) :
    Topology.IsEmbedding (orthogonalToDiffSphere n m) :=
  (isClosedEmbedding_orthogonalToDiffSphere n m).isEmbedding

/-- The restriction of rotations of `ℝⁿ⁺¹` to the unit sphere embeds `SO(n + 1)` in the
diffeomorphism group of `Sⁿ` with the weak Whitney topology. -/
theorem isEmbedding_orthogonalToDiffSphere_comp_inclusion (n : ℕ) (m : ℕ∞ω) :
    Topology.IsEmbedding ((orthogonalToDiffSphere n m).comp
      (Submonoid.inclusion (specialUnitaryGroup_le_unitaryGroup (n := Fin (n + 1)) (α := ℝ)))) :=
  (isEmbedding_orthogonalToDiffSphere n m).comp
    (Topology.IsEmbedding.inclusion specialUnitaryGroup_le_unitaryGroup)

end TauCeti

end
