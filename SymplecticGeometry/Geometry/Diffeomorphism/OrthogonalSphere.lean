/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Sphere
public import TauCeti.LinearAlgebra.Matrix.OrthogonalGroup.Basic
import TauCeti.Topology.Algebra.UnitaryGroup

/-!
# The orthogonal group as a group of diffeomorphisms of the sphere

Tau Ceti's `TauCeti.orthogonalToDiffSphere n m` restricts an orthogonal transformation of `ℝⁿ⁺¹`
to a `C^m` diffeomorphism of the unit sphere `Sⁿ`. It is continuous for the weak Whitney topology
and injective. Since `O(n + 1)` is compact and the diffeomorphism group is Hausdorff, it is a
closed embedding. This file also names its restriction to the rotations `SO(n + 1)`.

* `TauCeti.isClosedEmbedding_orthogonalToDiffSphere`: `O(n + 1)` is a closed subspace of the
  diffeomorphism group of `Sⁿ`.
* `TauCeti.isEmbedding_orthogonalToDiffSphere`: the embedding of `O(n + 1)`.
* `TauCeti.specialOrthogonalToDiffSphere n m : SO(n + 1) →* Diff(Sⁿ)`: the restriction of
  rotations to the unit sphere.
* `TauCeti.isClosedEmbedding_specialOrthogonalToDiffSphere` and
  `TauCeti.isEmbedding_specialOrthogonalToDiffSphere`: `SO(n + 1)` is a closed subspace of the
  diffeomorphism group of `Sⁿ`.
-/

public section

open Metric Matrix
open scoped Manifold ContDiff TauCeti.DiffeomorphWeakWhitney

namespace TauCeti

variable (n : ℕ) (m : ℕ∞ω)

/-- The restriction of orthogonal transformations of `ℝⁿ⁺¹` to the unit sphere is a closed
embedding of `O(n + 1)` in the diffeomorphism group of `Sⁿ` with the weak Whitney topology. -/
theorem isClosedEmbedding_orthogonalToDiffSphere :
    Topology.IsClosedEmbedding (orthogonalToDiffSphere n m) :=
  (continuous_orthogonalToDiffSphere n m).isClosedEmbedding (orthogonalToDiffSphere_injective n m)

/-- The restriction of orthogonal transformations of `ℝⁿ⁺¹` to the unit sphere embeds `O(n + 1)`
in the diffeomorphism group of `Sⁿ` with the weak Whitney topology. -/
theorem isEmbedding_orthogonalToDiffSphere :
    Topology.IsEmbedding (orthogonalToDiffSphere n m) :=
  (isClosedEmbedding_orthogonalToDiffSphere n m).isEmbedding

/-- The restriction of rotations of `ℝⁿ⁺¹` to the unit sphere, `SO(n + 1) →* Diff(Sⁿ)`: the
restriction `TauCeti.orthogonalToDiffSphere n m` of `O(n + 1)`, on the subgroup `SO(n + 1)`. -/
noncomputable def specialOrthogonalToDiffSphere :
    specialOrthogonalGroup (Fin (n + 1)) ℝ →*
      Diff (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) m :=
  (orthogonalToDiffSphere n m).comp specialOrthogonalGroup.toOrthogonalGroup

theorem specialOrthogonalToDiffSphere_def :
    specialOrthogonalToDiffSphere n m =
      (orthogonalToDiffSphere n m).comp specialOrthogonalGroup.toOrthogonalGroup :=
  (rfl)

/-- The restriction of a rotation to the unit sphere is its restriction as an orthogonal
transformation. -/
@[simp]
theorem specialOrthogonalToDiffSphere_apply (A : specialOrthogonalGroup (Fin (n + 1)) ℝ) :
    specialOrthogonalToDiffSphere n m A =
      orthogonalToDiffSphere n m (specialOrthogonalGroup.toOrthogonalGroup A) :=
  (rfl)

/-- The restriction of rotations of `ℝⁿ⁺¹` to the unit sphere is injective. -/
theorem specialOrthogonalToDiffSphere_injective :
    Function.Injective (specialOrthogonalToDiffSphere n m) := by
  rw [specialOrthogonalToDiffSphere_def, MonoidHom.coe_comp]
  refine (orthogonalToDiffSphere_injective n m).comp fun A B h ↦ Subtype.ext ?_
  simpa using congrArg Subtype.val h

/-- The restriction of rotations of `ℝⁿ⁺¹` to the unit sphere is continuous for the weak Whitney
topology. -/
theorem continuous_specialOrthogonalToDiffSphere :
    Continuous (specialOrthogonalToDiffSphere n m) := by
  rw [specialOrthogonalToDiffSphere_def, MonoidHom.coe_comp]
  refine (continuous_orthogonalToDiffSphere n m).comp (continuous_induced_rng.2 ?_)
  simpa [Function.comp_def] using continuous_subtypeVal

/-- The restriction of rotations of `ℝⁿ⁺¹` to the unit sphere is a closed embedding of
`SO(n + 1)` in the diffeomorphism group of `Sⁿ` with the weak Whitney topology. -/
theorem isClosedEmbedding_specialOrthogonalToDiffSphere :
    Topology.IsClosedEmbedding (specialOrthogonalToDiffSphere n m) :=
  (continuous_specialOrthogonalToDiffSphere n m).isClosedEmbedding
    (specialOrthogonalToDiffSphere_injective n m)

/-- The restriction of rotations of `ℝⁿ⁺¹` to the unit sphere embeds `SO(n + 1)` in the
diffeomorphism group of `Sⁿ` with the weak Whitney topology. -/
theorem isEmbedding_specialOrthogonalToDiffSphere :
    Topology.IsEmbedding (specialOrthogonalToDiffSphere n m) :=
  (isClosedEmbedding_specialOrthogonalToDiffSphere n m).isEmbedding

end TauCeti

end
