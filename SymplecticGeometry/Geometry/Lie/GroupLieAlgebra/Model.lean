/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Basic
public import TauCeti.Topology.Algebra.Lie.Bracket

/-!
# The bracket on the model space of a Lie group

Mathlib's `GroupLieAlgebra I G` is the tangent space of `G` at the identity, which is the model
space `E` of `G` by definition. Differential forms with values in the Lie algebra are written, as
Tau Ceti's connection forms and Maurer–Cartan form are, with values in `E`, which carries the norm.
Tau Ceti's adjoint action `TauCeti.Lie.adjointContinuousLinearMap g` acts on such forms by
`TauCeti.SmoothForm.mapCoeff` once it is read as a map of `E`. This file gives the bracket of
`GroupLieAlgebra I G` as a continuous bilinear map of `E`, for `TauCeti.SmoothForm.wedgeWith`.

## Main definitions

* `GroupLieAlgebra.bracketL I G : E →L[ℝ] E →L[ℝ] E`: the bracket of `GroupLieAlgebra I G`, as a
  continuous bilinear map of `E` (Tau Ceti's `TauCeti.lieL`).

## Main results

* `GroupLieAlgebra.adjointContinuousLinearMap_bracketL`: the adjoint action preserves the
  bracket.
-/

public section

noncomputable section

open TauCeti TauCeti.Lie
open scoped Manifold ContDiff

namespace GroupLieAlgebra

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]

section Bracket

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable [FiniteDimensional ℝ E] [LieGroup I ∞ G]

variable (G) in
/-- The bracket of the Lie algebra `GroupLieAlgebra I G` (Mathlib's, that of left-invariant
vector fields), as a continuous bilinear map of the model space `E` (Tau Ceti's `TauCeti.lieL`). -/
def bracketL : E →L[ℝ] E →L[ℝ] E :=
  lieL ℝ (GroupLieAlgebra I G) (GroupLieAlgebra I G)

variable {I}

theorem bracketL_def :
    bracketL I G = lieL ℝ (GroupLieAlgebra I G) (GroupLieAlgebra I G) :=
  (rfl)

theorem bracketL_apply (v w : E) :
    bracketL I G v w = @Bracket.bracket (GroupLieAlgebra I G) (GroupLieAlgebra I G) _ v w :=
  lieL_apply (𝕜 := ℝ) (L := GroupLieAlgebra I G) (M := GroupLieAlgebra I G) v w

/-- The bracket on the model space is antisymmetric. -/
theorem bracketL_swap (v w : E) : bracketL I G w v = -bracketL I G v w := by
  rw [bracketL_apply, bracketL_apply]
  -- `v` and `w` have type `E`, so `L` would be taken to be `E` unless given.
  exact (lie_skew (L := GroupLieAlgebra I G) w v).symm

/-- The bracket on the model space vanishes on equal arguments. -/
@[simp]
theorem bracketL_self (v : E) : bracketL I G v v = 0 := by
  rw [bracketL_apply]
  -- `v` has type `E`, so `L` would be taken to be `E` unless given.
  exact lie_self (L := GroupLieAlgebra I G) v

/-- The adjoint action preserves the bracket. -/
theorem adjointContinuousLinearMap_bracketL (g : G) (v w : E) :
    (adjointContinuousLinearMap (I := I) g : E →L[ℝ] E) (bracketL I G v w) =
      bracketL I G ((adjointContinuousLinearMap (I := I) g : E →L[ℝ] E) v)
        ((adjointContinuousLinearMap (I := I) g : E →L[ℝ] E) w) := by
  rw [bracketL_apply]
  exact (adjointContinuousLinearMap_lie (I := I) g v w).trans
    (bracketL_apply (I := I) (G := G) _ _).symm

end Bracket

end GroupLieAlgebra

end
