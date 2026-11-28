/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Basic
public import TauCeti.Topology.Algebra.Lie.Bracket

/-!
# The adjoint action and the bracket on the model space of a Lie group

Mathlib's `GroupLieAlgebra I G` is the tangent space of `G` at the identity, which is the model
space `E` of `G` by definition. Differential forms with values in the Lie algebra are written, as
Tau Ceti's connection forms and Maurer–Cartan form are, with values in `E`, which carries the norm.
A linear map of `GroupLieAlgebra I G` is a linear map of `E` only up to unfolding `TangentSpace`,
so Tau Ceti's adjoint action and the bracket do not act on such forms by
`TauCeti.SmoothForm.mapCoeff`
and `TauCeti.SmoothForm.wedgeWith` as they stand. This file restates them as maps of `E`.

## Main definitions

* `GroupLieAlgebra.adjointL I g : E →L[ℝ] E`: Tau Ceti's adjoint action
  `TauCeti.Lie.adjointContinuousLinearMap g`, as a continuous linear map of `E`.
* `GroupLieAlgebra.bracketL I G : E →L[ℝ] E →L[ℝ] E`: the bracket of `GroupLieAlgebra I G`, as a
  continuous bilinear map of `E` (Tau Ceti's `TauCeti.lieL`).

## Main results

* `GroupLieAlgebra.adjointL_bracketL`: the adjoint action preserves the bracket.
* `GroupLieAlgebra.adjointL_eq_id`: the adjoint action of a commutative group is trivial.
-/

public section

noncomputable section

open TauCeti TauCeti.Lie
open scoped Manifold ContDiff

namespace GroupLieAlgebra

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]

section Adjoint

variable [LieGroup I 1 G]

/-- Tau Ceti's adjoint action `Ad g` of a Lie group on its Lie algebra
(`TauCeti.Lie.adjointContinuousLinearMap`), as a continuous linear map of the model space `E`,
which is the Lie algebra by definition. -/
def adjointL (g : G) : E →L[ℝ] E :=
  adjointContinuousLinearMap (I := I) g

variable {I}

theorem adjointL_def (g : G) :
    (adjointL I g : E →L[ℝ] E) = adjointContinuousLinearMap (I := I) g :=
  (rfl)

theorem adjointL_apply (g : G) (v : E) :
    adjointL I g v = adjointContinuousLinearMap (I := I) g v :=
  (rfl)

/-- The adjoint action of the identity is the identity. -/
@[simp]
theorem adjointL_one : adjointL I (1 : G) = ContinuousLinearMap.id ℝ E :=
  adjointContinuousLinearMap_one (I := I)

/-- The adjoint action is multiplicative: `Ad_{gh} = Ad_g ∘ Ad_h`. -/
theorem adjointL_mul (g h : G) : adjointL I (g * h) = (adjointL I g).comp (adjointL I h) :=
  adjointContinuousLinearMap_mul (I := I) g h

/-- The adjoint action of `g` undoes that of `g⁻¹`: `Ad_g (Ad_{g⁻¹} v) = v`. -/
@[simp]
theorem adjointL_adjointL_inv (g : G) (v : E) : adjointL I g (adjointL I g⁻¹ v) = v :=
  adjointContinuousLinearMap_adjointContinuousLinearMap_inv (I := I) g v

/-- The adjoint action of `g⁻¹` undoes that of `g`: `Ad_{g⁻¹} (Ad_g v) = v`. -/
@[simp]
theorem adjointL_inv_adjointL (g : G) (v : E) : adjointL I g⁻¹ (adjointL I g v) = v :=
  adjointContinuousLinearMap_inv_adjointContinuousLinearMap (I := I) g v

/-- The adjoint action of a commutative Lie group on the model space is trivial. -/
@[simp]
theorem adjointL_eq_id [IsMulCommutative G] (g : G) :
    adjointL I g = ContinuousLinearMap.id ℝ E :=
  adjointContinuousLinearMap_eq_id (I := I) g

end Adjoint

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
  exact (lie_skew (L := GroupLieAlgebra I G) w v).symm

/-- The bracket on the model space vanishes on equal arguments. -/
@[simp]
theorem bracketL_self (v : E) : bracketL I G v v = 0 := by
  rw [bracketL_apply]
  exact lie_self (L := GroupLieAlgebra I G) v

/-- The adjoint action preserves the bracket. -/
theorem adjointL_bracketL (g : G) (v w : E) :
    adjointL I g (bracketL I G v w) =
      bracketL I G (adjointL I g v) (adjointL I g w) := by
  rw [bracketL_apply, bracketL_apply, adjointL_apply]
  exact adjointContinuousLinearMap_lie (I := I) g v w

end Bracket

end GroupLieAlgebra

end
