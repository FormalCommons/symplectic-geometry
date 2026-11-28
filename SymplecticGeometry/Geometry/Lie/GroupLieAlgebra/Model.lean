/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Basic
public import TauCeti.Geometry.Lie.Tangent.LeftInvariantDerivation
public import TauCeti.Topology.Algebra.Lie.Bracket
import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# The bracket on the model space of a Lie group

Mathlib's `GroupLieAlgebra I G` is the tangent space of `G` at the identity, which is the model
space `E` of `G` by definition. Differential forms with values in the Lie algebra are written, as
Tau Ceti's connection forms and Maurer–Cartan form are, with values in `E`, which carries the norm.
Tau Ceti's adjoint action `TauCeti.Lie.adjointContinuousLinearMap g` acts on such forms by
`TauCeti.SmoothForm.mapCoeff` once it is read as a map of `E`. This file gives the bracket of
`GroupLieAlgebra I G` as a continuous bilinear map of `E`, for `TauCeti.SmoothForm.wedgeWith`.
It also evaluates Tau Ceti's linear equivalence `groupLieAlgebraEquivModelVectorSpace` of
`GroupLieAlgebra I G` with `E`, and its inverse: both send each vector to itself.

## Main definitions

* `GroupLieAlgebra.bracketL I G : E →L[ℝ] E →L[ℝ] E`: the bracket of `GroupLieAlgebra I G`, as a
  continuous bilinear map of `E` (Tau Ceti's `TauCeti.lieL`).

## Main results

* `groupLieAlgebraEquivModelVectorSpace_apply` and
  `groupLieAlgebraEquivModelVectorSpace_symm_apply`: Tau Ceti's identification of
  `GroupLieAlgebra I G` with `E`, and its inverse, send each vector to itself.
* `toContinuousLinearMap_conj_groupLieAlgebraEquivModelVectorSpace_apply`: an endomorphism of
  `GroupLieAlgebra I G`, conjugated to `E` by that identification, acts on `E` as itself; the
  `_ad_apply` form evaluates the conjugate of `ad X` to the bracket with `X`.
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

/-- The bracket on the model space is the bracket of `GroupLieAlgebra I G`, carried to `E` and
back through Mathlib's identification `tangentSpaceCastModel I 1` of the tangent space at the
identity with `E`. -/
theorem bracketL_apply (v w : E) :
    bracketL I G v w = tangentSpaceCastModel I (1 : G)
      ⁅((tangentSpaceCastModel I (1 : G)).symm v : GroupLieAlgebra I G),
        (tangentSpaceCastModel I (1 : G)).symm w⁆ :=
  lieL_apply (𝕜 := ℝ) (L := GroupLieAlgebra I G) (M := GroupLieAlgebra I G) v w

/-- The bracket on the model space is antisymmetric. -/
theorem bracketL_swap (v w : E) : bracketL I G w v = -bracketL I G v w := by
  rw [bracketL_apply, bracketL_apply, ← lie_skew, map_neg]

/-- The bracket on the model space vanishes on equal arguments. -/
@[simp]
theorem bracketL_self (v : E) : bracketL I G v v = 0 := by
  rw [bracketL_apply, lie_self, map_zero]

/-- The adjoint action preserves the bracket. -/
theorem adjointContinuousLinearMap_bracketL (g : G) (v w : E) :
    (adjointContinuousLinearMap (I := I) g : E →L[ℝ] E) (bracketL I G v w) =
      bracketL I G ((adjointContinuousLinearMap (I := I) g : E →L[ℝ] E) v)
        ((adjointContinuousLinearMap (I := I) g : E →L[ℝ] E) w) :=
  -- `tangentSpaceCastModel` is the identity, so Tau Ceti's lemma for `GroupLieAlgebra I G`
  -- applies to the two sides as they are.
  (congrArg _ (bracketL_apply v w)).trans <| (adjointContinuousLinearMap_lie (I := I) g v w).trans
    (bracketL_apply (I := I) (G := G) _ _).symm

end Bracket

end GroupLieAlgebra

section ModelVectorSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]

/-- Tau Ceti's identification `groupLieAlgebraEquivModelVectorSpace` of the Lie algebra
`GroupLieAlgebra I G` with the model space sends each element of the Lie algebra to itself, read
as a vector of the model space. -/
theorem groupLieAlgebraEquivModelVectorSpace_apply (v : GroupLieAlgebra I G) :
    groupLieAlgebraEquivModelVectorSpace v = v :=
  (rfl)

/-- The inverse of Tau Ceti's `groupLieAlgebraEquivModelVectorSpace` sends each vector of the
model space to itself, read as an element of the Lie algebra `GroupLieAlgebra I G`. -/
theorem groupLieAlgebraEquivModelVectorSpace_symm_apply (v : E) :
    (groupLieAlgebraEquivModelVectorSpace (I := I) (G := G)).symm v = v :=
  (rfl)

variable [FiniteDimensional ℝ E]

/-- An endomorphism `f` of the Lie algebra `GroupLieAlgebra I G`, carried to the model space `E`
by conjugation with `groupLieAlgebraEquivModelVectorSpace` and read as a continuous linear map,
sends each vector `v` of `E` to `f v`. -/
theorem toContinuousLinearMap_conj_groupLieAlgebraEquivModelVectorSpace_apply
    (f : Module.End ℝ (GroupLieAlgebra I G)) (v : E) :
    Module.End.toContinuousLinearMap E
      ((groupLieAlgebraEquivModelVectorSpace (I := I) (G := G)).conj f) v = f v := by
  rw [Module.End.toContinuousLinearMap_apply, LinearEquiv.conj_apply_apply,
    groupLieAlgebraEquivModelVectorSpace_apply, groupLieAlgebraEquivModelVectorSpace_symm_apply]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField in
/-- The adjoint map `ad X` of the Lie algebra `GroupLieAlgebra I G`, carried to the model space
`E` by conjugation with `groupLieAlgebraEquivModelVectorSpace` and read as a continuous linear
map, sends each `v` to the bracket `⁅X, v⁆`. -/
theorem toContinuousLinearMap_conj_groupLieAlgebraEquivModelVectorSpace_ad_apply
    [LieGroup I ∞ G] (X v : GroupLieAlgebra I G) :
    Module.End.toContinuousLinearMap E
      ((groupLieAlgebraEquivModelVectorSpace (I := I) (G := G)).conj
        (LieAlgebra.ad ℝ (GroupLieAlgebra I G) X)) v = ⁅X, v⁆ :=
  (toContinuousLinearMap_conj_groupLieAlgebraEquivModelVectorSpace_apply (E := E) _ v).trans
    (LieAlgebra.ad_apply ℝ (GroupLieAlgebra I G) X v)

end ModelVectorSpace

end
