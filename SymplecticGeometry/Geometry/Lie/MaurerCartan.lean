/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Calculus.DifferentialForm.Basic
public import TauCeti.Geometry.Lie.MaurerCartan
public import TauCeti.Geometry.Manifold.DifferentialForm.MapCoeff
public import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import Mathlib.Data.Fin.Tuple.Reflection
public import SymplecticGeometry.Geometry.Lie.GroupLieAlgebra.Model
import SymplecticGeometry.Geometry.Manifold.IsManifold.Basic

/-!
# The left Maurer–Cartan form: right translates and the structure equation

Tau Ceti defines the left Maurer–Cartan form `θ_g v = d(L_{g⁻¹})_g v` of a real Lie group `G`
(`TauCeti.leftMaurerCartanForm`), a smooth one-form with values in the model space `E`, which is
the Lie algebra `GroupLieAlgebra I G`, and proves its pointwise laws under left and right
translations. This file identifies `θ` with a left-invariant form, and adds the law under right
translations as an identity of smooth forms, the Maurer–Cartan equation, and the structure
equation along a map from a normed space.

## Main results

* `TauCeti.leftMaurerCartanForm_eq_leftInvariantSmoothForm`: `θ` is the left-invariant extension
  of the identity of the Lie algebra.
* `SymplecticGeometry.mpullback_mul_right_leftMaurerCartanForm`: right translation by `h` pulls
  `θ` back to its image under `Ad(h⁻¹)`, as smooth forms.
* `SymplecticGeometry.differentiable_mfderiv_inv_mul_mfderiv`: the left-trivialized derivative
  `y ↦ d(L_{(γ y)⁻¹})(dγ_y v)` of a smooth map `γ` from a normed space to `G` is differentiable.
* `SymplecticGeometry.mextDeriv_leftMaurerCartanForm_apply`: the Maurer–Cartan equation
  `dθ(v, w) = -⁅θ v, θ w⁆`, for `G` finite-dimensional.
* `SymplecticGeometry.fderiv_leftMaurerCartanForm_mfderiv_sub`: the structure equation for the
  left-trivialized derivatives `a_v = θ (dγ v)` of a smooth map `γ` from a normed space to `G`,
  `∂_v a_w - ∂_w a_v = -⁅a_v, a_w⁆`; for a two-parameter map `γ : ℝ × ℝ → G` and the coordinate
  directions this reads `∂_s b - ∂_t a = -⁅a, b⁆`.

## Implementation notes

The identity of smooth forms under right translations is Tau Ceti's pointwise
`TauCeti.leftMaurerCartanForm_apply_mfderiv_mul_right`. The Maurer–Cartan equation is Tau Ceti's
`TauCeti.mextDeriv_leftInvariantForm`, which computes the exterior derivative of a left-invariant
form by the Chevalley–Eilenberg differential, read on `θ`. The structure equation along `γ` pulls
`θ` back to the normed space (`TauCeti.SmoothForm.mextDeriv_mpullback_apply_two`), identifies the
exterior derivative there with that of a normed space (`TauCeti.mextDeriv_eq_extDeriv`), and
evaluates it on a pair of directions as a difference of directional derivatives
(`TauCeti.extDeriv_apply_pair_of_differentiableAt`).

## References

* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, Vol. I, Interscience, 1963,
  Chapter I, §4 (the canonical one-form of a Lie group).
-/

public section

noncomputable section

open TauCeti TauCeti.Lie
open scoped Manifold ContDiff

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]

/-- The left Maurer–Cartan form is the left-invariant extension of the identity of the Lie algebra
`GroupLieAlgebra I G`, read as a one-form on it with values in the model space `E`. -/
theorem leftMaurerCartanForm_eq_leftInvariantSmoothForm :
    leftMaurerCartanForm I G = leftInvariantSmoothForm I G E 1
      (ContinuousAlternatingMap.ofSubsingleton ℝ (GroupLieAlgebra I G) E 0
        (ContinuousLinearMap.id ℝ E)) := by
  refine SmoothBundleForm.ext fun g u ↦ ?_
  have hu : u = ![u 0] := (FinVec.etaExpand_eq u).symm
  rw [leftInvariantSmoothForm_val, leftInvariantForm_apply, hu, leftMaurerCartanForm_apply]
  -- The identity of `E` applied to the translated vector is that vector, by definition.
  rfl

end TauCeti

namespace SymplecticGeometry

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]

/-- Right translation by `h` pulls the left Maurer–Cartan form back to its image under the
adjoint action of `h⁻¹`: `R_h^* θ = Ad(h⁻¹) θ`. -/
theorem mpullback_mul_right_leftMaurerCartanForm (h : G) :
    SmoothForm.mpullback (· * h) contMDiff_mul_right (leftMaurerCartanForm I G) =
      SmoothForm.mapCoeff (F := E) (G := E) (adjointContinuousLinearMap (I := I) h⁻¹)
        (leftMaurerCartanForm I G) := by
  refine SmoothBundleForm.ext fun g v ↦ ?_
  have hv : v = ![v 0] := (FinVec.etaExpand_eq v).symm
  rw [hv, SmoothForm.mpullback_apply_one]
  refine (leftMaurerCartanForm_apply_mfderiv_mul_right g h (v 0)).trans ?_
  -- `Ad(h⁻¹)` is typed on `GroupLieAlgebra I G`, so `rw` cannot match `mapCoeff (F := E)`.
  exact ((DFunLike.congr_fun (congrFun (SmoothForm.coe_mapCoeff (F := E) (G := E)
    (adjointContinuousLinearMap (I := I) h⁻¹) (leftMaurerCartanForm I G)) g) _).trans
    (RoughForm.mapCoeff_apply (F := E) (G := E) _ _ _ _)).symm

section LeftTrivialization

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']

/-- The left-trivialized derivative of a smooth map `γ : E' → G` from a normed space in a fixed
direction `v`, `y ↦ d(L_{(γ y)⁻¹})(dγ_y v)`, is differentiable as a map into the Lie algebra,
the model space `E`. -/
theorem differentiable_mfderiv_inv_mul_mfderiv {γ : E' → G} (hγ : ContMDiff 𝓘(ℝ, E') I ∞ γ)
    (v : E') :
    Differentiable ℝ fun y ↦
      mfderiv I I ((γ y)⁻¹ * ·) (γ y) (mfderiv 𝓘(ℝ, E') I γ y v) := by
  simpa [leftMaurerCartanForm_apply] using
    SmoothForm.differentiable_apply_one_mfderiv (leftMaurerCartanForm I G) hγ v

end LeftTrivialization

/-! ### The structure equation -/

section StructureEquation

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable [FiniteDimensional ℝ E]

/-- **The Maurer–Cartan equation**: the exterior derivative of the left Maurer–Cartan form `θ`
is `dθ(v, w) = -⁅θ v, θ w⁆`, the bracket being that of `GroupLieAlgebra I G` read on the model
space `E` (`GroupLieAlgebra.bracketL`). -/
theorem mextDeriv_leftMaurerCartanForm_apply (g : G) (v w : TangentSpace I g) :
    mextDeriv (leftMaurerCartanForm I G).val g ![v, w] =
      -GroupLieAlgebra.bracketL I G
        ((leftMaurerCartanForm I G).val g ![v]) ((leftMaurerCartanForm I G).val g ![w]) := by
  rw [GroupLieAlgebra.bracketL_apply, tangentSpaceCastModel_apply, tangentSpaceCastModel_symm_apply,
    tangentSpaceCastModel_symm_apply]
  obtain ⟨ξ, rfl⟩ := exists_mulInvariantVectorField_eq v
  obtain ⟨η, rfl⟩ := exists_mulInvariantVectorField_eq w
  have hvw : ![mulInvariantVectorField ξ g, mulInvariantVectorField η g] =
      fun i ↦ mulInvariantVectorField (![ξ, η] i) g :=
    FinVec.etaExpand_eq fun i ↦ mulInvariantVectorField (![ξ, η] i) g
  rw [leftMaurerCartanForm_apply_mulInvariantVectorField,
    leftMaurerCartanForm_apply_mulInvariantVectorField,
    leftMaurerCartanForm_eq_leftInvariantSmoothForm,
    leftInvariantSmoothForm_val, mextDeriv_leftInvariantForm, hvw,
    leftInvariantForm_apply_mulInvariantVectorField, LieModule.Cohomology.trivialD_succ_apply]
  -- The identity of `E` read on `⁅ξ, η⁆`.
  have hid : ContinuousAlternatingMap.ofSubsingleton ℝ (GroupLieAlgebra I G) E 0
      (ContinuousLinearMap.id ℝ E) ![⁅ξ, η⁆] = ⁅ξ, η⁆ :=
    ContinuousAlternatingMap.ofSubsingleton_apply_apply ..
  simp [hid]

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']

/-- **The structure equation along a map from a normed space.** For a smooth map `γ : E' → G`,
write `a_v y = θ (dγ_y v)` for the left-trivialized derivative of `γ` in the direction `v`, `θ`
being the left Maurer–Cartan form. Then `∂_v a_w - ∂_w a_v = -⁅a_v, a_w⁆`. -/
theorem fderiv_leftMaurerCartanForm_mfderiv_sub {γ : E' → G} (hγ : ContMDiff 𝓘(ℝ, E') I ∞ γ)
    (x v w : E') :
    fderiv ℝ (fun y ↦ (leftMaurerCartanForm I G).val (γ y) ![mfderiv 𝓘(ℝ, E') I γ y w]) x v -
        fderiv ℝ (fun y ↦ (leftMaurerCartanForm I G).val (γ y) ![mfderiv 𝓘(ℝ, E') I γ y v]) x w =
      -GroupLieAlgebra.bracketL I G
        ((leftMaurerCartanForm I G).val (γ x) ![mfderiv 𝓘(ℝ, E') I γ x v])
        ((leftMaurerCartanForm I G).val (γ x) ![mfderiv 𝓘(ℝ, E') I γ x w]) := by
  have hpull := SmoothForm.mextDeriv_mpullback_apply_two γ hγ (leftMaurerCartanForm I G) x v w
  have hd := ((isSmoothForm_modelSpace_iff.1 (SmoothForm.isSmoothForm
    (SmoothForm.mpullback γ hγ (leftMaurerCartanForm I G)))).differentiable (by simp)) x
  rw [mextDeriv_eq_extDeriv] at hpull
  have hfun (u : E') : (fun y ↦ (SmoothForm.mpullback γ hγ (leftMaurerCartanForm I G)).val y
      (fun _ ↦ u)) =
      fun y ↦ (leftMaurerCartanForm I G).val (γ y) ![mfderiv 𝓘(ℝ, E') I γ y u] :=
    funext fun y ↦ (congrArg _ (FinVec.etaExpand_eq _).symm).trans
      (SmoothForm.mpullback_apply_one γ hγ _ y u)
  rw [← hfun, ← hfun]
  exact (extDeriv_apply_pair_of_differentiableAt hd v w).symm.trans
    (hpull.trans (mextDeriv_leftMaurerCartanForm_apply _ _ _))

end StructureEquation

end SymplecticGeometry

end
