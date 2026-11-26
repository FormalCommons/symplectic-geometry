/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Lie.GroupLieAlgebra.Normed
public import TauCeti.Analysis.Calculus.DifferentialForm.Basic
public import TauCeti.Geometry.Lie.Adjoint.Basic
public import TauCeti.Geometry.Lie.LeftInvariantForm
public import TauCeti.Geometry.Manifold.DifferentialForm.MapCoeff
public import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.Smooth

/-!
# The left Maurer–Cartan form

For a real Lie group `G` with Lie algebra `𝔤 = GroupLieAlgebra I G`, the left Maurer–Cartan form
`θ` is the `𝔤`-valued one-form that translates a tangent vector at `g` back to the identity:
`θ_g v = d(L_{g⁻¹})_g v`. Tau Ceti has it evaluated on a vector field
(`TauCeti.leftMaurerCartanEval`); this file names it as a smooth form, Tau Ceti's left-invariant
extension `TauCeti.leftInvariantSmoothForm` of the identity of `𝔤`.

## Main definitions

* `SymplecticGeometry.leftMaurerCartanForm I G : SmoothForm I G (GroupLieAlgebra I G) 1`.

## Main results

* `SymplecticGeometry.leftMaurerCartanForm_apply`: its value at `g` on `v` is
  `mfderiv I I (g⁻¹ * ·) g v`.
* `SymplecticGeometry.leftMaurerCartanForm_apply_mulInvariantVectorField`: it takes the value `ξ`
  on the left-invariant vector field of `ξ`.
* `SymplecticGeometry.mpullback_mul_left_leftMaurerCartanForm`: it is left-invariant.
* `SymplecticGeometry.mpullback_mul_right_leftMaurerCartanForm`: right translation by `h` pulls
  it back to its image under `Ad(h⁻¹)`.
* `SymplecticGeometry.differentiable_mfderiv_inv_mul_mfderiv`: the left-trivialized derivative
  `y ↦ d(L_{(γ y)⁻¹})(dγ_y v)` of a smooth map `γ` from a normed space to `G` is differentiable.
* `SymplecticGeometry.mextDeriv_leftMaurerCartanForm_apply`: the Maurer–Cartan equation
  `dθ(v, w) = -⁅θ v, θ w⁆`, for `G` finite-dimensional.
* `SymplecticGeometry.fderiv_leftMaurerCartanForm_mfderiv_sub`: the structure equation for the
  left-trivialized derivatives `a_v = θ (dγ v)` of a smooth map `γ` from a normed space to `G`,
  `∂_v a_w - ∂_w a_v = -⁅a_v, a_w⁆`; for a two-parameter map `γ : ℝ × ℝ → G` and the coordinate
  directions this reads `∂_s b - ∂_t a = -⁅a, b⁆`.

## Implementation notes

Smoothness and left-invariance come from Tau Ceti's `TauCeti.leftInvariantSmoothForm` and
`TauCeti.mpullback_mul_left_leftInvariantSmoothForm`. The proof of
`mpullback_mul_right_leftMaurerCartanForm` follows that of Tau Ceti's
`Module.Dual.mpullback_mul_right_leftInvariantForm`.

The Maurer–Cartan equation is Tau Ceti's `TauCeti.mextDeriv_leftInvariantForm`, which computes
the exterior derivative of a left-invariant form by the Chevalley–Eilenberg differential, read
on `θ`. The structure equation along `γ` pulls `θ` back to the normed space
(`TauCeti.SmoothForm.mextDeriv_mpullback_apply_two`), identifies the exterior derivative there
with that of a normed space (`TauCeti.mextDeriv_eq_extDeriv`), and evaluates it on a pair of
directions as a difference of directional derivatives
(`TauCeti.extDeriv_apply_pair_of_differentiableAt`).

The norm on `𝔤` that `SmoothForm` needs is the scoped one of
`SymplecticGeometry.Geometry.Lie.GroupLieAlgebra.Normed`; statements about this form need
`open scoped GroupLieAlgebra`.

## References

* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, Vol. I, Interscience, 1963,
  Chapter I, §4 (the canonical one-form of a Lie group).
-/

public section

noncomputable section

open TauCeti TauCeti.Lie
open scoped Manifold ContDiff GroupLieAlgebra

namespace SymplecticGeometry

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (G : Type*) [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]

/-- The **left Maurer–Cartan form** of a Lie group `G`: the smooth one-form with values in the
Lie algebra `𝔤 = GroupLieAlgebra I G` whose value at `g` on a tangent vector `v` is
`d(L_{g⁻¹})_g v`. It is the left-invariant extension of the identity of `𝔤`, read as a
one-form on `𝔤`. -/
def leftMaurerCartanForm : SmoothForm I G (GroupLieAlgebra I G) 1 :=
  leftInvariantSmoothForm I G (GroupLieAlgebra I G) 1
    (ContinuousAlternatingMap.ofSubsingleton ℝ (GroupLieAlgebra I G) (GroupLieAlgebra I G) 0
      (ContinuousLinearMap.id ℝ (GroupLieAlgebra I G)))

theorem leftMaurerCartanForm_def :
    leftMaurerCartanForm I G = leftInvariantSmoothForm I G (GroupLieAlgebra I G) 1
      (ContinuousAlternatingMap.ofSubsingleton ℝ (GroupLieAlgebra I G) (GroupLieAlgebra I G) 0
        (ContinuousLinearMap.id ℝ (GroupLieAlgebra I G))) :=
  (rfl)

variable {I G}

/-- The left Maurer–Cartan form at `g` translates a tangent vector at `g` to the identity by the
differential of left multiplication by `g⁻¹`. -/
theorem leftMaurerCartanForm_apply (g : G) (v : Fin 1 → TangentSpace I g) :
    (leftMaurerCartanForm I G).val g v = mfderiv I I (g⁻¹ * ·) g (v 0) := by
  rw [leftMaurerCartanForm_def, leftInvariantSmoothForm_val, leftInvariantForm_apply]
  -- `ofSubsingleton_apply_apply` does not rewrite here: the form is on `𝔤` with the scoped norm,
  -- the vectors are in tangent spaces, and the two topologies agree only by unfolding.
  exact ContinuousAlternatingMap.ofSubsingleton_apply_apply _ _ _ _ _ _

/-- The left Maurer–Cartan form takes the constant value `ξ` on the left-invariant vector field of
`ξ`. -/
@[simp]
theorem leftMaurerCartanForm_apply_mulInvariantVectorField (ξ : GroupLieAlgebra I G) (g : G) :
    (leftMaurerCartanForm I G).val g ![mulInvariantVectorField ξ g] = ξ := by
  rw [leftMaurerCartanForm_apply, Matrix.cons_val_zero, mfderiv_inv_mul_mulInvariantVectorField]

/-- The left Maurer–Cartan form is left-invariant: `L_h^* θ = θ`. -/
@[simp]
theorem mpullback_mul_left_leftMaurerCartanForm (h : G) :
    SmoothForm.mpullback (h * ·) contMDiff_mul_left (leftMaurerCartanForm I G) =
      leftMaurerCartanForm I G :=
  mpullback_mul_left_leftInvariantSmoothForm _ h

/-- Right translation by `h` pulls the left Maurer–Cartan form back to its image under the
adjoint action of `h⁻¹`: `R_h^* θ = Ad(h⁻¹) θ`. -/
@[simp]
theorem mpullback_mul_right_leftMaurerCartanForm (h : G) :
    SmoothForm.mpullback (· * h) contMDiff_mul_right (leftMaurerCartanForm I G) =
      SmoothForm.mapCoeff (adjointContinuousLinearMap h⁻¹) (leftMaurerCartanForm I G) := by
  refine SmoothBundleForm.ext fun g v ↦ ?_
  obtain ⟨ξ, hξ⟩ := exists_mulInvariantVectorField_eq (v 0)
  rw [SmoothForm.coe_mpullback, TauCeti.mpullback_apply, SmoothForm.coe_mapCoeff,
    RoughForm.mapCoeff_apply, leftMaurerCartanForm_apply, leftMaurerCartanForm_apply, ← hξ,
    mfderiv_mul_right_mulInvariantVectorField, mfderiv_inv_mul_mulInvariantVectorField,
    mfderiv_inv_mul_mulInvariantVectorField]

section LeftTrivialization

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']

/-- The left-trivialized derivative of a smooth map `γ : E' → G` from a normed space in a fixed
direction `v`, `y ↦ d(L_{(γ y)⁻¹})(dγ_y v)`, is differentiable as a map into the Lie algebra. -/
theorem differentiable_mfderiv_inv_mul_mfderiv {γ : E' → G} (hγ : ContMDiff 𝓘(ℝ, E') I ∞ γ)
    (v : E') :
    Differentiable (F := GroupLieAlgebra I G) ℝ fun y ↦
      mfderiv I I ((γ y)⁻¹ * ·) (γ y) (mfderiv 𝓘(ℝ, E') I γ y v) := by
  simpa [leftMaurerCartanForm_apply] using
    SmoothForm.differentiable_apply_one_mfderiv (leftMaurerCartanForm I G) hγ v

end LeftTrivialization

/-! ### The structure equation -/

section StructureEquation

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable [FiniteDimensional ℝ E]

/-- **The Maurer–Cartan equation**: the exterior derivative of the left Maurer–Cartan form `θ`
is `dθ(v, w) = -⁅θ v, θ w⁆`, the bracket being that of `GroupLieAlgebra I G`. -/
theorem mextDeriv_leftMaurerCartanForm_apply (g : G) (v w : TangentSpace I g) :
    mextDeriv (leftMaurerCartanForm I G).val g ![v, w] =
      -⁅(leftMaurerCartanForm I G).val g ![v], (leftMaurerCartanForm I G).val g ![w]⁆ := by
  obtain ⟨ξ, rfl⟩ := exists_mulInvariantVectorField_eq v
  obtain ⟨η, rfl⟩ := exists_mulInvariantVectorField_eq w
  have hvw : ![mulInvariantVectorField ξ g, mulInvariantVectorField η g] =
      fun i ↦ mulInvariantVectorField (![ξ, η] i) g := by
    ext i
    fin_cases i <;> rfl
  rw [leftMaurerCartanForm_apply_mulInvariantVectorField,
    leftMaurerCartanForm_apply_mulInvariantVectorField, hvw, leftMaurerCartanForm_def,
    leftInvariantSmoothForm_val, mextDeriv_leftInvariantForm,
    leftInvariantForm_apply_mulInvariantVectorField, LieModule.Cohomology.trivialD_succ_apply]
  simp

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']

/-- **The structure equation along a map from a normed space.** For a smooth map `γ : E' → G`,
write `a_v y = θ (dγ_y v)` for the left-trivialized derivative of `γ` in the direction `v`, `θ`
being the left Maurer–Cartan form. Then `∂_v a_w - ∂_w a_v = -⁅a_v, a_w⁆`. -/
theorem fderiv_leftMaurerCartanForm_mfderiv_sub {γ : E' → G} (hγ : ContMDiff 𝓘(ℝ, E') I ∞ γ)
    (x v w : E') :
    fderiv ℝ (fun y ↦ (leftMaurerCartanForm I G).val (γ y) ![mfderiv 𝓘(ℝ, E') I γ y w]) x v -
        fderiv ℝ (fun y ↦ (leftMaurerCartanForm I G).val (γ y) ![mfderiv 𝓘(ℝ, E') I γ y v]) x w =
      -⁅(leftMaurerCartanForm I G).val (γ x) ![mfderiv 𝓘(ℝ, E') I γ x v],
        (leftMaurerCartanForm I G).val (γ x) ![mfderiv 𝓘(ℝ, E') I γ x w]⁆ := by
  have hpull := SmoothForm.mextDeriv_mpullback_apply_two γ hγ (leftMaurerCartanForm I G) x v w
  have hd := ((isSmoothForm_modelSpace_iff.1 (SmoothForm.isSmoothForm
    (SmoothForm.mpullback γ hγ (leftMaurerCartanForm I G)))).differentiable (by simp)) x
  rw [mextDeriv_eq_extDeriv, mextDeriv_leftMaurerCartanForm_apply] at hpull
  have hfun (u : E') : (fun y ↦ (SmoothForm.mpullback γ hγ (leftMaurerCartanForm I G)).val y
      (fun _ ↦ u)) =
      fun y ↦ (leftMaurerCartanForm I G).val (γ y) ![mfderiv 𝓘(ℝ, E') I γ y u] :=
    funext fun y ↦ (congrArg _ (by ext i; fin_cases i; rfl)).trans
      (SmoothForm.mpullback_apply_one γ hγ _ y u)
  rw [← hfun, ← hfun]
  exact (extDeriv_apply_pair_of_differentiableAt hd v w).symm.trans hpull

end StructureEquation

end SymplecticGeometry

end
