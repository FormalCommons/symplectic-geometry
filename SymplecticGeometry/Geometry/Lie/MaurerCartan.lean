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
* `SymplecticGeometry.mfderiv_inv_mul_mfderiv_mul_right`,
  `SymplecticGeometry.mfderiv_inv_mul_mfderiv_mul_left`: translated back to the identity, the
  derivative of right translation by `h` is `Ad(h⁻¹)`, and that of a left translation is trivial.
* `SymplecticGeometry.mpullback_mul_left_leftMaurerCartanForm`: it is left-invariant.
* `SymplecticGeometry.mpullback_mul_right_leftMaurerCartanForm`: right translation by `h` pulls
  it back to its image under `Ad(h⁻¹)`.
* `SymplecticGeometry.differentiable_mfderiv_inv_mul_mfderiv`: the left-trivialized derivative
  `y ↦ d(L_{(γ y)⁻¹})(dγ_y v)` of a smooth map `γ` from a normed space to `G` is differentiable.
* `SymplecticGeometry.mfderiv_mul_apply`: the product rule `d(ab) v = d(R_b)(da v) + d(L_a)(db v)`
  for maps `a b : M → G` from a manifold.
* `SymplecticGeometry.mfderiv_inv_mul_mfderiv_mul`: the product rule for left-trivialized
  derivatives, `(ab)⁻¹(ab)' = Ad_{b⁻¹}(a⁻¹a') + b⁻¹b'`.
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

/-! ### Translations and the product rule

These hold over any nontrivially normed field, for Lie groups of class `C¹`. -/

section ProductRule

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E H : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M : Type*} [TopologicalSpace M] [ChartedSpace H' M]
  {a b : M → G} {z : M}

section Mul

variable [Mul G] [ContMDiffMul I 1 G]

/-- **The product rule** for maps into a manifold `G` with a `C¹` multiplication: the derivative
of the pointwise product `z ↦ a z * b z` at `z` sends `v` to
`d(R_{b z})(da v) + d(L_{a z})(db v)`. -/
theorem mfderiv_mul_apply (ha : MDifferentiableAt I' I a z) (hb : MDifferentiableAt I' I b z)
    (v : TangentSpace I' z) :
    mfderiv I' I (fun z ↦ a z * b z) z v =
      mfderiv I I (· * b z) (a z) (mfderiv I' I a z v) +
        mfderiv I I (a z * ·) (b z) (mfderiv I' I b z v) := by
  have hmul : MDifferentiableAt (I.prod I) I (fun p : G × G ↦ p.1 * p.2) (a z, b z) :=
    (contMDiff_mul I 1).mdifferentiableAt (by simp)
  have hcomp := mfderiv_comp_apply z hmul (ha.prodMk hb) v
  rw [mfderiv_prodMk ha hb] at hcomp
  exact hcomp.trans (mfderiv_prod_eq_add_apply hmul)

end Mul

variable [Group G] [LieGroup I 1 G]

/-- Translated back to the identity, the derivative of right translation by `h` at `g` is the
adjoint action of `h⁻¹`: `d(L_{(gh)⁻¹})(d(R_h)_g v) = Ad(h⁻¹) (d(L_{g⁻¹})_g v)`. -/
theorem mfderiv_inv_mul_mfderiv_mul_right (g h : G) (v : TangentSpace I g) :
    mfderiv I I ((g * h)⁻¹ * ·) (g * h) (mfderiv I I (· * h) g v) =
      adjointContinuousLinearMap (I := I) h⁻¹ (mfderiv I I (g⁻¹ * ·) g v) := by
  obtain ⟨ξ, rfl⟩ := exists_mulInvariantVectorField_eq v
  rw [mfderiv_mul_right_mulInvariantVectorField, mfderiv_inv_mul_mulInvariantVectorField,
    mfderiv_inv_mul_mulInvariantVectorField]

/-- Translated back to the identity, a tangent vector at `h` and its left translate by `g` agree:
`d(L_{(gh)⁻¹})(d(L_g)_h v) = d(L_{h⁻¹})_h v`. -/
theorem mfderiv_inv_mul_mfderiv_mul_left (g h : G) (v : TangentSpace I h) :
    mfderiv I I ((g * h)⁻¹ * ·) (g * h) (mfderiv I I (g * ·) h v) =
      mfderiv I I (h⁻¹ * ·) h v := by
  obtain ⟨ξ, rfl⟩ := exists_mulInvariantVectorField_eq v
  rw [mfderiv_mul_left_mulInvariantVectorField, mfderiv_inv_mul_mulInvariantVectorField,
    mfderiv_inv_mul_mulInvariantVectorField]

/-- **The product rule for left-trivialized derivatives.** For maps `a b : M → G` differentiable
at `z`, the left-trivialized derivative of `z ↦ a z * b z` is the image of that of `a` under the
adjoint action of `(b z)⁻¹`, plus that of `b`; in matrix notation,
`(ab)⁻¹(ab)' = Ad_{b⁻¹}(a⁻¹a') + b⁻¹b'`. -/
theorem mfderiv_inv_mul_mfderiv_mul (ha : MDifferentiableAt I' I a z)
    (hb : MDifferentiableAt I' I b z) (v : TangentSpace I' z) :
    mfderiv I I ((a z * b z)⁻¹ * ·) (a z * b z) (mfderiv I' I (fun z ↦ a z * b z) z v) =
      adjointContinuousLinearMap (I := I) (b z)⁻¹
          (mfderiv I I ((a z)⁻¹ * ·) (a z) (mfderiv I' I a z v)) +
        (show GroupLieAlgebra I G from mfderiv I I ((b z)⁻¹ * ·) (b z) (mfderiv I' I b z v)) := by
  -- `dsimp only` drops the `show` that types the last summand in the Lie algebra.
  dsimp only
  rw [mfderiv_mul_apply ha hb, map_add, mfderiv_inv_mul_mfderiv_mul_right,
    mfderiv_inv_mul_mfderiv_mul_left]
  -- The two sums are taken in the tangent space at `(a z * b z)⁻¹ * (a z * b z)` and in the Lie
  -- algebra, the tangent space at `1`: both are the model space `E` with its addition.
  rfl

end ProductRule

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
  rw [SmoothForm.coe_mpullback, TauCeti.mpullback_apply, SmoothForm.coe_mapCoeff,
    RoughForm.mapCoeff_apply, leftMaurerCartanForm_apply, leftMaurerCartanForm_apply,
    mfderiv_inv_mul_mfderiv_mul_right]

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
