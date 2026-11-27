/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Curve

/-!
# The adjoint action as the differential of conjugation, and the product rule

Tau Ceti defines the adjoint action `Ad_g` of a Lie group `G` on its Lie algebra as the
differential at `1` of the diffeomorphism `TauCeti.Lie.conjDiffeomorph g`. This file states the
same facts for the plain function `x ↦ g * x * g⁻¹`, so that a map written with conjugation can be
differentiated without passing to the diffeomorphism.

It also proves the product rule for the pointwise product of two maps into `G`, and its form for
derivatives translated back to the identity, in which the adjoint action appears. All of this is
calculus on a Lie group of class `C¹` over any nontrivially normed field: no differential forms
are needed.

## Main results

* `TauCeti.Lie.mdifferentiable_conj`: conjugation by `g` is differentiable.
* `TauCeti.Lie.mfderiv_conj_one_apply`: its differential at `1` is `Ad_g`.
* `mfderiv_mul_apply`: the product rule `d(ab) v = d(R_b)(da v) + d(L_a)(db v)` for maps
  `a b : M → G` from a manifold into a manifold with a `C¹` multiplication.
* `hasDerivAt_comp_mul_of_hasDerivAt`: along a product `s ↦ b s * c s` of two curves, the
  derivative of `f (b s * c s)` is the sum of the derivatives in `b` and in `c` alone.
* `TauCeti.Lie.mfderiv_inv_mul_mfderiv_mul_right`,
  `TauCeti.Lie.mfderiv_inv_mul_mfderiv_mul_left`: translated back to the identity, the
  derivative of right translation by `h` is `Ad(h⁻¹)`, and that of a left translation is trivial.
* `TauCeti.Lie.mfderiv_inv_mul_mfderiv_mul`: the product rule for left-trivialized derivatives,
  `(ab)⁻¹(ab)' = Ad_{b⁻¹}(a⁻¹a') + b⁻¹b'`.
-/

public section

open scoped Manifold ContDiff

section ProductRule

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E H : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Mul G] [ContMDiffMul I 1 G]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M : Type*} [TopologicalSpace M] [ChartedSpace H' M]
  {a b : M → G} {z : M}

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

/-- **The derivative along a product of curves is the sum of the partial derivatives.** For
curves `b c : 𝕜 → G` differentiable at `t` and a map `f : G → F` differentiable at `b t * c t`,
if `s ↦ f (b s * c t)` has derivative `d₁` and `s ↦ f (b t * c s)` has derivative `d₂` at `t`,
then `s ↦ f (b s * c s)` has derivative `d₁ + d₂` at `t`. -/
theorem hasDerivAt_comp_mul_of_hasDerivAt {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : G → F} {b c : 𝕜 → G} {t : 𝕜} {d₁ d₂ : F}
    (hf : MDifferentiableAt I 𝓘(𝕜, F) f (b t * c t)) (hb : MDifferentiableAt 𝓘(𝕜) I b t)
    (hc : MDifferentiableAt 𝓘(𝕜) I c t) (h₁ : HasDerivAt (fun s ↦ f (b s * c t)) d₁ t)
    (h₂ : HasDerivAt (fun s ↦ f (b t * c s)) d₂ t) :
    HasDerivAt (fun s ↦ f (b s * c s)) (d₁ + d₂) t := by
  -- The unit tangent vector at `t`.
  obtain ⟨v, hv1⟩ : ∃ v : TangentSpace 𝓘(𝕜) t, v = (1 : 𝕜) := ⟨_, rfl⟩
  -- Along each of the three curves through `b t * c t`, the chain rule gives the derivative.
  have hv {γ : 𝕜 → G} (hγ : MDifferentiableAt 𝓘(𝕜) I γ t) (h : γ t = b t * c t) :
      HasDerivAt (f ∘ γ) (mvfderiv I f (γ t) (mfderiv 𝓘(𝕜) I γ t v)) t := by
    refine TauCeti.Manifold.hasDerivAt_comp_curve (h ▸ hf) ?_
    subst hv1
    exact hγ.hasMFDerivAt.congr_mfderiv ((ContinuousLinearMap.smulRight_one_eq_toSpanSingleton
      𝕜 _).trans (ContinuousLinearMap.toSpanSingleton_apply_map_one 𝕜 _)).symm
  have hbc : MDifferentiableAt 𝓘(𝕜) I (fun s ↦ b s * c s) t :=
    ((contMDiff_mul I 1).mdifferentiableAt one_ne_zero).comp t (hb.prodMk hc)
  have hb' : MDifferentiableAt 𝓘(𝕜) I (fun s ↦ b s * c t) t :=
    (contMDiff_mul_right.mdifferentiableAt one_ne_zero).comp t hb
  have hc' : MDifferentiableAt 𝓘(𝕜) I (fun s ↦ b t * c s) t :=
    (contMDiff_mul_left.mdifferentiableAt one_ne_zero).comp t hc
  refine (hv hbc rfl).congr_deriv ?_
  have e₁ : mfderiv 𝓘(𝕜) I (fun s ↦ b s * c t) t v =
      mfderiv I I (· * c t) (b t) (mfderiv 𝓘(𝕜) I b t v) :=
    mfderiv_comp_apply t (contMDiff_mul_right.mdifferentiableAt one_ne_zero) hb v
  have e₂ : mfderiv 𝓘(𝕜) I (fun s ↦ b t * c s) t v =
      mfderiv I I (b t * ·) (c t) (mfderiv 𝓘(𝕜) I c t v) :=
    mfderiv_comp_apply t (contMDiff_mul_left.mdifferentiableAt one_ne_zero) hc v
  rw [h₁.unique (hv hb' rfl), h₂.unique (hv hc' rfl), mfderiv_mul_apply hb hc, map_add, e₁, e₂]

end ProductRule

namespace TauCeti.Lie

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I 1 G]

/-- Conjugation `x ↦ g * x * g⁻¹` by an element `g` of a `C¹` Lie group is differentiable. -/
theorem mdifferentiable_conj (g : G) : MDifferentiable I I (fun x : G ↦ g * x * g⁻¹) :=
  ((contMDiff_const.mul contMDiff_id).mul contMDiff_const).mdifferentiable one_ne_zero

/-- The differential at `1` of conjugation `x ↦ g * x * g⁻¹` is the adjoint action `Ad_g`. -/
theorem mfderiv_conj_one_apply (g : G) (X : GroupLieAlgebra I G) :
    mfderiv I I (fun x : G ↦ g * x * g⁻¹) 1 X = adjointRepresentation 𝕜 I G g X := by
  rw [adjointRepresentation_apply, adjointContinuousLinearMap_apply]
  congr 2
  exact funext fun x ↦ (conjDiffeomorph_apply g x).symm

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

variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M : Type*} [TopologicalSpace M] [ChartedSpace H' M]
  {a b : M → G} {z : M}

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

end TauCeti.Lie

end
