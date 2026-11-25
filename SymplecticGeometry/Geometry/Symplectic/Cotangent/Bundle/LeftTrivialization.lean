/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.LeftTrivialization
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Lift

/-!
# Right translation in the left trivialization of `T*G`

Let `G` be a real Lie group modelled on `E`, and `Φ : G × 𝔤* ≃ T*G` Tau Ceti's left
trivialization of its cotangent bundle (`TauCeti.CotangentBundle.leftTrivialization`). Tau Ceti
proves that `Φ^* ω` is invariant under left multiplication on the factor `G`
(`TauCeti.CotangentBundle.leftTrivialization_mul` with
`TauCeti.CotangentBundle.mpullback_smul_symplecticForm`). This file proves the counterpart for
right multiplication: for `h : G`, the form `Φ^* ω` is invariant under
`(g, a) ↦ (g * h, a ∘ Ad_h)`
(`TauCeti.CotangentBundle.mpullback_prodMap_mul_right_mpullback_leftTrivialization_symplecticForm`).

In the left trivialization, this map is the cotangent lift of right multiplication by `h`
(`TauCeti.CotangentBundle.cotangentRel_mul_right_leftTrivialization`, read through
`TauCeti.CotangentBundle.cotangentRel_diffeomorph_iff`), and cotangent lifts of diffeomorphisms
preserve the canonical symplectic form (`Diffeomorph.mpullback_cotangent_symplecticForm`).

## Main results

* `TauCeti.CotangentBundle.mpullback_prodMap_mul_right_mpullback_leftTrivialization_symplecticForm`:
  the pullback `Φ^* ω` of the canonical symplectic form along the left trivialization is invariant
  under `(g, a) ↦ (g * h, a ∘ Ad_h)`.

## References

* J. E. Marsden, T. S. Ratiu, *Introduction to Mechanics and Symmetry*, 2nd ed., Texts in Applied
  Mathematics 17, Springer, 1999.
-/

public section

open Bundle TauCeti.Manifold
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.CotangentBundle

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {G : Type*} [TopologicalSpace G]
  [ChartedSpace H G] [Group G] [LieGroup I ∞ G]

/-- The pullback `Φ^* ω` of the canonical symplectic form of `T*G` along the left trivialization
`Φ : G × 𝔤* ≃ T*G` is invariant under `(g, a) ↦ (g * h, a ∘ Ad_h)`, for each `h : G`. -/
@[simp]
theorem mpullback_prodMap_mul_right_mpullback_leftTrivialization_symplecticForm (h : G) :
    SmoothForm.mpullback
        (Prod.map (· * h) fun a : E →L[ℝ] ℝ ↦
          (a ∘L Lie.adjointContinuousLinearMap (I := I) h : E →L[ℝ] ℝ))
        (by exact contMDiff_mul_right.prodMap (contDiff_id.clm_comp contDiff_const).contMDiff)
        (SmoothForm.mpullback (leftTrivialization I G) (leftTrivialization I G).contMDiff
          (symplecticForm I G)) =
      SmoothForm.mpullback (leftTrivialization I G) (leftTrivialization I G).contMDiff
        (symplecticForm I G) := by
  -- Right multiplication by `h`, as a diffeomorphism of `G`.
  let R : G ≃ₘ⟮I, I⟯ G :=
    { Equiv.mulRight h with
      contMDiff_toFun := contMDiff_mul_right
      contMDiff_invFun := contMDiff_mul_right }
  -- In the left trivialization, `(g, a) ↦ (g * h, a ∘ Ad_h)` is the cotangent lift of `R`.
  have hR : (leftTrivialization I G ∘
      Prod.map (· * h) fun a : E →L[ℝ] ℝ ↦
        (a ∘L Lie.adjointContinuousLinearMap (I := I) h : E →L[ℝ] ℝ)) =
        R.cotangent ∘ leftTrivialization I G :=
    funext fun p ↦ ((cotangentRel_diffeomorph_iff I I R _ _).1
      (cotangentRel_mul_right_leftTrivialization p.1 h p.2)).symm
  rw [SmoothForm.mpullback_mpullback_of_comp_eq _ _ (leftTrivialization I G).contMDiff
    R.cotangent.contMDiff hR, Diffeomorph.mpullback_cotangent_symplecticForm]

end TauCeti.CotangentBundle

end
