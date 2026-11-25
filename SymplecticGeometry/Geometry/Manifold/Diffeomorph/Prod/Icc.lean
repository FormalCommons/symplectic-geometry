/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Icc
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth

/-!
# Restricting a diffeomorphism of `M × ℝ` onto `M' × ℝ` to `M × [a, b]`

Let `Φ` be a `C^n` diffeomorphism of `M × ℝ` onto `M' × ℝ` such that `Φ` and `Φ⁻¹` both preserve
the second coordinate `t` for every `t ∈ [a, b]`, `a < b`. Then `Φ` maps each level `M × {t}`,
`t ∈ [a, b]`, onto `M' × {t}`, so it restricts to a `C^n` diffeomorphism
`Diffeomorph.restrictProdIcc` of the manifold with boundary `M × [a, b]` onto `M' × [a, b]`. Its
inverse is the restriction of `Φ⁻¹` (`Diffeomorph.restrictProdIcc_symm`).

The restriction preserves the second coordinate (`Diffeomorph.restrictProdIcc_apply_snd`) and
commutes with the inclusions `Prod.map id Subtype.val` of `M × [a, b]` into `M × ℝ` and of
`M' × [a, b]` into `M' × ℝ` (`Diffeomorph.prodMap_subtypeVal_comp_restrictProdIcc`, and
`Diffeomorph.prodMap_subtypeVal_comp_symm_restrictProdIcc` for the inverses). So, for `n = ∞`,
pulling a smooth form on `M' × ℝ` back by `Φ` and restricting it to `M × [a, b]` is restricting it
to `M' × [a, b]` first and then pulling it back by the restriction
(`Diffeomorph.mpullback_restrictProdIcc_mpullback_prodMap_subtypeVal`).

Both hypotheses are used: the one on `Φ` makes the restriction of `Φ⁻¹` a left inverse of that
of `Φ`, and the one on `Φ⁻¹` makes it a right inverse.

The restriction is smooth componentwise: its second component is the projection, and its first
is `Prod.fst ∘ Φ ∘ Prod.map id Subtype.val`, smooth by Mathlib's `contMDiff_subtypeVal_Icc`. The
construction follows Tau Ceti's `Diffeomorph.restrictUnitClosedBall` for the closed unit ball.
-/

public section

open Set
open scoped Manifold ContDiff

namespace Diffeomorph

variable {E H M E' H' M' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M'] [ChartedSpace H' M']
  {a b : ℝ} [Fact (a < b)] {n : WithTop ℕ∞}

section restrictProdIcc

variable (Φ : (M × ℝ) ≃ₘ^n⟮I.prod 𝓘(ℝ), I'.prod 𝓘(ℝ)⟯ M' × ℝ)

/-- The restriction to `M × [a, b]` of a `C^n` diffeomorphism `Φ` of `M × ℝ` onto `M' × ℝ` such
that `Φ` and its inverse preserve the second coordinate `t` for every `t ∈ [a, b]`: it sends
`(x, t)` to `((Φ (x, t)).1, t)`, a diffeomorphism of `M × [a, b]` onto `M' × [a, b]`. -/
noncomputable def restrictProdIcc (hΦ : ∀ x, ∀ t ∈ Icc a b, (Φ (x, t)).2 = t)
    (hΦ' : ∀ x, ∀ t ∈ Icc a b, (Φ.symm (x, t)).2 = t) :
    (M × Icc a b) ≃ₘ^n⟮I.prod (𝓡∂ 1), I'.prod (𝓡∂ 1)⟯ M' × Icc a b where
  toFun p := ((Φ (p.1, p.2)).1, p.2)
  invFun p := ((Φ.symm (p.1, p.2)).1, p.2)
  left_inv p := by
    simp only
    rw [show ((Φ (p.1, p.2)).1, (p.2 : ℝ)) = Φ (p.1, p.2) from
      Prod.ext rfl (hΦ p.1 p.2 p.2.property).symm, Φ.symm_apply_apply]
  right_inv p := by
    simp only
    rw [show ((Φ.symm (p.1, p.2)).1, (p.2 : ℝ)) = Φ.symm (p.1, p.2) from
      Prod.ext rfl (hΦ' p.1 p.2 p.2.property).symm, Φ.apply_symm_apply]
  contMDiff_toFun :=
    (contMDiff_fst.comp (Φ.contMDiff.comp (contMDiff_id.prodMap contMDiff_subtypeVal_Icc))).prodMk
      contMDiff_snd
  contMDiff_invFun :=
    (contMDiff_fst.comp
      (Φ.symm.contMDiff.comp (contMDiff_id.prodMap contMDiff_subtypeVal_Icc))).prodMk contMDiff_snd

variable (hΦ : ∀ x, ∀ t ∈ Icc a b, (Φ (x, t)).2 = t)
  (hΦ' : ∀ x, ∀ t ∈ Icc a b, (Φ.symm (x, t)).2 = t)

@[simp]
theorem restrictProdIcc_apply (p : M × Icc a b) :
    Φ.restrictProdIcc hΦ hΦ' p = ((Φ (p.1, p.2)).1, p.2) :=
  (rfl)

/-- The restriction of `Φ` to `M × [a, b]` preserves the second coordinate. -/
theorem restrictProdIcc_apply_snd (p : M × Icc a b) : (Φ.restrictProdIcc hΦ hΦ' p).2 = p.2 :=
  (rfl)

/-- The inverse of the restriction of `Φ` to `M × [a, b]` is the restriction of `Φ⁻¹` to
`M' × [a, b]`. -/
@[simp]
theorem restrictProdIcc_symm :
    (Φ.restrictProdIcc hΦ hΦ').symm = Φ.symm.restrictProdIcc hΦ' hΦ :=
  (rfl)

/-- The restriction of `Φ` to `M × [a, b]` commutes with the inclusions `M × [a, b] → M × ℝ` and
`M' × [a, b] → M' × ℝ`. -/
theorem prodMap_subtypeVal_comp_restrictProdIcc :
    Prod.map id Subtype.val ∘ Φ.restrictProdIcc hΦ hΦ' = Φ ∘ Prod.map id Subtype.val :=
  funext fun p ↦ Prod.ext rfl (hΦ p.1 p.2 p.2.property).symm

/-- The inverse of the restriction of `Φ` to `M × [a, b]` commutes with the inclusions
`M' × [a, b] → M' × ℝ` and `M × [a, b] → M × ℝ`, as `Φ⁻¹`. -/
theorem prodMap_subtypeVal_comp_symm_restrictProdIcc :
    Prod.map id Subtype.val ∘ (Φ.restrictProdIcc hΦ hΦ').symm =
      Φ.symm ∘ Prod.map id Subtype.val := by
  rw [restrictProdIcc_symm]
  exact Φ.symm.prodMap_subtypeVal_comp_restrictProdIcc hΦ' hΦ

end restrictProdIcc

/-- For a diffeomorphism `Φ` of `M × ℝ` onto `M' × ℝ` that keeps the levels over `[a, b]`, and a
smooth form `α` on `M' × ℝ`, the pull-back by the restriction of `Φ` of the restriction of `α` to
`M' × [a, b]` is the restriction of `Φ^* α` to `M × [a, b]`. -/
theorem mpullback_restrictProdIcc_mpullback_prodMap_subtypeVal [IsManifold I 1 M]
    [IsManifold I' 1 M'] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}
    (Φ : (M × ℝ) ≃ₘ⟮I.prod 𝓘(ℝ), I'.prod 𝓘(ℝ)⟯ M' × ℝ)
    (hΦ : ∀ x, ∀ t ∈ Icc a b, (Φ (x, t)).2 = t) (hΦ' : ∀ x, ∀ t ∈ Icc a b, (Φ.symm (x, t)).2 = t)
    (α : TauCeti.SmoothForm (I'.prod 𝓘(ℝ)) (M' × ℝ) F k) :
    TauCeti.SmoothForm.mpullback (Φ.restrictProdIcc hΦ hΦ') (Φ.restrictProdIcc hΦ hΦ').contMDiff
        (TauCeti.SmoothForm.mpullback (Prod.map id Subtype.val)
          (contMDiff_id.prodMap contMDiff_subtypeVal_Icc) α) =
      TauCeti.SmoothForm.mpullback (Prod.map id Subtype.val)
        (contMDiff_id.prodMap contMDiff_subtypeVal_Icc)
        (TauCeti.SmoothForm.mpullback Φ Φ.contMDiff α) :=
  TauCeti.SmoothForm.mpullback_mpullback_of_comp_eq _ _ _ _
    (Φ.prodMap_subtypeVal_comp_restrictProdIcc hΦ hΦ') α

end Diffeomorph

end
