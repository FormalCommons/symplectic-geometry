/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.TopForm
public import TauCeti.Geometry.Manifold.Orientation.TopForm
public import TauCeti.Geometry.Symplectic.Manifold.Torus.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.AddCircle
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.ChangeOfVariables
import TauCeti.Geometry.Manifold.Orientation.AddCircle

/-!
# The area of the standard symplectic two-torus

For positive periods `p`, the standard symplectic form `ω_T = dt_inl ∧ dt_inr` of the two-torus
`T = ∀ i : Unit ⊕ Unit, AddCircle (p i)` (`TauCeti.torusSymplecticForm p`) has area
`p inl * p inr` for the orientation on which it is positive
(`TauCeti.integralTopForm_torusSymplecticForm`).

The map `(a, b) ↦ (inl ↦ a, inr ↦ b)` from `AddCircle (p inl) × AddCircle (p inr)` onto `T` is a
homeomorphism, built from Mathlib's `Homeomorph.sumPiEquivProdPi` and `Homeomorph.piUnique`, and
it is smooth. It pulls `ω_T` back to the area form `ds ∧ dt` of the product, the wedge of the time
forms of the two circles, whose integral for the product of the positive orientations of the
circles is `p inl * p inr` (`AddCircle.integralTopForm_wedge_timeForm`). That product orientation
is the orientation of `ds ∧ dt`, so the map preserves orientation, and the change of variables
formula (`TauCeti.integralTopForm_mpullback_of_isOrientationPreservingAt`) gives the area of `T`.

## Main results

* `TauCeti.integralTopForm_torusSymplecticForm`: the integral of `torusSymplecticForm p` over the
  two-torus, for the orientation of that form, is `p inl * p inr`.
-/

public section

noncomputable section

open Set
open scoped Manifold ContDiff

namespace TauCeti

variable (p : Unit ⊕ Unit → ℝ) [∀ i, Fact (0 < p i)]

/-- **The area of the standard symplectic two-torus.** The integral of the standard symplectic
form `torusSymplecticForm p` over the torus `∀ i : Unit ⊕ Unit, AddCircle (p i)`, for the
orientation on which that form is positive, is the product `p inl * p inr` of the periods. -/
theorem integralTopForm_torusSymplecticForm :
    integralTopForm (Manifold.Orientation.ofTopForm (by simp) (torusSymplecticForm p).val
      ((torusSymplecticForm p).isSmoothForm.of_le zero_le)
      (isSymplectic_torusSymplecticForm p).isNondegenerate.apply_ne_zero)
      (torusSymplecticForm p).val = p (.inl ()) * p (.inr ()) := by
  set a := p (.inl ())
  set b := p (.inr ())
  -- The homeomorphism `(s, t) ↦ (inl ↦ s, inr ↦ t)` and its smoothness.
  let Φ : AddCircle a × AddCircle b ≃ₜ ∀ i, AddCircle (p i) :=
    ((Homeomorph.sumPiEquivProdPi Unit Unit fun i ↦ AddCircle (p i)).trans
      ((Homeomorph.piUnique _).prodCongr (Homeomorph.piUnique _))).symm
  have hΦ : ContMDiff (𝓘(ℝ).prod 𝓘(ℝ)) (ModelWithCorners.pi fun _ : Unit ⊕ Unit ↦ 𝓘(ℝ)) ∞ Φ :=
    contMDiff_pi_iff.2 fun i ↦ by
      cases i
      exacts [contMDiff_fst, contMDiff_snd]
  -- `Φ` pulls `ω_T` back to the area form `ds ∧ dt` of the product.
  set W : SmoothTwoForm (𝓘(ℝ).prod 𝓘(ℝ)) (AddCircle a × AddCircle b) :=
    SmoothForm.wedge (SmoothForm.mpullback Prod.fst contMDiff_fst (AddCircle.timeForm a))
    (SmoothForm.mpullback Prod.snd contMDiff_snd (AddCircle.timeForm b)) with hW
  have h1 : SmoothForm.mpullback Φ hΦ (torusTimeForm p (.inl ())) =
      SmoothForm.mpullback Prod.fst contMDiff_fst (AddCircle.timeForm a) := by
    rw [torusTimeForm_def, ← LinearMap.comp_apply, ← SmoothForm.mpullback_comp]
    -- The coordinate of `Φ` at `inl` is `Prod.fst` by definition.
    rfl
  have h2 : SmoothForm.mpullback Φ hΦ (torusTimeForm p (.inr ())) =
      SmoothForm.mpullback Prod.snd contMDiff_snd (AddCircle.timeForm b) := by
    rw [torusTimeForm_def, ← LinearMap.comp_apply, ← SmoothForm.mpullback_comp]
    -- The coordinate of `Φ` at `inr` is `Prod.snd` by definition.
    rfl
  have hpull : SmoothForm.mpullback Φ hΦ (torusSymplecticForm p) = W := by
    rw [torusSymplecticForm_def, Fintype.sum_unique, hW, ← h1, ← h2]
    exact SmoothForm.mpullback_wedge (k := 1) (l := 1) Φ hΦ _ _
  have hW1 (x : AddCircle a × AddCircle b) : 0 < W.val x (Module.Basis.finTwoProd ℝ) := by
    have h : W.eval₂ x ((1 : ℝ), (0 : ℝ)) ((0 : ℝ), (1 : ℝ)) = 1 :=
      (AddCircle.eval₂_wedge_timeForm a b x _ _).trans (by norm_num)
    replace h := (SmoothBundleForm.eval₂_apply W x _ _).symm.trans h
    have hb : (⇑(Module.Basis.finTwoProd ℝ) : Fin 2 → ℝ × ℝ) = ![(1, 0), (0, 1)] := by
      ext i : 1
      fin_cases i <;> simp
    rw [hb]
    exact h.symm ▸ one_pos
  have hW0 (x : AddCircle a × AddCircle b) : W.val x ≠ 0 := fun h ↦
    (hW1 x).ne' ((congrFun (congrArg DFunLike.coe h) _).trans
      (congrFun ContinuousAlternatingMap.coe_zero _))
  -- The product orientation of the circles is the orientation of `ds ∧ dt`.
  have hprod : (AddCircle.orientation a).prod (AddCircle.orientation b) =
      Manifold.Orientation.ofTopForm (by simp) W.val (W.isSmoothForm.of_le zero_le) hW0 :=
    Manifold.Orientation.ext fun x ↦ by
      rw [AddCircle.orientationAt_orientation_prod_orientation]
      exact (Manifold.Orientation.orientation_eq_orientationAt_ofTopForm_iff _ _ _ _).2 (hW1 x)
  rw [← Φ.isOpenEmbedding.integralTopForm_mpullback_of_isOrientationPreservingAt
    (o := (AddCircle.orientation a).prod (AddCircle.orientation b))
    (fun x ↦ ?_) (by rw [Φ.surjective.range_eq]; exact subset_univ _)]
  · rw [← SmoothForm.coe_mpullback _ hΦ, hpull]
    exact AddCircle.integralTopForm_wedge_timeForm a b
  · rw [hprod]
    refine Manifold.Orientation.isOrientationPreservingAt_ofTopForm_of_mpullback_eq_smul
      _ _ _ _ _ _ one_pos ?_
    rw [one_smul, ← SmoothForm.coe_mpullback _ hΦ, hpull]

end TauCeti

end
