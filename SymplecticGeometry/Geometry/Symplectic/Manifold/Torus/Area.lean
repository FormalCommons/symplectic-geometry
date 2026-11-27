/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.TopForm
public import TauCeti.Geometry.Manifold.Orientation.TopForm
public import TauCeti.Geometry.Symplectic.Manifold.Torus.Basic
public import SymplecticGeometry.Geometry.Manifold.Orientation.PositiveForm
import Mathlib.Topology.Homeomorph.Lemmas
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Integration.AddCircle
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.ChangeOfVariables

/-!
# The area of the standard symplectic two-torus

For positive periods `p`, the standard symplectic form `ω_T = dt_inl ∧ dt_inr` of the two-torus
`T = ∀ i : Unit ⊕ Unit, AddCircle (p i)` (`TauCeti.torusSymplecticForm p`) has area
`p inl * p inr` for the orientation on which it is positive, the standard orientation
`TauCeti.torusSymplecticOrientation p` (`TauCeti.integralTopForm_torusSymplecticForm`). This is
not Tau Ceti's `TauCeti.torusOrientation`, which orients the torus `∀ i : Fin n, AddCircle (p i)`
by its volume form `TauCeti.torusVolumeForm`.

The map `(a, b) ↦ (inl ↦ a, inr ↦ b)` from `AddCircle (p inl) × AddCircle (p inr)` onto `T` is a
homeomorphism (`TauCeti.addCircleProdHomeomorphTorus`), built from Mathlib's
`Homeomorph.sumPiEquivProdPi` and `Homeomorph.piUnique`, and it is smooth
(`TauCeti.contMDiff_addCircleProdHomeomorphTorus`). It pulls `ω_T` back to the area form
`ds ∧ dt` of the product, the wedge of the time forms of the two circles, whose integral for the
product of the positive orientations of the circles is `p inl * p inr`
(`AddCircle.integralTopForm_wedge_timeForm`). That product orientation is the orientation of
`ds ∧ dt` (`AddCircle.orientation_prod_orientation_eq_ofTopForm`), so the map preserves
orientation, and the change of variables formula
(`TauCeti.integralTopForm_mpullback_of_isOrientationPreservingAt`) gives the area of `T`.

## Main results

* `TauCeti.addCircleProdHomeomorphTorus`: the homeomorphism from
  `AddCircle (p inl) × AddCircle (p inr)` onto the two-torus.
* `TauCeti.contMDiff_addCircleProdHomeomorphTorus`: it is smooth.
* `TauCeti.torusSymplecticOrientation p`: the orientation of the two-torus on which
  `torusSymplecticForm p` is positive, and
  `TauCeti.orientation_eq_orientationAt_torusSymplecticOrientation_iff`: its positive tangent bases,
  and `TauCeti.isPositive_torusSymplecticForm`: the form is positive for it.
* `TauCeti.integralTopForm_torusSymplecticForm`: the integral of `torusSymplecticForm p` over the
  two-torus, for `torusSymplecticOrientation p`, is `p inl * p inr`.
-/

public section

noncomputable section

open Set
open scoped Manifold ContDiff

namespace TauCeti

variable (p : Unit ⊕ Unit → ℝ)

/-- The homeomorphism `(s, t) ↦ (inl ↦ s, inr ↦ t)` from the product of the circles
`AddCircle (p inl)` and `AddCircle (p inr)` onto the two-torus `∀ i : Unit ⊕ Unit, AddCircle (p i)`.
-/
def addCircleProdHomeomorphTorus :
    AddCircle (p (.inl ())) × AddCircle (p (.inr ())) ≃ₜ ∀ i, AddCircle (p i) :=
  ((Homeomorph.sumPiEquivProdPi Unit Unit fun i ↦ AddCircle (p i)).trans
    ((Homeomorph.piUnique _).prodCongr (Homeomorph.piUnique _))).symm

@[simp]
theorem addCircleProdHomeomorphTorus_apply_inl
    (x : AddCircle (p (.inl ())) × AddCircle (p (.inr ()))) :
    addCircleProdHomeomorphTorus p x (.inl ()) = x.1 :=
  (rfl)

@[simp]
theorem addCircleProdHomeomorphTorus_apply_inr
    (x : AddCircle (p (.inl ())) × AddCircle (p (.inr ()))) :
    addCircleProdHomeomorphTorus p x (.inr ()) = x.2 :=
  (rfl)

@[simp]
theorem addCircleProdHomeomorphTorus_symm_apply (y : ∀ i, AddCircle (p i)) :
    (addCircleProdHomeomorphTorus p).symm y = (y (.inl ()), y (.inr ())) :=
  (rfl)

variable [∀ i, Fact (0 < p i)]

/-- The homeomorphism `addCircleProdHomeomorphTorus p` from a product of two circles onto the
two-torus is smooth. -/
theorem contMDiff_addCircleProdHomeomorphTorus :
    ContMDiff (𝓘(ℝ).prod 𝓘(ℝ)) (ModelWithCorners.pi fun _ : Unit ⊕ Unit ↦ 𝓘(ℝ)) ∞
      (addCircleProdHomeomorphTorus p) :=
  contMDiff_pi_iff.2 fun i ↦ by
    rcases i with ⟨⟨⟩⟩ | ⟨⟨⟩⟩
    · simpa only [addCircleProdHomeomorphTorus_apply_inl] using contMDiff_fst
    · simpa only [addCircleProdHomeomorphTorus_apply_inr] using contMDiff_snd

/-- The **standard orientation** of the two-torus `∀ i : Unit ⊕ Unit, AddCircle (p i)`: the
orientation on which the nowhere-vanishing standard symplectic form `torusSymplecticForm p` is
positive. -/
def torusSymplecticOrientation :
    Manifold.Orientation (ModelWithCorners.pi fun _ : Unit ⊕ Unit ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i))
      (Fin 2) :=
  Manifold.Orientation.ofTopForm (by simp) (torusSymplecticForm p).val
    ((torusSymplecticForm p).isSmoothForm.of_le zero_le)
    (isSymplectic_torusSymplecticForm p).isNondegenerate.apply_ne_zero

theorem torusSymplecticOrientation_def :
    torusSymplecticOrientation p =
      Manifold.Orientation.ofTopForm (by simp) (torusSymplecticForm p).val
        ((torusSymplecticForm p).isSmoothForm.of_le zero_le)
        (isSymplectic_torusSymplecticForm p).isNondegenerate.apply_ne_zero :=
  (rfl)

/-- A tangent basis of the two-torus is positive for `torusSymplecticOrientation p` exactly when
the standard symplectic form `torusSymplecticForm p` is positive on it. -/
theorem orientation_eq_orientationAt_torusSymplecticOrientation_iff {x : ∀ i, AddCircle (p i)}
    (b : Module.Basis (Fin 2) ℝ
      (TangentSpace (ModelWithCorners.pi fun _ : Unit ⊕ Unit ↦ 𝓘(ℝ)) x)) :
    b.orientation = (torusSymplecticOrientation p).orientationAt x ↔
      0 < (torusSymplecticForm p).val x b :=
  Manifold.Orientation.orientation_eq_orientationAt_ofTopForm_iff _ _ _ b

/-- The standard symplectic form `torusSymplecticForm p` is positive for the standard orientation
`torusSymplecticOrientation p` of the two-torus. -/
theorem isPositive_torusSymplecticForm :
    (torusSymplecticOrientation p).IsPositive (torusSymplecticForm p).val :=
  Manifold.Orientation.isPositive_ofTopForm _ _ _

/-- **The area of the standard symplectic two-torus.** The integral of the standard symplectic
form `torusSymplecticForm p` over the torus `∀ i : Unit ⊕ Unit, AddCircle (p i)`, for the
orientation on which that form is positive, is the product `p inl * p inr` of the periods. -/
theorem integralTopForm_torusSymplecticForm :
    integralTopForm (torusSymplecticOrientation p) (torusSymplecticForm p).val =
      p (.inl ()) * p (.inr ()) := by
  set a := p (.inl ())
  set b := p (.inr ())
  set Φ := addCircleProdHomeomorphTorus p
  have hΦ := contMDiff_addCircleProdHomeomorphTorus p
  -- `Φ` pulls `ω_T` back to the area form `ds ∧ dt` of the product.
  set W : SmoothTwoForm (𝓘(ℝ).prod 𝓘(ℝ)) (AddCircle a × AddCircle b) :=
    SmoothForm.wedge (SmoothForm.mpullback Prod.fst contMDiff_fst (AddCircle.timeForm a))
    (SmoothForm.mpullback Prod.snd contMDiff_snd (AddCircle.timeForm b)) with hW
  have h1 : SmoothForm.mpullback Φ hΦ (torusTimeForm p (.inl ())) =
      SmoothForm.mpullback Prod.fst contMDiff_fst (AddCircle.timeForm a) := by
    rw [torusTimeForm_def, ← LinearMap.comp_apply, ← SmoothForm.mpullback_comp]
    exact SmoothForm.mpullback_congr _ _
      (funext (addCircleProdHomeomorphTorus_apply_inl p)) _
  have h2 : SmoothForm.mpullback Φ hΦ (torusTimeForm p (.inr ())) =
      SmoothForm.mpullback Prod.snd contMDiff_snd (AddCircle.timeForm b) := by
    rw [torusTimeForm_def, ← LinearMap.comp_apply, ← SmoothForm.mpullback_comp]
    exact SmoothForm.mpullback_congr _ _
      (funext (addCircleProdHomeomorphTorus_apply_inr p)) _
  have hpull : SmoothForm.mpullback Φ hΦ (torusSymplecticForm p) = W := by
    rw [torusSymplecticForm_def, Fintype.sum_unique, hW, ← h1, ← h2]
    exact SmoothForm.mpullback_wedge (k := 1) (l := 1) Φ hΦ _ _
  rw [← Φ.isOpenEmbedding.integralTopForm_mpullback_of_isOrientationPreservingAt
    (o := (AddCircle.orientation a).prod (AddCircle.orientation b))
    (fun x ↦ ?_) (by rw [Φ.surjective.range_eq]; exact subset_univ _)]
  · rw [← SmoothForm.coe_mpullback _ hΦ, hpull]
    exact AddCircle.integralTopForm_wedge_timeForm a b
  · rw [AddCircle.orientation_prod_orientation_eq_ofTopForm, torusSymplecticOrientation_def]
    refine Manifold.Orientation.isOrientationPreservingAt_ofTopForm_of_mpullback_eq_smul
      _ _ _ _ _ _ one_pos ?_
    rw [one_smul, ← SmoothForm.coe_mpullback _ hΦ, hpull]

end TauCeti

end
