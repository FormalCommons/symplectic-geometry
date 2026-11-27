/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Basic
public import Mathlib.Topology.Homotopy.Equiv
public import SymplecticGeometry.Topology.Sets.Annulus
import Mathlib.Analysis.Normed.Module.Connected
import TauCeti.Analysis.Normed.Module.Ball.Radial.PuncturedBall
import TauCeti.Topology.Homotopy.DeformationRetract

/-!
# Open annuli up to homotopy

For a real normed space `E`, this file shows that the open annulus `a < ‖x‖ < b` is path
connected when `0 ≤ a < b` and `E` has dimension at least two, and that for `0 ≤ a' ≤ a < b`
the inclusion of the annulus `a < ‖x‖ < b` into the annulus `a' < ‖x‖ < b` is a homotopy
equivalence. For the latter, Tau Ceti's radial push `TauCeti.puncturedBallPush` with
radius `m = (a + b) / 2` moves each point of the larger annulus along its ray, never inward and
never past norm `max ‖x‖ m`, and ends with norm at least `m`. So it is a deformation of the
larger annulus into the smaller one that keeps the smaller one in itself, and
`ContinuousMap.HomotopyEquiv.ofWeakDeformationRetraction` makes the inclusion a homotopy
equivalence.

## Main results

* `SymplecticGeometry.isPathConnected_annulus`: the annulus is path connected.
* `SymplecticGeometry.annulusHomotopyEquiv`: the inclusion of `annulus E a b` into
  `annulus E a' b` as a homotopy equivalence, with `SymplecticGeometry.annulusHomotopyEquiv_toFun`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Cambridge University Press, 2002, Chapter 0 (deformation retractions).
-/

public section

open Set unitInterval TauCeti

namespace SymplecticGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- For `0 ≤ a < b`, the open annulus `a < ‖x‖ < b` of a real normed space of dimension at least
two is path connected. -/
theorem isPathConnected_annulus (h : 1 < Module.rank ℝ E) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    IsPathConnected (annulus E a b : Set E) := by
  have hS := (isPathConnected_sphere h (0 : E) zero_le_one).prod
    ((convex_Ioo a b).isPathConnected (nonempty_Ioo.2 hab))
  convert hS.image (f := fun p : E × ℝ ↦ p.2 • p.1) (by fun_prop) using 1
  ext x
  simp only [coe_annulus, mem_ofPred_eq, mem_image, Prod.exists, mem_prod, mem_sphere_iff_norm,
    sub_zero, mem_Ioo]
  refine ⟨fun hx ↦ ⟨‖x‖⁻¹ • x, ‖x‖, ⟨?_, hx⟩, ?_⟩, ?_⟩
  · have : ‖x‖ ≠ 0 := (ha.trans_lt hx.1).ne'
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ this]
  · have : ‖x‖ ≠ 0 := (ha.trans_lt hx.1).ne'
    rw [smul_smul, mul_inv_cancel₀ this, one_smul]
  · rintro ⟨u, r, ⟨hu, hr⟩, rfl⟩
    rwa [norm_smul, hu, mul_one, Real.norm_of_nonneg (ha.trans hr.1.le)]

section HomotopyEquiv

variable {a a' b : ℝ}

/-- For `0 ≤ a' ≤ a < b`, the inclusion of the annulus `a < ‖x‖ < b` into the annulus
`a' < ‖x‖ < b`, as a homotopy equivalence. -/
noncomputable def annulusHomotopyEquiv (ha' : 0 ≤ a') (h : a' ≤ a) (hab : a < b) :
    ContinuousMap.HomotopyEquiv (annulus E a b) (annulus E a' b) :=
  have hm : (a + b) / 2 < b := by linarith
  -- the push never decreases the norm
  have hge : ∀ (t : I) (y : E), ‖y‖ ≤ ‖puncturedBallPush ((a + b) / 2) t y‖ := fun t y ↦
    (norm_puncturedBallPush _ t y).symm ▸ le_mul_of_one_le_left (norm_nonneg _) (le_max_left _ _)
  have hlt : ∀ (t : I) (x : annulus E a' b),
      ‖puncturedBallPush ((a + b) / 2) t (x : E)‖ < b := fun t x ↦
    (norm_puncturedBallPush_le _ _ _).trans_lt (max_lt (mem_annulus.1 x.property).2 hm)
  .ofWeakDeformationRetraction (annulus_mono h le_rfl)
    (fun p ↦ puncturedBallPush ((a + b) / 2) p.1 (p.2 : E))
    (continuous_iff_continuousAt.2 fun p ↦
      (continuousAt_puncturedBallPush (t := p.1) _ (ne_zero_of_mem_annulus ha' p.2.property)).comp
        (f := fun q : I × annulus E a' b ↦ (q.1, (q.2 : E)))
        (by fun_prop : Continuous _).continuousAt)
    (fun p ↦ mem_annulus.2 ⟨(mem_annulus.1 p.2.property).1.trans_le
      (hge _ _), hlt p.1 p.2⟩)
    (fun _ ↦ puncturedBallPush_zero _ _)
    (fun x ↦ mem_annulus.2 ⟨(by linarith : a < (a + b) / 2).trans_le
      (le_norm_puncturedBallPush_one _ (ne_zero_of_mem_annulus ha' x.property)), hlt 1 x⟩)
    (fun t x hx ↦ mem_annulus.2 ⟨(mem_annulus.1 hx).1.trans_le
      (hge _ _), hlt t x⟩)

@[simp]
theorem annulusHomotopyEquiv_toFun (ha' : 0 ≤ a') (h : a' ≤ a) (hab : a < b) :
    (annulusHomotopyEquiv (E := E) ha' h hab).toFun =
      ContinuousMap.inclusion (annulus_mono (E := E) h (le_refl b)) :=
  ContinuousMap.ext fun _ ↦
    Subtype.ext (ContinuousMap.HomotopyEquiv.coe_ofWeakDeformationRetraction_apply ..)

end HomotopyEquiv

end SymplecticGeometry

end
