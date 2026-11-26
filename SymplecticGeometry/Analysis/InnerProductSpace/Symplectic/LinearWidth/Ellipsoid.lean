/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Analysis.InnerProductSpace.Symplectic.Ellipsoid.Spectrum
public import SymplecticGeometry.Analysis.InnerProductSpace.Symplectic.LinearWidth.Basic

/-!
# The linear symplectic width of an ellipsoid

The standard ellipsoid `E(r)` lies between the ball `B²ⁿ(rᵢ)` and the cylinder `Z²ⁿ(rᵢ)` over
the `i`-th coordinate plane, for `rᵢ` its smallest radius. Both have width `π rᵢ²`, so this is
the width of `E(r)`. An ellipsoid `{z | Q z ≤ 1}`, for `Q` positive definite, is carried onto
some `E(r)` by a linear symplectic map, and the radii `r` form its symplectic spectrum; so its
width is `π s²` for the smallest element `s` of the spectrum. The width of the ellipsoid is
attained both by a symplectic ball inside it and by a symplectic cylinder around it, so it is
the supremum of the widths of the former and the infimum of the widths of the latter.

## Main results

* `SymplecticGeometry.stdEllipsoid_subset_stdCylinder`: `E(r) ⊆ Z²ⁿ(rᵢ)` for `0 < rᵢ`.
* `SymplecticGeometry.linearSymplecticWidth_stdEllipsoid`: `w_L(E(r)) = π rᵢ²` for a positive
  smallest radius `rᵢ`.
* `SymplecticGeometry.linearSymplecticWidth_setOfPred_le_one_eq`: the ellipsoid of a positive
  definite form has width `π s²`, for `s` the smallest element of its symplectic spectrum.
* `SymplecticGeometry.linearSymplecticWidth_setOfPred_le_one`: the width of the ellipsoid of a
  positive definite form, in terms of its symplectic spectrum, as a supremum over symplectic
  balls and as an infimum over symplectic cylinders.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.4
  (Theorem 2.4.8)
-/

public section

namespace SymplecticGeometry

open TauCeti TauCeti.SymplecticForm Metric StdSpace
open scoped ENNReal NNReal Real

variable {ι : Type*} [Fintype ι]

/-- The standard ellipsoid `E(r)` lies in the cylinder of radius `rᵢ` over the `i`-th
coordinate plane, for `0 < rᵢ`. -/
theorem stdEllipsoid_subset_stdCylinder {r : ι → ℝ} {i : ι} (hi : 0 < r i) :
    stdEllipsoid r ⊆ stdCylinder i (r i) := by
  intro z hz
  rw [mem_stdEllipsoid_iff] at hz
  rw [mem_stdCylinder_iff_of_nonneg hi.le]
  have h : (z.x i ^ 2 + z.y i ^ 2) / r i ^ 2 ≤ 1 :=
    (Finset.single_le_sum (fun j _ ↦ by positivity) (Finset.mem_univ i)).trans hz
  rwa [div_le_one (by positivity)] at h

/-- The standard ellipsoid `E(r)` has width `π rᵢ²`, for `rᵢ` its smallest radius, if that
radius is positive. -/
theorem linearSymplecticWidth_stdEllipsoid {r : ι → ℝ} {i : ι} (hi : 0 < r i)
    (hmin : ∀ j, r i ≤ r j) :
    linearSymplecticWidth (stdEllipsoid r) = ENNReal.ofReal (π * r i ^ 2) := by
  refine le_antisymm ((linearSymplecticWidth_mono (stdEllipsoid_subset_stdCylinder hi)).trans
    (linearSymplecticWidth_stdCylinder_le i (r i))) ?_
  exact ofReal_pi_mul_sq_le_linearSymplecticWidth_of_closedBall_subset hi.le
    (closedBall_subset_stdEllipsoid hmin)

/-- The ellipsoid `{z | Q z ≤ 1}` has width `π s²`, for `s` the smallest element of the
symplectic spectrum of `Q`. Such an `s` exists only if `Q` is positive definite. -/
theorem linearSymplecticWidth_setOfPred_le_one_eq {Q : QuadraticForm ℝ (StdSpace ι)}
    {s : ℝ} (hs : s ∈ symplecticSpectrum Q)
    (hmin : ∀ t ∈ symplecticSpectrum Q, s ≤ t) :
    linearSymplecticWidth {z | Q z ≤ 1} = ENNReal.ofReal (π * s ^ 2) := by
  obtain ⟨r, e, i, hr, he, h, hspec, rfl⟩ :=
    exists_isSymplectomorphism_image_eq_stdEllipsoid_of_mem_symplecticSpectrum hs
  have hi : ∀ j, r i ≤ r j := fun j ↦
    hmin _ (hspec ▸ Multiset.mem_map_of_mem _ (Finset.mem_univ j))
  rw [← linearSymplecticWidth_stdEllipsoid (hr i) hi, ← h, ← LinearEquiv.coe_toAffineEquiv,
    linearSymplecticWidth_image ((LinearEquiv.toAffineEquiv_mem_affineSymplecticGroup_iff e).2 he)]

/-- **The linear symplectic width of an ellipsoid.** Let `Q` be a quadratic form on `ℝ²ⁿ`
and `s` the smallest element of its symplectic spectrum (so `Q` is positive definite). The ellipsoid
`E = {z | Q z ≤ 1}` has width `π s²`; this is the supremum of the widths of the affine
symplectic images of balls that lie in `E`, and the infimum of the widths of the affine
symplectic images of cylinders that contain `E`.

Milestone: *Linear symplectic width of an ellipsoid*. -/
theorem linearSymplecticWidth_setOfPred_le_one {Q : QuadraticForm ℝ (StdSpace ι)}
    {s : ℝ} (hs : s ∈ symplecticSpectrum Q)
    (hmin : ∀ t ∈ symplecticSpectrum Q, s ≤ t) :
    linearSymplecticWidth {z | Q z ≤ 1} = ENNReal.ofReal (π * s ^ 2) ∧
    linearSymplecticWidth {z | Q z ≤ 1} =
      ⨆ (f ∈ affineSymplecticGroup (stdForm ι)) (r : ℝ≥0)
        (_ : f '' closedBall 0 (r : ℝ) ⊆ {z | Q z ≤ 1}),
        linearSymplecticWidth (f '' closedBall 0 (r : ℝ)) ∧
    linearSymplecticWidth {z | Q z ≤ 1} =
      ⨅ (f ∈ affineSymplecticGroup (stdForm ι)) (i : ι) (R : ℝ)
        (_ : {z | Q z ≤ 1} ⊆ f '' stdCylinder i R),
        linearSymplecticWidth (f '' stdCylinder i R) := by
  have hE := linearSymplecticWidth_setOfPred_le_one_eq hs hmin
  refine ⟨hE, linearSymplecticWidth_eq_iSup_image_closedBall _, ?_⟩
  · refine le_antisymm (le_iInf₂ fun _ _ ↦ le_iInf₂ fun i R ↦ le_iInf fun h ↦
      linearSymplecticWidth_mono h) ?_
    obtain ⟨r, e, i, hr, he, h, -, rfl⟩ :=
      exists_isSymplectomorphism_image_eq_stdEllipsoid_of_mem_symplecticSpectrum hs
    have hg := (LinearEquiv.toAffineEquiv_mem_affineSymplecticGroup_iff e).2 he
    have hsub : {z | Q z ≤ 1} ⊆
        (e.toAffineEquiv⁻¹ : StdSpace ι ≃ᵃ[ℝ] StdSpace ι) '' stdCylinder i (r i) := by
      rw [AffineEquiv.inv_def, AffineEquiv.image_symm, ← Set.image_subset_iff,
        LinearEquiv.coe_toAffineEquiv, h]
      exact stdEllipsoid_subset_stdCylinder (hr i)
    refine (iInf₂_le _ (inv_mem hg)).trans
      ((iInf₂_le i (r i)).trans ((iInf_le _ hsub).trans ?_))
    rw [linearSymplecticWidth_image_stdCylinder (inv_mem hg) i (hr i).le, hE]

end SymplecticGeometry

end
