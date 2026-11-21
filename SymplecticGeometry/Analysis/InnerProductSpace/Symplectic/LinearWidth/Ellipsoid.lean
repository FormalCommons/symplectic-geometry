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
* `SymplecticGeometry.linearSymplecticWidth_stdEllipsoid`: `w_L(E(r)) = π rᵢ²` for positive
  radii with smallest radius `rᵢ`.
* `SymplecticGeometry.linearSymplecticWidth_setOf_le_one`: the width of the ellipsoid of a
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

/-- The standard ellipsoid `E(r)` with positive radii has width `π rᵢ²`, for `rᵢ` its smallest
radius. -/
theorem linearSymplecticWidth_stdEllipsoid {r : ι → ℝ} (hr : ∀ j, 0 < r j) {i : ι}
    (hmin : ∀ j, r i ≤ r j) :
    linearSymplecticWidth (stdEllipsoid r) = ENNReal.ofReal (π * r i ^ 2) := by
  refine le_antisymm ((linearSymplecticWidth_mono (stdEllipsoid_subset_stdCylinder (hr i))).trans
    (linearSymplecticWidth_stdCylinder_le i (r i))) ?_
  exact le_linearSymplecticWidth (one_mem _) (hr i).le (by
    rw [AffineEquiv.coe_one, Set.image_id]
    exact closedBall_subset_stdEllipsoid hmin)

/-- The normal form of an ellipsoid with a smallest element `s` of its spectrum: a linear
symplectic map carries it onto `E(r)` with positive radii, `s = rᵢ` and `rᵢ` the smallest
radius. -/
private theorem exists_normalForm_of_mem_symplecticSpectrum {Q : QuadraticForm ℝ (StdSpace ι)}
    (hQ : Q.PosDef) {s : ℝ} (hs : s ∈ symplecticSpectrum Q)
    (hmin : ∀ t ∈ symplecticSpectrum Q, s ≤ t) :
    ∃ (r : ι → ℝ) (e : StdSpace ι ≃ₗ[ℝ] StdSpace ι) (i : ι), (∀ j, 0 < r j) ∧
      IsSymplectomorphism (stdForm ι) (stdForm ι) e ∧ e '' {z | Q z ≤ 1} = stdEllipsoid r ∧
      r i = s ∧ ∀ j, r i ≤ r j := by
  obtain ⟨r, e, hr, he, h⟩ := exists_isSymplectomorphism_image_eq_stdEllipsoid hQ
  have hspec := symplecticSpectrum_eq hQ hr he h
  rw [hspec] at hs hmin
  obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hs
  exact ⟨r, e, i, hr, he, h, rfl,
    fun j ↦ hmin _ (Multiset.mem_map_of_mem _ (Finset.mem_univ j))⟩

/-- The ellipsoid of a positive definite form `Q` has width `π s²`, for `s` the smallest element
of the symplectic spectrum of `Q`. -/
theorem linearSymplecticWidth_setOf_le_one_eq {Q : QuadraticForm ℝ (StdSpace ι)}
    (hQ : Q.PosDef) {s : ℝ} (hs : s ∈ symplecticSpectrum Q)
    (hmin : ∀ t ∈ symplecticSpectrum Q, s ≤ t) :
    linearSymplecticWidth {z | Q z ≤ 1} = ENNReal.ofReal (π * s ^ 2) := by
  obtain ⟨r, e, i, hr, he, h, rfl, hi⟩ := exists_normalForm_of_mem_symplecticSpectrum hQ hs hmin
  rw [← linearSymplecticWidth_stdEllipsoid hr hi, ← h, ← LinearEquiv.coe_toAffineEquiv,
    linearSymplecticWidth_image ((LinearEquiv.toAffineEquiv_mem_affineSymplecticGroup_iff e).2 he)]

/-- **The linear symplectic width of an ellipsoid.** Let `Q` be a positive definite form on
`ℝ²ⁿ` and `s` the smallest element of its symplectic spectrum. The ellipsoid
`E = {z | Q z ≤ 1}` has width `π s²`; this is the supremum of the widths of the affine
symplectic images of balls that lie in `E`, and the infimum of the widths of the affine
symplectic images of cylinders that contain `E`.

Milestone: *Linear symplectic width of an ellipsoid*. -/
theorem linearSymplecticWidth_setOf_le_one {Q : QuadraticForm ℝ (StdSpace ι)}
    (hQ : Q.PosDef) {s : ℝ} (hs : s ∈ symplecticSpectrum Q)
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
  have hE := linearSymplecticWidth_setOf_le_one_eq hQ hs hmin
  have : Nonempty ι := Fintype.card_pos_iff.1
    (card_symplecticSpectrum hQ ▸ Multiset.card_pos_iff_exists_mem.2 ⟨s, hs⟩)
  refine ⟨hE, ?_, ?_⟩
  · refine le_antisymm ?_ (iSup₂_le fun _ _ ↦ iSup₂_le fun r hr ↦
      linearSymplecticWidth_mono hr)
    rw [linearSymplecticWidth_def]
    refine iSup_le fun r ↦ iSup₂_le fun f hf ↦ iSup_le fun hr ↦ ?_
    refine le_iSup₂_of_le f hf (le_iSup₂_of_le r hr ?_)
    rw [linearSymplecticWidth_image_closedBall hf 0 r.coe_nonneg]
  · refine le_antisymm (le_iInf₂ fun _ _ ↦ le_iInf₂ fun i R ↦ le_iInf fun h ↦
      linearSymplecticWidth_mono h) ?_
    obtain ⟨r, e, i, hr, he, h, rfl, -⟩ :=
      exists_normalForm_of_mem_symplecticSpectrum hQ hs hmin
    have hg := (LinearEquiv.toAffineEquiv_mem_affineSymplecticGroup_iff e).2 he
    have hsub : {z | Q z ≤ 1} ⊆
        (e.toAffineEquiv⁻¹ : StdSpace ι ≃ᵃ[ℝ] StdSpace ι) '' stdCylinder i (r i) := by
      intro z hz
      refine ⟨e z, stdEllipsoid_subset_stdCylinder (hr i) (h ▸ ⟨z, hz, rfl⟩), ?_⟩
      simpa [AffineEquiv.inv_def] using e.toAffineEquiv.symm_apply_apply z
    refine (iInf₂_le _ (inv_mem hg)).trans
      ((iInf₂_le i (r i)).trans ((iInf_le _ hsub).trans ?_))
    rw [linearSymplecticWidth_image (inv_mem hg), hE]
    exact linearSymplecticWidth_stdCylinder_le i (r i)

end SymplecticGeometry

end
