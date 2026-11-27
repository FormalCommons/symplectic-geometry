/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.Thickening
public import TauCeti.Topology.Algebra.Module.Equiv.Fin
import Mathlib.Analysis.Normed.Group.Bounded
import SymplecticGeometry.Analysis.Normed.Group.Pi

/-!
# Holonomic approximation for families over a finite-dimensional space

A family of data on `D = (Fin m → ℝ) × (Fin k → ℝ)` over a finite-dimensional real normed space
`L` is a datum on `L × D`. This file sets up the coordinates in which such a family becomes a
datum over the cube of
`SymplecticGeometry.Analysis.Calculus.HolonomicApproximation.Cube`, following the parametric
form of the holonomic approximation theorem in [EliashbergMishachev2002], Theorem 4.7.4, where
the parameters are treated as extra core coordinates that are not approximated.

With `p = Module.finrank ℝ L` and the coordinates `e = (Module.finBasis ℝ L).equivFun`, the
continuous linear equivalence `SymplecticGeometry.familyCubeEquiv L m k hR`, for `R ≠ 0`, sends
`(l, (u, v))` to `(Fin.append (R⁻¹ • e l) u, v)` in
`D' = (Fin (p + m) → ℝ) × (Fin k → ℝ)`; the concatenation is Tau Ceti's
`(TauCeti.splitCoords p m).symm`, an isometry for the sup norms by Mathlib's
`Fin.appendIsometry`. The core coordinates of `D'` in `J = Finset.univ.map (Fin.natAddEmb p)` are
those of `D`; those outside `J` record the parameter.

## Main results

* `SymplecticGeometry.familyCubeEquiv_apply`, `SymplecticGeometry.familyCubeEquiv_symm_apply`:
  the values of the equivalence and of its inverse.
* `SymplecticGeometry.mapsTo_familyCubeEquiv`: for `R > 0` bounding `‖e l‖` on `K`, the
  equivalence maps `K ×ˢ Q` into the cube `Q'` of `D'`;
  `SymplecticGeometry.exists_pos_norm_finBasis_equivFun_lt` gives such an `R` for a compact `K`.
* `SymplecticGeometry.familyCubeEquiv_symm_fst_eq_iff`: two points of `D'` have the same
  parameter exactly when their core coordinates outside `J` agree.
* `SymplecticGeometry.range_familyCubeEquiv_zero_fst`,
  `SymplecticGeometry.norm_familyCubeEquiv_zero_fst`: on the vectors `(0, w)` the equivalence is
  an isometry onto the vectors of `D'` in the directions `J`.
* `SymplecticGeometry.dist_familyCubeEquiv_of_fst_eq`: it preserves the distance of two points
  with the same parameter, and `SymplecticGeometry.infDist_le_infDist_familyCubeEquiv` bounds the
  distance to `Q` by the distance of the image to `Q'`.

## References

* [Y. Eliashberg and N. Mishachev, *Introduction to the h-Principle*][EliashbergMishachev2002]
-/

public section

namespace SymplecticGeometry

open Metric Module Set TauCeti

variable (L : Type*) [NormedAddCommGroup L] [NormedSpace ℝ L] [FiniteDimensional ℝ L]
  (m k : ℕ) {R : ℝ}

/-- The coordinates of a family over `L`: the continuous linear equivalence of
`L × ((Fin m → ℝ) × (Fin k → ℝ))` with `(Fin (finrank ℝ L + m) → ℝ) × (Fin k → ℝ)` sending
`(l, (u, v))` to `(Fin.append (R⁻¹ • e l) u, v)`, where `e = (Module.finBasis ℝ L).equivFun`. -/
noncomputable def familyCubeEquiv (hR : R ≠ 0) :
    (L × (Fin m → ℝ) × (Fin k → ℝ)) ≃L[ℝ] (Fin (finrank ℝ L + m) → ℝ) × (Fin k → ℝ) :=
  (ContinuousLinearEquiv.prodAssoc ℝ L (Fin m → ℝ) (Fin k → ℝ)).symm.trans
    (((((finBasis ℝ L).equivFun.toContinuousLinearEquiv.trans
        (ContinuousLinearEquiv.smulLeft (Units.mk0 R⁻¹ (inv_ne_zero hR)))).prodCongr
          (ContinuousLinearEquiv.refl ℝ (Fin m → ℝ))).trans
        (splitCoords (finrank ℝ L) m).symm).prodCongr
      (ContinuousLinearEquiv.refl ℝ (Fin k → ℝ)))

variable {L m k}

/-- The value of `familyCubeEquiv`: the scaled coordinates of the parameter are put before the
core coordinates. -/
@[simp]
theorem familyCubeEquiv_apply (hR : R ≠ 0) (p : L × (Fin m → ℝ) × (Fin k → ℝ)) :
    familyCubeEquiv L m k hR p =
      (Fin.append (R⁻¹ • (finBasis ℝ L).equivFun p.1) p.2.1, p.2.2) := by
  obtain ⟨l, u, v⟩ := p
  simp [familyCubeEquiv, Units.smul_def]

/-- The value of the inverse of `familyCubeEquiv`: the first `finrank ℝ L` core coordinates,
scaled by `R`, are the coordinates of the parameter, and the others are the core coordinates of
the space part. -/
@[simp]
theorem familyCubeEquiv_symm_apply (hR : R ≠ 0)
    (z : (Fin (finrank ℝ L + m) → ℝ) × (Fin k → ℝ)) :
    (familyCubeEquiv L m k hR).symm z =
      ((finBasis ℝ L).equivFun.symm (R • fun i ↦ z.1 (Fin.castAdd m i)),
        (fun i ↦ z.1 (Fin.natAdd (finrank ℝ L) i), z.2)) := by
  rw [ContinuousLinearEquiv.symm_apply_eq, familyCubeEquiv_apply]
  ext i
  · induction i using Fin.addCases with
    | left i =>
      simp only [Fin.append_left, LinearEquiv.apply_symm_apply, smul_smul, inv_mul_cancel₀ hR,
        one_smul]
    | right i => simp
  · rfl

/-- The parameter of a point of `(Fin (finrank ℝ L + m) → ℝ) × (Fin k → ℝ)` depends only on its
core coordinates outside `Finset.univ.map (Fin.natAddEmb (finrank ℝ L))`: two points have the
same parameter if and only if these coordinates agree. -/
theorem familyCubeEquiv_symm_fst_eq_iff (hR : R ≠ 0)
    (z z' : (Fin (finrank ℝ L + m) → ℝ) × (Fin k → ℝ)) :
    ((familyCubeEquiv L m k hR).symm z).1 = ((familyCubeEquiv L m k hR).symm z').1 ↔
      ∀ i ∉ Finset.univ.map (Fin.natAddEmb (finrank ℝ L)), z.1 i = z'.1 i := by
  simp only [familyCubeEquiv_symm_apply, (finBasis ℝ L).equivFun.symm.injective.eq_iff,
    smul_right_injective _ hR |>.eq_iff, funext_iff]
  refine ⟨fun h i hi ↦ ?_, fun h i ↦ h _ ?_⟩
  · induction i using Fin.addCases with
    | left i => exact h i
    | right i => exact absurd (Finset.mem_map_of_mem _ (Finset.mem_univ i)) hi
  · simp only [Finset.mem_map, Finset.mem_univ, true_and, not_exists]
    intro j hj
    have := congrArg Fin.val hj
    simp at this
    omega

/-- A point of `(Fin (finrank ℝ L + m) → ℝ) × (Fin k → ℝ)` comes from a point of parameter `0`
if and only if it lies in the directions `Finset.univ.map (Fin.natAddEmb (finrank ℝ L))`. -/
theorem familyCubeEquiv_symm_fst_eq_zero_iff (hR : R ≠ 0)
    (z : (Fin (finrank ℝ L + m) → ℝ) × (Fin k → ℝ)) :
    ((familyCubeEquiv L m k hR).symm z).1 = 0 ↔
      ∀ i ∉ Finset.univ.map (Fin.natAddEmb (finrank ℝ L)), z.1 i = 0 := by
  simpa using familyCubeEquiv_symm_fst_eq_iff hR z 0

/-- On the vectors `(0, w)`, `familyCubeEquiv` is onto the vectors in the directions
`Finset.univ.map (Fin.natAddEmb (finrank ℝ L))`. -/
theorem range_familyCubeEquiv_zero_fst (hR : R ≠ 0) :
    range (fun w ↦ familyCubeEquiv L m k hR (0, w)) =
      {z | ∀ i ∉ Finset.univ.map (Fin.natAddEmb (finrank ℝ L)), z.1 i = 0} := by
  ext z
  simp only [mem_range, mem_ofPred_eq, ← familyCubeEquiv_symm_fst_eq_zero_iff hR]
  constructor
  · rintro ⟨w, rfl⟩
    simp
  · intro h
    exact ⟨((familyCubeEquiv L m k hR).symm z).2, by
      rw [← h, Prod.mk.eta, ContinuousLinearEquiv.apply_symm_apply]⟩

/-- `familyCubeEquiv` preserves the distance of two points with the same parameter. -/
theorem dist_familyCubeEquiv_of_fst_eq (hR : R ≠ 0) {p p' : L × (Fin m → ℝ) × (Fin k → ℝ)}
    (h : p.1 = p'.1) :
    dist (familyCubeEquiv L m k hR p) (familyCubeEquiv L m k hR p') = dist p p' := by
  obtain ⟨l, x⟩ := p
  obtain ⟨l', x'⟩ := p'
  obtain rfl : l = l' := h
  simp [Prod.dist_eq, Fin.dist_append]

/-- On the vectors `(0, w)`, `familyCubeEquiv` preserves the norm. -/
theorem norm_familyCubeEquiv_zero_fst (hR : R ≠ 0) (w : (Fin m → ℝ) × (Fin k → ℝ)) :
    ‖familyCubeEquiv L m k hR (0, w)‖ = ‖w‖ := by
  simp [Fin.norm_append, Prod.norm_def]

/-- For `R > 0` with `‖e l‖ ≤ R` on `K`, `familyCubeEquiv` maps `K ×ˢ Q` into the cube of
`(Fin (finrank ℝ L + m) → ℝ) × (Fin k → ℝ)`, where `Q = closedBall 0 1 ×ˢ {0}` is the cube of
`(Fin m → ℝ) × (Fin k → ℝ)`. -/
theorem mapsTo_familyCubeEquiv (hR : 0 < R) {K : Set L}
    (hK : ∀ l ∈ K, ‖(finBasis ℝ L).equivFun l‖ ≤ R) :
    MapsTo (familyCubeEquiv L m k hR.ne')
      (K ×ˢ (closedBall (0 : Fin m → ℝ) 1 ×ˢ {(0 : Fin k → ℝ)}))
      (closedBall 0 1 ×ˢ {0}) := by
  rintro ⟨l, u, v⟩ ⟨hl, hu, hv⟩
  simp only [mem_singleton_iff, mem_closedBall, dist_zero_right] at hu hv
  subst hv
  refine ⟨?_, by simp⟩
  rw [familyCubeEquiv_apply, mem_closedBall, dist_zero_right, Fin.norm_append, norm_smul,
    norm_inv, Real.norm_of_nonneg hR.le]
  exact max_le ((inv_mul_le_one₀ hR).2 (hK l hl)) hu

/-- A compact set of parameters has a positive strict bound `R` for the norms of its
coordinates `e l`, as `mapsTo_familyCubeEquiv` needs. -/
theorem exists_pos_norm_finBasis_equivFun_lt {K : Set L} (hK : IsCompact K) :
    ∃ R > 0, ∀ l ∈ K, ‖(finBasis ℝ L).equivFun l‖ < R := by
  obtain ⟨R, hR, h⟩ := (hK.image (finBasis ℝ L).equivFun.toContinuousLinearEquiv.continuous
    ).isBounded.exists_pos_norm_lt
  exact ⟨R, hR, fun l hl ↦ h _ (mem_image_of_mem _ hl)⟩

/-- The distance of a point to the cube `Q = closedBall 0 1 ×ˢ {0}` of
`(Fin m → ℝ) × (Fin k → ℝ)` is at most the distance of its image under `familyCubeEquiv` to the
cube of `(Fin (finrank ℝ L + m) → ℝ) × (Fin k → ℝ)`. -/
theorem infDist_le_infDist_familyCubeEquiv (hR : R ≠ 0) (p : L × (Fin m → ℝ) × (Fin k → ℝ)) :
    infDist p.2 (closedBall (0 : Fin m → ℝ) 1 ×ˢ {(0 : Fin k → ℝ)}) ≤
      infDist (familyCubeEquiv L m k hR p) (closedBall 0 1 ×ˢ {0}) := by
  refine (le_infDist ⟨0, by simp⟩).2 ?_
  rintro ⟨y, v⟩ ⟨hy, hv⟩
  simp only [mem_singleton_iff, mem_closedBall, dist_zero_right] at hy hv
  subst hv
  set u : Fin m → ℝ := fun i ↦ y (Fin.natAdd (finrank ℝ L) i)
  have hyu : y = Fin.append (fun i ↦ y (Fin.castAdd m i)) u :=
    Fin.append_castAdd_natAdd.symm
  have hu : (u, (0 : Fin k → ℝ)) ∈ closedBall (0 : Fin m → ℝ) 1 ×ˢ {(0 : Fin k → ℝ)} := by
    refine ⟨?_, rfl⟩
    rw [mem_closedBall, dist_zero_right]
    exact (le_max_right _ _).trans ((Fin.norm_append _ _).symm.le.trans (hyu ▸ hy))
  refine (infDist_le_dist_of_mem hu).trans ?_
  rw [familyCubeEquiv_apply, hyu, Prod.dist_eq, Prod.dist_eq, Fin.dist_append]
  exact max_le_max (le_max_right _ _) le_rfl

/-- A point whose image under `familyCubeEquiv` lies within `δ` of the cube of
`(Fin (finrank ℝ L + m) → ℝ) × (Fin k → ℝ)` has its space part within `δ` of the cube
`Q = closedBall 0 1 ×ˢ {0}` of `(Fin m → ℝ) × (Fin k → ℝ)`. -/
theorem mem_thickening_of_familyCubeEquiv_mem_thickening (hR : R ≠ 0) {δ : ℝ}
    {p : L × (Fin m → ℝ) × (Fin k → ℝ)}
    (hp : familyCubeEquiv L m k hR p ∈ thickening δ (closedBall 0 1 ×ˢ {0})) :
    p.2 ∈ thickening δ (closedBall (0 : Fin m → ℝ) 1 ×ˢ {(0 : Fin k → ℝ)}) := by
  rw [mem_thickening_iff_infDist_lt ⟨0, by simp⟩] at hp ⊢
  exact (infDist_le_infDist_familyCubeEquiv hR p).trans_lt hp

end SymplecticGeometry

end
