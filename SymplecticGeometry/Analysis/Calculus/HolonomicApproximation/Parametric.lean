/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.Thickening
public import TauCeti.Topology.Algebra.Module.Equiv.Fin
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Normed.Group.Bounded
import SymplecticGeometry.Analysis.Normed.Group.Pi
import TauCeti.Analysis.Calculus.ContDiff.ContinuousLinearMap
import TauCeti.Analysis.Calculus.FDeriv.Prod

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
* `SymplecticGeometry.familyRelativeSet`: the relative set on the core of `D'` for
  `B ⊆ Fin m → ℝ` and `P₀ ⊆ L`, the points `Fin.append s u` with `u ∈ B` or `s = R⁻¹ • e l` for
  some `l ∈ P₀`. It is closed when `B` and `P₀` are
  (`SymplecticGeometry.isClosed_familyRelativeSet`), contains the faces of the cube of `D'` in
  the directions `J` when `sphere 0 1 ⊆ B`
  (`SymplecticGeometry.mem_familyRelativeSet_of_abs_eq_one`), and its product with `{0}` lies in
  the image of any `U` that contains `univ ×ˢ (B ×ˢ {0})` and `P₀ ×ˢ univ`
  (`SymplecticGeometry.familyRelativeSet_prod_zero_subset_image`).
* `SymplecticGeometry.familyFDeriv f G`: for a family of data `(f (l, ·), G (l, ·))` on a space
  `E`, the datum on `L × E` that completes `G` by the derivative of `f` in the parameter. It is
  smooth when `f` and `G` are (`ContDiff.familyFDeriv`).
* `SymplecticGeometry.fderiv_eq_familyFDeriv_iff`: where `f` is differentiable, its derivative
  is `familyFDeriv f G` exactly when its derivative in the space variable is `G`, since the
  partial derivatives of `f` are its derivative composed with the inclusions of the two factors
  (Tau Ceti's `TauCeti.fderiv_slice_left` and `TauCeti.fderiv_slice_right`).
  `SymplecticGeometry.fderiv_comp_symm_eq_familyFDeriv_comp_iff` reads this in coordinates
  `Ψ : L × E ≃L[ℝ] E'`, such as `familyCubeEquiv`, in the form of the hypothesis `hUf` of the
  cube theorem.

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

variable (L) in
/-- The relative set, in the core of `(Fin (finrank ℝ L + m) → ℝ) × (Fin k → ℝ)`, for
`B ⊆ Fin m → ℝ` and a set of parameters `P₀ ⊆ L`: the points `Fin.append s u` with `u ∈ B`, or
with `s = R⁻¹ • e l` for some `l ∈ P₀`, where `e = (Module.finBasis ℝ L).equivFun`. It is the
image of `univ ×ˢ B ∪ ((fun l ↦ R⁻¹ • e l) '' P₀) ×ˢ univ` under
`(splitCoords (finrank ℝ L) m).symm` (`familyRelativeSet_eq_image`), written as a preimage
under `splitCoords`. -/
noncomputable def familyRelativeSet (R : ℝ) (B : Set (Fin m → ℝ)) (P₀ : Set L) :
    Set (Fin (finrank ℝ L + m) → ℝ) :=
  splitCoords (𝕜 := ℝ) (finrank ℝ L) m ⁻¹'
    (univ ×ˢ B ∪ ((fun l ↦ R⁻¹ • (finBasis ℝ L).equivFun l) '' P₀) ×ˢ univ)

theorem familyRelativeSet_def (R : ℝ) (B : Set (Fin m → ℝ)) (P₀ : Set L) :
    familyRelativeSet L R B P₀ = splitCoords (𝕜 := ℝ) (finrank ℝ L) m ⁻¹'
      (univ ×ˢ B ∪ ((fun l ↦ R⁻¹ • (finBasis ℝ L).equivFun l) '' P₀) ×ˢ univ) :=
  (rfl)

/-- `familyRelativeSet` is the image of `univ ×ˢ B ∪ ((fun l ↦ R⁻¹ • e l) '' P₀) ×ˢ univ` under
the concatenation `(splitCoords (finrank ℝ L) m).symm`. -/
theorem familyRelativeSet_eq_image (R : ℝ) (B : Set (Fin m → ℝ)) (P₀ : Set L) :
    familyRelativeSet L R B P₀ = (splitCoords (𝕜 := ℝ) (finrank ℝ L) m).symm ''
      (univ ×ˢ B ∪ ((fun l ↦ R⁻¹ • (finBasis ℝ L).equivFun l) '' P₀) ×ˢ univ) := by
  rw [familyRelativeSet_def, ContinuousLinearEquiv.image_symm_eq_preimage]

/-- A point lies in `familyRelativeSet` if and only if its last `m` coordinates lie in `B` or
its first `finrank ℝ L` coordinates are `R⁻¹ • e l` for some `l ∈ P₀`. -/
@[simp]
theorem mem_familyRelativeSet_iff {R : ℝ} {B : Set (Fin m → ℝ)} {P₀ : Set L}
    {z : Fin (finrank ℝ L + m) → ℝ} :
    z ∈ familyRelativeSet L R B P₀ ↔ (fun i ↦ z (Fin.natAdd (finrank ℝ L) i)) ∈ B ∨
      ∃ l ∈ P₀, R⁻¹ • (finBasis ℝ L).equivFun l = fun i ↦ z (Fin.castAdd m i) := by
  simp only [familyRelativeSet_def, mem_preimage, splitCoords_apply, mem_union, mem_prod,
    mem_univ, true_and, and_true, mem_image]

/-- For closed `B` and `P₀`, `familyRelativeSet` is closed. -/
theorem isClosed_familyRelativeSet (R : ℝ) {B : Set (Fin m → ℝ)} {P₀ : Set L} (hB : IsClosed B)
    (hP₀ : IsClosed P₀) : IsClosed (familyRelativeSet L R B P₀) := by
  rw [familyRelativeSet_def]
  refine ((isClosed_univ.prod hB).union (IsClosed.prod ?_ isClosed_univ)).preimage
    (splitCoords (finrank ℝ L) m).continuous
  exact (isClosedMap_smul₀ R⁻¹).comp
    (finBasis ℝ L).equivFun.toContinuousLinearEquiv.toHomeomorph.isClosedMap _ hP₀

/-- When `sphere 0 1 ⊆ B`, `familyRelativeSet` contains the faces of the cube `closedBall 0 1`
in the directions `Finset.univ.map (Fin.natAddEmb (finrank ℝ L))`, that is the points of the
cube with a coordinate of absolute value `1` in one of these directions. -/
theorem mem_familyRelativeSet_of_abs_eq_one (R : ℝ) {B : Set (Fin m → ℝ)} (P₀ : Set L)
    (hB : sphere 0 1 ⊆ B) (u : Fin (finrank ℝ L + m) → ℝ) (hu : u ∈ closedBall 0 1)
    (hi : ∃ i ∈ Finset.univ.map (Fin.natAddEmb (finrank ℝ L)), |u i| = 1) :
    u ∈ familyRelativeSet L R B P₀ := by
  obtain ⟨_, hi, hui⟩ := hi
  obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hi
  refine mem_familyRelativeSet_iff.2 (Or.inl (hB ?_))
  rw [mem_closedBall, dist_zero_right] at hu
  rw [mem_sphere, dist_zero_right]
  refine le_antisymm ((pi_norm_comp_le u (Fin.natAdd _)).trans hu) ?_
  rw [← hui, ← Real.norm_eq_abs]
  exact norm_le_pi_norm (fun i ↦ u (Fin.natAdd (finrank ℝ L) i)) i

/-- If `U ⊆ L × ((Fin m → ℝ) × (Fin k → ℝ))` contains every point `(l, (u, 0))` with `u ∈ B` and
every point over a parameter of `P₀`, then the image of `U` under `familyCubeEquiv` contains
`familyRelativeSet L R B P₀ ×ˢ {0}`. -/
theorem familyRelativeSet_prod_zero_subset_image (hR : R ≠ 0) {B : Set (Fin m → ℝ)}
    {P₀ : Set L} {U : Set (L × (Fin m → ℝ) × (Fin k → ℝ))} (hBU : univ ×ˢ (B ×ˢ {0}) ⊆ U)
    (hP₀U : P₀ ×ˢ univ ⊆ U) :
    familyRelativeSet L R B P₀ ×ˢ {0} ⊆ familyCubeEquiv L m k hR '' U := by
  rintro ⟨z, v⟩ ⟨hz, hv⟩
  rw [mem_singleton_iff] at hv
  subst hv
  rw [ContinuousLinearEquiv.image_eq_preimage_symm, mem_preimage]
  rcases mem_familyRelativeSet_iff.1 hz with hz | ⟨l, hl, hlz⟩
  · exact hBU ⟨mem_univ _, by simpa using hz⟩
  · refine hP₀U ⟨?_, mem_univ _⟩
    rw [familyCubeEquiv_symm_apply, ← hlz, smul_smul, mul_inv_cancel₀ hR, one_smul,
      LinearEquiv.symm_apply_apply]
    exact hl

section Datum

variable {L E E' F : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {f : L × E → F} {G : L × E → E →L[ℝ] F} {q : L × E}

/-- The datum on `L × E` of a family over `L` of data `(f (l, ·), G (l, ·))` on `E`: at `q`, it
is the derivative of `f` in the parameter on the `L` component and `G q` on the `E` component. -/
noncomputable def familyFDeriv (f : L × E → F) (G : L × E → E →L[ℝ] F) (q : L × E) :
    L × E →L[ℝ] F :=
  (fderiv ℝ (fun l ↦ f (l, q.2)) q.1).coprod (G q)

theorem familyFDeriv_def (f : L × E → F) (G : L × E → E →L[ℝ] F) (q : L × E) :
    familyFDeriv f G q = (fderiv ℝ (fun l ↦ f (l, q.2)) q.1).coprod (G q) :=
  (rfl)

@[simp]
theorem familyFDeriv_apply (f : L × E → F) (G : L × E → E →L[ℝ] F) (q w : L × E) :
    familyFDeriv f G q w = fderiv ℝ (fun l ↦ f (l, q.2)) q.1 w.1 + G q w.2 :=
  ContinuousLinearMap.coprod_apply ..

/-- `familyFDeriv f G` is `Cⁿ` when `f` is `Cᵐ` with `n + 1 ≤ m` and `G` is `Cⁿ`. -/
theorem _root_.ContDiff.familyFDeriv {n m : WithTop ℕ∞} (hf : ContDiff ℝ m f)
    (hG : ContDiff ℝ n G) (hnm : n + 1 ≤ m) : ContDiff ℝ n (familyFDeriv f G) := by
  have h : ContDiff ℝ n fun q : L × E ↦ fderiv ℝ (fun l ↦ f (l, q.2)) q.1 :=
    ContDiff.fderiv (f := fun (q : L × E) (l : L) ↦ f (l, q.2))
      (hf.comp (contDiff_snd.prodMk (contDiff_snd.comp contDiff_fst))) contDiff_fst hnm
  rw [show SymplecticGeometry.familyFDeriv f G = fun q ↦ _ from
    funext (familyFDeriv_def f G)]
  exact contDiff_iff_contDiffAt.2 fun q ↦ h.contDiffAt.continuousLinearMapCoprod hG.contDiffAt

/-- At a point `q` where `f` is differentiable, its derivative is `familyFDeriv f G q` exactly
when its derivative in the space variable at `q` is `G q`. -/
theorem fderiv_eq_familyFDeriv_iff (hf : DifferentiableAt ℝ f q) :
    fderiv ℝ f q = familyFDeriv f G q ↔ fderiv ℝ (fun x ↦ f (q.1, x)) q.2 = G q := by
  obtain ⟨l, x⟩ := q
  rw [TauCeti.fderiv_slice_right hf, familyFDeriv_def, TauCeti.fderiv_slice_left hf]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [h, ContinuousLinearMap.coprod_comp_inr]
  · rw [← h, ContinuousLinearMap.coprod_comp_inl_inr]

/-- In coordinates `Ψ : L × E ≃L[ℝ] E'`, such as `familyCubeEquiv`, the datum
`(f ∘ Ψ.symm, q' ↦ familyFDeriv f G (Ψ.symm q') ∘L Ψ.symm)` on `E'` is holonomic at `Ψ q`
exactly when the derivative of `f` in the space variable at `q` is `G q`, provided `f` is
differentiable at `q`. -/
theorem fderiv_comp_symm_eq_familyFDeriv_comp_iff (Ψ : (L × E) ≃L[ℝ] E')
    (hf : DifferentiableAt ℝ f q) :
    fderiv ℝ (f ∘ Ψ.symm) (Ψ q) = familyFDeriv f G q ∘L (Ψ.symm : E' →L[ℝ] L × E) ↔
      fderiv ℝ (fun x ↦ f (q.1, x)) q.2 = G q := by
  rw [Ψ.symm.comp_right_fderiv, Ψ.symm_apply_apply, ← fderiv_eq_familyFDeriv_iff hf]
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ rfl⟩
  refine ContinuousLinearMap.ext fun w ↦ ?_
  simpa using congr($h (Ψ w))

end Datum

end SymplecticGeometry

end
