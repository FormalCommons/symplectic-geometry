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
public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Basic
public import TauCeti.Topology.Algebra.Module.Equiv.Fin
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import SymplecticGeometry.Analysis.Calculus.HolonomicApproximation.Cube
import SymplecticGeometry.Analysis.Normed.Group.Pi
import SymplecticGeometry.Geometry.Diffeomorphism.Diffeotopy.OfContMDiff
import SymplecticGeometry.Topology.MetricSpace.Thickening
import TauCeti.Analysis.Calculus.ContDiff.ContinuousLinearMap
import TauCeti.Analysis.Calculus.FDeriv.Prod

/-!
# Holonomic approximation for families over a finite-dimensional space

A family of data on `D = (Fin m → ℝ) × (Fin k → ℝ)` over a finite-dimensional real normed space
`L` is a datum on `L × D`. This file proves the holonomic approximation theorem for such
families, `SymplecticGeometry.exists_holonomic_approximation_family`, the parametric form of
[EliashbergMishachev2002], Theorem 4.7.4, in coordinates. It sets up the coordinates in which
such a family becomes a datum over the cube of
`SymplecticGeometry.Analysis.Calculus.HolonomicApproximation.Cube`, where the parameters are
treated as extra core coordinates that are not approximated, applies the cube theorem
`SymplecticGeometry.exists_holonomic_approximation_cube_directions` there, and carries the
result back.

With `p = Module.finrank ℝ L` and the coordinates `e = (Module.finBasis ℝ L).equivFun`, the
continuous linear equivalence `SymplecticGeometry.familyCubeEquiv L m k hR`, for `R ≠ 0`, sends
`(l, (u, v))` to `(Fin.append (R⁻¹ • e l) u, v)` in
`D' = (Fin (p + m) → ℝ) × (Fin k → ℝ)`; the concatenation is Tau Ceti's
`(TauCeti.splitCoords p m).symm`, an isometry for the sup norms by Mathlib's
`Fin.appendIsometry`. The core coordinates of `D'` in `J = Finset.univ.map (Fin.natAddEmb p)` are
those of `D`; those outside `J` record the parameter.

## Main results

* `SymplecticGeometry.exists_holonomic_approximation_family`: for a smooth family over `L` of
  formal sections on `D`, holonomic near `B ×ˢ {0}` for a closed `B ⊇ sphere 0 1` and everywhere
  over a closed set `P₀` of parameters, a family of diffeotopies of `D` and a smooth `f'`,
  unchanged over a neighbourhood of `B` in the core, over `P₀` and off a compact set near the
  cube, with `f'` holonomically `ε`-close to the datum near the moved cube for the parameters in
  a compact `K`. The neighbourhood of `B` comes from the one of the cube theorem by
  `SymplecticGeometry.exists_mem_nhdsSet_familyCubeEquiv_fst_mem`.
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
* `SymplecticGeometry.exists_mem_nhdsSet_familyCubeEquiv_fst_mem`: a neighbourhood of
  `familyRelativeSet L R B P₀` gives, by `generalized_tube_lemma`, a neighbourhood `N` of `B`
  such that each point over `N` whose image under `familyCubeEquiv` lies within `r` of the cube
  has the core part of that image in the given neighbourhood. Near the cube, the scaled
  parameter coordinates and the core part have norm less than `1 + r`
  (`SymplecticGeometry.norm_lt_of_familyCubeEquiv_mem_thickening`).
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
* `SymplecticGeometry.exists_holonomic_approximation_family_of_cube`: the conclusion of the cube
  theorem on `D'`, in the directions `J` and for the datum transported by `familyCubeEquiv`, read
  back on `L × D`. The diffeotopy is the conjugate of the one on `D'`, built from its slices by
  `TauCeti.Diffeotopy.ofContMDiff`, since Tau Ceti's `TauCeti.Diffeotopy.transDiffeomorph` keeps
  the model and `familyCubeEquiv` changes it. It keeps the parameter, and the bound on the space
  derivative is `SymplecticGeometry.norm_fderiv_comp_familyCubeEquiv_sub_le`.

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
    exact (pi_norm_comp_le y (Fin.natAdd _)).trans hy
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

/-- A point whose image under `familyCubeEquiv` lies within `r > 0` of the cube of
`(Fin (finrank ℝ L + m) → ℝ) × (Fin k → ℝ)` has scaled parameter coordinates
`R⁻¹ • e p.1` and core part `p.2.1` of norm less than `1 + r`, where
`e = (Module.finBasis ℝ L).equivFun`. -/
theorem norm_lt_of_familyCubeEquiv_mem_thickening (hR : R ≠ 0) {r : ℝ} (hr : 0 < r)
    {p : L × (Fin m → ℝ) × (Fin k → ℝ)}
    (hp : familyCubeEquiv L m k hR p ∈ thickening r (closedBall 0 1 ×ˢ {0})) :
    ‖R⁻¹ • (finBasis ℝ L).equivFun p.1‖ < 1 + r ∧ ‖p.2.1‖ < 1 + r := by
  rw [thickening_prod, thickening_closedBall hr zero_le_one] at hp
  have hn := hp.1
  rw [mem_ball, dist_zero_right, familyCubeEquiv_apply, Fin.norm_append, add_comm] at hn
  exact ⟨(le_max_left _ _).trans_lt hn, (le_max_right _ _).trans_lt hn⟩

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

open scoped Topology in
/-- For a neighbourhood `N''` of `familyRelativeSet L R B P₀` with `B` closed and `0 < r`,
there is a neighbourhood `N` of `B` such that every point `p` with core part in `N` either has
the core part of its image under `familyCubeEquiv` in `N''`, or has its image at distance at
least `r` from the cube `closedBall 0 1 ×ˢ {0}` of `(Fin (finrank ℝ L + m) → ℝ) × (Fin k → ℝ)`. -/
theorem exists_mem_nhdsSet_familyCubeEquiv_fst_mem (hR : R ≠ 0) {B : Set (Fin m → ℝ)}
    (hB : IsClosed B) {P₀ : Set L} {N'' : Set (Fin (finrank ℝ L + m) → ℝ)}
    (hN'' : N'' ∈ 𝓝ˢ (familyRelativeSet L R B P₀)) {r : ℝ} (hr : 0 < r) :
    ∃ N ∈ 𝓝ˢ B, ∀ p : L × (Fin m → ℝ) × (Fin k → ℝ), p.2.1 ∈ N →
      (familyCubeEquiv L m k hR p).1 ∈ N'' ∨
        familyCubeEquiv L m k hR p ∉ thickening r (closedBall 0 1 ×ˢ {0}) := by
  have hB'N'' : familyRelativeSet L R B P₀ ⊆ interior N'' :=
    subset_interior_iff_mem_nhdsSet.2 hN''
  obtain ⟨U₁, N₁, -, hN₁, hU₁, hBN₁, hUN₁⟩ := generalized_tube_lemma
    (isCompact_closedBall (0 : Fin (finrank ℝ L) → ℝ) (1 + r))
    ((isCompact_closedBall (0 : Fin m → ℝ) (1 + r)).inter_left hB)
    (isOpen_interior.preimage (splitCoords (𝕜 := ℝ) (finrank ℝ L) m).symm.continuous)
    (fun su hsu ↦ hB'N'' (mem_familyRelativeSet_iff.2 (Or.inl (by simpa using hsu.2.1))))
  refine ⟨N₁ ∪ (closedBall 0 (1 + r))ᶜ,
    (hN₁.union isClosed_closedBall.isOpen_compl).mem_nhdsSet.2 fun u hu ↦ ?_, fun p hp ↦ ?_⟩
  · by_cases hu2 : u ∈ closedBall 0 (1 + r)
    · exact Or.inl (hBN₁ ⟨hu, hu2⟩)
    · exact Or.inr hu2
  · by_cases hpC : familyCubeEquiv L m k hR p ∈ thickening r (closedBall 0 1 ×ˢ {0})
    · obtain ⟨hs, hu⟩ := norm_lt_of_familyCubeEquiv_mem_thickening hR hr hpC
      rcases hp with hp | hp
      · have hmem := hUN₁ (show (_, p.2.1) ∈ U₁ ×ˢ N₁ from
          ⟨hU₁ (mem_closedBall_zero_iff.2 hs.le), hp⟩)
        rw [mem_preimage, splitCoords_symm_apply] at hmem
        exact Or.inl (interior_subset (by simpa using hmem))
      · exact absurd (mem_closedBall_zero_iff.2 hu.le) hp
    · exact Or.inr hpC

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

section Conjugation

open scoped Manifold ContDiff Topology

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The derivative in the space variable of `f'' ∘ familyCubeEquiv` differs from `G p` at `p` by
at most `ε` in operator norm, when `f''` is differentiable at `q = familyCubeEquiv p` and its
derivative there differs from the transported datum `familyFDeriv f G p ∘L Ψ.symm` by at most
`ε * ‖w‖` on each vector `w` in the directions `Finset.univ.map (Fin.natAddEmb (finrank ℝ L))`.
On a space vector `w`, the first difference is the second evaluated at `Ψ (0, w)`. -/
theorem norm_fderiv_comp_familyCubeEquiv_sub_le (hR : R ≠ 0)
    {f'' : (Fin (finrank ℝ L + m) → ℝ) × (Fin k → ℝ) → F}
    {f : L × (Fin m → ℝ) × (Fin k → ℝ) → F}
    {G : L × (Fin m → ℝ) × (Fin k → ℝ) → (Fin m → ℝ) × (Fin k → ℝ) →L[ℝ] F}
    {p : L × (Fin m → ℝ) × (Fin k → ℝ)} {ε : ℝ} (hε : 0 ≤ ε)
    (hf'' : DifferentiableAt ℝ f'' (familyCubeEquiv L m k hR p))
    (h : ∀ w : (Fin (finrank ℝ L + m) → ℝ) × (Fin k → ℝ),
      (∀ i ∉ Finset.univ.map (Fin.natAddEmb (finrank ℝ L)), w.1 i = 0) →
        ‖((fderiv ℝ f'' (familyCubeEquiv L m k hR p) -
          familyFDeriv f G p ∘L ((familyCubeEquiv L m k hR).symm :
            _ →L[ℝ] L × (Fin m → ℝ) × (Fin k → ℝ)) :
          (Fin (finrank ℝ L + m) → ℝ) × (Fin k → ℝ) →L[ℝ] F)) w‖ ≤ ε * ‖w‖) :
    ‖fderiv ℝ (fun x ↦ f'' (familyCubeEquiv L m k hR (p.1, x))) p.2 - G p‖ ≤ ε := by
  set Ψ := familyCubeEquiv L m k hR
  have hd : fderiv ℝ (fun x ↦ f'' (Ψ (p.1, x))) p.2 =
      fderiv ℝ f'' (Ψ p) ∘L (Ψ : _ →L[ℝ] _) ∘L ContinuousLinearMap.inr ℝ L _ :=
    (hf''.hasFDerivAt.comp p.2 (Ψ.hasFDerivAt.comp p.2 (hasFDerivAt_prodMk_right p.1 p.2))).fderiv
  rw [hd]
  refine ContinuousLinearMap.opNorm_le_bound _ hε fun w ↦ ?_
  have hw := h (Ψ (0, w)) fun i hi ↦ by
    have hmem : Ψ (0, w) ∈ range (fun w ↦ Ψ (0, w)) := mem_range_self w
    rw [range_familyCubeEquiv_zero_fst] at hmem
    exact hmem i hi
  rw [norm_familyCubeEquiv_zero_fst] at hw
  simpa using hw

/-- The output of holonomic approximation on `D' = (Fin (finrank ℝ L + m) → ℝ) × (Fin k → ℝ)`, in
the directions `J = Finset.univ.map (Fin.natAddEmb (finrank ℝ L))`, for the datum
`(f ∘ Ψ.symm, q ↦ familyFDeriv f G (Ψ.symm q) ∘L Ψ.symm)` transported by
`Ψ = familyCubeEquiv L m k hR`, carried back to a family over `L`.

Let `R > 0` bound `‖e l‖` on `K ⊆ L`, where `e = (Module.finBasis ℝ L).equivFun`. Let `h''` be a
diffeotopy of `D'` that keeps the coordinates outside `J` and moves points by less than `δ`, let
`f''` be smooth, let `C''` be a compact subset of the `δ`-thickening of the cube of `D'` off which
`h''` is the identity and `f''` is the transported `f`, and let `V''` be open, contain the image
of the cube under `h'' 1`, and be a set on which `f''` is `ε`-close to the transported `f` and its
derivative is `ε`-close to the transported datum on the vectors in the directions `J`. Then the
conjugate `h` of `h''` by `Ψ`, with `f' = f'' ∘ Ψ`, keeps the parameter, moves points by less
than `δ`, is the identity and has `f' = f` off a compact set whose points have space part within
`δ` of `Q = closedBall 0 1 ×ˢ {0}`, and on an open set `V` containing `h (1, (l, y))` for `l ∈ K`
and `y ∈ Q`, `f'` is `ε`-close to `f` and its space derivative is at most `ε` from `G`. -/
theorem exists_holonomic_approximation_family_of_cube (hR : 0 < R) {K : Set L}
    (hK : ∀ l ∈ K, ‖(finBasis ℝ L).equivFun l‖ ≤ R)
    {f : L × (Fin m → ℝ) × (Fin k → ℝ) → F}
    {G : L × (Fin m → ℝ) × (Fin k → ℝ) → (Fin m → ℝ) × (Fin k → ℝ) →L[ℝ] F}
    (h'' : Diffeotopy 𝓘(ℝ, (Fin (finrank ℝ L + m) → ℝ) × (Fin k → ℝ)) ∞
      ((Fin (finrank ℝ L + m) → ℝ) × (Fin k → ℝ)))
    {f'' : (Fin (finrank ℝ L + m) → ℝ) × (Fin k → ℝ) → F}
    {V'' C'' : Set ((Fin (finrank ℝ L + m) → ℝ) × (Fin k → ℝ))} {ε δ : ℝ}
    (hC'' : IsCompact C'') (hC''Q : C'' ⊆ thickening δ (closedBall 0 1 ×ˢ {0}))
    (hhC'' : ∀ t, ∀ x ∉ C'', h'' (t, x) = x)
    (hfC'' : ∀ x ∉ C'', f'' x = f ((familyCubeEquiv L m k hR.ne').symm x))
    (hdist : ∀ t x, dist (h'' (t, x)) x < δ)
    (hJ : ∀ t x, ∀ i ∉ Finset.univ.map (Fin.natAddEmb (finrank ℝ L)), (h'' (t, x)).1 i = x.1 i)
    (hV'' : IsOpen V'') (hQV'' : (fun x ↦ h'' (1, x)) '' (closedBall 0 1 ×ˢ {0}) ⊆ V'')
    (hf'' : ContDiff ℝ ∞ f'')
    (happrox : ∀ x ∈ V'', ‖f'' x - f ((familyCubeEquiv L m k hR.ne').symm x)‖ < ε ∧
      ∀ w : (Fin (finrank ℝ L + m) → ℝ) × (Fin k → ℝ),
        (∀ i ∉ Finset.univ.map (Fin.natAddEmb (finrank ℝ L)), w.1 i = 0) →
          ‖((fderiv ℝ f'' x - familyFDeriv f G ((familyCubeEquiv L m k hR.ne').symm x) ∘L
            ((familyCubeEquiv L m k hR.ne').symm : _ →L[ℝ] L × (Fin m → ℝ) × (Fin k → ℝ)) :
              (Fin (finrank ℝ L + m) → ℝ) × (Fin k → ℝ) →L[ℝ] F)) w‖ ≤ ε * ‖w‖) :
    ∃ (h : Diffeotopy 𝓘(ℝ, L × (Fin m → ℝ) × (Fin k → ℝ)) ∞ (L × (Fin m → ℝ) × (Fin k → ℝ)))
      (f' : L × (Fin m → ℝ) × (Fin k → ℝ) → F) (V : Set (L × (Fin m → ℝ) × (Fin k → ℝ))),
      (∀ t p, h (t, p) =
        (familyCubeEquiv L m k hR.ne').symm (h'' (t, familyCubeEquiv L m k hR.ne' p))) ∧
      (∀ p, f' p = f'' (familyCubeEquiv L m k hR.ne' p)) ∧
      (∀ t p, (h (t, p)).1 = p.1) ∧ ContDiff ℝ ∞ f' ∧
      (∃ C, IsCompact C ∧
        (∀ p ∈ C, p.2 ∈ thickening δ (closedBall (0 : Fin m → ℝ) 1 ×ˢ {(0 : Fin k → ℝ)})) ∧
        ∀ p ∉ C, (∀ t, h (t, p) = p) ∧ f' p = f p) ∧
      (∀ t p, dist (h (t, p)) p < δ) ∧
      IsOpen V ∧ (∀ l ∈ K, ∀ y ∈ closedBall (0 : Fin m → ℝ) 1 ×ˢ {(0 : Fin k → ℝ)},
        h (1, (l, y)) ∈ V) ∧
      ∀ p ∈ V, ‖f' p - f p‖ < ε ∧ ‖fderiv ℝ (fun x ↦ f' (p.1, x)) p.2 - G p‖ ≤ ε := by
  set Ψ := familyCubeEquiv L m k hR.ne'
  -- the conjugate of `h''` by `Ψ`, built slice by slice since `Ψ` changes the model
  let ψ (t : unitInterval) :
      (L × (Fin m → ℝ) × (Fin k → ℝ)) ≃ₘ[ℝ] (L × (Fin m → ℝ) × (Fin k → ℝ)) :=
    Ψ.toDiffeomorph.trans ((h''.timeSlice t).trans Ψ.symm.toDiffeomorph)
  have hψ (p : unitInterval × (L × (Fin m → ℝ) × (Fin k → ℝ))) :
      ψ p.1 p.2 = Ψ.symm (h'' (p.1, Ψ p.2)) := by
    simp [ψ, Diffeotopy.timeSlice_apply]
  have hc : ContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, L × (Fin m → ℝ) × (Fin k → ℝ)))
      𝓘(ℝ, L × (Fin m → ℝ) × (Fin k → ℝ)) ∞ (fun p : unitInterval × _ ↦ ψ p.1 p.2) := by
    simp_rw [hψ]
    exact Ψ.symm.contDiff.contMDiff.comp
      (h''.contMDiff.comp (contMDiff_fst.prodMk (Ψ.contDiff.contMDiff.comp contMDiff_snd)))
  set h := Diffeotopy.ofContMDiff ψ hc fun x ↦ by simpa using hψ (0, x)
  have hh (t p) : h (t, p) = Ψ.symm (h'' (t, Ψ p)) := by
    rw [Diffeotopy.ofContMDiff_apply]
    exact hψ (t, p)
  have hfst (t p) : (h (t, p)).1 = p.1 := by
    rw [hh]
    conv_rhs => rw [← Ψ.symm_apply_apply p]
    exact (familyCubeEquiv_symm_fst_eq_iff hR.ne' _ _).2 (hJ t (Ψ p))
  have hΨh (t p) : Ψ (h (t, p)) = h'' (t, Ψ p) := by
    rw [hh, ContinuousLinearEquiv.apply_symm_apply]
  refine ⟨h, f'' ∘ Ψ, Ψ ⁻¹' V'', hh, fun _ ↦ rfl, hfst, hf''.comp Ψ.contDiff,
    ⟨Ψ.symm '' C'', hC''.image Ψ.symm.continuous, ?_, fun p hp ↦ ?_⟩, fun t p ↦ ?_,
    hV''.preimage Ψ.continuous, fun l hl y hy ↦ ?_, fun p hp ↦ ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    refine mem_thickening_of_familyCubeEquiv_mem_thickening hR.ne' ?_
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact hC''Q hx
  · have hp' : Ψ p ∉ C'' := fun h' ↦ hp ⟨Ψ p, h', Ψ.symm_apply_apply p⟩
    refine ⟨fun t ↦ ?_, ?_⟩
    · rw [hh, hhC'' t _ hp', ContinuousLinearEquiv.symm_apply_apply]
    · rw [Function.comp_apply, hfC'' _ hp', ContinuousLinearEquiv.symm_apply_apply]
  · rw [← dist_familyCubeEquiv_of_fst_eq hR.ne' (hfst t p), hΨh]
    exact hdist t (Ψ p)
  · rw [mem_preimage, hΨh]
    exact hQV'' ⟨Ψ (l, y), mapsTo_familyCubeEquiv hR hK ⟨hl, hy⟩, rfl⟩
  · obtain ⟨h₁, h₂⟩ := happrox (Ψ p) hp
    rw [ContinuousLinearEquiv.symm_apply_apply] at h₁ h₂
    exact ⟨h₁, norm_fderiv_comp_familyCubeEquiv_sub_le hR.ne'
      ((norm_nonneg _).trans_lt h₁).le (hf''.differentiable (by simp) _) h₂⟩

/-- Holonomic approximation for a smooth family over a finite-dimensional real normed space `L`,
in coordinates ([EliashbergMishachev2002], Theorem 4.7.4). Let `(f (l, ·), G (l, ·))` be a
smooth family of formal sections on `D = (Fin m → ℝ) × (Fin k → ℝ)`, `0 < k`, holonomic on an
open `U ⊆ L × D` that contains every point `(l, (u, 0))` with `u` in a closed `B ⊇ sphere 0 1`
and every point over a closed set `P₀` of parameters. Then for `ε, δ > 0` and a compact `K ⊆ L`
there are a diffeotopy `h` of `L × D` keeping the parameter and moving points by less than `δ`,
a smooth `f'` and an open `V` such that `h` is the identity and `f' = f` off a compact set whose
points have space part within `δ` of the cube `Q = closedBall 0 1 ×ˢ {0}`, over a neighbourhood
of `B` in the core and over `P₀`; `V` contains `h (1, (l, y))` for `l ∈ K` and `y ∈ Q`; and on
`V`, `f'` is `ε`-close to `f` and its derivative in the space variable is `ε`-close to `G`. -/
theorem exists_holonomic_approximation_family (hk : 0 < k)
    {f : L × (Fin m → ℝ) × (Fin k → ℝ) → F}
    {G : L × (Fin m → ℝ) × (Fin k → ℝ) → (Fin m → ℝ) × (Fin k → ℝ) →L[ℝ] F}
    (hf : ContDiff ℝ ∞ f) (hG : ContDiff ℝ ∞ G) {K P₀ : Set L} (hK : IsCompact K)
    (hP₀ : IsClosed P₀) {B : Set (Fin m → ℝ)} (hB : IsClosed B) (hSB : sphere 0 1 ⊆ B)
    {U : Set (L × (Fin m → ℝ) × (Fin k → ℝ))} (hU : IsOpen U) (hBU : univ ×ˢ (B ×ˢ {0}) ⊆ U)
    (hP₀U : P₀ ×ˢ univ ⊆ U) (hUf : ∀ p ∈ U, fderiv ℝ (fun x ↦ f (p.1, x)) p.2 = G p)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ (h : Diffeotopy 𝓘(ℝ, L × (Fin m → ℝ) × (Fin k → ℝ)) ∞ (L × (Fin m → ℝ) × (Fin k → ℝ)))
      (f' : L × (Fin m → ℝ) × (Fin k → ℝ) → F) (V : Set (L × (Fin m → ℝ) × (Fin k → ℝ))),
      (∀ t p, (h (t, p)).1 = p.1) ∧ ContDiff ℝ ∞ f' ∧
      (∃ C, IsCompact C ∧
        (∀ p ∈ C, p.2 ∈ thickening δ (closedBall (0 : Fin m → ℝ) 1 ×ˢ {(0 : Fin k → ℝ)})) ∧
        ∀ p ∉ C, (∀ t, h (t, p) = p) ∧ f' p = f p) ∧
      (∀ t p, dist (h (t, p)) p < δ) ∧
      (∃ N ∈ 𝓝ˢ B, ∀ p : L × (Fin m → ℝ) × (Fin k → ℝ), p.2.1 ∈ N →
        (∀ t, h (t, p) = p) ∧ f' p = f p) ∧
      (∀ p : L × (Fin m → ℝ) × (Fin k → ℝ), p.1 ∈ P₀ → (∀ t, h (t, p) = p) ∧ f' p = f p) ∧
      IsOpen V ∧ (∀ l ∈ K, ∀ y ∈ closedBall (0 : Fin m → ℝ) 1 ×ˢ {(0 : Fin k → ℝ)},
        h (1, (l, y)) ∈ V) ∧
      ∀ p ∈ V, ‖f' p - f p‖ < ε ∧ ‖fderiv ℝ (fun x ↦ f' (p.1, x)) p.2 - G p‖ < ε := by
  -- step 1: the coordinates `Ψ`
  obtain ⟨R, hR, hRK⟩ := exists_pos_norm_finBasis_equivFun_lt hK
  set Ψ := familyCubeEquiv L m k hR.ne'
  -- step 2: the transported datum, holonomic on `Ψ '' U`
  set G'' : (Fin (finrank ℝ L + m) → ℝ) × (Fin k → ℝ) →
      (Fin (finrank ℝ L + m) → ℝ) × (Fin k → ℝ) →L[ℝ] F := fun q ↦
    familyFDeriv f G (Ψ.symm q) ∘L (Ψ.symm : _ →L[ℝ] L × (Fin m → ℝ) × (Fin k → ℝ))
  have hG'' : ContDiff ℝ ∞ G'' :=
    ((hf.familyFDeriv hG (by simp)).comp Ψ.symm.contDiff).clm_comp contDiff_const
  have hUf'' : ∀ x ∈ Ψ '' U, fderiv ℝ (f ∘ Ψ.symm) x = G'' x := by
    rintro _ ⟨q, hq, rfl⟩
    have := (fderiv_comp_symm_eq_familyFDeriv_comp_iff (G := G) Ψ
      (hf.differentiable (by simp) q)).2 (hUf q hq)
    simpa [G''] using this
  -- steps 3 and 4: the cube theorem in the directions of the space, relative to
  -- `familyRelativeSet L R B P₀`
  obtain ⟨h'', f'', V'', ⟨C'', hC'', hC''Q, hhC'', hfC''⟩, hdist, hJ, hV'', hQV'', hf'', happrox,
      N'', hN'', hN''h⟩ :=
    exists_holonomic_approximation_cube_directions hk (Finset.univ.map (Fin.natAddEmb _))
      (hf.comp Ψ.symm.contDiff) hG'' (isClosed_familyRelativeSet R hB hP₀)
      (fun u hu hi ↦ mem_familyRelativeSet_of_abs_eq_one R P₀ hSB u hu hi)
      (Ψ.isOpenMap _ hU) (familyRelativeSet_prod_zero_subset_image hR.ne' hBU hP₀U) hUf''
      (half_pos hε) (lt_min hδ one_pos)
  -- step 5: back to `L × D`
  obtain ⟨h, f', V, hh, hf', hfst, hf'c, ⟨C, hC, hCQ, hCfix⟩, hdist', hV, hKV, happrox'⟩ :=
    exists_holonomic_approximation_family_of_cube hR (fun l hl ↦ (hRK l hl).le) h'' hC''
      hC''Q hhC'' hfC'' hdist hJ hV'' hQV'' hf'' happrox
  -- a point whose image has core part in `N''`, or lies off `C''`, is fixed
  have hfix : ∀ p, (Ψ p).1 ∈ N'' → (∀ t, h (t, p) = p) ∧ f' p = f p := fun p hp ↦ by
    obtain ⟨h₁, h₂⟩ := hN''h (Ψ p) hp
    refine ⟨fun t ↦ ?_, ?_⟩
    · rw [hh, h₁, ContinuousLinearEquiv.symm_apply_apply]
    · rw [hf', h₂, Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
  have hfixC : ∀ p, Ψ p ∉ C'' → (∀ t, h (t, p) = p) ∧ f' p = f p := fun p hp ↦ by
    refine ⟨fun t ↦ ?_, ?_⟩
    · rw [hh, hhC'' t _ hp, ContinuousLinearEquiv.symm_apply_apply]
    · rw [hf', hfC'' _ hp, Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
  -- step 6: the neighbourhood of `B`, by the tube lemma
  obtain ⟨N, hN, hNfix⟩ := exists_mem_nhdsSet_familyCubeEquiv_fst_mem (k := k) hR.ne' hB hN''
    (lt_min hδ one_pos)
  refine ⟨h, f', V, hfst, hf'c,
    ⟨C, hC, fun p hp ↦ thickening_mono (min_le_left δ 1) _ (hCQ p hp), hCfix⟩,
    fun t p ↦ (hdist' t p).trans_le (min_le_left δ 1),
    ⟨N, hN, fun p hp ↦ (hNfix p hp).elim (hfix p) fun hpC ↦ hfixC p fun h' ↦ hpC (hC''Q h')⟩,
    fun p hp ↦ hfix p (interior_subset (subset_interior_iff_mem_nhdsSet.2 hN'' ?_)), hV, hKV,
    fun p hp ↦ ⟨(happrox' p hp).1.trans (half_lt_self hε),
      (happrox' p hp).2.trans_lt (half_lt_self hε)⟩⟩
  refine mem_familyRelativeSet_iff.2 (Or.inr ⟨p.1, hp, ?_⟩)
  ext i
  simp [Ψ]

end Conjugation

end SymplecticGeometry

end
