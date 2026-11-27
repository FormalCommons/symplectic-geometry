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
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Tactic.Module
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.UrysohnsLemma
import SymplecticGeometry.Analysis.Calculus.HolonomicApproximation.Cube
import SymplecticGeometry.Analysis.Normed.Group.Pi
import SymplecticGeometry.Geometry.Diffeomorphism.Diffeotopy.OfContMDiff
import SymplecticGeometry.Topology.Compactness.Normed
import SymplecticGeometry.Topology.MetricSpace.Thickening
import TauCeti.Analysis.Calculus.ContDiff.ContinuousLinearMap
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Convex.PartitionOfUnity

/-!
# Holonomic approximation for families of formal sections

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
* `SymplecticGeometry.exists_contDiff_fderiv_eq_of_fderiv_eq_on_prod`: a datum on `L × E`
  that is holonomic on `K ×ˢ W`, for a set `K` of parameters and an open `W` containing a
  closed `S`, becomes holonomic on an open set containing `univ ×ˢ S` when `G` is replaced by
  `G + χ • (∂ₓf - G)`, with `χ` a smooth cutoff on `E` equal to `1` near `S` and to `0` near the
  complement of `W` (Mathlib's `exists_contMDiffMap_zero_one_nhds_of_isClosed`). Nothing changes
  where the datum is already holonomic or over `K`, so the output meets the hypotheses of
  `exists_holonomic_approximation_family` for a datum that is holonomic near `B ×ˢ {0}` only
  over `K`.
* `SymplecticGeometry.exists_holonomic_approximation_continuous_family`: the same theorem for a
  family over a compact Hausdorff space `P`, continuous in the parameter together with the first
  space derivatives. The result is stated through a continuous `σ : P → Fin n → ℝ` and a smooth
  diffeotopy and correction `g` on `(Fin n → ℝ) × D`. It follows from the smooth version over
  `Fin n → ℝ`. Tau Ceti's `ContinuousMap.exists_partitionOfUnity_dist_finsum_smul_le`, applied
  to the error `G l - fderiv ℝ (f l)` curried into a map from `P` to the continuous maps on
  `closedBall 0 2`, gives finitely many parameters `l i` and a partition of unity `ρ` on `P` such
  that `∑ i, ρ i l • (G (l i) - fderiv ℝ (f (l i)))` is uniformly close to the error at `l`. Then
  `σ l = Fin.cons (τ l) (ρ · l)`, where `τ` vanishes on `P₀` and equals `1` where the error is
  not already small. The datum over `s : Fin n → ℝ` is `∑ i, s i.succ • f (l i)`, with the
  errors of the samples added back through the cutoff `Real.smoothTransition (2 * s 0 - 1)`, so
  it is holonomic where `s 0 < 1 / 2`.

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
  have hd := TauCeti.fderiv_slice_right (f := f'' ∘ Ψ) (hf''.comp p Ψ.differentiableAt)
  rw [Ψ.comp_right_fderiv, ContinuousLinearMap.comp_assoc] at hd
  simp only [Function.comp_apply] at hd
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

section Cutoff

open scoped ContDiff Topology Manifold

variable {L E F : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A cutoff in space makes a family of data holonomic near a closed set `S` for every
parameter, without changing it over a set `K` of parameters. Let `f : L × E → F` be `Cᵐ` and
`G : L × E → E →L[ℝ] F` be `Cⁿ`, with `n + 1 ≤ m` and `n ≤ ∞`, and let the derivative of `f` in
the space variable equal `G` on `K ×ˢ W`, for an open `W` containing `S`. Then there are a `Cⁿ`
map `G'` and an open set `U'` containing `univ ×ˢ S` such that the derivative of `f` in the
space variable equals `G'` on `U'`, `G'` equals `G` at every point where the derivative of `f`
in the space variable is `G`, and `G' (l, x) = G (l, x)` for every `l ∈ K` and every `x`.

With `S := B ×ˢ {0}` and `P₀ := ∅`, the output fits the hypotheses `hBU`, `hP₀U` and `hUf` of
`exists_holonomic_approximation_family`, and its approximation bounds over `K` are then bounds
against `G`. -/
theorem exists_contDiff_fderiv_eq_of_fderiv_eq_on_prod {m n : WithTop ℕ∞}
    {f : L × E → F} {G : L × E → E →L[ℝ] F} (hf : ContDiff ℝ m f)
    (hG : ContDiff ℝ n G) (hnm : n + 1 ≤ m) (hn : n ≤ ∞) {K : Set L} {S W : Set E}
    (hS : IsClosed S) (hW : IsOpen W) (hSW : S ⊆ W)
    (hWf : ∀ l ∈ K, ∀ x ∈ W, fderiv ℝ (fun y ↦ f (l, y)) x = G (l, x)) :
    ∃ G' : L × E → E →L[ℝ] F, ContDiff ℝ n G' ∧
      (∃ U' : Set (L × E), IsOpen U' ∧ univ ×ˢ S ⊆ U' ∧
        ∀ p ∈ U', fderiv ℝ (fun x ↦ f (p.1, x)) p.2 = G' p) ∧
      (∀ p, fderiv ℝ (fun x ↦ f (p.1, x)) p.2 = G p → G' p = G p) ∧
      ∀ l ∈ K, ∀ x, G' (l, x) = G (l, x) := by
  -- a smooth cutoff `χ`, zero near `Wᶜ` and one near `S`
  obtain ⟨χ, hχ0, hχ1, -⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    (I := 𝓘(ℝ, E)) (n := ⊤) hW.isClosed_compl hS (disjoint_compl_left_iff_subset.2 hSW)
  obtain ⟨O, hO, hSO, hOχ⟩ := mem_nhdsSet_iff_exists.1 hχ1
  have hχ : ContDiff ℝ n χ := (contMDiff_iff_contDiff.1 χ.contMDiff).of_le hn
  -- the derivative of `f` in the space variable
  set d : L × E → E →L[ℝ] F := fun p ↦ fderiv ℝ (fun x ↦ f (p.1, x)) p.2 with hd_def
  have hd : ContDiff ℝ n d :=
    ContDiff.fderiv (f := fun (p : L × E) (x : E) ↦ f (p.1, x))
      (hf.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)) contDiff_snd hnm
  have hGd : ∀ p, d p = G p → G p + χ p.2 • (d p - G p) = G p := fun p hp ↦ by
    rw [hp, sub_self, smul_zero, add_zero]
  refine ⟨fun p ↦ G p + χ p.2 • (d p - G p),
    hG.add ((hχ.comp contDiff_snd).smul (hd.sub hG)),
    ⟨univ ×ˢ O, isOpen_univ.prod hO, fun p hp ↦ ⟨mem_univ _, hSO hp.2⟩, fun p hp ↦ ?_⟩,
    hGd, fun l hl x ↦ ?_⟩
  · beta_reduce
    rw [hOχ hp.2, one_smul, add_sub_cancel, hd_def]
  · by_cases hx : x ∈ W
    · exact hGd _ (hWf l hl x hx)
    · beta_reduce
      rw [hχ0.self_of_nhdsSet x hx, zero_smul, add_zero]

end Cutoff

section Continuous

open scoped Manifold ContDiff Topology

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {P : Type*} [TopologicalSpace P]

/-- The final estimate of `exists_holonomic_approximation_continuous_family`, at one point. For
weights `w i` and `c ∈ [0, 1]`, the approximation `d₀ + (A - ∑ i, w i • d i)` of `e₀ + d₀` is
`ε`-close to it when `A` is `ε / 2`-close to `∑ i, w i • (d i + c • e i)`, `∑ i, w i • e i` is
within `ε / 8` of `e₀`, and `‖e₀‖ < ε / 4` if `c < 1`: the difference is
`(A - ∑ i, w i • (d i + c • e i)) + c • (∑ i, w i • e i - e₀) - (1 - c) • e₀`. -/
private theorem norm_add_sub_sum_smul_sub_lt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {n : ℕ} {w : Fin n → ℝ} {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1)
    {d e : Fin n → E} {A d₀ e₀ : E} {ε : ℝ} (hA : ‖A - ∑ i, w i • (d i + c • e i)‖ < ε / 2)
    (he : ‖∑ i, w i • e i - e₀‖ ≤ ε / 8) (he₀ : c < 1 → ‖e₀‖ < ε / 4) :
    ‖d₀ + (A - ∑ i, w i • d i) - (e₀ + d₀)‖ < ε := by
  have hε : 0 < ε := by linarith [(norm_nonneg _).trans_lt hA]
  have key : d₀ + (A - ∑ i, w i • d i) - (e₀ + d₀) =
      (A - ∑ i, w i • (d i + c • e i)) + c • (∑ i, w i • e i - e₀) - (1 - c) • e₀ := by
    simp only [smul_add, Finset.sum_add_distrib, smul_comm (w _) c, ← Finset.smul_sum]
    module
  have h₁ : ‖c • (∑ i, w i • e i - e₀)‖ ≤ ε / 8 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) hc.2).trans he
  have h₂ : ‖(1 - c) • e₀‖ ≤ ε / 4 := by
    rcases eq_or_lt_of_le hc.2 with hc1 | hc1
    · rw [hc1, sub_self, zero_smul, norm_zero]
      positivity
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    exact (mul_le_of_le_one_left (norm_nonneg _) (by linarith [hc.1])).trans (he₀ hc1).le
  rw [key]
  calc _ ≤ ‖A - ∑ i, w i • (d i + c • e i)‖ + ‖c • (∑ i, w i • e i - e₀)‖ +
        ‖(1 - c) • e₀‖ := (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ < ε := by linarith

/-- Holonomic approximation for a family over a compact Hausdorff space `P` that is only
continuous in the parameter, in coordinates ([EliashbergMishachev2002], Theorem 4.7.4). Let
`(f l, G l)`, `l : P`, be formal sections on `D = (Fin m → ℝ) × (Fin k → ℝ)`, `0 < k`, each
smooth, with `fderiv ℝ (f l) x` and `G l x` jointly continuous in `(l, x)`, and holonomic on an
open `U ⊆ P × D` that contains every point `(l, (u, 0))` with `u` in a closed `B ⊇ sphere 0 1`
and every point over a closed `P₀ ⊆ P`. Then for `ε, δ > 0` there are a continuous
`σ : P → Fin n → ℝ`, a diffeotopy `h` of `(Fin n → ℝ) × D` keeping the first coordinate, a smooth
`g` and an open `V ⊆ P × D` with the following properties, where the diffeotopy at `l` is the
slice of `h` at `σ l` and the approximation at `l` is `f l + g (σ l, ·)`. Each slice is smooth;
since `σ` is continuous and `g` smooth, the correction `g (σ l, ·)` has all its space derivatives
continuous in `(l, x)`, so the approximation is smooth with first space derivative continuous in
`(l, x)`. At every point `(s, x)` of `(Fin n → ℝ) × D`, not only for `s` in the range of `σ`,
`h` is the identity and `g` vanishes when `(s, x)` lies off a compact set `C` whose points have
space part in the `δ`-thickening of the cube `Q = closedBall 0 1 ×ˢ {0}`, or when the core
coordinate of `x` lies in a neighbourhood `N` of `B`; and `h` moves the space part by less than
`δ`. Over `σ l` with `l ∈ P₀`, `h` is the identity and `g` vanishes; `V` contains the image of
`Q` under the slice at time `1`, for every `l`; and on `V`, `g (σ l, ·)` is less than `ε` and
the space derivative of the approximation is `ε`-close to `G`. -/
theorem exists_holonomic_approximation_continuous_family [CompactSpace P] [T2Space P]
    (hk : 0 < k) {f : P → (Fin m → ℝ) × (Fin k → ℝ) → F}
    {G : P → (Fin m → ℝ) × (Fin k → ℝ) → (Fin m → ℝ) × (Fin k → ℝ) →L[ℝ] F}
    (hf : ∀ l, ContDiff ℝ ∞ (f l)) (hG : ∀ l, ContDiff ℝ ∞ (G l))
    (hdf : Continuous fun p : P × (Fin m → ℝ) × (Fin k → ℝ) ↦ fderiv ℝ (f p.1) p.2)
    (hcG : Continuous fun p : P × (Fin m → ℝ) × (Fin k → ℝ) ↦ G p.1 p.2)
    {P₀ : Set P} (hP₀ : IsClosed P₀) {B : Set (Fin m → ℝ)} (hB : IsClosed B)
    (hSB : sphere 0 1 ⊆ B) {U : Set (P × (Fin m → ℝ) × (Fin k → ℝ))} (hU : IsOpen U)
    (hBU : univ ×ˢ (B ×ˢ {0}) ⊆ U) (hP₀U : P₀ ×ˢ univ ⊆ U)
    (hUf : ∀ p ∈ U, fderiv ℝ (f p.1) p.2 = G p.1 p.2) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ (n : ℕ) (σ : P → Fin n → ℝ)
      (h : Diffeotopy 𝓘(ℝ, (Fin n → ℝ) × (Fin m → ℝ) × (Fin k → ℝ)) ∞
        ((Fin n → ℝ) × (Fin m → ℝ) × (Fin k → ℝ)))
      (g : (Fin n → ℝ) × (Fin m → ℝ) × (Fin k → ℝ) → F)
      (V : Set (P × (Fin m → ℝ) × (Fin k → ℝ))),
      Continuous σ ∧ (∀ t q, (h (t, q)).1 = q.1) ∧ ContDiff ℝ ∞ g ∧
      (∃ C, IsCompact C ∧
        (∀ q ∈ C, q.2 ∈ thickening δ (closedBall (0 : Fin m → ℝ) 1 ×ˢ {(0 : Fin k → ℝ)})) ∧
        ∀ q ∉ C, (∀ t, h (t, q) = q) ∧ g q = 0) ∧
      (∀ t q, dist (h (t, q)).2 q.2 < δ) ∧
      (∃ N ∈ 𝓝ˢ B, ∀ q : (Fin n → ℝ) × (Fin m → ℝ) × (Fin k → ℝ), q.2.1 ∈ N →
        (∀ t, h (t, q) = q) ∧ g q = 0) ∧
      (∀ l ∈ P₀, ∀ x, (∀ t, h (t, (σ l, x)) = (σ l, x)) ∧ g (σ l, x) = 0) ∧
      IsOpen V ∧ (∀ l, ∀ y ∈ closedBall (0 : Fin m → ℝ) 1 ×ˢ {(0 : Fin k → ℝ)},
        (l, (h (1, (σ l, y))).2) ∈ V) ∧
      ∀ p ∈ V, ‖g (σ p.1, p.2)‖ < ε ∧
        ‖fderiv ℝ (fun x ↦ f p.1 x + g (σ p.1, x)) p.2 - G p.1 p.2‖ < ε := by
  classical
  -- step 1: the error `e` of the datum, and uniform control on the compact `closedBall 0 2`
  set e : P → (Fin m → ℝ) × (Fin k → ℝ) → (Fin m → ℝ) × (Fin k → ℝ) →L[ℝ] F :=
    fun l x ↦ G l x - fderiv ℝ (f l) x
  have hce : Continuous fun p : P × (Fin m → ℝ) × (Fin k → ℝ) ↦ e p.1 p.2 := hcG.sub hdf
  have heU : ∀ l x, (l, x) ∈ U → e l x = 0 := fun l x hp ↦ by simp [e, hUf _ hp]
  set O : Set ((Fin m → ℝ) × (Fin k → ℝ)) := (Prod.snd '' Uᶜ)ᶜ
  have hO : IsOpen O := (isClosedMap_snd_of_compactSpace _ hU.isClosed_compl).isOpen_compl
  have hOU : ∀ l, ∀ x ∈ O, (l, x) ∈ U := fun l x hx ↦ by_contra fun h ↦ hx ⟨(l, x), h, rfl⟩
  have hBO : B ×ˢ {0} ⊆ O := by
    rintro x hx ⟨p, hp, rfl⟩
    exact hp (hBU ⟨mem_univ _, hx⟩)
  set O₀ : Set P := {l | ∀ x ∈ closedBall (0 : (Fin m → ℝ) × (Fin k → ℝ)) 2,
    ‖G l x - fderiv ℝ (f l) x‖ < ε / 4}
  have hO₀ : IsOpen O₀ := (isCompact_closedBall _ _).isOpen_setOf_forall_norm_sub_lt
    (f := fun p : P × (Fin m → ℝ) × (Fin k → ℝ) ↦ G p.1 p.2) hcG hdf _
  have hP₀O₀ : P₀ ⊆ O₀ := fun l hl x _ ↦ by
    simpa [hUf (l, x) (hP₀U ⟨hl, mem_univ x⟩)] using hε
  -- step 2: a partition of unity `ρ` on `P`, indexed by finitely many samples `pts i`, whose
  -- combinations of the sampled errors are uniformly `ε / 8`-close to `e` on `closedBall 0 2`
  set Φ : C(P, C(closedBall (0 : (Fin m → ℝ) × (Fin k → ℝ)) 2,
      (Fin m → ℝ) × (Fin k → ℝ) →L[ℝ] F)) :=
    ContinuousMap.curry ⟨fun p ↦ e p.1 p.2,
      hce.comp (continuous_fst.prodMk (continuous_subtypeVal.comp continuous_snd))⟩
  obtain ⟨t, ρ, hρ⟩ := ContinuousMap.exists_partitionOfUnity_dist_finsum_smul_le
    (E := C(closedBall (0 : (Fin m → ℝ) × (Fin k → ℝ)) 2, (Fin m → ℝ) × (Fin k → ℝ) →L[ℝ] F))
    Φ (ε := ε / 8) (by positivity)
  set n' := t.card
  set pts : Fin n' → P := fun i ↦ (t.equivFin.symm i : P)
  have hρe : ∀ l, ∀ x ∈ closedBall (0 : (Fin m → ℝ) × (Fin k → ℝ)) 2,
      ‖∑ i, ρ (t.equivFin.symm i) l • e (pts i) x - e l x‖ ≤ ε / 8 := fun l x hx ↦ by
    have := (ContinuousMap.dist_apply_le_dist ⟨x, hx⟩).trans (hρ l)
    rw [finsum_eq_sum_of_fintype, ← t.equivFin.symm.sum_comp, dist_eq_norm] at this
    simpa [Φ, pts] using this
  -- step 3: the extra coordinate `τ` and the cutoff `χ`
  obtain ⟨τ, hτ0, hτ1, hτI⟩ := exists_continuous_zero_one_of_isClosed hP₀
    hO₀.isClosed_compl (disjoint_compl_right_iff_subset.2 hP₀O₀)
  set χ : ℝ → ℝ := fun r ↦ Real.smoothTransition (2 * r - 1)
  have hχ : ContDiff ℝ ∞ χ := Real.smoothTransition.contDiff.comp (by fun_prop)
  -- step 4: the datum on `(Fin (n' + 1) → ℝ) × D` and the smooth version
  set σ : P → Fin (n' + 1) → ℝ := fun l ↦ Fin.cons (τ l) fun i ↦ ρ (t.equivFin.symm i) l
  have hσ : Continuous σ := continuous_pi fun j ↦ by
    refine Fin.cases ?_ (fun i ↦ ?_) j
    · simpa [σ] using τ.continuous
    · simpa [σ] using (ρ _).continuous
  have hσK : ∀ l, σ l ∈ closedBall 0 1 := fun l ↦ by
    refine mem_closedBall_zero_iff.2 ((pi_norm_le_iff_of_nonneg zero_le_one).2 fun j ↦ ?_)
    refine Fin.cases ?_ (fun i ↦ ?_) j
    · simpa [σ, abs_le, Real.norm_eq_abs] using
        ⟨(neg_nonpos.2 zero_le_one).trans (hτI l).1, (hτI l).2⟩
    · simpa [σ, abs_le, Real.norm_eq_abs] using
        ⟨(neg_nonpos.2 zero_le_one).trans (ρ.nonneg _ l), ρ.le_one _ l⟩
  have hfd : ∀ l, ContDiff ℝ ∞ (fderiv ℝ (f l)) := fun l ↦ (hf l).fderiv_right (by simp)
  set F₀ : (Fin (n' + 1) → ℝ) × (Fin m → ℝ) × (Fin k → ℝ) → F :=
    fun q ↦ ∑ i, q.1 i.succ • f (pts i) q.2
  set G₀ : (Fin (n' + 1) → ℝ) × (Fin m → ℝ) × (Fin k → ℝ) →
      (Fin m → ℝ) × (Fin k → ℝ) →L[ℝ] F :=
    fun q ↦ ∑ i, q.1 i.succ • (fderiv ℝ (f (pts i)) q.2 + χ (q.1 0) • e (pts i) q.2)
  have hcoord : ∀ j, ContDiff ℝ ∞ fun q : (Fin (n' + 1) → ℝ) × (Fin m → ℝ) × (Fin k → ℝ) ↦ q.1 j :=
    fun j ↦ by fun_prop
  have hF₀ : ContDiff ℝ ∞ F₀ := ContDiff.sum fun i _ ↦
    (hcoord i.succ).smul ((hf _).comp contDiff_snd)
  have hG₀ : ContDiff ℝ ∞ G₀ := ContDiff.sum fun i _ ↦
    (hcoord i.succ).smul (((hfd _).comp contDiff_snd).add
      ((hχ.comp (hcoord 0)).smul
        (((hG _).sub (hfd _)).comp contDiff_snd)))
  have hF₀d : ∀ (s : Fin (n' + 1) → ℝ) x, HasFDerivAt (fun y ↦ F₀ (s, y))
      (∑ i, s i.succ • fderiv ℝ (f (pts i)) x) x := fun s x ↦
    HasFDerivAt.fun_sum fun (i : Fin n') _ ↦
      (((hf _).differentiable (by simp) x).hasFDerivAt).const_smul (s i.succ)
  set U₀ : Set ((Fin (n' + 1) → ℝ) × (Fin m → ℝ) × (Fin k → ℝ)) :=
    {q | q.1 0 < 1 / 2 ∨ q.2 ∈ O}
  have hU₀ : IsOpen U₀ := (isOpen_lt ((continuous_apply 0).comp continuous_fst)
    continuous_const).union (hO.preimage continuous_snd)
  have hUf₀ : ∀ q ∈ U₀, fderiv ℝ (fun x ↦ F₀ (q.1, x)) q.2 = G₀ q := fun q hq ↦ by
    rw [(hF₀d q.1 q.2).fderiv]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rcases hq with hq | hq
    · have hχ0 : χ (q.1 0) = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
      rw [hχ0, zero_smul, add_zero]
    · rw [heU _ _ (hOU _ _ hq), smul_zero, add_zero]
  obtain ⟨h, f'', V'', hfst, hf'', ⟨C₁, hC₁, hC₁Q, hC₁fix⟩, hdist, ⟨N, hN, hNfix⟩, hP₀fix,
      hV'', hKV'', happrox⟩ :=
    exists_holonomic_approximation_family hk hF₀ hG₀ (isCompact_closedBall 0 1)
      (isClosed_le (continuous_apply 0) (continuous_const (y := (1 / 4 : ℝ)))) hB hSB hU₀
      (fun q hq ↦ Or.inr (hBO hq.2)) (fun q hq ↦ Or.inl (lt_of_le_of_lt hq.1 (by norm_num)))
      hUf₀ (half_pos hε) (lt_min hδ one_pos)
  have hfix : ∀ q, ((∀ t, h (t, q) = q) ∧ f'' q = F₀ q) →
      (∀ t, h (t, q) = q) ∧ f'' q - F₀ q = 0 := fun q hq ↦ ⟨hq.1, sub_eq_zero.2 hq.2⟩
  refine ⟨n' + 1, σ, h, fun q ↦ f'' q - F₀ q,
    {p | (σ p.1, p.2) ∈ V''} ∩ univ ×ˢ ball 0 2, hσ, hfst, hf''.sub hF₀,
    ⟨C₁, hC₁, fun q hq ↦ thickening_mono (min_le_left _ _) _ (hC₁Q q hq),
      fun q hq ↦ hfix _ (hC₁fix q hq)⟩,
    fun t q ↦ ?_, ⟨N, hN, fun q hq ↦ hfix _ (hNfix q hq)⟩,
    fun l hl x ↦ hfix _ (hP₀fix _ ?_), ?_, fun l y hy ↦ ?_, fun p hp ↦ ?_⟩
  · have := hdist t q
    rw [Prod.dist_eq] at this
    exact (le_max_right _ _).trans_lt (this.trans_le (min_le_left _ _))
  · simp [σ, hτ0 hl]
  · exact (hV''.preimage ((hσ.comp continuous_fst).prodMk continuous_snd)).inter
      (isOpen_univ.prod isOpen_ball)
  · have hq : (σ l, (h (1, (σ l, y))).2) = h (1, (σ l, y)) := Prod.ext (hfst 1 (σ l, y)).symm rfl
    refine ⟨by simpa [hq] using hKV'' (σ l) (hσK l) y hy, mem_univ _, ?_⟩
    have hd := hdist 1 (σ l, y)
    rw [Prod.dist_eq] at hd
    have hy0 : dist y 0 ≤ 1 := by
      rw [Prod.dist_eq]
      exact max_le (mem_closedBall.1 hy.1) (by simp [mem_singleton_iff.1 hy.2])
    exact mem_ball.2 ((dist_triangle _ y 0).trans_lt (by
      linarith [le_max_right (dist (h (1, (σ l, y))).1 (σ l, y).1)
        (dist (h (1, (σ l, y))).2 (σ l, y).2), min_le_right δ 1]))
  obtain ⟨h₁, h₂⟩ := happrox (σ p.1, p.2) hp.1
  refine ⟨h₁.trans (half_lt_self hε), ?_⟩
  obtain ⟨l, x⟩ := p
  simp only at h₂ hp ⊢
  have hx : x ∈ closedBall (0 : (Fin m → ℝ) × (Fin k → ℝ)) 2 := ball_subset_closedBall hp.2.2
  have hA : HasFDerivAt (fun y ↦ f'' (σ l, y)) (fderiv ℝ (fun y ↦ f'' (σ l, y)) x) x :=
    ((hf''.differentiable (by simp) _).comp x
      ((differentiableAt_const _).prodMk differentiableAt_id)).hasFDerivAt
  rw [(((hf l).differentiable (by simp) x).hasFDerivAt.fun_add
    (hA.fun_sub (hF₀d (σ l) x))).fderiv, show G l x = e l x + fderiv ℝ (f l) x by simp [e]]
  simp only [σ, Fin.cons_succ, Fin.cons_zero, G₀] at h₂ ⊢
  refine norm_add_sub_sum_smul_sub_lt
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩ h₂ (hρe l x hx) fun hc ↦ ?_
  have hl : l ∈ O₀ := by
    by_contra hl
    refine hc.ne (Real.smoothTransition.one_of_one_le ?_)
    rw [hτ1 hl]
    norm_num
  exact hl x hx

end Continuous

end SymplecticGeometry

end
