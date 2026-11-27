/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Instances.Surface.Puncture
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import SymplecticGeometry.AlgebraicTopology.FundamentalGroup.PlaneMinusRealPoints
import SymplecticGeometry.AlgebraicTopology.FundamentalGroup.Basic

/-!
# The punctured sphere as the plane minus real points

This file is the base case `g = 0` of the computation of the fundamental groups of the punctured
closed surfaces `ClosedSurface.puncture g n`. It reads the sphere `ClosedSurface 0`, punctured at
the centres of the balls `0, …, n`, in the complementary chart `ClosedSurface.sphereCoChart`, which
sends `0` to the base point and misses only the centre of the ball `0`. In that chart, after the
standard identification `Complex.orthonormalBasisOneI.repr` of `ℂ` with the Euclidean plane, the
centre of the ball `j ≥ 1` is the real point `1 / j`, so `puncture 0 (n + 1)` is the plane minus
the points `1, 1 / 2, …, 1 / n`, based at `0`.

The points are indexed so that the point of index `k : Fin n` is the centre of the ball
`(Fin.castSucc k).rev`, which is the ball of the peripheral loop
`ClosedSurface.peripheralLoop 0 (n + 1) (Fin.castSucc k)`. Indexed this way they increase with
`k`, and they are positive, at most `1`, and at least `1 / (n + 1) ^ 2` apart: the hypotheses under
which `AlgebraicTopology/FundamentalGroup/PlaneMinusRealPoints.lean` computes the fundamental group
of the plane minus real points.

## Main definitions

* `SymplecticGeometry.ClosedSurface.puncturedSpherePoint n k`: the real number
  `1 / (Fin.castSucc k).rev`, for `k : Fin n`.
* `SymplecticGeometry.ClosedSurface.puncturedSphereHomeomorph n`: the homeomorphism from the plane
  minus the points `puncturedSpherePoint n k` to `puncture 0 (n + 1)`, given by the complementary
  chart.

## Main results

* `SymplecticGeometry.ClosedSurface.strictMono_puncturedSpherePoint`,
  `SymplecticGeometry.ClosedSurface.puncturedSpherePoint_pos`,
  `SymplecticGeometry.ClosedSurface.puncturedSpherePoint_le_one`,
  `SymplecticGeometry.ClosedSurface.one_div_sq_le_abs_puncturedSpherePoint_sub`: the points
  increase, lie in `(0, 1]`, and are at least `1 / (n + 1) ^ 2` apart.
* `SymplecticGeometry.ClosedSurface.sphereCoChart_puncturedSpherePoint`: the complementary chart
  sends `puncturedSpherePoint n k` to the centre of the ball `(Fin.castSucc k).rev`.
* `SymplecticGeometry.ClosedSurface.image_sphereCoChart_compl_range_puncturedSpherePoint`: the
  complementary chart maps the plane minus these points onto `puncture 0 (n + 1)`.
* `SymplecticGeometry.ClosedSurface.coe_puncturedSphereHomeomorph_apply`,
  `SymplecticGeometry.ClosedSurface.puncturedSphereHomeomorph_zero`: the homeomorphism is the
  complementary chart, and sends `0` to the base point.
* `SymplecticGeometry.ClosedSurface.ballPath_zero_zero_apply`,
  `SymplecticGeometry.ClosedSurface.ballCircle_zero_zero_apply`: in the complementary chart, the
  path to the ball `0` is the segment from `0` to `2 √2 e^{iπ/4}`, and its circle is the circle
  `circlePath 0 (2 √2) (π / 4)`, counterclockwise, since the inversion in the unit circle keeps
  the direction of a circle about `0`.
* `SymplecticGeometry.ClosedSurface.map_peripheralLoop_last`: carried to the plane minus the
  points, the last peripheral loop, about the ball `0`, is the reverse of the loop
  `PlaneMinusRealPoints.outerLoop` about the circle of radius `2 √2`, reached at the angle `π / 4`.
* `SymplecticGeometry.ClosedSurface.fromPath_map_peripheralLoop_last`,
  `SymplecticGeometry.ClosedSurface.fromPath_map_peripheralLoop_last_eq_inv_prod`: its class is
  the inverse of that of `outerLoop`, and so, by
  `PlaneMinusRealPoints.fromPath_outerLoop_eq_prod`, the inverse of the product over `List.ofFn`
  of the classes of the loops `PlaneMinusRealPoints.loop` about the points.

## References

* [A. A. Kosinski, *Differential Manifolds*][Kosinski1993] (the two charts of the sphere).
-/

public section

noncomputable section

open Set Function Topology

namespace SymplecticGeometry.ClosedSurface

/-! ### The points -/

variable (n : ℕ)

/-- The point of the real axis that is the centre of the ball `(Fin.castSucc k).rev` of the sphere
in the complementary chart: the inverse `1 / (Fin.castSucc k).rev`, for `k : Fin n`. These are the
points `1 / n < ⋯ < 1 / 2 < 1`, in increasing order. -/
def puncturedSpherePoint (k : Fin n) : ℝ := (((Fin.castSucc k).rev : ℕ) : ℝ)⁻¹

theorem puncturedSpherePoint_def (k : Fin n) :
    puncturedSpherePoint n k = (((Fin.castSucc k).rev : ℕ) : ℝ)⁻¹ :=
  (rfl)

variable {n}

/-- The point of index `k` is `1 / (n - k)`. -/
theorem puncturedSpherePoint_eq (k : Fin n) : puncturedSpherePoint n k = ((n - k : ℕ) : ℝ)⁻¹ := by
  rw [puncturedSpherePoint_def, Fin.val_rev, Fin.val_castSucc]
  congr 2
  omega

/-- The points are positive. -/
theorem puncturedSpherePoint_pos (k : Fin n) : 0 < puncturedSpherePoint n k := by
  rw [puncturedSpherePoint_eq]
  exact inv_pos.2 (Nat.cast_pos.2 (by omega))

/-- The points are at most `1`. -/
theorem puncturedSpherePoint_le_one (k : Fin n) : puncturedSpherePoint n k ≤ 1 := by
  rw [puncturedSpherePoint_eq]
  exact inv_le_one_of_one_le₀ (by exact_mod_cast (by omega : 1 ≤ n - k))

/-- The points increase with their index. -/
theorem strictMono_puncturedSpherePoint : StrictMono (puncturedSpherePoint n) := by
  intro i j (hij : (i : ℕ) < j)
  rw [puncturedSpherePoint_eq, puncturedSpherePoint_eq]
  exact inv_strictAnti₀ (Nat.cast_pos.2 (by omega)) (by exact_mod_cast (by omega : n - j < n - i))

/-- Distinct points `puncturedSpherePoint n i` are at least `1 / (n + 1) ^ 2` apart. -/
theorem one_div_sq_le_abs_puncturedSpherePoint_sub :
    Pairwise fun i j : Fin n ↦
      1 / ((n : ℝ) + 1) ^ 2 ≤ |puncturedSpherePoint n i - puncturedSpherePoint n j| := by
  intro i j hij
  have hij : (i : ℕ) ≠ j := Fin.val_ne_of_ne hij
  rw [puncturedSpherePoint_eq, puncturedSpherePoint_eq]
  -- With `a = n - i` and `b = n - j`, distinct integers in `[1, n]`, the gap is `|b - a| / (a b)`.
  have ha : (1 : ℝ) ≤ ((n - i : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ n - i)
  have hb : (1 : ℝ) ≤ ((n - j : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ n - j)
  have ha' : ((n - i : ℕ) : ℝ) ≤ n := by exact_mod_cast (by omega : n - i ≤ n)
  have hb' : ((n - j : ℕ) : ℝ) ≤ n := by exact_mod_cast (by omega : n - j ≤ n)
  have hab : 1 ≤ |((n - j : ℕ) : ℝ) - ((n - i : ℕ) : ℝ)| := by
    rcases lt_or_gt_of_ne hij with h | h
    · rw [abs_of_neg (by rw [sub_neg]; exact_mod_cast (by omega : n - j < n - i))]
      have : ((n - j : ℕ) : ℝ) + 1 ≤ ((n - i : ℕ) : ℝ) := by
        exact_mod_cast (by omega : n - j + 1 ≤ n - i)
      linarith
    · rw [abs_of_pos (by rw [sub_pos]; exact_mod_cast (by omega : n - i < n - j))]
      have : ((n - i : ℕ) : ℝ) + 1 ≤ ((n - j : ℕ) : ℝ) := by
        exact_mod_cast (by omega : n - i + 1 ≤ n - j)
      linarith
  rw [inv_sub_inv (by positivity) (by positivity), abs_div,
    abs_of_pos (by positivity : (0 : ℝ) < ((n - i : ℕ) : ℝ) * ((n - j : ℕ) : ℝ)),
    div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul ha' hb' (by linarith) (by linarith)]

/-- No point is `0`. -/
theorem puncturedSpherePoint_ne_zero (k : Fin n) : puncturedSpherePoint n k ≠ 0 :=
  (puncturedSpherePoint_pos k).ne'

/-- The complementary chart sends the point `puncturedSpherePoint n k` of the real axis to the
centre of the ball `(Fin.castSucc k).rev`. -/
theorem sphereCoChart_puncturedSpherePoint (k : Fin n) :
    sphereCoChart (Complex.orthonormalBasisOneI.repr (puncturedSpherePoint n k : ℂ)) =
      ball 0 (Fin.castSucc k).rev 0 := by
  have hk : ((Fin.castSucc k).rev : ℕ) ≠ 0 := by
    rw [Fin.val_rev, Fin.val_castSucc]
    omega
  rw [ball_zero_apply_zero_eq_sphereCoChart hk, puncturedSpherePoint_def]
  congr 1
  -- The identification sends a real number `x` to `x • e`.
  ext i
  fin_cases i <;> simp [-Complex.ofReal_inv]

/-! ### The homeomorphism -/

/-- The plane minus the points `puncturedSpherePoint n k` is the open subset
`puncture 0 (n + 1)` of the sphere, read in the complementary chart. -/
theorem image_sphereCoChart_compl_range_puncturedSpherePoint :
    (sphereCoChart ∘ Complex.orthonormalBasisOneI.repr) ''
        (range fun k ↦ (puncturedSpherePoint n k : ℂ))ᶜ =
      (puncture 0 (n + 1) : Set (ClosedSurface 0)) := by
  ext x
  simp only [mem_image, mem_compl_iff, mem_range, not_exists, comp_apply, SetLike.mem_coe,
    mem_puncture]
  constructor
  · rintro ⟨z, hz, rfl⟩ j hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · intro h
      have : sphereCoChart (Complex.orthonormalBasisOneI.repr z) ∈ range sphereCoChart :=
        mem_range_self _
      rw [range_sphereCoChart, h] at this
      exact this rfl
    · -- The ball `j` is the ball `(Fin.castSucc k).rev` for `k = n - j`.
      set k : Fin n := ⟨n - j, by omega⟩
      have hk : ((Fin.castSucc k).rev : ℕ) = j := by
        rw [Fin.val_rev, Fin.val_castSucc]
        simp only [k]
        omega
      rw [← hk, ← sphereCoChart_puncturedSpherePoint k]
      exact fun h ↦ hz k (Complex.orthonormalBasisOneI.repr.injective
        (isComplementaryBall_sphereChart.isOpenEmbedding.injective h)).symm
  · intro hx
    obtain ⟨w, rfl⟩ : x ∈ range sphereCoChart := by
      rw [range_sphereCoChart]
      exact hx 0 n.succ_pos
    refine ⟨Complex.orthonormalBasisOneI.repr.symm w, fun k hk ↦ ?_,
      by rw [LinearIsometryEquiv.apply_symm_apply]⟩
    refine hx _ (Fin.castSucc k).rev.isLt ?_
    rw [← sphereCoChart_puncturedSpherePoint, hk, LinearIsometryEquiv.apply_symm_apply]

variable (n) in
/-- The **punctured sphere as the plane minus real points**: the homeomorphism from the plane minus
the points `puncturedSpherePoint n k = 1 / (Fin.castSucc k).rev` to the sphere punctured at the
centres of the balls `0, …, n`, given by the complementary chart `ClosedSurface.sphereCoChart`
after the identification `Complex.orthonormalBasisOneI.repr` of `ℂ` with the Euclidean plane. -/
def puncturedSphereHomeomorph :
    ((range fun k ↦ (puncturedSpherePoint n k : ℂ))ᶜ : Set ℂ) ≃ₜ puncture 0 (n + 1) :=
  ((isComplementaryBall_sphereChart.isOpenEmbedding.comp
      Complex.orthonormalBasisOneI.repr.toHomeomorph.isOpenEmbedding).isEmbedding.homeomorphImage
      _).trans
    (Homeomorph.setCongr image_sphereCoChart_compl_range_puncturedSpherePoint)

/-- The homeomorphism is the complementary chart, read through the identification of `ℂ` with the
Euclidean plane. -/
@[simp] theorem coe_puncturedSphereHomeomorph_apply
    (z : ((range fun k ↦ (puncturedSpherePoint n k : ℂ))ᶜ : Set ℂ)) :
    (puncturedSphereHomeomorph n z : ClosedSurface 0) =
      sphereCoChart (Complex.orthonormalBasisOneI.repr z) :=
  (rfl)

/-- The point `0` is not among the points `puncturedSpherePoint n k`. -/
theorem zero_mem_compl_range_puncturedSpherePoint :
    (0 : ℂ) ∈ (range fun k ↦ (puncturedSpherePoint n k : ℂ))ᶜ := by
  rintro ⟨k, hk⟩
  exact puncturedSpherePoint_ne_zero k (Complex.ofReal_eq_zero.1 hk)

/-- The homeomorphism sends `0` to the base point of the sphere. -/
@[simp] theorem puncturedSphereHomeomorph_zero :
    puncturedSphereHomeomorph n ⟨0, zero_mem_compl_range_puncturedSpherePoint⟩ =
      ⟨basePoint 0, basePoint_mem_puncture⟩ := by
  ext
  rw [coe_puncturedSphereHomeomorph_apply, map_zero, sphereCoChart_zero]

/-- The inverse of the homeomorphism sends the base point of the sphere to `0`. -/
@[simp] theorem puncturedSphereHomeomorph_symm_basePoint :
    (puncturedSphereHomeomorph n).symm ⟨basePoint 0, basePoint_mem_puncture⟩ =
      ⟨0, zero_mem_compl_range_puncturedSpherePoint⟩ :=
  (puncturedSphereHomeomorph n).symm_apply_eq.2 puncturedSphereHomeomorph_zero.symm

/-! ### The loop about the ball `0` -/

/-- The points `puncturedSpherePoint n k` lie inside the circle of radius `2 √2` about `0`. -/
theorem abs_puncturedSpherePoint_lt (k : Fin n) : |puncturedSpherePoint n k| < 2 * √2 := by
  rw [abs_of_pos (puncturedSpherePoint_pos k)]
  refine (puncturedSpherePoint_le_one k).trans_lt ?_
  nlinarith [Real.sq_sqrt (zero_le_two : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]

/-- The point `2 √2 e^{iπ/4}` of `ℂ` is `(2, 2)`. -/
private theorem repr_circleMap_two_mul_sqrt_two :
    Complex.orthonormalBasisOneI.repr (circleMap 0 (2 * √2) (Real.pi / 4)) = !₂[2, 2] := by
  have hs : √2 * √2 = 2 := Real.mul_self_sqrt zero_le_two
  ext i
  fin_cases i <;>
    simp [Complex.orthonormalBasisOneI_repr_apply, circleMap_zero_re, circleMap_zero_im,
      Real.cos_pi_div_four, Real.sin_pi_div_four] <;>
    linarith [hs]

/-- In the complementary chart, read through the identification of `ℂ` with the Euclidean plane,
the path to the ball `0` of the sphere is the segment from `0` to `2 √2 e^{iπ/4}`. -/
theorem ballPath_zero_zero_apply (t : unitInterval) :
    ballPath 0 0 t = sphereCoChart (Complex.orthonormalBasisOneI.repr
      (Path.segment 0 (circleMap 0 (2 * √2) (Real.pi / 4)) t)) := by
  rw [ballPath_zero_zero, Path.cast_coe, Path.map_coe, comp_apply, Path.segment_apply,
    Path.segment_apply, AffineMap.lineMap_apply_module', AffineMap.lineMap_apply_module',
    add_zero, add_zero, sub_zero, sub_zero, map_smul, repr_circleMap_two_mul_sqrt_two]

/-- In the complementary chart, read through the identification of `ℂ` with the Euclidean plane,
the circle of the ball `0` of the sphere is the circle of radius `2 √2` about `0`, run once
counterclockwise from the angle `π / 4`: the inversion in the unit circle keeps the direction of
a circle about `0`. -/
theorem ballCircle_zero_zero_apply (t : unitInterval) :
    ballCircle 0 0 t = sphereCoChart (Complex.orthonormalBasisOneI.repr
      (circlePath 0 (2 * √2) (Real.pi / 4) t)) := by
  set z := Complex.orthonormalBasisOneI.repr (circlePath 0 (2 * √2) (Real.pi / 4) t) with hz_def
  -- In the chart `sphereChart` the circle has radius `1 / (2 √2)`, and the inversion takes it
  -- to the circle of radius `2 √2`, point by point along the same rays.
  have hz : z = (2 * √2 : ℝ) • EuclideanTorus.neckIsometry (circleMap 0 1 (2 * Real.pi * t)) := by
    rw [hz_def, EuclideanTorus.neckIsometry_circleMap, circlePath_apply]
    ext i
    fin_cases i <;> simp [Complex.orthonormalBasisOneI_repr_apply, circleMap_zero_re,
      circleMap_zero_im, add_comm]
  have hn : ‖z‖ = 2 * √2 := by
    rw [hz_def, LinearIsometryEquiv.norm_map, circlePath_apply, norm_circleMap_zero,
      abs_of_pos (by positivity)]
  have hne : z ≠ 0 := by
    rw [← norm_pos_iff, hn]
    positivity
  rw [ballCircle_apply, ball_zero_eq_sphereChart, sphereCoChart_of_ne hne, zero_smul,
    OpenPartialHomeomorph.univBall_apply (by norm_num), LinearIsometryEquiv.norm_map,
    norm_circleMap_zero, abs_one, vadd_eq_add, add_zero]
  congr 1
  rw [EuclideanGeometry.inversion, dist_zero_right, hn, vsub_eq_sub, sub_zero, vadd_eq_add,
    add_zero, hz, smul_smul]
  congr 1
  field_simp
  norm_num

variable (n) in
/-- Through the homeomorphism `puncturedSphereHomeomorph n`, the reverse of the loop `outerLoop`
about the circle of radius `2 √2`, reached along the ray at the angle `π / 4`, is the last
peripheral loop of `puncture 0 (n + 1)`, the loop about the ball `0`. -/
theorem puncturedSphereHomeomorph_outerLoop_symm_apply (t : unitInterval) :
    puncturedSphereHomeomorph n ((PlaneMinusRealPoints.outerLoop puncturedSpherePoint_ne_zero
        abs_puncturedSpherePoint_lt (div_pos Real.pi_pos four_pos)
        (by linarith [Real.pi_pos] : Real.pi / 4 < Real.pi)).symm t) =
      peripheralLoop 0 (n + 1) (Fin.last n) t := by
  have hsymm : (PlaneMinusRealPoints.outerLoopInPlane (2 * √2) (Real.pi / 4)).symm =
      ((Path.segment 0 (circleMap 0 (2 * √2) (Real.pi / 4))).trans
        (circlePath 0 (2 * √2) (Real.pi / 4)).symm).trans
          (Path.segment 0 (circleMap 0 (2 * √2) (Real.pi / 4))).symm := by
    rw [PlaneMinusRealPoints.outerLoopInPlane_def, Path.trans_symm, Path.trans_symm,
      Path.symm_symm]
  have ht := congrArg (· t) hsymm
  rw [Path.symm_apply, comp_apply] at ht
  ext
  rw [coe_puncturedSphereHomeomorph_apply, coe_peripheralLoop_apply, Path.symm_apply, comp_apply,
    PlaneMinusRealPoints.coe_outerLoop_apply, ht, Fin.rev_last, Fin.val_zero, ballLoop_def]
  simp only [Path.trans_apply, Path.symm_apply, comp_apply]
  split_ifs <;> simp only [ballPath_zero_zero_apply, ballCircle_zero_zero_apply]

variable (n) in
/-- **The loop about the ball `0` is the reversed large circle.** The last peripheral loop of
`puncture 0 (n + 1)`, the loop about the ball `0`, carried to the plane minus the points
`puncturedSpherePoint n k` by the inverse of `puncturedSphereHomeomorph n`, is the reverse of the
loop `outerLoop` about the circle of radius `2 √2`, reached along the ray at the angle
`π / 4`. -/
theorem map_peripheralLoop_last :
    ((peripheralLoop 0 (n + 1) (Fin.last n)).map
        (puncturedSphereHomeomorph n).symm.continuous).cast
        puncturedSphereHomeomorph_symm_basePoint.symm
        puncturedSphereHomeomorph_symm_basePoint.symm =
      (PlaneMinusRealPoints.outerLoop puncturedSpherePoint_ne_zero abs_puncturedSpherePoint_lt
        (div_pos Real.pi_pos four_pos)
        (by linarith [Real.pi_pos] : Real.pi / 4 < Real.pi)).symm := by
  ext t
  rw [Path.cast_coe, Path.map_coe, comp_apply, ← puncturedSphereHomeomorph_outerLoop_symm_apply,
    Homeomorph.symm_apply_apply]

variable (n) in
/-- In the fundamental group of the plane minus the points `puncturedSpherePoint n k`, at `0`, the
last peripheral loop of `puncture 0 (n + 1)`, carried there by the inverse of
`puncturedSphereHomeomorph n`, has the inverse of the class of `outerLoop`, the loop about the
circle of radius `2 √2` reached along the ray at the angle `π / 4`. -/
theorem fromPath_map_peripheralLoop_last :
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        (((peripheralLoop 0 (n + 1) (Fin.last n)).map
          (puncturedSphereHomeomorph n).symm.continuous).cast
            puncturedSphereHomeomorph_symm_basePoint.symm
            puncturedSphereHomeomorph_symm_basePoint.symm)) =
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        (PlaneMinusRealPoints.outerLoop puncturedSpherePoint_ne_zero abs_puncturedSpherePoint_lt
          (div_pos Real.pi_pos four_pos)
          (by linarith [Real.pi_pos] : Real.pi / 4 < Real.pi))))⁻¹ := by
  rw [map_peripheralLoop_last, Path.Homotopic.Quotient.mk_symm, FundamentalGroup.fromPath_symm]

variable (n) in
/-- In the fundamental group of the plane minus the points `puncturedSpherePoint n k`, at `0`, the
last peripheral loop of `puncture 0 (n + 1)`, carried there by the inverse of
`puncturedSphereHomeomorph n`, has the inverse of the product, over `List.ofFn`, of the classes of
the loops `PlaneMinusRealPoints.loop` about the points. -/
theorem fromPath_map_peripheralLoop_last_eq_inv_prod :
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        (((peripheralLoop 0 (n + 1) (Fin.last n)).map
          (puncturedSphereHomeomorph n).symm.continuous).cast
            puncturedSphereHomeomorph_symm_basePoint.symm
            puncturedSphereHomeomorph_symm_basePoint.symm)) =
      (List.ofFn fun k ↦ FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        (PlaneMinusRealPoints.loop (by positivity) one_div_sq_le_abs_puncturedSpherePoint_sub
          puncturedSpherePoint_ne_zero k))).prod⁻¹ := by
  rw [fromPath_map_peripheralLoop_last, PlaneMinusRealPoints.fromPath_outerLoop_eq_prod
    (by positivity) one_div_sq_le_abs_puncturedSpherePoint_sub puncturedSpherePoint_pos
    (fun k ↦ (le_abs_self _).trans_lt (abs_puncturedSpherePoint_lt k))
    (div_pos Real.pi_pos four_pos) (by linarith [Real.pi_pos] : Real.pi / 4 < Real.pi)
    strictMono_puncturedSpherePoint]

end SymplecticGeometry.ClosedSurface

end
