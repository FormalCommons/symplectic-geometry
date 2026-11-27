/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Instances.Surface.Puncture
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import SymplecticGeometry.AlgebraicTopology.FundamentalGroup.PlaneMinusRealPoints
import TauCeti.AlgebraicTopology.FundamentalGroup.PuncturedStarConvex
import TauCeti.AlgebraicTopology.UniversalCover.Circle.FundamentalGroup
import SymplecticGeometry.Geometry.Euclidean.Inversion
import TauCeti.Topology.Path.Map
import TauCeti.Topology.Circle.Degree
import SymplecticGeometry.AlgebraicTopology.FundamentalGroup.Basic
public import TauCeti.GroupTheory.SurfaceGroup.Basic
import TauCeti.GroupTheory.SurfaceGroup.LowGenus
import TauCeti.AlgebraicTopology.FundamentalGroup.Homeomorph
import TauCeti.GroupTheory.FreeGroup.Primitive

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
* `SymplecticGeometry.ClosedSurface.puncturedSphereFundamentalGroupMulEquiv n`: the isomorphism of
  the fundamental group of `puncture 0 (n + 1)`, at the base point, with Tau Ceti's orientable
  surface group `TauCeti.SurfaceGroup.Orientable 0 (n + 1)`.

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
* `SymplecticGeometry.ClosedSurface.ballCircle_zero_apply_eq_sphereChart`: in the chart
  `sphereChart`, the circle of the ball `j` is the circle of radius `√2 / 4` about `j • e`, from the
  angle `π / 4`.
* `SymplecticGeometry.ClosedSurface.map_peripheralLoop_castSucc_homotopic_loop`: the peripheral
  loop `Fin.castSucc k`, carried to the plane minus the points, is homotopic to the loop
  `PlaneMinusRealPoints.loop` about `puncturedSpherePoint n k`, for `δ = 1 / (n + 1) ^ 2`.
* `SymplecticGeometry.ClosedSurface.puncturedSphereFundamentalGroupMulEquiv_peripheralLoop`: that
  isomorphism sends the class of each peripheral loop to the peripheral element of the same index.
* `SymplecticGeometry.ClosedSurface.exists_puncturedFundamentalGroupMulEquiv_zero`: for every `n`,
  the fundamental group of `puncture 0 n` is isomorphic to `Orientable 0 n`, the peripheral loops
  going to the peripheral elements; for `n = 0` both groups are trivial, the sphere being simply
  connected.

## Implementation notes

The comparison of the loops about the finite punctures is made in the chart `sphereChart`, read in
`ℂ`, to which the inversion `z ↦ (conj z)⁻¹` in the unit circle carries the plane minus the points.
There the reversed circle of the ball `j = (Fin.castSucc k).rev` is a clockwise circle about the
real point `j`, the path to it runs from `-i` through the lower half-plane, and the loop
`PlaneMinusRealPoints.loop` becomes a small loop about `j` run clockwise, since the inversion
reverses orientation. Both lie in the punctured fan `PlaneMinusRealPoints.fan c 1 k \ {j}` of
the centres `c i = (Fin.castSucc i).rev`, the lower half-plane together with the strip of
half-width `1 / 2` about `j`, punctured at `j`. It is star-convex about `j`
(`PlaneMinusRealPoints.starConvex_fan`), so its direction map from `j` is injective on
fundamental groups (`StarConvex.fundamentalGroup_map_directionFrom_bijective`). Both inner
loops have direction of degree `-1`, the inverted one by Tau Ceti's dog-on-a-leash lemma
`Circle.degree_eq_of_norm_sub_lt`, so Tau Ceti's `Circle.homotopic_trans_of_degree_map_eq` makes
them conjugate along any path. This follows the proof of Tau Ceti's
`TauCeti.ThricePuncturedSphere.transport_δZero_eq_periph0`
(`TauCeti/AlgebraicTopology/ThricePuncturedSphere/ZeroOneGenerators.lean`), which compares two
loops about a puncture of the thrice-punctured sphere in the same way.

## References

* [A. A. Kosinski, *Differential Manifolds*][Kosinski1993] (the two charts of the sphere).
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Theorem 1.7, Proposition 1.14 and Proposition 1.18 (the fundamental group of the circle, the
  simple connectivity of the sphere `S²`, and the use of the circle for the degree of a loop).
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

/-! ### The loops about the finite punctures

The comparison is made in the chart `sphereChart`, read in `ℂ`, where the circle of the ball
`j = (Fin.castSucc k).rev` is a circle about the real point `j`. The inversion `z ↦ 1 / conj z`
in the unit circle carries the plane minus the points `puncturedSpherePoint n i` to that chart. -/

section Loops

open Metric
open Complex (I)
open EuclideanGeometry (inversion inversion_zero_eq_sq_div_conj)
open EuclideanTorus (neckIsometry)
open PlaneMinusRealPoints (fan approach circle)

private theorem sphereCoChart_repr_inversion {u : ℂ} (hu : u ≠ 0) :
    sphereCoChart (Complex.orthonormalBasisOneI.repr (inversion 0 1 u)) =
      sphereChart (Complex.orthonormalBasisOneI.repr u) := by
  rw [sphereCoChart_of_ne, LinearIsometryEquiv.map_inversion_zero,
    EuclideanGeometry.inversion_inversion _ one_ne_zero]
  rw [LinearIsometryEquiv.map_inversion_zero]
  simpa [EuclideanGeometry.inversion_eq_center] using hu

/-- The circle of the ball `j` of the sphere, in the chart `sphereChart`. -/
theorem ballCircle_zero_apply_eq_sphereChart (j : ℕ) (t : unitInterval) :
    ballCircle 0 j t = sphereChart (Complex.orthonormalBasisOneI.repr
      (circleMap (j : ℂ) (√2 / 4) (Real.pi / 4 + 2 * Real.pi * t))) := by
  have hn : ‖neckIsometry (circleMap 0 1 (2 * Real.pi * t))‖ = 1 := by simp
  have h2 : √(1 + (1 : ℝ) ^ 2) = √2 := by norm_num
  have hs : (1 / 2) / √2 = √2 / 4 := by
    have := Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    field_simp
    linarith
  rw [ballCircle_apply, ball_zero_eq_sphereChart, OpenPartialHomeomorph.univBall_apply
    (by norm_num), hn, h2, hs, EuclideanTorus.neckIsometry_circleMap]
  congr 1
  ext i
  fin_cases i
  · simp [circleMap, Complex.exp_re, Complex.exp_im, add_comm (Real.pi / 4)]
    ring
  · simp [circleMap, Complex.exp_re, Complex.exp_im, add_comm (Real.pi / 4)]

/-! ### The punctured fan about a real point of the chart `sphereChart`

For real points `c i`, any two at least `1` apart, both loops are compared in the punctured fan
`PlaneMinusRealPoints.fan c 1 k \ {c k}`: the lower half-plane together with the strip of
half-width `1 / 2` about `c k`, punctured at `c k`. -/

variable {ι : Type*} {c : ι → ℝ} {k : ι} {r : ℝ}

/-- For `1 ≤ c k`, the point `0` is not in the fan about `c k`. -/
private theorem zero_notMem_fan (ha : 1 ≤ c k) : (0 : ℂ) ∉ fan c 1 k := by
  rw [PlaneMinusRealPoints.mem_fan_iff]
  rintro (h | h)
  · simp at h
  · rw [Complex.zero_re, zero_sub, abs_neg, abs_of_pos (by linarith)] at h
    linarith

/-- A point near `(c k)⁻¹` is sent by the inversion into the punctured fan about `c k`. -/
private theorem inversion_mem_fan_diff (ha : 1 ≤ c k) (hr : 0 < r) (har : c k ^ 2 * r ≤ 1 / 4)
    {w : ℂ} (hw : ‖w - ((c k)⁻¹ : ℝ)‖ ≤ r) (hw0 : w ≠ ((c k)⁻¹ : ℝ)) :
    inversion 0 1 w ∈ fan c 1 k \ {(c k : ℂ)} := by
  set a := c k
  have ha0 : 0 < a := by linarith
  have hwn : a⁻¹ - r ≤ ‖w‖ := by
    have := norm_sub_norm_le (((a⁻¹ : ℝ)) : ℂ) (w)
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity), norm_sub_rev] at this
    linarith
  have hra : r * a ≤ 1 / 4 := by nlinarith
  have hpos : 0 < a⁻¹ - r := by
    have : a⁻¹ * a = 1 := inv_mul_cancel₀ ha0.ne'
    nlinarith
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha0.ne'
  have hw' : w ≠ 0 := by
    intro h
    rw [h, norm_zero] at hwn
    linarith
  refine ⟨PlaneMinusRealPoints.ball_subset_fan k ?_, fun h ↦ hw0 ?_⟩
  · rw [mem_ball, dist_eq_norm, EuclideanGeometry.norm_inversion_zero_sub_ofReal,
      Complex.ofReal_one, one_pow, one_div,
      show w⁻¹ - a = a * ((a⁻¹ : ℝ) - w) / w by
        push_cast
        field_simp,
      norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg ha0.le, norm_sub_rev,
      div_lt_iff₀ (norm_pos_iff.2 hw')]
    have : a * a⁻¹ = 1 := mul_inv_cancel₀ ha0.ne'
    nlinarith [norm_nonneg (w - (a⁻¹ : ℝ))]
  · have := congrArg (inversion 0 1) (mem_singleton_iff.1 h)
    rw [EuclideanGeometry.inversion_inversion _ one_ne_zero] at this
    simpa using this

/-- The start of the circle of radius `√2 / 4` about `a` at the angle `π / 4`. -/
private theorem circleMap_pi_div_four (a : ℝ) :
    circleMap (a : ℂ) (√2 / 4) (Real.pi / 4) = ((a + 1 / 4 : ℝ) : ℂ) + ((1 / 4 : ℝ) : ℂ) * I := by
  have hs : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  apply Complex.ext <;>
    simp [circleMap, Complex.exp_re, Complex.exp_im, Real.cos_pi_div_four,
      Real.sin_pi_div_four] <;> nlinarith

/-- The path in the chart `sphereChart` from `-i` to the start of the circle about `a`: right to
`a + 1 / 4 - i`, then up. -/
private def chartApproach (a : ℝ) : Path (-I) (circleMap (a : ℂ) (√2 / 4) (Real.pi / 4)) :=
  (Path.segment (-I) (((a + 1 / 4 : ℝ) : ℂ) - I)).trans
    (Path.segment (((a + 1 / 4 : ℝ) : ℂ) - I) (circleMap (a : ℂ) (√2 / 4) (Real.pi / 4)))

private theorem range_chartApproach_subset :
    range (chartApproach (c k)) ⊆ fan c 1 k \ {(c k : ℂ)} := by
  rw [chartApproach, Path.trans_range, union_subset_iff, range_subset_iff, range_subset_iff]
  refine ⟨fun s ↦ PlaneMinusRealPoints.mem_fan_diff_of_im_neg k ?_, fun s ↦ ?_⟩
  · simp [Path.segment_apply, AffineMap.lineMap_apply_module]
  set a := c k
  rw [Path.segment_apply, circleMap_pi_div_four, AffineMap.lineMap_apply_module]
  have hs0 := s.prop.1
  have hs1 := s.prop.2
  set z := (1 - (s : ℝ)) • (((a + 1 / 4 : ℝ) : ℂ) - I) +
    (s : ℝ) • (((a + 1 / 4 : ℝ) : ℂ) + ((1 / 4 : ℝ) : ℂ) * I) with hz
  have hre : z.re = a + 1 / 4 := by simp [hz]; ring
  have him : z.im = -1 + 5 / 4 * s := by simp [hz]; ring
  rcases lt_or_ge z.im 0 with h | h
  · exact PlaneMinusRealPoints.mem_fan_diff_of_im_neg k h
  -- Above the real axis, the vertical segment stays in the disc of radius `1 / 2` about `a`.
  refine ⟨PlaneMinusRealPoints.ball_subset_fan k ?_, fun h' ↦ by
    simp [mem_singleton_iff.1 h'] at hre⟩
  rw [mem_ball, dist_eq_norm]
  have hsq : ‖z - a‖ ^ 2 < (1 / 2) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, hre,
      him, sub_zero]
    nlinarith
  exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) hsq

private theorem circlePath_mem (t : unitInterval) :
    circlePath (c k : ℂ) (√2 / 4) (Real.pi / 4) t ∈ fan c 1 k \ {(c k : ℂ)} := by
  have h2 : √2 < 2 := by
    rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have h0 : 0 < √2 := by positivity
  refine ⟨PlaneMinusRealPoints.ball_subset_fan k ?_, fun h ↦ ?_⟩
  · rw [circlePath_apply, mem_ball, dist_eq_norm, circleMap_sub_center, norm_circleMap_zero,
      abs_of_pos (by positivity)]
    linarith
  · have := congrArg (fun z : ℂ ↦ ‖z - c k‖) (Set.eq_of_mem_singleton h)
    simp only [circlePath_apply, circleMap_sub_center, norm_circleMap_zero, sub_self,
      norm_zero] at this
    rw [abs_of_pos (by positivity)] at this
    linarith

private theorem approach_ne_zero {x r : ℝ} (hxr : 0 < x + r) (t : unitInterval) :
    approach x r t ≠ 0 := by
  rw [PlaneMinusRealPoints.approach_def, Path.trans_apply]
  split_ifs
  · intro h
    have := congrArg Complex.im h
    simp [Path.segment_apply, AffineMap.lineMap_apply_module] at this
    linarith
  · intro h
    have := congrArg Complex.re h
    simp [Path.segment_apply, AffineMap.lineMap_apply_module] at this
    linarith

private theorem inversion_approach_mem (ha : 1 ≤ c k) (hr : 0 < r) (har : c k ^ 2 * r ≤ 1 / 4)
    (t : unitInterval) : inversion 0 1 (approach (c k)⁻¹ r t) ∈ fan c 1 k \ {(c k : ℂ)} := by
  rw [PlaneMinusRealPoints.approach_def, Path.trans_apply]
  split_ifs
  · refine PlaneMinusRealPoints.mem_fan_diff_of_im_neg k
      (EuclideanGeometry.inversion_zero_im_neg one_ne_zero ?_)
    simp [Path.segment_apply, AffineMap.lineMap_apply_module]
  · set z := Path.segment ((((c k)⁻¹ + r : ℝ) : ℂ) - I) (((c k)⁻¹ + r : ℝ) : ℂ) ⟨2 * t - 1, _⟩
    have hre : z.re = (c k)⁻¹ + r := by
      simp [z, Path.segment_apply, AffineMap.lineMap_apply_module]; ring
    have him : z.im ≤ 0 := by
      simp [z, Path.segment_apply, AffineMap.lineMap_apply_module]
      linarith [t.prop.2]
    rcases him.lt_or_eq with h | h
    · exact PlaneMinusRealPoints.mem_fan_diff_of_im_neg k
        (EuclideanGeometry.inversion_zero_im_neg one_ne_zero h)
    · have hz : z = (((c k)⁻¹ + r : ℝ) : ℂ) := Complex.ext (by simp [hre]) (by simp [h])
      rw [hz]
      refine inversion_mem_fan_diff ha hr har (by simp [abs_of_pos hr]) ?_
      intro h'
      have := congrArg Complex.re h'
      simp at this
      linarith

private theorem circle_mem (ha : 1 ≤ c k) (hr : 0 < r) (har : c k ^ 2 * r ≤ 1 / 4)
    (t : unitInterval) :
    inversion 0 1 (circle (c k)⁻¹ r t) ∈ fan c 1 k \ {(c k : ℂ)} := by
  rw [PlaneMinusRealPoints.circle_apply]
  refine inversion_mem_fan_diff ha hr har ?_ ?_
  · rw [circleMap_sub_center, norm_circleMap_zero, abs_of_pos hr]
  · intro h
    have := congrArg (fun z : ℂ ↦ ‖z - ((c k)⁻¹ : ℝ)‖) h
    simp only [circleMap_sub_center, norm_circleMap_zero, sub_self, norm_zero,
      abs_of_pos hr] at this
    linarith

private theorem circle_ne_zero (ha : 1 ≤ c k) (hr : 0 < r) (har : c k ^ 2 * r ≤ 1 / 4)
    (t : unitInterval) :
    circle (c k)⁻¹ r t ≠ 0 := by
  intro h
  have := (circle_mem ha hr har t).1
  rw [h, EuclideanGeometry.inversion_self] at this
  exact zero_notMem_fan ha this

/-! ### The comparison in the punctured fan -/

section Compare

variable (ha : 1 ≤ c k) (hr : 0 < r) (har : c k ^ 2 * r ≤ 1 / 4)

variable (c k) in
/-- The point `-i` of the punctured fan. -/
private def nNegI : ↥(fan c 1 k \ {(c k : ℂ)}) := ⟨-I, PlaneMinusRealPoints.negI_mem_fan k⟩

@[simp] private theorem coe_nNegI : (nNegI c k : ℂ) = -I := (rfl)

variable (c k) in
/-- The start of the circle about `c k`, in the punctured fan. -/
private def nStart : ↥(fan c 1 k \ {(c k : ℂ)}) :=
  ⟨circleMap (c k : ℂ) (√2 / 4) (Real.pi / 4), by simpa [circlePath_apply] using circlePath_mem 0⟩

include ha hr har in
private theorem inversion_add_mem :
    inversion 0 1 ((((c k)⁻¹ + r : ℝ)) : ℂ) ∈ fan c 1 k \ {(c k : ℂ)} := by
  refine inversion_mem_fan_diff ha hr har (by simp [abs_of_pos hr]) ?_
  intro h'
  have := congrArg Complex.re h'
  simp at this
  linarith

/-- The image under the inversion of the start of the circle `circle (c k)⁻¹ r`. -/
private def nInvStart : ↥(fan c 1 k \ {(c k : ℂ)}) := ⟨_, inversion_add_mem ha hr har⟩

variable (c k) in
/-- `chartApproach` in the punctured fan. -/
private def nApproach : Path (nNegI c k) (nStart c k) :=
  (chartApproach (c k)).codRestrict (x := nNegI c k) (y := nStart c k)
    fun t ↦ range_chartApproach_subset (mem_range_self t)

variable (c k) in
/-- The circle about `c k` in the punctured fan. -/
private def nCircle : Path (nStart c k) (nStart c k) :=
  (circlePath (c k : ℂ) (√2 / 4) (Real.pi / 4)).codRestrict (x := nStart c k) (y := nStart c k)
    circlePath_mem

include ha hr in
private theorem approach_add_pos : 0 < (c k)⁻¹ + r := by
  have : 0 < (c k)⁻¹ := inv_pos.2 (by linarith)
  linarith

/-- The inverted approach path in the punctured fan. -/
private def nInvApproach : Path (nNegI c k) (nInvStart ha hr har) :=
  -- The point of `γ.map' h` at `t` is `inversion 0 1 (γ t)` by definition (`Path.map'_coe`); the
  -- end points given to `codRestrict` keep `rw` from stating that, so the membership is closed
  -- up to that definition.
  (((approach (c k)⁻¹ r).map' (continuousOn_const.inversion continuousOn_const continuousOn_id
    (by rintro _ ⟨t, rfl⟩; exact approach_ne_zero (approach_add_pos ha hr) t))).codRestrict
    (x := ⟨inversion 0 1 (-I), by
      rw [show inversion (0 : ℂ) 1 (-I) = -I by simp [inversion_zero_eq_sq_div_conj]]
      exact PlaneMinusRealPoints.negI_mem_fan k⟩)
    (y := nInvStart ha hr har)
    fun t ↦ inversion_approach_mem ha hr har t).cast
    (Subtype.ext (by simp [inversion_zero_eq_sq_div_conj])) rfl

/-- The inverted circle in the punctured fan. -/
private def nInvCircle : Path (nInvStart ha hr har) (nInvStart ha hr har) :=
  -- As in `nInvApproach`, the membership is closed up to the definition of `Path.map'`.
  ((circle (c k)⁻¹ r).map' (continuousOn_const.inversion continuousOn_const continuousOn_id
    (by rintro _ ⟨t, rfl⟩; exact circle_ne_zero ha hr har t))).codRestrict
    (x := nInvStart ha hr har) (y := nInvStart ha hr har)
    fun t ↦ circle_mem ha hr har t

@[simp] private theorem coe_nApproach_apply (t : unitInterval) :
    (nApproach c k t : ℂ) = chartApproach (c k) t :=
  Path.codRestrict_coe _ _ t

@[simp] private theorem coe_nCircle_apply (t : unitInterval) :
    (nCircle c k t : ℂ) = circlePath (c k : ℂ) (√2 / 4) (Real.pi / 4) t :=
  Path.codRestrict_coe _ _ t

@[simp] private theorem coe_nInvApproach_apply (t : unitInterval) :
    (nInvApproach ha hr har t : ℂ) = inversion 0 1 (approach (c k)⁻¹ r t) := by
  rw [nInvApproach, Path.cast_coe]
  exact (Path.codRestrict_coe _ _ t).trans (congrFun (Path.map'_coe _ _) t)

@[simp] private theorem coe_nInvCircle_apply (t : unitInterval) :
    (nInvCircle ha hr har t : ℂ) = inversion 0 1 (circle (c k)⁻¹ r t) := by
  exact (Path.codRestrict_coe _ _ t).trans (congrFun (Path.map'_coe _ _) t)

private theorem degree_nCircle :
    Circle.degree ((nCircle c k).map (Complex.directionFrom (c k : ℂ) (fan c 1 k)).continuous) =
      1 := by
  have hρ : 0 < √2 / 4 := by positivity
  refine Circle.degree_eq_of_sub_eq _ (θ := fun t ↦ Real.pi / 4 + 2 * Real.pi * t)
    (by fun_prop) (fun t ↦ ?_) (by simp)
  apply Subtype.ext
  rw [Circle.coe_exp, Path.map_coe, Function.comp_apply, Complex.coe_directionFrom_apply]
  rw [coe_nCircle_apply]
  simp only [circlePath_apply, circleMap_sub_center,
    circleMap_zero, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_of_nonneg hρ.le]
  rw [mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.2 hρ.ne')]

/-- The loop `t ↦ e^{i(π - 2πt)}` of the circle. -/
private def negExpLoop : Path (Circle.exp Real.pi) (Circle.exp Real.pi) where
  toFun t := Circle.exp (Real.pi - 2 * Real.pi * t)
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by
    simp only [Set.Icc.coe_one, mul_one]
    rw [show Real.pi - 2 * Real.pi = Real.pi + (-1 : ℤ) * (2 * Real.pi) by ring,
      Circle.exp_add, Circle.exp_int_mul_two_pi, mul_one]

private theorem degree_negExpLoop : Circle.degree negExpLoop = -1 :=
  Circle.degree_eq_of_sub_eq _ (θ := fun t ↦ Real.pi - 2 * Real.pi * t) (by fun_prop)
    (fun _ ↦ rfl) (by simp)

/-- The conjugate of the point of angle `2πt` on the circle `circle x r` is the point of angle
`-2πt` on the circle of radius `r` about `x`. -/
private theorem conj_circle_apply (x r : ℝ) (t : unitInterval) :
    starRingEnd ℂ (circle x r t) = (x : ℂ) + r * Complex.exp (-(2 * Real.pi * t : ℝ) * I) := by
  simp only [PlaneMinusRealPoints.circle_apply, circleMap, map_add, map_mul, Complex.conj_ofReal,
    ← Complex.exp_conj, Complex.conj_I]
  congr 2
  push_cast
  ring_nf

/-- The inverted circle about `a⁻¹` differs from the clockwise circle `a - a ^ 2 r e^{-2πit}`
about `a` by `a ^ 2 r ^ 2 e^{-4πit} / (a⁻¹ + r e^{-2πit})`, where `E = e^{-2πit}`. -/
private theorem inversion_circle_sub_eq {a r : ℝ} (ha : a ≠ 0) {E : ℂ}
    (hw0 : ((a⁻¹ : ℝ) : ℂ) + r * E ≠ 0) :
    (((a⁻¹ : ℝ) : ℂ) + r * E)⁻¹ - a - -((a ^ 2 * r : ℝ) : ℂ) * E =
      (a ^ 2 * r ^ 2 : ℝ) * E ^ 2 / (((a⁻¹ : ℝ) : ℂ) + r * E) := by
  rw [eq_div_iff hw0]
  have hD := inv_mul_cancel₀ hw0
  have hai : (a : ℂ) * ((a⁻¹ : ℝ) : ℂ) = 1 := by
    push_cast
    exact mul_inv_cancel₀ (by exact_mod_cast ha)
  push_cast at hD hai ⊢
  linear_combination hD - (1 - (a : ℂ) * r * E) * hai

include ha hr har in
private theorem degree_nInvCircle :
    Circle.degree ((nInvCircle ha hr har).map
      (Complex.directionFrom (c k : ℂ) (fan c 1 k)).continuous) = -1 := by
  set a := c k
  have ha0 : 0 < a := by linarith
  have hra : r * a ≤ 1 / 4 := by nlinarith
  have hpos : 2 * r < a⁻¹ := by
    have : a⁻¹ * a = 1 := inv_mul_cancel₀ ha0.ne'
    nlinarith
  -- Compare the direction of the inverted circle with the clockwise loop `t ↦ -e^{-2πit}`, by
  -- Tau Ceti's dog-on-a-leash lemma: the inverted circle is `a - a ^ 2 r e^{-2πit}` up to an
  -- error smaller than `a ^ 2 r`.
  rw [← degree_negExpLoop]
  set E : unitInterval → ℂ := fun t ↦ Complex.exp (-(2 * Real.pi * t : ℝ) * I) with hE
  have hEn (t : unitInterval) : ‖E t‖ = 1 := by
    simp only [hE, ← Complex.ofReal_neg]
    exact Complex.norm_exp_ofReal_mul_I _
  refine Circle.degree_eq_of_norm_sub_lt _ _
    (z := fun t ↦ inversion 0 1 (circle a⁻¹ r t) - a)
    (w := fun t ↦ -((a ^ 2 * r : ℝ) : ℂ) * E t) (fun t ↦ ?_) (fun t ↦ ?_) (fun t ↦ ?_)
  · simp [Path.map_coe, a]
  · -- The comparison loop is `a ^ 2 r` times `t ↦ -e^{-2πit}`.
    have hn : ‖-((a ^ 2 * r : ℝ) : ℂ) * E t‖ = a ^ 2 * r := by
      rw [norm_mul, hEn, mul_one, norm_neg, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rw [hn]
    simp only [negExpLoop, Path.coe_mk_mk, Circle.coe_exp, hE]
    rw [show ((Real.pi - 2 * Real.pi * t : ℝ) : ℂ) * I =
        Real.pi * I + (-(2 * Real.pi * t : ℝ)) * I by push_cast; ring,
      Complex.exp_add, Complex.exp_pi_mul_I]
    have : ((a ^ 2 * r : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (by positivity : (0 : ℝ) < a ^ 2 * r).ne'
    field_simp
  · -- The error: `|a⁻¹ + r E| ≥ a⁻¹ - r > r`, so its norm is less than `a ^ 2 r`.
    have hw : ‖((a⁻¹ : ℝ) : ℂ) + r * E t‖ ≥ a⁻¹ - r := by
      have := norm_sub_norm_le (((a⁻¹ : ℝ)) : ℂ) (-(r * E t))
      rw [sub_neg_eq_add, Complex.norm_real, Real.norm_of_nonneg (by positivity), norm_neg,
        norm_mul, hEn, mul_one, Complex.norm_real, Real.norm_of_nonneg hr.le] at this
      linarith
    have hw0 : ((a⁻¹ : ℝ) : ℂ) + r * E t ≠ 0 := by
      intro h
      rw [h, norm_zero] at hw
      linarith
    rw [inversion_zero_eq_sq_div_conj, Complex.ofReal_one, one_pow, one_div, conj_circle_apply,
      inversion_circle_sub_eq ha0.ne' hw0, norm_div, norm_mul, norm_pow, hEn, one_pow, mul_one,
      Complex.norm_real, Real.norm_of_nonneg (by positivity), norm_mul, hEn, mul_one, norm_neg,
      Complex.norm_real, Real.norm_of_nonneg (by positivity), div_lt_iff₀ (by linarith)]
    have : 0 < a ^ 2 * r := by positivity
    nlinarith

include ha hr har in
/-- In the punctured fan about `c k`, the inverted loop about `(c k)⁻¹` is homotopic to the
reversed circle about `c k`, both reached from `-i`. -/
private theorem nInvApproach_homotopic :
    ((nInvApproach ha hr har).trans
        ((nInvCircle ha hr har).trans (nInvApproach ha hr har).symm)).Homotopic
      ((nApproach c k).trans ((nCircle c k).symm.trans (nApproach c k).symm)) := by
  have hd := ((PlaneMinusRealPoints.starConvex_fan one_pos k
    ).fundamentalGroup_map_directionFrom_bijective
    (r := 1 / 4) (by norm_num) (PlaneMinusRealPoints.sphere_subset_fan one_pos k)
    (nInvStart ha hr har)).injective
  have h := Circle.homotopic_trans_of_degree_map_eq hd (γ := nInvCircle ha hr har)
    (δ := (nCircle c k).symm) (by
      rw [degree_nInvCircle ha hr har, ← Path.map_symm, Circle.degree_symm, degree_nCircle])
    ((nInvApproach ha hr har).symm.trans (nApproach c k))
  have h' := Path.Homotopic.Quotient.eq.2 h
  refine Path.Homotopic.Quotient.exact ?_
  rw [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_trans, h']
  simp only [Path.trans_symm, Path.symm_symm, Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.mk_symm, Path.Homotopic.Quotient.trans_assoc,
    Path.Homotopic.Quotient.trans_symm_trans, Path.Homotopic.Quotient.trans_symm,
    Path.Homotopic.Quotient.trans_refl]

end Compare

/-! ### The comparison for the punctured sphere -/

section Small

variable {n : ℕ} (k : Fin n)

variable (n) in
/-- The centre of the ball `(Fin.castSucc k).rev` of the sphere in the chart `sphereChart`: the
real point `(Fin.castSucc k).rev`. -/
private def ballCentre (k : Fin n) : ℝ := ((Fin.castSucc k).rev : ℕ)

private theorem inv_ballCentre : (ballCentre n k)⁻¹ = puncturedSpherePoint n k := by
  rw [ballCentre, puncturedSpherePoint_def]

private theorem one_le_ballCentre : 1 ≤ ballCentre n k := by
  have : 1 ≤ ((Fin.castSucc k).rev : ℕ) := by rw [Fin.val_rev, Fin.val_castSucc]; omega
  rw [ballCentre]
  exact_mod_cast this

private theorem ballCentre_sq_mul_le :
    ballCentre n k ^ 2 * (1 / ((n : ℝ) + 1) ^ 2 / 4) ≤ 1 / 4 := by
  have h1 : ballCentre n k ≤ n := by
    have : ((Fin.castSucc k).rev : ℕ) ≤ n := by rw [Fin.val_rev, Fin.val_castSucc]; omega
    rw [ballCentre]
    exact_mod_cast this
  have h0 : 0 ≤ ballCentre n k := by linarith [one_le_ballCentre k]
  rw [mul_div_assoc', mul_one_div, div_div, div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

/-- The centres of the balls are distinct naturals, so any two are at least `1` apart. -/
private theorem pairwise_one_le_abs_ballCentre_sub :
    Pairwise fun i j : Fin n ↦ (1 : ℝ) ≤ |ballCentre n i - ballCentre n j| := by
  intro i j hij
  have hne : ((Fin.castSucc i).rev : ℕ) ≠ ((Fin.castSucc j).rev : ℕ) :=
    fun h ↦ hij (Fin.castSucc_injective _ (Fin.rev_injective (Fin.ext h)))
  rw [ballCentre, ballCentre]
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have : (((Fin.castSucc i).rev : ℕ) : ℝ) + 1 ≤ ((Fin.castSucc j).rev : ℕ) := by
      exact_mod_cast h
    rw [abs_sub_comm, abs_of_pos (by linarith)]
    linarith
  · have : (((Fin.castSucc j).rev : ℕ) : ℝ) + 1 ≤ ((Fin.castSucc i).rev : ℕ) := by
      exact_mod_cast h
    rw [abs_of_pos (by linarith)]
    linarith

private theorem inversion_mem_compl_range
    (u : ↥(fan (ballCentre n) 1 k \ {(ballCentre n k : ℂ)})) :
    inversion 0 1 (u : ℂ) ∈ (range fun i ↦ (puncturedSpherePoint n i : ℂ))ᶜ := by
  rintro ⟨i, hi⟩
  simp only at hi
  have hu := congrArg (inversion 0 1) hi
  rw [EuclideanGeometry.inversion_inversion _ one_ne_zero, ← inv_ballCentre,
    EuclideanGeometry.inversion_zero_ofReal] at hu
  have hu' : (u : ℂ) = ballCentre n i := by simpa using hu.symm
  have hV := u.prop.1
  rw [hu'] at hV
  obtain rfl := PlaneMinusRealPoints.eq_of_ofReal_mem_fan one_pos
    pairwise_one_le_abs_ballCentre_sub hV
  exact u.prop.2 (mem_singleton_iff.2 hu')

/-- The inversion, from the punctured fan about the centre of the ball `(Fin.castSucc k).rev` in
the chart `sphereChart` to the plane minus the points. -/
private def inversionToCompl :
    C(↥(fan (ballCentre n) 1 k \ {(ballCentre n k : ℂ)}),
      ↥(range fun i ↦ (puncturedSpherePoint n i : ℂ))ᶜ) where
  toFun u := ⟨inversion 0 1 u, inversion_mem_compl_range k u⟩
  continuous_toFun := (continuous_const.inversion continuous_const continuous_subtypeVal
    fun u h ↦ zero_notMem_fan (one_le_ballCentre k) (by rw [← h]; exact u.prop.1)).subtype_mk _

private theorem coe_inversionToCompl_apply
    (u : ↥(fan (ballCentre n) 1 k \ {(ballCentre n k : ℂ)})) :
    (inversionToCompl k u : ℂ) = inversion 0 1 (u : ℂ) :=
  (rfl)

/-- The segment from `0` to `-i` in the plane minus the points, ending at the image of `-i`
under `inversionToCompl`. -/
private def segmentToNegI : Path (⟨0, zero_mem_compl_range_puncturedSpherePoint⟩ :
      ↥(range fun i ↦ (puncturedSpherePoint n i : ℂ))ᶜ) (inversionToCompl k (nNegI _ _)) :=
  ((Path.segment (0 : ℂ) (-I)).cast rfl
    (by simp [coe_inversionToCompl_apply, inversion_zero_eq_sq_div_conj])).codRestrict
    (PlaneMinusRealPoints.segment_mem_compl_range puncturedSpherePoint_ne_zero)

@[simp] private theorem coe_segmentToNegI_apply (t : unitInterval) :
    (segmentToNegI k t : ℂ) = Path.segment (0 : ℂ) (-I) t :=
  Path.codRestrict_coe _ _ t

private theorem loop_eq_trans :
    PlaneMinusRealPoints.loop (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1) ^ 2)
        one_div_sq_le_abs_puncturedSpherePoint_sub puncturedSpherePoint_ne_zero k =
      (segmentToNegI k).trans ((((nInvApproach (one_le_ballCentre k) (by positivity)
        (ballCentre_sq_mul_le k)).trans ((nInvCircle (one_le_ballCentre k) (by positivity)
        (ballCentre_sq_mul_le k)).trans (nInvApproach (one_le_ballCentre k) (by positivity)
        (ballCentre_sq_mul_le k)).symm)).map (inversionToCompl k).continuous).trans
          (segmentToNegI k).symm) := by
  refine Path.ext (funext fun t ↦ Subtype.ext ?_)
  rw [PlaneMinusRealPoints.coe_loop_apply, PlaneMinusRealPoints.loopInPlane_def, ← inv_ballCentre]
  simp only [Path.trans_apply, Path.symm_apply, Path.map_coe, comp_apply, apply_dite Subtype.val]
  split_ifs <;> simp only [coe_segmentToNegI_apply, coe_nInvApproach_apply, coe_nInvCircle_apply,
    coe_inversionToCompl_apply, EuclideanGeometry.inversion_inversion _ one_ne_zero]

private theorem sphereCoChart_segment_negI (s : unitInterval) :
    sphereCoChart ((Path.segment 0 !₂[0, -1]) s) =
      sphereCoChart (Complex.orthonormalBasisOneI.repr ((Path.segment 0 (-I)) s)) := by
  congr 1
  ext i
  fin_cases i <;> simp [Path.segment_apply, AffineMap.lineMap_apply_module]

private theorem sphereChart_segment_bottom {x : ℝ} {m : ℕ} (hx : x = m + 1) (s : unitInterval) :
    sphereChart ((Path.segment !₂[0, -1] !₂[(m : ℝ) + 5 / 4, -1]) s) =
      sphereCoChart (Complex.orthonormalBasisOneI.repr
        (inversion 0 1 ((Path.segment (-I) (((x + 1 / 4 : ℝ) : ℂ) - I)) s))) := by
  rw [sphereCoChart_repr_inversion]
  · congr 1
    ext i
    fin_cases i
    · simp [Path.segment_apply, AffineMap.lineMap_apply_module, hx]
      ring_nf
      simp
    · simp [Path.segment_apply, AffineMap.lineMap_apply_module, hx]
  · intro h
    have := congrArg Complex.im h
    simp [Path.segment_apply, AffineMap.lineMap_apply_module] at this
    linarith

private theorem sphereChart_segment_up {x : ℝ} {m : ℕ} (hx : x = m + 1) (s : unitInterval) :
    sphereChart ((Path.segment !₂[(m : ℝ) + 5 / 4, -1] !₂[(m : ℝ) + 5 / 4, 1 / 4]) s) =
      sphereCoChart (Complex.orthonormalBasisOneI.repr (inversion 0 1
        ((Path.segment (((x + 1 / 4 : ℝ) : ℂ) - I)
          (circleMap (x : ℂ) (√2 / 4) (Real.pi / 4))) s))) := by
  rw [sphereCoChart_repr_inversion, circleMap_pi_div_four]
  · congr 1
    ext i
    fin_cases i
    · simp [Path.segment_apply, AffineMap.lineMap_apply_module, hx]
      ring
    · simp [Path.segment_apply, AffineMap.lineMap_apply_module, hx]
  · rw [circleMap_pi_div_four]
    intro h
    have := congrArg Complex.re h
    simp [Path.segment_apply, AffineMap.lineMap_apply_module] at this
    have : (0 : ℝ) ≤ m := m.cast_nonneg
    nlinarith

private theorem ballCircle_eq_sphereCoChart {m : ℕ} (hx : ballCentre n k = m + 1)
    (s : unitInterval) :
    ballCircle 0 (m + 1) s = sphereCoChart (Complex.orthonormalBasisOneI.repr
      (inversion 0 1 ((circlePath (ballCentre n k : ℂ) (√2 / 4) (Real.pi / 4)) s))) := by
  rw [sphereCoChart_repr_inversion, ballCircle_zero_apply_eq_sphereChart, circlePath_apply,
    hx]
  · simp
  · exact fun h ↦ zero_notMem_fan (one_le_ballCentre k) (h ▸ (circlePath_mem s).1)

private theorem peripheralLoop_eq_trans :
    ((peripheralLoop 0 (n + 1) (Fin.castSucc k)).map
        (puncturedSphereHomeomorph n).symm.continuous).cast
        puncturedSphereHomeomorph_symm_basePoint.symm
        puncturedSphereHomeomorph_symm_basePoint.symm =
      (((segmentToNegI k).trans ((nApproach (ballCentre n) k).map
        (inversionToCompl k).continuous)).trans
        ((nCircle (ballCentre n) k).symm.map
          (inversionToCompl k).continuous)).trans
        ((segmentToNegI k).trans ((nApproach (ballCentre n) k).map
          (inversionToCompl k).continuous)).symm := by
  refine Path.ext (funext fun t ↦ ?_)
  rw [Path.cast_coe, Path.map_coe, comp_apply, Homeomorph.symm_apply_eq]
  apply Subtype.ext
  rw [coe_peripheralLoop_apply, coe_puncturedSphereHomeomorph_apply, ballLoop_def]
  obtain ⟨m, hm⟩ : ∃ m, ((Fin.castSucc k).rev : ℕ) = m + 1 :=
    ⟨n - 1 - k, by rw [Fin.val_rev, Fin.val_castSucc]; omega⟩
  have ha : ballCentre n k = (m : ℝ) + 1 := by rw [ballCentre, hm]; push_cast; ring
  conv_lhs => rw [hm, ballPath_zero_succ]
  simp only [Path.trans_apply, Path.symm_apply, Path.map_coe, Path.cast_coe, comp_apply,
    apply_dite Subtype.val, coe_segmentToNegI_apply, coe_nApproach_apply, coe_nCircle_apply,
    coe_inversionToCompl_apply, chartApproach, apply_dite (inversion (0 : ℂ) 1),
    apply_dite Complex.orthonormalBasisOneI.repr, apply_dite sphereCoChart]
  split_ifs
  · exact sphereCoChart_segment_negI _
  · exact sphereChart_segment_bottom ha _
  · exact sphereChart_segment_up ha _
  · exact ballCircle_eq_sphereCoChart k ha _
  · exact sphereCoChart_segment_negI _
  · exact sphereChart_segment_bottom ha _
  · exact sphereChart_segment_up ha _

/-- **The loops about the finite punctures.** For `k : Fin n`, the peripheral loop
`peripheralLoop 0 (n + 1) (Fin.castSucc k)` of the punctured sphere, about the centre of the ball
`(Fin.castSucc k).rev`, carried to the plane minus the points `puncturedSpherePoint n i` by the
inverse of `puncturedSphereHomeomorph n`, is homotopic to the loop
`PlaneMinusRealPoints.loop` about the point `puncturedSpherePoint n k`, for `δ = 1 / (n + 1) ^ 2`.
So the two have the same class in the fundamental group at `0`. -/
theorem map_peripheralLoop_castSucc_homotopic_loop :
    (((peripheralLoop 0 (n + 1) (Fin.castSucc k)).map
        (puncturedSphereHomeomorph n).symm.continuous).cast
        puncturedSphereHomeomorph_symm_basePoint.symm
        puncturedSphereHomeomorph_symm_basePoint.symm).Homotopic
      (PlaneMinusRealPoints.loop (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1) ^ 2)
        one_div_sq_le_abs_puncturedSpherePoint_sub puncturedSpherePoint_ne_zero k) := by
  rw [peripheralLoop_eq_trans, loop_eq_trans]
  have H := (nInvApproach_homotopic (one_le_ballCentre k) (by positivity)
    (ballCentre_sq_mul_le k)).map (inversionToCompl k)
  refine Path.Homotopic.Quotient.exact ?_
  rw [Path.Homotopic.Quotient.mk_trans (segmentToNegI k), Path.Homotopic.Quotient.mk_trans _
    (segmentToNegI k).symm, Path.Homotopic.Quotient.eq.2 H]
  simp only [Path.map_trans, ← Path.map_symm, Path.trans_symm,
    Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
    Path.Homotopic.Quotient.trans_assoc]

end Small

end Loops

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

/-! ### The fundamental group of the punctured sphere -/

section FundamentalGroup

open TauCeti

variable (n) in
/-- The **fundamental group of the punctured sphere**: the fundamental group of the sphere
punctured at the centres of the balls `0, …, n`, at the base point, is Tau Ceti's orientable
surface group `TauCeti.SurfaceGroup.Orientable 0 (n + 1)`. It is the composite of the map of
fundamental groups along the inverse of `puncturedSphereHomeomorph n`, of the identification
`PlaneMinusRealPoints.fundamentalGroupMulEquiv` of the plane minus the points
`puncturedSpherePoint n k` with the free group on `Fin n`, and of the inverse of Tau Ceti's free
basis `TauCeti.SurfaceGroup.Orientable.genusZeroBasis n`, whose element `k` is the peripheral
element `Fin.castSucc k`. -/
def puncturedSphereFundamentalGroupMulEquiv :
    FundamentalGroup (puncture 0 (n + 1)) ⟨basePoint 0, basePoint_mem_puncture⟩ ≃*
      SurfaceGroup.Orientable 0 (n + 1) :=
  (FundamentalGroup.homeomorphMulEquivOfEq (puncturedSphereHomeomorph n).symm
      puncturedSphereHomeomorph_symm_basePoint).trans <|
    (PlaneMinusRealPoints.fundamentalGroupMulEquiv (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1) ^ 2)
      one_div_sq_le_abs_puncturedSpherePoint_sub puncturedSpherePoint_ne_zero).trans
        (SurfaceGroup.Orientable.genusZeroBasis n).repr.symm

/-- The image of the class of a loop of the punctured sphere under the isomorphism with the surface
group, read off from the class of that loop carried to the plane minus the points. -/
private theorem puncturedSphereFundamentalGroupMulEquiv_fromPath (γ : Path
      (⟨basePoint 0, basePoint_mem_puncture⟩ : puncture 0 (n + 1))
      ⟨basePoint 0, basePoint_mem_puncture⟩) :
    puncturedSphereFundamentalGroupMulEquiv n (FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk γ)) =
      (SurfaceGroup.Orientable.genusZeroBasis n).repr.symm
        (PlaneMinusRealPoints.fundamentalGroupMulEquiv (by positivity)
          one_div_sq_le_abs_puncturedSpherePoint_sub puncturedSpherePoint_ne_zero
          (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
            ((γ.map (puncturedSphereHomeomorph n).symm.continuous).cast
              puncturedSphereHomeomorph_symm_basePoint.symm
              puncturedSphereHomeomorph_symm_basePoint.symm)))) := by
  rw [puncturedSphereFundamentalGroupMulEquiv, MulEquiv.trans_apply, MulEquiv.trans_apply,
    FundamentalGroup.homeomorphMulEquivOfEq_apply, FundamentalGroup.mapOfEq_fromPath_mk]

/-- The isomorphism sends the class of the peripheral loop `Fin.castSucc k`, about the ball
`(Fin.castSucc k).rev`, to the peripheral element `Fin.castSucc k`. -/
private theorem puncturedSphereFundamentalGroupMulEquiv_peripheralLoop_castSucc (k : Fin n) :
    puncturedSphereFundamentalGroupMulEquiv n (FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (peripheralLoop 0 (n + 1) (Fin.castSucc k)))) =
      SurfaceGroup.Orientable.peripheral 0 (n + 1) (Fin.castSucc k) := by
  rw [puncturedSphereFundamentalGroupMulEquiv_fromPath,
    Path.Homotopic.Quotient.eq.2 (map_peripheralLoop_castSucc_homotopic_loop k),
    PlaneMinusRealPoints.fundamentalGroupMulEquiv_loop, FreeGroupBasis.repr_symm_apply_of,
    SurfaceGroup.Orientable.genusZeroBasis_apply]

/-- The isomorphism sends the class of the last peripheral loop, about the ball `0`, to the last
peripheral element. -/
private theorem puncturedSphereFundamentalGroupMulEquiv_peripheralLoop_last :
    puncturedSphereFundamentalGroupMulEquiv n (FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (peripheralLoop 0 (n + 1) (Fin.last n)))) =
      SurfaceGroup.Orientable.peripheral 0 (n + 1) (Fin.last n) := by
  rw [puncturedSphereFundamentalGroupMulEquiv_fromPath,
    fromPath_map_peripheralLoop_last_eq_inv_prod, map_inv, map_list_prod, List.map_ofFn,
    map_inv, map_list_prod, List.map_ofFn, SurfaceGroup.Orientable.peripheral_last]
  simp [Function.comp_def]

/-- The isomorphism sends the class of each peripheral loop to the peripheral element of the same
index. -/
@[simp]
theorem puncturedSphereFundamentalGroupMulEquiv_peripheralLoop (i : Fin (n + 1)) :
    puncturedSphereFundamentalGroupMulEquiv n (FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (peripheralLoop 0 (n + 1) i))) =
      SurfaceGroup.Orientable.peripheral 0 (n + 1) i := by
  induction i using Fin.lastCases with
  | last => exact puncturedSphereFundamentalGroupMulEquiv_peripheralLoop_last
  | cast k => exact puncturedSphereFundamentalGroupMulEquiv_peripheralLoop_castSucc k

variable (n) in
/-- **The base case of the fundamental groups of the punctured closed surfaces**: for every `n`,
the fundamental group of the sphere punctured at the centres of the balls `0, …, n - 1`, at the
base point, is isomorphic to Tau Ceti's orientable surface group
`TauCeti.SurfaceGroup.Orientable 0 n`, by an isomorphism sending the class of each peripheral loop
`peripheralLoop 0 n i` to the peripheral element `i`. The clauses on the loops
`puncturedCircleLoop 0 n k i` are those of the statement in every genus, and are empty, since
there is no `k : Fin 0`. For `n = 0` both groups are trivial; for `n + 1` the isomorphism is
`puncturedSphereFundamentalGroupMulEquiv n`. -/
theorem exists_puncturedFundamentalGroupMulEquiv_zero :
    ∃ e : FundamentalGroup (puncture 0 n) ⟨basePoint 0, basePoint_mem_puncture⟩ ≃*
        SurfaceGroup.Orientable 0 n,
      (∀ k : Fin 0, e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
          (puncturedCircleLoop 0 n k 0))) = SurfaceGroup.Orientable.a 0 n k) ∧
      (∀ k : Fin 0, e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
          (puncturedCircleLoop 0 n k 1))) = SurfaceGroup.Orientable.b 0 n k) ∧
      ∀ i, e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (peripheralLoop 0 n i))) =
        SurfaceGroup.Orientable.peripheral 0 n i := by
  cases n with
  | zero =>
    have h : (puncture 0 0 : Set (ClosedSurface 0)) = univ := by
      rw [puncture_zero, TopologicalSpace.Opens.coe_top]
    have := ((Homeomorph.setCongr h).trans (Homeomorph.Set.univ _)).toHomotopyEquiv
      |>.simplyConnectedSpace
    let := uniqueOfSubsingleton (1 : FundamentalGroup (puncture 0 0)
      ⟨basePoint 0, basePoint_mem_puncture⟩)
    let := uniqueOfSubsingleton (1 : SurfaceGroup.Orientable 0 0)
    exact ⟨MulEquiv.ofUnique, finZeroElim, finZeroElim, finZeroElim⟩
  | succ n =>
    exact ⟨puncturedSphereFundamentalGroupMulEquiv n, finZeroElim, finZeroElim,
      puncturedSphereFundamentalGroupMulEquiv_peripheralLoop⟩

end FundamentalGroup

end SymplecticGeometry.ClosedSurface

end
