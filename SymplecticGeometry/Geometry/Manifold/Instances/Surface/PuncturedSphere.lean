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
import TauCeti.Geometry.Euclidean.Inversion
import TauCeti.Topology.Circle.Degree
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
* `SymplecticGeometry.ClosedSurface.ballCircle_zero_apply_eq_sphereChart`: in the chart
  `sphereChart`, the circle of the ball `j` is the circle of radius `√2 / 4` about `j • e`, from the
  angle `π / 4`.
* `SymplecticGeometry.ClosedSurface.map_peripheralLoop_castSucc_homotopic_loop`: the peripheral
  loop `Fin.castSucc k`, carried to the plane minus the points, is homotopic to the loop
  `PlaneMinusRealPoints.loop` about `puncturedSpherePoint n k`, for `δ = 1 / (n + 1) ^ 2`.

## Implementation notes

The comparison of the loops about the finite punctures is made in the chart `sphereChart`, read in
`ℂ`, to which the inversion `z ↦ (conj z)⁻¹` in the unit circle carries the plane minus the points.
There the reversed circle of the ball `j = (Fin.castSucc k).rev` is a clockwise circle about the
real point `j`, the path to it runs from `-i` through the lower half-plane, and the loop
`PlaneMinusRealPoints.loop` becomes a small loop about `j` run clockwise, since the inversion
reverses orientation. Both lie in the lower half-plane together with the disc of radius `1 / 2`
about `j`, punctured at `j`, a punctured star-convex set whose direction map from `j` is injective
on fundamental groups (`StarConvex.fundamentalGroup_map_directionFrom_bijective`). Both inner
loops have direction of degree `-1`, the inverted one by Tau Ceti's dog-on-a-leash lemma
`Circle.degree_eq_of_norm_sub_lt`, so Tau Ceti's `Circle.homotopic_trans_of_degree_map_eq` makes
them conjugate along any path. This follows the proof of Tau Ceti's
`TauCeti.ThricePuncturedSphere.transport_δZero_eq_periph0`
(`TauCeti/AlgebraicTopology/ThricePuncturedSphere/ZeroOneGenerators.lean`), which compares two
loops about a puncture of the thrice-punctured sphere in the same way.

## References

* [A. A. Kosinski, *Differential Manifolds*][Kosinski1993] (the two charts of the sphere).
* [A. Hatcher, *Algebraic Topology*][Hatcher2017], Theorem 1.7 and Proposition 1.18 (the
  fundamental group of the circle, and its use for the degree of a loop).
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
open EuclideanGeometry (inversion)
open EuclideanTorus (neckIsometry)

private theorem inversion_eq_inv_conj (z : ℂ) : inversion 0 1 z = (starRingEnd ℂ z)⁻¹ := by
  rw [TauCeti.inversion_eq_conj_reciprocal]
  simp

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


/-! ### A punctured neighbourhood of `a` in the chart `sphereChart` -/

open Complex (I)

/-- The open lower half-plane together with the disc of radius `1 / 2` about `a`. -/
private def nbhdV (a : ℝ) : Set ℂ := {z | z.im < 0} ∪ Metric.ball (a : ℂ) (1 / 2)

private theorem starConvex_nbhdV (a : ℝ) : StarConvex ℝ (a : ℂ) (nbhdV a) := by
  intro z hz s t hs ht hst
  rcases hz with hz | hz
  · rcases ht.eq_or_lt with rfl | ht'
    · right
      rw [add_zero] at hst
      simp [hst]
    · left
      simp only [mem_ofPred_eq, Complex.add_im, Complex.real_smul, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, add_zero, zero_add]
      exact mul_neg_of_pos_of_neg ht' hz
  · right
    exact (convex_ball _ _).starConvex (mem_ball_self (by norm_num)) hz hs ht hst

private theorem sphere_subset_nbhdV (a : ℝ) : sphere (a : ℂ) (1 / 4) ⊆ nbhdV a :=
  fun _ hz ↦ Or.inr (sphere_subset_ball (by norm_num) hz)

private theorem mem_nbhdV_diff_of_im_neg {z : ℂ} (a : ℝ) (hz : z.im < 0) :
    z ∈ nbhdV a \ {(a : ℂ)} :=
  ⟨Or.inl hz, fun h ↦ by simp [mem_singleton_iff.1 h] at hz⟩

private theorem inversion_im_neg {z : ℂ} (hz : z.im < 0) : (inversion 0 1 z).im < 0 := by
  rw [inversion_eq_inv_conj, Complex.inv_im, Complex.conj_im, Complex.normSq_conj, neg_neg]
  exact div_neg_of_neg_of_pos hz (Complex.normSq_pos.2 (by rintro rfl; simp at hz))

private theorem norm_inversion_sub (z : ℂ) (a : ℝ) :
    ‖inversion 0 1 z - a‖ = ‖z⁻¹ - a‖ := by
  rw [inversion_eq_inv_conj, show (starRingEnd ℂ z)⁻¹ - a = starRingEnd ℂ (z⁻¹ - a) by
    simp [map_sub, map_inv₀], Complex.norm_conj]


/-- The image under the inversion in the unit circle of a path that avoids `0`. -/
private def invPath {x y : ℂ} (γ : Path x y) (h : ∀ t, γ t ≠ 0) :
    Path (inversion 0 1 x) (inversion 0 1 y) where
  toFun t := inversion 0 1 (γ t)
  continuous_toFun := continuous_const.inversion continuous_const γ.continuous h
  source' := by simp
  target' := by simp

@[simp] private theorem invPath_apply {x y : ℂ} (γ : Path x y) (h : ∀ t, γ t ≠ 0)
    (t : unitInterval) :
    invPath γ h t = inversion 0 1 (γ t) :=
  rfl

private theorem inversion_neg_I : inversion 0 1 (-I) = -I := by
  rw [inversion_eq_inv_conj]; simp

private theorem inversion_ofReal (x : ℝ) : inversion 0 1 (x : ℂ) = ((x⁻¹ : ℝ) : ℂ) := by
  rw [inversion_eq_inv_conj, Complex.conj_ofReal, Complex.ofReal_inv]

private theorem trans_apply_mem {X : Type*} [TopologicalSpace X] {S : Set X} {x y z : X}
    {p : Path x y} {q : Path y z} (hp : ∀ s, p s ∈ S) (hq : ∀ s, q s ∈ S) (t : unitInterval) :
    p.trans q t ∈ S := by
  rw [Path.trans_apply]
  split_ifs
  · exact hp _
  · exact hq _

variable {a r : ℝ}

/-- A point near `a⁻¹` is sent by the inversion into the punctured neighbourhood of `a`. -/
private theorem inversion_mem_nbhdV_diff (ha : 1 ≤ a) (hr : 0 < r) (har : a ^ 2 * r ≤ 1 / 4) {w : ℂ}
    (hw : ‖w - (a⁻¹ : ℝ)‖ ≤ r) (hw0 : w ≠ (a⁻¹ : ℝ)) : inversion 0 1 w ∈ nbhdV a \ {(a : ℂ)} := by
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
  refine ⟨Or.inr ?_, fun h ↦ hw0 ?_⟩
  · rw [mem_ball, dist_eq_norm, norm_inversion_sub,
      show w⁻¹ - a = a * ((a⁻¹ : ℝ) - w) / w by
        push_cast
        field_simp,
      norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg ha0.le, norm_sub_rev,
      div_lt_iff₀ (norm_pos_iff.2 hw')]
    have : a * a⁻¹ = 1 := mul_inv_cancel₀ ha0.ne'
    nlinarith [norm_nonneg (w - (a⁻¹ : ℝ))]
  · have := congrArg (inversion 0 1) (mem_singleton_iff.1 h)
    rwa [EuclideanGeometry.inversion_inversion _ one_ne_zero, inversion_ofReal] at this

/-- The start of the circle of radius `√2 / 4` about `a` at the angle `π / 4`. -/
private theorem circleMap_pi_div_four (a : ℝ) :
    circleMap (a : ℂ) (√2 / 4) (Real.pi / 4) = ((a + 1 / 4 : ℝ) : ℂ) + ((1 / 4 : ℝ) : ℂ) * I := by
  have hs : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  apply Complex.ext <;>
    simp [circleMap, Complex.exp_re, Complex.exp_im, Real.cos_pi_div_four,
      Real.sin_pi_div_four] <;> nlinarith


variable (a) in
/-- The path in the chart `sphereChart` from `-i` to the start of the circle about `a`: right to
`a + 1 / 4 - i`, then up. -/
private def chartApproach : Path (-I) (circleMap (a : ℂ) (√2 / 4) (Real.pi / 4)) :=
  (Path.segment (-I) (((a + 1 / 4 : ℝ) : ℂ) - I)).trans
    (Path.segment (((a + 1 / 4 : ℝ) : ℂ) - I) (circleMap (a : ℂ) (√2 / 4) (Real.pi / 4)))

private theorem chartApproach_mem (t : unitInterval) : chartApproach a t ∈ nbhdV a \ {(a : ℂ)} := by
  refine trans_apply_mem (fun s ↦ ?_) (fun s ↦ ?_) t
  · refine mem_nbhdV_diff_of_im_neg a ?_
    simp [Path.segment_apply, AffineMap.lineMap_apply_module]
  · rw [Path.segment_apply, circleMap_pi_div_four, AffineMap.lineMap_apply_module]
    have hs0 := s.prop.1
    have hs1 := s.prop.2
    set z := (1 - (s : ℝ)) • (((a + 1 / 4 : ℝ) : ℂ) - I) +
      (s : ℝ) • (((a + 1 / 4 : ℝ) : ℂ) + ((1 / 4 : ℝ) : ℂ) * I) with hz
    have hre : z.re = a + 1 / 4 := by simp [hz]; ring
    have him : z.im = -1 + 5 / 4 * s := by simp [hz]; ring
    rcases lt_or_ge z.im 0 with h | h
    · exact mem_nbhdV_diff_of_im_neg a h
    · refine ⟨Or.inr ?_, fun h' ↦ by simp [mem_singleton_iff.1 h'] at hre⟩
      rw [mem_ball, dist_eq_norm]
      have hsq : ‖z - a‖ ^ 2 < (1 / 2) ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, hre,
          him, sub_zero]
        nlinarith
      exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) hsq

private theorem circlePath_mem (t : unitInterval) :
    circlePath (a : ℂ) (√2 / 4) (Real.pi / 4) t ∈ nbhdV a \ {(a : ℂ)} := by
  have h2 : √2 < 2 := by
    rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have h0 : 0 < √2 := by positivity
  refine ⟨Or.inr ?_, fun h ↦ ?_⟩
  · rw [circlePath_apply, mem_ball, dist_eq_norm, circleMap_sub_center, norm_circleMap_zero,
      abs_of_pos (by positivity)]
    linarith
  · have := congrArg (fun z : ℂ ↦ ‖z - a‖) (Set.eq_of_mem_singleton h)
    simp only [circlePath_apply, circleMap_sub_center, norm_circleMap_zero, sub_self,
      norm_zero] at this
    rw [abs_of_pos (by positivity)] at this
    linarith


open PlaneMinusRealPoints (approach circle)

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

private theorem inversion_approach_mem (ha : 1 ≤ a) (hr : 0 < r) (har : a ^ 2 * r ≤ 1 / 4)
    (t : unitInterval) : inversion 0 1 (approach a⁻¹ r t) ∈ nbhdV a \ {(a : ℂ)} := by
  rw [PlaneMinusRealPoints.approach_def, Path.trans_apply]
  split_ifs
  · refine mem_nbhdV_diff_of_im_neg a (inversion_im_neg ?_)
    simp [Path.segment_apply, AffineMap.lineMap_apply_module]
  · set z := Path.segment (((a⁻¹ + r : ℝ) : ℂ) - I) ((a⁻¹ + r : ℝ) : ℂ) ⟨2 * t - 1, _⟩
    have hre : z.re = a⁻¹ + r := by
      simp [z, Path.segment_apply, AffineMap.lineMap_apply_module]; ring
    have him : z.im ≤ 0 := by
      simp [z, Path.segment_apply, AffineMap.lineMap_apply_module]
      linarith [t.prop.2]
    rcases him.lt_or_eq with h | h
    · exact mem_nbhdV_diff_of_im_neg a (inversion_im_neg h)
    · have hz : z = ((a⁻¹ + r : ℝ) : ℂ) := Complex.ext (by simp [hre]) (by simp [h])
      rw [hz]
      refine inversion_mem_nbhdV_diff ha hr har (by simp [abs_of_pos hr]) ?_
      intro h'
      have := congrArg Complex.re h'
      simp at this
      linarith

private theorem circle_mem (ha : 1 ≤ a) (hr : 0 < r) (har : a ^ 2 * r ≤ 1 / 4) (t : unitInterval) :
    inversion 0 1 (circle a⁻¹ r t) ∈ nbhdV a \ {(a : ℂ)} := by
  rw [PlaneMinusRealPoints.circle_apply]
  refine inversion_mem_nbhdV_diff ha hr har ?_ ?_
  · rw [circleMap_sub_center, norm_circleMap_zero, abs_of_pos hr]
  · intro h
    have := congrArg (fun z : ℂ ↦ ‖z - (a⁻¹ : ℝ)‖) h
    simp only [circleMap_sub_center, norm_circleMap_zero, sub_self, norm_zero,
      abs_of_pos hr] at this
    linarith

private theorem circle_ne_zero (ha : 1 ≤ a) (hr : 0 < r) (har : a ^ 2 * r ≤ 1 / 4)
    (t : unitInterval) :
    circle a⁻¹ r t ≠ 0 := by
  intro h
  have := (circle_mem ha hr har t).1
  rw [h, EuclideanGeometry.inversion_self] at this
  rcases this with h0 | h0
  · simp at h0
  · rw [mem_ball, dist_zero_left, Complex.norm_real, Real.norm_of_nonneg (by linarith)] at h0
    linarith


/-! ### The comparison in the punctured neighbourhood -/

section Compare

variable (ha : 1 ≤ a) (hr : 0 < r) (har : a ^ 2 * r ≤ 1 / 4)

variable (a) in
/-- The point `-i` of the punctured neighbourhood. -/
private def nNegI : ↥(nbhdV a \ {(a : ℂ)}) := ⟨-I, mem_nbhdV_diff_of_im_neg a (by simp)⟩

variable (a) in
/-- The start of the circle about `a`, in the punctured neighbourhood. -/
private def nStart : ↥(nbhdV a \ {(a : ℂ)}) :=
  ⟨circleMap (a : ℂ) (√2 / 4) (Real.pi / 4), by simpa [circlePath_apply] using circlePath_mem 0⟩

include ha hr har in
private theorem inversion_add_mem :
    inversion 0 1 ((a⁻¹ + r : ℝ) : ℂ) ∈ nbhdV a \ {(a : ℂ)} := by
  refine inversion_mem_nbhdV_diff ha hr har (by simp [abs_of_pos hr]) ?_
  intro h'
  have := congrArg Complex.re h'
  simp at this
  linarith

/-- The image under the inversion of the start of the circle `circle a⁻¹ r`. -/
private def nInvStart : ↥(nbhdV a \ {(a : ℂ)}) := ⟨_, inversion_add_mem ha hr har⟩

/-- `chartApproach` in the punctured neighbourhood. -/
private def nApproach : Path (nNegI a) (nStart a) :=
  (chartApproach a).codRestrict (x := nNegI a) (y := nStart a) (chartApproach_mem (a := a))

/-- The circle about `a` in the punctured neighbourhood. -/
private def nCircle : Path (nStart a) (nStart a) :=
  (circlePath (a : ℂ) (√2 / 4) (Real.pi / 4)).codRestrict (x := nStart a) (y := nStart a)
    (circlePath_mem (a := a))

include ha hr in
private theorem approach_add_pos : 0 < a⁻¹ + r := by
  have : 0 < a⁻¹ := inv_pos.2 (by linarith)
  linarith

/-- The inverted approach path in the punctured neighbourhood. -/
private def nInvApproach : Path (nNegI a) (nInvStart ha hr har) :=
  ((invPath (approach a⁻¹ r) (approach_ne_zero (approach_add_pos ha hr))).codRestrict
    (x := ⟨inversion 0 1 (-I), by rw [inversion_neg_I]; exact (nNegI a).property⟩)
    (y := nInvStart ha hr har)
    (inversion_approach_mem ha hr har)).cast (Subtype.ext inversion_neg_I.symm) rfl

/-- The inverted circle in the punctured neighbourhood. -/
private def nInvCircle : Path (nInvStart ha hr har) (nInvStart ha hr har) :=
  (invPath (circle a⁻¹ r) (circle_ne_zero ha hr har)).codRestrict (x := nInvStart ha hr har)
    (y := nInvStart ha hr har) (circle_mem ha hr har)

@[simp] private theorem coe_nApproach_apply (t : unitInterval) :
    (nApproach (a := a) t : ℂ) = chartApproach a t := 
  Path.codRestrict_coe _ _ t

@[simp] private theorem coe_nCircle_apply (t : unitInterval) :
    (nCircle (a := a) t : ℂ) = circlePath (a : ℂ) (√2 / 4) (Real.pi / 4) t := 
  Path.codRestrict_coe _ _ t

@[simp] private theorem coe_nInvApproach_apply (t : unitInterval) :
    (nInvApproach ha hr har t : ℂ) = inversion 0 1 (approach a⁻¹ r t) := by
  rw [nInvApproach, Path.cast_coe]
  exact Path.codRestrict_coe _ _ t

@[simp] private theorem coe_nInvCircle_apply (t : unitInterval) :
    (nInvCircle ha hr har t : ℂ) = inversion 0 1 (circle a⁻¹ r t) := 
  Path.codRestrict_coe _ _ t

private theorem degree_nCircle :
    Circle.degree ((nCircle (a := a)).map (Complex.directionFrom (a : ℂ) (nbhdV a)).continuous) =
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

include ha hr har in
private theorem degree_nInvCircle :
    Circle.degree ((nInvCircle ha hr har).map
      (Complex.directionFrom (a : ℂ) (nbhdV a)).continuous) = -1 := by
  have ha0 : 0 < a := by linarith
  have hra : r * a ≤ 1 / 4 := by nlinarith
  have hpos : 2 * r < a⁻¹ := by
    have : a⁻¹ * a = 1 := inv_mul_cancel₀ ha0.ne'
    nlinarith
  rw [← degree_negExpLoop]
  set E : unitInterval → ℂ := fun t ↦ Complex.exp (-(2 * Real.pi * t : ℝ) * I) with hE
  have hEn (t : unitInterval) : ‖E t‖ = 1 := by
    simp only [hE, ← Complex.ofReal_neg]
    exact Complex.norm_exp_ofReal_mul_I _
  refine Circle.degree_eq_of_norm_sub_lt _ _
    (z := fun t ↦ inversion 0 1 (circle a⁻¹ r t) - a)
    (w := fun t ↦ -((a ^ 2 * r : ℝ) : ℂ) * E t) (fun t ↦ ?_) (fun t ↦ ?_) (fun t ↦ ?_)
  · simp [Path.map_coe]
  · have hn : ‖-((a ^ 2 * r : ℝ) : ℂ) * E t‖ = a ^ 2 * r := by
      rw [norm_mul, hEn, mul_one, norm_neg, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rw [hn]
    simp only [negExpLoop, Path.coe_mk_mk, Circle.coe_exp, hE]
    rw [show ((Real.pi - 2 * Real.pi * t : ℝ) : ℂ) * I =
        Real.pi * I + (-(2 * Real.pi * t : ℝ)) * I by push_cast; ring,
      Complex.exp_add, Complex.exp_pi_mul_I]
    have : ((a ^ 2 * r : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (by positivity : (0 : ℝ) < a ^ 2 * r).ne'
    field_simp
  · have hc : starRingEnd ℂ (circle a⁻¹ r t) = ((a⁻¹ : ℝ) : ℂ) + r * E t := by
      simp only [PlaneMinusRealPoints.circle_apply, circleMap, map_add, map_mul,
        Complex.conj_ofReal, ← Complex.exp_conj, hE, map_mul, Complex.conj_I]
      congr 2
      push_cast
      ring_nf
    have hw : ‖((a⁻¹ : ℝ) : ℂ) + r * E t‖ ≥ a⁻¹ - r := by
      have := norm_sub_norm_le (((a⁻¹ : ℝ)) : ℂ) (-(r * E t))
      rw [sub_neg_eq_add, Complex.norm_real, Real.norm_of_nonneg (by positivity), norm_neg,
        norm_mul, hEn, mul_one, Complex.norm_real, Real.norm_of_nonneg hr.le] at this
      linarith
    have hw0 : ((a⁻¹ : ℝ) : ℂ) + r * E t ≠ 0 := by
      intro h
      rw [h, norm_zero] at hw
      linarith
    have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha0.ne'
    have hid : inversion 0 1 (circle a⁻¹ r t) - a - -((a ^ 2 * r : ℝ) : ℂ) * E t =
        (a ^ 2 * r ^ 2 : ℝ) * E t ^ 2 / (((a⁻¹ : ℝ) : ℂ) + r * E t) := by
      rw [inversion_eq_inv_conj, hc, eq_div_iff hw0]
      have hD := inv_mul_cancel₀ hw0
      have hai : (a : ℂ) * ((a⁻¹ : ℝ) : ℂ) = 1 := by push_cast; field_simp
      push_cast at hD hai ⊢
      linear_combination hD - (1 - (a : ℂ) * r * E t) * hai
    rw [hid, norm_div, norm_mul, norm_pow, hEn, one_pow, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (by positivity), norm_mul, hEn, mul_one, norm_neg, Complex.norm_real,
      Real.norm_of_nonneg (by positivity), div_lt_iff₀ (by linarith)]
    have : 0 < a ^ 2 * r := by positivity
    nlinarith

private theorem quotient_trans_symm_trans {X : Type*} [TopologicalSpace X]
    {x y z : X} (p : Path.Homotopic.Quotient x y) (q : Path.Homotopic.Quotient x z) :
    p.trans (p.symm.trans q) = q := by
  rw [← Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.trans_symm,
    Path.Homotopic.Quotient.refl_trans]

include ha hr har in
/-- In the punctured neighbourhood of `a`, the inverted loop about `a⁻¹` is homotopic to the
reversed circle about `a`, both reached from `-i`. -/
private theorem nInvApproach_homotopic :
    ((nInvApproach ha hr har).trans
        ((nInvCircle ha hr har).trans (nInvApproach ha hr har).symm)).Homotopic
      ((nApproach (a := a)).trans ((nCircle (a := a)).symm.trans (nApproach (a := a)).symm)) := by
  have hd := ((starConvex_nbhdV a).fundamentalGroup_map_directionFrom_bijective (r := 1 / 4)
    (by norm_num) (sphere_subset_nbhdV a) (nInvStart ha hr har)).injective
  have h := Circle.homotopic_trans_of_degree_map_eq hd (γ := nInvCircle ha hr har)
    (δ := (nCircle (a := a)).symm) (by
      rw [degree_nInvCircle ha hr har, ← Path.map_symm, Circle.degree_symm, degree_nCircle])
    ((nInvApproach ha hr har).symm.trans nApproach)
  have h' := Path.Homotopic.Quotient.eq.2 h
  refine Path.Homotopic.Quotient.exact ?_
  rw [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_trans, h']
  simp only [Path.trans_symm, Path.symm_symm, Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.mk_symm, Path.Homotopic.Quotient.trans_assoc,
    quotient_trans_symm_trans,
    Path.Homotopic.Quotient.trans_symm, Path.Homotopic.Quotient.trans_refl]

end Compare

/-! ### The loops about the finite punctures -/

section Small

variable {n : ℕ} (k : Fin n)

private theorem one_le_rev_castSucc : (1 : ℝ) ≤ (((Fin.castSucc k).rev : ℕ) : ℝ) := by
  have : 1 ≤ ((Fin.castSucc k).rev : ℕ) := by rw [Fin.val_rev, Fin.val_castSucc]; omega
  exact_mod_cast this

private theorem sq_rev_castSucc_mul_le :
    (((Fin.castSucc k).rev : ℕ) : ℝ) ^ 2 * (1 / ((n : ℝ) + 1) ^ 2 / 4) ≤ 1 / 4 := by
  have h1 : (((Fin.castSucc k).rev : ℕ) : ℝ) ≤ n := by
    have : ((Fin.castSucc k).rev : ℕ) ≤ n := by rw [Fin.val_rev, Fin.val_castSucc]; omega
    exact_mod_cast this
  rw [mul_div_assoc', mul_one_div, div_div, div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

private theorem inversion_mem_compl_range
    (u : ↥(nbhdV (((Fin.castSucc k).rev : ℕ) : ℝ) \ {((((Fin.castSucc k).rev : ℕ) : ℝ) : ℂ)})) :
    inversion 0 1 (u : ℂ) ∈ (range fun i ↦ (puncturedSpherePoint n i : ℂ))ᶜ := by
  rintro ⟨i, hi⟩
  simp only at hi
  have hu := congrArg (inversion 0 1) hi
  rw [EuclideanGeometry.inversion_inversion _ one_ne_zero, puncturedSpherePoint_def,
    inversion_ofReal, inv_inv] at hu
  have hV := u.prop.1
  have hne := u.prop.2
  rw [← hu] at hV hne
  rcases hV with hV | hV
  · simp at hV
  · rw [mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      at hV
    obtain ⟨h1, h2⟩ := abs_lt.1 hV
    have hm : ((Fin.castSucc i).rev : ℕ) = ((Fin.castSucc k).rev : ℕ) := by
      rcases lt_trichotomy ((Fin.castSucc i).rev : ℕ) ((Fin.castSucc k).rev : ℕ) with h | h | h
      · have : (((Fin.castSucc i).rev : ℕ) : ℝ) + 1 ≤ ((Fin.castSucc k).rev : ℕ) := by
          exact_mod_cast h
        linarith
      · exact h
      · have : (((Fin.castSucc k).rev : ℕ) : ℝ) + 1 ≤ ((Fin.castSucc i).rev : ℕ) := by
          exact_mod_cast h
        linarith
    exact hne (by rw [hm]; rfl)

/-- The inversion, from the punctured neighbourhood of the centre of the ball
`(Fin.castSucc k).rev` in the chart `sphereChart` to the plane minus the points. -/
private def inversionToCompl :
    C(↥(nbhdV (((Fin.castSucc k).rev : ℕ) : ℝ) \ {((((Fin.castSucc k).rev : ℕ) : ℝ) : ℂ)}),
      ↥(range fun i ↦ (puncturedSpherePoint n i : ℂ))ᶜ) where
  toFun u := ⟨inversion 0 1 u, inversion_mem_compl_range k u⟩
  continuous_toFun := (continuous_const.inversion continuous_const continuous_subtypeVal
    fun u h ↦ by
      have := u.prop.1
      rw [h] at this
      rcases this with h0 | h0
      · simp at h0
      · rw [mem_ball, dist_zero_left, Complex.norm_real, Real.norm_of_nonneg (by positivity)] at h0
        linarith [one_le_rev_castSucc k]).subtype_mk _

private theorem segment_zero_negI_mem (t : unitInterval) :
    Path.segment (0 : ℂ) (-I) t ∈ (range fun i ↦ (puncturedSpherePoint n i : ℂ))ᶜ := by
  rintro ⟨i, hi⟩
  have : puncturedSpherePoint n i = 0 := by
    simpa [Path.segment_apply, AffineMap.lineMap_apply_module] using congrArg Complex.re hi
  exact puncturedSpherePoint_ne_zero i this

/-- The segment from `0` to `-i` in the plane minus the points, ending at the image of `-i`
under `inversionToCompl`. -/
private def segmentToNegI : Path (⟨0, zero_mem_compl_range_puncturedSpherePoint⟩ :
      ↥(range fun i ↦ (puncturedSpherePoint n i : ℂ))ᶜ) (inversionToCompl k (nNegI _)) :=
  ((Path.segment (0 : ℂ) (-I)).cast rfl inversion_neg_I).codRestrict fun t ↦ by
    exact segment_zero_negI_mem t

@[simp] private theorem coe_segmentToNegI_apply (t : unitInterval) :
    (segmentToNegI k t : ℂ) = Path.segment (0 : ℂ) (-I) t := 
  Path.codRestrict_coe _ _ t

private theorem coe_inversionToCompl_apply
    (u : ↥(nbhdV (((Fin.castSucc k).rev : ℕ) : ℝ) \ {((((Fin.castSucc k).rev : ℕ) : ℝ) : ℂ)})) :
    (inversionToCompl k u : ℂ) = inversion 0 1 (u : ℂ) := rfl

private theorem loop_eq_trans :
    PlaneMinusRealPoints.loop (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1) ^ 2)
        one_div_sq_le_abs_puncturedSpherePoint_sub puncturedSpherePoint_ne_zero k =
      (segmentToNegI k).trans ((((nInvApproach (one_le_rev_castSucc k) (by positivity)
        (sq_rev_castSucc_mul_le k)).trans ((nInvCircle (one_le_rev_castSucc k) (by positivity)
        (sq_rev_castSucc_mul_le k)).trans (nInvApproach (one_le_rev_castSucc k) (by positivity)
        (sq_rev_castSucc_mul_le k)).symm)).map (inversionToCompl k).continuous).trans
          (segmentToNegI k).symm) := by
  refine Path.ext (funext fun t ↦ Subtype.ext ?_)
  rw [PlaneMinusRealPoints.coe_loop_apply, PlaneMinusRealPoints.loopInPlane_def,
    puncturedSpherePoint_def]
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

private theorem ballCircle_eq_sphereCoChart {x : ℝ} {m : ℕ} (hx : x = m + 1) (s : unitInterval) :
    ballCircle 0 (m + 1) s = sphereCoChart (Complex.orthonormalBasisOneI.repr
      (inversion 0 1 ((circlePath (x : ℂ) (√2 / 4) (Real.pi / 4)) s))) := by
  rw [sphereCoChart_repr_inversion, ballCircle_zero_apply_eq_sphereChart, circlePath_apply,
    hx]
  · push_cast
    rfl
  · have := (circlePath_mem (a := x) s).1
    intro h
    rw [h] at this
    rcases this with h0 | h0
    · simp at h0
    · rw [mem_ball, dist_zero_left, Complex.norm_real, Real.norm_of_nonneg (by
        rw [hx]; positivity)] at h0
      have : (0 : ℝ) ≤ m := m.cast_nonneg
      linarith

private theorem peripheralLoop_eq_trans :
    ((peripheralLoop 0 (n + 1) (Fin.castSucc k)).map
        (puncturedSphereHomeomorph n).symm.continuous).cast
        puncturedSphereHomeomorph_symm_basePoint.symm
        puncturedSphereHomeomorph_symm_basePoint.symm =
      (((segmentToNegI k).trans ((nApproach (a := (((Fin.castSucc k).rev : ℕ) : ℝ))).map
        (inversionToCompl k).continuous)).trans
        ((nCircle (a := (((Fin.castSucc k).rev : ℕ) : ℝ))).symm.map
          (inversionToCompl k).continuous)).trans
        ((segmentToNegI k).trans ((nApproach (a := (((Fin.castSucc k).rev : ℕ) : ℝ))).map
          (inversionToCompl k).continuous)).symm := by
  refine Path.ext (funext fun t ↦ ?_)
  rw [Path.cast_coe, Path.map_coe, comp_apply, Homeomorph.symm_apply_eq]
  apply Subtype.ext
  rw [coe_peripheralLoop_apply, coe_puncturedSphereHomeomorph_apply, ballLoop_def]
  obtain ⟨m, hm⟩ : ∃ m, ((Fin.castSucc k).rev : ℕ) = m + 1 :=
    ⟨n - 1 - k, by rw [Fin.val_rev, Fin.val_castSucc]; omega⟩
  have ha : ((((Fin.castSucc k).rev : ℕ) : ℝ)) = (m : ℝ) + 1 := by rw [hm]; push_cast; ring
  conv_lhs => rw [hm, ballPath_zero_succ]
  simp only [Path.trans_apply, Path.symm_apply, Path.map_coe, Path.cast_coe, comp_apply,
    apply_dite Subtype.val, coe_segmentToNegI_apply, coe_nApproach_apply, coe_nCircle_apply,
    coe_inversionToCompl_apply, chartApproach, apply_dite (inversion (0 : ℂ) 1),
    apply_dite Complex.orthonormalBasisOneI.repr, apply_dite sphereCoChart]
  split_ifs
  · exact sphereCoChart_segment_negI _
  · exact sphereChart_segment_bottom ha _
  · exact sphereChart_segment_up ha _
  · exact ballCircle_eq_sphereCoChart ha _
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
  have H := (nInvApproach_homotopic (one_le_rev_castSucc k) (by positivity)
    (sq_rev_castSucc_mul_le k)).map (inversionToCompl k)
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

end SymplecticGeometry.ClosedSurface

end
