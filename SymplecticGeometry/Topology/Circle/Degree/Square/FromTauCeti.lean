/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Complex.Arg
public import TauCeti.Topology.Circle.Degree.Square
import all TauCeti.Topology.Circle.Degree.Square

/-!
# The direction from the centre of the square

This file is a part of Tau Ceti's file `TauCeti/Topology/Circle/Degree/Square.lean`, as of the
commit `a4c9303b28` of Tau Ceti's main branch (unchanged there through `834d3b1a61`), which the
pinned release does not have yet. It contains the declarations of that file's section
*The direction from the centre*:

* `TauCeti.squareCenterOffset`, `TauCeti.squareCenterDirection`: the offset of a point of the
  square from the centre, as a complex number, and its direction;
* `TauCeti.squareBoundaryDegree_squareCenterDirection`: the direction from the centre has
  degree `1` around the boundary of the square,

together with the private lemma `TauCeti.squareBoundaryDegree_eq_of_mul_two_pi` that the last
proof uses. The basic map of nonzero degree is the direction `TauCeti.squareCenterDirection` of
a point from the centre of the square, the point `c / ‖c‖` of the circle for its offset
`c = (s - 1/2) + (t - 1/2) i` from the centre. Its degree is `1`: along each edge the direction
sweeps a quarter turn, as the arguments of the corners `(±1 ± i) / 2` show.

They are stated under their Tau Ceti names and namespace, with Tau Ceti's statements, proofs and
docstrings unchanged, so that moving Tau Ceti past this commit deletes this file without
renames. The imports are those of Tau Ceti's file at that commit; the import of the pinned
version of Tau Ceti's file is also made with `import all`, since the proofs use the private
edges of the square, `pathAngle`, `pathAngle_eq` and `squareBoundaryDegree_mul_two_pi` of that
file.

## References

* A. Hatcher, *Vector Bundles and K-Theory*, Section 1.2 (clutching functions and the winding
  number of a map from the boundary of a disc to the circle).
-/

public section

noncomputable section

open Set Function
open scoped unitInterval Topology.Homotopy

namespace TauCeti

variable {Γ Γ' : (Fin 2 → I) → Circle}

/-- An integer is the degree of `Γ` around the boundary of the square once its multiple of `2π`
is the multiple `squareBoundaryDegree Γ * 2π`. -/
private theorem squareBoundaryDegree_eq_of_mul_two_pi {n : ℤ}
    (h : (squareBoundaryDegree Γ : ℝ) * (2 * Real.pi) = n * (2 * Real.pi)) :
    squareBoundaryDegree Γ = n := by
  exact_mod_cast mul_right_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0) h


/-! ### The direction from the centre -/

/-- The position of a point `(s, t)` of the square relative to the centre `(1/2, 1/2)`, as the
complex number `(s - 1/2) + (t - 1/2) i`. -/
def squareCenterOffset (y : Fin 2 → I) : ℂ :=
  ((y 0 : ℝ) - 1 / 2 : ℝ) + ((y 1 : ℝ) - 1 / 2 : ℝ) * Complex.I

/-- The real part of the offset from the centre is `s - 1/2`. -/
@[simp]
theorem re_squareCenterOffset (y : Fin 2 → I) : (squareCenterOffset y).re = (y 0 : ℝ) - 1 / 2 := by
  simp [squareCenterOffset]

/-- The imaginary part of the offset from the centre is `t - 1/2`. -/
@[simp]
theorem im_squareCenterOffset (y : Fin 2 → I) : (squareCenterOffset y).im = (y 1 : ℝ) - 1 / 2 := by
  simp [squareCenterOffset]

@[fun_prop]
theorem continuous_squareCenterOffset : Continuous squareCenterOffset := by
  unfold squareCenterOffset
  fun_prop

/-- The centre of the square is not on its boundary. -/
theorem squareCenterOffset_ne_zero_of_mem {y : Fin 2 → I} (hy : y ∈ Cube.boundary (Fin 2)) :
    squareCenterOffset y ≠ 0 := by
  intro h0
  simp only [Complex.ext_iff, re_squareCenterOffset, im_squareCenterOffset, Complex.zero_re,
    Complex.zero_im, sub_eq_zero] at h0
  obtain ⟨i, hi | hi⟩ := hy <;> fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one] at hi <;>
    norm_num [hi] at h0

/-- The direction of a point of the square from its centre, the point `c / ‖c‖` of the circle for
`c = squareCenterOffset y` (`TauCeti.coe_squareCenterDirection`). It is `1` at the centre. -/
def squareCenterDirection (y : Fin 2 → I) : Circle :=
  Circle.exp (Complex.arg (squareCenterOffset y))

/-- Away from the centre, the direction from the centre is `c / ‖c‖` for the offset `c`. -/
theorem coe_squareCenterDirection {y : Fin 2 → I} (hy : squareCenterOffset y ≠ 0) :
    (squareCenterDirection y : ℂ) = squareCenterOffset y / ‖squareCenterOffset y‖ := by
  rw [squareCenterDirection, Circle.coe_exp, Complex.exp_arg_mul_I hy]

/-- The direction from the centre is continuous on the boundary of the square. -/
theorem continuousOn_squareCenterDirection :
    ContinuousOn squareCenterDirection (Cube.boundary (Fin 2)) :=
  (Topology.IsInducing.subtypeVal.continuousOn_iff).2 <|
    (continuous_squareCenterOffset.continuousOn.div
      (Complex.continuous_ofReal.comp continuous_squareCenterOffset.norm).continuousOn
      fun y hy ↦ by simpa using squareCenterOffset_ne_zero_of_mem hy).congr
    fun y hy ↦ coe_squareCenterDirection (squareCenterOffset_ne_zero_of_mem hy)

/-- Along a path of the square, the angle swept by a map is the change of any continuous lift of
it along `Circle.exp`. -/
private theorem pathAngle_eq_sub {a b : Fin 2 → I} (γ : Path a b) (h : ContinuousOn Γ (range γ))
    {θ : I → ℝ} (hθ : Continuous θ) (hθΓ : ∀ t, Circle.exp (θ t) = Γ (γ t)) :
    pathAngle γ Γ = θ 1 - θ 0 := by
  rw [pathAngle_eq γ h]
  exact Circle.angleChange_eq_sub _ hθ hθΓ

/-- Along an edge of the square that avoids the closed negative real axis, as seen from the
centre, the direction from the centre sweeps the angle between the arguments of the ends. -/
private theorem pathAngle_squareCenterDirection_eq_arg_sub {a b : Fin 2 → I} (γ : Path a b)
    (hrange : range γ ⊆ Cube.boundary (Fin 2))
    (hslit : ∀ t, squareCenterOffset (γ t) ∈ Complex.slitPlane) :
    pathAngle γ squareCenterDirection =
      Complex.arg (squareCenterOffset b) - Complex.arg (squareCenterOffset a) := by
  rw [pathAngle_eq_sub γ (continuousOn_squareCenterDirection.mono hrange)
    (continuous_iff_continuousAt.2 fun t ↦ (Complex.continuousAt_arg (hslit t)).comp
      (f := fun s ↦ squareCenterOffset (γ s)) (by fun_prop)) fun t ↦ rfl]
  simp only [comp_apply, Path.source, Path.target]

/-- Along an edge of the square that avoids the closed positive real axis, as seen from the
centre, the direction from the centre sweeps the angle between the arguments of the negated
ends. -/
private theorem pathAngle_squareCenterDirection_eq_arg_neg_sub {a b : Fin 2 → I} (γ : Path a b)
    (hrange : range γ ⊆ Cube.boundary (Fin 2))
    (hslit : ∀ t, -squareCenterOffset (γ t) ∈ Complex.slitPlane) :
    pathAngle γ squareCenterDirection =
      Complex.arg (-squareCenterOffset b) - Complex.arg (-squareCenterOffset a) := by
  have hθ : Continuous fun t ↦ Complex.arg (-squareCenterOffset (γ t)) + Real.pi :=
    (continuous_iff_continuousAt.2 fun t ↦ (Complex.continuousAt_arg (hslit t)).comp
      (f := fun s ↦ -squareCenterOffset (γ s)) (by fun_prop)).add continuous_const
  rw [pathAngle_eq_sub γ (continuousOn_squareCenterDirection.mono hrange) hθ
    fun t ↦ Circle.ext ?_]
  · simp only [Path.source, Path.target]
    ring
  have hne := squareCenterOffset_ne_zero_of_mem (hrange (mem_range_self t))
  rw [Circle.exp_add, Circle.coe_mul, Circle.coe_exp, Complex.exp_arg_mul_I (neg_ne_zero.2 hne),
    coe_squareCenterDirection hne, Circle.coe_exp, Complex.exp_pi_mul_I, norm_neg]
  ring

/-- **The direction from the centre has degree one.** Running once counterclockwise around the
boundary of the square, the direction of the point from the centre of the square turns once
counterclockwise around the circle. -/
theorem squareBoundaryDegree_squareCenterDirection :
    squareBoundaryDegree squareCenterDirection = 1 := by
  -- The four edges, read through the arguments of the corners as seen from the centre.
  have hbot := pathAngle_squareCenterDirection_eq_arg_sub squareBottom range_squareBottom
    fun t ↦ Complex.mem_slitPlane_iff.2 (Or.inr (by norm_num [squareBottom]))
  have hright := pathAngle_squareCenterDirection_eq_arg_sub squareRight range_squareRight
    fun t ↦ Complex.mem_slitPlane_iff.2 (Or.inl (by norm_num [squareRight]))
  have htop := pathAngle_squareCenterDirection_eq_arg_sub squareTop range_squareTop
    fun t ↦ Complex.mem_slitPlane_iff.2 (Or.inr (by norm_num [squareTop]))
  have hleft := pathAngle_squareCenterDirection_eq_arg_neg_sub squareLeft range_squareLeft
    fun t ↦ Complex.mem_slitPlane_iff.2 (Or.inl (by norm_num [squareLeft]))
  -- Every corner is `±z` or `±conj z` for the upper right corner `z = (1 + i) / 2`.
  set z : ℂ := squareCenterOffset ![1, 1]
  have hz : 0 < z.im := by norm_num [z]
  have h00 : squareCenterOffset ![0, 0] = -z := by apply Complex.ext <;> norm_num [z]
  have h10 : squareCenterOffset ![1, 0] = (starRingEnd ℂ) z := by
    apply Complex.ext <;> norm_num [z]
  have h01 : squareCenterOffset ![0, 1] = -(starRingEnd ℂ) z := by
    apply Complex.ext <;> norm_num [z]
  have hconj : Complex.arg ((starRingEnd ℂ) z) = -Complex.arg z := by
    have hπ : Complex.arg z ≠ Real.pi := fun h ↦ hz.ne' (Complex.arg_eq_pi_iff.1 h).2
    simp [Complex.arg_conj, hπ]
  have key := squareBoundaryDegree_mul_two_pi continuousOn_squareCenterDirection
  rw [hbot, hright, htop, hleft, h00, h10, h01, neg_neg, neg_neg,
    Complex.arg_neg_eq_arg_sub_pi_of_im_pos hz,
    Complex.arg_neg_eq_arg_add_pi_of_im_neg (by simpa using hz), hconj] at key
  exact squareBoundaryDegree_eq_of_mul_two_pi (by rw [key]; push_cast; ring)

end TauCeti
