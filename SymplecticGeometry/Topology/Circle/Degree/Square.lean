/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.Circle.Degree.Square
public import TauCeti.Topology.Homotopy.Cube.Radius
public import TauCeti.Topology.Circle.FreeLoop
import SymplecticGeometry.AlgebraicTopology.UniversalCover.Circle.FreeLoop.Basic

/-!
# The degree around the boundary of the square and around an inner circle

Tau Ceti's degree `TauCeti.squareBoundaryDegree Γ` of a map `Γ : I² → S¹` is read along the
boundary of the square. This file compares it with the degree along a circle about the centre of
the square.

* `TauCeti.squareBoundaryDegree_comp`: composing with a self-map `g` of the circle multiplies the
  degree around the boundary by the degree of `g`.
* `TauCeti.abs_re_squareCenterOffset_le`, `TauCeti.abs_im_squareCenterOffset_le`,
  `TauCeti.one_half_le_norm_squareCenterOffset_of_mem`: the offset of a point of the square from
  the centre has coordinates of absolute value at most `1/2`, and norm at least `1/2` on the
  boundary; the centre itself has offset `0` (`TauCeti.squareCenterOffset_cubeCenter`).
* `SymplecticGeometry.squareOfOffset`: the point of the square with a given offset from the centre,
  clamped to the square, which inverts `TauCeti.squareCenterOffset`
  (`SymplecticGeometry.squareOfOffset_squareCenterOffset`,
  `SymplecticGeometry.squareCenterOffset_squareOfOffset`).
* `TauCeti.squareBoundaryDegree_eq_degree_toBasedLoop`: if `Γ` is continuous on the closed
  annulus of the points whose offset from the centre (`TauCeti.squareCenterOffset`) has norm at
  least `r`, for `0 ≤ r ≤ 1/2`, then its degree around the boundary of the square is the degree
  of the loop `ζ ↦ Γ (centre + r ζ)` on the circle of radius `r` about the centre, given as any
  self-map `g` of the circle that agrees with it.
* `SymplecticGeometry.squareBoundaryDegree_eq_degree_squareOfOffset`: the same, with the loop
  `ζ ↦ Γ (squareOfOffset (r ζ))` read off `Γ`, continuous by
  `SymplecticGeometry.continuous_comp_squareOfOffset_mul`.

The proof pushes the boundary of the square radially onto the circle of radius `r`, inside the
annulus, which leaves the composite of the loop on the circle with the direction from the centre
`TauCeti.squareCenterDirection`, a map of degree `1` around the boundary
(`TauCeti.squareBoundaryDegree_squareCenterDirection`).

## References

* A. Hatcher, *Vector Bundles and K-Theory*, Section 1.2 (clutching functions and the winding
  number of a map from the boundary of a disc to the circle).
-/

public section

noncomputable section

open Set

open scoped unitInterval

namespace TauCeti

variable {Γ : (Fin 2 → I) → Circle}

/-- **Composition with a circle map.** For `Γ` continuous on the boundary of the square and a
self-map `g` of the circle, the degree of `g ∘ Γ` around the boundary is the degree of `g` times
that of `Γ`. -/
theorem squareBoundaryDegree_comp (hΓ : ContinuousOn Γ (Cube.boundary (Fin 2)))
    (g : C(Circle, Circle)) :
    squareBoundaryDegree (g ∘ Γ) = g.circleDegree * squareBoundaryDegree Γ := by
  rw [squareBoundaryDegree_eq_degree (g.continuous.comp_continuousOn hΓ),
    squareBoundaryDegree_eq_degree hΓ, ← Circle.degree_map]
  exact Circle.degree_congr _ _ fun _ ↦ rfl

/-- The real part of the offset of a point of the square from the centre is at most `1/2` in
absolute value. -/
theorem abs_re_squareCenterOffset_le (y : Fin 2 → I) :
    |(squareCenterOffset y).re| ≤ 1 / 2 := by
  rw [re_squareCenterOffset, abs_le]
  constructor <;> linarith [unitInterval.nonneg (y 0), unitInterval.le_one (y 0)]

/-- The imaginary part of the offset of a point of the square from the centre is at most `1/2` in
absolute value. -/
theorem abs_im_squareCenterOffset_le (y : Fin 2 → I) :
    |(squareCenterOffset y).im| ≤ 1 / 2 := by
  rw [im_squareCenterOffset, abs_le]
  constructor <;> linarith [unitInterval.nonneg (y 1), unitInterval.le_one (y 1)]

/-- The centre of the square has offset `0` from the centre. -/
@[simp]
theorem squareCenterOffset_cubeCenter : squareCenterOffset (cubeCenter : Fin 2 → I) = 0 :=
  Complex.ext (by simp [re_squareCenterOffset, cubeCenter_apply])
    (by simp [im_squareCenterOffset, cubeCenter_apply])

/-- The points of the boundary of the square are at distance at least `1/2` from the centre. -/
theorem one_half_le_norm_squareCenterOffset_of_mem {y : Fin 2 → I}
    (hy : y ∈ Cube.boundary (Fin 2)) : 1 / 2 ≤ ‖squareCenterOffset y‖ := by
  obtain ⟨i, hi | hi⟩ := hy <;> fin_cases i <;>
    simp only [Fin.zero_eta, Fin.mk_one] at hi
  · simpa [hi] using Complex.abs_re_le_norm (squareCenterOffset y)
  · simpa [hi] using Complex.abs_im_le_norm (squareCenterOffset y)
  · have := Complex.abs_re_le_norm (squareCenterOffset y)
    norm_num [hi] at this
    linarith
  · have := Complex.abs_im_le_norm (squareCenterOffset y)
    norm_num [hi] at this
    linarith

end TauCeti

namespace SymplecticGeometry

open TauCeti

variable {Γ : (Fin 2 → I) → Circle}

/-- The point of the square whose offset from the centre is `z`, each coordinate clamped to
`[0, 1]`. It inverts `TauCeti.squareCenterOffset`
(`SymplecticGeometry.squareOfOffset_squareCenterOffset`), and `TauCeti.squareCenterOffset` inverts
it on the offsets whose real and imaginary parts are at most `1/2` in absolute value
(`SymplecticGeometry.squareCenterOffset_squareOfOffset`). -/
def squareOfOffset (z : ℂ) : Fin 2 → I :=
  ![projIcc 0 1 zero_le_one (1 / 2 + z.re), projIcc 0 1 zero_le_one (1 / 2 + z.im)]

theorem squareOfOffset_def (z : ℂ) : squareOfOffset z =
    ![projIcc 0 1 zero_le_one (1 / 2 + z.re), projIcc 0 1 zero_le_one (1 / 2 + z.im)] :=
  (rfl)

@[fun_prop]
theorem continuous_squareOfOffset : Continuous squareOfOffset := by
  refine continuous_pi fun i ↦ ?_
  fin_cases i <;> simp only [squareOfOffset_def] <;> fun_prop

@[simp]
theorem squareOfOffset_squareCenterOffset (y : Fin 2 → I) :
    squareOfOffset (squareCenterOffset y) = y := by
  ext i
  fin_cases i <;> simp [squareOfOffset_def]

theorem squareCenterOffset_squareOfOffset {z : ℂ} (hre : |z.re| ≤ 1 / 2)
    (him : |z.im| ≤ 1 / 2) : squareCenterOffset (squareOfOffset z) = z := by
  rw [abs_le] at hre him
  apply Complex.ext <;> simp only [squareOfOffset_def, re_squareCenterOffset,
    im_squareCenterOffset, Matrix.cons_val_zero, Matrix.cons_val_one]
  · rw [projIcc_of_mem _ ⟨by linarith, by linarith⟩]
    ring
  · rw [projIcc_of_mem _ ⟨by linarith, by linarith⟩]
    ring

/-- For `0 ≤ r ≤ 1/2`, the point of the square at offset `r ζ` from the centre, for `ζ` on the
circle, has offset exactly `r ζ`. -/
theorem squareCenterOffset_squareOfOffset_mul {r : ℝ} (hr₀ : 0 ≤ r) (hr : r ≤ 1 / 2)
    (ζ : Circle) : squareCenterOffset (squareOfOffset (r * ζ)) = r * ζ := by
  have hn : ‖(r : ℂ) * ζ‖ ≤ 1 / 2 := by simpa [abs_of_nonneg hr₀] using hr
  exact squareCenterOffset_squareOfOffset ((Complex.abs_re_le_norm _).trans hn)
    ((Complex.abs_im_le_norm _).trans hn)

/-- If `Γ` is continuous on the closed annulus of the points at distance at least `r` from the
centre, for `0 ≤ r ≤ 1/2`, then the loop `ζ ↦ Γ (centre + r ζ)` on the circle of radius `r` is
continuous. -/
theorem continuous_comp_squareOfOffset_mul {r : ℝ} (hr₀ : 0 ≤ r) (hr : r ≤ 1 / 2)
    (hΓ : ContinuousOn Γ {y | r ≤ ‖squareCenterOffset y‖}) :
    Continuous fun ζ : Circle ↦ Γ (squareOfOffset (r * ζ)) := by
  refine hΓ.comp_continuous (by fun_prop) fun ζ ↦ ?_
  simp [squareCenterOffset_squareOfOffset_mul hr₀ hr, abs_of_nonneg hr₀]

end SymplecticGeometry

namespace TauCeti

open SymplecticGeometry

variable {Γ : (Fin 2 → I) → Circle}

/-- **The degree around the boundary of the square is the degree around an inner circle.** Let
`0 ≤ r ≤ 1/2`, let `Γ` be continuous on the closed annulus of the points of the square at distance
at least `r` from the centre, and let `g` be the self-map of the circle with `g ζ = Γ y` for the
point `y` of the square at offset `r ζ` from the centre. Then the degree of `Γ` around the boundary
of the square is the degree of the loop `g.toBasedLoop` traced by `g`. -/
theorem squareBoundaryDegree_eq_degree_toBasedLoop {r : ℝ} (hr₀ : 0 ≤ r) (hr : r ≤ 1 / 2)
    (hΓ : ContinuousOn Γ {y | r ≤ ‖squareCenterOffset y‖}) (g : C(Circle, Circle))
    (hg : ∀ (ζ : Circle) (y : Fin 2 → I), squareCenterOffset y = r * ζ → g ζ = Γ y) :
    squareBoundaryDegree Γ = Circle.degree g.toBasedLoop := by
  -- The factor by which the radial homotopy scales the offset of `y` at time `t`.
  let s : I × (Fin 2 → I) → ℝ := fun q ↦ (1 - q.1) + q.1 * (r / ‖squareCenterOffset q.2‖)
  let K : I × (Fin 2 → I) → Fin 2 → I := fun q ↦ squareOfOffset (s q * squareCenterOffset q.2)
  have hs {q : I × (Fin 2 → I)} (hq : q.2 ∈ Cube.boundary (Fin 2)) :
      0 ≤ s q ∧ s q ≤ 1 ∧ r ≤ s q * ‖squareCenterOffset q.2‖ := by
    have hn := one_half_le_norm_squareCenterOffset_of_mem hq
    have hpos : 0 < ‖squareCenterOffset q.2‖ := by linarith
    have hle : r / ‖squareCenterOffset q.2‖ ≤ 1 := (div_le_one hpos).2 (by linarith)
    have h0 : 0 ≤ r / ‖squareCenterOffset q.2‖ := by positivity
    have ht := And.intro (unitInterval.nonneg q.1) (unitInterval.le_one q.1)
    refine ⟨by nlinarith [ht.1, ht.2], by nlinarith [ht.1, ht.2], ?_⟩
    have : s q * ‖squareCenterOffset q.2‖ = (1 - q.1) * ‖squareCenterOffset q.2‖ + q.1 * r := by
      simp only [s]
      field_simp
    rw [this]
    nlinarith [ht.1, ht.2]
  have hK {q : I × (Fin 2 → I)} (hq : q.2 ∈ Cube.boundary (Fin 2)) :
      squareCenterOffset (K q) = s q * squareCenterOffset q.2 := by
    obtain ⟨hs₀, hs₁, -⟩ := hs hq
    apply squareCenterOffset_squareOfOffset <;>
      simp only [Complex.re_ofReal_mul, Complex.im_ofReal_mul, abs_mul, abs_of_nonneg hs₀]
    · nlinarith [abs_re_squareCenterOffset_le q.2, abs_nonneg (squareCenterOffset q.2).re]
    · nlinarith [abs_im_squareCenterOffset_le q.2, abs_nonneg (squareCenterOffset q.2).im]
  have hH : ContinuousOn (fun q ↦ Γ (K q)) (univ ×ˢ Cube.boundary (Fin 2)) := by
    refine hΓ.comp (continuous_squareOfOffset.comp_continuousOn ?_) fun q hq ↦ ?_
    · refine ContinuousOn.mul (Complex.continuous_ofReal.comp_continuousOn ?_) (by fun_prop)
      refine ContinuousOn.add (by fun_prop) (ContinuousOn.mul (by fun_prop) ?_)
      exact continuousOn_const.div (by fun_prop) fun q hq ↦
        (one_half_pos.trans_le (one_half_le_norm_squareCenterOffset_of_mem hq.2)).ne'
    · obtain ⟨hs₀, -, hr'⟩ := hs hq.2
      simpa [hK hq.2, norm_mul, abs_of_nonneg hs₀] using hr'
  have h := squareBoundaryDegree_eq_of_homotopy hH
  have h₀ : (fun y ↦ Γ (K (0, y))) = Γ := by
    funext y
    simp [K, s]
  have h₁ : EqOn (fun y ↦ Γ (K (1, y))) (g ∘ squareCenterDirection) (Cube.boundary (Fin 2)) := by
    intro y hy
    have hne := squareCenterOffset_ne_zero_of_mem hy
    refine (hg _ _ ?_).symm
    rw [hK (q := (1, y)) hy, coe_squareCenterDirection hne]
    simp only [s, Set.Icc.coe_one, sub_self, one_mul, zero_add]
    push_cast
    ring
  rw [h₀] at h
  rw [h, squareBoundaryDegree_congr h₁,
    squareBoundaryDegree_comp continuousOn_squareCenterDirection,
    squareBoundaryDegree_squareCenterDirection, mul_one, Circle.degree_toBasedLoop]

end TauCeti

namespace SymplecticGeometry

open TauCeti

variable {Γ : (Fin 2 → I) → Circle}

/-- **The degree around the boundary of the square is the degree around an inner circle**, with
the loop read off `Γ`. Let `0 ≤ r ≤ 1/2` and let `Γ` be continuous on the closed annulus of the
points of the square at distance at least `r` from the centre. Then the degree of `Γ` around the
boundary of the square is the degree of the loop `ζ ↦ Γ (centre + r ζ)`. -/
theorem squareBoundaryDegree_eq_degree_squareOfOffset {r : ℝ} (hr₀ : 0 ≤ r) (hr : r ≤ 1 / 2)
    (hΓ : ContinuousOn Γ {y | r ≤ ‖squareCenterOffset y‖}) :
    squareBoundaryDegree Γ = Circle.degree
      (⟨fun ζ : Circle ↦ Γ (squareOfOffset (r * ζ)),
        continuous_comp_squareOfOffset_mul hr₀ hr hΓ⟩ : C(Circle, Circle)).toBasedLoop :=
  squareBoundaryDegree_eq_degree_toBasedLoop hr₀ hr hΓ _ fun ζ y hy ↦ by
    simp [← hy]

end SymplecticGeometry
