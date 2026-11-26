/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Normed.Algebra.HolomorphicFunctionalCalculus.Riesz
public import TauCeti.Analysis.Normed.Algebra.Spectrum
public import TauCeti.MeasureTheory.Integral.DominatedConvergence
public import TauCeti.MeasureTheory.Integral.Circle.Integral
public import SymplecticGeometry.Analysis.Complex.DiscIndicator
public import SymplecticGeometry.Analysis.Normed.Algebra.HolomorphicFunctionalCalculus.Riesz
public import SymplecticGeometry.Analysis.Normed.Algebra.Spectrum
public import SymplecticGeometry.Analysis.Normed.Group.Compact
public import SymplecticGeometry.MeasureTheory.Integral.CircleIntegral

/-!
# The Riesz projection onto the spectrum inside the unit disc

For an element `a` of a complex Banach algebra `A`, `unitDiscRieszProjection a` is the contour
integral `(2πi)⁻¹ ∮_{|z| = 1} (z1 - a)⁻¹ dz` of Mathlib's `resolvent` over the unit circle.

When no point of the spectrum of `a` lies on the unit circle, the part of the spectrum in the
open unit disc is a clopen part `unitDiscClopens a h` of it, and the integral is Tau Ceti's Riesz
idempotent of that part (`unitDiscRieszProjection_eq_rieszIdempotent`). To see this, take radii
`1 < ρ₁ < ρ₂ < s < R` such that no point of the spectrum has norm in `[1, s]` and every point has
norm `< R`. The function equal to `1` on the disc `‖z‖ < ρ₁` and to `0` outside it is holomorphic
on the neighbourhood `‖z‖ < ρ₁ ∨ ρ₂ < ‖z‖` of the spectrum, which leaves out the annulus
`ρ₁ ≤ ‖z‖ ≤ ρ₂`. The cycle made of the unit circle, the circle of radius `R`, and the circle of
radius `s` taken with the opposite orientation lies in that neighbourhood, off the spectrum,
and winds once around every point of the spectrum; on it the integrand of Tau Ceti's
`rieszIdempotent_eq_integral` vanishes except on the unit circle.

Hence `unitDiscRieszProjection a` is an idempotent commuting with `a`, and for an operator `T`
on a complex Banach space an eigenvector of `T` lies in its kernel only for an eigenvalue of norm
`> 1` and in its range only for an eigenvalue of norm `< 1`.

The projection is natural under continuous algebra isomorphisms, in particular under conjugation
of operators by an isomorphism of Banach spaces, and depends continuously on `a` as long as the
spectrum avoids the unit circle.

The proof of `Commute.unitDiscRieszProjection_right` adapts that of Tau Ceti's
`Commute.integral_smul_resolvent_right` from integrals over cycles to circle integrals.

## Main results

* `SymplecticGeometry.unitDiscRieszProjection`: the contour integral above.
* `SymplecticGeometry.unitDiscRieszProjection_eq_rieszIdempotent`: it is the Riesz idempotent of
  the part of the spectrum in the open unit disc.
* `SymplecticGeometry.isIdempotentElem_unitDiscRieszProjection`,
  `SymplecticGeometry.commute_unitDiscRieszProjection`: it is an idempotent commuting with `a`.
* `SymplecticGeometry.map_unitDiscRieszProjection`,
  `SymplecticGeometry.unitDiscRieszProjection_conjContinuousAlgEquiv`: naturality.
* `SymplecticGeometry.continuousAt_unitDiscRieszProjection`: continuity at each element whose
  spectrum avoids the unit circle, from the joint continuity of the resolvent
  (`spectrum.continuousAt_resolvent_prod`) and the upper hemicontinuity of the spectrum
  (`spectrum.eventually_disjoint_of_isClosed`).
* `ContinuousWithinAt.unitDiscRieszProjection`, `ContinuousAt.unitDiscRieszProjection`,
  `ContinuousOn.unitDiscRieszProjection`, `Continuous.unitDiscRieszProjection`: continuity in a
  family, with the spectrum condition only where continuity is asked.
* `SymplecticGeometry.eq_zero_of_unitDiscRieszProjection_apply_eq_zero`,
  `SymplecticGeometry.eq_zero_of_unitDiscRieszProjection_apply_eq_self`: where the eigenvalues
  of the two pieces lie, from `ContinuousLinearMap.mem_image_of_rieszIdempotent_apply_eq_self`
  (an eigenvalue on the range of a Riesz idempotent lies in its part of the spectrum).

## References

* [A. Hatcher, *Vector Bundles and K-Theory*][Hatcher2017], §2.1 (the splitting of a linear
  clutching function).
* T. Kato, *Perturbation Theory for Linear Operators*, Springer, 1995, §I.5.3.
* J. B. Conway, *A Course in Functional Analysis*, second edition, VII.4.
-/

public section

noncomputable section

open Complex Metric Set Filter TopologicalSpace TauCeti

open scoped Real Topology

namespace SymplecticGeometry

variable {A B : Type*} [NormedRing A] [NormedAlgebra ℂ A] [NormedRing B] [NormedAlgebra ℂ B]

/-- The **Riesz projection** of `a` for the unit circle: the contour integral
`(2πi)⁻¹ ∮_{|z| = 1} (z1 - a)⁻¹ dz` of the resolvent of `a`. When the spectrum of `a` avoids the
unit circle, it is the Riesz idempotent of the part of the spectrum in the open unit disc
(`unitDiscRieszProjection_eq_rieszIdempotent`). -/
def unitDiscRieszProjection (a : A) : A :=
  (2 * π * I)⁻¹ • ∮ z in C(0, 1), resolvent a z

theorem unitDiscRieszProjection_def (a : A) :
    unitDiscRieszProjection a = (2 * π * I)⁻¹ • ∮ z in C(0, 1), resolvent a z := (rfl)

/-- The part of the spectrum of `a` in the open unit disc, as a clopen part of the spectrum, when
no point of the spectrum lies on the unit circle. -/
def unitDiscClopens (a : A) (h : ∀ z ∈ spectrum ℂ a, ‖z‖ ≠ 1) : Clopens (spectrum ℂ a) where
  carrier := {z | ‖(z : ℂ)‖ < 1}
  isClopen' := by
    refine ⟨?_, isOpen_lt (by fun_prop) continuous_const⟩
    have : {z : spectrum ℂ a | ‖(z : ℂ)‖ < 1} = ({z | ‖(z : ℂ)‖ ≤ 1} : Set (spectrum ℂ a)) :=
      Set.ext fun z ↦ by
        simp only [Set.mem_ofPred_eq]
        exact ⟨le_of_lt, fun hz ↦ lt_of_le_of_ne hz (h z z.property)⟩
    rw [this]
    exact isClosed_le (by fun_prop) continuous_const

@[simp]
theorem mem_unitDiscClopens {a : A} {h : ∀ z ∈ spectrum ℂ a, ‖z‖ ≠ 1} {z : spectrum ℂ a} :
    z ∈ unitDiscClopens a h ↔ ‖(z : ℂ)‖ < 1 := Iff.rfl

/-- `unitDiscRieszProjection` is natural under continuous algebra isomorphisms. -/
theorem map_unitDiscRieszProjection (φ : A ≃A[ℂ] B) (a : A) :
    φ (unitDiscRieszProjection a) = unitDiscRieszProjection (φ a) := by
  have hres : ∀ z : ℂ, φ (resolvent a z) = resolvent (φ a) z := fun z ↦ by
    simp only [resolvent]
    rw [map_ringInverse φ, map_sub, AlgHomClass.commutes φ]
  rw [unitDiscRieszProjection_def, unitDiscRieszProjection_def, map_smul,
    ← φ.toContinuousLinearEquiv_apply, ← ContinuousLinearEquiv.circleIntegral_comp_comm]
  simp only [φ.toContinuousLinearEquiv_apply, hres]

/-- A step of the proof of `unitDiscRieszProjection_eq_rieszIdempotent`: if every point of `σ`
has norm `< 1` or in `[m, R)`, and `1 < ρ₁ < ρ₂ < s < m`, then the cycle made of the circles of
radii `1` and `R`, minus the circle of radius `s`, lies in `U \ σ` for
`U = {‖z‖ < ρ₁} ∪ {ρ₂ < ‖z‖}`, is null-homologous in `U`, and winds once around each point
of `σ`. -/
private theorem isIn_isNullHomologous_circleCycle {σ : Set ℂ} {ρ₁ ρ₂ s m R : ℝ}
    (h1 : 1 < ρ₁) (h12 : ρ₁ < ρ₂) (h2s : ρ₂ < s) (hsm : s < m) (hgap : ∀ z ∈ σ, ‖z‖ < 1 ∨ m ≤ ‖z‖)
    (hσR : ∀ z ∈ σ, ‖z‖ < R) (hmR : m < R) :
    (Contour.circleCycle 0 1 + Contour.circleCycle 0 R - Contour.circleCycle 0 s).IsIn
        (({z | ‖z‖ < ρ₁} ∪ {z | ρ₂ < ‖z‖}) \ σ) ∧
      (Contour.circleCycle 0 1 + Contour.circleCycle 0 R - Contour.circleCycle 0 s).IsNullHomologous
        ({z | ‖z‖ < ρ₁} ∪ {z | ρ₂ < ‖z‖}) ∧
      ∀ z ∈ σ, Contour.Cycle.windingNumber z
        (Contour.circleCycle 0 1 + Contour.circleCycle 0 R - Contour.circleCycle 0 s) = 1 := by
  have hR0 : 0 < R := by linarith
  have hs0 : 0 < s := by linarith
  have hw0 : ∀ (r : ℝ) (z : ℂ), 0 ≤ r → r < ‖z‖ →
      Contour.Cycle.windingNumber z (Contour.circleCycle 0 r) = 0 := fun r z hr hz ↦
    Contour.Cycle.windingNumber_circleCycle_eq_zero_of_lt_dist hr (by rwa [dist_zero_right])
  have hw1 : ∀ (r : ℝ) (z : ℂ), ‖z‖ < r →
      Contour.Cycle.windingNumber z (Contour.circleCycle 0 r) = 1 := fun r z hz ↦
    Contour.Cycle.windingNumber_circleCycle_eq_one_of_dist_lt (by rwa [dist_zero_right])
  refine ⟨?_, ?_, fun z hz ↦ ?_⟩
  · -- Each of the three circles lies in `U` and misses `σ`.
    refine ((Contour.Cycle.isIn_iff.mpr ?_).add (Contour.Cycle.isIn_iff.mpr ?_)).sub
      (Contour.Cycle.isIn_iff.mpr ?_) <;>
      rw [Contour.Cycle.trace_circleCycle] <;> intro z hz <;>
      rw [mem_sphere_zero_iff_norm] at hz
    · rw [abs_one] at hz
      refine ⟨Or.inl (show ‖z‖ < ρ₁ by linarith), fun hσ ↦ ?_⟩
      rcases hgap z hσ with h' | h' <;> linarith
    · rw [abs_of_pos hR0] at hz
      exact ⟨Or.inr (show ρ₂ < ‖z‖ by linarith), fun hσ ↦ (hσR z hσ).ne hz⟩
    · rw [abs_of_pos hs0] at hz
      refine ⟨Or.inr (show ρ₂ < ‖z‖ by linarith), fun hσ ↦ ?_⟩
      rcases hgap z hσ with h' | h' <;> linarith
  · -- Off `U`, that is for `ρ₁ ≤ ‖z‖ ≤ ρ₂`, the winding numbers are `0 + 1 - 1`.
    rw [Contour.Cycle.isNullHomologous_iff]
    intro z hz
    simp only [mem_union, mem_ofPred_eq, not_or, not_lt] at hz
    simp only [map_add, map_sub]
    rw [hw0 1 z zero_le_one (by linarith), hw1 R z (by linarith), hw1 s z (by linarith)]
    ring
  · -- Inside the unit disc they are `1 + 1 - 1`, beyond radius `m` they are `0 + 1 - 0`.
    simp only [map_add, map_sub]
    rw [hw1 R z (hσR z hz)]
    rcases hgap z hz with hz' | hz'
    · rw [hw1 1 z hz', hw1 s z (by linarith)]
      ring
    · rw [hw0 1 z zero_le_one (by linarith), hw0 s z hs0.le (by linarith)]
      ring

/-- A step of the proof of `unitDiscRieszProjection_eq_rieszIdempotent`: the function equal to
`f` on the disc `‖z‖ < ρ` and to `0` outside it has circle integral `0` over every circle of
radius `r > ρ ≥ 0` around `0`. -/
private theorem circleIntegral_ite_norm_lt_smul_eq_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (f : ℂ → E) {ρ r : ℝ} (hρ : 0 ≤ ρ) (hr : ρ < r) :
    ∮ z in C(0, r), (if ‖z‖ < ρ then (1 : ℂ) else 0) • f z = 0 := by
  rw [circleIntegral.integral_congr (by linarith) (g := fun _ ↦ (0 : E))]
  · simp [circleIntegral]
  · intro z hz
    rw [mem_sphere_zero_iff_norm] at hz
    simp [hz, hr.not_gt]

variable [CompleteSpace A]

/-- If the spectrum of `a` avoids the unit circle, `unitDiscRieszProjection a` is the Riesz
idempotent of the part of the spectrum in the open unit disc. -/
theorem unitDiscRieszProjection_eq_rieszIdempotent (a : A)
    (h : ∀ z ∈ spectrum ℂ a, ‖z‖ ≠ 1) :
    unitDiscRieszProjection a = rieszIdempotent a (unitDiscClopens a h) := by
  -- Radii `1 < ρ₁ < ρ₂ < s < m < R` with no point of the spectrum of norm in `[1, m)` and every
  -- point of norm `< R`.
  obtain ⟨m, hm, hgap⟩ := (spectrum.isCompact (𝕜 := ℂ) a).exists_lt_forall_norm_lt_or_le h
  obtain ⟨R, hR⟩ := (spectrum.isCompact (𝕜 := ℂ) a).isBounded.subset_ball 0
  obtain ⟨ρ₁, ρ₂, s, h1, h12, h2s, hsm⟩ : ∃ ρ₁ ρ₂ s : ℝ, 1 < ρ₁ ∧ ρ₁ < ρ₂ ∧ ρ₂ < s ∧ s < m :=
    ⟨1 + (m - 1) / 4, 1 + (m - 1) / 2, 1 + 3 * (m - 1) / 4, by linarith, by linarith,
      by linarith, by linarith⟩
  obtain ⟨R', hmR', hσR'⟩ : ∃ R' : ℝ, m < R' ∧ ∀ z ∈ spectrum ℂ a, ‖z‖ < R' :=
    ⟨max R m + 1, by linarith [le_max_right R m], fun z hz ↦ by
      linarith [mem_ball_zero_iff.mp (hR hz), le_max_left R m]⟩
  -- The neighbourhood `U` of the spectrum and the function `χ`, holomorphic and idempotent on
  -- `U`, equal to `1` exactly on the part of the spectrum in the unit disc.
  set U : Set ℂ := {z | ‖z‖ < ρ₁} ∪ {z | ρ₂ < ‖z‖}
  have hUo : IsOpen U :=
    (isOpen_lt (by fun_prop) continuous_const).union (isOpen_lt continuous_const (by fun_prop))
  have hσU : spectrum ℂ a ⊆ U := fun z hz ↦ by
    rcases hgap z hz with hz' | hz'
    · exact Or.inl (show ‖z‖ < ρ₁ by linarith)
    · exact Or.inr (show ρ₂ < ‖z‖ by linarith)
  set χ : ℂ → ℂ := fun z ↦ if ‖z‖ < ρ₁ then 1 else 0
  have hχ_in : ∀ z, ‖z‖ < ρ₁ → χ z = 1 := fun z hz ↦ ite_eq_left_iff.mpr fun h' ↦ (h' hz).elim
  have hχ_out : ∀ z, ρ₁ < ‖z‖ → χ z = 0 := fun z hz ↦
    ite_eq_right_iff.mpr fun h' ↦ (lt_asymm h' hz).elim
  have hχd : DifferentiableOn ℂ χ U := (Complex.differentiableOn_ite_norm_lt ρ₁).mono <| by
    rintro z (hz | hz) <;> simp only [mem_ofPred_eq] at hz ⊢ <;> [exact hz.ne; linarith]
  have hχi : ∀ z ∈ U, IsIdempotentElem (χ z) := fun z _ ↦ by
    simp only [χ]
    split_ifs
    exacts [IsIdempotentElem.one, IsIdempotentElem.zero]
  have hK : ∀ (x : ℂ) (hx : x ∈ spectrum ℂ a),
      χ x = 1 ↔ (⟨x, hx⟩ : spectrum ℂ a) ∈ unitDiscClopens a h := by
    intro x hx
    rw [mem_unitDiscClopens]
    rcases hgap x hx with hx' | hx'
    · simpa [hx'] using hχ_in x (by linarith)
    · have h1 : ¬ ‖x‖ < 1 := by linarith
      simp [h1, hχ_out x (by linarith)]
  -- Tau Ceti's contour formula on the cycle of `isIn_isNullHomologous_circleCycle`, whose
  -- two outer circles contribute nothing.
  obtain ⟨hΓ, hn, hw⟩ := isIn_isNullHomologous_circleCycle h1 h12 h2s hsm hgap hσR' hmR'
  rw [rieszIdempotent_eq_integral a _ hUo hσU hχd hχi hK _ hΓ hn hw, unitDiscRieszProjection_def]
  congr 1
  have hzero : ∀ r : ℝ, ρ₁ < r → ∮ z in C(0, r), χ z • resolvent a z = 0 := fun r hr ↦
    circleIntegral_ite_norm_lt_smul_eq_zero _ (by linarith) hr
  simp only [map_add, map_sub, Contour.Cycle.integral_circleCycle]
  rw [hzero R' (by linarith), hzero s (by linarith), add_zero, sub_zero]
  refine circleIntegral.integral_congr zero_le_one fun z hz ↦ ?_
  rw [mem_sphere_zero_iff_norm] at hz
  simp only [hχ_in z (by linarith), one_smul]

/-- If the spectrum of `a` avoids the unit circle, `unitDiscRieszProjection a` is idempotent. -/
theorem isIdempotentElem_unitDiscRieszProjection (a : A) (h : ∀ z ∈ spectrum ℂ a, ‖z‖ ≠ 1) :
    IsIdempotentElem (unitDiscRieszProjection a) := by
  rw [unitDiscRieszProjection_eq_rieszIdempotent a h]
  exact isIdempotentElem_rieszIdempotent a _

/-- Every element commuting with `a` commutes with `unitDiscRieszProjection a`. -/
theorem _root_.Commute.unitDiscRieszProjection_right {a b : A} (hb : Commute b a) :
    Commute b (unitDiscRieszProjection a) := by
  rw [unitDiscRieszProjection_def]
  refine Commute.smul_right ?_ _
  by_cases hi : CircleIntegrable (resolvent a) 0 1
  · have hl := (ContinuousLinearMap.mul ℂ A b).circleIntegral_comp_comm hi
    have hr := ((ContinuousLinearMap.mul ℂ A).flip b).circleIntegral_comp_comm hi
    simp only [ContinuousLinearMap.mul_apply', ContinuousLinearMap.flip_apply] at hl hr
    rw [Commute, SemiconjBy, ← hl, ← hr]
    exact circleIntegral.integral_congr zero_le_one fun z _ ↦ hb.resolvent_right z
  · rw [circleIntegral.integral_undef hi]
    exact Commute.zero_right b

/-- `a` commutes with its Riesz projection `unitDiscRieszProjection a`. -/
theorem commute_unitDiscRieszProjection (a : A) : Commute a (unitDiscRieszProjection a) :=
  (Commute.refl a).unitDiscRieszProjection_right


/-- The Riesz projection is continuous at every element whose spectrum avoids the unit circle. -/
theorem continuousAt_unitDiscRieszProjection {a : A} (h : ∀ z ∈ spectrum ℂ a, ‖z‖ ≠ 1) :
    ContinuousAt unitDiscRieszProjection a := by
  have hdisj (b : A) :
      Disjoint (sphere (0 : ℂ) 1) (spectrum ℂ b) ↔ ∀ z ∈ spectrum ℂ b, ‖z‖ ≠ 1 := by
    simp only [Set.disjoint_right, mem_sphere_zero_iff_norm, ne_eq]
  -- Near `a` the spectrum still avoids the unit circle, and there the integrand is continuous.
  have hS : {b : A | Disjoint (sphere (0 : ℂ) 1) (spectrum ℂ b)} ∈ 𝓝 a :=
    spectrum.eventually_disjoint_of_isClosed isClosed_sphere ((hdisj a).2 h)
  have hc : ContinuousOn (fun b : A ↦ unitDiscRieszProjection b)
      {b : A | Disjoint (sphere (0 : ℂ) 1) (spectrum ℂ b)} := by
    simp only [unitDiscRieszProjection_def, circleIntegral, deriv_circleMap]
    refine continuousOn_const.smul
      (continuousOn_parametric_intervalIntegral_of_continuousOn fun p hp ↦ ?_)
    have hz : circleMap 0 1 p.2 ∈ resolventSet ℂ p.1 :=
      spectrum.mem_resolventSet_iff.mpr
        (spectrum.notMem_iff.mp fun hσ ↦ (hdisj p.1).1 hp.1 _ hσ (by simp))
    refine (ContinuousAt.smul (by fun_prop) ?_).continuousWithinAt
    exact (spectrum.continuousAt_resolvent_prod hz).comp (f := fun q : A × ℝ ↦
      (q.1, circleMap 0 1 q.2)) (by fun_prop)
  exact hc.continuousAt hS

/-- The Riesz projection of a family continuous within `s` at `x`, whose spectrum at `x` avoids
the unit circle, is continuous within `s` at `x`. -/
@[fun_prop]
theorem _root_.ContinuousWithinAt.unitDiscRieszProjection {X : Type*} [TopologicalSpace X]
    {f : X → A} {s : Set X} {x : X} (hf : ContinuousWithinAt f s x)
    (h : ∀ z ∈ spectrum ℂ (f x), ‖z‖ ≠ 1) :
    ContinuousWithinAt (fun y ↦ unitDiscRieszProjection (f y)) s x :=
  (continuousAt_unitDiscRieszProjection h).comp_continuousWithinAt hf

/-- The Riesz projection of a family continuous at `x`, whose spectrum at `x` avoids the unit
circle, is continuous at `x`. -/
@[fun_prop]
theorem _root_.ContinuousAt.unitDiscRieszProjection {X : Type*} [TopologicalSpace X]
    {f : X → A} {x : X} (hf : ContinuousAt f x) (h : ∀ z ∈ spectrum ℂ (f x), ‖z‖ ≠ 1) :
    ContinuousAt (fun y ↦ unitDiscRieszProjection (f y)) x :=
  (continuousAt_unitDiscRieszProjection h).comp hf

/-- The Riesz projection of a family continuous on `s`, whose spectra on `s` avoid the unit
circle, is continuous on `s`. -/
@[fun_prop]
theorem _root_.ContinuousOn.unitDiscRieszProjection {X : Type*} [TopologicalSpace X]
    {f : X → A} {s : Set X} (hf : ContinuousOn f s)
    (h : ∀ x ∈ s, ∀ z ∈ spectrum ℂ (f x), ‖z‖ ≠ 1) :
    ContinuousOn (fun x ↦ unitDiscRieszProjection (f x)) s :=
  fun x hx ↦ (hf x hx).unitDiscRieszProjection (h x hx)

/-- The Riesz projection depends continuously on the element, along a continuous family whose
spectra avoid the unit circle. -/
@[continuity, fun_prop]
theorem _root_.Continuous.unitDiscRieszProjection {X : Type*} [TopologicalSpace X] {f : X → A}
    (hf : Continuous f) (h : ∀ x, ∀ z ∈ spectrum ℂ (f x), ‖z‖ ≠ 1) :
    Continuous fun x ↦ unitDiscRieszProjection (f x) :=
  continuous_iff_continuousAt.mpr fun x ↦ hf.continuousAt.unitDiscRieszProjection (h x)

end SymplecticGeometry

namespace SymplecticGeometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
/-- The Riesz projection of the conjugate `e ∘ T ∘ e⁻¹` of an operator `T` is the conjugate of
the Riesz projection of `T`. -/
theorem unitDiscRieszProjection_conjContinuousAlgEquiv (e : E ≃L[ℂ] F) (T : E →L[ℂ] E) :
    unitDiscRieszProjection (e.conjContinuousAlgEquiv T) =
      e.conjContinuousAlgEquiv (unitDiscRieszProjection T) :=
  (map_unitDiscRieszProjection _ T).symm

/-- If the spectrum of `T` avoids the unit circle, no nonzero vector in the kernel of
`unitDiscRieszProjection T` is an eigenvector of `T` for an eigenvalue `w` with `‖w‖ ≤ 1`. -/
theorem eq_zero_of_unitDiscRieszProjection_apply_eq_zero {T : E →L[ℂ] E}
    (h : ∀ z ∈ spectrum ℂ T, ‖z‖ ≠ 1) {v : E} (hP : unitDiscRieszProjection T v = 0) {w : ℂ}
    (hw : ‖w‖ ≤ 1) (hT : T v = w • v) : v = 0 := by
  by_contra hv
  have hP' : rieszIdempotent T (unitDiscClopens T h)ᶜ v = v := by
    rw [rieszIdempotent_compl, ← unitDiscRieszProjection_eq_rieszIdempotent T h]
    simp [hP]
  obtain ⟨z, hz, rfl⟩ :=
    ContinuousLinearMap.mem_image_of_rieszIdempotent_apply_eq_self _ hv hP' hT
  have hz' : ¬ ‖(z : ℂ)‖ < 1 := by simpa using hz
  exact h z z.property (le_antisymm hw (not_lt.mp hz'))

/-- If the spectrum of `T` avoids the unit circle, no nonzero vector `v` in the range of
`unitDiscRieszProjection T` satisfies `w • T v = v` for a scalar `w` with `‖w‖ ≤ 1`: the
eigenvalues of `T` on this range have norm `< 1`. -/
theorem eq_zero_of_unitDiscRieszProjection_apply_eq_self {T : E →L[ℂ] E}
    (h : ∀ z ∈ spectrum ℂ T, ‖z‖ ≠ 1) {v : E} (hP : unitDiscRieszProjection T v = v) {w : ℂ}
    (hw : ‖w‖ ≤ 1) (hT : w • T v = v) : v = 0 := by
  by_contra hv
  have hw0 : w ≠ 0 := by rintro rfl; simp at hT; exact hv hT.symm
  have hT' : T v = w⁻¹ • v := (eq_inv_smul_iff₀ hw0).mpr hT
  rw [unitDiscRieszProjection_eq_rieszIdempotent T h] at hP
  obtain ⟨z, hz, hzw⟩ :=
    ContinuousLinearMap.mem_image_of_rieszIdempotent_apply_eq_self _ hv hP hT'
  have hz' : ‖(z : ℂ)‖ < 1 := by simpa using hz
  rw [hzw, norm_inv] at hz'
  have := (inv_lt_one₀ (norm_pos_iff.mpr hw0)).mp hz'
  linarith

end SymplecticGeometry

end
