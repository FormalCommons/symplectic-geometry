/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Normed.Algebra.HolomorphicFunctionalCalculus.Riesz
public import TauCeti.MeasureTheory.Integral.Circle.Integral

/-!
# The Riesz projection onto the spectrum inside the unit disc

For an element `a` of a complex Banach algebra `A`, `unitDiscRieszProjection a` is the contour
integral `(2πi)⁻¹ ∮_{|z| = 1} (z1 - a)⁻¹ dz` of Mathlib's `resolvent` over the unit circle.

When no point of the spectrum of `a` lies on the unit circle, the part of the spectrum in the
open unit disc is a clopen part `unitDiscClopens a h` of it, and the integral is Tau Ceti's Riesz
idempotent of that part (`unitDiscRieszProjection_eq_rieszIdempotent`). To see this, the unit
circle is completed by a large circle and a circle just outside the unit disc, taken with the
opposite orientation, to a cycle winding once around the whole spectrum, on which the function
equal to `1` inside the unit disc and to `0` outside it is holomorphic. Hence
`unitDiscRieszProjection a` is an idempotent commuting with `a`, and for an operator `T`
on a complex Banach space an eigenvector of `T` lies in its kernel only for an eigenvalue of norm
`> 1` and in its range only for an eigenvalue of norm `< 1`.

The projection is natural under continuous algebra isomorphisms, in particular under conjugation
of operators by an isomorphism of Banach spaces, and depends continuously on `a` as long as the
spectrum avoids the unit circle.

## Main results

* `SymplecticGeometry.unitDiscRieszProjection`: the contour integral above.
* `SymplecticGeometry.unitDiscRieszProjection_eq_rieszIdempotent`: it is the Riesz idempotent of
  the part of the spectrum in the open unit disc.
* `SymplecticGeometry.isIdempotentElem_unitDiscRieszProjection`,
  `SymplecticGeometry.commute_unitDiscRieszProjection`: it is an idempotent commuting with `a`.
* `SymplecticGeometry.map_unitDiscRieszProjection`,
  `ContinuousLinearMap.unitDiscRieszProjection_conjContinuousAlgEquiv`: naturality.
* `Continuous.unitDiscRieszProjection`: continuity in a family.
* `ContinuousLinearMap.eq_zero_of_unitDiscRieszProjection_apply_eq_zero`,
  `ContinuousLinearMap.eq_zero_of_unitDiscRieszProjection_apply_eq_self`: where the eigenvalues
  of the two pieces lie.

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

/-- The resolvent `(a, z) ↦ (z1 - a)⁻¹` is jointly continuous at every point `(a, z)` with `z` in
the resolvent set of `a`. -/
theorem spectrum.continuousAt_resolvent_prod {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] {a : A} {z : ℂ} (hz : z ∈ resolventSet ℂ a) :
    ContinuousAt (fun p : A × ℂ ↦ resolvent p.1 p.2) (a, z) := by
  have hu := spectrum.mem_resolventSet_iff.mp hz
  simp only [resolvent]
  refine ContinuousAt.comp_of_eq (NormedRing.inverse_continuousAt hu.unit) ?_ hu.unit_spec.symm
  fun_prop

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

variable [CompleteSpace A] [CompleteSpace B]

/-- If the spectrum of `a` avoids the unit circle, it has a gap: it avoids an annulus
`1 ≤ ‖z‖ < m` with `1 < m`. -/
theorem exists_one_lt_forall_mem_spectrum (a : A) (h : ∀ z ∈ spectrum ℂ a, ‖z‖ ≠ 1) :
    ∃ m : ℝ, 1 < m ∧ ∀ z ∈ spectrum ℂ a, ‖z‖ < 1 ∨ m ≤ ‖z‖ := by
  set S := spectrum ℂ a ∩ {z | 1 ≤ ‖z‖}
  have hS : IsCompact S :=
    (spectrum.isCompact (𝕜 := ℂ) a).inter_right (isClosed_le (by fun_prop) (by fun_prop))
  rcases S.eq_empty_or_nonempty with hS₀ | hS₀
  · refine ⟨2, one_lt_two, fun z hz ↦ Or.inl (not_le.mp fun hz' ↦ ?_)⟩
    exact (Set.eq_empty_iff_forall_notMem.mp hS₀) z ⟨hz, hz'⟩
  · obtain ⟨z₀, ⟨hz₀, hz₀'⟩, hmin⟩ := hS.exists_isMinOn hS₀ continuous_norm.continuousOn
    refine ⟨‖z₀‖, lt_of_le_of_ne hz₀' (h z₀ hz₀).symm, fun z hz ↦ ?_⟩
    rcases lt_or_ge ‖z‖ 1 with hz' | hz'
    · exact Or.inl hz'
    · exact Or.inr (hmin ⟨hz, hz'⟩)

/-- If the spectrum of `a` avoids the unit circle, `unitDiscRieszProjection a` is the Riesz
idempotent of the part of the spectrum in the open unit disc. -/
theorem unitDiscRieszProjection_eq_rieszIdempotent (a : A)
    (h : ∀ z ∈ spectrum ℂ a, ‖z‖ ≠ 1) :
    unitDiscRieszProjection a = rieszIdempotent a (unitDiscClopens a h) := by
  obtain ⟨m, hm, hgap⟩ := exists_one_lt_forall_mem_spectrum a h
  obtain ⟨R, hR⟩ := (spectrum.isCompact (𝕜 := ℂ) a).isBounded.subset_ball 0
  obtain ⟨ρ₁, ρ₂, s, h1, h12, h2s, hsm⟩ : ∃ ρ₁ ρ₂ s : ℝ, 1 < ρ₁ ∧ ρ₁ < ρ₂ ∧ ρ₂ < s ∧ s < m :=
    ⟨1 + (m - 1) / 4, 1 + (m - 1) / 2, 1 + 3 * (m - 1) / 4, by linarith, by linarith,
      by linarith, by linarith⟩
  obtain ⟨R', hmR', hσR'⟩ : ∃ R' : ℝ, m < R' ∧ ∀ z ∈ spectrum ℂ a, ‖z‖ < R' :=
    ⟨max R m + 1, by linarith [le_max_right R m], fun z hz ↦ by
      linarith [mem_ball_zero_iff.mp (hR hz), le_max_left R m]⟩
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
  have hχd : DifferentiableOn ℂ χ U := by
    rintro z (hz | hz)
    · refine (differentiableAt_const (1 : ℂ)).congr_of_eventuallyEq ?_ |>.differentiableWithinAt
      filter_upwards [(isOpen_lt (by fun_prop) continuous_const).mem_nhds hz] with w hw
      exact hχ_in w hw
    · refine (differentiableAt_const (0 : ℂ)).congr_of_eventuallyEq ?_ |>.differentiableWithinAt
      have hz' : ρ₁ < ‖z‖ := by simp only [mem_ofPred_eq] at hz; linarith
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hz'] with w hw
      exact hχ_out w hw
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
  set Γ := Contour.circleCycle 0 1 + Contour.circleCycle 0 R' - Contour.circleCycle 0 s
  have hR'0 : 0 < R' := by linarith
  have hs0 : 0 < s := by linarith
  have hΓ : Γ.IsIn (U \ spectrum ℂ a) := by
    refine ((Contour.Cycle.isIn_iff.mpr ?_).add (Contour.Cycle.isIn_iff.mpr ?_)).sub
      (Contour.Cycle.isIn_iff.mpr ?_) <;>
      rw [Contour.Cycle.trace_circleCycle] <;> intro z hz <;>
      rw [mem_sphere_zero_iff_norm] at hz
    · rw [abs_one] at hz
      exact ⟨Or.inl (show ‖z‖ < ρ₁ by linarith), fun hσ ↦ h z hσ hz⟩
    · rw [abs_of_pos hR'0] at hz
      exact ⟨Or.inr (show ρ₂ < ‖z‖ by linarith), fun hσ ↦ (hσR' z hσ).ne hz⟩
    · rw [abs_of_pos hs0] at hz
      refine ⟨Or.inr (show ρ₂ < ‖z‖ by linarith), fun hσ ↦ ?_⟩
      rcases hgap z hσ with h' | h' <;> linarith
  have hw0 : ∀ (r : ℝ) (z : ℂ), 0 ≤ r → r < ‖z‖ →
      Contour.Cycle.windingNumber z (Contour.circleCycle 0 r) = 0 := fun r z hr hz ↦
    Contour.Cycle.windingNumber_circleCycle_eq_zero_of_lt_dist hr (by rwa [dist_zero_right])
  have hw1 : ∀ (r : ℝ) (z : ℂ), ‖z‖ < r →
      Contour.Cycle.windingNumber z (Contour.circleCycle 0 r) = 1 := fun r z hz ↦
    Contour.Cycle.windingNumber_circleCycle_eq_one_of_dist_lt (by rwa [dist_zero_right])
  have hn : Γ.IsNullHomologous U := by
    rw [Contour.Cycle.isNullHomologous_iff]
    intro z hz
    simp only [U, mem_union, mem_ofPred_eq, not_or, not_lt] at hz
    simp only [Γ, map_add, map_sub]
    rw [hw0 1 z zero_le_one (by linarith), hw1 R' z (by linarith), hw1 s z (by linarith)]
    ring
  have hw : ∀ z ∈ spectrum ℂ a, Contour.Cycle.windingNumber z Γ = 1 := by
    intro z hz
    simp only [Γ, map_add, map_sub]
    rw [hw1 R' z (hσR' z hz)]
    rcases hgap z hz with hz' | hz'
    · rw [hw1 1 z hz', hw1 s z (by linarith)]
      ring
    · rw [hw0 1 z zero_le_one (by linarith), hw0 s z hs0.le (by linarith)]
      ring
  rw [rieszIdempotent_eq_integral a _ hUo hσU hχd hχi hK Γ hΓ hn hw, unitDiscRieszProjection_def]
  congr 1
  have hzero : ∀ r : ℝ, ρ₁ < r → ∮ z in C(0, r), χ z • resolvent a z = 0 := fun r hr ↦ by
    rw [circleIntegral.integral_congr (by linarith) (g := fun _ ↦ (0 : A))]
    · simp [circleIntegral]
    · intro z hz
      rw [mem_sphere_zero_iff_norm] at hz
      simp only [hχ_out z (hz ▸ hr), zero_smul]
  simp only [Γ, map_add, map_sub, Contour.Cycle.integral_circleCycle]
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

theorem commute_unitDiscRieszProjection (a : A) : Commute a (unitDiscRieszProjection a) :=
  (Commute.refl a).unitDiscRieszProjection_right

/-- `unitDiscRieszProjection` is natural under continuous algebra isomorphisms. -/
theorem map_unitDiscRieszProjection (φ : A ≃A[ℂ] B) (a : A) :
    φ (unitDiscRieszProjection a) = unitDiscRieszProjection (φ a) := by
  have hres : ∀ z : ℂ, φ (resolvent a z) = resolvent (φ a) z := fun z ↦ by
    simp only [resolvent]
    rw [map_ringInverse φ, map_sub, AlgHomClass.commutes φ]
  let L : A →L[ℂ] B := φ.toContinuousLinearEquiv
  have hL : ∀ x, L x = φ x := φ.toContinuousLinearEquiv_apply
  rw [unitDiscRieszProjection_def, unitDiscRieszProjection_def, map_smul]
  congr 1
  by_cases hi : CircleIntegrable (resolvent a) 0 1
  · rw [← hL, ← L.circleIntegral_comp_comm hi]
    simp only [hL, hres]
  · have hi' : ¬ CircleIntegrable (resolvent (φ a)) 0 1 := fun hi' ↦ by
      let L' : B →L[ℂ] A := φ.symm.toContinuousLinearEquiv
      have hL' : ∀ z, L' (resolvent (φ a) z) = resolvent a z := fun z ↦ by
        rw [← hres, ContinuousLinearEquiv.coe_coe, ContinuousAlgEquiv.toContinuousLinearEquiv_apply,
          ContinuousAlgEquiv.symm_apply_apply]
      have h' := (circleIntegrable_def _ _ _).mp hi'
      refine hi ((circleIntegrable_def _ _ _).mpr ⟨?_, ?_⟩)
      · simpa only [Function.comp_def, hL'] using L'.integrableOn_comp h'.1
      · simpa only [Function.comp_def, hL'] using L'.integrableOn_comp h'.2
    rw [circleIntegral.integral_undef hi, circleIntegral.integral_undef hi', map_zero]

/-- The Riesz projection depends continuously on the element, along a continuous family whose
spectra avoid the unit circle. -/
theorem _root_.Continuous.unitDiscRieszProjection {X : Type*} [TopologicalSpace X] {f : X → A}
    (hf : Continuous f) (h : ∀ x, ∀ z ∈ spectrum ℂ (f x), ‖z‖ ≠ 1) :
    Continuous fun x ↦ unitDiscRieszProjection (f x) := by
  simp only [unitDiscRieszProjection_def, circleIntegral, deriv_circleMap]
  refine continuous_const.smul
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ _ _)
  refine continuous_iff_continuousAt.mpr fun p ↦ ?_
  have hz : circleMap 0 1 p.2 ∈ resolventSet ℂ (f p.1) := by
    refine spectrum.mem_resolventSet_iff.mpr
      (spectrum.notMem_iff.mp fun hσ ↦ h p.1 _ hσ ?_)
    simp
  refine ContinuousAt.smul (by fun_prop) ?_
  exact (spectrum.continuousAt_resolvent_prod hz).comp (f := fun q : X × ℝ ↦
    (f q.1, circleMap 0 1 q.2)) (by fun_prop)

end SymplecticGeometry

namespace ContinuousLinearMap

open SymplecticGeometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- The Riesz projection of the conjugate `e ∘ T ∘ e⁻¹` of an operator `T` is the conjugate of
the Riesz projection of `T`. -/
theorem unitDiscRieszProjection_conjContinuousAlgEquiv (e : E ≃L[ℂ] F) (T : E →L[ℂ] E) :
    unitDiscRieszProjection (e.conjContinuousAlgEquiv T) =
      e.conjContinuousAlgEquiv (unitDiscRieszProjection T) :=
  (map_unitDiscRieszProjection _ T).symm

/-- If a vector `v` in the range of the Riesz idempotent of a clopen part `K` of the spectrum of
`T` is an eigenvector of `T` for the eigenvalue `μ`, then `μ` lies in `K`. -/
theorem mem_image_of_rieszIdempotent_apply_eq_self {T : E →L[ℂ] E}
    (K : Clopens (spectrum ℂ T)) {v : E} (hv : v ≠ 0) (hP : rieszIdempotent T K v = v) {μ : ℂ}
    (hT : T v = μ • v) : μ ∈ ((↑) '' (K : Set (spectrum ℂ T)) : Set ℂ) := by
  by_contra hμ
  obtain ⟨u, hu⟩ := (isUnit_sub_mul_rieszIdempotent_add_iff T K μ).mpr hμ
  refine hv ?_
  have h0 : (↑u : E →L[ℂ] E) v = 0 := by
    rw [hu]
    simp [hP, hT, Algebra.algebraMap_eq_smul_one]
  have h1 := congrArg (↑u⁻¹ : E →L[ℂ] E) h0
  rwa [← mul_apply_eq_comp, Units.inv_mul, one_apply_eq_self,
    map_zero] at h1

/-- If the spectrum of `T` avoids the unit circle, no nonzero vector in the kernel of
`unitDiscRieszProjection T` is an eigenvector of `T` for an eigenvalue `w` with `‖w‖ ≤ 1`. -/
theorem eq_zero_of_unitDiscRieszProjection_apply_eq_zero {T : E →L[ℂ] E}
    (h : ∀ z ∈ spectrum ℂ T, ‖z‖ ≠ 1) {v : E} (hP : unitDiscRieszProjection T v = 0) {w : ℂ}
    (hw : ‖w‖ ≤ 1) (hT : T v = w • v) : v = 0 := by
  by_contra hv
  have hP' : rieszIdempotent T (unitDiscClopens T h)ᶜ v = v := by
    rw [rieszIdempotent_compl, ← unitDiscRieszProjection_eq_rieszIdempotent T h]
    simp [hP]
  obtain ⟨z, hz, rfl⟩ := mem_image_of_rieszIdempotent_apply_eq_self _ hv hP' hT
  have hz' : ¬ ‖(z : ℂ)‖ < 1 := hz
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
  obtain ⟨z, hz, hzw⟩ := mem_image_of_rieszIdempotent_apply_eq_self _ hv hP hT'
  have hz' : ‖(z : ℂ)‖ < 1 := hz
  rw [hzw, norm_inv] at hz'
  have := (inv_lt_one₀ (norm_pos_iff.mpr hw0)).mp hz'
  linarith

end ContinuousLinearMap

end
