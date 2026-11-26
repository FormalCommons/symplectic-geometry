/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Analysis.InnerProductSpace.Symplectic.LinearWidth.Basic
public import TauCeti.Geometry.Symplectic.WittExtension
import SymplecticGeometry.Analysis.InnerProductSpace.Ellipsoid
import SymplecticGeometry.LinearAlgebra.BilinearMap.Sign

/-!
# Linear symplectic rigidity

A linear map `Ψ` of the standard model `StdSpace ι = ℝ²ⁿ` has the *linear nonsqueezing property*
(`SymplecticGeometry.HasLinearNonsqueezing`) if it sends the image of a ball `B²ⁿ(r)` under a
linear symplectomorphism into the image of a cylinder `Z²ⁿ(R)` under a linear symplectomorphism
only when `r ≤ R`. Linear symplectomorphisms have it, by the affine nonsqueezing theorem, and so
do the anti-symplectic linear maps.

Conversely, for a linear equivalence `Ψ`, `HasLinearNonsqueezing Ψ` together with
`HasLinearNonsqueezing Ψ⁻¹` forces `Ψ^* ω₀ = ±ω₀` (McDuff–Salamon, Theorem 2.4.2). The proof
here works with the transpose `Ψᵀ` (the adjoint for the standard inner product). If
`ω₀(a, b) = 1`, Witt's theorem gives a linear symplectomorphism that carries the cylinder over
the first coordinate plane to
`{z | ⟪a, z⟫² + ⟪b, z⟫² ≤ 1}`, and, when `λ = ω₀(Ψᵀ a, Ψᵀ b)` is not zero, one that moves the
pair `(Ψᵀ a, Ψᵀ b)` to `(√|λ| e, ±√|λ| f)` for the first pair of coordinate vectors `e`, `f`.
Then `Ψ` sends a linear symplectic ball of radius `1 / √|λ|` into a linear symplectic cylinder of
radius `1`, so the property gives `|λ| ≥ 1`. The case `λ = 0` is reduced to this one by
changing `b`. By homogeneity `|ω₀(a, b)| ≤ |ω₀(Ψᵀ a, Ψᵀ b)|` for all `a`, `b`; the property of
`Ψ⁻¹` gives the reverse inequality, and `LinearMap.eq_or_eq_neg_of_forall_sq_eq_sq₂` turns the
equality of absolute values into `(Ψᵀ)^* ω₀ = ±ω₀`, hence `Ψ^* ω₀ = ±ω₀`.

Finally, for any linear map `Ψ`, the identity `Ψ^* ω₀ = ±ω₀` is equivalent to the equality
`linearSymplecticWidth (Ψ '' E) = linearSymplecticWidth E` for all ellipsoids `E = {z | Q z ≤ 1}`
(McDuff–Salamon, Theorem 2.4.4). For the nontrivial direction, `Ψ` is onto, since the image of
the unit ball has positive width; images of balls are ellipsoids, of width `π r²`, and images of
cylinders have width `π R²`, so the map and its inverse have the linear nonsqueezing property.

## Main definitions

* `SymplecticGeometry.HasLinearNonsqueezing Ψ`: the linear nonsqueezing property.

## Main results

* `TauCeti.SymplecticForm.IsSymplectomorphism.hasLinearNonsqueezing` and
  `SymplecticGeometry.hasLinearNonsqueezing_of_forall_apply_eq_or_forall_apply_eq_neg`: linear
  maps with `Ψ^* ω₀ = ±ω₀` have the linear nonsqueezing property.
* `SymplecticGeometry.HasLinearNonsqueezing.abs_stdForm_le_abs_stdForm_adjointEquiv`: the
  transpose of a map with the property does not decrease `|ω₀|`.
* `SymplecticGeometry.forall_apply_eq_or_forall_apply_eq_neg_of_hasLinearNonsqueezing`: affine
  rigidity, and `SymplecticGeometry.hasLinearNonsqueezing_and_hasLinearNonsqueezing_symm_iff`,
  its converse included.
* `SymplecticGeometry.forall_linearSymplecticWidth_image_eq_iff`: `Ψ^* ω₀ = ±ω₀` holds exactly
  when `Ψ` leaves unchanged the width of each ellipsoid `{z | Q z ≤ 1}`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.4
-/

public section

namespace SymplecticGeometry

open TauCeti Metric
open scoped ENNReal Real

variable {ι : Type*} [Fintype ι]

/-- A linear map `Ψ` of the standard model has the linear nonsqueezing property if, whenever it
sends the image `φ (B²ⁿ(r))` of a closed ball of radius `r ≥ 0` under a linear symplectomorphism
`φ` into the image `θ (Z²ⁿ(R))` of a cylinder under a linear symplectomorphism `θ`, then
`r ≤ R`. -/
def HasLinearNonsqueezing (Ψ : StdSpace ι →ₗ[ℝ] StdSpace ι) : Prop :=
  ∀ (φ θ : StdSpace ι ≃ₗ[ℝ] StdSpace ι),
    (stdForm ι).IsSymplectomorphism (stdForm ι) φ →
    (stdForm ι).IsSymplectomorphism (stdForm ι) θ →
    ∀ (i : ι) (r R : ℝ), 0 ≤ r →
      Ψ '' (φ '' closedBall 0 r) ⊆ θ '' stdCylinder i R → r ≤ R

/-- Unfolds `HasLinearNonsqueezing`. -/
theorem hasLinearNonsqueezing_iff {Ψ : StdSpace ι →ₗ[ℝ] StdSpace ι} :
    HasLinearNonsqueezing Ψ ↔
      ∀ (φ θ : StdSpace ι ≃ₗ[ℝ] StdSpace ι),
        (stdForm ι).IsSymplectomorphism (stdForm ι) φ →
        (stdForm ι).IsSymplectomorphism (stdForm ι) θ →
        ∀ (i : ι) (r R : ℝ), 0 ≤ r →
          Ψ '' (φ '' closedBall 0 r) ⊆ θ '' stdCylinder i R → r ≤ R :=
  Iff.rfl

/-- A linear map has the linear nonsqueezing property as soon as it does not decrease the width
of the images of balls of positive radius under linear symplectomorphisms: these images have
width `π r²`, and the images of cylinders of radius `R` have width at most `π R²`. -/
theorem hasLinearNonsqueezing_of_forall_linearSymplecticWidth_le
    {Ψ : StdSpace ι →ₗ[ℝ] StdSpace ι}
    (h : ∀ φ : StdSpace ι ≃ₗ[ℝ] StdSpace ι, (stdForm ι).IsSymplectomorphism (stdForm ι) φ →
      ∀ r : ℝ, 0 < r → linearSymplecticWidth (φ '' closedBall 0 r) ≤
        linearSymplecticWidth (Ψ '' (φ '' closedBall 0 r))) :
    HasLinearNonsqueezing Ψ := by
  intro φ θ hφ hθ i r R hr hsub
  have hR : 0 ≤ R := by
    by_contra! hR
    rw [stdCylinder_eq_empty hR, Set.image_empty] at hsub
    exact hsub ⟨φ 0, ⟨0, mem_closedBall_self hr, rfl⟩, rfl⟩
  rcases hr.eq_or_lt with rfl | hr'
  · exact hR
  have : Nonempty ι := ⟨i⟩
  have hball := linearSymplecticWidth_image_closedBall
    ((LinearEquiv.toAffineEquiv_mem_affineSymplecticGroup_iff φ).2 hφ) 0 hr
  have hcyl := linearSymplecticWidth_image
    ((LinearEquiv.toAffineEquiv_mem_affineSymplecticGroup_iff θ).2 hθ) (stdCylinder i R)
  rw [LinearEquiv.coe_toAffineEquiv] at hball hcyl
  have hle := ((h φ hφ r hr').trans (linearSymplecticWidth_mono hsub)).trans
    (hcyl.le.trans (linearSymplecticWidth_stdCylinder_le i R))
  rw [hball, ENNReal.ofReal_le_ofReal_iff (by positivity)] at hle
  exact (pow_le_pow_iff_left₀ hr hR two_ne_zero).1 (le_of_mul_le_mul_left hle Real.pi_pos)

/-- A linear map `Ψ` with `Ψ^* ω₀ = ω₀` or `Ψ^* ω₀ = -ω₀` has the linear nonsqueezing
property. -/
theorem hasLinearNonsqueezing_of_forall_apply_eq_or_forall_apply_eq_neg
    {Ψ : StdSpace ι →ₗ[ℝ] StdSpace ι}
    (hΨ : (∀ z w, stdForm ι (Ψ z) (Ψ w) = stdForm ι z w) ∨
      ∀ z w, stdForm ι (Ψ z) (Ψ w) = -stdForm ι z w) :
    HasLinearNonsqueezing Ψ :=
  hasLinearNonsqueezing_of_forall_linearSymplecticWidth_le fun _ _ _ _ ↦
    (linearSymplecticWidth_image_of_forall_apply_eq_or_forall_apply_eq_neg hΨ _).ge

/-! ### Affine rigidity -/

/-- The key step of affine rigidity: if `Ψ` has the linear nonsqueezing property, `ω₀(a, b) = 1`
and `λ = ω₀(Ψᵀ a, Ψᵀ b)` is not zero, then `|λ| ≥ 1`. If `|λ| < 1`, Witt's theorem gives a
linear symplectic cylinder of radius `1` defined by `a` and `b`, and a linear symplectic ball of
radius `|λ|^(-1/2) > 1` that `Ψ` sends into it. -/
private theorem one_le_abs_stdForm_adjointEquiv_of_ne_zero {Ψ : StdSpace ι ≃ₗ[ℝ] StdSpace ι}
    (h : HasLinearNonsqueezing (Ψ : StdSpace ι →ₗ[ℝ] StdSpace ι)) {a b : StdSpace ι}
    (hab : stdForm ι a b = 1)
    (hne : stdForm ι (ContinuousLinearEquiv.adjointEquiv Ψ.toContinuousLinearEquiv a)
      (ContinuousLinearEquiv.adjointEquiv Ψ.toContinuousLinearEquiv b) ≠ 0) :
    1 ≤ |stdForm ι (ContinuousLinearEquiv.adjointEquiv Ψ.toContinuousLinearEquiv a)
      (ContinuousLinearEquiv.adjointEquiv Ψ.toContinuousLinearEquiv b)| := by
  classical
  set A := ContinuousLinearEquiv.adjointEquiv Ψ.toContinuousLinearEquiv
  set l := stdForm ι (A a) (A b)
  obtain ⟨i⟩ : Nonempty ι := by
    by_contra! hι
    simp at hab
  set s := √|l|
  set t := l / s
  have hs : 0 < s := Real.sqrt_pos.2 (abs_pos.2 hne)
  have hs2 : s ^ 2 = |l| := Real.sq_sqrt (abs_nonneg l)
  have ht2 : t ^ 2 = |l| := by
    rw [div_pow, hs2, ← sq_abs, sq, mul_div_assoc, div_self (abs_pos.2 hne).ne', mul_one]
  set e := EuclideanSpace.single (Sum.inl i : ι ⊕ ι) (1 : ℝ)
  set f := EuclideanSpace.single (Sum.inr i : ι ⊕ ι) (1 : ℝ)
  have hef : stdForm ι e f = 1 := by simp [e, f, StdSpace.x_apply, StdSpace.y_apply]
  obtain ⟨σ, hσ, hσe, hσf⟩ := SymplecticForm.exists_isSymplectomorphism_apply_eq rfl hef hab
  obtain ⟨τ, hτ, hτe, hτf⟩ := SymplecticForm.exists_isSymplectomorphism_apply_eq
    (ω₁ := stdForm ι) (ω₂ := stdForm ι) (q' := s⁻¹ • A a) (p' := t⁻¹ • A b) rfl hef (by
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
      rw [← mul_assoc, ← mul_inv, show t * s = l from div_mul_cancel₀ l hs.ne']
      exact inv_mul_cancel₀ hne)
  have ht : t ≠ 0 := div_ne_zero hne hs.ne'
  set θ := (ContinuousLinearEquiv.adjointEquiv σ.toContinuousLinearEquiv).symm.toLinearEquiv
  set φ := (ContinuousLinearEquiv.adjointEquiv τ.symm.toContinuousLinearEquiv).toLinearEquiv
  have hτa : τ.symm (A a) = s • e := by
    rw [LinearEquiv.symm_apply_eq, map_smul, hτe, smul_inv_smul₀ hs.ne']
  have hτb : τ.symm (A b) = t • f := by
    rw [LinearEquiv.symm_apply_eq, map_smul, hτf, smul_inv_smul₀ ht]
  -- `⟪u, Ψ (φ z)⟫ = ⟪τ⁻¹ (Ψᵀ u), z⟫`
  have hinner (u z : StdSpace ι) : inner ℝ u (Ψ (φ z)) = inner ℝ (τ.symm (A u)) z := by
    simp only [A, φ, ContinuousLinearEquiv.coe_toLinearEquiv,
      ContinuousLinearEquiv.adjointEquiv_apply]
    rw [← LinearEquiv.coe_toContinuousLinearEquiv' Ψ, ← ContinuousLinearEquiv.coe_coe,
      ← ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right]
    simp only [ContinuousLinearEquiv.coe_coe, LinearEquiv.coe_toContinuousLinearEquiv']
  have key := h φ θ hτ.symm.adjoint hσ.adjoint.symm i s⁻¹ 1 (inv_nonneg.2 hs.le) (by
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    rw [ContinuousLinearEquiv.coe_toLinearEquiv,
      image_adjointEquiv_symm_stdCylinder σ i zero_le_one,
      Set.mem_ofPred_eq, LinearEquiv.coe_coe, hσe, hσf, hinner, hinner, hτa, hτb,
      real_inner_smul_left,
      real_inner_smul_left]
    simp only [e, f, EuclideanSpace.inner_single_left, map_one, one_mul]
    have hn := StdSpace.sq_x_add_sq_y_le_norm_sq z i
    rw [StdSpace.x_apply, StdSpace.y_apply] at hn
    have hz' : ‖z‖ ≤ s⁻¹ := mem_closedBall_zero_iff.1 hz
    calc (s * z (Sum.inl i)) ^ 2 + (t * z (Sum.inr i)) ^ 2
        = |l| * (z (Sum.inl i) ^ 2 + z (Sum.inr i) ^ 2) := by
          rw [mul_pow, mul_pow, hs2, ht2]; ring
      _ ≤ |l| * ‖z‖ ^ 2 := by gcongr
      _ ≤ |l| * s⁻¹ ^ 2 := by gcongr
      _ = 1 ^ 2 := by rw [← hs2]; field_simp)
  rw [← hs2]
  exact one_le_pow₀ ((inv_le_one₀ hs).1 key)

/-- The case `ω₀(Ψᵀ a, Ψᵀ b) = 0` reduces to `one_le_abs_stdForm_adjointEquiv_of_ne_zero`:
replacing `b` by a suitable `b + (d - ω₀(a, d) b) / 2` keeps `ω₀(a, b) = 1` and makes
`ω₀(Ψᵀ a, Ψᵀ b) = 1 / 2`. -/
private theorem one_le_abs_stdForm_adjointEquiv {Ψ : StdSpace ι ≃ₗ[ℝ] StdSpace ι}
    (h : HasLinearNonsqueezing (Ψ : StdSpace ι →ₗ[ℝ] StdSpace ι)) {a b : StdSpace ι}
    (hab : stdForm ι a b = 1) :
    1 ≤ |stdForm ι (ContinuousLinearEquiv.adjointEquiv Ψ.toContinuousLinearEquiv a)
      (ContinuousLinearEquiv.adjointEquiv Ψ.toContinuousLinearEquiv b)| := by
  set A := ContinuousLinearEquiv.adjointEquiv Ψ.toContinuousLinearEquiv
  by_cases hne : stdForm ι (A a) (A b) = 0
  swap
  · exact one_le_abs_stdForm_adjointEquiv_of_ne_zero h hab hne
  exfalso
  have ha : A a ≠ 0 := by
    intro ha0
    rw [A.map_eq_zero_iff] at ha0
    simp [ha0] at hab
  obtain ⟨w, hw⟩ : ∃ w, stdForm ι (A a) w ≠ 0 :=
    (stdForm ι).nondegenerate.exists_apply_ne_zero ha
  set d := (stdForm ι (A a) w)⁻¹ • A.symm w
  have hd : stdForm ι (A a) (A d) = 1 := by
    simp only [d, map_smul, A.apply_symm_apply, smul_eq_mul]
    exact inv_mul_cancel₀ hw
  set b' := b + (2 : ℝ)⁻¹ • (d - stdForm ι a d • b)
  have h1 : stdForm ι a b' = 1 := by
    simp only [b', map_add, map_sub, map_smul, smul_eq_mul]
    linear_combination (1 - 2⁻¹ * stdForm ι a d) * hab
  have h2 : stdForm ι (A a) (A b') = 2⁻¹ := by
    simp only [b', map_add, map_sub, map_smul, smul_eq_mul]
    linear_combination (1 - 2⁻¹ * stdForm ι a d) * hne + 2⁻¹ * hd
  have := one_le_abs_stdForm_adjointEquiv_of_ne_zero h h1 (by rw [h2]; norm_num)
  rw [h2] at this
  norm_num at this

/-- If `Ψ` has the linear nonsqueezing property, then its adjoint does not decrease the
absolute value of `ω₀`: `|ω₀(a, b)| ≤ |ω₀(Ψᵀ a, Ψᵀ b)|`. -/
theorem HasLinearNonsqueezing.abs_stdForm_le_abs_stdForm_adjointEquiv
    {Ψ : StdSpace ι ≃ₗ[ℝ] StdSpace ι}
    (h : HasLinearNonsqueezing (Ψ : StdSpace ι →ₗ[ℝ] StdSpace ι)) (a b : StdSpace ι) :
    |stdForm ι a b| ≤
      |stdForm ι (ContinuousLinearEquiv.adjointEquiv Ψ.toContinuousLinearEquiv a)
        (ContinuousLinearEquiv.adjointEquiv Ψ.toContinuousLinearEquiv b)| := by
  rcases eq_or_ne (stdForm ι a b) 0 with hc | hc
  · rw [hc, abs_zero]
    exact abs_nonneg _
  have h1 := one_le_abs_stdForm_adjointEquiv h (a := (stdForm ι a b)⁻¹ • a) (b := b) (by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    exact inv_mul_cancel₀ hc)
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, abs_mul, abs_inv] at h1
  rwa [inv_mul_eq_div, one_le_div (abs_pos.2 hc)] at h1

/-- **Affine rigidity.** For a linear equivalence `Ψ` of the standard model, if
`HasLinearNonsqueezing Ψ` and `HasLinearNonsqueezing Ψ⁻¹`, then `Ψ^* ω₀ = ω₀` or
`Ψ^* ω₀ = -ω₀`. -/
theorem forall_apply_eq_or_forall_apply_eq_neg_of_hasLinearNonsqueezing
    (Ψ : StdSpace ι ≃ₗ[ℝ] StdSpace ι) (h : HasLinearNonsqueezing (Ψ : StdSpace ι →ₗ[ℝ] _))
    (h' : HasLinearNonsqueezing (Ψ.symm : StdSpace ι →ₗ[ℝ] _)) :
    (∀ z w, stdForm ι (Ψ z) (Ψ w) = stdForm ι z w) ∨
      ∀ z w, stdForm ι (Ψ z) (Ψ w) = -stdForm ι z w := by
  set A := ContinuousLinearEquiv.adjointEquiv Ψ.toContinuousLinearEquiv
  have hinv (a : StdSpace ι) :
      ContinuousLinearEquiv.adjointEquiv Ψ.symm.toContinuousLinearEquiv (A a) = a := by
    simp only [A, ContinuousLinearEquiv.adjointEquiv_apply]
    exact ContinuousLinearEquiv.adjoint_symm_adjoint_apply Ψ.toContinuousLinearEquiv a
  -- `|ω₀(Ψᵀ a, Ψᵀ b)| = |ω₀(a, b)|`, by the nonsqueezing property of `Ψ` and of `Ψ⁻¹`
  have hsq (a b : StdSpace ι) : stdForm ι (A a) (A b) ^ 2 = stdForm ι a b ^ 2 := by
    have h₂ := h'.abs_stdForm_le_abs_stdForm_adjointEquiv (A a) (A b)
    rw [hinv, hinv] at h₂
    exact sq_eq_sq_iff_abs_eq_abs _ _ |>.2
      (le_antisymm h₂ (h.abs_stdForm_le_abs_stdForm_adjointEquiv a b))
  -- the adjoint of `Ψᵀ` is `Ψ`
  have hA (z : StdSpace ι) :
      ContinuousLinearEquiv.adjointEquiv A.toLinearEquiv.toContinuousLinearEquiv z = Ψ z := by
    have hcoe : (A.toLinearEquiv.toContinuousLinearEquiv : StdSpace ι →L[ℝ] StdSpace ι) =
        ContinuousLinearMap.adjoint (Ψ.toContinuousLinearEquiv : StdSpace ι →L[ℝ] StdSpace ι) :=
      ContinuousLinearMap.ext fun _ ↦ ContinuousLinearEquiv.adjointEquiv_apply _ _
    rw [ContinuousLinearEquiv.adjointEquiv_apply, hcoe, ContinuousLinearMap.adjoint_adjoint,
      ContinuousLinearEquiv.coe_coe, LinearEquiv.coe_toContinuousLinearEquiv']
  rcases LinearMap.eq_or_eq_neg_of_forall_sq_eq_sq₂
    (B := (stdForm ι).toBilinForm.compl₁₂ (A : StdSpace ι →ₗ[ℝ] StdSpace ι)
      (A : StdSpace ι →ₗ[ℝ] StdSpace ι)) (ω := (stdForm ι).toBilinForm) hsq with hB | hB
  · left
    have he := SymplecticForm.isSymplectomorphism_iff.1
      (SymplecticForm.isSymplectomorphism_iff.2 (fun z w ↦ LinearMap.congr_fun₂ hB z w) :
        (stdForm ι).IsSymplectomorphism (stdForm ι) A.toLinearEquiv).adjoint
    simpa only [ContinuousLinearEquiv.coe_toLinearEquiv, hA] using he
  · right
    have he := forall_adjointEquiv_apply_eq_neg_of_forall_apply_eq_neg (Ψ := A.toLinearEquiv)
      fun z w ↦ LinearMap.congr_fun₂ hB z w
    simpa only [hA] using he

/-- For a linear equivalence `Ψ` of the standard model, `Ψ^* ω₀ = ±ω₀` holds exactly when
`HasLinearNonsqueezing Ψ` and `HasLinearNonsqueezing Ψ⁻¹` both hold. -/
theorem hasLinearNonsqueezing_and_hasLinearNonsqueezing_symm_iff
    (Ψ : StdSpace ι ≃ₗ[ℝ] StdSpace ι) :
    HasLinearNonsqueezing (Ψ : StdSpace ι →ₗ[ℝ] StdSpace ι) ∧
        HasLinearNonsqueezing (Ψ.symm : StdSpace ι →ₗ[ℝ] StdSpace ι) ↔
      (∀ z w, stdForm ι (Ψ z) (Ψ w) = stdForm ι z w) ∨
        ∀ z w, stdForm ι (Ψ z) (Ψ w) = -stdForm ι z w := by
  refine ⟨fun h ↦ forall_apply_eq_or_forall_apply_eq_neg_of_hasLinearNonsqueezing Ψ h.1 h.2,
    fun hΨ ↦ ⟨hasLinearNonsqueezing_of_forall_apply_eq_or_forall_apply_eq_neg hΨ,
      hasLinearNonsqueezing_of_forall_apply_eq_or_forall_apply_eq_neg ?_⟩⟩
  simp only [LinearEquiv.coe_coe]
  refine hΨ.imp (fun h z w ↦ ?_) (fun h z w ↦ ?_)
  · simpa only [LinearEquiv.apply_symm_apply] using (h (Ψ.symm z) (Ψ.symm w)).symm
  · have := h (Ψ.symm z) (Ψ.symm w)
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at this
    linarith

/-! ### Linear symplectic rigidity -/

/-- **Linear symplectic rigidity.** For a linear map `Ψ` of the standard model, `Ψ^* ω₀ = ω₀` or
`Ψ^* ω₀ = -ω₀` holds if and only if `Ψ` does not change the linear symplectic width of the
ellipsoids `{z | Q z ≤ 1}`, for `Q` ranging over the positive definite quadratic forms.

Milestone: *Linear symplectic rigidity*. -/
theorem forall_linearSymplecticWidth_image_eq_iff (Ψ : StdSpace ι →ₗ[ℝ] StdSpace ι) :
    (∀ Q : QuadraticForm ℝ (StdSpace ι), Q.PosDef →
      linearSymplecticWidth (Ψ '' {z | Q z ≤ 1}) = linearSymplecticWidth {z | Q z ≤ 1}) ↔
    (∀ z w, stdForm ι (Ψ z) (Ψ w) = stdForm ι z w) ∨
      ∀ z w, stdForm ι (Ψ z) (Ψ w) = -stdForm ι z w := by
  refine ⟨fun h ↦ ?_, fun hΨ _ _ ↦
    linearSymplecticWidth_image_of_forall_apply_eq_or_forall_apply_eq_neg hΨ _⟩
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact Or.inl fun z w ↦ by simp
  -- the images of balls under linear equivalences are ellipsoids
  have hball (e : StdSpace ι ≃ₗ[ℝ] StdSpace ι) (r : ℝ) (hr : 0 < r) :
      linearSymplecticWidth (Ψ '' (e '' closedBall 0 r)) =
        linearSymplecticWidth (e '' closedBall 0 r) := by
    obtain ⟨Q, hQ, hEq⟩ := e.exists_posDef_image_closedBall_eq hr
    rw [hEq]
    exact h Q hQ
  -- `Ψ` is surjective, since the image of the unit ball has positive width
  have hsurj : Function.Surjective Ψ := by
    have h1 : linearSymplecticWidth (Ψ '' closedBall 0 1) =
        linearSymplecticWidth (closedBall (0 : StdSpace ι) 1) := by
      have := hball (LinearEquiv.refl ℝ _) 1 one_pos
      rwa [show ⇑(LinearEquiv.refl ℝ (StdSpace ι)) = id from funext LinearEquiv.refl_apply,
        Set.image_id] at this
    have h2 := linearSymplecticWidth_image_closedBall (one_mem _) (0 : StdSpace ι) zero_le_one
    rw [AffineEquiv.coe_one, Set.image_id] at h2
    obtain ⟨z, hz⟩ := nonempty_interior_of_linearSymplecticWidth_ne_zero
      (A := Ψ '' closedBall 0 1) (by simp [h1, h2, Real.pi_pos])
    refine LinearMap.range_eq_top.1 (Submodule.eq_top_of_nonempty_interior' _ ⟨z, ?_⟩)
    exact interior_mono (Set.image_subset_range _ _) hz
  set e := LinearEquiv.ofBijective Ψ ⟨LinearMap.injective_iff_surjective.2 hsurj, hsurj⟩
  have he : ⇑e = ⇑Ψ := funext fun _ ↦ LinearEquiv.ofBijective_apply _ _
  have h₁ : HasLinearNonsqueezing (e : StdSpace ι →ₗ[ℝ] StdSpace ι) :=
    hasLinearNonsqueezing_of_forall_linearSymplecticWidth_le fun φ _ r hr ↦ by
      rw [LinearEquiv.coe_coe, he, hball φ r hr]
  -- `Ψ⁻¹` also preserves the widths of ellipsoids, since `Ψ` maps ellipsoids onto ellipsoids
  have h₂ : HasLinearNonsqueezing (e.symm : StdSpace ι →ₗ[ℝ] StdSpace ι) :=
    hasLinearNonsqueezing_of_forall_linearSymplecticWidth_le fun φ _ r hr ↦ by
      obtain ⟨Q, hQ, hEq⟩ := φ.exists_posDef_image_closedBall_eq hr
      have hQe := h (Q.comp (e : StdSpace ι →ₗ[ℝ] StdSpace ι)) (hQ.comp _ e.injective)
      have himage : Ψ '' {z | Q.comp (e : StdSpace ι →ₗ[ℝ] StdSpace ι) z ≤ 1} =
          {z | Q z ≤ 1} :=
        Set.image_preimage_eq {z | Q z ≤ 1} hsurj
      rw [himage] at hQe
      rw [hEq, LinearEquiv.coe_coe, e.image_symm_eq_preimage, hQe]
      rfl
  simpa only [he] using forall_apply_eq_or_forall_apply_eq_neg_of_hasLinearNonsqueezing e h₁ h₂

end SymplecticGeometry

namespace TauCeti.SymplecticForm.IsSymplectomorphism

open SymplecticGeometry

variable {ι : Type*} [Fintype ι]

/-- A linear symplectomorphism of the standard model has the linear nonsqueezing property. -/
theorem hasLinearNonsqueezing {e : StdSpace ι ≃ₗ[ℝ] StdSpace ι}
    (he : (stdForm ι).IsSymplectomorphism (stdForm ι) e) :
    HasLinearNonsqueezing (e : StdSpace ι →ₗ[ℝ] StdSpace ι) :=
  hasLinearNonsqueezing_of_forall_apply_eq_or_forall_apply_eq_neg
    (Or.inl (SymplecticForm.isSymplectomorphism_iff.1 he))

end TauCeti.SymplecticForm.IsSymplectomorphism

end
