/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

import SymplecticGeometry.Topology.Algebra.Module.Alternating.Basic
import TauCeti.Analysis.SpecialFunctions.Complex.Arg
public import TauCeti.Geometry.Manifold.DifferentialForm.Opens.PartialDiffeomorph
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
public import TauCeti.Geometry.Symplectic.Complex.Line
public import TauCeti.Geometry.Symplectic.Manifold.Prod
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
public import TauCeti.Geometry.Toric.WeightedCircle.Transition

/-!
# The annulus map and product collars

For `0 ≤ δ` and the annulus `A(δ, ε) = {δ < |z| < ε}` of `ℂ`, the map
`a(z) = √(ε² + δ² - |z|²) z̄ / |z|` exchanges the two boundary circles: it sends the circle of
radius `r` to the circle of radius `√(ε² + δ² - r²)`, reversing the angle. It is an involution
of the annulus, and it preserves the area form `ω₀ = dx ∧ dy` of `ℂ`: in polar coordinates it
reverses both `r² / 2` (up to a constant) and the angle. Gluing two collars `Q × A(δ, ε)` by
`id_Q × a` is the step of the symplectic fibre sum that joins the two complements of the
neighbourhoods of `Q`.

## Main definitions and results

* `SymplecticGeometry.annulus δ ε`: the annulus `{δ < ‖z‖ < ε}`, an open subset of `ℂ`.
* `SymplecticGeometry.annulusMap δ ε`: the map `a`, with `norm_annulusMap`,
  `annulusMap_annulusMap` (it is an involution of the annulus), `mapsTo_annulusMap`, and
  `norm_annulusMap_eq_norm_iff`: it fixes exactly the radius `√((δ² + ε²) / 2)`.
* `SymplecticGeometry.annulusPartialDiffeomorph δ ε`: `a` as a partial diffeomorphism of `ℂ`
  with source and target the annulus, and `SymplecticGeometry.annulusDiffeomorph δ ε`, the
  diffeomorphism of the annulus that it gives.
* `SymplecticGeometry.annulusMap_eventuallyEq_weightedSliceTransitionBranch`: near a point
  `z ≠ 0`, `a` is Tau Ceti's `TauCeti.Toric.weightedSliceTransitionBranch 1 1 ((ε² + δ²) / 2) z`,
  so that its smoothness (`contDiffAt_annulusMap`) and
  `SymplecticGeometry.stdComplexSymplecticForm_fderiv_annulusMap`, that its derivative
  preserves `TauCeti.stdComplexSymplecticForm`, follow from Tau Ceti's lemmas for the branch;
  and
  `SymplecticGeometry.mpullback_annulusMap`: `annulusDiffeomorph` pulls the restriction of the
  constant form `ω₀` to the annulus back to itself.
* `SymplecticGeometry.prodAnnulusDiffeomorph Q δ ε`: the identity of `Q` times
  `annulusDiffeomorph`, and `SymplecticGeometry.mpullback_prodAnnulusDiffeomorph`: it
  preserves the product form `τ ⊕ ω₀` of Tau Ceti's `TauCeti.SmoothTwoForm.prod`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §7.2, pp. 318–319.
* [R. E. Gompf, *A new construction of symplectic manifolds*][Gompf1995].
-/

public section

noncomputable section

open Complex TopologicalSpace TauCeti
open scoped Manifold ContDiff ComplexConjugate Topology

namespace SymplecticGeometry

/-- The open annulus `{z : ℂ | δ < ‖z‖ < ε}`. -/
def annulus (δ ε : ℝ) : Opens ℂ :=
  ⟨{z | δ < ‖z‖ ∧ ‖z‖ < ε}, (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)⟩

@[simp]
theorem mem_annulus {δ ε : ℝ} {z : ℂ} : z ∈ annulus δ ε ↔ δ < ‖z‖ ∧ ‖z‖ < ε :=
  Iff.rfl

/-- The map `z ↦ √(ε² + δ² - ‖z‖²) z̄ / ‖z‖`, which exchanges the circles of radii `r` and
`√(ε² + δ² - r²)` and reverses the angle. -/
def annulusMap (δ ε : ℝ) (z : ℂ) : ℂ :=
  (√(ε ^ 2 + δ ^ 2 - ‖z‖ ^ 2) / ‖z‖) • conj z

theorem annulusMap_def (δ ε : ℝ) (z : ℂ) :
    annulusMap δ ε z = (√(ε ^ 2 + δ ^ 2 - ‖z‖ ^ 2) / ‖z‖) • conj z :=
  (rfl)

/-- Away from `0`, the annulus map sends the circle of radius `‖z‖` to that of radius
`√(ε² + δ² - ‖z‖²)`. -/
theorem norm_annulusMap (δ ε : ℝ) {z : ℂ} (hz : z ≠ 0) :
    ‖annulusMap δ ε z‖ = √(ε ^ 2 + δ ^ 2 - ‖z‖ ^ 2) := by
  have : ‖z‖ ≠ 0 := norm_ne_zero_iff.2 hz
  rw [annulusMap_def, norm_smul, Complex.norm_conj, Real.norm_eq_abs,
    abs_of_nonneg (by positivity), div_mul_cancel₀ _ this]

/-- The annulus map is an involution of the open disc of radius `√(ε² + δ²)`. -/
theorem annulusMap_annulusMap (δ ε : ℝ) {z : ℂ} (hzr : ‖z‖ ^ 2 < ε ^ 2 + δ ^ 2) :
    annulusMap δ ε (annulusMap δ ε z) = z := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [annulusMap_def]
  have hr : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hs2 : √(ε ^ 2 + δ ^ 2 - ‖z‖ ^ 2) ^ 2 = ε ^ 2 + δ ^ 2 - ‖z‖ ^ 2 :=
    Real.sq_sqrt (by linarith)
  rw [annulusMap_def (z := annulusMap δ ε z), norm_annulusMap δ ε hz, hs2,
    show ε ^ 2 + δ ^ 2 - (ε ^ 2 + δ ^ 2 - ‖z‖ ^ 2) = ‖z‖ ^ 2 by ring,
    Real.sqrt_sq hr.le, annulusMap_def, Complex.real_smul, Complex.real_smul, map_mul,
    Complex.conj_ofReal, Complex.conj_conj, ← mul_assoc, ← Complex.ofReal_mul,
    show ‖z‖ / √(ε ^ 2 + δ ^ 2 - ‖z‖ ^ 2) * (√(ε ^ 2 + δ ^ 2 - ‖z‖ ^ 2) / ‖z‖) = 1 by
      field_simp, Complex.ofReal_one, one_mul]

/-- For `0 ≤ δ`, the annulus map sends the annulus `A(δ, ε)` into itself. -/
theorem mapsTo_annulusMap {δ ε : ℝ} (hδ : 0 ≤ δ) :
    Set.MapsTo (annulusMap δ ε) (annulus δ ε) (annulus δ ε) := by
  rintro z ⟨h₁, h₂⟩
  have hz : z ≠ 0 := norm_pos_iff.1 (hδ.trans_lt h₁)
  have h₁' : δ ^ 2 < ‖z‖ ^ 2 := pow_lt_pow_left₀ h₁ hδ two_ne_zero
  have h₂' : ‖z‖ ^ 2 < ε ^ 2 := pow_lt_pow_left₀ h₂ (norm_nonneg z) two_ne_zero
  rw [SetLike.mem_coe, mem_annulus, norm_annulusMap δ ε hz]
  constructor
  · rw [Real.lt_sqrt hδ]
    linarith
  · rw [Real.sqrt_lt' (hδ.trans_lt h₁ |>.trans h₂)]
    linarith

/-- Away from `0`, the annulus map preserves the norm of `z` exactly on the circle of radius
`√((δ² + ε²) / 2)`. -/
theorem norm_annulusMap_eq_norm_iff (δ ε : ℝ) {z : ℂ} (hz : z ≠ 0) :
    ‖annulusMap δ ε z‖ = ‖z‖ ↔ ‖z‖ = √((δ ^ 2 + ε ^ 2) / 2) := by
  rcases le_or_gt (‖z‖ ^ 2) (ε ^ 2 + δ ^ 2) with hzr | hzr
  · rw [norm_annulusMap δ ε hz, Real.sqrt_eq_iff_eq_sq (by linarith) (norm_nonneg z),
      eq_comm (a := ‖z‖), Real.sqrt_eq_iff_eq_sq (by positivity) (norm_nonneg z)]
    constructor <;> intro h <;> linarith
  -- Outside the disc of radius `√(ε² + δ²)` the image is `0`, and neither side holds.
  rw [norm_annulusMap δ ε hz, Real.sqrt_eq_zero'.2 (by linarith)]
  refine ⟨fun h ↦ absurd h.symm (norm_ne_zero_iff.2 hz), fun h ↦ ?_⟩
  rw [h, Real.sq_sqrt (by positivity)] at hzr
  nlinarith [sq_nonneg δ, sq_nonneg ε]

/-- Away from `0`, the annulus map agrees with Tau Ceti's branch near `z` of the change of
slices, for the weights `a = b = 1` and the level `(ε² + δ²) / 2`. -/
theorem annulusMap_eq_weightedSliceTransitionBranch (δ ε : ℝ) {z w : ℂ} (hz : z ≠ 0)
    (hw : w ≠ 0) :
    annulusMap δ ε w = Toric.weightedSliceTransitionBranch 1 1 ((ε ^ 2 + δ ^ 2) / 2) z w := by
  have hz' : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hz
  set θ := arg (w / z) + arg z
  have he : exp (θ * I) = w / ‖w‖ := by
    rw [ofReal_add, add_mul, exp_add, exp_arg_mul_I (div_ne_zero hw hz), exp_arg_mul_I hz,
      norm_div]
    push_cast
    field_simp
  have he' : exp (-θ * I) = conj w / ‖w‖ := by
    rw [show -(θ : ℂ) * I = conj ((θ : ℂ) * I) by simp, exp_conj, he, map_div₀, conj_ofReal]
  rw [Toric.weightedSliceTransitionBranch_apply, annulusMap_def, Circle.coe_exp, Nat.cast_one,
    one_mul, one_mul, div_one, div_one, ofReal_neg, he', real_smul, ofReal_div,
    show 2 * ((ε ^ 2 + δ ^ 2) / 2) = ε ^ 2 + δ ^ 2 by ring]
  ring

/-- Near a point `z ≠ 0`, the annulus map is Tau Ceti's branch near `z` of the change of slices,
for the weights `a = b = 1` and the level `(ε² + δ²) / 2`. -/
theorem annulusMap_eventuallyEq_weightedSliceTransitionBranch (δ ε : ℝ) {z : ℂ} (hz : z ≠ 0) :
    annulusMap δ ε =ᶠ[𝓝 z] Toric.weightedSliceTransitionBranch 1 1 ((ε ^ 2 + δ ^ 2) / 2) z :=
  (eventually_ne_nhds hz).mono fun _ hw ↦ annulusMap_eq_weightedSliceTransitionBranch δ ε hz hw

/-- The derivative of the annulus map preserves the area form of `ℂ`, at every point `z ≠ 0`
with `‖z‖² < ε² + δ²`. -/
theorem stdComplexSymplecticForm_fderiv_annulusMap (δ ε : ℝ) {z : ℂ} (hz : z ≠ 0)
    (hzr : ‖z‖ ^ 2 < ε ^ 2 + δ ^ 2) (v w : ℂ) :
    TauCeti.stdComplexSymplecticForm (fderiv ℝ (annulusMap δ ε) z v)
        (fderiv ℝ (annulusMap δ ε) z w) = TauCeti.stdComplexSymplecticForm v w := by
  rw [(annulusMap_eventuallyEq_weightedSliceTransitionBranch δ ε hz).fderiv_eq]
  exact Toric.stdComplexSymplecticForm_fderiv_weightedSliceTransitionBranch one_pos one_pos
    (div_self hz ▸ one_mem_slitPlane) (by linarith) v w

/-- Points of the annulus with `0 ≤ δ` are nonzero and lie in the disc of radius `√(ε² + δ²)`,
where the annulus map is smooth and involutive. -/
theorem ne_zero_and_sq_lt_of_mem_annulus {δ ε : ℝ} (hδ : 0 ≤ δ) {z : ℂ}
    (hz : z ∈ annulus δ ε) : z ≠ 0 ∧ ‖z‖ ^ 2 < ε ^ 2 + δ ^ 2 := by
  obtain ⟨h₁, h₂⟩ := hz
  exact ⟨norm_pos_iff.1 (hδ.trans_lt h₁), by
    nlinarith [pow_lt_pow_left₀ h₂ (norm_nonneg z) two_ne_zero, sq_nonneg δ]⟩

/-- The annulus map is smooth at every point `z ≠ 0` with `‖z‖² < ε² + δ²`. -/
theorem contDiffAt_annulusMap (δ ε : ℝ) {z : ℂ} (hz : z ≠ 0)
    (hzr : ‖z‖ ^ 2 < ε ^ 2 + δ ^ 2) {n : WithTop ℕ∞} : ContDiffAt ℝ n (annulusMap δ ε) z :=
  (Toric.contDiffAt_weightedSliceTransitionBranch (a := 1) (b := 1)
    (ε := (ε ^ 2 + δ ^ 2) / 2) (div_self hz ▸ one_mem_slitPlane)
    (by linarith)).congr_of_eventuallyEq
    (annulusMap_eventuallyEq_weightedSliceTransitionBranch δ ε hz)

/-- The annulus map is smooth on the annulus, for `0 ≤ δ`. -/
theorem contDiffOn_annulusMap {δ ε : ℝ} (hδ : 0 ≤ δ) {n : WithTop ℕ∞} :
    ContDiffOn ℝ n (annulusMap δ ε) (annulus δ ε) := fun _ hz ↦
  (contDiffAt_annulusMap δ ε (ne_zero_and_sq_lt_of_mem_annulus hδ hz).1
    (ne_zero_and_sq_lt_of_mem_annulus hδ hz).2).contDiffWithinAt

/-- For `0 ≤ δ`, the annulus map as a partial diffeomorphism of `ℂ` whose source and target are
the annulus `A(δ, ε)`; it is its own inverse. -/
def annulusPartialDiffeomorph (δ ε : ℝ) (hδ : 0 ≤ δ) :
    PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞ where
  toFun := annulusMap δ ε
  invFun := annulusMap δ ε
  source := annulus δ ε
  target := annulus δ ε
  map_source' := mapsTo_annulusMap hδ
  map_target' := mapsTo_annulusMap hδ
  left_inv' _ hz := annulusMap_annulusMap δ ε (ne_zero_and_sq_lt_of_mem_annulus hδ hz).2
  right_inv' _ hz := annulusMap_annulusMap δ ε (ne_zero_and_sq_lt_of_mem_annulus hδ hz).2
  open_source := (annulus δ ε).isOpen
  open_target := (annulus δ ε).isOpen
  contMDiffOn_toFun := contMDiffOn_iff_contDiffOn.2 (contDiffOn_annulusMap hδ)
  contMDiffOn_invFun := contMDiffOn_iff_contDiffOn.2 (contDiffOn_annulusMap hδ)

@[simp]
theorem coe_annulusPartialDiffeomorph (δ ε : ℝ) (hδ : 0 ≤ δ) :
    ⇑(annulusPartialDiffeomorph δ ε hδ) = annulusMap δ ε :=
  (rfl)

@[simp]
theorem annulusPartialDiffeomorph_source (δ ε : ℝ) (hδ : 0 ≤ δ) :
    (annulusPartialDiffeomorph δ ε hδ).source = annulus δ ε :=
  (rfl)

@[simp]
theorem annulusPartialDiffeomorph_target (δ ε : ℝ) (hδ : 0 ≤ δ) :
    (annulusPartialDiffeomorph δ ε hδ).target = annulus δ ε :=
  (rfl)

/-- For `0 ≤ δ`, the annulus map as a diffeomorphism of the annulus `A(δ, ε)`. -/
def annulusDiffeomorph (δ ε : ℝ) (hδ : 0 ≤ δ) :
    annulus δ ε ≃ₘ⟮𝓘(ℝ, ℂ), 𝓘(ℝ, ℂ)⟯ annulus δ ε :=
  (annulusPartialDiffeomorph δ ε hδ).toDiffeomorphSourceTarget

@[simp]
theorem coe_annulusDiffeomorph_apply (δ ε : ℝ) (hδ : 0 ≤ δ) (z : annulus δ ε) :
    (annulusDiffeomorph δ ε hδ z : ℂ) = annulusMap δ ε z :=
  (annulusPartialDiffeomorph δ ε hδ).toDiffeomorphSourceTarget_apply_coe z

/-- The diffeomorphism of the annulus is an involution. -/
@[simp]
theorem annulusDiffeomorph_symm (δ ε : ℝ) (hδ : 0 ≤ δ) :
    (annulusDiffeomorph δ ε hδ).symm = annulusDiffeomorph δ ε hδ :=
  Diffeomorph.ext fun z ↦ Subtype.ext
    (((annulusPartialDiffeomorph δ ε hδ).toDiffeomorphSourceTarget_symm_apply_coe z).trans
      (coe_annulusDiffeomorph_apply δ ε hδ z).symm)

/-- **The annulus map preserves the area form.** The diffeomorphism `annulusDiffeomorph` pulls
the restriction to the annulus of the constant form `ω₀` of `TauCeti.stdComplexSymplecticForm`
back to itself. -/
theorem mpullback_annulusMap (δ ε : ℝ) (hδ : 0 ≤ δ) :
    SmoothForm.mpullback (annulusDiffeomorph δ ε hδ) (annulusDiffeomorph δ ε hδ).contMDiff
        (SmoothForm.mpullback (Subtype.val : annulus δ ε → ℂ) contMDiff_subtypeVal
          stdComplexSymplecticForm.constSmooth) =
      SmoothForm.mpullback (Subtype.val : annulus δ ε → ℂ) contMDiff_subtypeVal
        stdComplexSymplecticForm.constSmooth := by
  refine (SmoothForm.mpullback_toDiffeomorphSourceTarget_eq_iff
    (annulusPartialDiffeomorph δ ε hδ)).2 fun z hz ↦ ?_
  ext v w
  obtain ⟨hz₀, hzr⟩ := ne_zero_and_sq_lt_of_mem_annulus hδ hz
  rw [mpullback_apply_pair, ← SmoothBundleForm.eval₂_apply, ← SmoothBundleForm.eval₂_apply,
    SymplecticForm.fromTangentSpace_constSmooth_apply,
    SymplecticForm.fromTangentSpace_constSmooth_apply, mfderiv_eq_fderiv]
  exact stdComplexSymplecticForm_fderiv_annulusMap δ ε hz₀ hzr _ _

section Prod

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} (Q : Type*) [TopologicalSpace Q] [ChartedSpace H Q]

/-- For `0 ≤ δ`, the diffeomorphism `id_Q × a` of the collar `Q × A(δ, ε)`, where `a` is the
annulus map. -/
def prodAnnulusDiffeomorph (δ ε : ℝ) (hδ : 0 ≤ δ) :
    (Q × annulus δ ε) ≃ₘ⟮I.prod 𝓘(ℝ, ℂ), I.prod 𝓘(ℝ, ℂ)⟯ (Q × annulus δ ε) :=
  (Diffeomorph.refl I Q ∞).prodCongr (annulusDiffeomorph δ ε hδ)

theorem coe_prodAnnulusDiffeomorph (δ ε : ℝ) (hδ : 0 ≤ δ) :
    ⇑(prodAnnulusDiffeomorph (I := I) Q δ ε hδ) = Prod.map id (annulusDiffeomorph δ ε hδ) := by
  rw [prodAnnulusDiffeomorph, Diffeomorph.coe_prodCongr, Diffeomorph.coe_refl]

@[simp]
theorem prodAnnulusDiffeomorph_apply (δ ε : ℝ) (hδ : 0 ≤ δ) (p : Q × annulus δ ε) :
    prodAnnulusDiffeomorph (I := I) Q δ ε hδ p = (p.1, annulusDiffeomorph δ ε hδ p.2) := by
  rw [coe_prodAnnulusDiffeomorph, Prod.map_apply, id]

/-- The diffeomorphism `id_Q × a` of the collar is an involution. -/
@[simp]
theorem prodAnnulusDiffeomorph_symm (δ ε : ℝ) (hδ : 0 ≤ δ) :
    (prodAnnulusDiffeomorph (I := I) Q δ ε hδ).symm = prodAnnulusDiffeomorph Q δ ε hδ := by
  rw [prodAnnulusDiffeomorph, Diffeomorph.prodCongr_symm, Diffeomorph.symm_refl,
    annulusDiffeomorph_symm]

variable {Q} [IsManifold I ∞ Q]

/-- **The collar map preserves the product form.** For every two-form `τ` on `Q`, the
diffeomorphism `id_Q × a` of `Q × A(δ, ε)` pulls the product form `τ ⊕ ω₀` back to itself, where
`ω₀` is the area form of `ℂ` restricted to the annulus. -/
theorem mpullback_prodAnnulusDiffeomorph (τ : SmoothTwoForm I Q) (δ ε : ℝ) (hδ : 0 ≤ δ) :
    SmoothForm.mpullback (prodAnnulusDiffeomorph Q δ ε hδ)
        (prodAnnulusDiffeomorph Q δ ε hδ).contMDiff
        (τ.prod (SmoothForm.mpullback (Subtype.val : annulus δ ε → ℂ) contMDiff_subtypeVal
          stdComplexSymplecticForm.constSmooth)) =
      τ.prod (SmoothForm.mpullback (Subtype.val : annulus δ ε → ℂ) contMDiff_subtypeVal
        stdComplexSymplecticForm.constSmooth) := by
  simp only [coe_prodAnnulusDiffeomorph]
  rw [SmoothTwoForm.mpullback_prodMap_prod contMDiff_id (annulusDiffeomorph δ ε hδ).contMDiff,
    SmoothForm.mpullback_id, LinearMap.id_apply, mpullback_annulusMap]

end Prod

end SymplecticGeometry

end
