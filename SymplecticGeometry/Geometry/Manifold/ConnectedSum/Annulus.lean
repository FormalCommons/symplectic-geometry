/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Euclidean.Inversion
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset

/-!
# The gluing map of the connected sum by annuli

The connected sum of McDuff–Salamon glues `M₁` and `M₂`, from each of which a small ball has been
removed, along an annulus of the model space `E`, by the map `ξ ↦ ε² Φ ξ / ‖ξ‖²` for a linear
isometry `Φ` of `E`. This map is `Φ` after the inversion `EuclideanGeometry.inversion 0 ε` in the
sphere of radius `ε` about the origin, which sends `‖ξ‖` to `ε² / ‖ξ‖`. So it preserves the open
annulus `ε² < ‖ξ‖ < 1`, whose middle sphere `‖ξ‖ = ε` the inversion fixes, and exchanges its two
ends. This file builds the map, on the model space alone, as a diffeomorphism of that annulus.

## Main definitions and results

* `SymplecticGeometry.ConnectedSum.annulus E ε`: the open annulus `{ξ | ε² < ‖ξ‖ < 1}` of `E`,
  with `mem_annulus`.
* `SymplecticGeometry.ConnectedSum.inversion_mem_annulus_iff`: for `ε ≠ 0` the inversion
  `inversion 0 ε` maps the annulus onto itself; it is an involution (Mathlib's
  `EuclideanGeometry.inversion_inversion`) that exchanges the two ends of the annulus
  (`EuclideanGeometry.norm_inversion_zero_lt_iff` and
  `EuclideanGeometry.lt_norm_inversion_zero_iff` with `r = 1` and `r = ε²`).
  `SymplecticGeometry.ConnectedSum.map_mem_annulus_iff`: so does every linear isometry.
* `SymplecticGeometry.ConnectedSum.gluingPartialDiffeomorph Φ ε hε`: the map
  `ξ ↦ Φ (inversion 0 ε ξ)` as a `C^n` partial diffeomorphism of `E` with source and target the
  annulus, and inverse `η ↦ inversion 0 ε (Φ⁻¹ η)`.
* `SymplecticGeometry.ConnectedSum.gluingDiffeomorph Φ ε hε`: the diffeomorphism of the annulus
  that it gives, with `coe_gluingDiffeomorph_apply` and `coe_gluingDiffeomorph_symm_apply`; for
  `Φ` the identity it is an involution (`gluingDiffeomorph_refl_symm`).

The smoothness of the inversion away from its centre is Tau Ceti's
`EuclideanGeometry.contDiffAt_inversion`, and the diffeomorphism is Tau Ceti's
`PartialDiffeomorph.toDiffeomorphSourceTarget`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §7.1, Exercise 7.1.4.
-/

public section

noncomputable section

open TopologicalSpace EuclideanGeometry
open scoped Manifold ContDiff

namespace SymplecticGeometry.ConnectedSum

variable (E : Type*) [NormedAddCommGroup E]

/-- The open annulus `{ξ | ε² < ‖ξ‖ < 1}` of `E`, along which the connected sum is glued. -/
def annulus (ε : ℝ) : Opens E :=
  ⟨{ξ | ε ^ 2 < ‖ξ‖ ∧ ‖ξ‖ < 1}, (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)⟩

variable {E}

@[simp]
theorem mem_annulus {ε : ℝ} {ξ : E} : ξ ∈ annulus E ε ↔ ε ^ 2 < ‖ξ‖ ∧ ‖ξ‖ < 1 :=
  Iff.rfl

/-- The points of the annulus are nonzero. -/
theorem ne_zero_of_mem_annulus {ε : ℝ} {ξ : E} (hξ : ξ ∈ annulus E ε) : ξ ≠ 0 :=
  norm_pos_iff.1 ((sq_nonneg ε).trans_lt hξ.1)

/-- A linear isometry `Φ` of `E` maps the annulus onto itself. -/
theorem map_mem_annulus_iff [NormedSpace ℝ E] (Φ : E ≃ₗᵢ[ℝ] E) {ε : ℝ} {ξ : E} :
    Φ ξ ∈ annulus E ε ↔ ξ ∈ annulus E ε := by
  simp

variable [InnerProductSpace ℝ E]

/-- For `ε ≠ 0`, the inversion in the sphere of radius `ε` about the origin maps the annulus
`ε² < ‖ξ‖ < 1` onto itself. -/
theorem inversion_mem_annulus_iff {ε : ℝ} (hε : ε ≠ 0) {ξ : E} :
    inversion (0 : E) ε ξ ∈ annulus E ε ↔ ξ ∈ annulus E ε := by
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp only [inversion_self]
  have hε₂ : 0 < ε ^ 2 := by positivity
  rw [mem_annulus, mem_annulus, lt_norm_inversion_zero_iff ε hε₂ hξ,
    norm_inversion_zero_lt_iff ε one_pos hξ, div_self hε₂.ne', div_one, and_comm]

/-- For `ε ≠ 0`, the map `ξ ↦ Φ (inversion 0 ε ξ)`, which is `ε² Φ ξ / ‖ξ‖²`, as a `C^n` partial
diffeomorphism of `E` whose source and target are the annulus `ε² < ‖ξ‖ < 1`. Its inverse is
`η ↦ inversion 0 ε (Φ⁻¹ η)`. -/
def gluingPartialDiffeomorph (Φ : E ≃ₗᵢ[ℝ] E) (ε : ℝ) (hε : ε ≠ 0) {n : ℕ∞ω} :
    PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E n where
  toFun ξ := Φ (inversion 0 ε ξ)
  invFun η := inversion 0 ε (Φ.symm η)
  source := annulus E ε
  target := annulus E ε
  map_source' _ hξ := (map_mem_annulus_iff Φ).2 ((inversion_mem_annulus_iff hε).2 hξ)
  map_target' _ hη := (inversion_mem_annulus_iff hε).2 ((map_mem_annulus_iff Φ.symm).2 hη)
  left_inv' ξ _ := by simp [inversion_inversion (0 : E) hε]
  right_inv' η _ := by simp [inversion_inversion (0 : E) hε]
  open_source := (annulus E ε).isOpen
  open_target := (annulus E ε).isOpen
  contMDiffOn_toFun := contMDiffOn_iff_contDiffOn.2 fun ξ hξ ↦
    (Φ.contDiff.contDiffAt.comp ξ
      (contDiffAt_inversion (ne_zero_of_mem_annulus hξ))).contDiffWithinAt
  contMDiffOn_invFun := contMDiffOn_iff_contDiffOn.2 fun η hη ↦
    ((contDiffAt_inversion (Φ.symm.map_ne_zero_iff.2 (ne_zero_of_mem_annulus hη))).comp η
      Φ.symm.contDiff.contDiffAt).contDiffWithinAt

variable (Φ : E ≃ₗᵢ[ℝ] E) {ε : ℝ} (hε : ε ≠ 0) {n : ℕ∞ω}

@[simp]
theorem gluingPartialDiffeomorph_apply (ξ : E) :
    gluingPartialDiffeomorph Φ ε hε (n := n) ξ = Φ (inversion 0 ε ξ) :=
  (rfl)

@[simp]
theorem gluingPartialDiffeomorph_symm_apply (η : E) :
    (gluingPartialDiffeomorph Φ ε hε (n := n)).toPartialEquiv.symm η = inversion 0 ε (Φ.symm η) :=
  (rfl)

@[simp]
theorem gluingPartialDiffeomorph_source :
    (gluingPartialDiffeomorph Φ ε hε (n := n)).source = annulus E ε :=
  (rfl)

@[simp]
theorem gluingPartialDiffeomorph_target :
    (gluingPartialDiffeomorph Φ ε hε (n := n)).target = annulus E ε :=
  (rfl)

/-- For `ε ≠ 0`, the gluing map `ξ ↦ Φ (inversion 0 ε ξ)` of the connected sum, as a `C^n`
diffeomorphism of the annulus `ε² < ‖ξ‖ < 1` onto itself. -/
def gluingDiffeomorph : annulus E ε ≃ₘ^n⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ annulus E ε :=
  (gluingPartialDiffeomorph Φ ε hε).toDiffeomorphSourceTarget

@[simp]
theorem coe_gluingDiffeomorph_apply (ξ : annulus E ε) :
    (gluingDiffeomorph Φ hε (n := n) ξ : E) = Φ (inversion 0 ε ξ) :=
  (gluingPartialDiffeomorph Φ ε hε).toDiffeomorphSourceTarget_apply_coe ξ

@[simp]
theorem coe_gluingDiffeomorph_symm_apply (η : annulus E ε) :
    ((gluingDiffeomorph Φ hε (n := n)).symm η : E) = inversion 0 ε (Φ.symm η) :=
  (gluingPartialDiffeomorph Φ ε hε).toDiffeomorphSourceTarget_symm_apply_coe η

/-- For `Φ` the identity, the gluing diffeomorphism is the inversion, an involution of the
annulus. -/
theorem gluingDiffeomorph_refl_symm :
    (gluingDiffeomorph (LinearIsometryEquiv.refl ℝ E) hε (n := n)).symm =
      gluingDiffeomorph (LinearIsometryEquiv.refl ℝ E) hε :=
  Diffeomorph.ext fun η ↦ Subtype.ext <| by
    rw [coe_gluingDiffeomorph_symm_apply, coe_gluingDiffeomorph_apply]
    have h := (LinearIsometryEquiv.refl ℝ E).symm_apply_apply (η : E)
    rw [LinearIsometryEquiv.coe_refl, id] at h
    rw [h, LinearIsometryEquiv.coe_refl, id]

end SymplecticGeometry.ConnectedSum

end
