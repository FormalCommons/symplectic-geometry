/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Euclidean.Inversion
public import SymplecticGeometry.Topology.Sets.Annulus
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset

import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions

/-!
# The gluing map of the connected sum by annuli

The connected sum of McDuff–Salamon glues `M₁` and `M₂`, from each of which a small ball has been
removed, along an annulus of the model space `E`, by the map `ξ ↦ ε² Φ ξ / ‖ξ‖²` for a linear
isometry `Φ` of `E`. This map is `Φ` after the inversion `EuclideanGeometry.inversion 0 ε` in the
sphere of radius `ε` about the origin, which sends `‖ξ‖` to `ε² / ‖ξ‖`. So it preserves the open
annulus `ε² < ‖ξ‖ < 1`, whose middle sphere `‖ξ‖ = ε` the inversion fixes, and exchanges its two
ends. This file builds the map, on the model space alone, as a diffeomorphism of that annulus.

## Main definitions and results

The annulus is `SymplecticGeometry.annulus E (ε ^ 2) 1`, which every linear isometry maps onto
itself (`SymplecticGeometry.map_mem_annulus_iff`).

* `SymplecticGeometry.ConnectedSum.inversion_mem_annulus_iff`: for `ε ≠ 0` the inversion
  `inversion 0 ε` maps the annulus onto itself; it is an involution (Mathlib's
  `EuclideanGeometry.inversion_inversion`) that exchanges the two ends of the annulus
  (`EuclideanGeometry.norm_inversion_zero_lt_iff` and
  `EuclideanGeometry.lt_norm_inversion_zero_iff` with `r = 1` and `r = ε²`).
* `SymplecticGeometry.ConnectedSum.gluingPartialDiffeomorph Φ ε hε`: the map
  `ξ ↦ Φ (inversion 0 ε ξ)` as a `C^n` partial diffeomorphism of `E` with source and target the
  annulus, and inverse `η ↦ inversion 0 ε (Φ⁻¹ η)`, which is the same map for `Φ⁻¹`
  (`gluingPartialDiffeomorph_symm`).
* `SymplecticGeometry.ConnectedSum.gluingDiffeomorph Φ ε hε`: the diffeomorphism of the annulus
  that it gives, with `coe_gluingDiffeomorph_apply` and `coe_gluingDiffeomorph_symm_apply`; its
  inverse is the gluing diffeomorphism for `Φ⁻¹` (`gluingDiffeomorph_symm`).

The smoothness of the inversion away from its centre is Tau Ceti's
`EuclideanGeometry.contDiffAt_inversion`, and the diffeomorphism is Tau Ceti's
`PartialDiffeomorph.toDiffeomorphSourceTarget`. The inverse is identified by Tau Ceti's
`LinearIsometryEquiv.map_inversion_zero`: a linear isometry commutes with inversion about `0`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §7.1, Exercise 7.1.4.
-/

public section

noncomputable section

open TopologicalSpace EuclideanGeometry
open scoped Manifold ContDiff

namespace SymplecticGeometry.ConnectedSum

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- For `ε ≠ 0`, the inversion in the sphere of radius `ε` about the origin maps the annulus
`ε² < ‖ξ‖ < 1` onto itself. -/
theorem inversion_mem_annulus_iff {ε : ℝ} (hε : ε ≠ 0) {ξ : E} :
    inversion (0 : E) ε ξ ∈ annulus E (ε ^ 2) 1 ↔ ξ ∈ annulus E (ε ^ 2) 1 := by
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
  source := annulus E (ε ^ 2) 1
  target := annulus E (ε ^ 2) 1
  map_source' _ hξ := (map_mem_annulus_iff Φ).2 ((inversion_mem_annulus_iff hε).2 hξ)
  map_target' _ hη := (inversion_mem_annulus_iff hε).2 ((map_mem_annulus_iff Φ.symm).2 hη)
  left_inv' ξ _ := by simp [inversion_inversion (0 : E) hε]
  right_inv' η _ := by simp [inversion_inversion (0 : E) hε]
  open_source := (annulus E (ε ^ 2) 1).isOpen
  open_target := (annulus E (ε ^ 2) 1).isOpen
  contMDiffOn_toFun := contMDiffOn_iff_contDiffOn.2 fun ξ hξ ↦
    (Φ.contDiff.contDiffAt.comp ξ
      (contDiffAt_inversion (ne_zero_of_mem_annulus (sq_nonneg ε) hξ))).contDiffWithinAt
  contMDiffOn_invFun := contMDiffOn_iff_contDiffOn.2 fun η hη ↦
    ((contDiffAt_inversion
      (Φ.symm.map_ne_zero_iff.2 (ne_zero_of_mem_annulus (sq_nonneg ε) hη))).comp η
      Φ.symm.contDiff.contDiffAt).contDiffWithinAt

variable (Φ : E ≃ₗᵢ[ℝ] E) (ε : ℝ) (hε : ε ≠ 0) {n : ℕ∞ω}

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
    (gluingPartialDiffeomorph Φ ε hε (n := n)).source = annulus E (ε ^ 2) 1 :=
  (rfl)

@[simp]
theorem gluingPartialDiffeomorph_target :
    (gluingPartialDiffeomorph Φ ε hε (n := n)).target = annulus E (ε ^ 2) 1 :=
  (rfl)

/-- The inverse of the gluing map for `Φ` is the gluing map for `Φ⁻¹`. -/
@[simp]
theorem gluingPartialDiffeomorph_symm :
    (gluingPartialDiffeomorph Φ ε hε (n := n)).symm = gluingPartialDiffeomorph Φ.symm ε hε :=
  PartialDiffeomorph.ext (fun η ↦ by simp [LinearIsometryEquiv.map_inversion_zero])
    (fun ξ ↦ by simp [LinearIsometryEquiv.map_inversion_zero]) rfl

/-- For `ε ≠ 0`, the gluing map `ξ ↦ Φ (inversion 0 ε ξ)` of the connected sum, as a `C^n`
diffeomorphism of the annulus `ε² < ‖ξ‖ < 1` onto itself. -/
def gluingDiffeomorph : annulus E (ε ^ 2) 1 ≃ₘ^n⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ annulus E (ε ^ 2) 1 :=
  (gluingPartialDiffeomorph Φ ε hε).toDiffeomorphSourceTarget

@[simp]
theorem coe_gluingDiffeomorph_apply (ξ : annulus E (ε ^ 2) 1) :
    (gluingDiffeomorph Φ ε hε (n := n) ξ : E) = Φ (inversion 0 ε ξ) :=
  (gluingPartialDiffeomorph Φ ε hε).toDiffeomorphSourceTarget_apply_coe ξ

theorem coe_gluingDiffeomorph_symm_apply (η : annulus E (ε ^ 2) 1) :
    ((gluingDiffeomorph Φ ε hε (n := n)).symm η : E) = inversion 0 ε (Φ.symm η) :=
  (gluingPartialDiffeomorph Φ ε hε).toDiffeomorphSourceTarget_symm_apply_coe η

/-- The inverse of the gluing diffeomorphism for `Φ` is the gluing diffeomorphism for `Φ⁻¹`. -/
@[simp]
theorem gluingDiffeomorph_symm :
    (gluingDiffeomorph Φ ε hε (n := n)).symm = gluingDiffeomorph Φ.symm ε hε :=
  Diffeomorph.ext fun η ↦ Subtype.ext <| by
    simp [coe_gluingDiffeomorph_symm_apply, LinearIsometryEquiv.map_inversion_zero]

end SymplecticGeometry.ConnectedSum

end
