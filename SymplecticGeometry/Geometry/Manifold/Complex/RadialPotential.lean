/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
public import TauCeti.Geometry.Manifold.Instances.Cylinder
public import TauCeti.Analysis.Complex.Euclidean.Space
import SymplecticGeometry.Analysis.Complex.QuadraticLeviForm
import SymplecticGeometry.Analysis.Complex.Euclidean.Space

/-!
# Radial potentials on `ℂⁿ ∖ 0`

For a finite type `ι` and a function `g : ℝ → ℝ` smooth on `(0, ∞)`, the function
`z ↦ g |z|²` with `|z|² = ∑ᵢ ‖zᵢ‖²` is smooth on `TauCeti.puncturedSpace (ι → ℂ)`.

* `SymplecticGeometry.radialPotential hg`: this function, as a smooth map to `ℝ`, with
  `coe_radialPotential` and `radialPotential_apply`. It is linear in `g`
  (`radialPotential_add`, `radialPotential_const_mul`).
* `SymplecticGeometry.radialFunction hg`: for `g` smooth on all of `ℝ`, the same function
  `z ↦ g |z|²` on all of `ι → ℂ`, with `radialFunction_apply`; it restricts to
  `radialPotential` on `(ι → ℂ) ∖ 0` (`radialFunction_coe`).

For `g = log` it is the Kähler potential of the Fubini–Study form
(`SymplecticGeometry.fubiniStudyPotential`), and `Geometry/Symplectic/Complex/Radial.lean`
computes its form `(1/4) d (J* d (g ∘ s))` for general `g`.
-/

public section

open Set TauCeti
open scoped Manifold ContDiff

namespace SymplecticGeometry

variable {ι : Type*} [Fintype ι]

/-- The radial potential `z ↦ g |z|²` on `(ι → ℂ) ∖ 0`, for `g` smooth on `(0, ∞)`, as a smooth
function (`radialPotential_apply`). -/
noncomputable def radialPotential {g : ℝ → ℝ} (hg : ContDiffOn ℝ ∞ g (Ioi 0)) :
    C^∞⟮𝓘(ℝ, ι → ℂ), puncturedSpace (ι → ℂ); ℝ⟯ :=
  ⟨fun z ↦ g (‖complexToRealEuclidean ι z‖ ^ 2), fun z ↦
    (contDiffAt_comp_norm_sq_complexToRealEuclidean hg z).contMDiffAt.comp z
      (contMDiff_subtypeVal z)⟩

/-- The radial potential is the function `z ↦ g ‖ẑ‖²`, for `ẑ` the image of `z` in
`EuclideanSpace ℝ (ι ⊕ ι)`. -/
theorem coe_radialPotential {g : ℝ → ℝ} (hg : ContDiffOn ℝ ∞ g (Ioi 0)) :
    ⇑(radialPotential (ι := ι) hg) =
      fun z : puncturedSpace (ι → ℂ) ↦ g (‖complexToRealEuclidean ι z‖ ^ 2) :=
  (rfl)

/-- The radial potential takes the value `g |z|²` at `z`. -/
@[simp]
theorem radialPotential_apply {g : ℝ → ℝ} (hg : ContDiffOn ℝ ∞ g (Ioi 0))
    (z : puncturedSpace (ι → ℂ)) :
    radialPotential hg z = g (∑ i, ‖(z : ι → ℂ) i‖ ^ 2) := by
  simp only [coe_radialPotential, norm_sq_complexToRealEuclidean]

/-- The radial potential of `g₁ + g₂` is the sum of those of `g₁` and `g₂`. -/
theorem radialPotential_add {g₁ g₂ : ℝ → ℝ} (hg₁ : ContDiffOn ℝ ∞ g₁ (Ioi 0))
    (hg₂ : ContDiffOn ℝ ∞ g₂ (Ioi 0)) :
    radialPotential (ι := ι) (g := fun s ↦ g₁ s + g₂ s) (hg₁.add hg₂) =
      radialPotential hg₁ + radialPotential hg₂ :=
  ContMDiffMap.ext fun z ↦ by simp

/-- The radial potential of `c g` is `c` times that of `g`. -/
theorem radialPotential_const_mul (c : ℝ) {g : ℝ → ℝ} (hg : ContDiffOn ℝ ∞ g (Ioi 0)) :
    radialPotential (ι := ι) (g := fun s ↦ c * g s) (contDiffOn_const.mul hg) =
      c • radialPotential hg :=
  ContMDiffMap.ext fun z ↦ by simp

/-- The radial function `z ↦ g |z|²` on all of `ι → ℂ`, for `g` smooth on `ℝ`, as a smooth
function (`radialFunction_apply`). On `(ι → ℂ) ∖ 0` it is the radial potential of `g`
(`radialFunction_coe`). -/
noncomputable def radialFunction {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) :
    C^∞⟮𝓘(ℝ, ι → ℂ), ι → ℂ; ℝ⟯ :=
  ⟨fun z ↦ g (‖complexToRealEuclidean ι z‖ ^ 2),
    (hg.comp contDiff_norm_sq_complexToRealEuclidean).contMDiff⟩

/-- The radial function of `g` takes the value `g ‖ẑ‖²` at `z`, for `ẑ` the image of `z` in
`EuclideanSpace ℝ (ι ⊕ ι)`. -/
theorem radialFunction_apply {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (z : ι → ℂ) :
    radialFunction hg z = g (‖complexToRealEuclidean ι z‖ ^ 2) :=
  (rfl)

/-- On `(ι → ℂ) ∖ 0`, the radial function of `g` is the radial potential of `g`. -/
theorem radialFunction_coe {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (z : puncturedSpace (ι → ℂ)) :
    radialFunction hg (z : ι → ℂ) = radialPotential hg.contDiffOn z := by
  rw [radialFunction_apply, coe_radialPotential]

end SymplecticGeometry

end
