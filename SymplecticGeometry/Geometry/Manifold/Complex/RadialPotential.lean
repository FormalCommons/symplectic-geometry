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

end SymplecticGeometry

end
