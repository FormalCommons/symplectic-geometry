/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Complex.Euclidean.Space
public import TauCeti.Analysis.Complex.QuadraticLeviForm
public import TauCeti.Geometry.Manifold.Instances.Cylinder
import SymplecticGeometry.Analysis.Complex.Euclidean.Space

/-!
# The squared norm on `ι → ℂ`

For a finite type `ι`, write `s(z) = |z|² = ‖complexToRealEuclidean ι z‖ ^ 2 = ∑ᵢ ‖zᵢ‖²` on
`ι → ℂ`. This file gives the first-order and Levi-form data of `s` in the coordinates of `ι → ℂ`:

* `TauCeti.contDiff_norm_sq_complexToRealEuclidean`: `s` is smooth.
* `TauCeti.leviForm_norm_sq_complexToRealEuclidean`: the Levi form of `s` is the Hermitian
  product `star v ⬝ᵥ w`. It is `TauCeti.leviForm_norm_sq` for `EuclideanSpace ℂ ι`, carried
  along `EuclideanSpace.equiv`.
* `TauCeti.extendRCLike_fderiv_norm_sq_complexToRealEuclidean`: the complex-linear extension of
  the differential of `s` at `z` is `v ↦ 2 (star z ⬝ᵥ v)`, that is `2 ∂s`.
* `TauCeti.norm_sq_complexToRealEuclidean_pos`: `s` is positive on `puncturedSpace (ι → ℂ)`.
* `TauCeti.contDiffAt_comp_norm_sq_complexToRealEuclidean`: for `g` smooth on `(0, ∞)`, `g ∘ s`
  is smooth at every point of `puncturedSpace (ι → ℂ)`.
-/

public section

open Set
open scoped ContDiff

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- The squared Euclidean norm `s(z) = |z|² = ∑ᵢ ‖zᵢ‖²` on `ι → ℂ` is smooth. -/
theorem contDiff_norm_sq_complexToRealEuclidean :
    ContDiff ℝ ∞ fun z : ι → ℂ ↦ ‖complexToRealEuclidean ι z‖ ^ 2 :=
  (contDiff_norm_sq ℝ).comp (complexToRealEuclidean ι).contDiff

/-- The Levi form of `s(z) = |z|² = ∑ᵢ ‖zᵢ‖²` on `ι → ℂ` is the Hermitian product
`star v ⬝ᵥ w`. -/
theorem leviForm_norm_sq_complexToRealEuclidean (z v w : ι → ℂ) :
    leviForm (fun y ↦ ‖complexToRealEuclidean ι y‖ ^ 2) z v w = star v ⬝ᵥ w := by
  set L := (EuclideanSpace.equiv ι ℂ).symm
  have hs : (fun y ↦ ‖complexToRealEuclidean ι y‖ ^ 2) =
      (fun x : EuclideanSpace ℂ ι ↦ ‖x‖ ^ 2) ∘ L := by
    funext y
    rw [Function.comp_apply, norm_sq_complexToRealEuclidean,
      EuclideanSpace.norm_sq_eq]
    simp [L]
  rw [hs, leviForm_comp_apply (contDiff_norm_sq ℝ).contDiffAt L.contDiff.contDiffAt,
    leviForm_norm_sq, L.fderiv]
  simp [L, PiLp.inner_apply, dotProduct, mul_comm]

/-- The complex-linear extension of the differential of `s(z) = |z|²` at `z` is
`v ↦ 2 (star z ⬝ᵥ v)`, the form `2 ∂s`. -/
theorem extendRCLike_fderiv_norm_sq_complexToRealEuclidean (z v : ι → ℂ) :
    StrongDual.extendRCLike (𝕜 := ℂ)
        (fderiv ℝ (fun y ↦ ‖complexToRealEuclidean ι y‖ ^ 2) z) v = 2 * (star z ⬝ᵥ v) := by
  have hd := ((complexToRealEuclidean ι).hasFDerivAt (x := z)).norm_sq
  rw [hd.fderiv, StrongDual.extendRCLike_apply]
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, innerSL_apply_apply, inner_complexToRealEuclidean,
    nsmul_eq_mul, Nat.cast_ofNat, dotProduct_smul]
  apply Complex.ext <;> simp

/-- The squared Euclidean norm `|z|²` is positive on `(ι → ℂ) ∖ 0`. -/
theorem norm_sq_complexToRealEuclidean_pos (z : puncturedSpace (ι → ℂ)) :
    0 < ‖complexToRealEuclidean ι z‖ ^ 2 :=
  pow_pos (norm_pos_iff.2 (by simpa using mem_puncturedSpace.1 z.property)) 2

/-- For `g` smooth on `(0, ∞)`, the function `w ↦ g |w|²` on `ι → ℂ` is smooth at
every point of `(ι → ℂ) ∖ 0`. -/
theorem contDiffAt_comp_norm_sq_complexToRealEuclidean {g : ℝ → ℝ}
    (hg : ContDiffOn ℝ ∞ g (Ioi 0)) (z : puncturedSpace (ι → ℂ)) :
    ContDiffAt ℝ ∞ (fun w ↦ g (‖complexToRealEuclidean ι w‖ ^ 2))
      (z : ι → ℂ) :=
  ContDiffAt.comp (g := g) (f := fun w ↦ ‖complexToRealEuclidean ι w‖ ^ 2) _
    (hg.contDiffAt (Ioi_mem_nhds (norm_sq_complexToRealEuclidean_pos z)))
    contDiff_norm_sq_complexToRealEuclidean.contDiffAt

end TauCeti

end
