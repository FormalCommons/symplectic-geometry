/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Complex.Euclidean.Space
public import TauCeti.Analysis.Complex.QuadraticLeviForm
public import TauCeti.Geometry.Manifold.Instances.Cylinder
public import Mathlib.Analysis.InnerProductSpace.Laplacian
import SymplecticGeometry.Analysis.Complex.Euclidean.Space
import SymplecticGeometry.Analysis.InnerProductSpace.PiL2
import TauCeti.Analysis.Complex.LeviForm.Laplacian

/-!
# The squared norm on `ι → ℂ`

For a finite type `ι`, write `s(z) = |z|² = ‖complexToRealEuclidean ι z‖ ^ 2 = ∑ᵢ ‖zᵢ‖²` on
`ι → ℂ`. This file gives the first-order and Levi-form data of `s` in the coordinates of `ι → ℂ`:

* `TauCeti.contDiff_norm_sq_complexToRealEuclidean`: `s` is `C^n` for every `n`.
* `TauCeti.leviForm_norm_sq_complexToRealEuclidean`: the Levi form of `s` is the Hermitian
  product `star v ⬝ᵥ w`. It is `TauCeti.leviForm_norm_sq_comp_apply` for the complex-linear map
  `(EuclideanSpace.equiv ι ℂ).symm`.
* `TauCeti.extendRCLike_fderiv_norm_sq_complexToRealEuclidean`: the complex-linear extension of
  the differential of `s` at `z` is `v ↦ 2 (star z ⬝ᵥ v)`, that is `2 ∂s`.
* `TauCeti.norm_sq_complexToRealEuclidean_pos`: `s` is positive on `puncturedSpace (ι → ℂ)`.
* `TauCeti.contDiffAt_comp_norm_sq_complexToRealEuclidean`: for `g` of class `C^n` on `(0, ∞)`,
  `g ∘ s` is `C^n` at every point of `puncturedSpace (ι → ℂ)`.
* `TauCeti.laplacian_comp_sum_norm_sq_div_four`: for `u : ℂ → ι → ℂ` complex `C²` at `t` and
  `ψ : ℝ → ℝ` of class `C²` at `s(u t)`, a quarter of the Laplacian of `ψ ∘ s ∘ u` at `t` is
  `ψ'(s) |v|² + ψ''(s) |star (u t) ⬝ᵥ v|²`, for `v = u'(t)`. The orthonormal basis `{1}` of `ℂ`
  turns the Laplacian into four times the Levi form on `1` (`TauCeti.sum_re_leviForm_apply_self`),
  which the chain rules `TauCeti.leviForm_comp_apply` and `TauCeti.leviForm_scalar_comp_apply`
  compute from the Levi form and the differential of `s` above.
-/

public section

open Set
open scoped ContDiff Laplacian ComplexConjugate

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- The squared Euclidean norm `s(z) = |z|² = ∑ᵢ ‖zᵢ‖²` on `ι → ℂ` is `C^n` for every
`n`. -/
theorem contDiff_norm_sq_complexToRealEuclidean {n : WithTop ℕ∞} :
    ContDiff ℝ n fun z : ι → ℂ ↦ ‖complexToRealEuclidean ι z‖ ^ 2 :=
  (contDiff_norm_sq ℝ).comp (complexToRealEuclidean ι).contDiff

/-- The Levi form of `s(z) = |z|² = ∑ᵢ ‖zᵢ‖²` on `ι → ℂ` is the Hermitian product
`star v ⬝ᵥ w`. -/
theorem leviForm_norm_sq_complexToRealEuclidean (z v w : ι → ℂ) :
    leviForm (fun y ↦ ‖complexToRealEuclidean ι y‖ ^ 2) z v w = star v ⬝ᵥ w := by
  let L : (ι → ℂ) →L[ℂ] EuclideanSpace ℂ ι := (EuclideanSpace.equiv ι ℂ).symm
  have hs : (fun y ↦ ‖complexToRealEuclidean ι y‖ ^ 2) = fun y ↦ ‖L y‖ ^ 2 := by
    funext y
    rw [norm_sq_complexToRealEuclidean, EuclideanSpace.norm_sq_eq]
    simp [L]
  rw [hs, leviForm_norm_sq_comp_apply]
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

/-- For `g` of class `C^n` on `(0, ∞)`, the function `w ↦ g |w|²` on `ι → ℂ` is `C^n` at
every point of `(ι → ℂ) ∖ 0`. -/
theorem contDiffAt_comp_norm_sq_complexToRealEuclidean {n : WithTop ℕ∞} {g : ℝ → ℝ}
    (hg : ContDiffOn ℝ n g (Ioi 0)) (z : puncturedSpace (ι → ℂ)) :
    ContDiffAt ℝ n (fun w ↦ g (‖complexToRealEuclidean ι w‖ ^ 2))
      (z : ι → ℂ) :=
  ContDiffAt.comp (g := g) (f := fun w ↦ ‖complexToRealEuclidean ι w‖ ^ 2) _
    (hg.contDiffAt (Ioi_mem_nhds (norm_sq_complexToRealEuclidean_pos z)))
    contDiff_norm_sq_complexToRealEuclidean.contDiffAt

/-- The Laplacian of a radial function along a holomorphic curve. For `u : ℂ → ι → ℂ` complex
`C²` at `t` and `ψ : ℝ → ℝ` of class `C²` at `s = |u t|²`, a quarter of the Laplacian of
`t ↦ ψ |u t|²` at `t` is `ψ'(s) |v|² + ψ''(s) |star (u t) ⬝ᵥ v|²`, for `v = u'(t)`. -/
theorem laplacian_comp_sum_norm_sq_div_four {ψ : ℝ → ℝ} {u : ℂ → ι → ℂ} {t : ℂ}
    (hψ : ContDiffAt ℝ 2 ψ (∑ i, ‖u t i‖ ^ 2)) (hu : ContDiffAt ℂ 2 u t) :
    Δ (fun s ↦ ψ (∑ i, ‖u s i‖ ^ 2)) t / 4 =
      deriv ψ (∑ i, ‖u t i‖ ^ 2) * ∑ i, ‖deriv u t i‖ ^ 2 +
        deriv (deriv ψ) (∑ i, ‖u t i‖ ^ 2) * Complex.normSq (star (u t) ⬝ᵥ deriv u t) := by
  set N : (ι → ℂ) → ℝ := fun y ↦ ‖complexToRealEuclidean ι y‖ ^ 2
  have hN : ContDiffAt ℝ 2 N (u t) := contDiff_norm_sq_complexToRealEuclidean.contDiffAt
  have hs : N (u t) = ∑ i, ‖u t i‖ ^ 2 := norm_sq_complexToRealEuclidean _
  have hcomp : (fun s ↦ ψ (∑ i, ‖u s i‖ ^ 2)) = (ψ ∘ N) ∘ u :=
    funext fun s ↦ by simp only [Function.comp_apply, N, norm_sq_complexToRealEuclidean]
  have h2 : iteratedDeriv 2 ψ = deriv (deriv ψ) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [← hs] at hψ
  -- `{1}` is an orthonormal basis of `ℂ`, so the Laplacian is four times the Levi form on `1`.
  rw [← sum_re_leviForm_apply_self (OrthonormalBasis.singleton (Fin 1) ℂ), hcomp]
  simp only [Finset.univ_unique, Finset.sum_singleton, OrthonormalBasis.singleton_apply]
  rw [leviForm_comp_apply (hψ.comp _ hN) hu, leviForm_scalar_comp_apply hψ hN,
    leviForm_norm_sq_complexToRealEuclidean, extendRCLike_fderiv_norm_sq_complexToRealEuclidean,
    h2, hs]
  simp only [fderiv_apply_one_eq_deriv]
  have h4 : conj (2 * star (u t) ⬝ᵥ deriv u t) * (2 * star (u t) ⬝ᵥ deriv u t) =
      4 * (Complex.normSq (star (u t) ⬝ᵥ deriv u t) : ℂ) := by
    rw [map_mul, Complex.conj_ofNat, Complex.normSq_eq_conj_mul_self]
    ring
  rw [h4, inv_mul_cancel_left₀ (by norm_num), Complex.add_re, Complex.re_ofReal_mul,
    Complex.re_ofReal_mul, Matrix.re_star_dotProduct_self, Complex.ofReal_re]

end TauCeti

end
