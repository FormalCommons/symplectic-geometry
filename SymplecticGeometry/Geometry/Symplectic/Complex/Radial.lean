/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Projectivization.FubiniStudy.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Basic
import TauCeti.Analysis.Complex.QuadraticLeviForm
import TauCeti.Geometry.Manifold.Complex.DdbarForm.Basic
public import TauCeti.Geometry.Manifold.Complex.LeviForm
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

/-!
# Radial potential forms on `ℂⁿ⁺¹ ∖ 0`

Write `Z = TauCeti.puncturedSpace (Fin (n + 1) → ℂ)` for `ℂⁿ⁺¹ ∖ 0` with the complex structure
`J` of `Fin (n + 1) → ℂ`, `s(z) = |z|² = ∑ᵢ ‖zᵢ‖²`, `⟨z, v⟩ = Re ∑ᵢ conj zᵢ vᵢ` and
`ω₀ = stdComplexPiSymplecticForm (Fin (n + 1))`. A function `g : ℝ → ℝ` that is smooth on
`(0, ∞)` gives the smooth radial potential `g ∘ s` on `Z`; this file computes its form. The
blowup constructions read the forms they build off `Z` in these terms.

* `SymplecticGeometry.radialPotentialForm n g hg` is the form `(1/4) d (J* d (g ∘ s))` of the
  potential `SymplecticGeometry.radialPotential hg = g ∘ s`, where `J*` is
  `covectorComplexStructure`, the real form of `dᶜ`. By `Dolbeault/Potential.lean` it is
  `(i/2) ∂∂bar (g ∘ s)`, and half of Tau Ceti's real (1,1)-form `TauCeti.ddbarForm` of `g ∘ s`
  (`TauCeti.coe_mextDerivₗ_covectorComplexStructure_eq_two_smul_ddbarForm`).
* `SymplecticGeometry.radialPotentialForm_apply`: at `z`, with `s = |z|²`,
  `ω_g(v, w) = g'(s) ω₀(v, w) + g''(s) (⟨z, v⟩ ω₀(z, w) - ⟨z, w⟩ ω₀(z, v))`, the second term
  being the value of `(i/2) ∂s ∧ ∂bar s`. It is read off from the Levi form, since `ddbarForm` is
  twice its imaginary part: Tau Ceti's chain rule `TauCeti.leviForm_scalar_comp_apply` (of which
  `TauCeti.manifoldLeviForm_scalar_comp_apply` is the manifold form) gives the Levi form of
  `g ∘ s`, from that of `s`, the Hermitian product `star v ⬝ᵥ w`
  (`SymplecticGeometry.leviForm_norm_sq_complexToRealEuclidean`, by `TauCeti.leviForm_norm_sq`),
  and from `∂s = star z ⬝ᵥ ·`
  (`SymplecticGeometry.extendRCLike_fderiv_norm_sq_complexToRealEuclidean`).
* `SymplecticGeometry.radialPotentialForm_id`: for `g = id` the form is `ω₀`, restricted to `Z`.
* `SymplecticGeometry.radialPotentialForm_log`: for `g = log` it is the Fubini–Study lift
  `SymplecticGeometry.fubiniStudyLift n`, since its primitive is `(1/4) J* d log |z|²`
  (`SymplecticGeometry.fubiniStudyPrimitive_eq`).

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §7.1.
-/

public section

open Set TauCeti TauCeti.Manifold TauCeti.ComplexManifold SmoothAlmostComplexStructure
open scoped Manifold ContDiff ComplexConjugate

namespace SymplecticGeometry

/-! ### The Levi form of `|z|²` -/

section LeviForm

variable {ι : Type*} [Fintype ι]

/-- The Levi form of `s(z) = |z|² = ∑ᵢ ‖zᵢ‖²` on `ι → ℂ` is the Hermitian product
`star v ⬝ᵥ w`. -/
theorem leviForm_norm_sq_complexToRealEuclidean (z v w : ι → ℂ) :
    leviForm (fun y ↦ ‖complexToRealEuclidean ι y‖ ^ 2) z v w = star v ⬝ᵥ w := by
  set L := (EuclideanSpace.equiv ι ℂ).symm
  have hs : (fun y ↦ ‖complexToRealEuclidean ι y‖ ^ 2) =
      (fun x : EuclideanSpace ℂ ι ↦ ‖x‖ ^ 2) ∘ L := by
    funext y
    rw [Function.comp_apply, norm_sq_complexToRealEuclidean, EuclideanSpace.norm_sq_eq]
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
  simp only [smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    innerSL_apply_apply, inner_complexToRealEuclidean, nsmul_eq_mul, Nat.cast_ofNat,
    dotProduct_smul]
  apply Complex.ext <;> simp

end LeviForm

/-! ### Radial potentials on `ℂⁿ⁺¹ ∖ 0` -/

variable (n : ℕ)

/-- The squared Euclidean norm is positive on `ℂⁿ⁺¹ ∖ 0`. -/
theorem norm_sq_complexToRealEuclidean_pos (z : puncturedSpace (Fin (n + 1) → ℂ)) :
    0 < ‖complexToRealEuclidean (Fin (n + 1)) z‖ ^ 2 :=
  pow_pos (norm_pos_iff.2 (by simpa using mem_puncturedSpace.1 z.property)) 2

variable {n} in
/-- For `g` smooth on `(0, ∞)`, the function `w ↦ g |w|²` on `Fin (n + 1) → ℂ` is smooth at
every point of `ℂⁿ⁺¹ ∖ 0`. -/
theorem contDiffAt_comp_norm_sq_complexToRealEuclidean {g : ℝ → ℝ}
    (hg : ContDiffOn ℝ ∞ g (Ioi 0)) (z : puncturedSpace (Fin (n + 1) → ℂ)) :
    ContDiffAt ℝ ∞ (fun w ↦ g (‖complexToRealEuclidean (Fin (n + 1)) w‖ ^ 2))
      (z : Fin (n + 1) → ℂ) :=
  ContDiffAt.comp (g := g) (f := fun w ↦ ‖complexToRealEuclidean (Fin (n + 1)) w‖ ^ 2) _
    (hg.contDiffAt (Ioi_mem_nhds (norm_sq_complexToRealEuclidean_pos n z)))
    ((contDiff_norm_sq ℝ).comp (complexToRealEuclidean (Fin (n + 1))).contDiff).contDiffAt

variable {n} in
/-- The radial potential `z ↦ g |z|²` on `ℂⁿ⁺¹ ∖ 0`, for `g` smooth on `(0, ∞)`, as a smooth
function (`radialPotential_apply`). -/
noncomputable def radialPotential {g : ℝ → ℝ} (hg : ContDiffOn ℝ ∞ g (Ioi 0)) :
    C^∞⟮𝓘(ℝ, Fin (n + 1) → ℂ), puncturedSpace (Fin (n + 1) → ℂ); ℝ⟯ :=
  ⟨fun z ↦ g (‖complexToRealEuclidean (Fin (n + 1)) z‖ ^ 2), fun z ↦
    (contDiffAt_comp_norm_sq_complexToRealEuclidean hg z).contMDiffAt.comp z
      (contMDiff_subtypeVal z)⟩

variable {n} in
/-- The radial potential is the function `z ↦ g ‖ẑ‖²`, for `ẑ` the image of `z` in
`EuclideanSpace ℝ (Fin (n + 1) ⊕ Fin (n + 1))`. -/
theorem coe_radialPotential {g : ℝ → ℝ} (hg : ContDiffOn ℝ ∞ g (Ioi 0)) :
    ⇑(radialPotential (n := n) hg) =
      fun z : puncturedSpace (Fin (n + 1) → ℂ) ↦ g (‖complexToRealEuclidean (Fin (n + 1)) z‖ ^ 2) :=
  (rfl)

variable {n} in
/-- The radial potential takes the value `g |z|²` at `z`. -/
@[simp]
theorem radialPotential_apply {g : ℝ → ℝ} (hg : ContDiffOn ℝ ∞ g (Ioi 0))
    (z : puncturedSpace (Fin (n + 1) → ℂ)) :
    radialPotential hg z = g (∑ i, ‖(z : Fin (n + 1) → ℂ) i‖ ^ 2) := by
  simp only [coe_radialPotential, norm_sq_complexToRealEuclidean]

/-- The form of the radial potential `g |z|²` on `ℂⁿ⁺¹ ∖ 0`, for `g` smooth on `(0, ∞)`:
`(1/4) d (J* d (g ∘ s))`, where `J*` is the almost complex structure `a ↦ -a ∘ J` on one-forms
dual to the complex structure `J` of `ℂⁿ⁺¹ ∖ 0`. Its value is `radialPotentialForm_apply`. -/
noncomputable def radialPotentialForm (g : ℝ → ℝ) (hg : ContDiffOn ℝ ∞ g (Ioi 0)) :
    SmoothTwoForm 𝓘(ℝ, Fin (n + 1) → ℂ) (puncturedSpace (Fin (n + 1) → ℂ)) :=
  (4 : ℝ)⁻¹ • mextDerivₗ 𝓘(ℝ, Fin (n + 1) → ℂ) 1
    ((ofComplexManifold (Fin (n + 1) → ℂ)
      (puncturedSpace (Fin (n + 1) → ℂ))).covectorComplexStructure
        (mextDerivₗ 𝓘(ℝ, Fin (n + 1) → ℂ) 0 (SmoothForm.ofFunction (radialPotential hg))))

theorem radialPotentialForm_def (g : ℝ → ℝ) (hg : ContDiffOn ℝ ∞ g (Ioi 0)) :
    radialPotentialForm n g hg = (4 : ℝ)⁻¹ • mextDerivₗ 𝓘(ℝ, Fin (n + 1) → ℂ) 1
      ((ofComplexManifold (Fin (n + 1) → ℂ)
        (puncturedSpace (Fin (n + 1) → ℂ))).covectorComplexStructure
          (mextDerivₗ 𝓘(ℝ, Fin (n + 1) → ℂ) 0 (SmoothForm.ofFunction (radialPotential hg)))) :=
  (rfl)

variable {n} in
/-- **The form of a radial potential.** With `s = |z|²`, `⟨z, v⟩ = Re (star z ⬝ᵥ v)` and
`ω₀ = stdComplexPiSymplecticForm (Fin (n + 1))`, the form of the potential `g ∘ s` is
`g'(s) ω₀(v, w) + g''(s) (⟨z, v⟩ ω₀(z, w) - ⟨z, w⟩ ω₀(z, v))`. The second term is the value of
`(i/2) ∂s ∧ ∂bar s`. -/
theorem radialPotentialForm_apply (g : ℝ → ℝ) (hg : ContDiffOn ℝ ∞ g (Ioi 0))
    (z : puncturedSpace (Fin (n + 1) → ℂ)) (v w : TangentSpace 𝓘(ℝ, Fin (n + 1) → ℂ) z) :
    (radialPotentialForm n g hg).eval₂ z v w =
      deriv g (∑ i, ‖(z : Fin (n + 1) → ℂ) i‖ ^ 2) *
          stdComplexPiSymplecticForm (Fin (n + 1)) v w +
        deriv (deriv g) (∑ i, ‖(z : Fin (n + 1) → ℂ) i‖ ^ 2) *
          ((star (z : Fin (n + 1) → ℂ) ⬝ᵥ v).re * stdComplexPiSymplecticForm (Fin (n + 1)) z w -
            (star (z : Fin (n + 1) → ℂ) ⬝ᵥ w).re *
              stdComplexPiSymplecticForm (Fin (n + 1)) z v) := by
  set s : (Fin (n + 1) → ℂ) → ℝ := fun y ↦ ‖complexToRealEuclidean (Fin (n + 1)) y‖ ^ 2
  have hs : ContDiffAt ℝ 2 s (z : Fin (n + 1) → ℂ) :=
    ((contDiff_norm_sq ℝ).comp (complexToRealEuclidean (Fin (n + 1))).contDiff).contDiffAt
  have hgs : ContDiffAt ℝ 2 g (s z) :=
    (hg.contDiffAt (Ioi_mem_nhds (norm_sq_complexToRealEuclidean_pos n z))).of_le (by simp)
  have hu : ContMDiffAt 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ) 2 (g ∘ s) (z : Fin (n + 1) → ℂ) :=
    ((contDiffAt_comp_norm_sq_complexToRealEuclidean hg z).of_le (by simp)).contMDiffAt
  have hval : ContMDiffAt 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) 2
      (Subtype.val : puncturedSpace (Fin (n + 1) → ℂ) → _) z := contMDiff_subtypeVal z
  have key := congrFun (coe_mextDerivₗ_covectorComplexStructure_eq_two_smul_ddbarForm
    (u := (g ∘ s) ∘ Subtype.val) (SmoothForm.ofFunction (radialPotential hg)) (fun y ↦ by
      rw [SmoothForm.coe_ofFunction, RoughForm.ofFunction_apply, coe_radialPotential]
      rfl)) z
  rw [SmoothBundleForm.eval₂_apply, radialPotentialForm_def, SmoothForm.smul_toRoughForm,
    Pi.smul_apply, ContinuousAlternatingMap.smul_apply, key, Pi.smul_apply,
    ContinuousAlternatingMap.smul_apply]
  -- Read `v` and `w` as vectors of `Fin (n + 1) → ℂ`, where the Levi form takes them.
  revert v w
  intro (v : Fin (n + 1) → ℂ) (w : Fin (n + 1) → ℂ)
  rw [ddbarForm_apply_of_contMDiffAt (hu.comp z (contMDiff_subtypeVal z)),
    manifoldLeviForm_comp_apply hu hval, mfderiv_subtype_val_apply (I := 𝓘(ℂ, Fin (n + 1) → ℂ)) z v,
    mfderiv_subtype_val_apply (I := 𝓘(ℂ, Fin (n + 1) → ℂ)) z w, manifoldLeviForm_eq_leviForm,
    leviForm_scalar_comp_apply hgs hs,
    leviForm_norm_sq_complexToRealEuclidean, extendRCLike_fderiv_norm_sq_complexToRealEuclidean,
    extendRCLike_fderiv_norm_sq_complexToRealEuclidean]
  have h2 : iteratedDeriv 2 g = deriv (deriv g) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  beta_reduce
  simp only [stdComplexPiSymplecticForm_apply_eq_im, s, norm_sq_complexToRealEuclidean, h2,
    map_mul, Complex.conj_ofNat, smul_eq_mul]
  norm_num
  ring

/-- For `g = id` the radial potential form is the standard form `ω₀`, restricted to
`ℂⁿ⁺¹ ∖ 0`. -/
theorem radialPotentialForm_id (hg : ContDiffOn ℝ ∞ id (Ioi 0)) :
    radialPotentialForm n id hg = SmoothForm.mpullback Subtype.val contMDiff_subtypeVal
      (stdComplexPiSymplecticForm (Fin (n + 1))).constSmooth := by
  refine SmoothBundleForm.ext_eval₂ fun z v w ↦ ?_
  rw [radialPotentialForm_apply, SmoothForm.eval₂_mpullback,
    SymplecticForm.eval₂_constSmooth_mfderiv_eq, mvfderiv_subtype_val_apply,
    mvfderiv_subtype_val_apply]
  simp

/-- For `g = log` the radial potential form is the Fubini–Study lift `ρ`, the pull-back of the
Fubini–Study form to `ℂⁿ⁺¹ ∖ 0`. -/
theorem radialPotentialForm_log (hg : ContDiffOn ℝ ∞ Real.log (Ioi 0)) :
    radialPotentialForm n Real.log hg = fubiniStudyLift n := by
  have h : SmoothForm.ofFunction (radialPotential hg) = fubiniStudyPotential n :=
    SmoothBundleForm.ext fun z v ↦ by
      rw [SmoothForm.coe_ofFunction, fubiniStudyPotential_def, coe_radialPotential]
  rw [radialPotentialForm_def, fubiniStudyLift_def, fubiniStudyPrimitive_eq, map_smul, h]

end SymplecticGeometry

end
