/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Projectivization.FubiniStudy.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import SymplecticGeometry.Analysis.Complex.QuadraticLeviForm
import SymplecticGeometry.LinearAlgebra.Matrix.DotProduct
import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Basic
import TauCeti.Geometry.Manifold.Complex.DdbarForm.Basic
public import TauCeti.Geometry.Manifold.Complex.LeviForm
public import SymplecticGeometry.Geometry.Manifold.Complex.Plurisubharmonic
public import SymplecticGeometry.Geometry.Symplectic.Manifold.Kahler
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

/-!
# Radial potential forms on `ℂⁿ ∖ 0`

For a finite type `ι`, write `Z = TauCeti.puncturedSpace (ι → ℂ)` for `(ι → ℂ) ∖ 0` with the
complex structure `J` of `ι → ℂ`, `s(z) = |z|² = ∑ᵢ ‖zᵢ‖²`, `⟨z, v⟩ = Re ∑ᵢ conj zᵢ vᵢ` and
`ω₀ = stdComplexPiSymplecticForm ι`. A function `g : ℝ → ℝ` that is smooth on
`(0, ∞)` gives the smooth radial potential `g ∘ s` on `Z`; this file computes its form. The
blowup constructions read the forms they build off `Z` in these terms.

* `SymplecticGeometry.radialPotentialForm ι g hg` is the form `(1/4) d (J* d (g ∘ s))` of the
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
  (`TauCeti.leviForm_norm_sq_complexToRealEuclidean`, by `TauCeti.leviForm_norm_sq`),
  and from `∂s = star z ⬝ᵥ ·`
  (`TauCeti.extendRCLike_fderiv_norm_sq_complexToRealEuclidean`). Both are in
  `SymplecticGeometry/Analysis/Complex/QuadraticLeviForm.lean`.
* `SymplecticGeometry.radialPotentialForm_apply_I_smul`: on `(v, i v)` the form is
  `g'(s) |v|² + g''(s) |star z ⬝ᵥ v|²`.
* `SymplecticGeometry.isManifoldStrictlyPlurisubharmonicAt_radialPotential`: if `g' > 0` and
  `(s g')' = g' + s g'' > 0` on `(0, ∞)`, the potential `g ∘ s` is strictly plurisubharmonic on
  `Z`. When `g'' < 0`, Cauchy–Schwarz `|star z ⬝ᵥ v|² ≤ |z|² |v|²`
  (`Matrix.norm_star_dotProduct_sq_le`) bounds the value on `(v, i v)` below by
  `(g' + s g'') |v|²`.
* `SymplecticGeometry.isKahler_radialPotentialForm`: under the same hypotheses the form is Kähler
  for `J`, as a positive multiple of the form of a strictly plurisubharmonic function
  (`SymplecticGeometry.isKahler_mextDerivₗ_covectorComplexStructure`).
* `SymplecticGeometry.radialPotentialForm_id`: for `g = id` the form is `ω₀`, restricted to `Z`.
* `SymplecticGeometry.radialPotentialForm_log`: for `ι = Fin (n + 1)` and `g = log` it is the
  Fubini–Study lift `SymplecticGeometry.fubiniStudyLift n`, since its primitive is
  `(1/4) J* d log |z|²` (`SymplecticGeometry.fubiniStudyPrimitive_eq`).

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §7.1.
-/

public section

open Set TauCeti TauCeti.Manifold TauCeti.ComplexManifold SmoothAlmostComplexStructure
open scoped Manifold ContDiff ComplexConjugate

namespace SymplecticGeometry

variable {ι : Type*} [Fintype ι]

/-- For `g` smooth on `(0, ∞)`, the function `w ↦ g |w|²` on `ι → ℂ` is smooth at
every point of `(ι → ℂ) ∖ 0`. -/
theorem contDiffAt_comp_norm_sq_complexToRealEuclidean {g : ℝ → ℝ}
    (hg : ContDiffOn ℝ ∞ g (Ioi 0)) (z : puncturedSpace (ι → ℂ)) :
    ContDiffAt ℝ ∞ (fun w ↦ g (‖complexToRealEuclidean ι w‖ ^ 2))
      (z : ι → ℂ) :=
  ContDiffAt.comp (g := g) (f := fun w ↦ ‖complexToRealEuclidean ι w‖ ^ 2) _
    (hg.contDiffAt (Ioi_mem_nhds (norm_sq_complexToRealEuclidean_pos z)))
    ((contDiff_norm_sq ℝ).comp (complexToRealEuclidean ι).contDiff).contDiffAt

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

variable (ι) in
/-- The form of the radial potential `g |z|²` on `(ι → ℂ) ∖ 0`, for `g` smooth on `(0, ∞)`:
`(1/4) d (J* d (g ∘ s))`, where `J*` is the almost complex structure `a ↦ -a ∘ J` on one-forms
dual to the complex structure `J` of `(ι → ℂ) ∖ 0`. Its value is `radialPotentialForm_apply`. -/
noncomputable def radialPotentialForm (g : ℝ → ℝ) (hg : ContDiffOn ℝ ∞ g (Ioi 0)) :
    SmoothTwoForm 𝓘(ℝ, ι → ℂ) (puncturedSpace (ι → ℂ)) :=
  (4 : ℝ)⁻¹ • mextDerivₗ 𝓘(ℝ, ι → ℂ) 1
    ((ofComplexManifold (ι → ℂ)
      (puncturedSpace (ι → ℂ))).covectorComplexStructure
        (mextDerivₗ 𝓘(ℝ, ι → ℂ) 0 (SmoothForm.ofFunction (radialPotential hg))))

theorem radialPotentialForm_def (g : ℝ → ℝ) (hg : ContDiffOn ℝ ∞ g (Ioi 0)) :
    radialPotentialForm ι g hg = (4 : ℝ)⁻¹ • mextDerivₗ 𝓘(ℝ, ι → ℂ) 1
      ((ofComplexManifold (ι → ℂ)
        (puncturedSpace (ι → ℂ))).covectorComplexStructure
          (mextDerivₗ 𝓘(ℝ, ι → ℂ) 0 (SmoothForm.ofFunction (radialPotential hg)))) :=
  (rfl)

/-- **The form of a radial potential.** With `s = |z|²`, `⟨z, v⟩ = Re (star z ⬝ᵥ v)` and
`ω₀ = stdComplexPiSymplecticForm ι`, the form of the potential `g ∘ s` is
`g'(s) ω₀(v, w) + g''(s) (⟨z, v⟩ ω₀(z, w) - ⟨z, w⟩ ω₀(z, v))`. The second term is the value of
`(i/2) ∂s ∧ ∂bar s`. -/
theorem radialPotentialForm_apply (g : ℝ → ℝ) (hg : ContDiffOn ℝ ∞ g (Ioi 0))
    (z : puncturedSpace (ι → ℂ)) (v w : TangentSpace 𝓘(ℝ, ι → ℂ) z) :
    (radialPotentialForm ι g hg).eval₂ z v w =
      deriv g (∑ i, ‖(z : ι → ℂ) i‖ ^ 2) *
          stdComplexPiSymplecticForm ι v w +
        deriv (deriv g) (∑ i, ‖(z : ι → ℂ) i‖ ^ 2) *
          ((star (z : ι → ℂ) ⬝ᵥ v).re * stdComplexPiSymplecticForm ι z w -
            (star (z : ι → ℂ) ⬝ᵥ w).re *
              stdComplexPiSymplecticForm ι z v) := by
  set s : (ι → ℂ) → ℝ := fun y ↦ ‖complexToRealEuclidean ι y‖ ^ 2
  have hs : ContDiffAt ℝ 2 s (z : ι → ℂ) :=
    ((contDiff_norm_sq ℝ).comp (complexToRealEuclidean ι).contDiff).contDiffAt
  have hgs : ContDiffAt ℝ 2 g (s z) :=
    (hg.contDiffAt (Ioi_mem_nhds (norm_sq_complexToRealEuclidean_pos z))).of_le (by simp)
  have hu : ContMDiffAt 𝓘(ℝ, ι → ℂ) 𝓘(ℝ) 2 (g ∘ s) (z : ι → ℂ) :=
    ((contDiffAt_comp_norm_sq_complexToRealEuclidean hg z).of_le (by simp)).contMDiffAt
  have hval : ContMDiffAt 𝓘(ℂ, ι → ℂ) 𝓘(ℂ, ι → ℂ) 2
      (Subtype.val : puncturedSpace (ι → ℂ) → _) z := contMDiff_subtypeVal z
  have key := congrFun (coe_mextDerivₗ_covectorComplexStructure_eq_two_smul_ddbarForm
    (u := (g ∘ s) ∘ Subtype.val) (SmoothForm.ofFunction (radialPotential hg)) (fun y ↦ by
      rw [SmoothForm.coe_ofFunction, RoughForm.ofFunction_apply, coe_radialPotential]
      rfl)) z
  rw [SmoothBundleForm.eval₂_apply, radialPotentialForm_def, SmoothForm.smul_toRoughForm,
    Pi.smul_apply, ContinuousAlternatingMap.smul_apply, key, Pi.smul_apply,
    ContinuousAlternatingMap.smul_apply]
  -- Read `v` and `w` as vectors of `ι → ℂ`, where the Levi form takes them.
  revert v w
  intro (v : ι → ℂ) (w : ι → ℂ)
  rw [ddbarForm_apply_of_contMDiffAt (hu.comp z (contMDiff_subtypeVal z)),
    manifoldLeviForm_comp_apply hu hval, mfderiv_subtype_val_apply (I := 𝓘(ℂ, ι → ℂ)) z v,
    mfderiv_subtype_val_apply (I := 𝓘(ℂ, ι → ℂ)) z w, manifoldLeviForm_eq_leviForm,
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

/-- On a vector and its rotation by `i`, the form of the radial potential `g ∘ s` at `z` is the
Levi form `g'(s) |v|² + g''(s) |star z ⬝ᵥ v|²`, where `s = |z|²`. -/
theorem radialPotentialForm_apply_I_smul (g : ℝ → ℝ) (hg : ContDiffOn ℝ ∞ g (Ioi 0))
    (z : puncturedSpace (ι → ℂ)) (v : ι → ℂ) :
    (radialPotentialForm ι g hg).eval₂ z v (Complex.I • v) =
      deriv g (∑ i, ‖(z : ι → ℂ) i‖ ^ 2) * ∑ i, ‖v i‖ ^ 2 +
        deriv (deriv g) (∑ i, ‖(z : ι → ℂ) i‖ ^ 2) *
          Complex.normSq (star (z : ι → ℂ) ⬝ᵥ v) := by
  rw [radialPotentialForm_apply g hg z v (Complex.I • v)]
  simp only [stdComplexPiSymplecticForm_apply_eq_im, dotProduct_smul, smul_eq_mul,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Matrix.re_star_dotProduct_self,
    Complex.normSq_apply]
  ring

/-- **Radial potentials are strictly plurisubharmonic.** If `g' > 0` and `(s g')' > 0` on
`(0, ∞)`, the radial potential `z ↦ g |z|²` is strictly plurisubharmonic at every point of
`(ι → ℂ) ∖ 0`. -/
theorem isManifoldStrictlyPlurisubharmonicAt_radialPotential {g : ℝ → ℝ}
    (hg : ContDiffOn ℝ ∞ g (Ioi 0)) (hg₁ : ∀ s ∈ Ioi (0 : ℝ), 0 < deriv g s)
    (hg₂ : ∀ s ∈ Ioi (0 : ℝ), 0 < deriv (fun t ↦ t * deriv g t) s)
    (z : puncturedSpace (ι → ℂ)) :
    IsManifoldStrictlyPlurisubharmonicAt (ι → ℂ) (radialPotential hg) z := by
  rw [isManifoldStrictlyPlurisubharmonicAt_iff_forall_pos]
  intro v hv
  have h4 : mextDerivₗ 𝓘(ℝ, ι → ℂ) 1
      ((ofComplexManifold (ι → ℂ) (puncturedSpace (ι → ℂ))).covectorComplexStructure
        (mextDerivₗ 𝓘(ℝ, ι → ℂ) 0 (SmoothForm.ofFunction (radialPotential hg)))) =
      (4 : ℝ) • radialPotentialForm ι g hg := by
    rw [radialPotentialForm_def, smul_inv_smul₀ four_ne_zero]
  rw [(SmoothBundleForm.eval₂_apply _ z v (Complex.I • v)).symm.trans (by rw [h4]),
    SmoothForm.eval₂_smul 4 (radialPotentialForm ι g hg) z v (Complex.I • v), smul_eq_mul,
    radialPotentialForm_apply_I_smul g hg z v]
  set s := ∑ i, ‖(z : ι → ℂ) i‖ ^ 2
  have hs : 0 < s := by
    simpa only [s, norm_sq_complexToRealEuclidean] using norm_sq_complexToRealEuclidean_pos z
  have hA : 0 < ∑ i, ‖v i‖ ^ 2 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
    exact Finset.sum_pos' (fun j _ ↦ by positivity)
      ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.2 hi) 2⟩
  -- Cauchy–Schwarz: `|star z ⬝ᵥ v|² ≤ |z|² |v|²`.
  have hCS : Complex.normSq (star (z : ι → ℂ) ⬝ᵥ v) ≤ s * ∑ i, ‖v i‖ ^ 2 := by
    rw [← Complex.sq_norm]
    exact Matrix.norm_star_dotProduct_sq_le (z : ι → ℂ) v
  -- `(s g')' = g' + s g''`.
  have hd : DifferentiableAt ℝ (deriv g) s :=
    ((hg.deriv_of_isOpen (m := 1) isOpen_Ioi (by simp)).differentiableOn
      one_ne_zero).differentiableAt (Ioi_mem_nhds hs)
  have h₂ := hg₂ s hs
  rw [deriv_fun_mul (c := fun t ↦ t) differentiableAt_fun_id hd, deriv_id'', one_mul]
    at h₂
  have h₁ := hg₁ s hs
  have hN := Complex.normSq_nonneg (star (z : ι → ℂ) ⬝ᵥ v)
  rcases le_or_gt 0 (deriv (deriv g) s) with h | h
  · nlinarith [mul_nonneg h hN, mul_pos h₁ hA]
  · nlinarith [mul_le_mul_of_nonpos_left hCS h.le, mul_pos h₂ hA]

/-- **Radial potential forms are Kähler.** If `g' > 0` and `(s g')' > 0` on `(0, ∞)`, the form of
the radial potential `z ↦ g |z|²` is a Kähler form for the complex structure of `(ι → ℂ) ∖ 0`. -/
theorem isKahler_radialPotentialForm {g : ℝ → ℝ} (hg : ContDiffOn ℝ ∞ g (Ioi 0))
    (hg₁ : ∀ s ∈ Ioi (0 : ℝ), 0 < deriv g s)
    (hg₂ : ∀ s ∈ Ioi (0 : ℝ), 0 < deriv (fun t ↦ t * deriv g t) s) :
    (radialPotentialForm ι g hg).IsKahler
      (ofComplexManifold (ι → ℂ) (puncturedSpace (ι → ℂ))) := by
  rw [radialPotentialForm_def]
  exact (isKahler_mextDerivₗ_covectorComplexStructure
    (isManifoldStrictlyPlurisubharmonicAt_radialPotential hg hg₁ hg₂)).smul (by norm_num)

/-- For `g = id` the radial potential form is the standard form `ω₀`, restricted to
`(ι → ℂ) ∖ 0`. -/
theorem radialPotentialForm_id (hg : ContDiffOn ℝ ∞ id (Ioi 0)) :
    radialPotentialForm ι id hg = SmoothForm.mpullback Subtype.val contMDiff_subtypeVal
      (stdComplexPiSymplecticForm ι).constSmooth := by
  refine SmoothBundleForm.ext_eval₂ fun z v w ↦ ?_
  rw [radialPotentialForm_apply, SmoothForm.eval₂_mpullback,
    SymplecticForm.eval₂_constSmooth_mfderiv_eq, mvfderiv_subtype_val_apply,
    mvfderiv_subtype_val_apply]
  simp

/-- For `g = log` the radial potential form is the Fubini–Study lift `ρ`, the pull-back of the
Fubini–Study form to `ℂⁿ⁺¹ ∖ 0`. -/
theorem radialPotentialForm_log (n : ℕ) (hg : ContDiffOn ℝ ∞ Real.log (Ioi 0)) :
    radialPotentialForm (Fin (n + 1)) Real.log hg = fubiniStudyLift n := by
  have h : SmoothForm.ofFunction (radialPotential hg) = fubiniStudyPotential n :=
    SmoothBundleForm.ext fun z v ↦ by
      rw [SmoothForm.coe_ofFunction, fubiniStudyPotential_def, coe_radialPotential]
  rw [radialPotentialForm_def, fubiniStudyLift_def, fubiniStudyPrimitive_eq, map_smul, h]

end SymplecticGeometry

end
