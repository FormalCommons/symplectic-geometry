/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Projectivization.FubiniStudy.Basic
public import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import SymplecticGeometry.Analysis.Calculus.InverseFunctionTheorem.Deriv
import SymplecticGeometry.Analysis.Complex.QuadraticLeviForm
import SymplecticGeometry.Analysis.InnerProductSpace.PiL2
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Basic
import TauCeti.Geometry.Manifold.Complex.DdbarForm.Basic
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Opens
public import TauCeti.Geometry.Manifold.Complex.LeviForm
public import SymplecticGeometry.Geometry.Manifold.Complex.Plurisubharmonic
import SymplecticGeometry.Geometry.Symplectic.Manifold.Rescale
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
import SymplecticGeometry.Analysis.Complex.Euclidean.Space
import SymplecticGeometry.MeasureTheory.Integral.IntervalIntegral.Primitive
import TauCeti.Analysis.Normed.Group.Basic

/-!
# Radial potential forms on `ℂⁿ ∖ 0`

For a finite type `ι`, write `Z = TauCeti.puncturedSpace (ι → ℂ)` for `(ι → ℂ) ∖ 0` with the
complex structure `J` of `ι → ℂ`, `s(z) = |z|² = ∑ᵢ ‖zᵢ‖²`, `⟨z, v⟩ = Re ∑ᵢ conj zᵢ vᵢ` and
`ω₀ = stdComplexPiSymplecticForm ι`. A function `g : ℝ → ℝ` that is smooth on
`(0, ∞)` gives the smooth radial potential `g ∘ s` on `Z`; this file computes its form. The
blowup constructions read the forms they build off `Z` in these terms.

* `SymplecticGeometry.radialPotentialForm ι g hg` is the form `(1/4) d (J* d (g ∘ s))` of the
  potential `SymplecticGeometry.radialPotential hg = g ∘ s`
  (`Geometry/Manifold/Complex/RadialPotential.lean`), where `J*` is `covectorComplexStructure`,
  the real form of `dᶜ`. By `Dolbeault/Potential.lean` it is `(i/2) ∂∂bar (g ∘ s)`, and half of
  Tau Ceti's real (1,1)-form `TauCeti.ddbarForm` of `g ∘ s`
  (`TauCeti.coe_mextDerivₗ_covectorComplexStructure_eq_two_smul_ddbarForm`).
* `SymplecticGeometry.radialPotentialForm_apply`: at `z`, with `s = |z|²`,
  `ω_g(v, w) = g'(s) ω₀(v, w) + g''(s) (⟨z, v⟩ ω₀(z, w) - ⟨z, w⟩ ω₀(z, v))`, the second term
  being the value of `(i/2) ∂s ∧ ∂bar s`. It is read off from the Levi form, since `ddbarForm` is
  twice its imaginary part: Tau Ceti's chain rule `TauCeti.leviForm_scalar_comp_apply` (of which
  `TauCeti.manifoldLeviForm_scalar_comp_apply` is the manifold form) gives the Levi form of
  `g ∘ s`, from that of `s`, the Hermitian product `star v ⬝ᵥ w`
  (`TauCeti.leviForm_norm_sq_complexToRealEuclidean`, by `TauCeti.leviForm_norm_sq_comp_apply`),
  and from `∂s = star z ⬝ᵥ ·`
  (`TauCeti.extendRCLike_fderiv_norm_sq_complexToRealEuclidean`). Both are in
  `SymplecticGeometry/Analysis/Complex/QuadraticLeviForm.lean`.
* `SymplecticGeometry.radialPotentialForm_apply_I_smul`: on `(v, i v)` the form is
  `g'(s) |v|² + g''(s) |star z ⬝ᵥ v|²`.
* `SymplecticGeometry.isManifoldStrictlyPlurisubharmonicAt_radialPotential`: if `g' > 0` and
  `(s g')' = g' + s g'' > 0` at `s = |z|²`, the potential `g ∘ s` is strictly plurisubharmonic at
  `z`. When `g'' < 0`, Cauchy–Schwarz `|star z ⬝ᵥ v|² ≤ |z|² |v|²`
  (`Matrix.norm_star_dotProduct_sq_le`) bounds the value on `(v, i v)` below by
  `(g' + s g'') |v|²`.
* `SymplecticGeometry.isKahler_radialPotentialForm`: if both hold on `(0, ∞)`, the form is Kähler
  for `J`, as a positive multiple of the form of a strictly plurisubharmonic function
  (`SymplecticGeometry.isKahler_mextDerivₗ_covectorComplexStructure`).
* `SymplecticGeometry.radialPotentialForm_id`: for `g = id` the form is `ω₀`, restricted to `Z`.
* `SymplecticGeometry.radialPotentialForm_log`: for `ι = Fin (n + 1)` and `g = log` it is the
  Fubini–Study lift `SymplecticGeometry.fubiniStudyLift n`, since its primitive is
  `(1/4) J* d log |z|²` (`SymplecticGeometry.fubiniStudyPrimitive_eq`).
* `SymplecticGeometry.radialPotentialForm_add`, `SymplecticGeometry.radialPotentialForm_const_mul`:
  the form is linear in `g`, as its value is; `SymplecticGeometry.radialPotentialForm_congr`: it
  depends only on the values of `g` on `(0, ∞)`.

The second half of the file is about radial maps. For `h : ℝ → ℝ` positive on `(0, ∞)`:

* `SymplecticGeometry.radialMap h hh`: the map `z ↦ √(h(s) / s) • z` of `Z` to itself, with
  `radialMap_apply`, `norm_radialMap` (`|F z|² = h |z|²`) and `contMDiff_radialMap` (for `h`
  smooth on `(0, ∞)`).
* `SymplecticGeometry.radialShell ι h hs hd`: for `h` smooth on `(0, ∞)` with `h' > 0` there, the
  open shell `{w | |w|² ∈ h '' (0, ∞)}` of `ι → ℂ`. For `h s = s + c` it is `{w | c < |w|²}`
  (`SymplecticGeometry.mem_radialShell_add_const`, and `SymplecticGeometry.mem_radialShell_add_sq`
  for `c = l²`).
* `SymplecticGeometry.radialMapDiffeomorph ι h hs hh hd`: the radial map as a diffeomorphism
  of `Z` onto that shell. Its differential is injective because the differential of
  `|F|² = h ∘ s` is `h'(s) ds`, so the radial map is a local diffeomorphism
  (`TauCeti.isLocalDiffeomorphAt_of_injective_mfderiv`). It is bijective onto the shell because
  `h` is strictly increasing, and so it is a diffeomorphism by Mathlib's
  `IsLocalDiffeomorph.diffeomorphOfBijective`.
* `SymplecticGeometry.mpullback_radialMap_stdForm`: the pull-back of `ω₀` along the radial map
  of `h` is `radialPotentialForm ι g hg` for every `g` smooth on `(0, ∞)` with `g'(s) = h(s) / s`
  there. With `F z = ψ(s) z` and `ψ(s) = √(h(s) / s)`, the differential is
  `dF v = ψ v + ψ'(s) ds(v) z` and `ds(v) = 2 ⟨z, v⟩`, so
  `ω₀(dF v, dF w) = ψ² ω₀(v, w) + 2 ψ ψ' (⟨z, v⟩ ω₀(z, w) - ⟨z, w⟩ ω₀(z, v))`, which is
  `radialPotentialForm_apply` as `ψ² = g'` and `(ψ²)' = g''`.
* `SymplecticGeometry.isKahler_mpullback_radialMap`: if moreover `h' > 0` on `(0, ∞)`, that
  pull-back is Kähler, by `isKahler_radialPotentialForm` for the primitive
  `g t = ∫₁ᵗ h(u) / u du`, for which `g' = h / s > 0` and `(s g')' = h' > 0`.
* `SymplecticGeometry.isKahler_mpullback_radialMap_of_profile`: the same for the radial map
  `z ↦ f(|z|) z / |z|` of a profile `f` smooth on `(0, ∞)` with `f > 0` and `f' > 0`, read
  through `h(s) = f(√s)²`, whose derivative `f(√s) f'(√s) / √s` is positive. This is the form in
  which [McDuffSalamon2017], §7.1, states it.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §7.1.
-/

public section

open Set TopologicalSpace TauCeti TauCeti.Manifold TauCeti.ComplexManifold
  SmoothAlmostComplexStructure
open scoped Manifold ContDiff ComplexConjugate

namespace SymplecticGeometry

variable {ι : Type*} [Fintype ι]

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
    contDiff_norm_sq_complexToRealEuclidean.contDiffAt
  have hgs : ContDiffAt ℝ 2 g (s z) :=
    (hg.contDiffAt (Ioi_mem_nhds (norm_sq_complexToRealEuclidean_pos z))).of_le (by simp)
  have hu : ContMDiffAt 𝓘(ℝ, ι → ℂ) 𝓘(ℝ) 2 (g ∘ s) (z : ι → ℂ) :=
    (contDiffAt_comp_norm_sq_complexToRealEuclidean (hg.of_le (by simp)) z).contMDiffAt
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

/-- **Radial potentials are strictly plurisubharmonic.** Let `s = |z|²` at a point `z` of
`(ι → ℂ) ∖ 0`. If `g'(s) > 0` and `(t g')'(s) > 0`, the radial potential `z ↦ g |z|²` is strictly
plurisubharmonic at `z`. -/
theorem isManifoldStrictlyPlurisubharmonicAt_radialPotential {g : ℝ → ℝ}
    (hg : ContDiffOn ℝ ∞ g (Ioi 0)) (z : puncturedSpace (ι → ℂ))
    (hg₁ : 0 < deriv g (∑ i, ‖(z : ι → ℂ) i‖ ^ 2))
    (hg₂ : 0 < deriv (fun t ↦ t * deriv g t) (∑ i, ‖(z : ι → ℂ) i‖ ^ 2)) :
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
  have hA : 0 < ∑ i, ‖v i‖ ^ 2 := sum_norm_sq_pos hv
  -- Cauchy–Schwarz: `|star z ⬝ᵥ v|² ≤ |z|² |v|²`.
  have hCS : Complex.normSq (star (z : ι → ℂ) ⬝ᵥ v) ≤ s * ∑ i, ‖v i‖ ^ 2 := by
    rw [← Complex.sq_norm]
    exact Matrix.norm_star_dotProduct_sq_le (z : ι → ℂ) v
  -- `(s g')' = g' + s g''`.
  have hd : DifferentiableAt ℝ (deriv g) s :=
    ((hg.deriv_of_isOpen (m := 1) isOpen_Ioi (by simp)).differentiableOn
      one_ne_zero).differentiableAt (Ioi_mem_nhds hs)
  rw [deriv_fun_mul (c := fun t ↦ t) differentiableAt_fun_id hd, deriv_id'', one_mul]
    at hg₂
  have hN := Complex.normSq_nonneg (star (z : ι → ℂ) ⬝ᵥ v)
  rcases le_or_gt 0 (deriv (deriv g) s) with h | h
  · nlinarith [mul_nonneg h hN, mul_pos hg₁ hA]
  · nlinarith [mul_le_mul_of_nonpos_left hCS h.le, mul_pos hg₂ hA]

/-- **Radial potential forms are Kähler.** If `g' > 0` and `(s g')' > 0` on `(0, ∞)`, the form of
the radial potential `z ↦ g |z|²` is a Kähler form for the complex structure of `(ι → ℂ) ∖ 0`. -/
theorem isKahler_radialPotentialForm {g : ℝ → ℝ} (hg : ContDiffOn ℝ ∞ g (Ioi 0))
    (hg₁ : ∀ s ∈ Ioi (0 : ℝ), 0 < deriv g s)
    (hg₂ : ∀ s ∈ Ioi (0 : ℝ), 0 < deriv (fun t ↦ t * deriv g t) s) :
    (radialPotentialForm ι g hg).IsKahler
      (ofComplexManifold (ι → ℂ) (puncturedSpace (ι → ℂ))) := by
  rw [radialPotentialForm_def]
  refine (isKahler_mextDerivₗ_covectorComplexStructure fun z ↦ ?_).smul _ (by norm_num)
  have hz : ∑ i, ‖(z : ι → ℂ) i‖ ^ 2 ∈ Ioi 0 := by
    simpa only [mem_Ioi, norm_sq_complexToRealEuclidean] using norm_sq_complexToRealEuclidean_pos z
  exact isManifoldStrictlyPlurisubharmonicAt_radialPotential hg z (hg₁ _ hz) (hg₂ _ hz)

/-- The radial potential form depends only on the values of the potential on `(0, ∞)`. -/
theorem radialPotentialForm_congr {g g' : ℝ → ℝ} (hg : ContDiffOn ℝ ∞ g (Ioi 0))
    (hg' : ContDiffOn ℝ ∞ g' (Ioi 0)) (h : EqOn g g' (Ioi 0)) :
    radialPotentialForm ι g hg = radialPotentialForm ι g' hg' := by
  refine SmoothBundleForm.ext_eval₂ fun z v w ↦ ?_
  have hz : ∑ i, ‖(z : ι → ℂ) i‖ ^ 2 ∈ Ioi 0 := by
    simpa only [mem_Ioi, norm_sq_complexToRealEuclidean] using norm_sq_complexToRealEuclidean_pos z
  have he : g =ᶠ[nhds (∑ i, ‖(z : ι → ℂ) i‖ ^ 2)] g' :=
    Filter.eventuallyEq_of_mem (Ioi_mem_nhds hz) h
  rw [radialPotentialForm_apply, radialPotentialForm_apply, he.deriv_eq, he.deriv.deriv_eq]

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
  rw [radialPotentialForm_def, fubiniStudyLift_def, fubiniStudyPrimitive_eq, map_smul,
    fubiniStudyPotential_def]

/-- The radial potential form is additive in the potential: the form of `g₁ + g₂` is the sum of
the forms of `g₁` and `g₂`. -/
theorem radialPotentialForm_add {g₁ g₂ : ℝ → ℝ} (hg₁ : ContDiffOn ℝ ∞ g₁ (Ioi 0))
    (hg₂ : ContDiffOn ℝ ∞ g₂ (Ioi 0)) :
    radialPotentialForm ι (fun s ↦ g₁ s + g₂ s) (hg₁.add hg₂) =
      radialPotentialForm ι g₁ hg₁ + radialPotentialForm ι g₂ hg₂ := by
  refine SmoothBundleForm.ext_eval₂ fun z v w ↦ ?_
  rw [SmoothBundleForm.eval₂_add, radialPotentialForm_apply, radialPotentialForm_apply,
    radialPotentialForm_apply]
  have hz : ∑ i, ‖(z : ι → ℂ) i‖ ^ 2 ∈ Ioi 0 := by
    simpa only [mem_Ioi, norm_sq_complexToRealEuclidean] using norm_sq_complexToRealEuclidean_pos z
  have hd : ∀ {g : ℝ → ℝ}, ContDiffOn ℝ ∞ g (Ioi 0) → ∀ t ∈ Ioi (0 : ℝ),
      DifferentiableAt ℝ g t ∧ DifferentiableAt ℝ (deriv g) t := fun hg t ht ↦
    ⟨(hg.contDiffAt (Ioi_mem_nhds ht)).differentiableAt (by simp),
      ((hg.deriv_of_isOpen isOpen_Ioi (m := 1) (by simp)).contDiffAt
        (Ioi_mem_nhds ht)).differentiableAt (by simp)⟩
  have h1 : deriv (fun s ↦ g₁ s + g₂ s) =ᶠ[nhds (∑ i, ‖(z : ι → ℂ) i‖ ^ 2)]
      fun s ↦ deriv g₁ s + deriv g₂ s :=
    Filter.eventuallyEq_of_mem (Ioi_mem_nhds hz) fun t ht ↦
      deriv_add (hd hg₁ t ht).1 (hd hg₂ t ht).1
  rw [h1.deriv_eq, h1.eq_of_nhds, deriv_fun_add (hd hg₁ _ hz).2 (hd hg₂ _ hz).2]
  ring

/-- The radial potential form is homogeneous in the potential: the form of `c g` is `c` times
the form of `g`. -/
theorem radialPotentialForm_const_mul (c : ℝ) {g : ℝ → ℝ} (hg : ContDiffOn ℝ ∞ g (Ioi 0)) :
    radialPotentialForm ι (fun s ↦ c * g s) (contDiffOn_const.mul hg) =
      c • radialPotentialForm ι g hg := by
  refine SmoothBundleForm.ext_eval₂ fun z v w ↦ ?_
  rw [SmoothForm.eval₂_smul, radialPotentialForm_apply, radialPotentialForm_apply,
    deriv_const_mul_field', deriv_const_mul_field', smul_eq_mul]
  ring

/-! ### Radial maps -/

variable {h : ℝ → ℝ}

/-- The map `w ↦ √(h |w|² / |w|²) • w` of `ι → ℂ`, which `radialMap` restricts. -/
private noncomputable def radialScale (h : ℝ → ℝ) (w : ι → ℂ) : ι → ℂ :=
  √(h (‖complexToRealEuclidean ι w‖ ^ 2) / ‖complexToRealEuclidean ι w‖ ^ 2) • w

private theorem norm_sq_radialScale (hh : ∀ s ∈ Ioi (0 : ℝ), 0 < h s) {w : ι → ℂ}
    (hw : 0 < ‖complexToRealEuclidean ι w‖ ^ 2) :
    ‖complexToRealEuclidean ι (radialScale h w)‖ ^ 2 = h (‖complexToRealEuclidean ι w‖ ^ 2) := by
  rw [radialScale, map_smul, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  set s := ‖complexToRealEuclidean ι w‖ ^ 2
  rw [Real.sq_sqrt (div_pos (hh s hw) hw).le, div_mul_cancel₀ _ hw.ne']

private theorem contDiffAt_radialScale (hs : ContDiffOn ℝ ∞ h (Ioi 0))
    (hh : ∀ s ∈ Ioi (0 : ℝ), 0 < h s) (z : puncturedSpace (ι → ℂ)) :
    ContDiffAt ℝ ∞ (radialScale h) (z : ι → ℂ) :=
  (contDiffAt_comp_norm_sq_complexToRealEuclidean ((hs.div contDiffOn_id fun _ ht ↦
    ne_of_gt ht).sqrt fun t ht ↦ (div_pos (hh t ht) ht).ne') z).smul contDiffAt_id

/-- The derivative of `radialScale h` at `w ≠ 0`: with `N = |·|²` and `ψ t = √(h t / t)`, it is
`v ↦ ψ (N w) • v + (ψ' (N w) * N'(w) v) • w`. -/
private theorem hasFDerivAt_radialScale (hs : ContDiffOn ℝ ∞ h (Ioi 0))
    (hh : ∀ s ∈ Ioi (0 : ℝ), 0 < h s) {w : ι → ℂ}
    (hw : 0 < ‖complexToRealEuclidean ι w‖ ^ 2) :
    HasFDerivAt (radialScale h)
      (√(h (‖complexToRealEuclidean ι w‖ ^ 2) / ‖complexToRealEuclidean ι w‖ ^ 2) •
          ContinuousLinearMap.id ℝ (ι → ℂ) +
        (deriv (fun t ↦ √(h t / t)) (‖complexToRealEuclidean ι w‖ ^ 2) •
          fderiv ℝ (fun y ↦ ‖complexToRealEuclidean ι y‖ ^ 2) w).smulRight w) w := by
  have hhd : HasDerivAt h (deriv h _) (‖complexToRealEuclidean ι w‖ ^ 2) :=
    ((hs.contDiffAt (Ioi_mem_nhds hw)).differentiableAt (by simp)).hasDerivAt
  have hψd : DifferentiableAt ℝ (fun t ↦ √(h t / t)) (‖complexToRealEuclidean ι w‖ ^ 2) :=
    (DifferentiableAt.div hhd.differentiableAt differentiableAt_id hw.ne').sqrt
      (div_pos (hh _ hw) hw).ne'
  exact (hψd.hasDerivAt.comp_hasFDerivAt w
    ((contDiff_norm_sq_complexToRealEuclidean (n := 1)).differentiable one_ne_zero
      w).hasFDerivAt).smul
      (hasFDerivAt_id w)

/-- The differential of `radialScale h` is injective where `h' > 0`: the differential of
`|F|² = h ∘ |·|²` kills the radial part of a vector in its kernel, and then the scalar factor
`√(h s / s) ≠ 0` kills the rest. -/
private theorem injective_fderiv_radialScale (hs : ContDiffOn ℝ ∞ h (Ioi 0))
    (hh : ∀ s ∈ Ioi (0 : ℝ), 0 < h s) (hd : ∀ s ∈ Ioi (0 : ℝ), 0 < deriv h s) {w : ι → ℂ}
    (hw : 0 < ‖complexToRealEuclidean ι w‖ ^ 2) :
    Function.Injective (fderiv ℝ (radialScale h) w) := by
  have hF := hasFDerivAt_radialScale hs hh hw
  set N : (ι → ℂ) → ℝ := fun w ↦ ‖complexToRealEuclidean ι w‖ ^ 2
  have hNd : ∀ y, HasFDerivAt N (fderiv ℝ N y) y := fun y ↦
    ((contDiff_norm_sq_complexToRealEuclidean (n := 1)).differentiable one_ne_zero y).hasFDerivAt
  have hhd : HasDerivAt h (deriv h (N w)) (N w) :=
    ((hs.contDiffAt (Ioi_mem_nhds hw)).differentiableAt (by simp)).hasDerivAt
  have heq : N ∘ radialScale h =ᶠ[nhds w] h ∘ N :=
    ((contDiff_norm_sq_complexToRealEuclidean (n := 0)).continuous.continuousAt.eventually
      (Ioi_mem_nhds hw)).mono fun y hy ↦ norm_sq_radialScale hh hy
  have hchain : (fderiv ℝ N (radialScale h w)).comp (fderiv ℝ (radialScale h) w) =
      deriv h (N w) • fderiv ℝ N w := by
    rw [← ((hNd _).comp w hF.differentiableAt.hasFDerivAt).fderiv, heq.fderiv_eq,
      (hhd.comp_hasFDerivAt w (hNd w)).fderiv]
  refine (injective_iff_map_eq_zero _).2 fun v hv ↦ ?_
  have h1 : deriv h (N w) * fderiv ℝ N w v = 0 := by
    simpa [hv] using (congrArg (· v) hchain).symm
  have h2 : fderiv ℝ N w v = 0 := (mul_eq_zero.1 h1).resolve_left (hd _ hw).ne'
  rw [hF.fderiv] at hv
  simp only [add_apply, smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, h2, smul_zero, zero_smul, add_zero] at hv
  exact (smul_eq_zero.1 hv).resolve_left (Real.sqrt_ne_zero'.2 (div_pos (hh _ hw) hw))

private theorem radialScale_mem_puncturedSpace (hh : ∀ s ∈ Ioi (0 : ℝ), 0 < h s)
    (z : puncturedSpace (ι → ℂ)) : radialScale h (z : ι → ℂ) ∈ puncturedSpace (ι → ℂ) := by
  have hz := norm_sq_complexToRealEuclidean_pos z
  exact mem_puncturedSpace.2 (smul_ne_zero (Real.sqrt_ne_zero'.2 (div_pos (hh _ hz) hz))
    (mem_puncturedSpace.1 z.property))

/-- The radial map `z ↦ √(h |z|² / |z|²) • z` of `(ι → ℂ) ∖ 0` to itself, for `h : ℝ → ℝ`
positive on `(0, ∞)`, with `|z|² = ∑ᵢ ‖zᵢ‖²`. It maps the sphere `|z|² = s` into the sphere
`|w|² = h s` (`norm_radialMap`). -/
noncomputable def radialMap (h : ℝ → ℝ) (hh : ∀ s ∈ Ioi (0 : ℝ), 0 < h s)
    (z : puncturedSpace (ι → ℂ)) : puncturedSpace (ι → ℂ) :=
  ⟨radialScale h z, radialScale_mem_puncturedSpace hh z⟩

private theorem val_radialMap (hh : ∀ s ∈ Ioi (0 : ℝ), 0 < h s) (z : puncturedSpace (ι → ℂ)) :
    (radialMap h hh z : ι → ℂ) = radialScale h z :=
  rfl

/-- The radial map takes `z` to `√(h |z|² / |z|²) • z`. -/
@[simp]
theorem radialMap_apply (hh : ∀ s ∈ Ioi (0 : ℝ), 0 < h s) (z : puncturedSpace (ι → ℂ)) :
    (radialMap h hh z : ι → ℂ) =
      √(h (∑ i, ‖(z : ι → ℂ) i‖ ^ 2) / ∑ i, ‖(z : ι → ℂ) i‖ ^ 2) • (z : ι → ℂ) := by
  rw [val_radialMap, radialScale, norm_sq_complexToRealEuclidean]

/-- The radial map takes the sphere `|z|² = s` into the sphere `|w|² = h s`. -/
theorem norm_radialMap (hh : ∀ s ∈ Ioi (0 : ℝ), 0 < h s) (z : puncturedSpace (ι → ℂ)) :
    ‖complexToRealEuclidean ι (radialMap h hh z)‖ ^ 2 =
      h (‖complexToRealEuclidean ι z‖ ^ 2) :=
  norm_sq_radialScale hh (norm_sq_complexToRealEuclidean_pos z)

/-- For `h` smooth on `(0, ∞)`, the radial map is smooth. -/
theorem contMDiff_radialMap (hs : ContDiffOn ℝ ∞ h (Ioi 0))
    (hh : ∀ s ∈ Ioi (0 : ℝ), 0 < h s) :
    ContMDiff 𝓘(ℝ, ι → ℂ) 𝓘(ℝ, ι → ℂ) ∞ (radialMap (ι := ι) h hh) :=
  (ContMDiff.subtypeVal_comp_iff (puncturedSpace (ι → ℂ)) (radialMap h hh)).1 fun z ↦
    (contDiffAt_radialScale hs hh z).contMDiffAt.comp z
      (contMDiff_subtypeVal z)

variable (ι) in
/-- The open shell `{w | |w|² ∈ h '' (0, ∞)}` of `ι → ℂ`, for `h` smooth on `(0, ∞)` with
positive derivative there. As `h` is increasing, this is the shell between the squared radii
`h (0⁺)` and `h (∞)`. The radial map is a diffeomorphism onto it (`radialMapDiffeomorph`). -/
noncomputable def radialShell (h : ℝ → ℝ) (hs : ContDiffOn ℝ ∞ h (Ioi 0))
    (hd : ∀ s ∈ Ioi (0 : ℝ), 0 < deriv h s) : Opens (ι → ℂ) :=
  ⟨{w | ‖complexToRealEuclidean ι w‖ ^ 2 ∈ h '' Ioi 0},
    ((hs.of_le (by simp)).isOpen_image_of_deriv_ne_zero isOpen_Ioi fun t ht ↦
      (hd t ht).ne').preimage (contDiff_norm_sq_complexToRealEuclidean (n := 0)).continuous⟩

/-- A point is in the shell of `h` if and only if its squared norm `∑ᵢ ‖wᵢ‖²` is a value of `h`
on `(0, ∞)`. -/
@[simp]
theorem mem_radialShell (hs : ContDiffOn ℝ ∞ h (Ioi 0))
    (hd : ∀ s ∈ Ioi (0 : ℝ), 0 < deriv h s) {w : ι → ℂ} :
    w ∈ radialShell ι h hs hd ↔ ∑ i, ‖w i‖ ^ 2 ∈ h '' Ioi 0 := by
  rw [← norm_sq_complexToRealEuclidean]
  rfl

/-- A point is in the shell of `s ↦ s + c` exactly when its squared norm `∑ᵢ ‖wᵢ‖²` is greater
than `c`. -/
theorem mem_radialShell_add_const {c : ℝ} {w : ι → ℂ} :
    w ∈ radialShell ι (fun s ↦ s + c) (contDiffOn_id.add contDiffOn_const) (fun _ _ ↦ by simp) ↔
      c < ∑ i, ‖w i‖ ^ 2 := by
  rw [mem_radialShell, image_add_const_Ioi, zero_add, mem_Ioi]

/-- For `0 ≤ l`, a point is in the shell of `s ↦ s + l²` exactly when its Euclidean norm is
greater than `l`. -/
theorem mem_radialShell_add_sq {l : ℝ} (hl : 0 ≤ l) {w : ι → ℂ} :
    w ∈ radialShell ι (fun s ↦ s + l ^ 2) (contDiffOn_id.add contDiffOn_const)
        (fun _ _ ↦ by simp) ↔
      l < ‖complexToRealEuclidean ι w‖ := by
  rw [mem_radialShell_add_const, ← norm_sq_complexToRealEuclidean,
    pow_lt_pow_iff_left₀ hl (norm_nonneg _) two_ne_zero]

section Diffeomorph

variable (hs : ContDiffOn ℝ ∞ h (Ioi 0)) (hh : ∀ s ∈ Ioi (0 : ℝ), 0 < h s)
  (hd : ∀ s ∈ Ioi (0 : ℝ), 0 < deriv h s)
include hs hh hd

/-- The radial map, with values in its shell. -/
private noncomputable def radialMapShell (z : puncturedSpace (ι → ℂ)) :
    radialShell ι h hs hd :=
  ⟨radialScale h z, by
    have hz := norm_sq_complexToRealEuclidean_pos z
    exact ⟨_, hz, (norm_sq_radialScale hh hz).symm⟩⟩

private theorem val_radialMapShell (z : puncturedSpace (ι → ℂ)) :
    (radialMapShell hs hh hd z : ι → ℂ) = radialScale h z :=
  rfl

private theorem isLocalDiffeomorph_radialMapShell :
    IsLocalDiffeomorph 𝓘(ℝ, ι → ℂ) 𝓘(ℝ, ι → ℂ) ∞ (radialMapShell (ι := ι) hs hh hd) := by
  refine isLocalDiffeomorph_subtypeVal_comp_iff.1 fun z ↦ ?_
  have hz := norm_sq_complexToRealEuclidean_pos z
  have hg : IsLocalDiffeomorphAt 𝓘(ℝ, ι → ℂ) 𝓘(ℝ, ι → ℂ) ∞ (radialScale h) (z : ι → ℂ) :=
    isLocalDiffeomorphAt_of_injective_mfderiv
      (fun w hw ↦ (contDiffAt_radialScale hs hh ⟨w, hw⟩).contMDiffAt.contMDiffWithinAt)
      (puncturedSpace (ι → ℂ)).isOpen z.property
      BoundarylessManifold.isInteriorPoint (by simp)
      (by rw [mfderiv_eq_fderiv]; exact injective_fderiv_radialScale hs hh hd hz) rfl
  exact (isLocalDiffeomorph_subtype_val (I := 𝓘(ℝ, ι → ℂ)) z).comp (hg := hg)

private theorem bijective_radialMapShell :
    Function.Bijective (radialMapShell (ι := ι) hs hh hd) := by
  have hmono : StrictMonoOn h (Ioi 0) :=
    strictMonoOn_of_deriv_pos (convex_Ioi 0) hs.continuousOn
      fun t ht ↦ hd t (interior_subset ht)
  refine ⟨fun z z' hzz' ↦ ?_, fun w ↦ ?_⟩
  · have hzz : radialScale h (z : ι → ℂ) = radialScale h z' := congrArg Subtype.val hzz'
    have hz := norm_sq_complexToRealEuclidean_pos z
    have hz' := norm_sq_complexToRealEuclidean_pos z'
    have hN : ‖complexToRealEuclidean ι z‖ ^ 2 = ‖complexToRealEuclidean ι z'‖ ^ 2 :=
      hmono.injOn (mem_Ioi.2 hz) (mem_Ioi.2 hz') (by
        rw [← norm_sq_radialScale hh hz, ← norm_sq_radialScale hh hz', hzz])
    rw [radialScale, radialScale, hN] at hzz
    exact Subtype.ext
      (smul_right_injective _ (Real.sqrt_ne_zero'.2 (div_pos (hh _ hz') hz')) hzz)
  · -- `w` with `|w|² = h t` is the image of `√(t / |w|²) • w`, of squared norm `t`.
    obtain ⟨t, ht, hw⟩ := w.property
    set N := ‖complexToRealEuclidean ι (w : ι → ℂ)‖ ^ 2 with hN
    have hN0 : 0 < N := hw ▸ hh t ht
    have hw0 : (w : ι → ℂ) ≠ 0 := by
      rintro h0
      simp [hN, h0] at hN0
    have hzN := norm_sq_radialScale (h := fun _ ↦ t) (w := (w : ι → ℂ)) (fun _ _ ↦ ht) hN0
    rw [radialScale] at hzN
    refine ⟨⟨√(t / N) • (w : ι → ℂ),
      mem_puncturedSpace.2 (smul_ne_zero (Real.sqrt_ne_zero'.2 (div_pos ht hN0)) hw0)⟩,
      Subtype.ext ?_⟩
    rw [val_radialMapShell, Subtype.coe_mk]
    rw [radialScale, hzN, smul_smul, ← Real.sqrt_mul (div_pos (hh t ht) ht).le, hw,
      div_mul_div_cancel₀ ht.ne', div_self hN0.ne', Real.sqrt_one, one_smul]

variable (ι h) in
/-- For `h` smooth on `(0, ∞)`, positive there with positive derivative, the radial map is a
diffeomorphism of `(ι → ℂ) ∖ 0` onto the shell `{w | |w|² ∈ h '' (0, ∞)}`
(`coe_radialMapDiffeomorph_apply`). -/
noncomputable def radialMapDiffeomorph :
    puncturedSpace (ι → ℂ) ≃ₘ^∞⟮𝓘(ℝ, ι → ℂ), 𝓘(ℝ, ι → ℂ)⟯ radialShell ι h hs hd :=
  (isLocalDiffeomorph_radialMapShell hs hh hd).diffeomorphOfBijective
    (bijective_radialMapShell hs hh hd)

/-- The diffeomorphism onto the shell is the radial map. -/
@[simp]
theorem coe_radialMapDiffeomorph_apply (z : puncturedSpace (ι → ℂ)) :
    (radialMapDiffeomorph ι h hs hh hd z : ι → ℂ) = radialMap h hh z := by
  rw [radialMapDiffeomorph, IsLocalDiffeomorph.coe_diffeomorphOfBijective, val_radialMapShell,
    val_radialMap]

end Diffeomorph

/-! ### The pull-back of `ω₀` along a radial map -/

/-- **The pull-back of `ω₀` along a radial map.** For `h` smooth and positive on `(0, ∞)`, the
pull-back of the standard form `ω₀` of `(ι → ℂ) ∖ 0` along the radial map
`z ↦ √(h |z|² / |z|²) • z` is the radial potential form of any `g` smooth on `(0, ∞)` with
`g'(s) = h(s) / s` there. -/
theorem mpullback_radialMap_stdForm (hs : ContDiffOn ℝ ∞ h (Ioi 0))
    (hh : ∀ s ∈ Ioi (0 : ℝ), 0 < h s) {g : ℝ → ℝ} (hg : ContDiffOn ℝ ∞ g (Ioi 0))
    (hgh : ∀ s ∈ Ioi (0 : ℝ), deriv g s = h s / s) :
    SmoothForm.mpullback (radialMap h hh) (contMDiff_radialMap hs hh)
        (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal
          (stdComplexPiSymplecticForm ι).constSmooth) =
      radialPotentialForm ι g hg := by
  refine SmoothBundleForm.ext_eval₂ fun z v w ↦ ?_
  have hcomp : (Subtype.val ∘ radialMap h hh : puncturedSpace (ι → ℂ) → ι → ℂ) =
      radialScale h ∘ Subtype.val := funext (val_radialMap hh)
  rw [SmoothForm.mpullback_mpullback, SmoothForm.eval₂_mpullback,
    SymplecticForm.eval₂_constSmooth_mfderiv_eq, hcomp]
  have hD (u : TangentSpace 𝓘(ℝ, ι → ℂ) z) :
      mvfderiv 𝓘(ℝ, ι → ℂ) (radialScale h ∘ Subtype.val) z u = fderiv ℝ (radialScale h) z u :=
    by rw [mvfderiv_comp_subtype_val]; exact mvfderiv_eq_fderiv_apply _ _ u
  rw [hD, hD, radialPotentialForm_apply, ← norm_sq_complexToRealEuclidean]
  -- Read `v` and `w` as vectors of `ι → ℂ`.
  revert v w
  intro (v : ι → ℂ) (w : ι → ℂ)
  have hz := norm_sq_complexToRealEuclidean_pos z
  set S := ‖complexToRealEuclidean ι (z : ι → ℂ)‖ ^ 2
  set ψ : ℝ → ℝ := fun t ↦ √(h t / t)
  rw [(hasFDerivAt_radialScale hs hh hz).fderiv,
    ((complexToRealEuclidean ι).hasFDerivAt.norm_sq).fderiv]
  -- `g' = ψ²` near `S`, so `g'' (S) = 2 ψ(S) ψ'(S)`.
  have hψ : ∀ t ∈ Ioi (0 : ℝ), ψ t ^ 2 = deriv g t := fun t ht ↦ by
    rw [hgh t ht, Real.sq_sqrt (div_pos (hh t ht) ht).le]
  have hψd : DifferentiableAt ℝ ψ S :=
    (DifferentiableAt.div (((hs.contDiffAt (Ioi_mem_nhds hz)).differentiableAt (by simp)))
      differentiableAt_id hz.ne').sqrt (div_pos (hh _ hz) hz).ne'
  have h1 : deriv g S = ψ S ^ 2 := (hψ S hz).symm
  have h2 : deriv (deriv g) S = 2 * ψ S * deriv ψ S := by
    rw [← (Filter.eventuallyEq_of_mem (Ioi_mem_nhds hz) hψ).deriv_eq,
      (hψd.hasDerivAt.fun_pow 2).deriv]
    ring
  rw [h1, h2]
  simp only [add_apply, smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, innerSL_apply_apply, inner_complexToRealEuclidean,
    stdComplexPiSymplecticForm_apply_eq_im, dotProduct_add, add_dotProduct, dotProduct_smul,
    star_add, star_smul, smul_dotProduct, smul_eq_mul, nsmul_eq_mul]
  have hvz : (star v ⬝ᵥ (z : ι → ℂ)).im = -(star (z : ι → ℂ) ⬝ᵥ v).im := by
    rw [← stdComplexPiSymplecticForm_apply_eq_im, ← stdComplexPiSymplecticForm_apply_eq_im,
      SymplecticForm.neg_eq]
  have hzz : (star (z : ι → ℂ) ⬝ᵥ (z : ι → ℂ)).im = 0 := by
    rw [← stdComplexPiSymplecticForm_apply_eq_im, SymplecticForm.self_eq_zero]
  simp only [star_trivial, Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, hvz, hzz, zero_mul, add_zero, Nat.cast_ofNat, ψ, S]
  ring

/-- **Radial maps pull `ω₀` back to Kähler forms.** For `h` smooth on `(0, ∞)` with `h > 0` and
`h' > 0` there, the pull-back of the standard form `ω₀` of `(ι → ℂ) ∖ 0` along the radial map
`z ↦ √(h |z|² / |z|²) • z` is a Kähler form for the complex structure of `(ι → ℂ) ∖ 0`. -/
theorem isKahler_mpullback_radialMap (hs : ContDiffOn ℝ ∞ h (Ioi 0))
    (hh : ∀ s ∈ Ioi (0 : ℝ), 0 < h s) (hd : ∀ s ∈ Ioi (0 : ℝ), 0 < deriv h s) :
    SmoothTwoForm.IsKahler
      (SmoothForm.mpullback (radialMap h hh) (contMDiff_radialMap hs hh)
        (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal
          (stdComplexPiSymplecticForm ι).constSmooth))
      (ofComplexManifold (ι → ℂ) (puncturedSpace (ι → ℂ))) := by
  -- `g = ∫₁ h(u) / u du` is a primitive of `h(s) / s` on `(0, ∞)`.
  set q : ℝ → ℝ := fun t ↦ h t / t
  have hq : ContDiffOn ℝ ∞ q (Ioi 0) := hs.div contDiffOn_id fun _ ht ↦ ne_of_gt ht
  set g : ℝ → ℝ := fun t ↦ ∫ u in (1 : ℝ)..t, q u
  have hgq : EqOn (deriv g) q (Ioi 0) :=
    hq.continuousOn.eqOn_deriv_integral_of_ordConnected isOpen_Ioi ordConnected_Ioi one_pos
  have hg : ContDiffOn ℝ ∞ g (Ioi 0) :=
    hq.contDiffOn_add_one_integral isOpen_Ioi ordConnected_Ioi one_pos
  rw [mpullback_radialMap_stdForm hs hh hg hgq]
  refine isKahler_radialPotentialForm hg (fun s hs ↦ ?_) (fun s hs ↦ ?_)
  · rw [hgq hs]
    exact div_pos (hh s hs) hs
  · -- `t g'(t) = h t` near `s`.
    have heq : (fun t ↦ t * deriv g t) =ᶠ[nhds s] h :=
      Filter.eventuallyEq_of_mem (Ioi_mem_nhds hs) fun t ht ↦ by
        rw [hgq ht, mul_div_cancel₀ _ (ne_of_gt ht)]
    rw [heq.deriv_eq]
    exact hd s hs

/-- **Radial maps pull `ω₀` back to Kähler forms**, for a radial map `z ↦ f(|z|) z / |z|` given
by its radial profile `f`. Let `f` be smooth on `(0, ∞)`, with `f > 0` and `f' > 0` there, and
let `h` be smooth and positive on `(0, ∞)` with `h(s) = f(√s)²` there, so that the radial map
of `h` is `z ↦ f(|z|) z / |z|`. Then the pull-back of the standard form `ω₀` of `(ι → ℂ) ∖ 0`
along this map is a Kähler form for the complex structure of `(ι → ℂ) ∖ 0`. -/
theorem isKahler_mpullback_radialMap_of_profile {f : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f (Ioi 0))
    (hf₀ : ∀ r ∈ Ioi (0 : ℝ), 0 < f r) (hf₁ : ∀ r ∈ Ioi (0 : ℝ), 0 < deriv f r)
    (hs : ContDiffOn ℝ ∞ h (Ioi 0)) (hh : ∀ s ∈ Ioi (0 : ℝ), 0 < h s)
    (hfh : ∀ s ∈ Ioi (0 : ℝ), h s = f √s ^ 2) :
    SmoothTwoForm.IsKahler
      (SmoothForm.mpullback (radialMap h hh) (contMDiff_radialMap hs hh)
        (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal
          (stdComplexPiSymplecticForm ι).constSmooth))
      (ofComplexManifold (ι → ℂ) (puncturedSpace (ι → ℂ))) := by
  refine isKahler_mpullback_radialMap hs hh fun s hs ↦ ?_
  -- `h'(s) = 2 f(√s) f'(√s) / (2 √s)`.
  have hr : 0 < √s := Real.sqrt_pos.2 hs
  have hfd : HasDerivAt f (deriv f √s) √s :=
    ((hf.contDiffAt (Ioi_mem_nhds hr)).differentiableAt (by simp)).hasDerivAt
  have hD : HasDerivAt (fun x ↦ f √x ^ 2) _ s :=
    (hfd.comp s (Real.hasDerivAt_sqrt (ne_of_gt hs))).fun_pow 2
  rw [(Filter.eventuallyEq_of_mem (Ioi_mem_nhds hs) hfh).deriv_eq, hD.deriv]
  have := hf₀ _ hr
  have := hf₁ _ hr
  simp only [Nat.cast_ofNat, Function.comp_apply, Nat.add_one_sub_one, pow_one]
  positivity

end SymplecticGeometry

end
