/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.UnitaryGroup
public import SymplecticGeometry.Geometry.Manifold.Projectivization.FubiniStudy.Basic
public import TauCeti.Geometry.Manifold.Projectivization.Map
public import TauCeti.Geometry.Symplectic.Manifold.Kahler
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import TauCeti.Analysis.Calculus.ContDiff.FinInsertNth

/-!
# The Fubini–Study form is Kähler

This file proves the symmetries and the Kähler property of the Fubini–Study form
`SymplecticGeometry.fubiniStudyForm n` of `ℂPⁿ = ℙ ℂ (Fin (n + 1) → ℂ)`, and gives its Kähler
potentials in the affine charts. Each statement is proved on `ℂⁿ⁺¹ ∖ 0`, on the form
`ρ = fubiniStudyLift n` to which the Fubini–Study form pulls back along the projection
`Projectivization.mkNonzero ℂ n`, a surjective submersion. Write `J` for the complex structure
`TauCeti.SmoothAlmostComplexStructure.ofComplexManifold` of a complex manifold.

* `SymplecticGeometry.mpullback_map_fubiniStudyForm`: a matrix `A` with orthonormal columns,
  `Aᴴ * A = 1`, induces a map `ℂPᵐ → ℂPⁿ`, and the pull-back of the Fubini–Study form of `ℂPⁿ`
  along it is the Fubini–Study form of `ℂPᵐ`. Multiplication by `A` preserves the Hermitian
  product `star z ⬝ᵥ v` (`Matrix.star_mulVec_dotProduct_mulVec`), whose real and imaginary parts
  give `|z|²`, `⟨z, v⟩` and `ω₀(z, v)` (`TauCeti.stdComplexPiSymplecticForm_apply_eq_im`), so it
  preserves `ρ`; pull-back along `mkNonzero` is injective.
* `SymplecticGeometry.mpullback_unitary_fubiniStudyForm`: the case of the unitary group, acting by
  Tau Ceti's `Projectivization.mapDiffeomorph`.
* `SymplecticGeometry.compatible_fubiniStudyForm`: the Fubini–Study form is compatible with `J`.
  The projection is holomorphic, so its derivative carries multiplication by `i` to `J`, and `ρ`
  is invariant under multiplication by `i`. A tangent vector of `ℂPⁿ` at `[z]` is the image of a
  vector `u` with `star z ⬝ᵥ u = 0`, and on such a vector `ρ_z(u, i u) = |u|² / |z|² > 0`.
* `SymplecticGeometry.isKahler_fubiniStudyForm`: the Fubini–Study form is Kähler for `J`.
* `SymplecticGeometry.mpullback_affineChart_symm_fubiniStudyForm` and
  `SymplecticGeometry.mpullback_affineChart_symm_fubiniStudyForm_eq_del_delBar`: along the inverse
  `w ↦ [Fin.insertNth j 1 w]` of each affine chart, the Fubini–Study form is
  `(1/4) d (J* d f) = (i/2) ∂∂bar f` for the potential `f(w) = log (1 + ∑ₖ ‖wₖ‖²)`
  (`SymplecticGeometry.fubiniStudyAffinePotential`). The inverse chart is the projection after the
  holomorphic section `w ↦ Fin.insertNth j 1 w`, along which `log |z|²` pulls back to `f`; the
  potential identity on `ℂⁿ⁺¹ ∖ 0` (`fubiniStudyPrimitive_eq`) pulls back by naturality of `d`
  and of `J*` (`TauCeti.SmoothAlmostComplexStructure.mpullback_covectorComplexStructure`).

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  Example 4.3.3, p. 168, and Exercises 4.3.4–4.3.5, p. 169.
* [P. Griffiths, J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978], Chapter 0,
  §2.
* Daniel Huybrechts, *Complex Geometry: An Introduction*, Section 3.1.
-/

public section

open Function Matrix TauCeti Projectivization
open scoped Manifold ContDiff LinearAlgebra.Projectivization ComplexOrder

namespace Matrix

variable {l m R : Type*} [Fintype l] [Fintype m]

/-- A matrix with a left inverse acts injectively on vectors: `Matrix.toLin' A` is injective. -/
theorem injective_toLin'_of_mul_eq_one [CommSemiring R] [DecidableEq m] {A : Matrix l m R}
    {B : Matrix m l R} (h : B * A = 1) : Injective (toLin' A) := fun z w hzw ↦ by
  simpa [mulVec_mulVec, h] using congrArg (B *ᵥ ·) hzw

/-- A matrix with orthonormal columns, `Aᴴ * A = 1`, preserves the Hermitian product
`star z ⬝ᵥ v`. -/
theorem star_mulVec_dotProduct_mulVec [CommRing R] [StarRing R] [DecidableEq m]
    {A : Matrix l m R} (hA : Aᴴ * A = 1) (z v : m → R) :
    star (A *ᵥ z) ⬝ᵥ (A *ᵥ v) = star z ⬝ᵥ v := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, hA, one_mulVec]

/-- The real part of the Hermitian square of a complex vector is its squared Euclidean norm:
`Re (star z ⬝ᵥ z) = ∑ᵢ ‖zᵢ‖²`. -/
theorem re_star_dotProduct_self {ι : Type*} [Fintype ι] (z : ι → ℂ) :
    (star z ⬝ᵥ z).re = ∑ i, ‖z i‖ ^ 2 := by
  simp only [dotProduct, Complex.re_sum, Pi.star_apply, Complex.star_def, Complex.conj_mul',
    ← Complex.ofReal_pow, Complex.ofReal_re]

end Matrix

namespace TauCeti

/-- The standard symplectic form of `ι → ℂ` is the imaginary part of the Hermitian product:
`ω₀(z, w) = Im (star z ⬝ᵥ w)`. -/
theorem stdComplexPiSymplecticForm_apply_eq_im {ι : Type*} [Fintype ι] (z w : ι → ℂ) :
    stdComplexPiSymplecticForm ι z w = (star z ⬝ᵥ w).im := by
  simp only [stdComplexPiSymplecticForm_apply, stdComplexSymplecticForm_apply, dotProduct,
    Complex.im_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [Pi.star_apply, Complex.star_def, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

end TauCeti

namespace Projectivization

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜] {m n : ℕ}

/-- The map of projective spaces induced by an injective linear map is `C^r` for the underlying
real manifold structures. -/
theorem contMDiff_map_restrictScalars (f : (Fin (m + 1) → 𝕜) →ₗ[𝕜] Fin (n + 1) → 𝕜)
    (hf : Injective f) (r : ℕ∞ω) :
    ContMDiff 𝓘(ℝ, Fin m → 𝕜) 𝓘(ℝ, Fin n → 𝕜) r (map f hf) := by
  simpa using (contMDiff_map f hf r).restrictScalars ℝ

/-- The inverse of an affine chart is `C^r` for the underlying real manifold structures. -/
theorem contMDiff_affineChart_symm_restrictScalars (j : Fin (n + 1)) (r : ℕ∞ω) :
    ContMDiff 𝓘(ℝ, Fin n → 𝕜) 𝓘(ℝ, Fin n → 𝕜) r (affineChart (K := 𝕜) j).symm := by
  simpa using (contMDiff_affineChart_symm (𝕜 := 𝕜) j r).restrictScalars ℝ

end Projectivization

namespace SymplecticGeometry

variable {m n : ℕ}

/-! ### Invariance under matrices with orthonormal columns -/

section Unitary

variable (A : Matrix (Fin (n + 1)) (Fin (m + 1)) ℂ) (hA : Aᴴ * A = 1)

/-- Multiplication by `A`, from `ℂᵐ⁺¹ ∖ 0` to `ℂⁿ⁺¹ ∖ 0`. -/
private noncomputable def puncturedMulVec (z : puncturedSpace (Fin (m + 1) → ℂ)) :
    puncturedSpace (Fin (n + 1) → ℂ) :=
  ⟨A *ᵥ (z : Fin (m + 1) → ℂ), mem_puncturedSpace.2 fun h ↦ mem_puncturedSpace.1 z.property
    (injective_toLin'_of_mul_eq_one hA (by rw [toLin'_apply, h, map_zero]))⟩

private theorem coe_puncturedMulVec (z : puncturedSpace (Fin (m + 1) → ℂ)) :
    (puncturedMulVec A hA z : Fin (n + 1) → ℂ) = A *ᵥ (z : Fin (m + 1) → ℂ) :=
  rfl

private theorem contMDiff_puncturedMulVec (r : ℕ∞ω) :
    ContMDiff 𝓘(ℝ, Fin (m + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) r (puncturedMulVec A hA) :=
  (TauCeti.ContMDiff.subtypeVal_comp_iff _ _).1
    (((toLin' A).restrictScalars ℝ).toContinuousLinearMap.contDiff.contMDiff.comp
      contMDiff_subtypeVal)

private theorem mfderiv_puncturedMulVec (z : puncturedSpace (Fin (m + 1) → ℂ))
    (v : TangentSpace 𝓘(ℝ, Fin (m + 1) → ℂ) z) :
    mfderiv 𝓘(ℝ, Fin (m + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) (puncturedMulVec A hA) z v =
      A *ᵥ (v : Fin (m + 1) → ℂ) := by
  have h₁ := TauCeti.Manifold.mfderiv_subtype_val_comp_apply (I := 𝓘(ℝ, Fin (n + 1) → ℂ))
    (J := 𝓘(ℝ, Fin (m + 1) → ℂ)) (f := puncturedMulVec A hA) (x := z) v
  have h₂ := TauCeti.Manifold.mfderiv_comp_subtype_val_apply (I := 𝓘(ℝ, Fin (n + 1) → ℂ))
    (J := 𝓘(ℝ, Fin (m + 1) → ℂ))
    (f := ((toLin' A).restrictScalars ℝ).toContinuousLinearMap) (x := z) v
  rw [mfderiv_eq_fderiv, ContinuousLinearMap.fderiv] at h₂
  exact h₁.symm.trans h₂

private theorem mkNonzero_comp_puncturedMulVec :
    mkNonzero ℂ n ∘ puncturedMulVec A hA =
      map (toLin' A) (injective_toLin'_of_mul_eq_one hA) ∘ mkNonzero ℂ m := by
  funext z
  simp [puncturedMulVec, map_mk]

/-- The Fubini–Study form is invariant under matrices with orthonormal columns: for
`A : Matrix (Fin (n + 1)) (Fin (m + 1)) ℂ` with `Aᴴ * A = 1`, the pull-back of the Fubini–Study
form of `ℂPⁿ` along the induced map `ℂPᵐ → ℂPⁿ`, `[z] ↦ [A z]`, is the Fubini–Study form of
`ℂPᵐ`. -/
theorem mpullback_map_fubiniStudyForm :
    SmoothForm.mpullback (map (toLin' A) (injective_toLin'_of_mul_eq_one hA))
      (contMDiff_map_restrictScalars _ _ ∞) (fubiniStudyForm n) = fubiniStudyForm m := by
  refine SmoothForm.mpullback_injective_of_surjective (contMDiff_mkNonzero ℂ m ∞)
    (surjective_mkNonzero ℂ m) ((isSubmersion_mkNonzero ℂ m).surjective_mfderiv (by simp)) ?_
  rw [SmoothForm.mpullback_mpullback_of_comp_eq _ _ (contMDiff_puncturedMulVec A hA ∞)
      (contMDiff_mkNonzero ℂ n ∞) (mkNonzero_comp_puncturedMulVec A hA).symm,
    mpullback_mkNonzero_fubiniStudyForm, mpullback_mkNonzero_fubiniStudyForm]
  refine SmoothBundleForm.ext_eval₂ fun z v w ↦ ?_
  rw [SmoothForm.eval₂_mpullback, mfderiv_puncturedMulVec, mfderiv_puncturedMulVec,
    fubiniStudyLift_apply z, fubiniStudyLift_apply (puncturedMulVec A hA z)
      (A *ᵥ (v : Fin (m + 1) → ℂ)) (A *ᵥ (w : Fin (m + 1) → ℂ))]
  -- Read `v` and `w` as vectors of `Fin (m + 1) → ℂ`, so that the lemmas on vectors apply.
  revert v w
  intro (v : Fin (m + 1) → ℂ) (w : Fin (m + 1) → ℂ)
  simp only [stdComplexPiSymplecticForm_apply_eq_im, coe_puncturedMulVec, ← re_star_dotProduct_self,
    star_mulVec_dotProduct_mulVec hA]

/-- The Fubini–Study form is invariant under the unitary group `U(n + 1)`, acting on `ℂPⁿ` by the
diffeomorphisms `Projectivization.mapDiffeomorph`, read on the underlying real manifold. -/
theorem mpullback_unitary_fubiniStudyForm (U : unitaryGroup (Fin (n + 1)) ℂ) :
    SmoothForm.mpullback (mapDiffeomorph (UnitaryGroup.toLinearEquiv U) ∞)
      (by rw [coe_mapDiffeomorph]; exact contMDiff_map_restrictScalars _ _ ∞)
      (fubiniStudyForm n) = fubiniStudyForm n := by
  have hU : (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)ᴴ * U = 1 := by
    rw [← star_eq_conjTranspose]
    exact UnitaryGroup.star_mul_self U
  have h : ⇑(mapDiffeomorph (UnitaryGroup.toLinearEquiv U) ∞) =
      map (toLin' (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))
        (injective_toLin'_of_mul_eq_one hU) := by
    funext x
    induction x using ind with
    | h v hv => simp [map_mk, UnitaryGroup.toLinearEquiv]
  simp only [h]
  exact mpullback_map_fubiniStudyForm _ hU

end Unitary

/-! ### Compatibility and the Kähler property -/

section Kahler

open SmoothAlmostComplexStructure

variable (n) in
/-- The projection `ℂⁿ⁺¹ ∖ 0 → ℂPⁿ` is holomorphic, so its real derivative intertwines
multiplication by `i` with the complex structure of `ℂPⁿ`. -/
private theorem mfderiv_mkNonzero_I_smul (z : puncturedSpace (Fin (n + 1) → ℂ))
    (v : Fin (n + 1) → ℂ) :
    mfderiv 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin n → ℂ) (mkNonzero ℂ n) z (Complex.I • v) =
      ofComplexManifold (Fin n → ℂ) (ℙ ℂ (Fin (n + 1) → ℂ)) (mkNonzero ℂ n z)
        (mfderiv 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin n → ℂ) (mkNonzero ℂ n) z v) := by
  have h : IsPseudoholomorphicAt (ofComplexManifold (Fin (n + 1) → ℂ) (puncturedSpace _))
      (ofComplexManifold (Fin n → ℂ) (ℙ ℂ (Fin (n + 1) → ℂ))) (mkNonzero ℂ n) z :=
    isPseudoholomorphicAt_ofComplexManifold_iff.2
      ((contMDiff_mkNonzero_self 1 z).mdifferentiableAt one_ne_zero)
  have h' := h.mfderiv_apply_commute v
  rwa [ofComplexManifold_apply] at h'

/-- The two-form `ρ` on `ℂⁿ⁺¹ ∖ 0` is invariant under multiplication by `i`. -/
private theorem fubiniStudyLift_I_smul (z : puncturedSpace (Fin (n + 1) → ℂ))
    (v w : Fin (n + 1) → ℂ) :
    (fubiniStudyLift n).eval₂ z (Complex.I • v) (Complex.I • w) =
      (fubiniStudyLift n).eval₂ z v w := by
  rw [fubiniStudyLift_apply z (Complex.I • v) (Complex.I • w), fubiniStudyLift_apply z v w]
  simp only [stdComplexPiSymplecticForm_apply_eq_im, star_smul, smul_dotProduct, dotProduct_smul,
    smul_eq_mul, Complex.star_def, Complex.conj_I, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.neg_re, Complex.neg_im]
  ring

/-- On a vector `u ≠ 0` Hermitian-orthogonal to `z`, `ρ_z(u, i u)` is positive: it is
`|u|² / |z|²`. -/
private theorem fubiniStudyLift_I_smul_pos (z : puncturedSpace (Fin (n + 1) → ℂ))
    {u : Fin (n + 1) → ℂ} (hzu : star (z : Fin (n + 1) → ℂ) ⬝ᵥ u = 0) (hu : u ≠ 0) :
    0 < (fubiniStudyLift n).eval₂ z u (Complex.I • u) := by
  have hz := mem_puncturedSpace.1 z.property
  rw [fubiniStudyLift_apply z u (Complex.I • u)]
  simp only [stdComplexPiSymplecticForm_apply_eq_im, dotProduct_smul, smul_eq_mul, hzu, mul_zero,
    Complex.zero_re, Complex.zero_im, zero_mul, sub_zero, zero_div, Complex.mul_im, Complex.I_re,
    Complex.I_im, one_mul]
  have hpos (x : Fin (n + 1) → ℂ) (hx : x ≠ 0) : 0 < ∑ i, ‖x i‖ ^ 2 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
    exact Finset.sum_pos' (fun _ _ ↦ by positivity)
      ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.2 hi) 2⟩
  rw [zero_add, re_star_dotProduct_self]
  exact div_pos (hpos u hu) (hpos _ hz)

/-- The Fubini–Study form is compatible with the complex structure `J` of `ℂPⁿ`: it is
`J`-invariant, and `ω_FS(v, J v) > 0` for every nonzero tangent vector `v`. -/
theorem compatible_fubiniStudyForm :
    (fubiniStudyForm n).Compatible (ofComplexManifold (Fin n → ℂ) (ℙ ℂ (Fin (n + 1) → ℂ))) := by
  have hD := (isSubmersion_mkNonzero ℂ n).surjective_mfderiv (by simp)
  refine ⟨SmoothTwoForm.invariant_iff.2 fun x v w ↦ ?_, SmoothTwoForm.tames_iff.2 fun x t ht ↦ ?_⟩
  · obtain ⟨z, rfl⟩ := surjective_mkNonzero ℂ n x
    obtain ⟨(v : Fin (n + 1) → ℂ), rfl⟩ := hD z v
    obtain ⟨(w : Fin (n + 1) → ℂ), rfl⟩ := hD z w
    rw [← mfderiv_mkNonzero_I_smul n z v, ← mfderiv_mkNonzero_I_smul n z w]
    -- The vectors are read in `Fin (n + 1) → ℂ`, so the evaluation lemmas are applied by `exact`.
    exact (eval₂_fubiniStudyForm_mfderiv_mkNonzero z _ _).trans
      ((fubiniStudyLift_I_smul z v w).trans (eval₂_fubiniStudyForm_mfderiv_mkNonzero z _ _).symm)
  · obtain ⟨z, rfl⟩ := surjective_mkNonzero ℂ n x
    obtain ⟨(v : Fin (n + 1) → ℂ), rfl⟩ := hD z t
    -- Replace `v` by its component `u` Hermitian-orthogonal to `z`, which has the same image.
    have hz : star (z : Fin (n + 1) → ℂ) ⬝ᵥ (z : Fin (n + 1) → ℂ) ≠ 0 :=
      dotProduct_star_self_eq_zero.not.2 (mem_puncturedSpace.1 z.property)
    set c : ℂ := (star (z : Fin (n + 1) → ℂ) ⬝ᵥ v) / (star (z : Fin (n + 1) → ℂ) ⬝ᵥ z)
    set u : Fin (n + 1) → ℂ := v - c • (z : Fin (n + 1) → ℂ)
    have hu : mfderiv 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin n → ℂ) (mkNonzero ℂ n) z u =
        mfderiv 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin n → ℂ) (mkNonzero ℂ n) z v :=
      (map_sub _ _ _).trans <| (congrArg (_ - ·) (mfderiv_mkNonzero_smul_self z c)).trans
        (sub_zero _)
    rw [← hu, ← mfderiv_mkNonzero_I_smul n z u]
    refine lt_of_lt_of_eq (fubiniStudyLift_I_smul_pos z ?_ fun h ↦ ht ?_)
      (eval₂_fubiniStudyForm_mfderiv_mkNonzero z _ _).symm
    · rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, div_mul_cancel₀ _ hz, sub_self]
    · exact hu.symm.trans ((congrArg _ h).trans (map_zero _))

/-- The Fubini–Study form is Kähler for the complex structure of `ℂPⁿ`: it is closed, compatible
with the complex structure, and the complex structure is integrable. -/
theorem isKahler_fubiniStudyForm :
    (fubiniStudyForm n).IsKahler (ofComplexManifold (Fin n → ℂ) (ℙ ℂ (Fin (n + 1) → ℂ))) :=
  SmoothTwoForm.isKahler_ofComplexManifold_iff.2
    ⟨(isSymplectic_fubiniStudyForm n).isClosed, compatible_fubiniStudyForm⟩

end Kahler

/-! ### Local potentials -/

section Potential

open SmoothAlmostComplexStructure

variable (n) in
/-- The function `w ↦ log (1 + ∑ₖ ‖wₖ‖²)` on `ℂⁿ`, as a smooth `0`-form
(`fubiniStudyAffinePotential_apply`). In every affine chart of `ℂPⁿ` it is a Kähler potential of
the Fubini–Study form (`mpullback_affineChart_symm_fubiniStudyForm`); in homogeneous coordinates
it is `log (|z|² / |z_j|²)`. -/
noncomputable def fubiniStudyAffinePotential :
    SmoothForm 𝓘(ℝ, Fin n → ℂ) (Fin n → ℂ) ℝ 0 :=
  SmoothForm.ofFunction ⟨fun w ↦ Real.log (1 + ‖complexToRealEuclidean (Fin n) w‖ ^ 2), by
    intro w
    have h : ContDiffAt ℝ ∞ (fun w ↦ Real.log (1 + ‖complexToRealEuclidean (Fin n) w‖ ^ 2)) w :=
      (contDiff_const.add ((contDiff_norm_sq ℝ).comp
        (complexToRealEuclidean (Fin n)).contDiff)).contDiffAt.log
        (add_pos_of_pos_of_nonneg one_pos (sq_nonneg _)).ne'
    exact h.contMDiffAt⟩

variable (n) in
/-- As a rough form, the affine potential is the `0`-form of `w ↦ log (1 + ‖ŵ‖²)`. -/
theorem fubiniStudyAffinePotential_def :
    (fubiniStudyAffinePotential n : RoughForm 𝓘(ℝ, Fin n → ℂ) _ ℝ 0) =
      RoughForm.ofFunction 𝓘(ℝ, Fin n → ℂ)
        fun w : Fin n → ℂ ↦ Real.log (1 + ‖complexToRealEuclidean (Fin n) w‖ ^ 2) :=
  SmoothForm.coe_ofFunction _

/-- The affine potential takes the value `log (1 + ∑ₖ ‖wₖ‖²)` at `w`. -/
@[simp]
theorem fubiniStudyAffinePotential_apply (w : Fin n → ℂ)
    (v : Fin 0 → TangentSpace 𝓘(ℝ, Fin n → ℂ) w) :
    (fubiniStudyAffinePotential n).val w v = Real.log (1 + ∑ k, ‖w k‖ ^ 2) := by
  rw [fubiniStudyAffinePotential_def, RoughForm.ofFunction_apply, norm_sq_complexToRealEuclidean]

/-- The section `w ↦ Fin.insertNth j 1 w` of the projection over the affine chart of `j`. -/
private noncomputable def affineLift (j : Fin (n + 1)) (w : Fin n → ℂ) :
    puncturedSpace (Fin (n + 1) → ℂ) :=
  ⟨Fin.insertNth (α := fun _ ↦ ℂ) j 1 w, mem_puncturedSpace.2 (Fin.insertNth_one_ne_zero j w)⟩

private theorem contMDiff_affineLift_self (j : Fin (n + 1)) :
    ContMDiff 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) ∞ (affineLift j) :=
  (TauCeti.ContMDiff.subtypeVal_comp_iff _ _).1
    (ContDiff.finInsertNth (F := fun _ ↦ ℂ) j contDiff_const contDiff_id).contMDiff

private theorem contMDiff_affineLift (j : Fin (n + 1)) :
    ContMDiff 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ (affineLift j) := by
  simpa using (contMDiff_affineLift_self j).restrictScalars ℝ

private theorem mkNonzero_comp_affineLift (j : Fin (n + 1)) :
    mkNonzero ℂ n ∘ affineLift j = (affineChart (K := ℂ) j).symm :=
  funext fun w ↦ by rw [Function.comp_apply, mkNonzero_apply, affineChart_symm_apply]; rfl

private theorem mpullback_affineLift_fubiniStudyPotential (j : Fin (n + 1)) :
    SmoothForm.mpullback (affineLift j) (contMDiff_affineLift j) (fubiniStudyPotential n) =
      fubiniStudyAffinePotential n := by
  refine Subtype.ext <| funext fun w ↦ ContinuousAlternatingMap.ext fun v ↦ ?_
  rw [SmoothForm.mpullback_apply, fubiniStudyPotential_apply, fubiniStudyAffinePotential_apply]
  simp [affineLift, Fin.sum_univ_succAbove _ j]

/-- **Local potentials of the Fubini–Study form.** Along the inverse `w ↦ [Fin.insertNth j 1 w]`
of the affine chart of `j`, the Fubini–Study form pulls back to `(1/4) d (J* d f)`, where
`f = fubiniStudyAffinePotential n` is `w ↦ log (1 + ∑ₖ ‖wₖ‖²)` and `J*` is the structure
`a ↦ -a ∘ J` on one-forms of the complex structure `J` of `ℂⁿ`. -/
theorem mpullback_affineChart_symm_fubiniStudyForm (j : Fin (n + 1)) :
    SmoothForm.mpullback (affineChart (K := ℂ) j).symm
        (contMDiff_affineChart_symm_restrictScalars j ∞) (fubiniStudyForm n) =
      (4 : ℝ)⁻¹ • mextDerivₗ 𝓘(ℝ, Fin n → ℂ) 1
        ((ofComplexManifold (Fin n → ℂ) (Fin n → ℂ)).covectorComplexStructure
          (mextDerivₗ 𝓘(ℝ, Fin n → ℂ) 0 (fubiniStudyAffinePotential n))) := by
  have hJ : IsPseudoholomorphic (ofComplexManifold (Fin n → ℂ) (Fin n → ℂ))
      (ofComplexManifold (Fin (n + 1) → ℂ) (puncturedSpace (Fin (n + 1) → ℂ))) (affineLift j) :=
    isPseudoholomorphic_ofComplexManifold_iff.2
      ((contMDiff_affineLift_self j).mdifferentiable (by simp))
  have h : SmoothForm.mpullback (affineChart (K := ℂ) j).symm
      (contMDiff_affineChart_symm_restrictScalars j ∞) (fubiniStudyForm n) =
        SmoothForm.mpullback (affineLift j) (contMDiff_affineLift j)
          (SmoothForm.mpullback (mkNonzero ℂ n) (contMDiff_mkNonzero ℂ n ∞)
            (fubiniStudyForm n)) := by
    rw [SmoothForm.mpullback_mpullback]
    simp only [mkNonzero_comp_affineLift]
  rw [h, mpullback_mkNonzero_fubiniStudyForm, fubiniStudyLift_def,
    ← SmoothForm.mextDerivₗ_mpullback, fubiniStudyPrimitive_eq, SmoothForm.mpullback_smul,
    mpullback_covectorComplexStructure _ hJ, ← SmoothForm.mextDerivₗ_mpullback,
    mpullback_affineLift_fubiniStudyPotential, map_smul]

/-- The local potentials in Dolbeault form: along the inverse of the affine chart of `j`, the
complexified Fubini–Study form is `(i/2) ∂∂bar f` for `f = fubiniStudyAffinePotential n`, the
function `w ↦ log (1 + ∑ₖ ‖wₖ‖²)`, with the Dolbeault operators of `ℂⁿ`. -/
theorem mpullback_affineChart_symm_fubiniStudyForm_eq_del_delBar (j : Fin (n + 1)) :
    SmoothForm.mapCoeff Complex.ofRealCLM (SmoothForm.mpullback (affineChart (K := ℂ) j).symm
        (contMDiff_affineChart_symm_restrictScalars j ∞) (fubiniStudyForm n)) =
      (Complex.I / 2) • (ofComplexManifold (Fin n → ℂ) (Fin n → ℂ)).del
        ((ofComplexManifold (Fin n → ℂ) (Fin n → ℂ)).delBar
          (SmoothForm.mapCoeff Complex.ofRealCLM (fubiniStudyAffinePotential n))) := by
  rw [del_delBar_mapCoeff_ofReal_ofComplexManifold, mpullback_affineChart_symm_fubiniStudyForm]

end Potential

end SymplecticGeometry

end
