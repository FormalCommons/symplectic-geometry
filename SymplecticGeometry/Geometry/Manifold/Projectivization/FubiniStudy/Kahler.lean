/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.UnitaryGroup
public import SymplecticGeometry.Data.Matrix.Mul
public import SymplecticGeometry.Geometry.Manifold.Projectivization.FubiniStudy.Basic
public import SymplecticGeometry.LinearAlgebra.Matrix.DotProduct
public import TauCeti.Geometry.Manifold.Projectivization.Map
public import TauCeti.Geometry.Symplectic.Manifold.Kahler
public import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.Submanifold
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
  The projection is pseudoholomorphic (`Projectivization.isPseudoholomorphic_mkNonzero`), so its
  derivative carries multiplication by `i` to `J` (`Projectivization.mfderiv_mkNonzero_I_smul`),
  and `ρ` is invariant under multiplication by `i`. A tangent vector of `ℂPⁿ` at `[z]` is the
  image of a vector `u` with `star z ⬝ᵥ u = 0`, and on such a vector
  `ρ_z(u, i u) = |u|² / |z|² > 0`.
* `SymplecticGeometry.isKahler_fubiniStudyForm`: the Fubini–Study form is Kähler for `J`.
* `SymplecticGeometry.isKahler_mpullback_fubiniStudyForm`: on a smooth embedding `f : N → ℂPⁿ`
  with `J`-invariant tangent images, the pull-back of the Fubini–Study form is symplectic and
  Kähler for the restricted structure `J|_N`, which is integrable when `N` has no boundary. This
  is the case `M = ℂPⁿ` of the results of
  `SymplecticGeometry/Geometry/Symplectic/Manifold/AlmostComplex/Submanifold.lean`
  (`TauCeti.SmoothTwoForm.Tames.isSymplectic_mpullback`, `TauCeti.SmoothTwoForm.IsKahler.restrict`
  and `TauCeti.SmoothAlmostComplexStructure.IsIntegrable.restrict`).
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

namespace Projectivization

variable {n : ℕ}

open SmoothAlmostComplexStructure

variable (n) in
/-- The projection `ℂⁿ⁺¹ ∖ 0 → ℂPⁿ` is pseudoholomorphic for the complex structures of the two
complex manifolds. -/
theorem isPseudoholomorphic_mkNonzero :
    IsPseudoholomorphic (ofComplexManifold (Fin (n + 1) → ℂ) (puncturedSpace (Fin (n + 1) → ℂ)))
      (ofComplexManifold (Fin n → ℂ) (ℙ ℂ (Fin (n + 1) → ℂ))) (mkNonzero ℂ n) :=
  isPseudoholomorphic_ofComplexManifold_iff.2
    ((contMDiff_mkNonzero_self 1).mdifferentiable one_ne_zero)

/-- The real derivative of the projection `ℂⁿ⁺¹ ∖ 0 → ℂPⁿ` carries multiplication by `i` to the
complex structure of `ℂPⁿ`. -/
theorem mfderiv_mkNonzero_I_smul (z : puncturedSpace (Fin (n + 1) → ℂ))
    (v : Fin (n + 1) → ℂ) :
    mfderiv 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin n → ℂ) (mkNonzero ℂ n) z (Complex.I • v) =
      ofComplexManifold (Fin n → ℂ) (ℙ ℂ (Fin (n + 1) → ℂ)) (mkNonzero ℂ n z)
        (mfderiv 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin n → ℂ) (mkNonzero ℂ n) z v) := by
  have h := ((isPseudoholomorphic_mkNonzero n).isPseudoholomorphicAt z).mfderiv_apply_commute v
  rwa [ofComplexManifold_apply] at h

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
    (mulVec_injective_of_mul_eq_one hA (by rw [h, mulVec_zero]))⟩

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
      map (toLin' A)
          (by rw [toLin'_apply', coe_mulVecLin]; exact mulVec_injective_of_mul_eq_one hA) ∘
        mkNonzero ℂ m := by
  funext z
  simp [puncturedMulVec, map_mk]

/-- The Fubini–Study form is invariant under matrices with orthonormal columns: for
`A : Matrix (Fin (n + 1)) (Fin (m + 1)) ℂ` with `Aᴴ * A = 1`, the pull-back of the Fubini–Study
form of `ℂPⁿ` along the induced map `ℂPᵐ → ℂPⁿ`, `[z] ↦ [A z]`, is the Fubini–Study form of
`ℂPᵐ`. -/
theorem mpullback_map_fubiniStudyForm :
    SmoothForm.mpullback
        (map (toLin' A)
          (by rw [toLin'_apply', coe_mulVecLin]; exact mulVec_injective_of_mul_eq_one hA))
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
        (by rw [toLin'_apply', coe_mulVecLin]; exact mulVec_injective_of_mul_eq_one hU) := by
    funext x
    induction x using ind with
    | h v hv => simp [map_mk, UnitaryGroup.toLinearEquiv]
  simp only [h]
  exact mpullback_map_fubiniStudyForm _ hU

end Unitary

/-! ### Compatibility and the Kähler property -/

section Kahler

open SmoothAlmostComplexStructure

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
  rw [zero_add, re_star_dotProduct_self, ← norm_sq_complexToRealEuclidean,
    ← norm_sq_complexToRealEuclidean]
  exact div_pos (pow_pos (norm_pos_iff.2 (by simpa)) 2) (pow_pos (norm_pos_iff.2 (by simpa)) 2)

/-- The Fubini–Study form is compatible with the complex structure `J` of `ℂPⁿ`: it is
`J`-invariant, and `ω_FS(v, J v) > 0` for every nonzero tangent vector `v`. -/
theorem compatible_fubiniStudyForm :
    (fubiniStudyForm n).Compatible (ofComplexManifold (Fin n → ℂ) (ℙ ℂ (Fin (n + 1) → ℂ))) := by
  have hD := (isSubmersion_mkNonzero ℂ n).surjective_mfderiv (by simp)
  refine ⟨SmoothTwoForm.invariant_iff.2 fun x v w ↦ ?_, SmoothTwoForm.tames_iff.2 fun x t ht ↦ ?_⟩
  · obtain ⟨z, rfl⟩ := surjective_mkNonzero ℂ n x
    obtain ⟨(v : Fin (n + 1) → ℂ), rfl⟩ := hD z v
    obtain ⟨(w : Fin (n + 1) → ℂ), rfl⟩ := hD z w
    rw [← mfderiv_mkNonzero_I_smul z v, ← mfderiv_mkNonzero_I_smul z w]
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
    rw [← hu, ← mfderiv_mkNonzero_I_smul z u]
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

/-! ### Complex submanifolds -/

section Submanifold

variable {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold I' ∞ N] {hn : (∞ : ℕ∞ω) ≠ 0}

/-- **Complex submanifolds of `ℂPⁿ` are Kähler.** Let `f : N → ℂPⁿ` be a smooth embedding whose
tangent images are invariant under the complex structure `J` of `ℂPⁿ`, and let `J|_N` be the
restricted structure on `N`. Then the pull-back `f^* ω_FS` of the Fubini–Study form is a
symplectic form on `N`, the pair `(f^* ω_FS, J|_N)` is Kähler (closed, compatible, with vanishing
Nijenhuis tensor), and if `N` has no boundary, then `J|_N` is integrable.

Milestone: *Complex submanifolds of Kähler manifolds*. -/
theorem isKahler_mpullback_fubiniStudyForm
    {f : SmoothEmbedding I' 𝓘(ℝ, Fin n → ℂ) ∞ N (ℙ ℂ (Fin (n + 1) → ℂ))}
    (hJ : ∀ x, ∀ v ∈ f.tangentRange x hn,
      ofComplexManifold (Fin n → ℂ) (ℙ ℂ (Fin (n + 1) → ℂ)) (f x) v ∈ f.tangentRange x hn) :
    SmoothTwoForm.IsSymplectic (SmoothForm.mpullback f f.contMDiff (fubiniStudyForm n)) ∧
      SmoothTwoForm.IsKahler (SmoothForm.mpullback f f.contMDiff (fubiniStudyForm n))
        ((ofComplexManifold (Fin n → ℂ) (ℙ ℂ (Fin (n + 1) → ℂ))).restrict f hJ) ∧
      (BoundarylessManifold I' N →
        ((ofComplexManifold (Fin n → ℂ) (ℙ ℂ (Fin (n + 1) → ℂ))).restrict f hJ).IsIntegrable) :=
  ⟨compatible_fubiniStudyForm.tames.isSymplectic_mpullback hJ (isSymplectic_fubiniStudyForm n),
    isKahler_fubiniStudyForm.restrict hJ, fun _ ↦ isIntegrable_ofComplexManifold.restrict hJ⟩

end Submanifold

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
