/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Sum.FermatCubic
public import SymplecticGeometry.Geometry.Symplectic.Sum.RationalEllipticSurface
public import TauCeti.Geometry.Manifold.Orientation.TopForm
import SymplecticGeometry.LinearAlgebra.Alternating.Sign

/-!
# The form of `E(1)` on its fibre, read on the standard torus

Let `φ = SymplecticGeometry.fermatCubicTorusDiffeomorph p` be the diffeomorphism from the Fermat
cubic, the fibre of the rational elliptic surface `E(1)` over `[1 : 0]`, onto Tau Ceti's standard
torus `T = ∀ i : Unit ⊕ Unit, AddCircle (p i)`. Pulling the symplectic form of `E(1)` back along
`fibreEmbedding ∘ φ⁻¹` gives a two-form `σ` on `T`. This file shows that `σ` is positive on every
tangent basis of `T` that is positive for the orientation of `TauCeti.torusSymplecticForm p`. So
`σ` and the standard form satisfy the hypotheses on signs of Moser's theorem for area forms,
`TauCeti.SmoothTwoForm.exists_diffeomorph_mpullback_eq_of_integralTopForm_eq`.

The proof compares both forms with the complex structure of `ℂ`. Let `π` be the covering map
`SymplecticGeometry.latticeTorusCover p b` of `T` by `ℂ`, for the positively oriented basis
`b = fermatPeriodBasis` of the period lattice, and let `z ∈ ℂ` lie over a point `x` of `T`.

* `π` pulls the standard form back to `det A • ω₀`, with `det A > 0`
  (`SymplecticGeometry.mpullback_latticeTorusCover_torusSymplecticForm` and
  `SymplecticGeometry.det_latticeTorusEquiv_pos`), so the standard form is positive on the pair
  `(dπ 1, dπ i)`.
* `φ⁻¹ ∘ π` is the class map `ℂ → ℂ / Λ` followed by the uniformization and the inverse of
  `fermatCubicDiffeomorph`, so `H = fibreEmbedding ∘ φ⁻¹ ∘ π` is holomorphic and its real
  differential commutes with multiplication by `i`
  (`MDifferentiableAt.mfderiv_ofComplexManifold_apply`). Since `H` is an immersion, the form of
  `E(1)`, which tames the complex structure
  (`SymplecticGeometry.rationalEllipticSurface.tames_symplecticForm`), is positive on
  `(dH 1, dH i) = (dH 1, J dH 1)`; that is, `σ` is positive on `(dπ 1, dπ i)`.

Two alternating forms on the plane `T_x T` that are positive on one pair have the same sign on
every basis (`AlternatingMap.pos_apply_basis_of_pos`), which gives the claim.

## Main results

* `mpullback_fibreEmbedding_comp_fermatCubicTorusDiffeomorph_symm_apply_pos`:
  `σ` is positive on the positively oriented tangent bases of the standard torus.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §7.2 (the
  fibre of the rational elliptic surface as a torus).
-/

public section

open Complex TauCeti
open scoped Manifold ContDiff ComplexManifold

namespace SymplecticGeometry

namespace rationalEllipticSurface

variable (p : Unit ⊕ Unit → ℝ) [∀ i, Fact (0 < p i)]

/-- The standard form of the torus is positive on the images of `1` and `i` under the
differential of the covering map `latticeTorusCover p fermatPeriodBasis`. -/
private theorem eval₂_torusSymplecticForm_mfderiv_latticeTorusCover_pos (z : ℂ) :
    0 < SmoothBundleForm.eval₂ (torusSymplecticForm p) (latticeTorusCover p fermatPeriodBasis z)
      (mfderiv 𝓘(ℝ, ℂ) (ModelWithCorners.pi fun _ : Unit ⊕ Unit ↦ 𝓘(ℝ))
          (latticeTorusCover p fermatPeriodBasis) z (1 : ℂ))
      (mfderiv 𝓘(ℝ, ℂ) (ModelWithCorners.pi fun _ : Unit ⊕ Unit ↦ 𝓘(ℝ))
          (latticeTorusCover p fermatPeriodBasis) z I) := by
  have h := congr(SmoothBundleForm.eval₂
    $(mpullback_latticeTorusCover_torusSymplecticForm p fermatPeriodBasis) z (1 : ℂ) I)
  -- The tangent vectors `1` and `I` are elaborated in `ℂ`, not in `TangentSpace 𝓘(ℝ, ℂ) z`, so
  -- the evaluation lemmas only match up to that identification.
  erw [SmoothForm.eval₂_mpullback] at h
  have hc := SymplecticForm.constSmooth_apply stdComplexSymplecticForm z (1 : ℂ) I
  erw [SmoothBundleForm.eval₂_apply] at hc
  rw [h]
  erw [SmoothBundleForm.eval₂_apply]
  simp only [SetLike.val_smul, Pi.smul_apply, ContinuousAlternatingMap.coe_smul, hc,
    stdComplexSymplecticForm_apply, one_re, I_im, mul_one, one_im, I_re, mul_zero, sub_zero,
    smul_eq_mul]
  exact det_latticeTorusEquiv_pos p _ zero_lt_im_conj_mul_fermatPeriodBasis

/-- The pull-back of the form of `E(1)` along `fibreEmbedding ∘ φ⁻¹` is positive on the images
of `1` and `i` under the differential of the covering map `latticeTorusCover p fermatPeriodBasis`:
read on `ℂ`, the map to `E(1)` is holomorphic, and the form of `E(1)` tames its complex
structure. -/
private theorem eval₂_mpullback_fibreEmbedding_mfderiv_latticeTorusCover_pos (z : ℂ) :
    0 < SmoothBundleForm.eval₂
      (SmoothForm.mpullback (fibreEmbedding ∘ (fermatCubicTorusDiffeomorph p).symm)
        (fibreEmbedding.contMDiff.comp (fermatCubicTorusDiffeomorph p).symm.contMDiff)
        symplecticForm)
      (latticeTorusCover p fermatPeriodBasis z)
      (mfderiv 𝓘(ℝ, ℂ) (ModelWithCorners.pi fun _ : Unit ⊕ Unit ↦ 𝓘(ℝ))
          (latticeTorusCover p fermatPeriodBasis) z (1 : ℂ))
      (mfderiv 𝓘(ℝ, ℂ) (ModelWithCorners.pi fun _ : Unit ⊕ Unit ↦ 𝓘(ℝ))
          (latticeTorusCover p fermatPeriodBasis) z I) := by
  set φ := fermatCubicTorusDiffeomorph p
  have hπ := isLocalDiffeomorph_latticeTorusCover p fermatPeriodBasis
  -- Read on `ℂ`, the map to `E(1)` is a composite of holomorphic maps.
  have hH : (fibreEmbedding ∘ φ.symm) ∘ latticeTorusCover p fermatPeriodBasis =
      analyticFibreEmbedding ∘ fermatCubicDiffeomorph.symm ∘ fermatUniformization ∘
        ((↑) : ℂ → ℂ ⧸ fermatWeierstrassCurve.periodLattice.toAddSubgroup) := by
    funext z
    simp only [coe_fibreEmbedding, Function.comp_apply, fermatCubicTorusDiffeomorph_symm_apply,
      coe_fermatCubicDiffeomorph_symm_apply, coe_analyticFibreEmbedding, Subtype.mk.injEq,
      Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq, and_true, φ]
    rw [← latticeTorusDiffeomorph_mk, Diffeomorph.symm_apply_apply]
  have hhol : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ, Fin 2 → ℂ)
      ((fibreEmbedding ∘ φ.symm) ∘ latticeTorusCover p fermatPeriodBasis) z := by
    rw [hH]
    exact (analyticFibreEmbedding.contMDiff.mdifferentiableAt (by simp)).comp z
      ((fermatCubicDiffeomorph.symm.contMDiff.mdifferentiableAt (by simp)).comp z
        ((fermatUniformization.contMDiff.mdifferentiableAt (by simp)).comp z
          (AddSubgroup.hasMFDerivAt_quotientMk _ z).mdifferentiableAt))
  -- It is an immersion, so its differential does not vanish on `1`.
  have hne : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin 2 → ℂ)
      ((fibreEmbedding ∘ φ.symm) ∘ latticeTorusCover p fermatPeriodBasis) z (1 : ℂ) ≠ 0 := by
    rw [mfderiv_comp z ((fibreEmbedding.contMDiff.comp φ.symm.contMDiff).mdifferentiableAt
        (by simp)) (hπ.contMDiff.mdifferentiableAt (by simp)),
      mfderiv_comp _ (fibreEmbedding.contMDiff.mdifferentiableAt (by simp))
        (φ.symm.contMDiff.mdifferentiableAt (by simp))]
    refine (map_ne_zero_iff _ ?_).2 (one_ne_zero (α := ℂ))
    rw [ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_comp,
      ← φ.symm.isLocalDiffeomorph.mfderivToContinuousLinearEquiv_coe (by simp),
      ← hπ.mfderivToContinuousLinearEquiv_coe (by simp)]
    exact (fibreEmbedding.isImmersion.mfderiv_injective (by simp) _).comp
      ((ContinuousLinearEquiv.injective _).comp (ContinuousLinearEquiv.injective _))
  have h := SmoothForm.eval₂_mpullback (latticeTorusCover p fermatPeriodBasis) hπ.contMDiff
    (SmoothForm.mpullback (fibreEmbedding ∘ φ.symm)
      (fibreEmbedding.contMDiff.comp φ.symm.contMDiff) symplecticForm) z (1 : ℂ) I
  rw [← h, SmoothForm.mpullback_mpullback]
  -- As in `eval₂_torusSymplecticForm_mfderiv_latticeTorusCover_pos`, `1` and `I` are in `ℂ`.
  erw [SmoothForm.eval₂_mpullback]
  have hJ := hhol.mfderiv_ofComplexManifold_apply (1 : ℂ)
  rw [SmoothAlmostComplexStructure.ofComplexManifold_apply, smul_eq_mul, mul_one] at hJ
  rw [hJ]
  exact SmoothTwoForm.tames_iff.1 tames_symplecticForm _ _ hne

/-- **The form of `E(1)` on its fibre is positive for the orientation of the standard torus.**
Let `φ = fermatCubicTorusDiffeomorph p` identify the Fermat cubic, the fibre of the rational
elliptic surface over `[1 : 0]`, with the standard torus `∀ i : Unit ⊕ Unit, AddCircle (p i)`.
The pull-back of the symplectic form of the rational elliptic surface along
`fibreEmbedding ∘ φ⁻¹` is positive on every tangent basis of the torus that is positive for the
orientation of the standard form `torusSymplecticForm p`. -/
theorem mpullback_fibreEmbedding_comp_fermatCubicTorusDiffeomorph_symm_apply_pos
    (x : ∀ i, AddCircle (p i))
    (b : Module.Basis (Fin 2) ℝ (TangentSpace (ModelWithCorners.pi fun _ : Unit ⊕ Unit ↦ 𝓘(ℝ)) x))
    (hb : b.orientation = (Manifold.Orientation.ofTopForm (by simp) (torusSymplecticForm p).val
      ((torusSymplecticForm p).isSmoothForm.of_le zero_le)
      (isSymplectic_torusSymplecticForm p).isNondegenerate.apply_ne_zero).orientationAt x) :
    0 < (SmoothForm.mpullback (fibreEmbedding ∘ (fermatCubicTorusDiffeomorph p).symm)
      (fibreEmbedding.contMDiff.comp (fermatCubicTorusDiffeomorph p).symm.contMDiff)
      symplecticForm).val x b := by
  have hω := (Manifold.Orientation.orientation_eq_orientationAt_ofTopForm_iff _ _ _ b).1 hb
  obtain ⟨z, rfl⟩ := latticeTorusCover_surjective p fermatPeriodBasis x
  have hωL := eval₂_torusSymplecticForm_mfderiv_latticeTorusCover_pos p z
  have hσL := eval₂_mpullback_fibreEmbedding_mfderiv_latticeTorusCover_pos p z
  rw [SmoothBundleForm.eval₂_apply] at hωL hσL
  exact AlternatingMap.pos_apply_basis_of_pos
    (f := ((torusSymplecticForm p).val _).toAlternatingMap)
    (g := ((SmoothForm.mpullback (fibreEmbedding ∘ (fermatCubicTorusDiffeomorph p).symm)
      (fibreEmbedding.contMDiff.comp (fermatCubicTorusDiffeomorph p).symm.contMDiff)
      symplecticForm).val _).toAlternatingMap)
    b hωL hσL hω

end rationalEllipticSurface

end SymplecticGeometry

end
