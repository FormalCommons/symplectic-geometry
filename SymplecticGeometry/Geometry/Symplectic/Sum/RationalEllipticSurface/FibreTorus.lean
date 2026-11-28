/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Sum.FermatCubic
public import SymplecticGeometry.Geometry.Symplectic.Sum.RationalEllipticSurface.Basic
public import SymplecticGeometry.Geometry.Symplectic.Manifold.Torus.Area
public import SymplecticGeometry.Geometry.Manifold.Orientation.PositiveForm
import SymplecticGeometry.Geometry.Symplectic.Moser.Surface
import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.Pseudoholomorphic
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Integration.Positivity
import SymplecticGeometry.LinearAlgebra.Alternating.Sign
import TauCeti.Geometry.Manifold.MFDeriv.Basic

/-!
# The fibre of `E(1)` as the standard symplectic torus

Let `φ = SymplecticGeometry.fermatCubicTorusDiffeomorph p` be the diffeomorphism from the Fermat
cubic, the fibre of the rational elliptic surface `E(1)` over `[1 : 0]`, onto Tau Ceti's standard
torus `T = ∀ i : Unit ⊕ Unit, AddCircle (p i)`. Pulling the symplectic form of `E(1)` back along
`fibreEmbedding ∘ φ⁻¹` gives a two-form `σ` on `T`. This file shows that `σ` is positive on every
tangent basis of `T` that is positive for `TauCeti.torusSymplecticOrientation p`, the orientation of
`TauCeti.torusSymplecticForm p`. So `σ` and the standard form satisfy the hypotheses on signs of
Moser's theorem for area forms,
`TauCeti.SmoothTwoForm.exists_diffeomorph_mpullback_eq_of_integralTopForm_eq`.

The proof compares both forms with the complex structure of `ℂ`. Let `π` be the covering map
`SymplecticGeometry.latticeTorusCover p b` of `T` by `ℂ`, for the positively oriented basis
`b = fermatPeriodBasis` of the period lattice, and let `z ∈ ℂ` lie over a point `x` of `T`.

* `π` pulls the standard form back to `det A • ω₀`, with `det A > 0`, so the standard form is
  positive on the pair `(dπ 1, dπ i)`
  (`SymplecticGeometry.eval₂_torusSymplecticForm_mfderiv_latticeTorusCover_pos`).
* `φ⁻¹ ∘ π` is the class map `ℂ → ℂ / Λ` followed by the uniformization and the inverse of
  `fermatCubicDiffeomorph`, so `H = fibreEmbedding ∘ φ⁻¹ ∘ π` is holomorphic, hence
  pseudoholomorphic for the complex structures (`isPseudoholomorphicAt_ofComplexManifold_iff`).
  Since `H` is an immersion, and the form of `E(1)` tames the complex structure
  (`SymplecticGeometry.rationalEllipticSurface.tames_symplecticForm`), its pull-back along `H` is
  positive on `(1, i)` (`TauCeti.SmoothTwoForm.Tames.eval₂_mpullback_pos`); that is, `σ` is
  positive on `(dπ 1, dπ i)`.

Two alternating forms on the plane `T_x T` that are positive on one pair have the same sign on
every basis (`AlternatingMap.pos_apply_basis_of_pos`), which gives the claim.

Then the file identifies the fibre with the standard symplectic torus. Since `σ` is positive,
its integral `A` over `T` for the orientation `TauCeti.torusSymplecticOrientation p` is positive
(`TauCeti.Manifold.Orientation.IsPositive.integralTopForm_pos`), and the standard form has
integral `p inl * p inr` (`TauCeti.integralTopForm_torusSymplecticForm`). So for
`c = torusScale p = p inl * p inr / A > 0`, the forms `c • σ` and `torusSymplecticForm p` have
the same integral, and Moser's theorem gives a diffeomorphism `χ` of `T` with
`χ^*(c • σ) = torusSymplecticForm p`. The diffeomorphism `torusDiffeomorph p` is `φ⁻¹ ∘ χ`.

## Main results

* `isPositive_mpullback_fibreEmbedding_comp_fermatCubicTorusDiffeomorph_symm`:
  `σ` is positive for the orientation of the standard torus.
* `torusScale p`: the constant `p inl * p inr / A` by which the form of `E(1)` is rescaled, and
  `torusScale_pos`: it is positive.
* `torusDiffeomorph p`: the diffeomorphism `φ⁻¹ ∘ χ` from the standard torus onto the fibre.
* `mpullback_fibreEmbedding_comp_torusDiffeomorph`: `fibreEmbedding ∘ torusDiffeomorph p` pulls
  `torusScale p` times the form of `E(1)` back to `torusSymplecticForm p`.

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
      Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq, and_true, coe_fermatUniformization, φ]
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
    refine (map_ne_zero_iff _ ?_).2 (one_ne_zero (α := ℂ))
    refine TauCeti.injective_mfderiv_comp (J := ModelWithCorners.pi fun _ : Unit ⊕ Unit ↦ 𝓘(ℝ))
      (TauCeti.injective_mfderiv_comp
        (fibreEmbedding.isImmersion.mfderiv_injective (by simp) _)
        (φ.symm.isInvertible_mfderiv (by simp)).injective)
      (hπ.isInvertible_mfderiv (by simp) z).injective
  have h := SmoothForm.eval₂_mpullback (latticeTorusCover p fermatPeriodBasis) hπ.contMDiff
    (SmoothForm.mpullback (fibreEmbedding ∘ φ.symm)
      (fibreEmbedding.contMDiff.comp φ.symm.contMDiff) symplecticForm) z (1 : ℂ) I
  rw [← h, SmoothForm.mpullback_mpullback]
  have h2 := tames_symplecticForm.eval₂_mpullback_pos
    (J := SmoothAlmostComplexStructure.ofComplexManifold ℂ ℂ)
    (isPseudoholomorphicAt_ofComplexManifold_iff.2 hhol)
    ((fibreEmbedding.contMDiff.comp φ.symm.contMDiff).comp hπ.contMDiff) hne
  rwa [SmoothAlmostComplexStructure.ofComplexManifold_apply, smul_eq_mul, mul_one] at h2

/-- **The form of `E(1)` on its fibre is positive for the orientation of the standard torus.**
Let `φ = fermatCubicTorusDiffeomorph p` identify the Fermat cubic, the fibre of the rational
elliptic surface over `[1 : 0]`, with the standard torus `∀ i : Unit ⊕ Unit, AddCircle (p i)`.
The pull-back of the symplectic form of the rational elliptic surface along
`fibreEmbedding ∘ φ⁻¹` is positive for the orientation of the standard form
`torusSymplecticForm p`. -/
theorem isPositive_mpullback_fibreEmbedding_comp_fermatCubicTorusDiffeomorph_symm :
    (torusSymplecticOrientation p).IsPositive
      (SmoothForm.mpullback (fibreEmbedding ∘ (fermatCubicTorusDiffeomorph p).symm)
        (fibreEmbedding.contMDiff.comp (fermatCubicTorusDiffeomorph p).symm.contMDiff)
        symplecticForm).val :=
  Manifold.Orientation.isPositive_iff_forall_apply_pos.2 fun x b hb ↦ by
  have hω := (isPositive_torusSymplecticForm p).apply_pos hb
  obtain ⟨z, rfl⟩ := latticeTorusCover_surjective p fermatPeriodBasis x
  have hωL := eval₂_torusSymplecticForm_mfderiv_latticeTorusCover_pos p fermatPeriodBasis
    zero_lt_im_conj_mul_fermatPeriodBasis z
  have hσL := eval₂_mpullback_fibreEmbedding_mfderiv_latticeTorusCover_pos p z
  rw [SmoothBundleForm.eval₂_apply] at hωL hσL
  exact AlternatingMap.pos_apply_basis_of_pos
    (f := ((torusSymplecticForm p).val _).toAlternatingMap)
    (g := ((SmoothForm.mpullback (fibreEmbedding ∘ (fermatCubicTorusDiffeomorph p).symm)
      (fibreEmbedding.contMDiff.comp (fermatCubicTorusDiffeomorph p).symm.contMDiff)
      symplecticForm).val _).toAlternatingMap)
    b hωL hσL hω

/-- The pull-back of the form of `E(1)` to the standard torus has positive integral over it,
for the orientation of the standard form `torusSymplecticForm p`. -/
theorem integralTopForm_mpullback_fibreEmbedding_comp_fermatCubicTorusDiffeomorph_symm_pos :
    0 < integralTopForm (torusSymplecticOrientation p)
      (SmoothForm.mpullback (fibreEmbedding ∘ (fermatCubicTorusDiffeomorph p).symm)
        (fibreEmbedding.contMDiff.comp (fermatCubicTorusDiffeomorph p).symm.contMDiff)
        symplecticForm).val :=
  (isPositive_mpullback_fibreEmbedding_comp_fermatCubicTorusDiffeomorph_symm p).integralTopForm_pos
    (SmoothForm.isSmoothForm _ |>.of_le zero_le) (isClosed_tsupport _).isCompact

/-- The constant by which the form of `E(1)` is rescaled so that its fibre, the Fermat cubic, has
the area `p inl * p inr` of the standard torus `∀ i : Unit ⊕ Unit, AddCircle (p i)`: that area
divided by the integral of the pull-back of the form of `E(1)` along
`fibreEmbedding ∘ (fermatCubicTorusDiffeomorph p)⁻¹`, for the orientation of
`torusSymplecticForm p`. -/
noncomputable def torusScale : ℝ :=
  p (.inl ()) * p (.inr ()) /
    integralTopForm (torusSymplecticOrientation p)
      (SmoothForm.mpullback (fibreEmbedding ∘ (fermatCubicTorusDiffeomorph p).symm)
        (fibreEmbedding.contMDiff.comp (fermatCubicTorusDiffeomorph p).symm.contMDiff)
        symplecticForm).val

theorem torusScale_def :
    torusScale p = p (.inl ()) * p (.inr ()) /
      integralTopForm (torusSymplecticOrientation p)
        (SmoothForm.mpullback (fibreEmbedding ∘ (fermatCubicTorusDiffeomorph p).symm)
          (fibreEmbedding.contMDiff.comp (fermatCubicTorusDiffeomorph p).symm.contMDiff)
          symplecticForm).val := (rfl)

/-- The rescaling constant `torusScale p` is positive. -/
theorem torusScale_pos : 0 < torusScale p :=
  div_pos (mul_pos Fact.out Fact.out)
    (integralTopForm_mpullback_fibreEmbedding_comp_fermatCubicTorusDiffeomorph_symm_pos p)

/-- Moser's theorem for area forms, applied on the standard torus to the standard form and to the
pull-back of `torusScale p` times the form of `E(1)`, which have the same integral. -/
theorem exists_diffeomorph_mpullback_torusScale_smul_eq :
    ∃ χ : (∀ i, AddCircle (p i)) ≃ₘ⟮ModelWithCorners.pi fun _ : Unit ⊕ Unit ↦ 𝓘(ℝ),
        ModelWithCorners.pi fun _ : Unit ⊕ Unit ↦ 𝓘(ℝ)⟯ ∀ i, AddCircle (p i),
      SmoothForm.mpullback χ χ.contMDiff
        (SmoothForm.mpullback (fibreEmbedding ∘ (fermatCubicTorusDiffeomorph p).symm)
          (fibreEmbedding.contMDiff.comp (fermatCubicTorusDiffeomorph p).symm.contMDiff)
          (torusScale p • symplecticForm)) = torusSymplecticForm p := by
  have hint := integralTopForm_mpullback_fibreEmbedding_comp_fermatCubicTorusDiffeomorph_symm_pos p
  refine SmoothTwoForm.exists_diffeomorph_mpullback_eq_of_integralTopForm_eq
    (torusSymplecticOrientation p) ?_ ?_ ?_
  · exact isPositive_torusSymplecticForm p
  · rw [map_smul, SetLike.val_smul]
    exact (isPositive_mpullback_fibreEmbedding_comp_fermatCubicTorusDiffeomorph_symm p).smul
      (torusScale_pos p)
  · rw [map_smul, SetLike.val_smul, integralTopForm_smul, integralTopForm_torusSymplecticForm,
      torusScale_def, div_mul_cancel₀ _ hint.ne']

/-- **The fibre of `E(1)` as the standard symplectic torus.** A diffeomorphism from Tau Ceti's
standard torus `∀ i : Unit ⊕ Unit, AddCircle (p i)` onto the Fermat cubic, the fibre of the
rational elliptic surface over `[1 : 0]`, along which `fibreEmbedding` pulls `torusScale p` times
the form of `E(1)` back to `torusSymplecticForm p`
(`mpullback_fibreEmbedding_comp_torusDiffeomorph`). It is the inverse of
`fermatCubicTorusDiffeomorph p` after a diffeomorphism of the torus given by Moser's theorem. -/
noncomputable def torusDiffeomorph :
    (∀ i, AddCircle (p i)) ≃ₘ⟮ModelWithCorners.pi fun _ : Unit ⊕ Unit ↦ 𝓘(ℝ),
      𝓘(ℝ, Fin 1 → ℂ)⟯ SmoothProjectiveHypersurface.fermat 1 3 :=
  (exists_diffeomorph_mpullback_torusScale_smul_eq p).choose.trans
    (fermatCubicTorusDiffeomorph p).symm

theorem torusDiffeomorph_def :
    torusDiffeomorph p = (exists_diffeomorph_mpullback_torusScale_smul_eq p).choose.trans
      (fermatCubicTorusDiffeomorph p).symm := (rfl)

/-- `fibreEmbedding ∘ torusDiffeomorph p` pulls `torusScale p` times the symplectic form of
`E(1)` back to the standard symplectic form `torusSymplecticForm p` of the torus. -/
theorem mpullback_fibreEmbedding_comp_torusDiffeomorph :
    SmoothForm.mpullback (fibreEmbedding ∘ torusDiffeomorph p)
      (fibreEmbedding.contMDiff.comp (torusDiffeomorph p).contMDiff)
      (torusScale p • symplecticForm) = torusSymplecticForm p := by
  rw [← (exists_diffeomorph_mpullback_torusScale_smul_eq p).choose_spec,
    SmoothForm.mpullback_mpullback]
  exact SmoothForm.mpullback_congr _ _
    (by rw [torusDiffeomorph_def, Diffeomorph.coe_trans, Function.comp_assoc]) _

end rationalEllipticSurface

end SymplecticGeometry

end
