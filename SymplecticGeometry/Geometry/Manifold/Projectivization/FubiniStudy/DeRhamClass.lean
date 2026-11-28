/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Cohomology.RealImage
public import SymplecticGeometry.Geometry.Manifold.Complex.Orientation
public import SymplecticGeometry.Geometry.Manifold.DeRham.Basic
public import SymplecticGeometry.Geometry.Manifold.Projectivization.FubiniStudy.Basic
public import SymplecticGeometry.Topology.VectorBundle.Complex.ChernClass.ProjectiveSpace
public import TauCeti.Geometry.Manifold.SmoothSingular.SingularCohomology
public import TauCeti.Topology.VectorBundle.Orientation.Complex.FirstChernClass
import SymplecticGeometry.AlgebraicTopology.Cohomology.FundamentalClass
import SymplecticGeometry.AlgebraicTopology.Cohomology.Projectivization
import SymplecticGeometry.Geometry.Manifold.DeRham.FundamentalClass
import SymplecticGeometry.Geometry.Manifold.Projectivization.ChernClass
import SymplecticGeometry.Geometry.Manifold.Projectivization.FubiniStudy.Normalization
import SymplecticGeometry.Geometry.Manifold.Projectivization.HyperplaneClass
import SymplecticGeometry.Topology.ComplexProjectiveSpace.RealCohomology

/-!
# The de Rham class of the Fubini–Study form

Let `ω_FS = fubiniStudyForm n` be the Fubini–Study form of `ℂPⁿ = ℙ ℂ (Fin (n + 1) → ℂ)`,
normalized so that a line has area `π`, and `h = Projectivization.hyperplaneClass` the hyperplane
class, an integral class with `⟨h, [ℂP¹]⟩ = 1` for the complex orientation. This file computes
the image of the de Rham class `[ω_FS / π]` under Tau Ceti's de Rham homomorphism
`TauCeti.deRhamHom`: it is **minus** the real image of `h`
(`TopCat.singularCohomologyRealImageAddMonoidHom`, after reading `h` with values in `ULift ℤ`
through `TopCat.uliftIntegralCohomologyIso`).

Geometrically `[ω_FS / π]` is `h`. The sign is that of the library's comparison of de Rham
integration with singular cohomology: for a closed surface oriented by `o`, the class
`deRhamHom [φ]` takes the value `∫_o φ` on the fundamental class of the homological orientation
of `-o`, not of `o`
(`Manifold.Orientation.evalFundamentalClass_singularCohomologyIntChainsIso_hom_deRhamHom_mk`, in
the namespace `TauCeti`).
It is the sign of `SymplecticGeometry.Bundle.deRhamHom_realFirstChernClass_eq_neg_projectiveSpace`
and of the exceptional class in
`SymplecticGeometry.IsNormalizedBallEmbedding.deRhamHom_normalizedBlowupForm`.

## Main results

* `SymplecticGeometry.deRhamHom_mk_eq_neg_hyperplaneClass_of_integralTopForm_eq_one`: on `ℂP¹`,
  a closed two-form of integral `1` for the complex orientation has de Rham image `-h`.
* `SymplecticGeometry.deRhamHom_fubiniStudyForm_eq_neg_hyperplaneClass`: on `ℂPⁿ`, the de Rham
  image of `[ω_FS / π]` is `-h`.
* `SymplecticGeometry.deRhamHom_fubiniStudyForm_eq_neg_firstChernClass`: on `ℂPⁿ`, the de Rham
  image of `[(n + 1) ω_FS / π]` is minus the real image of Tau Ceti's first Chern class
  `TauCeti.firstChernClass` of the tangent bundle.

## Proof

On `ℂP¹`, for the complex orientation `o`, the integral `∫_o φ = 1` is the value of `h` on the
fundamental class of `o` (`Projectivization.complexManifoldEvalFundamentalClass_hyperplaneClass`),
so the surface comparison
`TauCeti.Manifold.Orientation.deRhamHom_mk_eq_neg_realImage_of_integralTopForm_eq` gives
`deRhamHom [φ] = -h`. Over `ℂPⁿ` with `n ≥ 1`, restriction along the coordinate line, the
inclusion `Function.ExtendByZero.linearMap` of `Fin.castLE`, is injective on `H²(-; ℝ)`
(`Projectivization.injective_singularCohomologyMap_map_real`); both sides restrict to the classes
on `ℂP¹`, since a line has area `π` (`integralTopForm_mpullback_map_fubiniStudyForm`) and `h`
restricts to `h` (`Projectivization.hyperplaneClass_map`). For `n = 0` the space is a point
(`Projectivization.isZero_singularCohomology_of_finrank_eq_one`). This reduction is
that of `SymplecticGeometry.Bundle.deRhamHom_realFirstChernClass_eq_neg_projectiveSpace`, for a
fixed closed form instead of a curvature form. The corollary for the first Chern class uses
`Projectivization.firstChernClass_tangentSpace`, `c₁(Tℂℙⁿ) = (n + 1) h`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Example 4.3.3 (the Fubini–Study form and the area of a line).
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3 (fundamental classes of closed oriented manifolds).
-/

public section

noncomputable section

open CategoryTheory Module TauCeti Projectivization
open scoped Manifold ContDiff LinearAlgebra.Projectivization

namespace SymplecticGeometry

/-- **A closed two-form of integral one on `ℂP¹` represents minus the hyperplane class.** Let `φ`
be a closed two-form on `ℂP¹ = ℙ ℂ (Fin 2 → ℂ)` whose integral over `ℂP¹`, for its orientation
as a complex curve, is `1`. Then the de Rham homomorphism sends the class of `φ` to minus the real
image of the hyperplane class. The sign comes from the library's convention for comparing de Rham
integration with singular cohomology; geometrically `[φ]` is the hyperplane class. -/
theorem deRhamHom_mk_eq_neg_hyperplaneClass_of_integralTopForm_eq_one
    (φ : closedForms 𝓘(ℝ, Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ)) 2)
    (hφ : integralTopForm (complexCurveOrientation (Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ))) φ.val.val = 1) :
    deRhamHom 𝓘(ℝ, Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ)) 2 (deRhamCohomology.mk _ 2 φ) =
      -(TopCat.of (ℙ ℂ (Fin 2 → ℂ))).singularCohomologyRealImageAddMonoidHom 2
        (((TopCat.of (ℙ ℂ (Fin 2 → ℂ))).uliftIntegralCohomologyIso 2).inv
          (hyperplaneClass (Fin 2 → ℂ))) := by
  have hE : finrank ℝ (Fin 1 → ℂ) = 2 := by
    rw [Module.finrank_pi_fintype]; simp
  refine Manifold.Orientation.deRhamHom_mk_eq_neg_realImage_of_integralTopForm_eq hE
    (complexCurveOrientation (Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ))) φ _ ?_
  have h1 := complexManifoldEvalFundamentalClass_hyperplaneClass
  rw [complexManifoldEvalFundamentalClass_def, complexManifoldHomologicalOrientation_def,
    ← complexCurveOrientation_eq_complexManifoldOrientationOfFinrank] at h1
  rw [hφ, ← HomologicalOrientation.evalFundamentalClass_uliftIntegralCohomologyIso_hom,
    Iso.inv_hom_id_apply]
  exact_mod_cast h1.symm

/-- **The de Rham class of the Fubini–Study form.** On `ℂPⁿ = ℙ ℂ (Fin (n + 1) → ℂ)`, the de Rham
homomorphism sends the class of `ω_FS / π`, for the Fubini–Study form `ω_FS = fubiniStudyForm n`,
to minus the real image of the hyperplane class. The sign comes from the library's convention for
comparing de Rham integration with singular cohomology; geometrically `[ω_FS / π]` is the
hyperplane class. For `n = 0` both sides vanish. -/
theorem deRhamHom_fubiniStudyForm_eq_neg_hyperplaneClass (n : ℕ) :
    deRhamHom 𝓘(ℝ, Fin n → ℂ) (ℙ ℂ (Fin (n + 1) → ℂ)) 2
        (deRhamCohomology.mk _ 2 ⟨(Real.pi)⁻¹ • fubiniStudyForm n,
          ((isSymplectic_fubiniStudyForm n).isClosed.smul _).mem_closedForms⟩) =
      -(TopCat.of (ℙ ℂ (Fin (n + 1) → ℂ))).singularCohomologyRealImageAddMonoidHom 2
        (((TopCat.of (ℙ ℂ (Fin (n + 1) → ℂ))).uliftIntegralCohomologyIso 2).inv
          (hyperplaneClass (Fin (n + 1) → ℂ))) := by
  rcases n with _ | m
  · -- `ℙ ℂ (Fin 1 → ℂ)` is a point, so its second cohomology vanishes.
    exact (ModuleCat.subsingleton_of_isZero (isZero_singularCohomology_of_finrank_eq_one
      (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ) (K := ℂ) (E := Fin (0 + 1) → ℂ) (by simp)
      two_ne_zero)).elim _ _
  · -- Restrict to a projective line, on which `H²(-; ℝ)` injects.
    let ι := Function.ExtendByZero.linearMap ℂ ℂ
      (Fin.castLE (by omega) : Fin 2 → Fin (m + 1 + 1))
    have hι : Function.Injective ι := Function.extend_injective (Fin.castLE_injective _) 0
    have hf := contMDiff_map_restrictScalars ι hι ∞
    refine injective_singularCohomologyMap_map_real ι hι (n := 1) (by simp) one_ne_zero ?_
    have h := deRhamHom_map hf 2 (deRhamCohomology.mk _ 2 ⟨(Real.pi)⁻¹ • fubiniStudyForm (m + 1),
      ((isSymplectic_fubiniStudyForm (m + 1)).isClosed.smul _).mem_closedForms⟩)
    rw [deRhamCohomology.map_mk] at h
    refine h.symm.trans ?_
    rw [deRhamHom_mk_eq_neg_hyperplaneClass_of_integralTopForm_eq_one, map_neg,
      ← TopCat.singularCohomologyRealImageAddMonoidHom_naturality]
    · -- The hyperplane class restricts to the hyperplane class.
      rw [TopCat.uliftIntegralCohomologyIso_inv, TopCat.uliftIntegralCohomologyIso_inv,
        ← TopCat.singularCohomologyValueMap_naturality_apply,
        ← TopCat.uliftIntegralCohomologyIso_inv, hyperplaneClass_map]
    · -- A line has area `π`.
      rw [closedForms.coe_mpullback, map_smul, Submodule.coe_smul, integralTopForm_smul,
        integralTopForm_mpullback_map_fubiniStudyForm, inv_mul_cancel₀ Real.pi_ne_zero]

/-- **The de Rham image of the first Chern class of `ℂPⁿ`.** On `ℂPⁿ = ℙ ℂ (Fin (n + 1) → ℂ)`, the
de Rham homomorphism sends the class of `(n + 1) ω_FS / π`, for the Fubini–Study form
`ω_FS = fubiniStudyForm n`, to minus the real image of Tau Ceti's first Chern class of the
tangent bundle. The sign is that of `deRhamHom_fubiniStudyForm_eq_neg_hyperplaneClass`. -/
theorem deRhamHom_fubiniStudyForm_eq_neg_firstChernClass (n : ℕ) :
    deRhamHom 𝓘(ℝ, Fin n → ℂ) (ℙ ℂ (Fin (n + 1) → ℂ)) 2
        (deRhamCohomology.mk _ 2 ⟨((n + 1 : ℝ) / Real.pi) • fubiniStudyForm n,
          ((isSymplectic_fubiniStudyForm n).isClosed.smul _).mem_closedForms⟩) =
      -(TopCat.of (ℙ ℂ (Fin (n + 1) → ℂ))).singularCohomologyRealImageAddMonoidHom 2
        (TauCeti.firstChernClass (Fin n → ℂ)
          (TangentSpace 𝓘(ℂ, Fin n → ℂ) : ℙ ℂ (Fin (n + 1) → ℂ) → Type)) := by
  have hc := congrArg ((TopCat.of (ℙ ℂ (Fin (n + 1) → ℂ))).uliftIntegralCohomologyIso 2).inv
    (firstChernClass_tangentSpace (m := n))
  rw [Iso.hom_inv_id_apply, map_zsmul] at hc
  have hφ : (⟨((n + 1 : ℝ) / Real.pi) • fubiniStudyForm n,
      ((isSymplectic_fubiniStudyForm n).isClosed.smul _).mem_closedForms⟩ :
        closedForms 𝓘(ℝ, Fin n → ℂ) (ℙ ℂ (Fin (n + 1) → ℂ)) 2) =
      ((n + 1 : ℕ) : ℝ) • ⟨(Real.pi)⁻¹ • fubiniStudyForm n,
        ((isSymplectic_fubiniStudyForm n).isClosed.smul _).mem_closedForms⟩ := by
    ext1
    rw [Submodule.coe_smul, smul_smul, div_eq_mul_inv, Nat.cast_succ]
  rw [hc, hφ, map_smul, map_smul, Nat.cast_smul_eq_nsmul,
    deRhamHom_fubiniStudyForm_eq_neg_hyperplaneClass, natCast_zsmul, map_nsmul, smul_neg]

end SymplecticGeometry

end
