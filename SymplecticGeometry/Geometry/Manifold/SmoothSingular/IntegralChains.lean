/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Cohomology.IntegralChains
public import TauCeti.Geometry.Manifold.SmoothSingular.Period
public import TauCeti.Geometry.Manifold.SmoothSingular.SingularCohomology
import SymplecticGeometry.Geometry.Manifold.SmoothSingular.Smoothing

/-!
# De Rham periods on integral homology classes

Let `M` be a Hausdorff `σ`-compact smooth manifold on a finite-dimensional model, and `φ` a closed
smooth real `p`-form on `M`. Tau Ceti's de Rham homomorphism sends the class of `φ` to a class
`deRhamHom [φ]` of `Hᵖ(M; ℝ)`, computed from real chains, while the periods
`TauCeti.closedFormHomologyPeriod φ` of `φ` are defined on integral homology. Read through integral
chains (`TopCat.singularCohomologyIntChainsIso`), `deRhamHom [φ]` is a class with values in `ℝ`
on integral chains, which pairs with integral homology classes `z ∈ Hₚ(M; ULift ℤ)`, those of
Tau Ceti's fundamental classes. This file shows that the pairing gives the periods:

`⟨deRhamHom [φ], z⟩ = ∫_z φ`

(`TauCeti.singularKronecker_singularCohomologyIntChainsIso_hom_deRhamHom_mk`).

## Proof

Represent `z` by a smooth integral cycle `z'` (smoothing), and `deRhamHom [φ]` by a real cocycle
`ψ`. Read through integral chains, `ψ` takes on `z'` its value on the real cycle `z'_ℝ` with the
same simplices and the coefficients cast to `ℝ`
(`TopCat.chainComplexMap_f_singularCochainComplexIntChainsIso_hom_f`, with the cycle
`SSet.intCastCyclesMap`). On a real smooth cycle, `ψ` gives the integral of `φ`
(`TauCeti.iCycles_chainComplexMap_ι_eq_integrationCochain`, from Tau Ceti's
`TauCeti.singularKronecker_deRhamHom_mk_apply` and
`TauCeti.homologyπ_smoothSingularHomologyIso_hom_singularKronecker_homologyπ`). The integral of
`φ` over `z'_ℝ` is its integral over `z'` read with coefficients `ℤ`
(`TauCeti.intCastChainMap_f_integrationCochain`), which is the period of `φ` on `z`
(`TauCeti.closedFormHomologyPeriod_homologyMap_ι_homologyπ`).

## Main results

* `TauCeti.singularKronecker_singularCohomologyIntChainsIso_hom_deRhamHom_mk`: the pairing of
  `deRhamHom [φ]`, read through integral chains, with `z ∈ Hₚ(M; ULift ℤ)` is the period of `φ`
  on `z`.
* `TauCeti.closedFormHomologyPeriod_uliftIntHomologyIso_smoothSingularHomologyIso`:
  the period of `φ` on the class of a smooth cycle with coefficients `ULift ℤ` is the integral of
  `φ` over it.
* `TauCeti.intCastChainMap_f_integrationCochain`: integration over smooth chains with
  coefficients `ULift ℤ` cast to `ℝ` is integration over the chains read with coefficients `ℤ`.
* `TauCeti.iCycles_chainComplexMap_ι_eq_integrationCochain`: a real cocycle whose class is
  `deRhamHom [φ]` takes on each real smooth cycle the integral of `φ` over it.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 18 (the de Rham theorem).
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.1 (the Kronecker
  pairing and change of coefficients).
-/

public section

noncomputable section

open CategoryTheory Limits
open scoped Manifold ContDiff

namespace TauCeti

variable {E H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M] in
/-- Integration of a form `ψ` over smooth chains with coefficients `ULift ℤ` made real, by casting
their coefficients to `ℝ` (`SSet.intCastChainMap`), is integration over the chains
read with coefficients `ℤ`. -/
theorem intCastChainMap_f_integrationCochain {p : ℕ} (ψ : RoughForm I M ℝ p) :
    (SSet.intCastChainMap ℝ (smoothSingularSubcomplex I M : SSet)).f p ≫
        (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℝ)).map (integrationCochain (R := ℝ) ψ) ≫
          (ModuleCat.restrictScalarsAlgebraMapIso (R := ℤ) (S := ℝ) ℝ).hom =
      (((SSet.chainComplexFunctor (ModuleCat.{0} ℤ)).map uliftIntIso.hom).app
          (smoothSingularSubcomplex I M : SSet)).f p ≫ integrationCochain (R := ℤ) ψ := by
  refine SSet.chainComplex_hom_ext fun σ ↦ ?_
  ext a
  refine (ConcreteCategory.comp_apply _ _ a).trans
    ((SSet.intCastChainMap_f_comp_apply _ σ _ a).trans ?_)
  rw [SSet.ιChainComplex_chainComplexFunctor_map_app_f_assoc,
    ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, uliftIntIso_hom_apply]
  erw [integrationCochain_ιChainComplex, integrationCochain_ιChainComplex]
  rw [one_smul, zsmul_eq_mul]

/-- The period of a closed form `φ` on the class of a smooth cycle `z` with coefficients `ULift ℤ`,
read with coefficients `ℤ` through `TauCeti.uliftIntHomologyIso`, is the integral of `φ` over `z`
with its coefficients read in `ℤ`. -/
theorem closedFormHomologyPeriod_uliftIntHomologyIso_smoothSingularHomologyIso
    {p : ℕ} (φ : closedForms I M p)
    (z : ((smoothSingularSubcomplex I M : SSet).chainComplex
      (ModuleCat.of ℤ (ULift.{0} ℤ))).cycles p) :
    closedFormHomologyPeriod φ ((uliftIntHomologyIso (TopCat.of M) p).hom.hom
      ((smoothSingularHomologyIso I M (ModuleCat.of ℤ (ULift.{0} ℤ)) p).hom.hom
        ((((smoothSingularSubcomplex I M : SSet).chainComplex
          (ModuleCat.of ℤ (ULift.{0} ℤ))).homologyπ p).hom z))) =
      (integrationCochain (R := ℤ) (φ.val : RoughForm I M ℝ p)).hom
        (((((SSet.chainComplexFunctor (ModuleCat.{0} ℤ)).map uliftIntIso.hom).app
          (smoothSingularSubcomplex I M : SSet)).f p).hom
          ((((smoothSingularSubcomplex I M : SSet).chainComplex
            (ModuleCat.of ℤ (ULift.{0} ℤ))).iCycles p).hom z)) := by
  set κ := ((SSet.chainComplexFunctor (ModuleCat.{0} ℤ)).map uliftIntIso.hom).app
    (smoothSingularSubcomplex I M : SSet)
  -- Read with coefficients `ℤ`, the class of `z` is that of the integral cycle `κ z`.
  have hκ : (smoothSingularHomologyIso I M (ModuleCat.of ℤ (ULift.{0} ℤ)) p).hom ≫
      (uliftIntHomologyIso (TopCat.of M) p).hom =
        HomologicalComplex.homologyMap κ p ≫
          (smoothSingularHomologyIso I M (ModuleCat.of ℤ ℤ) p).hom := by
    rw [uliftIntHomologyIso_hom]
    -- The change of coefficients on singular homology is, by definition of
    -- `singularHomologyFunctor`, the map on homology of the change of coefficients on the chains
    -- of `TopCat.toSSet`.
    exact smoothSingularHomologyIso_hom_comp_homologyMap_coefficients _ M uliftIntIso.hom p
  have h := ConcreteCategory.congr_hom hκ
    ((((smoothSingularSubcomplex I M : SSet).chainComplex
      (ModuleCat.of ℤ (ULift.{0} ℤ))).homologyπ p).hom z)
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    ← ConcreteCategory.comp_apply _ (HomologicalComplex.homologyMap κ p),
    HomologicalComplex.homologyπ_naturality, ConcreteCategory.comp_apply,
    smoothSingularHomologyIso_hom _ M (ModuleCat.of ℤ ℤ)] at h
  rw [h, closedFormHomologyPeriod_homologyMap_ι_homologyπ, ← ConcreteCategory.comp_apply _
    (((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).iCycles p),
    HomologicalComplex.cyclesMap_i, ConcreteCategory.comp_apply]

/-- A real singular cocycle `ψ` whose class is `deRhamHom [φ]` takes on every real smooth cycle `w`
the integral of `φ` over `w`. -/
theorem iCycles_chainComplexMap_ι_eq_integrationCochain {p : ℕ} (φ : closedForms I M p)
    (ψ : ((TopCat.of M).singularCochainComplex (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ)).cycles p)
    (hψ : ((TopCat.of M).singularCochainComplex (ModuleCat.of ℝ ℝ) ℝ
      (ModuleCat.of ℝ ℝ)).homologyπ p ψ = deRhamHom I M p (deRhamCohomology.mk I p φ))
    (w : ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℝ ℝ)).cycles p) :
    (((TopCat.of M).singularCochainComplex (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ)).iCycles p
        ψ).hom ((SSet.chainComplexMap (smoothSingularSubcomplex I M).ι (ModuleCat.of ℝ ℝ)).f p
          (((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℝ ℝ)).iCycles p w)) =
      (integrationCochain φ.val.val).hom
        (((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℝ ℝ)).iCycles p w) := by
  have h := ConcreteCategory.congr_hom
    (homologyπ_smoothSingularHomologyIso_hom_singularKronecker_homologyπ (I := I) (M := M)
      (R := ModuleCat.of ℝ ℝ) (N := ModuleCat.of ℝ ℝ) ℝ p ψ) w
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hψ] at h
  exact h.symm.trans (singularKronecker_deRhamHom_mk_apply I M p φ w)

/-- **De Rham periods on integral homology classes.** For a closed smooth real `p`-form `φ` and an
integral homology class `z ∈ Hₚ(M; ULift ℤ)`, the class `deRhamHom [φ]`, read as a class with
values in `ℝ` on integral chains through `TopCat.singularCohomologyIntChainsIso`, evaluates on
`z` to the period of `φ` on `z` read with coefficients `ℤ`. -/
theorem singularKronecker_singularCohomologyIntChainsIso_hom_deRhamHom_mk {p : ℕ}
    (φ : closedForms I M p)
    (z : ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) p).obj
      (ModuleCat.of ℤ (ULift.{0} ℤ))).obj (TopCat.of M)) :
    ((TopCat.of M).singularKronecker ℤ p (((TopCat.of M).singularCohomologyIntChainsIso ℝ p).hom
        (deRhamHom I M p (deRhamCohomology.mk I p φ)))).hom z =
      closedFormHomologyPeriod φ ((uliftIntHomologyIso (TopCat.of M) p).hom.hom z) := by
  -- A smooth cycle `z` with coefficients `ULift ℤ` representing the class.
  obtain ⟨z, rfl⟩ : ∃ z', (smoothSingularHomologyIso I M (ModuleCat.of ℤ (ULift.{0} ℤ)) p).hom.hom
      ((((smoothSingularSubcomplex I M : SSet).chainComplex
        (ModuleCat.of ℤ (ULift.{0} ℤ))).homologyπ p).hom z') = z := by
    obtain ⟨z', hz'⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ p
      ((smoothSingularHomologyIso I M (ModuleCat.of ℤ (ULift.{0} ℤ)) p).inv.hom z)
    exact ⟨z', by rw [hz']; exact Iso.inv_hom_id_apply _ _⟩
  rw [closedFormHomologyPeriod_uliftIntHomologyIso_smoothSingularHomologyIso]
  -- A real cocycle `ψ` representing `deRhamHom [φ]`, and the integral cocycle it gives.
  obtain ⟨ψ, hψ⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ p
    (deRhamHom I M p (deRhamCohomology.mk I p φ))
  have hI : ((TopCat.of M).singularCohomologyIntChainsIso ℝ p).hom
      (((TopCat.of M).singularCochainComplex (ModuleCat.of ℝ ℝ) ℝ
        (ModuleCat.of ℝ ℝ)).homologyπ p ψ) = _ :=
    (TopCat.of M).map_homologyπ_singularCohomologyIntChainsIso_hom_apply ℝ p ψ
  rw [← hψ, hI]
  refine (ConcreteCategory.congr_hom
    (homologyπ_smoothSingularHomologyIso_hom_singularKronecker_homologyπ (I := I) (M := M)
      (R := ModuleCat.of ℤ (ULift.{0} ℤ)) (N := ModuleCat.of ℤ ℝ) ℤ p _) z).trans ?_
  -- The cycles of the restricted cochain complex are those of the restricted short complex only
  -- after unfolding, which `rw` does not see.
  erw [TopCat.mapCyclesIso_inv_cyclesMap_singularCochainComplexIntChainsIso_hom_iCycles_apply]
  rw [ConcreteCategory.comp_apply]
  erw [TopCat.chainComplexMap_f_singularCochainComplexIntChainsIso_hom_f]
  rw [← ConcreteCategory.comp_apply _ (integrationCochain (R := ℤ) _),
    ← intCastChainMap_f_integrationCochain]
  simp only [ConcreteCategory.comp_apply]
  congr 1
  -- The cycle `z` with its coefficients cast to `ℝ`, a real smooth cycle.
  have h := iCycles_chainComplexMap_ι_eq_integrationCochain φ ψ hψ
    (SSet.intCastCyclesMap ℝ (smoothSingularSubcomplex I M : SSet) p z)
  -- The restricted cycles have the carrier of the real cycles, and the underlying chain of the
  -- cast cycle is read in the restricted complex, whose chains are the real chains only after
  -- unfolding.
  erw [SSet.intCastCyclesMap_iCycles_apply] at h
  exact h

end TauCeti

end
