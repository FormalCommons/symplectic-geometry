/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.FundamentalClass
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Basic
public import TauCeti.Geometry.Manifold.SmoothSingular.Period

/-!
# Periods of closed forms on singular homology with coefficients `ULift ℤ`

Tau Ceti's fundamental classes (`TauCeti.HomologicalOrientation.fundamentalClass` and
`TauCeti.HomologicalOrientation.mapFundamentalClass`) live in singular homology with coefficients
the `ℤ`-module `ULift ℤ`, while Tau Ceti's periods of closed forms
(`TauCeti.integrationCochain` with integer coefficients, `TauCeti.smoothHomologyPeriodHom`,
`TauCeti.deRhamCohomology.smoothHomologyPeriod` and `TauCeti.closedFormHomologyPeriod`) are
stated for the coefficient module `ℤ`. This file restates them for `ULift ℤ`, through Tau Ceti's
coefficient isomorphism `TauCeti.uliftIntIso`, so that they apply to fundamental classes as they
are.

## Main declarations

* `SymplecticGeometry.intIntegrationCochain φ`: the integral of a `p`-form over smooth singular
  `p`-chains with coefficients `ULift ℤ`, `∑ nᵢ σᵢ ↦ ∑ nᵢ ∫_{σᵢ} φ`: Tau Ceti's integer
  `TauCeti.integrationCochain` after the change of coefficients `ULift ℤ ≅ ℤ` on chains.
* `SymplecticGeometry.intIntegrationCochain_sum_apply`: additivity in finitely many continuous
  forms.
* `SymplecticGeometry.d_comp_intIntegrationCochain`: Stokes' theorem for these chains.
* `SymplecticGeometry.intIntegrationCochain_naturality`: naturality under smooth maps.
* `TauCeti.deRhamCohomology.singularHomologyPeriod`: the pairing of `Hᵖ_dR(M)` with
  `Hₚ(M; ULift ℤ)`, which is Tau Ceti's `TauCeti.closedFormHomologyPeriod` after the change of
  coefficients (`TauCeti.deRhamCohomology.singularHomologyPeriod_mk_apply`).
* `TauCeti.deRhamCohomology.singularHomologyPeriod_mk_apply_smoothCycle`: on the image of the class
  of a smooth cycle, the period of a closed form is its integral over the cycle.
* `TauCeti.deRhamCohomology.singularHomologyPeriod_map`: `⟨f^* c, A⟩ = ⟨c, f_* A⟩` for smooth `f`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 18 (smooth singular homology, Theorem 18.7, and the de Rham
  homomorphism, Proposition 18.13).
-/

public section

noncomputable section

open AlgebraicTopology CategoryTheory
open scoped Manifold ContDiff

namespace SymplecticGeometry

open TauCeti

section Cochain

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℕ}

/-- The integral of a `p`-form over smooth singular `p`-chains with coefficients `ULift ℤ`: the
`ℤ`-linear map `∑ nᵢ σᵢ ↦ ∑ nᵢ ∫_{σᵢ} φ`, Tau Ceti's integer integration cochain after the change
of coefficients `ULift ℤ ≅ ℤ`. -/
def intIntegrationCochain (φ : RoughForm I M F p) :
    ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ (ULift.{0} ℤ))).X p ⟶
      ModuleCat.of ℤ F :=
  (((SSet.chainComplexFunctor (ModuleCat.{0} ℤ)).map uliftIntIso.hom).app _).f p ≫
    integrationCochain (R := ℤ) φ

/-- The integral over a chain with coefficients `ULift ℤ` is the integral over the same chain with
its coefficients read in `ℤ`. -/
theorem intIntegrationCochain_def (φ : RoughForm I M F p) :
    intIntegrationCochain φ =
      (((SSet.chainComplexFunctor (ModuleCat.{0} ℤ)).map uliftIntIso.hom).app _).f p ≫
        integrationCochain (R := ℤ) φ :=
  (rfl)

/-- The integral of `φ` over a simplex with coefficient `n` is `n` times its integral. -/
theorem intIntegrationCochain_ιChainComplex (φ : RoughForm I M F p) (σ : SmoothSimplex I M p)
    (n : ULift.{0} ℤ) :
    (intIntegrationCochain φ).hom (((smoothSingularSubcomplex I M : SSet).ιChainComplex
      (R := ModuleCat.of ℤ (ULift.{0} ℤ)) σ).hom n) = n.down • σ.integral φ := by
  rw [← ConcreteCategory.comp_apply, intIntegrationCochain_def,
    SSet.ιChainComplex_chainComplexFunctor_map_app_f_assoc]
  simp only [ConcreteCategory.comp_apply]
  rw [integrationCochain_ιChainComplex, uliftIntIso_hom_apply]

/-- The integral of the zero form over chains with coefficients `ULift ℤ` is zero. -/
@[simp]
theorem intIntegrationCochain_zero : intIntegrationCochain (0 : RoughForm I M F p) = 0 := by
  rw [intIntegrationCochain_def, integrationCochain_zero, Limits.comp_zero]

/-- The integral over chains with coefficients `ULift ℤ` is additive in continuous forms. -/
theorem intIntegrationCochain_add [IsManifold I 1 M] {φ ψ : RoughForm I M F p}
    (hφ : IsSmoothForm I 0 φ) (hψ : IsSmoothForm I 0 ψ) :
    intIntegrationCochain (φ + ψ) = intIntegrationCochain φ + intIntegrationCochain ψ := by
  rw [intIntegrationCochain_def, integrationCochain_add hφ hψ, Preadditive.comp_add,
    intIntegrationCochain_def, intIntegrationCochain_def]

/-- The integral over a chain with coefficients `ULift ℤ` of a finite sum of continuous forms is
the sum of their integrals. -/
theorem intIntegrationCochain_sum_apply [IsManifold I 1 M] {ι : Type*} (s : Finset ι)
    (φ : ι → RoughForm I M F p) (hφ : ∀ i ∈ s, IsSmoothForm I 0 (φ i))
    (c : ((smoothSingularSubcomplex I M : SSet).chainComplex
      (ModuleCat.of ℤ (ULift.{0} ℤ))).X p) :
    (intIntegrationCochain (∑ i ∈ s, φ i)).hom c =
      ∑ i ∈ s, ((intIntegrationCochain (φ i)).hom c : F) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, intIntegrationCochain_add (hφ i (Finset.mem_insert_self i s))
      (IsSmoothForm.sum _ _ fun j hj ↦ hφ j (Finset.mem_insert_of_mem hj)), ModuleCat.hom_add,
      LinearMap.add_apply, ih fun j hj ↦ hφ j (Finset.mem_insert_of_mem hj), Finset.sum_insert hi]

variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {N : Type} [TopologicalSpace N] [ChartedSpace H' N]

/-- The integral over chains with coefficients `ULift ℤ` is natural for the chain map induced by a
smooth map: integrating `ψ` over the image of a chain is integrating its pullback over the
chain. -/
@[reassoc]
theorem intIntegrationCochain_naturality {f : M → N} (hf : ContMDiff I J ∞ f)
    (ψ : RoughForm J N F p) :
    (SSet.chainComplexMap (smoothSingularSubcomplexMap f hf)
      (ModuleCat.of ℤ (ULift.{0} ℤ))).f p ≫ intIntegrationCochain ψ =
        intIntegrationCochain (mpullback I J f ψ) := by
  rw [intIntegrationCochain_def, SSet.chainComplexMap_f_chainComplexFunctor_map_app_f_assoc,
    integrationCochain_naturality, intIntegrationCochain_def]

/-- **Stokes' theorem for smooth chains with coefficients `ULift ℤ`.** The integral of a `C¹` form
over the boundary of such a chain is the integral of its exterior derivative over the chain. -/
@[reassoc]
theorem d_comp_intIntegrationCochain [IsManifold I 2 M] {φ : RoughForm I M F p}
    (hφ : IsSmoothForm I 1 φ) :
    ((smoothSingularSubcomplex I M : SSet).chainComplex
      (ModuleCat.of ℤ (ULift.{0} ℤ))).d (p + 1) p ≫ intIntegrationCochain φ =
        intIntegrationCochain (mextDeriv φ) := by
  rw [intIntegrationCochain_def, ← HomologicalComplex.Hom.comm_assoc, d_comp_integrationCochain hφ,
    intIntegrationCochain_def]

end Cochain

end SymplecticGeometry

/-! ### The period of a de Rham class on singular homology with coefficients `ULift ℤ` -/

namespace TauCeti.deRhamCohomology

open SymplecticGeometry

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] {p : ℕ}

/-- The **period of a de Rham class on singular homology with coefficients `ULift ℤ`**: `⟨[φ], A⟩`
is Tau Ceti's period `TauCeti.closedFormHomologyPeriod φ` on the class `A` read with coefficients
`ℤ`, that is the integral of `φ` over a smooth integral cycle representing `A`. -/
def singularHomologyPeriod :
    deRhamCohomology I M p →ₗ[ℝ] (((singularHomologyFunctor (ModuleCat.{0} ℤ) p).obj
      (ModuleCat.of ℤ (ULift.{0} ℤ))).obj (TopCat.of M) →+ ℝ) where
  toFun c := (smoothHomologyPeriod c).comp ((uliftIntHomologyIso (TopCat.of M) p).hom ≫
    (smoothSingularHomologyIso I M (ModuleCat.of ℤ ℤ) p).inv).hom.toAddMonoidHom
  map_add' c d := by
    ext A
    rw [map_add]
    -- Both sides evaluate the sum `smoothHomologyPeriod c + smoothHomologyPeriod d` at the same
    -- class.
    rfl
  map_smul' a c := by
    ext A
    rw [map_smul]
    -- Both sides evaluate the multiple `a • smoothHomologyPeriod c` at the same class.
    rfl

/-- The period of the class of a closed form `φ` on `A ∈ Hₚ(M; ULift ℤ)` is Tau Ceti's period of
`φ` on `A` read in `Hₚ(M; ℤ)`. -/
theorem singularHomologyPeriod_mk_apply (φ : closedForms I M p)
    (A : ((singularHomologyFunctor (ModuleCat.{0} ℤ) p).obj
      (ModuleCat.of ℤ (ULift.{0} ℤ))).obj (TopCat.of M)) :
    singularHomologyPeriod (mk I p φ) A =
      closedFormHomologyPeriod φ ((uliftIntHomologyIso (TopCat.of M) p).hom.hom A) :=
  (congrArg (fun f : _ →+ ℝ ↦ f ((smoothSingularHomologyIso I M (ModuleCat.of ℤ ℤ) p).inv.hom
    ((uliftIntHomologyIso (TopCat.of M) p).hom.hom A))) (smoothHomologyPeriod_mk φ)).trans
      (closedFormHomologyPeriod_apply φ _).symm

/-- Changing coefficients from `ULift ℤ` to `ℤ` commutes with the inclusion of smooth singular
chains into singular chains, on homology. -/
private theorem smoothSingularHomologyIso_hom_comp_uliftIntHomologyIso_hom :
    (smoothSingularHomologyIso I M (ModuleCat.of ℤ (ULift.{0} ℤ)) p).hom ≫
        (uliftIntHomologyIso (TopCat.of M) p).hom =
      HomologicalComplex.homologyMap
        (((SSet.chainComplexFunctor (ModuleCat.{0} ℤ)).map uliftIntIso.hom).app
          (smoothSingularSubcomplex I M : SSet)) p ≫
        (smoothSingularHomologyIso I M (ModuleCat.of ℤ ℤ) p).hom := by
  rw [smoothSingularHomologyIso_hom, smoothSingularHomologyIso_hom, uliftIntHomologyIso_hom]
  -- The change of coefficients on singular homology is, by definition of `singularHomologyFunctor`,
  -- the map on homology of the change of coefficients on the chains of `TopCat.toSSet`.
  exact (HomologicalComplex.homologyMap_comp _ _ p).symm.trans
    ((congrArg (HomologicalComplex.homologyMap · p)
      (((SSet.chainComplexFunctor (ModuleCat.{0} ℤ)).map uliftIntIso.hom).naturality
        (smoothSingularSubcomplex I M).ι)).trans (HomologicalComplex.homologyMap_comp _ _ p))

/-- The period of the class of a closed form `φ` on the image in `Hₚ(M; ULift ℤ)` of the class of
a smooth cycle `z = ∑ nᵢ σᵢ` is the integral `∑ nᵢ ∫_{σᵢ} φ`. -/
theorem singularHomologyPeriod_mk_apply_smoothCycle (φ : closedForms I M p)
    (z : ((smoothSingularSubcomplex I M : SSet).chainComplex
      (ModuleCat.of ℤ (ULift.{0} ℤ))).cycles p) :
    singularHomologyPeriod (mk I p φ)
        ((smoothSingularHomologyIso I M (ModuleCat.of ℤ (ULift.{0} ℤ)) p).hom.hom
          ((((smoothSingularSubcomplex I M : SSet).chainComplex
            (ModuleCat.of ℤ (ULift.{0} ℤ))).homologyπ p).hom z)) =
      (intIntegrationCochain (φ.val : RoughForm I M ℝ p)).hom
        ((((smoothSingularSubcomplex I M : SSet).chainComplex
          (ModuleCat.of ℤ (ULift.{0} ℤ))).iCycles p).hom z) := by
  refine (singularHomologyPeriod_mk_apply φ _).trans ?_
  set κ := ((SSet.chainComplexFunctor (ModuleCat.{0} ℤ)).map uliftIntIso.hom).app
    (smoothSingularSubcomplex I M : SSet)
  have h := ConcreteCategory.congr_hom
    (smoothSingularHomologyIso_hom_comp_uliftIntHomologyIso_hom (I := I) (M := M) (p := p))
    ((((smoothSingularSubcomplex I M : SSet).chainComplex
      (ModuleCat.of ℤ (ULift.{0} ℤ))).homologyπ p).hom z)
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    ← ConcreteCategory.comp_apply _ (HomologicalComplex.homologyMap κ p),
    HomologicalComplex.homologyπ_naturality, ConcreteCategory.comp_apply,
    smoothSingularHomologyIso_hom I M (ModuleCat.of ℤ ℤ)] at h
  refine (congrArg (closedFormHomologyPeriod φ) h).trans ?_
  rw [closedFormHomologyPeriod_homologyMap_ι_homologyπ, ← ConcreteCategory.comp_apply,
    ← ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i_assoc, intIntegrationCochain_def,
    ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]

variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  [T2Space N] [SigmaCompactSpace N]

/-- **Naturality of periods**: for a smooth map `f : M → N`, a de Rham class `c` of `N` and
`A ∈ Hₚ(M; ULift ℤ)`, `⟨f^* c, A⟩ = ⟨c, f_* A⟩`. -/
theorem singularHomologyPeriod_map {f : M → N} (hf : ContMDiff I J ∞ f)
    (c : deRhamCohomology J N p)
    (A : ((singularHomologyFunctor (ModuleCat.{0} ℤ) p).obj
      (ModuleCat.of ℤ (ULift.{0} ℤ))).obj (TopCat.of M)) :
    singularHomologyPeriod (map f hf p c) A =
      singularHomologyPeriod c ((((singularHomologyFunctor (ModuleCat.{0} ℤ) p).obj
        (ModuleCat.of ℤ (ULift.{0} ℤ))).map (TopCat.ofHom ⟨f, hf.continuous⟩)).hom A) := by
  obtain ⟨ψ, rfl⟩ := mk_surjective J p c
  rw [map_mk]
  refine (singularHomologyPeriod_mk_apply _ A).trans
    (Eq.trans ?_ (singularHomologyPeriod_mk_apply ψ _).symm)
  refine (closedFormHomologyPeriod_mpullback hf ψ _).trans ?_
  rw [ContinuousMap.singularHomologyMap_eq_homologyMap_toSSet_map]
  -- `singularHomologyFunctor` is by definition the simplicial homology of `TopCat.toSSet`, so its
  -- map on homology is `SSet.homologyMap` of the induced map of simplicial sets.
  exact congrArg (closedFormHomologyPeriod ψ) (ConcreteCategory.congr_hom
    (homologyMap_comp_uliftIntHomologyIso_hom (TopCat.ofHom ⟨f, hf.continuous⟩) p) A).symm

end TauCeti.deRhamCohomology
