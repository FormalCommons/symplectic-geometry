/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.SimplicialSet.Homology.RestrictScalars
public import TauCeti.Algebra.Category.ModuleCat.RestrictScalars
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.FundamentalClass
public import TauCeti.Geometry.Manifold.SmoothSingular.DeRham
public import TauCeti.Geometry.Manifold.SmoothSingular.Smoothing

/-!
# Periods of closed forms on integral singular homology

For a closed smooth real `p`-form `φ` on a Hausdorff `σ`-compact manifold `M` and a class
`A ∈ Hₚ(M; ℤ)` of ordinary (continuous) singular homology, the period `⟨[φ], A⟩` is the integral
of `φ` over any smooth integral cycle `z = ∑ nᵢ σᵢ` representing `A`, that is `∑ nᵢ ∫_{σᵢ} φ`.
Such a cycle exists, and is unique up to smooth boundaries, by the smoothing theorem
(`TauCeti.smoothSingularHomologyIso`), and the integral does not depend on the choice by Stokes'
theorem. Exact forms integrate to zero on cycles, so the period depends only on the de Rham class.

## Main declarations

* `TauCeti.intIntegrationCochain φ`: the integral of a `p`-form over integral smooth singular
  `p`-chains, `∑ nᵢ σᵢ ↦ ∑ nᵢ ∫_{σᵢ} φ`: Tau Ceti's real `TauCeti.integrationCochain` after the
  change of coefficients.
* `TauCeti.intIntegrationCochain_sum_apply`: additivity in finitely many continuous forms.
* `TauCeti.d_comp_intIntegrationCochain`: Stokes' theorem for integral smooth chains.
* `TauCeti.intIntegrationCochain_naturality`: naturality under smooth maps.
* `TauCeti.deRhamCohomology.singularHomologyPeriod`: the pairing of `Hᵖ_dR(M)` with the integral
  singular homology `Hₚ(M; ℤ)`, in the model of Tau Ceti's fundamental classes
  (`TauCeti.HomologicalOrientation.mapFundamentalClass`).
* `TauCeti.deRhamCohomology.singularHomologyPeriod_mk_apply_smoothCycle`: on the image of the class
  of a smooth integral cycle, the period of a closed form is its integral over the cycle.
* `TauCeti.deRhamCohomology.singularHomologyPeriod_map`: `⟨f^* c, A⟩ = ⟨c, f_* A⟩` for smooth `f`.

## Implementation notes

Integral homology is written as Mathlib's `singularHomologyFunctor` with coefficients
`ModuleCat.of ℤ (ULift ℤ)`, the type of `TauCeti.HomologicalOrientation.mapFundamentalClass`, so
that the period applies to fundamental classes as they are. The target of the smoothing
isomorphism is the same module, written as the simplicial homology of
`TopCat.toSSet.obj (TopCat.of M)`; the two are equal by definition, and no cast is needed.

The integral cochain is the composite of the change of coefficients `ℤ → ℝ` on chains,
`SSet.restrictScalarsChainMap` along `algebraMap ℤ ℝ` applied to Tau Ceti's coefficient map
`TauCeti.intToRealCoeff` (with `ℝ` read as the restriction of scalars of the `ℝ`-module `ℝ`), with
the restriction of scalars of Tau Ceti's real-coefficient `TauCeti.integrationCochain`. Its value
on a simplex, Stokes' theorem and naturality are then derived from Tau Ceti's
`TauCeti.integrationCochain_ιChainComplex`, `TauCeti.d_comp_integrationCochain` and
`TauCeti.integrationCochain_naturality`. Its target is `ℝ` (or `F`) viewed as a `ℤ`-module.

In degree one, Tau Ceti's `TauCeti.deRhamCohomology.homologyPeriod` pairs `H¹_dR(M)` with the
homology of the chains `TauCeti.singularChains ℤ` (coefficients `ModuleCat.of ℤ ℤ`, not
`ULift ℤ`) and integrates along paths rather than over smooth simplices; relating the two needs
the change of coefficients `ULift ℤ ≅ ℤ` on homology and a comparison of the path integral with
the simplex integral on smooth `1`-simplices, which Tau Ceti does not provide, so it is not done
here.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 18 (smooth singular homology, Theorem 18.7, and the de Rham
  homomorphism, Proposition 18.13).
-/

public section

noncomputable section

open AlgebraicTopology CategoryTheory
open scoped Manifold ContDiff Simplicial

namespace TauCeti

section Cochain

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℕ}

/-- The integral of a `p`-form over integral smooth singular `p`-chains: the `ℤ`-linear map
`∑ nᵢ σᵢ ↦ ∑ nᵢ ∫_{σᵢ} φ`, Tau Ceti's real integration cochain after the change of coefficients
`ℤ → ℝ`. -/
def intIntegrationCochain (φ : RoughForm I M F p) :
    ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ (ULift.{0} ℤ))).X p ⟶
      (ModuleCat.restrictScalars (algebraMap ℤ ℝ)).obj (ModuleCat.of ℝ F) :=
  (SSet.restrictScalarsChainMap (algebraMap ℤ ℝ)
      (intToRealCoeff ≫ (ModuleCat.restrictScalarsAlgebraMapIso ℝ).inv) _).f p ≫
    (ModuleCat.restrictScalars (algebraMap ℤ ℝ)).map (integrationCochain φ)

/-- The integral over an integral chain is the real integral over the same chain with its
coefficients cast to `ℝ`. -/
theorem intIntegrationCochain_apply (φ : RoughForm I M F p)
    (c : ((smoothSingularSubcomplex I M : SSet).chainComplex
      (ModuleCat.of ℤ (ULift.{0} ℤ))).X p) :
    (intIntegrationCochain φ).hom c =
      (integrationCochain φ).hom (((SSet.restrictScalarsChainMap (algebraMap ℤ ℝ)
        (intToRealCoeff ≫ (ModuleCat.restrictScalarsAlgebraMapIso ℝ).inv) _).f p).hom c) :=
  (rfl)

/-- The integral of `φ` over a simplex with integral coefficient `n` is `n` times its integral. -/
theorem intIntegrationCochain_ιChainComplex (φ : RoughForm I M F p) (σ : SmoothSimplex I M p)
    (n : ULift.{0} ℤ) :
    (intIntegrationCochain φ).hom (((smoothSingularSubcomplex I M : SSet).ιChainComplex
      (R := ModuleCat.of ℤ (ULift.{0} ℤ)) σ).hom n) = n.down • σ.integral φ := by
  rw [intIntegrationCochain_apply, SSet.restrictScalarsChainMap_f_ιChainComplex,
    ModuleCat.comp_apply, ModuleCat.restrictScalarsAlgebraMapIso_inv_apply, intToRealCoeff_apply,
    integrationCochain_ιChainComplex, Int.cast_smul_eq_zsmul]

/-- The integral of the zero form over integral chains is zero. -/
@[simp]
theorem intIntegrationCochain_zero : intIntegrationCochain (0 : RoughForm I M F p) = 0 := by
  rw [intIntegrationCochain, integrationCochain_zero, Functor.map_zero, Limits.comp_zero]

/-- The integral over integral chains is additive in continuous forms. -/
theorem intIntegrationCochain_add [IsManifold I 1 M] {φ ψ : RoughForm I M F p}
    (hφ : IsSmoothForm I 0 φ) (hψ : IsSmoothForm I 0 ψ) :
    intIntegrationCochain (φ + ψ) = intIntegrationCochain φ + intIntegrationCochain ψ := by
  rw [intIntegrationCochain, integrationCochain_add hφ hψ, Functor.map_add,
    Preadditive.comp_add, intIntegrationCochain, intIntegrationCochain]

/-- The integral over an integral chain of a finite sum of continuous forms is the sum of their
integrals. -/
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

/-- The integral over integral chains is homogeneous in the form. -/
theorem intIntegrationCochain_smul_apply (a : ℝ) (φ : RoughForm I M F p)
    (c : ((smoothSingularSubcomplex I M : SSet).chainComplex
      (ModuleCat.of ℤ (ULift.{0} ℤ))).X p) :
    (intIntegrationCochain (a • φ)).hom c = a • ((intIntegrationCochain φ).hom c : F) := by
  rw [intIntegrationCochain_apply, intIntegrationCochain_apply, integrationCochain_smul,
    ModuleCat.hom_smul]
  exact LinearMap.smul_apply a (integrationCochain φ).hom _

variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {N : Type} [TopologicalSpace N] [ChartedSpace H' N]

/-- The integral over integral chains is natural for the chain map induced by a smooth map:
integrating `ψ` over the image of a chain is integrating its pullback over the chain. -/
@[reassoc]
theorem intIntegrationCochain_naturality {f : M → N} (hf : ContMDiff I J ∞ f)
    (ψ : RoughForm J N F p) :
    (SSet.chainComplexMap (smoothSingularSubcomplexMap f hf)
      (ModuleCat.of ℤ (ULift.{0} ℤ))).f p ≫ intIntegrationCochain ψ =
        intIntegrationCochain (mpullback I J f ψ) := by
  rw [intIntegrationCochain, SSet.chainComplexMap_f_restrictScalarsChainMap_assoc,
    ← Functor.map_comp, integrationCochain_naturality, intIntegrationCochain]

section Stokes

variable [IsManifold I 2 M]

/-- **Stokes' theorem for integral smooth chains.** The integral of a `C¹` form over the boundary
of an integral smooth singular chain is the integral of its exterior derivative over the chain. -/
@[reassoc]
theorem d_comp_intIntegrationCochain {φ : RoughForm I M F p} (hφ : IsSmoothForm I 1 φ) :
    ((smoothSingularSubcomplex I M : SSet).chainComplex
      (ModuleCat.of ℤ (ULift.{0} ℤ))).d (p + 1) p ≫ intIntegrationCochain φ =
        intIntegrationCochain (mextDeriv φ) := by
  rw [intIntegrationCochain, ← (SSet.restrictScalarsChainMap _ _ _).comm_assoc,
    Functor.mapHomologicalComplex_obj_d, ← Functor.map_comp, d_comp_integrationCochain hφ,
    intIntegrationCochain]

/-- A closed `C¹` form integrates to zero over the boundary of every integral smooth chain. -/
theorem d_comp_intIntegrationCochain_eq_zero {φ : RoughForm I M F p} (hφ : IsSmoothForm I 1 φ)
    (hdφ : mextDeriv φ = 0) :
    ((smoothSingularSubcomplex I M : SSet).chainComplex
      (ModuleCat.of ℤ (ULift.{0} ℤ))).d (p + 1) p ≫ intIntegrationCochain φ = 0 := by
  rw [d_comp_intIntegrationCochain hφ, hdφ, intIntegrationCochain_zero]

end Stokes

end Cochain

/-! ### The period of a de Rham class on integral singular homology -/

namespace deRhamCohomology

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type} [TopologicalSpace M] [ChartedSpace H M] {p : ℕ}

section Smooth

variable [IsManifold I 2 M]

/-- The integral of a closed form over integral smooth singular cycles, on their homology. -/
private def smoothPeriod (φ : closedForms I M p) :
    (smoothSingularSubcomplex I M : SSet).homology (ModuleCat.of ℤ (ULift.{0} ℤ)) p ⟶
      (ModuleCat.restrictScalars (algebraMap ℤ ℝ)).obj (ModuleCat.of ℝ ℝ) :=
  HomologicalComplex.homologyι _ p ≫ HomologicalComplex.descOpcycles _
    (intIntegrationCochain φ.val.val) (p + 1) (by simp)
    (d_comp_intIntegrationCochain_eq_zero (φ.val.isSmoothForm.of_le (by simp))
      ((mem_closedForms I φ.val).mp φ.property))

private theorem homologyπ_comp_smoothPeriod (φ : closedForms I M p) :
    HomologicalComplex.homologyπ _ p ≫ smoothPeriod φ =
      HomologicalComplex.iCycles _ p ≫ intIntegrationCochain φ.val.val := by
  simp [smoothPeriod]

private theorem smoothPeriod_add (φ ψ : closedForms I M p) :
    smoothPeriod (φ + ψ) = smoothPeriod φ + smoothPeriod ψ := by
  rw [← cancel_epi (HomologicalComplex.homologyπ _ p), Preadditive.comp_add,
    homologyπ_comp_smoothPeriod, homologyπ_comp_smoothPeriod, homologyπ_comp_smoothPeriod,
    ← Preadditive.comp_add, Submodule.coe_add, Submodule.coe_add,
    intIntegrationCochain_add (φ.val.isSmoothForm.of_le (by simp))
      (ψ.val.isSmoothForm.of_le (by simp))]

private theorem smoothPeriod_smul_apply (a : ℝ) (φ : closedForms I M p) (x) :
    (smoothPeriod (a • φ)).hom x = a • (smoothPeriod φ).hom x := by
  obtain ⟨z, rfl⟩ :=
    (ModuleCat.epi_iff_surjective (HomologicalComplex.homologyπ _ p)).mp inferInstance x
  rw [← ConcreteCategory.comp_apply, homologyπ_comp_smoothPeriod, ← ConcreteCategory.comp_apply,
    homologyπ_comp_smoothPeriod, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    Submodule.coe_smul, Submodule.coe_smul, intIntegrationCochain_smul_apply]

private theorem smoothPeriod_eq_zero_of_mem_exactForms (φ : closedForms I M p)
    (hφ : φ.val ∈ exactForms I M p) : smoothPeriod φ = 0 := by
  rw [← cancel_epi (HomologicalComplex.homologyπ _ p), homologyπ_comp_smoothPeriod,
    Limits.comp_zero]
  cases p with
  | zero =>
    rw [exactForms_zero, Submodule.mem_bot] at hφ
    simp [hφ]
  | succ k =>
    obtain ⟨ψ, hψ⟩ := (exactForms_succ I k).le hφ
    rw [← hψ, mextDerivₗ_apply, ← d_comp_intIntegrationCochain (ψ.isSmoothForm.of_le (by simp)),
      HomologicalComplex.iCycles_d_assoc, Limits.zero_comp]

end Smooth

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

/-- The periods of closed forms on integral singular homology, linear in the form. -/
private def singularHomologyPeriodClosedForms :
    closedForms I M p →ₗ[ℝ] (((singularHomologyFunctor (ModuleCat.{0} ℤ) p).obj
      (ModuleCat.of ℤ (ULift.{0} ℤ))).obj (TopCat.of M) →+ ℝ) where
  toFun φ := ((smoothSingularHomologyIso I M (ModuleCat.of ℤ (ULift.{0} ℤ)) p).inv ≫
    smoothPeriod φ).hom.toAddMonoidHom
  map_add' φ ψ := by
    ext A
    simp only [LinearMap.toAddMonoidHom_coe, ModuleCat.hom_comp, LinearMap.comp_apply,
      smoothPeriod_add, ModuleCat.hom_add, LinearMap.add_apply]
    -- Values of a sum of additive maps are sums of values, by definition.
    rfl
  map_smul' a φ := by
    ext A
    simp only [LinearMap.toAddMonoidHom_coe, ModuleCat.hom_comp, LinearMap.comp_apply]
    rw [smoothPeriod_smul_apply]
    -- Values of a multiple of an additive map are multiples of values, by definition.
    rfl

private theorem singularHomologyPeriodClosedForms_apply (φ : closedForms I M p) (A) :
    singularHomologyPeriodClosedForms φ A =
      (smoothPeriod φ).hom
        ((smoothSingularHomologyIso I M (ModuleCat.of ℤ (ULift.{0} ℤ)) p).inv.hom A) :=
  rfl

private theorem ker_mk_le_ker_singularHomologyPeriodClosedForms :
    LinearMap.ker (mk I (M := M) p) ≤
      LinearMap.ker (singularHomologyPeriodClosedForms (I := I) (M := M) (p := p)) := by
  intro φ hφ
  rw [LinearMap.mem_ker, mk_eq_zero_iff] at hφ
  rw [LinearMap.mem_ker]
  ext A
  rw [singularHomologyPeriodClosedForms_apply, smoothPeriod_eq_zero_of_mem_exactForms φ hφ,
    ModuleCat.hom_zero, LinearMap.zero_apply, AddMonoidHom.zero_apply]
  -- The zero of `ℝ` with scalars restricted to `ℤ` is the zero of `ℝ`, by definition.
  rfl

/-- The **period of a de Rham class on integral singular homology**: `⟨[φ], A⟩` is the integral
of the closed form `φ` over a smooth integral cycle representing `A ∈ Hₚ(M; ℤ)`. Such a cycle
exists, and the integral does not depend on it, by the smoothing theorem and Stokes' theorem. -/
def singularHomologyPeriod :
    deRhamCohomology I M p →ₗ[ℝ] (((singularHomologyFunctor (ModuleCat.{0} ℤ) p).obj
      (ModuleCat.of ℤ (ULift.{0} ℤ))).obj (TopCat.of M) →+ ℝ) :=
  LinearMap.liftOfSurjective (R := ℝ) (M := closedForms I M p) (M₂ := deRhamCohomology I M p)
    (M₃ := ((singularHomologyFunctor (ModuleCat.{0} ℤ) p).obj
      (ModuleCat.of ℤ (ULift.{0} ℤ))).obj (TopCat.of M) →+ ℝ)
    (f := mk I (M := M) p) (mk_surjective I p)
    ⟨singularHomologyPeriodClosedForms, ker_mk_le_ker_singularHomologyPeriodClosedForms⟩

private theorem singularHomologyPeriod_mk_apply (φ : closedForms I M p) (A) :
    singularHomologyPeriod (mk I p φ) A =
      (smoothPeriod φ).hom
        ((smoothSingularHomologyIso I M (ModuleCat.of ℤ (ULift.{0} ℤ)) p).inv.hom A) := by
  rw [singularHomologyPeriod, LinearMap.equivOfSurjective_apply]
  rfl

/-- The period of the class of a closed form `φ` on the image in `Hₚ(M; ℤ)` of the class of an
integral smooth cycle `z = ∑ nᵢ σᵢ` is the integral `∑ nᵢ ∫_{σᵢ} φ`. -/
theorem singularHomologyPeriod_mk_apply_smoothCycle (φ : closedForms I M p)
    (z : ((smoothSingularSubcomplex I M : SSet).chainComplex
      (ModuleCat.of ℤ (ULift.{0} ℤ))).cycles p) :
    singularHomologyPeriod (mk I p φ)
        ((smoothSingularHomologyIso I M (ModuleCat.of ℤ (ULift.{0} ℤ)) p).hom.hom
          ((((smoothSingularSubcomplex I M : SSet).chainComplex
            (ModuleCat.of ℤ (ULift.{0} ℤ))).homologyπ p).hom z)) =
      (intIntegrationCochain φ.val.val).hom ((((smoothSingularSubcomplex I M : SSet).chainComplex
        (ModuleCat.of ℤ (ULift.{0} ℤ))).iCycles p).hom z) := by
  refine (singularHomologyPeriod_mk_apply φ _).trans ?_
  rw [Iso.hom_inv_id_apply, ← ConcreteCategory.comp_apply, homologyπ_comp_smoothPeriod,
    ConcreteCategory.comp_apply]

variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  [T2Space N] [SigmaCompactSpace N]

omit [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] [FiniteDimensional ℝ E']
  [T2Space N] [SigmaCompactSpace N] in
private theorem homologyMap_comp_smoothPeriod {f : M → N} (hf : ContMDiff I J ∞ f)
    (ψ : closedForms J N p) :
    SSet.homologyMap (smoothSingularSubcomplexMap f hf) (ModuleCat.of ℤ (ULift.{0} ℤ)) p ≫
        smoothPeriod ψ = smoothPeriod (closedForms.mpullback f hf p ψ) := by
  rw [← cancel_epi (HomologicalComplex.homologyπ _ p), homologyπ_comp_smoothPeriod,
    HomologicalComplex.homologyπ_naturality_assoc, homologyπ_comp_smoothPeriod,
    HomologicalComplex.cyclesMap_i_assoc, intIntegrationCochain_naturality,
    closedForms.coe_mpullback, SmoothForm.coe_mpullback]

/-- **Naturality of periods**: for a smooth map `f : M → N`, a de Rham class `c` of `N` and
`A ∈ Hₚ(M; ℤ)`, `⟨f^* c, A⟩ = ⟨c, f_* A⟩`. -/
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
  rw [← homologyMap_comp_smoothPeriod hf]
  -- `singularHomologyFunctor` is by definition the simplicial homology of `TopCat.toSSet`, so its
  -- map on homology is `SSet.homologyMap` of the induced map of simplicial sets.
  exact ConcreteCategory.congr_hom
    (smoothSingularHomologyIso_inv_naturality_assoc (ModuleCat.of ℤ (ULift.{0} ℤ)) hf p
      (smoothPeriod ψ)) A

end deRhamCohomology

end TauCeti
