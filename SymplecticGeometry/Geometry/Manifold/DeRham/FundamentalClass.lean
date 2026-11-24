/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.Orientation.Simplex
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.FundamentalClass
public import TauCeti.Geometry.Manifold.Orientation.Euclidean
public import TauCeti.Geometry.Manifold.SmoothSingular.Period
public import TauCeti.Geometry.Manifold.SmoothSingular.TopForm
import Mathlib.Geometry.Manifold.PartitionOfUnity
import SymplecticGeometry.Geometry.Manifold.Orientation.Preserving
import SymplecticGeometry.Geometry.Manifold.SmoothSingular.RelativeCycle
import SymplecticGeometry.Geometry.Manifold.SmoothSingular.Smoothing
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Regularity
import TauCeti.Geometry.Manifold.Orientation.Chart
import TauCeti.Topology.OpenPartialHomeomorph.Constructions

/-!
# Integration against the fundamental class of a surface

Let `C` be a closed surface: a compact Hausdorff smooth manifold modelled on a real normed space
`E'` of dimension two, oriented by `o`. For a closed smooth two-form `φ` on `C` (every two-form is
closed, by `TauCeti.mextDeriv_eq_zero_of_finrank_le`), the integral of `φ` over `C` is the period
of `φ` (`TauCeti.closedFormHomologyPeriod`) on the fundamental class:

`∫_C φ = ⟨[φ], [C]⟩`

(`TauCeti.Manifold.Orientation.integralTopForm_eq_closedFormHomologyPeriod`). Tau Ceti's
fundamental classes have coefficients `ULift ℤ` and its periods are defined on homology with
coefficients `ℤ`, so `[C]` is read with coefficients `ℤ` through `TauCeti.uliftIntHomologyIso`.
The fundamental class is that of the homological orientation of `-o`: Tau Ceti's homological
orientation of a smooth orientation selects at each point minus the class of a positively oriented
simplex (`TopPair.relClass_fullSimplex_eq_neg_toHomologicalOrientation`), and it is the classes
of positively oriented simplices that integration sees.

## Proof

The proof is local.

* Every point lies in the image of the interior of the standard simplex `Δ²` under a map
  `g : ℝ² → C` that is, on a neighbourhood of `Δ²`, a smooth open embedding preserving orientation
  (`TauCeti.Manifold.Orientation.exists_isOpenEmbedding_isOrientationPreservingAt_fullSimplex`):
  the inverse of an oriented chart from Tau Ceti
  (`TauCeti.Manifold.Orientation.exists_partialDiffeomorph_isOrientationPreservingAt`), composed
  with an affine map that puts a small copy of `Δ²` in its target.
* Let `z` be a smooth cycle representing the fundamental class (smoothing), and `ψ` a
  form supported in a compact `K ⊆ g(interior Δ²)`. The image of `z` in `H₂(C, C ∖ K)` is the
  fundamental class along `K`, and so is the class of the simplex `σ` given by `g`
  (`TauCeti.SmoothSimplex.relativeClass_eq_fundamentalClassOn`). Hence `z - σ = ∂ b + c` with `b`
  smooth and `c` a smooth chain of `C ∖ K`
  (`TauCeti.exists_smoothSingular_sub_eq_d_add_of_relClass`). Stokes' theorem and the
  vanishing of `ψ` on `C ∖ K` give `∫_z ψ = ∫_σ ψ`, which is `∫_C ψ` by
  `TauCeti.SmoothSimplex.integral_eq_integralTopForm`
  (`TauCeti.Manifold.Orientation.integrationCochain_iCycles_eq_integralTopForm`).
* A smooth partition of unity subordinate to finitely many such images splits `φ`, and both sides
  are additive.

## Main results

* `TauCeti.Manifold.Orientation.exists_isOpenEmbedding_isOrientationPreservingAt_fullSimplex`:
  positively oriented simplices around every point of an oriented manifold.
* `TauCeti.Manifold.Orientation.integrationCochain_iCycles_eq_integralTopForm`: the local
  statement, for a form supported inside one positively oriented simplex.
* `TauCeti.Manifold.Orientation.integralTopForm_eq_closedFormHomologyPeriod`: `∫_C φ = ⟨[φ], [C]⟩`.
* `TauCeti.Manifold.Orientation.integralTopForm_mpullback_eq_closedFormHomologyPeriod`: for a closed
  two-form `φ` on a manifold `M` and a smooth `u : C → M`, `∫_C u^* φ = ⟨[φ], u_* [C]⟩`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapters 16 and 18.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §2.1 and §3.3.
-/

public section

noncomputable section

open CategoryTheory Set Topology TopologicalSpace Module Filter Simplicial
  SymplecticGeometry
open scoped Manifold ContDiff

namespace TauCeti.Manifold.Orientation

section Simplex

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {C : Type*} [TopologicalSpace C] [ChartedSpace E' C] [IsManifold 𝓘(ℝ, E') ∞ C]
  {p : ℕ} [NeZero p]

/-- **Positively oriented simplices.** Every point `x` of a smooth manifold of positive dimension
`p`, oriented by `o`, lies in the image of the interior of the standard simplex `Δᵖ` under a map
`g : ℝᵖ → C` which, on an open neighbourhood `U` of `Δᵖ`, is smooth, an open embedding, and
orientation preserving from the standard orientation of `ℝᵖ` to `o`. -/
theorem exists_isOpenEmbedding_isOrientationPreservingAt_fullSimplex
    (o : Manifold.Orientation 𝓘(ℝ, E') C (Fin p)) (x : C) :
    ∃ (U : Opens (EuclideanSpace ℝ (Fin p))) (g : EuclideanSpace ℝ (Fin p) → C),
      fullSimplex p ⊆ U ∧ ContMDiffOn (𝓡 p) 𝓘(ℝ, E') ∞ g U ∧
      IsOpenEmbedding (g ∘ ((↑) : U → EuclideanSpace ℝ (Fin p))) ∧
      (∀ y ∈ U, IsOrientationPreservingAt (euclideanSpace p) o g y) ∧
      x ∈ g '' interior (fullSimplex p) := by
  -- An oriented chart `φ : C → ℝᵖ` at `x`; its inverse preserves orientation on its target.
  obtain ⟨φ, hxφ, -, hφo⟩ := o.exists_partialDiffeomorph_isOrientationPreservingAt
    (n := ∞) (euclideanSpace p) isOpen_univ (mem_univ x)
  have hsymm (z) (hz : z ∈ φ.target) : IsOrientationPreservingAt (euclideanSpace p) o φ.symm z :=
    (hφo _ (φ.map_target hz)).partialDiffeomorph_symm hz (by simp)
  -- A ball about `φ x` inside the target of `φ`.
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 φ.open_target (φ x) (φ.map_source hxφ)
  -- Shrink `Δᵖ` into that ball by `A y = φ x + ε • (y - p₀)` around an interior point `p₀`.
  obtain ⟨p₀, hp₀⟩ := nonempty_interior_fullSimplex p
  obtain ⟨R, hR, hsub⟩ := (isCompact_fullSimplex p).isBounded.subset_ball_lt 0 p₀
  set ε := r / R
  have hε : 0 < ε := div_pos hr hR
  set A : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p) := fun y ↦ φ x + ε • (y - p₀)
    with hAdef
  have hA (y) (hy : y ∈ Metric.ball p₀ R) : A y ∈ φ.target := by
    refine hball ?_
    rw [Metric.mem_ball, hAdef, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg hε.le]
    rw [Metric.mem_ball, dist_eq_norm] at hy
    calc ε * ‖y - p₀‖ < ε * R := by gcongr
      _ = r := div_mul_cancel₀ r hR.ne'
  have hAd (y : EuclideanSpace ℝ (Fin p)) :
      HasFDerivAt A (ε • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin p))) y :=
    (((hasFDerivAt_id y).sub_const p₀).const_smul ε).const_add (φ x)
  let T : EuclideanSpace ℝ (Fin p) ≃ₜ EuclideanSpace ℝ (Fin p) := (Homeomorph.subRight p₀).trans
    ((Homeomorph.smulOfNeZero ε hε.ne').trans (Homeomorph.addLeft (φ x)))
  refine ⟨⟨Metric.ball p₀ R, Metric.isOpen_ball⟩, φ.symm ∘ A, hsub, fun y hy ↦ ?_, ?_,
    fun y hy ↦ ?_, ⟨p₀, hp₀, by simpa [A] using φ.left_inv hxφ⟩⟩
  · exact ((φ.symm.contMDiffOn.contMDiffAt (φ.open_target.mem_nhds (hA y hy))).comp y
      (contDiff_const.add
        ((contDiff_id.sub contDiff_const).const_smul ε)).contMDiff.contMDiffAt).contMDiffWithinAt
  · -- On the ball, `φ.symm ∘ A` is the inverse of `φ` after the affine homeomorphism `T`.
    refine φ.symm.toOpenPartialHomeomorph.isOpenEmbedding_comp
      (g := T ∘ ((↑) : Metric.ball p₀ R → _))
      (T.isOpenEmbedding.comp Metric.isOpen_ball.isOpenEmbedding_subtypeVal) ?_
    rintro _ ⟨y, rfl⟩
    exact hA y y.prop
  · refine (hsymm _ (hA y hy)).comp (isOrientationPreservingAt_of_det_fderiv_pos _ ?_)
    rw [(hAd y).fderiv, ContinuousLinearMap.det,
      ContinuousLinearMap.toLinearMap_smul, LinearMap.det_smul]
    simp only [ContinuousLinearMap.coe_id, LinearMap.det_id, mul_one]
    positivity

end Simplex

variable {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {C : Type} [TopologicalSpace C] [ChartedSpace E' C] [IsManifold 𝓘(ℝ, E') ∞ C]
  [T2Space C] [CompactSpace C]

/-- **Integration over a cycle representing the fundamental class, locally.** Let `σ` be the smooth
`2`-simplex given by a map `g : ℝ² → C` that is, on an open neighbourhood `U` of `Δ²`, a smooth
open embedding preserving orientation, and let `z` be a smooth cycle with coefficients `ULift ℤ`
whose class is the fundamental class of the homological orientation of `-o`. Then a `C¹` two-form
`ψ` supported in `g(interior Δ²)` integrates over `z`, with its coefficients read in `ℤ` through
`TauCeti.uliftIntIso`, to its integral over `C`. -/
theorem integrationCochain_iCycles_eq_integralTopForm (hE' : finrank ℝ E' = 2)
    (o : Manifold.Orientation 𝓘(ℝ, E') C (Fin 2))
    (z : ((smoothSingularSubcomplex 𝓘(ℝ, E') C : SSet).chainComplex
      (ModuleCat.of ℤ (ULift.{0} ℤ))).cycles 2)
    (hz : (smoothSingularHomologyIso 𝓘(ℝ, E') C (ModuleCat.of ℤ (ULift.{0} ℤ)) 2).hom.hom
      ((((smoothSingularSubcomplex 𝓘(ℝ, E') C : SSet).chainComplex
        (ModuleCat.of ℤ (ULift.{0} ℤ))).homologyπ 2).hom z) =
      ((-o).toHomologicalOrientation hE').fundamentalClass hE')
    {U : Opens (EuclideanSpace ℝ (Fin 2))} {g : EuclideanSpace ℝ (Fin 2) → C}
    (hU : fullSimplex 2 ⊆ U) (hgs : ContMDiffOn (𝓡 2) 𝓘(ℝ, E') ∞ g U)
    (hg : IsOpenEmbedding (g ∘ ((↑) : U → EuclideanSpace ℝ (Fin 2))))
    (ho : ∀ y ∈ U, IsOrientationPreservingAt (euclideanSpace 2) o g y)
    {ψ : RoughForm 𝓘(ℝ, E') C ℝ 2} (hψ : IsSmoothForm 𝓘(ℝ, E') 1 ψ)
    (hsupp : _root_.tsupport (α := E' [⋀^Fin 2]→L[ℝ] ℝ) ψ ⊆ g '' interior (fullSimplex 2)) :
    (integrationCochain (R := ℤ) ψ).hom
      (((((SSet.chainComplexFunctor (ModuleCat.{0} ℤ)).map uliftIntIso.hom).app
        (smoothSingularSubcomplex 𝓘(ℝ, E') C : SSet)).f 2).hom
        ((((smoothSingularSubcomplex 𝓘(ℝ, E') C : SSet).chainComplex
          (ModuleCat.of ℤ (ULift.{0} ℤ))).iCycles 2).hom z)) = integralTopForm o ψ := by
  set κ := ((SSet.chainComplexFunctor (ModuleCat.{0} ℤ)).map uliftIntIso.hom).app
    (smoothSingularSubcomplex 𝓘(ℝ, E') C : SSet)
  let σ : SmoothSimplex 𝓘(ℝ, E') C 2 := SmoothSimplex.ofContMDiffOn hgs (U.isOpen.mem_nhdsSet.2 hU)
  have hgσ (y : fullSimplex 2) : g y = σ.toContinuousMap y := by simp [σ]
  have hK : IsCompact (_root_.tsupport (α := E' [⋀^Fin 2]→L[ℝ] ℝ) ψ) :=
    (isClosed_tsupport _).isCompact
  let W : Opens C := ⟨(_root_.tsupport (α := E' [⋀^Fin 2]→L[ℝ] ℝ) ψ)ᶜ, hK.isClosed.isOpen_compl⟩
  have hσ := SmoothSimplex.range_toSSetObjEquiv_δ_subset_compl σ hU hgσ hg hsupp
  -- In `H₂(C, W)`, both `z` and `σ` give the fundamental class along the support of `ψ`.
  obtain ⟨b, c, hbc⟩ := exists_smoothSingular_sub_eq_d_add_of_relClass W z σ 1 hσ (by
    rw [hz]
    exact (((-o).toHomologicalOrientation hE').singularHomologyπ_fundamentalClass hE' hK).trans
      (SmoothSimplex.relativeClass_eq_fundamentalClassOn σ hU hgσ hg hE' o ho hK hsupp).symm)
  -- `ψ` integrates to zero over `∂ b`, by Stokes' theorem, and over `c`, where it vanishes.
  have hd : (integrationCochain (R := ℤ) ψ).hom ((κ.f 2).hom
      (((smoothSingularSubcomplex 𝓘(ℝ, E') C : SSet).chainComplex
      (ModuleCat.of ℤ (ULift.{0} ℤ))).d 3 2 b)) = 0 := by
    have h : ((smoothSingularSubcomplex 𝓘(ℝ, E') C : SSet).chainComplex
        (ModuleCat.of ℤ (ULift.{0} ℤ))).d 3 2 ≫ κ.f 2 ≫ integrationCochain (R := ℤ) ψ = 0 := by
      rw [← HomologicalComplex.Hom.comm_assoc, d_comp_integrationCochain (p := 2) hψ,
        mextDeriv_eq_zero_of_finrank_le hE'.le, integrationCochain_zero, Limits.comp_zero]
    simpa using ConcreteCategory.congr_hom h b
  have hc : (integrationCochain (R := ℤ) ψ).hom ((κ.f 2).hom ((SSet.chainComplexMap
      (smoothSingularSubcomplexMap (Subtype.val : W → C) (contMDiff_subtypeVal (I := 𝓘(ℝ, E'))))
        (ModuleCat.of ℤ (ULift.{0} ℤ))).f 2 c)) = 0 := by
    have h0 : mpullback 𝓘(ℝ, E') 𝓘(ℝ, E') (Subtype.val : W → C) ψ = 0 :=
      funext fun y ↦ mpullback_apply_eq_zero (image_eq_zero_of_notMem_tsupport y.prop)
    have h : (SSet.chainComplexMap (smoothSingularSubcomplexMap (Subtype.val : W → C)
        (contMDiff_subtypeVal (I := 𝓘(ℝ, E')))) (ModuleCat.of ℤ (ULift.{0} ℤ))).f 2 ≫ κ.f 2 ≫
          integrationCochain (R := ℤ) ψ = 0 := by
      rw [SSet.chainComplexMap_f_chainComplexFunctor_map_app_f_assoc,
        integrationCochain_naturality, h0, integrationCochain_zero, Limits.comp_zero]
    simpa using ConcreteCategory.congr_hom h c
  have hι : (integrationCochain (R := ℤ) ψ).hom ((κ.f 2).hom
      (((smoothSingularSubcomplex 𝓘(ℝ, E') C : SSet).ιChainComplex
        (R := ModuleCat.of ℤ (ULift.{0} ℤ)) σ).hom 1)) = σ.integral ψ := by
    rw [← ConcreteCategory.comp_apply _ (κ.f 2), SSet.ιChainComplex_chainComplexFunctor_map_app_f,
      ConcreteCategory.comp_apply, integrationCochain_ιChainComplex, uliftIntIso_hom_apply,
      ULift.one_down, one_smul]
  rw [← sub_add_cancel ((((smoothSingularSubcomplex 𝓘(ℝ, E') C : SSet).chainComplex
      (ModuleCat.of ℤ (ULift.{0} ℤ))).iCycles 2).hom z) (((smoothSingularSubcomplex 𝓘(ℝ, E') C :
        SSet).ιChainComplex (R := ModuleCat.of ℤ (ULift.{0} ℤ)) σ).hom 1),
    hbc, map_add, map_add, map_add, map_add, hd, hc, hι,
    σ.integral_eq_integralTopForm o hU hgσ hg ho
      (hψ.integrableTopForm hK (finBasisOfFinrankEq ℝ E' hE'))
      (hsupp.trans (image_mono interior_subset))]
  simp only [add_zero, zero_add]

/-- **Integration against the fundamental class of a surface.** For a closed surface `C`, oriented
by `o`, and a closed smooth two-form `φ`, the integral of `φ` over `C` is the period of `φ` on the
fundamental class `[C]` of the homological orientation of `-o`, read with coefficients `ℤ`:
`∫_C φ = ⟨[φ], [C]⟩`. Tau Ceti's homological orientation of `o` selects minus the classes of
positively oriented simplices, hence the sign. -/
theorem integralTopForm_eq_closedFormHomologyPeriod (hE' : finrank ℝ E' = 2)
    (o : Manifold.Orientation 𝓘(ℝ, E') C (Fin 2)) (φ : closedForms 𝓘(ℝ, E') C 2) :
    integralTopForm o φ.val.val = closedFormHomologyPeriod φ
      ((uliftIntHomologyIso (TopCat.of C) 2).hom.hom
        (((-o).toHomologicalOrientation hE').fundamentalClass hE')) := by
  -- A smooth cycle `z` with coefficients `ULift ℤ` representing the fundamental class.
  obtain ⟨z, hz⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ 2
    ((smoothSingularHomologyIso 𝓘(ℝ, E') C (ModuleCat.of ℤ (ULift.{0} ℤ)) 2).inv.hom
      (((-o).toHomologicalOrientation hE').fundamentalClass hE'))
  have hz' : (smoothSingularHomologyIso 𝓘(ℝ, E') C (ModuleCat.of ℤ (ULift.{0} ℤ)) 2).hom.hom
      ((((smoothSingularSubcomplex 𝓘(ℝ, E') C : SSet).chainComplex
        (ModuleCat.of ℤ (ULift.{0} ℤ))).homologyπ 2).hom z) =
      ((-o).toHomologicalOrientation hE').fundamentalClass hE' := by
    rw [hz, Iso.inv_hom_id_apply]
  -- Read with coefficients `ℤ`, the class of `z` is that of the integral cycle `κ z`, over which
  -- the period of `φ` is the integral of `φ`.
  set κ := ((SSet.chainComplexFunctor (ModuleCat.{0} ℤ)).map uliftIntIso.hom).app
    (smoothSingularSubcomplex 𝓘(ℝ, E') C : SSet)
  have hκ : (smoothSingularHomologyIso 𝓘(ℝ, E') C (ModuleCat.of ℤ (ULift.{0} ℤ)) 2).hom ≫
      (uliftIntHomologyIso (TopCat.of C) 2).hom =
        HomologicalComplex.homologyMap κ 2 ≫
          (smoothSingularHomologyIso 𝓘(ℝ, E') C (ModuleCat.of ℤ ℤ) 2).hom := by
    rw [uliftIntHomologyIso_hom]
    -- The change of coefficients on singular homology is, by definition of
    -- `singularHomologyFunctor`, the map on homology of the change of coefficients on the chains
    -- of `TopCat.toSSet`.
    exact smoothSingularHomologyIso_hom_comp_homologyMap_coefficients _ C uliftIntIso.hom 2
  have h := ConcreteCategory.congr_hom hκ
    ((((smoothSingularSubcomplex 𝓘(ℝ, E') C : SSet).chainComplex
      (ModuleCat.of ℤ (ULift.{0} ℤ))).homologyπ 2).hom z)
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hz',
    ← ConcreteCategory.comp_apply _ (HomologicalComplex.homologyMap κ 2),
    HomologicalComplex.homologyπ_naturality, ConcreteCategory.comp_apply,
    smoothSingularHomologyIso_hom _ C (ModuleCat.of ℤ ℤ)] at h
  rw [h, closedFormHomologyPeriod_homologyMap_ι_homologyπ, ← ConcreteCategory.comp_apply _
    (((smoothSingularSubcomplex 𝓘(ℝ, E') C : SSet).chainComplex (ModuleCat.of ℤ ℤ)).iCycles 2),
    HomologicalComplex.cyclesMap_i, ConcreteCategory.comp_apply]
  -- A finite cover of `C` by images of interiors of positively oriented simplices.
  choose U g hU hgs hg ho hx using
    exists_isOpenEmbedding_isOrientationPreservingAt_fullSimplex o
  have hV (x : C) : IsOpen (g x '' interior (fullSimplex 2)) := by
    have e : g x '' interior (fullSimplex 2) =
        (g x ∘ ((↑) : U x → EuclideanSpace ℝ (Fin 2))) '' ((↑) ⁻¹' interior (fullSimplex 2)) := by
      ext y
      constructor
      · rintro ⟨p, hp, rfl⟩
        exact ⟨⟨p, hU x (interior_subset hp)⟩, hp, rfl⟩
      · rintro ⟨p, hp, rfl⟩
        exact ⟨p, hp, rfl⟩
    rw [e]
    exact (hg x).isOpenMap _ (isOpen_interior.preimage continuous_subtypeVal)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ g x '' interior (fullSimplex 2))
    hV fun x _ ↦ mem_iUnion.2 ⟨x, hx x⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, E') isClosed_univ
    (fun x : t ↦ g x '' interior (fullSimplex 2)) (fun x ↦ hV x) fun y hy ↦ by simpa using ht hy
  -- Split `φ` along a subordinate partition of unity; both sides are additive.
  let ψ : t → RoughForm 𝓘(ℝ, E') C ℝ 2 := fun i y ↦ ρ i y • φ.val.val y
  have hφψ : φ.val.val = ∑ i, ψ i := by
    funext y
    rw [Finset.sum_apply, ← Finset.sum_smul, ← finsum_eq_sum_of_fintype, ρ.sum_eq_one (mem_univ y),
      one_smul]
  have hψ (i : t) : IsSmoothForm 𝓘(ℝ, E') 1 (ψ i) :=
    (φ.val.isSmoothForm.of_le (by simp)).fun_smul ((ρ i).contMDiff.of_le (by simp))
  have hsupp (i : t) : _root_.tsupport (α := E' [⋀^Fin 2]→L[ℝ] ℝ) (ψ i) ⊆
      g i '' interior (fullSimplex 2) :=
    (tsupport_smul_subset_left (α := E' [⋀^Fin 2]→L[ℝ] ℝ) (ρ i) φ.val.val).trans (hρ i)
  have hsum (s : Finset t) :
      integrationCochain (R := ℤ) (∑ i ∈ s, ψ i) = ∑ i ∈ s, integrationCochain (ψ i) := by
    classical
    induction s using Finset.induction_on with
    | empty => rw [Finset.sum_empty, Finset.sum_empty, integrationCochain_zero]
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, integrationCochain_add
        ((hψ i).of_le (by simp)) (IsSmoothForm.sum _ _ fun j _ ↦ (hψ j).of_le (by simp)), ih]
  rw [hφψ, integralTopForm_sum o ψ Finset.univ fun i _ ↦ (hψ i).integrableTopForm
      (isClosed_tsupport _).isCompact (finBasisOfFinrankEq ℝ E' hE'), hsum, ModuleCat.hom_sum,
    LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun i _ ↦ (integrationCochain_iCycles_eq_integralTopForm hE' o z
    hz' (hU i) (hgs i) (hg i) (ho i) (hψ i) (hsupp i)).symm

/-- **Integration of a pulled back closed two-form over a surface.** For a closed surface `C`,
oriented by `o`, a closed two-form `φ` on a manifold `M` and a smooth map `u : C → M`, the integral
of `u^* φ` over `C` is the period of `φ` on the image under `u` of the fundamental class of the
homological orientation of `-o`, read with coefficients `ℤ`: `∫_C u^* φ = ⟨[φ], u_* [C]⟩`. -/
theorem integralTopForm_mpullback_eq_closedFormHomologyPeriod {E H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] (hE' : finrank ℝ E' = 2)
    (o : Manifold.Orientation 𝓘(ℝ, E') C (Fin 2)) (φ : closedForms I M 2) {u : C → M}
    (hu : ContMDiff 𝓘(ℝ, E') I ∞ u) :
    integralTopForm o (mpullback 𝓘(ℝ, E') I u φ.val.val) =
      closedFormHomologyPeriod φ ((uliftIntHomologyIso (TopCat.of M) 2).hom.hom
        (((-o).toHomologicalOrientation hE').mapFundamentalClass hE' ⟨u, hu.continuous⟩)) := by
  have h := o.integralTopForm_eq_closedFormHomologyPeriod hE' (closedForms.mpullback u hu 2 φ)
  rw [closedForms.coe_mpullback, SmoothForm.coe_mpullback] at h
  refine h.trans ((closedFormHomologyPeriod_mpullback hu φ _).trans ?_)
  rw [ContinuousMap.singularHomologyMap_eq_homologyMap_toSSet_map,
    HomologicalOrientation.mapFundamentalClass_def]
  -- `singularHomologyFunctor` is by definition the simplicial homology of `TopCat.toSSet`, so its
  -- map on homology is `SSet.homologyMap` of the induced map of simplicial sets.
  exact congrArg (closedFormHomologyPeriod φ) (ConcreteCategory.congr_hom
    (homologyMap_comp_uliftIntHomologyIso_hom (TopCat.ofHom ⟨u, hu.continuous⟩) 2) _).symm

end TauCeti.Manifold.Orientation

end
