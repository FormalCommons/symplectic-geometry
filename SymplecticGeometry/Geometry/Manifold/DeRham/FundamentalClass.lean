/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.Orientation.Simplex
public import SymplecticGeometry.Geometry.Manifold.SmoothSingular.SingularPeriod
public import TauCeti.Geometry.Manifold.Orientation.Euclidean
public import TauCeti.Geometry.Manifold.SmoothSingular.TopForm
import Mathlib.Geometry.Manifold.PartitionOfUnity
import SymplecticGeometry.Geometry.Manifold.Orientation.Preserving
import SymplecticGeometry.Geometry.Manifold.SmoothSingular.RelativeCycle
import TauCeti.Analysis.InnerProductSpace.Reflection
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Regularity
import TauCeti.Geometry.Manifold.Orientation.Pullback
import TauCeti.Topology.OpenPartialHomeomorph.Constructions

/-!
# Integration against the fundamental class of a surface

Let `C` be a closed surface: a compact Hausdorff smooth manifold modelled on a real normed space
`E'` of dimension two, oriented by `o`. For a closed smooth two-form `φ` on `C` (every two-form is
closed, by `TauCeti.mextDeriv_eq_zero_of_finrank_le`), the integral of `φ` over `C` is the period
of its de Rham class on the fundamental class:

`∫_C φ = ⟨[φ], [C]⟩`

(`TauCeti.Manifold.Orientation.integralTopForm_eq_singularHomologyPeriod`). The fundamental class
is that of the homological orientation of `-o`: Tau Ceti's homological orientation of a smooth
orientation selects at each point minus the class of a positively oriented simplex
(`TopPair.relClass_fullSimplex_eq_neg_toHomologicalOrientation`), and it is the classes of
positively oriented simplices that integration sees.

## Proof

The proof is local.

* Every point lies in the image of the interior of the standard simplex `Δ²` under a map
  `g : ℝ² → C` that is, on a neighbourhood of `Δ²`, a smooth open embedding preserving orientation
  (`TauCeti.Manifold.Orientation.exists_isOpenEmbedding_isOrientationPreservingAt_fullSimplex`):
  a chart, a linear equivalence of `ℝ²` with `E'` matching the orientations at the point, and a
  small copy of `Δ²` around it. As in the proof of Tau Ceti's
  `exists_isOpenEmbedding_isLocalDiffeomorph_isOrientationPreservingAt` (namespace
  `TauCeti.Manifold.Orientation`), a linear equivalence that reverses orientation is
  precomposed with a reflection.
* Let `z` be a smooth integral cycle representing the fundamental class (smoothing), and `ψ` a
  form supported in a compact `K ⊆ g(interior Δ²)`. The image of `z` in `H₂(C, C ∖ K)` is the
  fundamental class along `K`, and so is the class of the simplex `σ` given by `g`
  (`TauCeti.SmoothSimplex.relativeClass_eq_fundamentalClassOn`). Hence `z - σ = ∂ b + c` with `b`
  smooth and `c` a smooth chain of `C ∖ K`
  (`TauCeti.exists_smoothSingular_sub_eq_d_add_of_relClass`). Stokes' theorem and the
  vanishing of `ψ` on `C ∖ K` give `∫_z ψ = ∫_σ ψ`, which is `∫_C ψ` by
  `TauCeti.SmoothSimplex.integral_eq_integralTopForm`
  (`TauCeti.Manifold.Orientation.intIntegrationCochain_iCycles_eq_integralTopForm`).
* A smooth partition of unity subordinate to finitely many such images splits `φ`, and both sides
  are additive.

## Main results

* `TauCeti.Manifold.Orientation.exists_isOpenEmbedding_isOrientationPreservingAt_fullSimplex`:
  positively oriented simplices around every point of an oriented manifold.
* `TauCeti.Manifold.Orientation.intIntegrationCochain_iCycles_eq_integralTopForm`: the local
  statement, for a form supported inside one positively oriented simplex.
* `TauCeti.Manifold.Orientation.integralTopForm_eq_singularHomologyPeriod`: `∫_C φ = ⟨[φ], [C]⟩`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapters 16 and 18.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §2.1 and §3.3.
-/

public section

noncomputable section

open CategoryTheory Set Topology TopologicalSpace Module Filter Simplicial
open scoped Manifold ContDiff

namespace TauCeti.Manifold.Orientation

section Simplex

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {C : Type*} [TopologicalSpace C] [ChartedSpace E' C] [IsManifold 𝓘(ℝ, E') ∞ C]
  {p : ℕ} [NeZero p]

/-- In the chart at `x`, some linear equivalence `L : ℝᵖ ≃ E'` makes `w ↦ c⁻¹ (c x + L w)`
preserve orientation at `0`. -/
private lemma exists_isOrientationPreservingAt_chartAt_symm (hE' : finrank ℝ E' = p)
    (o : Manifold.Orientation 𝓘(ℝ, E') C (Fin p)) (x : C) :
    ∃ L : EuclideanSpace ℝ (Fin p) ≃L[ℝ] E', IsOrientationPreservingAt (euclideanSpace p) o
      (fun w ↦ (chartAt E' x).symm (chartAt E' x x + L w)) 0 := by
  set c := chartAt E' x
  have hx0 (L : EuclideanSpace ℝ (Fin p) ≃L[ℝ] E') : c x + L 0 ∈ c.target := by
    simpa using c.map_source (mem_chart_source E' x)
  -- The derivative of `w ↦ c⁻¹ (c x + L w)` at `0` is invertible.
  have hinv (L : EuclideanSpace ℝ (Fin p) ≃L[ℝ] E') :
      (mfderiv (𝓡 p) 𝓘(ℝ, E') (fun w ↦ c.symm (c x + L w)) 0).IsInvertible := by
    have hT : HasMFDerivAt (𝓡 p) 𝓘(ℝ, E') (fun w ↦ c x + L w) 0
        (L : EuclideanSpace ℝ (Fin p) →L[ℝ] E') :=
      ((L : EuclideanSpace ℝ (Fin p) →L[ℝ] E').hasFDerivAt.const_add (c x)).hasMFDerivAt
    have h := (mdifferentiableAt_atlas_symm (chart_mem_atlas E' x) (hx0 L)).hasMFDerivAt.comp 0 hT
    rw [Function.comp_def] at h
    rw [h.mfderiv]
    have hc : (mfderiv 𝓘(ℝ, E') 𝓘(ℝ, E') c.symm (c x + L 0)).IsInvertible :=
      ⟨(mdifferentiable_chart (I := 𝓘(ℝ, E')) x).symm.mfderiv (e := c.symm) (hx0 L), rfl⟩
    exact hc.comp ⟨L, rfl⟩
  let L₀ : EuclideanSpace ℝ (Fin p) ≃L[ℝ] E' := ContinuousLinearEquiv.ofFinrankEq (by simp [hE'])
  obtain ⟨D, hD⟩ := hinv L₀
  rcases isOrientationPreservingAt_or_isOrientationReversingAt _ o _ 0 D hD with h | h
  · exact ⟨L₀, h⟩
  -- If `L₀` reverses orientation, precompose it with a reflection.
  obtain ⟨R, hR⟩ := TauCeti.exists_det_neg (F := EuclideanSpace ℝ (Fin p))
  let R' : EuclideanSpace ℝ (Fin p) ≃L[ℝ] EuclideanSpace ℝ (Fin p) := R.toContinuousLinearEquiv
  have h' : IsOrientationReversingAt (euclideanSpace p) o (fun w ↦ c.symm (c x + L₀ w)) (R' 0) := by
    rw [map_zero]
    exact h
  exact ⟨R'.trans L₀, h'.comp (isOrientationReversingAt_of_det_neg (euclideanSpace p) R' hR 0)⟩

/-- **Positively oriented simplices.** Every point `x` of a smooth manifold of positive dimension
`p`, oriented by `o`, lies in the image of the interior of the standard simplex `Δᵖ` under a map
`g : ℝᵖ → C` which, on an open neighbourhood `U` of `Δᵖ`, is smooth, an open embedding, and
orientation preserving from the standard orientation of `ℝᵖ` to `o`. -/
theorem exists_isOpenEmbedding_isOrientationPreservingAt_fullSimplex (hE' : finrank ℝ E' = p)
    (o : Manifold.Orientation 𝓘(ℝ, E') C (Fin p)) (x : C) :
    ∃ (U : Opens (EuclideanSpace ℝ (Fin p))) (g : EuclideanSpace ℝ (Fin p) → C),
      fullSimplex p ⊆ U ∧ ContMDiffOn (𝓡 p) 𝓘(ℝ, E') ∞ g U ∧
      IsOpenEmbedding (g ∘ ((↑) : U → EuclideanSpace ℝ (Fin p))) ∧
      (∀ y ∈ U, IsOrientationPreservingAt (euclideanSpace p) o g y) ∧
      x ∈ g '' interior (fullSimplex p) := by
  set c := chartAt E' x
  obtain ⟨L, hL⟩ := exists_isOrientationPreservingAt_chartAt_symm hE' o x
  set h : EuclideanSpace ℝ (Fin p) → C := fun w ↦ c.symm (c x + L w)
  have hT : ContMDiff (𝓡 p) 𝓘(ℝ, E') ∞ (fun w : EuclideanSpace ℝ (Fin p) ↦ c x + L w) :=
    (contDiff_const.add L.contDiff).contMDiff
  have hsm (w : EuclideanSpace ℝ (Fin p)) (hw : c x + L w ∈ c.target) :
      ContMDiffAt (𝓡 p) 𝓘(ℝ, E') ∞ h w :=
    ((contMDiffOn_chart_symm (x := x)).contMDiffAt (c.open_target.mem_nhds hw)).comp w (hT w)
  have hx0 : c x + L 0 ∈ c.target := by simpa using c.map_source (mem_chart_source E' x)
  -- On a ball about `0`, `h` lands in the chart target and preserves orientation.
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1
    (((hT.continuous.tendsto 0).eventually (c.open_target.mem_nhds hx0)).and
      (eventually_isOrientationPreservingAt ((hsm 0 hx0).of_le (by simp)) hL))
  -- Shrink `Δᵖ` into that ball by `A y = ε • (y - p₀)` around an interior point `p₀`.
  obtain ⟨p₀, hp₀⟩ := nonempty_interior_fullSimplex p
  obtain ⟨R, hR, hsub⟩ := (isCompact_fullSimplex p).isBounded.subset_ball_lt 0 p₀
  set ε := r / R
  have hε : 0 < ε := div_pos hr hR
  set A : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p) := fun y ↦ ε • (y - p₀) with hAdef
  have hA (y) (hy : y ∈ Metric.ball p₀ R) : A y ∈ Metric.ball 0 r := by
    rw [mem_ball_zero_iff, hAdef, norm_smul, Real.norm_of_nonneg hε.le]
    rw [Metric.mem_ball, dist_eq_norm] at hy
    calc ε * ‖y - p₀‖ < ε * R := by gcongr
      _ = r := div_mul_cancel₀ r hR.ne'
  have hAd (y : EuclideanSpace ℝ (Fin p)) :
      HasFDerivAt A (ε • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin p))) y :=
    ((hasFDerivAt_id y).sub_const p₀).const_smul ε
  let T : EuclideanSpace ℝ (Fin p) ≃ₜ E' := (Homeomorph.subRight p₀).trans
    ((Homeomorph.smulOfNeZero ε hε.ne').trans (L.toHomeomorph.trans (Homeomorph.addLeft (c x))))
  refine ⟨⟨Metric.ball p₀ R, Metric.isOpen_ball⟩, h ∘ A, hsub, fun y hy ↦ ?_, ?_, fun y hy ↦ ?_,
    ⟨p₀, hp₀, by simpa [A, h] using c.left_inv (mem_chart_source E' x)⟩⟩
  · exact ((hsm _ (hball _ (hA y hy)).1).comp y
      ((contDiff_id.sub contDiff_const).const_smul ε).contMDiff.contMDiffAt).contMDiffWithinAt
  · -- On the ball, `h ∘ A` is the chart inverse after the affine homeomorphism `T`.
    refine c.symm.isOpenEmbedding_comp (g := T ∘ ((↑) : Metric.ball p₀ R → _))
      (T.isOpenEmbedding.comp Metric.isOpen_ball.isOpenEmbedding_subtypeVal) ?_
    rintro _ ⟨y, rfl⟩
    exact (hball _ (hA y y.prop)).1
  · refine (hball _ (hA y hy)).2.comp (isOrientationPreservingAt_of_det_fderiv_pos _ ?_)
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
open embedding preserving orientation, and let `z` be a smooth integral cycle whose class is the
fundamental class of the homological orientation of `-o`. Then a `C¹` two-form `ψ` supported in
`g(interior Δ²)` integrates over `z` to its integral over `C`. -/
theorem intIntegrationCochain_iCycles_eq_integralTopForm (hE' : finrank ℝ E' = 2)
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
    (intIntegrationCochain ψ).hom ((((smoothSingularSubcomplex 𝓘(ℝ, E') C : SSet).chainComplex
      (ModuleCat.of ℤ (ULift.{0} ℤ))).iCycles 2).hom z) = integralTopForm o ψ := by
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
  have hd : (intIntegrationCochain ψ).hom
      (((smoothSingularSubcomplex 𝓘(ℝ, E') C : SSet).chainComplex
      (ModuleCat.of ℤ (ULift.{0} ℤ))).d 3 2 b) = 0 := by
    have h := congrArg (fun f ↦ ModuleCat.Hom.hom f b) (d_comp_intIntegrationCochain (p := 2) hψ)
    simp only [mextDeriv_eq_zero_of_finrank_le hE'.le, intIntegrationCochain_zero] at h
    exact h
  have hc : (intIntegrationCochain ψ).hom ((SSet.chainComplexMap (smoothSingularSubcomplexMap
      (Subtype.val : W → C) (contMDiff_subtypeVal (I := 𝓘(ℝ, E'))))
        (ModuleCat.of ℤ (ULift.{0} ℤ))).f 2 c) = 0 := by
    have h := congrArg (fun f ↦ ModuleCat.Hom.hom f c)
      (intIntegrationCochain_naturality (contMDiff_subtypeVal (I := 𝓘(ℝ, E')) (U := W)) ψ)
    have h0 : mpullback 𝓘(ℝ, E') 𝓘(ℝ, E') (Subtype.val : W → C) ψ = 0 :=
      funext fun y ↦ mpullback_apply_eq_zero (image_eq_zero_of_notMem_tsupport y.prop)
    simp only [h0, intIntegrationCochain_zero] at h
    exact h
  rw [← sub_add_cancel ((((smoothSingularSubcomplex 𝓘(ℝ, E') C : SSet).chainComplex
      (ModuleCat.of ℤ (ULift.{0} ℤ))).iCycles 2).hom z) (((smoothSingularSubcomplex 𝓘(ℝ, E') C :
        SSet).ιChainComplex (R := ModuleCat.of ℤ (ULift.{0} ℤ)) σ).hom 1),
    map_add, hbc, map_add, hd, hc, intIntegrationCochain_ιChainComplex,
    σ.integral_eq_integralTopForm o hU hgσ hg ho
      (hψ.integrableTopForm hK (finBasisOfFinrankEq ℝ E' hE'))
      (hsupp.trans (image_mono interior_subset))]
  simp only [ULift.one_down, one_smul, add_zero]
  -- The sum is taken in `ℝ` with scalars restricted to `ℤ`.
  exact zero_add _

/-- **Integration against the fundamental class of a surface.** For a closed surface `C`, oriented
by `o`, and a closed smooth two-form `φ`, the integral of `φ` over `C` is the period of its de Rham
class on the fundamental class `[C]` of the homological orientation of `-o`:
`∫_C φ = ⟨[φ], [C]⟩`. Tau Ceti's homological orientation of `o` selects minus the classes of
positively oriented simplices, hence the sign. -/
theorem integralTopForm_eq_singularHomologyPeriod (hE' : finrank ℝ E' = 2)
    (o : Manifold.Orientation 𝓘(ℝ, E') C (Fin 2)) (φ : closedForms 𝓘(ℝ, E') C 2) :
    integralTopForm o φ.val.val = deRhamCohomology.singularHomologyPeriod
      (deRhamCohomology.mk 𝓘(ℝ, E') 2 φ)
      (((-o).toHomologicalOrientation hE').fundamentalClass hE') := by
  -- A smooth integral cycle `z` representing the fundamental class.
  obtain ⟨z, hz⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ 2
    ((smoothSingularHomologyIso 𝓘(ℝ, E') C (ModuleCat.of ℤ (ULift.{0} ℤ)) 2).inv.hom
      (((-o).toHomologicalOrientation hE').fundamentalClass hE'))
  have hz' : (smoothSingularHomologyIso 𝓘(ℝ, E') C (ModuleCat.of ℤ (ULift.{0} ℤ)) 2).hom.hom
      ((((smoothSingularSubcomplex 𝓘(ℝ, E') C : SSet).chainComplex
        (ModuleCat.of ℤ (ULift.{0} ℤ))).homologyπ 2).hom z) =
      ((-o).toHomologicalOrientation hE').fundamentalClass hE' := by
    rw [hz, Iso.inv_hom_id_apply]
  rw [← hz', deRhamCohomology.singularHomologyPeriod_mk_apply_smoothCycle]
  -- A finite cover of `C` by images of interiors of positively oriented simplices.
  choose U g hU hgs hg ho hx using
    exists_isOpenEmbedding_isOrientationPreservingAt_fullSimplex hE' o
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
  rw [hφψ, integralTopForm_sum o ψ Finset.univ fun i _ ↦ (hψ i).integrableTopForm
      (isClosed_tsupport _).isCompact (finBasisOfFinrankEq ℝ E' hE'),
    intIntegrationCochain_sum_apply _ _ fun i _ ↦ (hψ i).of_le (by simp)]
  exact Finset.sum_congr rfl fun i _ ↦ (intIntegrationCochain_iCycles_eq_integralTopForm hE' o z
    hz' (hU i) (hgs i) (hg i) (ho i) (hψ i) (hsupp i)).symm

end TauCeti.Manifold.Orientation

end
