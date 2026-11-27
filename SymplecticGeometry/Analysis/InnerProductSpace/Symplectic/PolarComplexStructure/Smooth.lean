/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Analysis.InnerProductSpace.Symplectic.PolarComplexStructure.Basic
public import SymplecticGeometry.Topology.Algebra.Module.SymplecticForms
public import TauCeti.Analysis.InnerProductSpace.Positive.MetricChange.Smooth
public import TauCeti.Geometry.Symplectic.AlmostComplex.Topology
import TauCeti.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Sqrt.Analytic
import SymplecticGeometry.Analysis.InnerProductSpace.LinearMap

/-!
# Smoothness of `J_{g,ω}`

Let `W` be a finite-dimensional real inner product space. This file writes the complex structure
`J_{g,ω}` of `SymplecticGeometry.metricPolarComplexStructure` as an explicit formula in a pair
`(g, s)` of continuous bilinear forms on `W`, and shows that the formula is smooth on an open set
of pairs that contains every pair of an inner product and a symplectic form.

The formula, `SymplecticGeometry.metricPolarFormula g s`, takes the symmetric part `g'` of `g` and
the skew part `s'` of `s`, and evaluates Tau Ceti's coordinate expression for the polar complex
structure, `R A (√(-A²))⁻¹ √(g'♯)` with `R = (g'♯)^(-1/2)` and `A = R s'♯ R`. Outside the domain
the junk values of `Ring.inverse`, `CFC.sqrt` and the metric change transport make it a total
function, without a case split. The inner product of `W` is only an auxiliary choice: on inner
products and symplectic forms the formula is `J_{g,ω}`, which does not depend on it.

## Main definitions

* `SymplecticGeometry.polarDomain V`: the pairs `(g, s)` such that `g` is positive on nonzero
  vectors and the skew part of `s` is nondegenerate.
* `SymplecticGeometry.metricPolarFormula g s`: the explicit formula.

## Main results

* `SymplecticGeometry.isOpen_polarDomain`: the domain is open.
* `SymplecticGeometry.contDiffOn_metricPolarFormula`: the formula is smooth on the domain, of every
  order.
* `SymplecticGeometry.metricPolarFormula_symmetrizeBilinear_skewSymmetrizeBilinear`: the formula
  only depends on the symmetric part of `g` and the skew part of `s`.
* `SymplecticGeometry.metricPolarFormula_conj`: naturality of the formula on the domain under linear
  isomorphisms.
* `SymplecticGeometry.mem_polarDomain`: every inner product and symplectic form lie in the
  domain.
* `SymplecticGeometry.metricPolarFormula_eq`: on them, the formula is `J_{g,ω}`.
* `SymplecticGeometry.metricPolarFormula_eq_of_mem`: on the domain, the formula is `J_{g',ω'}`
  for the symmetric part `g'` of `g` and the skew part `ω'` of `s`.
* `SymplecticGeometry.continuous_metricPolarComplexStructure`: `J_{g,ω}` depends continuously
  on `(g, ω)`, and `Continuous.metricPolarComplexStructure` is its form for continuous
  families.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Proposition 2.5.6

## Implementation notes

The proof of `SymplecticGeometry.contDiffOn_metricPolarFormula` adapts the argument of Tau Ceti's
private lemma `contMDiffAt_metricChangeTransport_mul_mul_sqrt`
(`TauCeti/Geometry/Symplectic/Manifold/AlmostComplex/Polar.lean`) from smoothness at a point of a
manifold to smoothness on an open set of pairs of forms: the same factors `R` and `A`, and the
same final product. Where Tau Ceti inverts the square root of `-A²` with
`contDiffAt_ringInverse` at the unit that `CFC.isUnit_sqrt_iff` gives, this proof uses Tau Ceti's
`CFC.analyticOn_ringInverse_sqrt`, the analyticity of the inverse square root on strictly
positive elements.
-/

public section

open InnerProductSpace ContinuousLinearMap
open scoped RealInnerProductSpace

local postfix:1024 "♯" => continuousLinearMapOfBilin (𝕜 := ℝ)

namespace SymplecticGeometry

open TauCeti Module

section Domain

variable (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The domain of `SymplecticGeometry.metricPolarFormula`: the pairs `(g, s)` of continuous bilinear
forms on `V` such that `g` is positive on nonzero vectors and `s - sᵀ`, twice the skew part of `s`,
is nondegenerate. -/
def polarDomain : Set ((V →L[ℝ] V →L[ℝ] ℝ) × (V →L[ℝ] V →L[ℝ] ℝ)) :=
  {p | (∀ v, v ≠ 0 → 0 < p.1 v v) ∧ (p.2 - p.2.flip).toBilinForm.Nondegenerate}

variable {V}

/-- Membership in `SymplecticGeometry.polarDomain`: positivity of the first form on nonzero vectors
and nondegeneracy of the skew part of the second. -/
@[simp]
theorem mem_polarDomain_iff {p : (V →L[ℝ] V →L[ℝ] ℝ) × (V →L[ℝ] V →L[ℝ] ℝ)} :
    p ∈ polarDomain V ↔
      (∀ v, v ≠ 0 → 0 < p.1 v v) ∧ (p.2 - p.2.flip).toBilinForm.Nondegenerate :=
  Iff.rfl

/-- On the domain, the skew part of the second form is nondegenerate. -/
theorem nondegenerate_toBilinForm_of_mem_polarDomain {g s : V →L[ℝ] V →L[ℝ] ℝ}
    (h : (g, s) ∈ polarDomain V) : (skewSymmetrizeBilinear s).toBilinForm.Nondegenerate :=
  (nondegenerate_toBilinForm_skewSymmetrizeBilinear_iff s).2 (mem_polarDomain_iff.1 h).2

variable (V) in
/-- In finite dimension, the domain of `SymplecticGeometry.metricPolarFormula` is open. -/
theorem isOpen_polarDomain [FiniteDimensional ℝ V] : IsOpen (polarDomain V) :=
  (isOpen_setOf_forall_bilinear_apply_self_pos.preimage continuous_fst).inter
    (isOpen_setOfPred_nondegenerate_toBilinForm_sub_flip.preimage continuous_snd)

end Domain

section Formula

variable {W W' : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [NormedAddCommGroup W'] [InnerProductSpace ℝ W'] [FiniteDimensional ℝ W']

/-- The explicit formula for `J_{g,ω}`. With the symmetric part `g'` of `g`, the skew part `s'`
of `s`, `R = (g'♯)^(-1/2)` and `A = R s'♯ R`, it is `R A (√(-A²))⁻¹ √(g'♯)`. -/
noncomputable def metricPolarFormula (g s : W →L[ℝ] W →L[ℝ] ℝ) : W →L[ℝ] W :=
  let g' := (symmetrizeBilinear g).val
  let A := g'.metricChangeTransport * (skewSymmetrizeBilinear s)♯ * g'.metricChangeTransport
  g'.metricChangeTransport * (A * Ring.inverse (CFC.sqrt (-(A * A)))) * CFC.sqrt g'♯

theorem metricPolarFormula_def (g s : W →L[ℝ] W →L[ℝ] ℝ) :
    metricPolarFormula g s =
      let g' := (symmetrizeBilinear g).val
      let A := g'.metricChangeTransport * (skewSymmetrizeBilinear s)♯ * g'.metricChangeTransport
      g'.metricChangeTransport * (A * Ring.inverse (CFC.sqrt (-(A * A)))) * CFC.sqrt g'♯ :=
  (rfl)

/-- The formula is smooth, of every order including analyticity, on the domain
`SymplecticGeometry.polarDomain W`. -/
theorem contDiffOn_metricPolarFormula {n : WithTop ℕ∞} :
    ContDiffOn ℝ n (fun p ↦ metricPolarFormula p.1 p.2) (polarDomain W) := by
  let g' (p : (W →L[ℝ] W →L[ℝ] ℝ) × (W →L[ℝ] W →L[ℝ] ℝ)) := (symmetrizeBilinear p.1).val
  let s' (p : (W →L[ℝ] W →L[ℝ] ℝ) × (W →L[ℝ] W →L[ℝ] ℝ)) := skewSymmetrizeBilinear p.2
  let R (p : (W →L[ℝ] W →L[ℝ] ℝ) × (W →L[ℝ] W →L[ℝ] ℝ)) := (g' p).metricChangeTransport
  let A (p : (W →L[ℝ] W →L[ℝ] ℝ) × (W →L[ℝ] W →L[ℝ] ℝ)) := R p * (s' p)♯ * R p
  -- On the domain, `g'♯` and `-A²` are strictly positive.
  have hgpos : ∀ p ∈ polarDomain W, IsStrictlyPositive (g' p)♯ := fun p hp ↦
    isStrictlyPositive_continuousLinearMapOfBilin_symmetrizeBilinear hp.1
  have hApos : ∀ p ∈ polarDomain W, IsStrictlyPositive (-(A p * A p)) := fun p hp ↦ by
    let ω := SymplecticForm.ofContinuousBilinearMap (s' p)
      (isAlt_toBilinForm_skewSymmetrizeBilinear p.2)
      (nondegenerate_toBilinForm_of_mem_polarDomain hp)
    exact ω.isStrictlyPositive_neg_mul_self_metricChangeTransport (hgpos p hp) fun c d ↦
      (SymplecticForm.ofContinuousBilinearMap_apply _ _ _ c d).symm
  -- Each factor is smooth on the domain.
  have hg' : ContDiffOn ℝ n g' (polarDomain W) :=
    ((symmetricBilinearMaps ℝ W ℝ).subtypeL.contDiff.comp
      ((symmetrizeBilinear (𝕜 := ℝ) (V := W) (G := ℝ)).contDiff.comp contDiff_fst)).contDiffOn.congr
      fun p _ ↦ by simp [g']
  have hR : ContDiffOn ℝ n R (polarDomain W) := hg'.metricChangeTransport hgpos
  have hQ : ContDiffOn ℝ n (fun p ↦ CFC.sqrt (g' p)♯) (polarDomain W) :=
    hg'.sqrt_continuousLinearMapOfBilin hgpos
  have hs' : ContDiff ℝ n s' := by fun_prop
  have hA : ContDiffOn ℝ n A (polarDomain W) :=
    (hR.mul ((contDiff_continuousLinearMapOfBilin.comp hs').contDiffOn)).mul hR
  have hinv : ContDiffOn ℝ n (fun p ↦ Ring.inverse (CFC.sqrt (-(A p * A p))))
      (polarDomain W) :=
    CFC.analyticOn_ringInverse_sqrt.contDiffOn_of_completeSpace.comp (hA.mul hA).neg hApos
  exact (hR.mul (hA.mul hinv)).mul hQ

/-- The formula only sees the symmetric part of its first argument and the skew part of its
second. -/
theorem metricPolarFormula_symmetrizeBilinear_skewSymmetrizeBilinear
    (g s : W →L[ℝ] W →L[ℝ] ℝ) :
    metricPolarFormula (symmetrizeBilinear g).val (skewSymmetrizeBilinear s) =
      metricPolarFormula g s := by
  simp only [metricPolarFormula_def, symmetrizeBilinear_coe,
    skewSymmetrizeBilinear_skewSymmetrizeBilinear]

end Formula

section Domain

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- Every pair of an inner product and a symplectic form lies in the domain of the formula. -/
theorem mem_polarDomain (g : innerProducts V) (ω : SymplecticForm V) :
    ((g : V →L[ℝ] V →L[ℝ] ℝ), ω.toBilinForm.toContinuousBilinearMap) ∈ polarDomain V := by
  -- The skew part of `ω` is `ω`, which is nondegenerate.
  refine ⟨(mem_innerProducts.1 g.property).2,
    (nondegenerate_toBilinForm_skewSymmetrizeBilinear_iff _).1 ?_⟩
  rw [SymplecticForm.skewSymmetrizeBilinear_toContinuousBilinearMap]
  simpa using ω.nondegenerate

end Domain

section Polar

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

/-- On an inner product `g` and a symplectic form `ω`, the formula is `J_{g,ω}`. -/
theorem metricPolarFormula_eq (g : innerProducts W) (ω : SymplecticForm W) :
    metricPolarFormula g ω.toBilinForm.toContinuousBilinearMap =
      LinearMap.toContinuousLinearMap (metricPolarComplexStructure g ω).toLinearMap := by
  have hgpos : IsStrictlyPositive (g : W →L[ℝ] W →L[ℝ] ℝ)♯ :=
    isStrictlyPositive_continuousLinearMapOfBilin_iff.2 (mem_innerProducts.1 g.property)
  -- Read `ω` through the metric change `K`, which carries the inner product of `W` to `g`.
  let K := (g : W →L[ℝ] W →L[ℝ] ℝ).metricChangeEquiv hgpos
  let ω₀ := ω.transport K.toLinearEquiv.symm
  have hg (c d : W) : (g : W →L[ℝ] W →L[ℝ] ℝ) c d = ⟪K.symm c, K.symm d⟫ := by
    rw [ContinuousLinearMap.metricChangeEquiv_symm_apply,
      ContinuousLinearMap.metricChangeEquiv_symm_apply,
      ContinuousLinearMap.inner_sqrt_apply_sqrt_apply hgpos.nonneg]
  have hs (c d : W) : ω.toBilinForm.toContinuousBilinearMap c d = ω₀ (K.symm c) (K.symm d) := by
    simp [ω₀]
  have hJ : metricPolarComplexStructure g ω =
      ω₀.polarComplexStructure.transport K.toLinearEquiv := by
    rw [← metricPolarComplexStructure_innerSL, ← metricPolarComplexStructure_transport]
    congr 1
    · ext c d
      simp only [innerProducts.transport_apply, hg, innerSL_real_apply_apply]
    · rw [SymplecticForm.transport_trans, LinearEquiv.symm_trans_self,
        SymplecticForm.transport_refl]
  have hg' : (symmetrizeBilinear (g : W →L[ℝ] W →L[ℝ] ℝ)).val = g :=
    congrArg Subtype.val (symmetrizeBilinear_coe
      ⟨g, (mem_symmetricBilinearMaps ℝ W ℝ _).2 (mem_innerProducts.1 g.property).1⟩)
  simp only [metricPolarFormula_def, hg',
    SymplecticForm.skewSymmetrizeBilinear_toContinuousBilinearMap]
  rw [← ω₀.conjContinuousAlgEquiv_toContinuousLinearMap_polarComplexStructure K hg hs, hJ]
  ext v
  simp

/-- If `g` is positive on nonzero vectors and `ω` is a symplectic form whose bilinear form is the
skew part of `s`, then the formula at `(g, s)` is `J_{g',ω}` for the symmetric part `g'` of `g`.
On the domain, such an `ω` always exists. -/
theorem metricPolarFormula_eq_of_toContinuousBilinearMap_eq {g s : W →L[ℝ] W →L[ℝ] ℝ}
    (hg : ∀ v, v ≠ 0 → 0 < g v v) {ω : SymplecticForm W}
    (hω : ω.toBilinForm.toContinuousBilinearMap = skewSymmetrizeBilinear s) :
    metricPolarFormula g s = LinearMap.toContinuousLinearMap
      (metricPolarComplexStructure ⟨_, symmetrizeBilinear_mem_innerProducts hg⟩ ω).toLinearMap := by
  rw [← metricPolarFormula_eq, hω, Subtype.coe_mk,
    metricPolarFormula_symmetrizeBilinear_skewSymmetrizeBilinear]

/-- On the domain, the formula at `(g, s)` is `J_{g',ω'}` for the symmetric part `g'` of `g` and
the symplectic form `ω'` given by the skew part of `s`. -/
theorem metricPolarFormula_eq_of_mem {g s : W →L[ℝ] W →L[ℝ] ℝ} (h : (g, s) ∈ polarDomain W) :
    metricPolarFormula g s = LinearMap.toContinuousLinearMap (metricPolarComplexStructure
      ⟨_, symmetrizeBilinear_mem_innerProducts (mem_polarDomain_iff.1 h).1⟩
      (SymplecticForm.ofContinuousBilinearMap _ (fun v ↦ by simp)
        (nondegenerate_toBilinForm_of_mem_polarDomain h))).toLinearMap :=
  metricPolarFormula_eq_of_toContinuousBilinearMap_eq (mem_polarDomain_iff.1 h).1
    (SymplecticForm.toBilinForm_toContinuousBilinearMap_ofContinuousBilinearMap _ _ _)

end Polar

section Conj

variable {W W' : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [NormedAddCommGroup W'] [InnerProductSpace ℝ W'] [FiniteDimensional ℝ W']

/-- **Naturality of the formula.** On the domain, pushing both forms forward along a linear
isomorphism `e` conjugates the formula by `e`. -/
theorem metricPolarFormula_conj (e : W ≃L[ℝ] W') {g s : W →L[ℝ] W →L[ℝ] ℝ}
    (h : (g, s) ∈ polarDomain W) :
    metricPolarFormula (e.bilinearCongr g) (e.bilinearCongr s) =
      e.conjContinuousAlgEquiv (metricPolarFormula g s) := by
  let ω := SymplecticForm.ofContinuousBilinearMap (skewSymmetrizeBilinear s)
    (isAlt_toBilinForm_skewSymmetrizeBilinear s) (nondegenerate_toBilinForm_of_mem_polarDomain h)
  have hω : ω.toBilinForm.toContinuousBilinearMap = skewSymmetrizeBilinear s :=
    SymplecticForm.toBilinForm_toContinuousBilinearMap_ofContinuousBilinearMap _ _ _
  rw [metricPolarFormula_eq_of_mem h,
    ← metricPolarFormula_symmetrizeBilinear_skewSymmetrizeBilinear,
    e.bilinearCongr_apply_eq_bilinearComp g, symmetrizeBilinear_bilinearComp,
    ← e.bilinearCongr_apply_eq_bilinearComp]
  have hs : skewSymmetrizeBilinear (e.bilinearCongr s) =
      (ω.transport e.toLinearEquiv).toBilinForm.toContinuousBilinearMap := by
    rw [e.bilinearCongr_apply_eq_bilinearComp, skewSymmetrizeBilinear_bilinearComp]
    ext u v
    simpa using (DFunLike.congr_fun (DFunLike.congr_fun hω (e.symm u)) (e.symm v)).symm
  have hg : e.bilinearCongr (symmetrizeBilinear g).val =
      (innerProducts.transport e ⟨_, symmetrizeBilinear_mem_innerProducts h.1⟩ :
        W' →L[ℝ] W' →L[ℝ] ℝ) := by
    ext u v
    simp
  rw [hs, hg, metricPolarFormula_eq, metricPolarComplexStructure_transport]
  ext v
  simp [ω]

end Conj

section Continuous

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- `J_{g,ω}` depends continuously on the inner product `g` and the symplectic form `ω`. -/
theorem continuous_metricPolarComplexStructure :
    Continuous fun p : innerProducts V × SymplecticForm V ↦
      metricPolarComplexStructure p.1 p.2 := by
  -- Carry `V` to a Euclidean space, where `J_{g,ω}` is given by the smooth formula.
  let E := EuclideanSpace ℝ (Fin (finrank ℝ V))
  let e : V ≃L[ℝ] E := .ofFinrankEq finrank_euclideanSpace_fin.symm
  have hJ (p : innerProducts V × SymplecticForm V) : metricPolarComplexStructure p.1 p.2 =
      (metricPolarComplexStructure (innerProducts.transport e p.1)
        (p.2.transport e.toLinearEquiv)).transport e.toLinearEquiv.symm := by
    rw [metricPolarComplexStructure_transport, AlmostComplexStructure.transport_trans,
      LinearEquiv.self_trans_symm, AlmostComplexStructure.transport_refl]
  have hpair : Continuous fun p : innerProducts V × SymplecticForm V ↦
      ((innerProducts.transport e p.1 : E →L[ℝ] E →L[ℝ] ℝ),
        (p.2.transport e.toLinearEquiv).toBilinForm.toContinuousBilinearMap) :=
    (continuous_subtypeVal.comp ((innerProducts.transport e).continuous.comp continuous_fst)).prodMk
      ((SymplecticForm.continuous_iff.1 (SymplecticForm.continuous_transport e)).comp
        continuous_snd)
  have hf := (contDiffOn_metricPolarFormula (W := E) (n := 0)).continuousOn.comp_continuous hpair
    fun p ↦ mem_polarDomain _ _
  rw [AlmostComplexStructure.continuous_iff]
  refine (e.symm.conjContinuousAlgEquiv.continuous.comp hf).congr fun p ↦ ?_
  simp only [Function.comp_apply]
  rw [metricPolarFormula_eq, hJ p]
  ext v
  simp


/-- `J_{g,ω}` is continuous along continuous families of inner products and symplectic forms. -/
theorem _root_.Continuous.metricPolarComplexStructure {X : Type*} [TopologicalSpace X]
    {g : X → innerProducts V} {ω : X → SymplecticForm V} (hg : Continuous g)
    (hω : Continuous ω) : Continuous fun x ↦ metricPolarComplexStructure (g x) (ω x) :=
  continuous_metricPolarComplexStructure.comp (hg.prodMk hω)

end Continuous

end SymplecticGeometry
