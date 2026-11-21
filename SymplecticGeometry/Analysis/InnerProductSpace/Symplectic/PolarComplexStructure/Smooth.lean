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

/-!
# Smoothness of `J_{g,ω}`

Let `W` be a finite-dimensional real inner product space. This file writes the complex structure
`J_{g,ω}` of `SymplecticGeometry.metricPolarComplexStructure` as an explicit formula in a pair
`(g, s)` of continuous bilinear forms on `W`, and shows that the formula is smooth on an open set
of pairs that contains every pair of an inner product and a symplectic form.

The formula, `TauCeti.metricPolarFormula g s`, takes the symmetric part `g'` of `g` and the
skew part `s'` of `s`, and evaluates Tau Ceti's coordinate expression for the polar complex
structure, `R A (√(-A²))⁻¹ √(g'♯)` with `R = (g'♯)^(-1/2)` and `A = R s'♯ R`. Outside the domain
the junk values of `Ring.inverse`, `CFC.sqrt` and the metric change transport make it a total
function, without a case split. The inner product of `W` is only an auxiliary choice: on inner
products and symplectic forms the formula is `J_{g,ω}`, which does not depend on it.

## Main definitions

* `TauCeti.polarDomain V`: the pairs `(g, s)` such that `g` is positive on nonzero vectors and
  the skew part of `s` is nondegenerate.
* `TauCeti.metricPolarFormula g s`: the explicit formula.

## Main results

* `TauCeti.isOpen_polarDomain`: the domain is open.
* `TauCeti.contDiffOn_metricPolarFormula`: the formula is smooth on the domain, of every order.
* `TauCeti.metricPolarFormula_conj`: naturality of the formula on the domain under linear
  isomorphisms.
* `SymplecticGeometry.mem_polarDomain`: every inner product and symplectic form lie in the
  domain.
* `SymplecticGeometry.metricPolarFormula_eq`: on them, the formula is `J_{g,ω}`.
* `SymplecticGeometry.continuous_metricPolarComplexStructure`: `J_{g,ω}` depends continuously
  on `(g, ω)`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Proposition 2.5.6
-/

public section

open InnerProductSpace
open scoped RealInnerProductSpace

local postfix:1024 "♯" => continuousLinearMapOfBilin (𝕜 := ℝ)

namespace TauCeti

section Domain

variable (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The domain of `TauCeti.metricPolarFormula`: the pairs `(g, s)` of continuous bilinear forms
on `V` such that `g` is positive on nonzero vectors and `s - sᵀ`, twice the skew part of `s`, is
nondegenerate. -/
def polarDomain : Set ((V →L[ℝ] V →L[ℝ] ℝ) × (V →L[ℝ] V →L[ℝ] ℝ)) :=
  {p | (∀ v, v ≠ 0 → 0 < p.1 v v) ∧ (p.2 - p.2.flip).toBilinForm.Nondegenerate}

variable {V}

/-- Membership in `TauCeti.polarDomain`: positivity of the first form on nonzero vectors and
nondegeneracy of the skew part of the second. -/
@[simp]
theorem mem_polarDomain_iff {p : (V →L[ℝ] V →L[ℝ] ℝ) × (V →L[ℝ] V →L[ℝ] ℝ)} :
    p ∈ polarDomain V ↔
      (∀ v, v ≠ 0 → 0 < p.1 v v) ∧ (p.2 - p.2.flip).toBilinForm.Nondegenerate :=
  Iff.rfl

variable (V) in
/-- In finite dimension, the domain of `TauCeti.metricPolarFormula` is open. -/
theorem isOpen_polarDomain [FiniteDimensional ℝ V] : IsOpen (polarDomain V) := by
  refine (isOpen_setOf_forall_bilinear_apply_self_pos.preimage continuous_fst).inter
    (isOpen_setOf_nondegenerate fun v w ↦ ?_)
  have h (x y : V) : Continuous fun p : (V →L[ℝ] V →L[ℝ] ℝ) × (V →L[ℝ] V →L[ℝ] ℝ) ↦ p.2 x y :=
    (continuous_snd.clm_apply continuous_const).clm_apply continuous_const
  refine ((h v w).sub (h w v)).congr fun p ↦ ?_
  simp

/-- The symmetric part of a form that is positive on nonzero vectors is an inner product. -/
private theorem symmPart_mem_innerProducts {g : V →L[ℝ] V →L[ℝ] ℝ}
    (hg : ∀ v, v ≠ 0 → 0 < g v v) :
    (2 : ℝ)⁻¹ • (g + g.flip) ∈ SymplecticGeometry.innerProducts V := by
  rw [SymplecticGeometry.mem_innerProducts]
  refine ⟨fun u v ↦ ?_, fun v hv ↦ ?_⟩
  · simp only [smul_apply, add_apply, ContinuousLinearMap.flip_apply, smul_eq_mul]
    ring
  · simp only [smul_apply, add_apply, ContinuousLinearMap.flip_apply, smul_eq_mul]
    linarith [hg v hv]

/-- The skew part of a form whose skew part is nondegenerate is a symplectic form. -/
private noncomputable def skewPartForm {s : V →L[ℝ] V →L[ℝ] ℝ}
    (hs : (s - s.flip).toBilinForm.Nondegenerate) : SymplecticForm V :=
  ⟨((2 : ℝ)⁻¹ • (s - s.flip)).toBilinForm, fun v ↦ by simp,
    ⟨fun v hv ↦ hs.1 v fun w ↦ by simpa using hv w, fun w hw ↦ hs.2 w fun v ↦ by simpa using hw v⟩⟩

private theorem skewPartForm_apply {s : V →L[ℝ] V →L[ℝ] ℝ}
    (hs : (s - s.flip).toBilinForm.Nondegenerate) (u v : V) :
    skewPartForm hs u v = ((2 : ℝ)⁻¹ • (s - s.flip)) u v :=
  (rfl)

end Domain

variable {W W' : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [NormedAddCommGroup W'] [InnerProductSpace ℝ W'] [FiniteDimensional ℝ W']

/-- The explicit formula for `J_{g,ω}`. With the symmetric part `g'` of `g`, the skew part `s'`
of `s`, `R = (g'♯)^(-1/2)` and `A = R s'♯ R`, it is `R A (√(-A²))⁻¹ √(g'♯)`. -/
noncomputable def metricPolarFormula (g s : W →L[ℝ] W →L[ℝ] ℝ) : W →L[ℝ] W :=
  let g' := (2 : ℝ)⁻¹ • (g + g.flip)
  let A := g'.metricChangeTransport * ((2 : ℝ)⁻¹ • (s - s.flip))♯ * g'.metricChangeTransport
  g'.metricChangeTransport * (A * Ring.inverse (CFC.sqrt (-(A * A)))) * CFC.sqrt g'♯

theorem metricPolarFormula_def (g s : W →L[ℝ] W →L[ℝ] ℝ) :
    metricPolarFormula g s =
      let g' := (2 : ℝ)⁻¹ • (g + g.flip)
      let A := g'.metricChangeTransport * ((2 : ℝ)⁻¹ • (s - s.flip))♯ * g'.metricChangeTransport
      g'.metricChangeTransport * (A * Ring.inverse (CFC.sqrt (-(A * A)))) * CFC.sqrt g'♯ :=
  (rfl)

/-- The formula is smooth, of every order including analyticity, on the domain
`TauCeti.polarDomain W`. -/
theorem contDiffOn_metricPolarFormula {n : WithTop ℕ∞} :
    ContDiffOn ℝ n (fun p ↦ metricPolarFormula p.1 p.2) (polarDomain W) := by
  let g' (p : (W →L[ℝ] W →L[ℝ] ℝ) × (W →L[ℝ] W →L[ℝ] ℝ)) := (2 : ℝ)⁻¹ • (p.1 + p.1.flip)
  let s' (p : (W →L[ℝ] W →L[ℝ] ℝ) × (W →L[ℝ] W →L[ℝ] ℝ)) := (2 : ℝ)⁻¹ • (p.2 - p.2.flip)
  let R (p : (W →L[ℝ] W →L[ℝ] ℝ) × (W →L[ℝ] W →L[ℝ] ℝ)) := (g' p).metricChangeTransport
  let A (p : (W →L[ℝ] W →L[ℝ] ℝ) × (W →L[ℝ] W →L[ℝ] ℝ)) := R p * (s' p)♯ * R p
  have hflip : ContDiff ℝ n
      (ContinuousLinearMap.flip : (W →L[ℝ] W →L[ℝ] ℝ) → W →L[ℝ] W →L[ℝ] ℝ) :=
    (ContinuousLinearMap.flipₗᵢ ℝ W W ℝ).toContinuousLinearEquiv.contDiff (𝕜 := ℝ) (n := n)
      (E := W →L[ℝ] W →L[ℝ] ℝ) (F := W →L[ℝ] W →L[ℝ] ℝ)
  -- On the domain, `g'♯` and `-A²` are strictly positive.
  have hgpos : ∀ p ∈ polarDomain W, IsStrictlyPositive (g' p)♯ := fun p hp ↦
    isStrictlyPositive_continuousLinearMapOfBilin_iff.2
      (SymplecticGeometry.mem_innerProducts.1 (symmPart_mem_innerProducts hp.1))
  have hApos : ∀ p ∈ polarDomain W, IsStrictlyPositive (-(A p * A p)) := fun p hp ↦
    (skewPartForm hp.2).isStrictlyPositive_neg_mul_self_metricChangeTransport (hgpos p hp)
      fun c d ↦ by rw [skewPartForm_apply]
  -- Each factor is smooth on the domain.
  have hg' : ContDiffOn ℝ n g' (polarDomain W) :=
    ((contDiff_fst.add (hflip.comp contDiff_fst)).const_smul (2 : ℝ)⁻¹).contDiffOn
  have hR : ContDiffOn ℝ n R (polarDomain W) := hg'.metricChangeTransport hgpos
  have hQ : ContDiffOn ℝ n (fun p ↦ CFC.sqrt (g' p)♯) (polarDomain W) :=
    hg'.sqrt_continuousLinearMapOfBilin hgpos
  have hA : ContDiffOn ℝ n A (polarDomain W) :=
    (hR.mul ((contDiff_continuousLinearMapOfBilin.comp
      ((contDiff_snd.sub (hflip.comp contDiff_snd)).const_smul (2 : ℝ)⁻¹)).contDiffOn)).mul hR
  have hsqrt : ContDiffOn ℝ n (fun p ↦ CFC.sqrt (-(A p * A p))) (polarDomain W) :=
    ContinuousLinearMap.contDiffOn_sqrt.comp (hA.mul hA).neg hApos
  have hinv : ContDiffOn ℝ n (fun p ↦ Ring.inverse (CFC.sqrt (-(A p * A p))))
      (polarDomain W) := by
    intro p hp
    obtain ⟨u, hu⟩ := (CFC.isUnit_sqrt_iff _ (hApos p hp).nonneg).2 (hApos p hp).isUnit
    have h := contDiffAt_ringInverse ℝ (n := n) u
    rw [hu] at h
    exact h.comp_contDiffWithinAt p (hsqrt p hp)
  exact (hR.mul (hA.mul hinv)).mul hQ

end TauCeti

namespace SymplecticGeometry

open TauCeti Module

section Domain

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The symmetric part of an inner product is the inner product itself. -/
private theorem symmPart_coe_innerProducts (g : innerProducts V) :
    (2 : ℝ)⁻¹ • ((g : V →L[ℝ] V →L[ℝ] ℝ) + (g : V →L[ℝ] V →L[ℝ] ℝ).flip) = g := by
  ext u v
  simp only [smul_apply, add_apply, ContinuousLinearMap.flip_apply, smul_eq_mul,
    (mem_innerProducts.1 g.property).1 v u]
  ring

variable [FiniteDimensional ℝ V]

/-- The skew part of a symplectic form is the form itself. -/
private theorem skewPart_toContinuousBilinearMap (ω : SymplecticForm V) :
    (2 : ℝ)⁻¹ • (ω.toBilinForm.toContinuousBilinearMap -
      ω.toBilinForm.toContinuousBilinearMap.flip) = ω.toBilinForm.toContinuousBilinearMap := by
  ext u v
  simp only [smul_apply, smul_eq_mul, LinearMap.toContinuousBilinearMap_apply]
  have := ω.neg_eq u v
  change (2 : ℝ)⁻¹ * (ω u v - ω v u) = ω u v
  linarith

/-- Every pair of an inner product and a symplectic form lies in the domain of the formula. -/
theorem mem_polarDomain (g : innerProducts V) (ω : SymplecticForm V) :
    ((g : V →L[ℝ] V →L[ℝ] ℝ), ω.toBilinForm.toContinuousBilinearMap) ∈ polarDomain V := by
  -- `ω - ωᵀ = 2 ω` is nondegenerate because `ω` is.
  have h (v w : V) : (ω.toBilinForm.toContinuousBilinearMap -
      ω.toBilinForm.toContinuousBilinearMap.flip).toBilinForm v w = 2 * ω v w := by
    simp only [ContinuousLinearMap.toBilinForm_apply, sub_apply, ContinuousLinearMap.flip_apply,
      LinearMap.toContinuousBilinearMap_apply]
    change ω v w - ω w v = 2 * ω v w
    linarith [ω.neg_eq v w]
  refine ⟨(mem_innerProducts.1 g.property).2, fun v hv ↦ ω.nondegenerate.1 v fun w ↦ ?_,
    fun w hw ↦ ω.nondegenerate.2 w fun v ↦ ?_⟩
  · simpa [h] using hv w
  · simpa [h] using hw v

end Domain

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
      simp only [innerProducts.transport_apply, hg]
      rfl
    · rw [SymplecticForm.transport_trans, LinearEquiv.symm_trans_self,
        SymplecticForm.transport_refl]
  simp only [metricPolarFormula_def, symmPart_coe_innerProducts, skewPart_toContinuousBilinearMap]
  rw [← ω₀.conjContinuousAlgEquiv_toContinuousLinearMap_polarComplexStructure K hg hs, hJ]
  ext v
  simp

end SymplecticGeometry

namespace TauCeti

open SymplecticGeometry

variable {W W' : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [NormedAddCommGroup W'] [InnerProductSpace ℝ W'] [FiniteDimensional ℝ W']

/-- The formula only sees the symmetric part of its first argument and the skew part of its
second. -/
private theorem metricPolarFormula_symmPart_skewPart (g s : W →L[ℝ] W →L[ℝ] ℝ) :
    metricPolarFormula ((2 : ℝ)⁻¹ • (g + g.flip)) ((2 : ℝ)⁻¹ • (s - s.flip)) =
      metricPolarFormula g s := by
  have h₁ : (2 : ℝ)⁻¹ • ((2 : ℝ)⁻¹ • (g + g.flip) + ((2 : ℝ)⁻¹ • (g + g.flip)).flip) =
      (2 : ℝ)⁻¹ • (g + g.flip) := by
    ext u v
    simp only [smul_apply, add_apply, ContinuousLinearMap.flip_apply, smul_eq_mul]
    ring
  have h₂ : (2 : ℝ)⁻¹ • ((2 : ℝ)⁻¹ • (s - s.flip) - ((2 : ℝ)⁻¹ • (s - s.flip)).flip) =
      (2 : ℝ)⁻¹ • (s - s.flip) := by
    ext u v
    simp only [smul_apply, sub_apply, ContinuousLinearMap.flip_apply, smul_eq_mul]
    ring
  simp only [metricPolarFormula_def, h₁, h₂]

/-- On the domain, the formula is `J_{g',ω'}` for the symmetric part `g'` of `g` and the skew
part `ω'` of `s`. -/
private theorem metricPolarFormula_eq_of_mem {g s : W →L[ℝ] W →L[ℝ] ℝ}
    (h : (g, s) ∈ polarDomain W) :
    metricPolarFormula g s = LinearMap.toContinuousLinearMap
      (metricPolarComplexStructure ⟨_, symmPart_mem_innerProducts h.1⟩
        (skewPartForm h.2)).toLinearMap := by
  rw [← metricPolarFormula_symmPart_skewPart, ← metricPolarFormula_eq]
  exact congrArg _ (ContinuousLinearMap.toContinuousBilinearMap_toBilinForm _).symm

/-- **Naturality of the formula.** On the domain, pushing both forms forward along a linear
isomorphism `e` conjugates the formula by `e`. -/
theorem metricPolarFormula_conj (e : W ≃L[ℝ] W') {g s : W →L[ℝ] W →L[ℝ] ℝ}
    (h : (g, s) ∈ polarDomain W) :
    metricPolarFormula (g.bilinearComp (e.symm : W' →L[ℝ] W) (e.symm : W' →L[ℝ] W))
        (s.bilinearComp (e.symm : W' →L[ℝ] W) (e.symm : W' →L[ℝ] W)) =
      e.conjContinuousAlgEquiv (metricPolarFormula g s) := by
  have hg : (2 : ℝ)⁻¹ • (g.bilinearComp (e.symm : W' →L[ℝ] W) (e.symm : W' →L[ℝ] W) +
      (g.bilinearComp (e.symm : W' →L[ℝ] W) (e.symm : W' →L[ℝ] W)).flip) =
      (innerProducts.transport e ⟨_, symmPart_mem_innerProducts h.1⟩ :
        W' →L[ℝ] W' →L[ℝ] ℝ) := by
    ext u v
    simp
  have hs : (2 : ℝ)⁻¹ • (s.bilinearComp (e.symm : W' →L[ℝ] W) (e.symm : W' →L[ℝ] W) -
      (s.bilinearComp (e.symm : W' →L[ℝ] W) (e.symm : W' →L[ℝ] W)).flip) =
      ((skewPartForm h.2).transport e.toLinearEquiv).toBilinForm.toContinuousBilinearMap := by
    ext u v
    simp [skewPartForm_apply]
  rw [← metricPolarFormula_symmPart_skewPart, hg, hs, metricPolarFormula_eq,
    metricPolarComplexStructure_transport, metricPolarFormula_eq_of_mem h]
  ext v
  simp

end TauCeti

namespace SymplecticGeometry

open TauCeti Module

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

end SymplecticGeometry
