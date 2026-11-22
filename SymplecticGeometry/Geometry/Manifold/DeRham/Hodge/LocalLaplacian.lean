/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Analysis.InnerProductSpace.HodgeStar.AlternatingForm
public import SymplecticGeometry.Geometry.Manifold.DeRham.Hodge.Chart
import SymplecticGeometry.Analysis.Normed.Module.Alternating.Uncurry.Fin
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.PartialDiffeomorph
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import SymplecticGeometry.LinearAlgebra.BilinearForm.Gram
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Topology.Algebra.Module.Alternating.Basic
import TauCeti.Topology.Algebra.Module.Alternating.TopDegree

/-!
# The codifferential and the Hodge Laplacian in a chart

Let `ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞` be a chart of an oriented Riemannian manifold `M` of
dimension `m`, and `b` a basis of `E`, with Gram matrix `G(y)` for the metric in the chart
`gramInChart ψ y`. This file shows that the codifferential, read in the chart, is a first-order
operator whose principal part is minus the contraction with the metric dual of the derivative:
for a smooth `(k + 1)`-form `β` read in the chart as `a`,
`(d^* β)_ψ(y) = -∑ᵢⱼ G⁻¹ᵢⱼ(y) ι_{b_j} (∂_{b_i} a)(y) + C₀(y) a(y)`, with `C₀` smooth. It follows
that the Hodge Laplacian `Δ = d^* d + d d^*`, read in the chart, is a second-order operator whose
principal part is `-∑ᵢⱼ G⁻¹ᵢⱼ ∂_{b_i} ∂_{b_j}` times the identity.

The second-order terms of `d^* d` and `d d^*` combine by the pointwise identity
`ι_v ε_ξ + ε_ξ ι_v = ξ(v)`
(`ContinuousAlternatingMap.curryLeft_alternatizeUncurryFin_smulRight_add`, in
`Analysis/Normed/Module/Alternating/Uncurry/Fin.lean`), which is Tau Ceti's
`ContinuousAlternatingMap.alternatizeUncurryFin_curryLeft_comp_add_curryLeft` for a family
`ξ.smulRight w`, and by the symmetry of second derivatives. In degree `0` there is no `d d^*`
term and `ι_v ε_ξ = ξ(v)` alone; in the top degree there is no `d^* d` term, and `ε_ξ ι_v = ξ(v)`
since forms of degree `m + 1` vanish.

## Main results

* `SymplecticGeometry.smul_hodgeStarInChart_alternatizeUncurryFin_hodgeStarInChart`: the symbol of
  the codifferential in the chart: `± S' ε_ξ S a = -ι_u a`, with `u = ∑ᵢⱼ G⁻¹ᵢⱼ ξ(bᵢ) bⱼ` the
  vector dual to `ξ` (`LinearMap.BilinForm.apply_sum_inv_toMatrix_smul`). This is
  `Orientation.smul_formHodgeStar_alternatizeUncurryFin_formHodgeStar` in the tangent space at
  `ψ.symm y`, read through the differential of `ψ.symm`.
* `SymplecticGeometry.exists_mpullback_symm_codifferential_eq`: the codifferential in the chart is
  a first-order operator with principal part `-∑ᵢⱼ G⁻¹ᵢⱼ ι_{b_j} ∂_{b_i}`.
* `SymplecticGeometry.exists_mpullback_symm_hodgeLaplacian_eq`: the Hodge Laplacian in the chart
  is a second-order operator with principal part `-∑ᵢⱼ G⁻¹ᵢⱼ ∂_{b_i} ∂_{b_j}` and smooth
  lower-order coefficients.

## References

* F. W. Warner, *Foundations of Differentiable Manifolds and Lie Groups*, Graduate Texts in
  Mathematics 94, Springer, 1983, §6.1.
-/

public section

noncomputable section

open Module TauCeti ContinuousAlternatingMap
open Bundle
open scoped Manifold ContDiff RealInnerProductSpace Topology

namespace SymplecticGeometry

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] {m k l : ℕ}

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] (o : Manifold.Orientation I M (Fin m))
  (ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞)

/-- **The symbol of the codifferential in a chart.** On the target of the chart, for a covector
`ξ` and a `(k + 1)`-form `a` on `E`, `(-1) ^ (m (k + 2) + 1) S' (ε_ξ (S a)) = -ι_u a`, where `S`
and `S'` are the stars in the chart in degrees `k + 1` and `l + 1`, `ε_ξ` is `alternatizeUncurryFin`
of `ξ • ·`, and `u = ∑ᵢⱼ G⁻¹ᵢⱼ ξ(bᵢ) bⱼ` is the vector dual to `ξ` for the metric in the chart, `G`
being its Gram matrix in the basis `b`. -/
theorem smul_hodgeStarInChart_alternatizeUncurryFin_hodgeStarInChart (hkl : k + 1 + l = m)
    (hlk : l + 1 + k = m) (b : Basis (Fin m) ℝ E) {y : E} (hy : y ∈ ψ.target) (ξ : E →L[ℝ] ℝ)
    (a : E [⋀^Fin (k + 1)]→L[ℝ] ℝ) :
    (-1 : ℝ) ^ (m * (k + 2) + 1) • hodgeStarInChart o ψ hlk y
        (alternatizeUncurryFin (ξ.smulRight (hodgeStarInChart o ψ hkl y a))) =
      -a.curryLeft (∑ i, ∑ j,
        (Matrix.of fun i j ↦ gramInChart ψ y (b i) (b j))⁻¹ i j • ξ (b i) • b j) := by
  set u := ∑ i, ∑ j, (Matrix.of fun i j ↦ gramInChart ψ y (b i) (b j))⁻¹ i j • ξ (b i) • b j
  let := o.fact_finrank_tangentSpace (ψ.symm y)
  -- `A` is the differential of `ψ.symm` at `y`, and `P` its inverse, the differential of `ψ`.
  set e : E ≃L[ℝ] TangentSpace I (ψ.symm y) := ψ.mfderivSymmEquiv (by simp) hy
  set A : E →L[ℝ] TangentSpace I (ψ.symm y) := e.toContinuousLinearMap
  set P : TangentSpace I (ψ.symm y) →L[ℝ] E := e.symm.toContinuousLinearMap
  have hA : A = mfderiv 𝓘(ℝ, E) I ψ.symm y := ψ.toContinuousLinearMap_mfderivSymmEquiv _ hy
  have hP : P = mfderiv I 𝓘(ℝ, E) ψ (ψ.symm y) :=
    ψ.toContinuousLinearMap_mfderivSymmEquiv_symm _ hy
  -- Composing with `P`, then with `A`, is the identity, and so is the reverse: the two maps of
  -- Mathlib's `continuousAlternatingMapCongrLeftEquiv e` are these composites by definition.
  have hcomp {j : ℕ} (c : E [⋀^Fin j]→L[ℝ] ℝ) :
      (c.compContinuousLinearMap P).compContinuousLinearMap A = c :=
    e.continuousAlternatingMapCongrLeftEquiv.left_inv c
  have hcomp' {j : ℕ} (c : TangentSpace I (ψ.symm y) [⋀^Fin j]→L[ℝ] ℝ) :
      (c.compContinuousLinearMap A).compContinuousLinearMap P = c :=
    e.continuousAlternatingMapCongrLeftEquiv.right_inv c
  -- `u` is the vector dual to `ξ` for `gramInChart ψ y`, whose Gram matrix in `b` is invertible.
  have hM : LinearMap.BilinForm.toMatrix b (gramInChart ψ y).toLinearMap₁₂ =
      Matrix.of fun i j ↦ gramInChart ψ y (b i) (b j) := by
    ext
    simp [LinearMap.BilinForm.toMatrix_apply]
  have hdual (v : E) : gramInChart ψ y u v = ξ v := by
    have h := LinearMap.congr_fun (LinearMap.BilinForm.apply_sum_inv_toMatrix_smul
      (gramInChart ψ y).toLinearMap₁₂ b (hM ▸ (posDef_gramInChart ψ b hy).det_pos.ne'.isUnit)
      ξ.toLinearMap) v
    simpa [hM, u] using h
  have hS {j j' : ℕ} (h : j + j' = m) (c : E [⋀^Fin j]→L[ℝ] ℝ) :
      hodgeStarInChart o ψ h y c =
        (formHodgeStarCLM o h (ψ.symm y) (c.compContinuousLinearMap P)).compContinuousLinearMap
          A := by
    rw [hA, hP]
    -- `hodgeStarInChart_def`, applied to `c`; the composites differ from the right side only
    -- in the types `E` and `TangentSpace 𝓘(ℝ, E) _` of the vectors.
    exact DFunLike.congr_fun (hodgeStarInChart_def o ψ h y) c
  have hξ : ξ.comp P = innerSL ℝ (E := TangentSpace I (ψ.symm y)) (A u) := by
    ext v
    rw [ContinuousLinearMap.comp_apply, innerSL_apply_apply, ← hdual, gramInChart_apply, ← hA]
    exact congrArg (fun z ↦ ⟪A u, z⟫) (e.apply_symm_apply v)
  have hinner : compContinuousLinearMapCLM P ∘L ξ.smulRight
      ((formHodgeStarCLM o hkl (ψ.symm y) (a.compContinuousLinearMap P)).compContinuousLinearMap
        A) ∘L
        P = (innerSL ℝ (E := TangentSpace I (ψ.symm y)) (A u)).smulRight
          (formHodgeStarCLM o hkl (ψ.symm y) (a.compContinuousLinearMap P)) := by
    rw [← hξ]
    ext v w
    simp [hcomp']
  have key := (o.orientationAt (ψ.symm y)).smul_formHodgeStar_alternatizeUncurryFin_formHodgeStar
    (A u) (hkl.trans this.out.symm) (hlk.trans this.out.symm) (a.compContinuousLinearMap P)
  rw [hS, hS, alternatizeUncurryFin_compContinuousLinearMap, hinner, formHodgeStarCLM_apply,
    formHodgeStarCLM_apply]
  have hsign : (-1 : ℝ) ^ (m * (k + 2) + 1) =
      (-1) ^ (finrank ℝ (TangentSpace I (ψ.symm y)) * (k + 2) + 1) := by
    rw [this.out]
  have hcurry : ((a.compContinuousLinearMap P).curryLeft (A u)).compContinuousLinearMap A =
      a.curryLeft u := by
    rw [← curryLeft_compContinuousLinearMap, hcomp]
  ext w
  rw [← hcurry, ContinuousAlternatingMap.smul_apply, compContinuousLinearMap_apply,
    ContinuousAlternatingMap.neg_apply, compContinuousLinearMap_apply, hsign]
  exact congrArg (· (A ∘ w)) key

/-- **The codifferential in a chart is a first-order operator.** For a chart `ψ` and a basis `b`
of `E`, there is `C₀`, smooth on `ψ.target`, such that for every smooth `(k + 1)`-form `β`, read in
the chart as `a`, and every `y ∈ ψ.target`, the codifferential `d^* β` read in the chart is
`-∑ᵢⱼ G⁻¹ᵢⱼ(y) ι_{b_j} (∂_{b_i} a)(y) + C₀(y) a(y)`, where `G(y)` is the Gram matrix of `b` for the
metric in the chart and `ι` the interior product. -/
theorem exists_mpullback_symm_codifferential_eq
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    (hkl : k + 1 + l = m) (hlk : l + 1 + k = m) (b : Basis (Fin m) ℝ E) :
    ∃ C₀ : E → (E [⋀^Fin (k + 1)]→L[ℝ] ℝ) →L[ℝ] E [⋀^Fin k]→L[ℝ] ℝ,
      ContDiffOn ℝ ∞ C₀ ψ.target ∧
      ∀ (β : SmoothForm I M ℝ (k + 1)), ∀ y ∈ ψ.target,
        (mpullback 𝓘(ℝ, E) I ψ.symm (SmoothForm.codifferential o hkl β).val y :
            E [⋀^Fin k]→L[ℝ] ℝ) =
          -∑ i, ∑ j, (Matrix.of fun i j ↦ gramInChart ψ y (b i) (b j))⁻¹ i j •
              (fderiv ℝ (F := E [⋀^Fin (k + 1)]→L[ℝ] ℝ) (mpullback 𝓘(ℝ, E) I ψ.symm β.val) y
                (b i)).curryLeft (b j) +
            C₀ y (mpullback 𝓘(ℝ, E) I ψ.symm β.val y) := by
  refine ⟨fun z ↦ (-1 : ℝ) ^ (m * (k + 2) + 1) • (hodgeStarInChart o ψ hlk z ∘L
      alternatizeUncurryFinCLM ℝ E ℝ ∘L (fderiv ℝ (hodgeStarInChart o ψ hkl) z).flip), ?_, ?_⟩
  · refine contDiffOn_clm_apply.2 fun α ↦ ?_
    have hflip (z : E) : (fderiv ℝ (hodgeStarInChart o ψ hkl) z).flip α =
        (ContinuousLinearMap.apply ℝ _ α).comp (fderiv ℝ (hodgeStarInChart o ψ hkl) z) :=
      ContinuousLinearMap.ext fun _ ↦ rfl
    simp only [_root_.smul_apply, ContinuousLinearMap.comp_apply, hflip]
    exact ((contDiffOn_hodgeStarInChart o ψ hlk).clm_apply
      ((alternatizeUncurryFinCLM ℝ E ℝ).contDiff.comp_contDiffOn (contDiffOn_const.clm_comp
        ((contDiffOn_hodgeStarInChart o ψ hkl).fderiv_of_isOpen ψ.open_target
          (by simp))))).const_smul ((-1 : ℝ) ^ (m * (k + 2) + 1))
  intro β y hy
  have hT := ψ.open_target.mem_nhds hy
  set a : E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ := mpullback 𝓘(ℝ, E) I ψ.symm β.val
  have ha : DifferentiableAt ℝ a y := β.differentiableAt_mpullback_symm ψ hy
  have hS : DifferentiableAt ℝ (hodgeStarInChart o ψ hkl) y :=
    ((contDiffOn_hodgeStarInChart o ψ hkl).contDiffAt hT).differentiableAt (by simp)
  rw [mpullback_symm_codifferential o ψ hkl hlk β hy, extDeriv, fderiv_clm_apply hS ha,
    alternatizeUncurryFin_add, map_add, smul_add]
  refine congrArg₂ (· + ·) ?_ ?_
  swap
  · simp only [_root_.smul_apply, ContinuousLinearMap.comp_apply, alternatizeUncurryFinCLM_apply]
  -- The principal part: expand the derivative of `a` in the dual basis of `b`.
  rw [alternatizeUncurryFin_eq_sum_coord_smulRight b, _root_.map_sum, Finset.smul_sum]
  simp_rw [ContinuousLinearMap.comp_apply,
    smul_hodgeStarInChart_alternatizeUncurryFin_hodgeStarInChart o ψ hkl hlk b hy]
  simp [Finset.sum_neg_distrib, Basis.coord_apply, Finsupp.single_apply, ite_smul]

/-- The exterior product `ε_{b^*_i}` with the `i`-th coordinate covector of a basis `b`, from
`k`-forms to `(k + 1)`-forms. The two computations below expand `d` in the basis with it. -/
private def coordExtProd (b : Basis (Fin m) ℝ E) (k : ℕ) (i : Fin m) :
    (E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] E [⋀^Fin (k + 1)]→L[ℝ] ℝ :=
  alternatizeUncurryFinCLM ℝ E ℝ ∘L
    ContinuousLinearMap.smulRightL ℝ ℝ ℝ E _ (LinearMap.toContinuousLinearMap (b.coord i))

private theorem coordExtProd_apply (b : Basis (Fin m) ℝ E) (k : ℕ) (i : Fin m)
    (w : E [⋀^Fin k]→L[ℝ] ℝ) : coordExtProd b k i w =
      alternatizeUncurryFin ((LinearMap.toContinuousLinearMap (b.coord i)).smulRight w) := by
  simp [coordExtProd]

/-- The exterior derivative of a form `a` on `E` is `∑ᵢ ε_{b^*_i} (∂_{b_i} a)`. -/
private theorem extDeriv_eq_sum_coordExtProd (b : Basis (Fin m) ℝ E)
    (a : E → E [⋀^Fin k]→L[ℝ] ℝ) (z : E) :
    extDeriv a z = ∑ i, coordExtProd b k i (fderiv ℝ a z (b i)) := by
  rw [extDeriv, alternatizeUncurryFin_eq_sum_coord_smulRight b]
  simp only [coordExtProd_apply]

/-- **`d^* d` in a chart.** For a smooth `k`-form `α` read in the chart as `a`, the form
`d^* d α` read in the chart is `-∑ⱼₗ G⁻¹ⱼₗ ∑ᵢ ι_{b_l} ε_{b^*_i} (∂_{b_j} ∂_{b_i} a)` plus a
first-order term `∑ᵢ Bᵢ (∂_{b_i} a)` with smooth coefficients, `b^*` being the dual basis. -/
private theorem exists_mpullback_symm_codifferential_mextDeriv_eq
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    (hkl : k + 1 + l = m) (hlk : l + 1 + k = m) (b : Basis (Fin m) ℝ E) :
    ∃ B : Fin m → E → (E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] E [⋀^Fin k]→L[ℝ] ℝ,
      (∀ i, ContDiffOn ℝ ∞ (B i) ψ.target) ∧
      ∀ (α : SmoothForm I M ℝ k), ∀ y ∈ ψ.target,
        (mpullback 𝓘(ℝ, E) I ψ.symm
            (SmoothForm.codifferential o hkl (mextDerivₗ I k α)).val y :
            E [⋀^Fin k]→L[ℝ] ℝ) =
          -∑ j, ∑ l, (Matrix.of fun i j ↦ gramInChart ψ y (b i) (b j))⁻¹ j l •
              ∑ i, (alternatizeUncurryFin ((LinearMap.toContinuousLinearMap (b.coord i)).smulRight
                (fderiv ℝ (fun z ↦ fderiv ℝ
                  (mpullback 𝓘(ℝ, E) I ψ.symm α.val : E → E [⋀^Fin k]→L[ℝ] ℝ) z (b i)) y
                  (b j)))).curryLeft (b l) +
            ∑ i, B i y (fderiv ℝ (mpullback 𝓘(ℝ, E) I ψ.symm α.val : E → E [⋀^Fin k]→L[ℝ] ℝ) y
              (b i)) := by
  obtain ⟨C₀, hC₀, hδ⟩ := exists_mpullback_symm_codifferential_eq o ψ hkl hlk b
  refine ⟨fun i z ↦ C₀ z ∘L coordExtProd b k i, fun i ↦ hC₀.clm_comp contDiffOn_const,
    fun α y hy ↦ ?_⟩
  set a : E → E [⋀^Fin k]→L[ℝ] ℝ := mpullback 𝓘(ℝ, E) I ψ.symm α.val
  have hev : (mpullback 𝓘(ℝ, E) I ψ.symm (mextDerivₗ I k α).val :
      E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ) =ᶠ[𝓝 y] fun z ↦ ∑ i, coordExtProd b k i (fderiv ℝ a z (b i)) :=
    Filter.eventually_of_mem (ψ.open_target.mem_nhds hy) fun z hz ↦
      (mpullback_symm_mextDerivₗ ψ α hz).trans (extDeriv_eq_sum_coordExtProd b a z)
  have hD : HasFDerivAt (fun z ↦ ∑ i, coordExtProd b k i (fderiv ℝ a z (b i)))
      (∑ i, (coordExtProd b k i).comp (fderiv ℝ (fun z ↦ fderiv ℝ a z (b i)) y)) y :=
    HasFDerivAt.fun_sum fun i _ ↦ (coordExtProd b k i).hasFDerivAt.comp y
      (((α.contDiffOn_fderiv_mpullback_symm_apply ψ (b i)).contDiffAt
        (ψ.open_target.mem_nhds hy)).differentiableAt (by simp)).hasFDerivAt
  rw [hδ (mextDerivₗ I k α) y hy, hev.fderiv_eq, hev.eq_of_nhds, hD.fderiv]
  simp only [_root_.sum_apply, ContinuousLinearMap.comp_apply, _root_.map_sum, coordExtProd_apply,
    curryLeft_sum]
  -- The two sides agree up to reducible unfolding.
  with_reducible rfl

/-- **`d d^*` in a chart.** For a smooth `(k + 1)`-form `α` read in the chart as `a`, the
form `d d^* α` read in the chart is `-∑ⱼₗ G⁻¹ⱼₗ ∑ᵢ ε_{b^*_i} ι_{b_l} (∂_{b_i} ∂_{b_j} a)` plus terms
`∑ᵢ Bᵢ (∂_{b_i} a) + C a` with smooth coefficients, `b^*` being the dual basis. -/
private theorem exists_mpullback_symm_mextDeriv_codifferential_eq
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    (hkl : k + 1 + l = m) (hlk : l + 1 + k = m) (b : Basis (Fin m) ℝ E) :
    ∃ (B : Fin m → E → (E [⋀^Fin (k + 1)]→L[ℝ] ℝ) →L[ℝ] E [⋀^Fin (k + 1)]→L[ℝ] ℝ)
      (C : E → (E [⋀^Fin (k + 1)]→L[ℝ] ℝ) →L[ℝ] E [⋀^Fin (k + 1)]→L[ℝ] ℝ),
      (∀ i, ContDiffOn ℝ ∞ (B i) ψ.target) ∧ ContDiffOn ℝ ∞ C ψ.target ∧
      ∀ (α : SmoothForm I M ℝ (k + 1)), ∀ y ∈ ψ.target,
        (mpullback 𝓘(ℝ, E) I ψ.symm
            (mextDerivₗ I k (SmoothForm.codifferential o hkl α)).val y :
            E [⋀^Fin (k + 1)]→L[ℝ] ℝ) =
          -∑ j, ∑ l, (Matrix.of fun i j ↦ gramInChart ψ y (b i) (b j))⁻¹ j l •
              ∑ i, alternatizeUncurryFin ((LinearMap.toContinuousLinearMap (b.coord i)).smulRight
                (curryLeft (fderiv ℝ (fun z ↦ fderiv ℝ
                  (mpullback 𝓘(ℝ, E) I ψ.symm α.val : E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ) z (b j)) y
                  (b i)) (b l))) +
            ∑ i, B i y (fderiv ℝ (mpullback 𝓘(ℝ, E) I ψ.symm α.val :
              E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ) y (b i)) +
            C y (mpullback 𝓘(ℝ, E) I ψ.symm α.val y) := by
  obtain ⟨C₀, hC₀, hδ⟩ := exists_mpullback_symm_codifferential_eq o ψ hkl hlk b
  -- `κ l` is the interior product with `b l`.
  set κ : Fin m → (E [⋀^Fin (k + 1)]→L[ℝ] ℝ) →L[ℝ] E [⋀^Fin k]→L[ℝ] ℝ := fun l ↦
    (curryLeftLI (𝕜 := ℝ) (E := E) (F := ℝ) (n := k)).toContinuousLinearMap.flip (b l)
  have hκ (l : Fin m) (w : E [⋀^Fin (k + 1)]→L[ℝ] ℝ) : κ l w = w.curryLeft (b l) := rfl
  set g : E → Matrix (Fin m) (Fin m) ℝ := fun z ↦
    (Matrix.of fun i j ↦ gramInChart ψ z (b i) (b j))⁻¹
  have hgs (j l : Fin m) : ContDiffOn ℝ ∞ (fun z ↦ g z j l) ψ.target :=
    contDiffOn_inv_gramInChart_apply ψ b j l
  have hdg (j l : Fin m) : ContDiffOn ℝ ∞ (fun z ↦ fderiv ℝ (fun z ↦ g z j l) z) ψ.target :=
    (hgs j l).fderiv_of_isOpen ψ.open_target (m := ∞) (by simp)
  -- The partial derivatives of `C₀` are smooth.
  have hdC₀ (i : Fin m) : ContDiffOn ℝ ∞ (fun z ↦ fderiv ℝ C₀ z (b i)) ψ.target :=
    (hC₀.fderiv_of_isOpen ψ.open_target (m := ∞) (by simp)).clm_apply
      (contDiffOn_const (c := b i))
  refine ⟨fun j z ↦ -∑ i, ∑ l, fderiv ℝ (fun z ↦ g z j l) z (b i) • (coordExtProd b k i ∘L κ l) +
      coordExtProd b k j ∘L C₀ z,
    fun z ↦ ∑ i, coordExtProd b k i ∘L fderiv ℝ C₀ z (b i), fun j ↦ ?_, ?_, fun α y hy ↦ ?_⟩
  · refine (ContDiffOn.sum fun i _ ↦ ContDiffOn.sum fun l _ ↦ ?_).neg.add
      (contDiffOn_const.clm_comp hC₀)
    refine contDiffOn_clm_apply.2 fun w ↦ ?_
    simp only [_root_.smul_apply]
    exact ((hdg j l).clm_apply contDiffOn_const).smul contDiffOn_const
  · exact ContDiffOn.sum fun i _ ↦ contDiffOn_const.clm_comp (hdC₀ i)
  set a : E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ := mpullback 𝓘(ℝ, E) I ψ.symm α.val
  have hT := ψ.open_target.mem_nhds hy
  -- `d^* α` read in the chart, near `y`.
  set F : E → E [⋀^Fin k]→L[ℝ] ℝ := fun z ↦
    -∑ j, ∑ l, g z j l • κ l (fderiv ℝ a z (b j)) + C₀ z (a z)
  have hev : (mpullback 𝓘(ℝ, E) I ψ.symm (SmoothForm.codifferential o hkl α).val :
      E → E [⋀^Fin k]→L[ℝ] ℝ) =ᶠ[𝓝 y] F :=
    Filter.eventually_of_mem hT fun z hz ↦ hδ α z hz
  have hF : HasFDerivAt F
      (-∑ j, ∑ l, (g y j l • (κ l).comp (fderiv ℝ (fun z ↦ fderiv ℝ a z (b j)) y) +
          (fderiv ℝ (fun z ↦ g z j l) y).smulRight (κ l (fderiv ℝ a y (b j)))) +
        ((C₀ y).comp (fderiv ℝ a y) + (fderiv ℝ C₀ y).flip (a y))) y := by
    refine (HasFDerivAt.fun_sum fun j _ ↦ HasFDerivAt.fun_sum fun l _ ↦ ?_).neg.add ?_
    · exact (((hgs j l).contDiffAt hT).differentiableAt (by simp)).hasFDerivAt.smul
        ((κ l).hasFDerivAt.comp y
          (((α.contDiffOn_fderiv_mpullback_symm_apply ψ (b j)).contDiffAt
            (ψ.open_target.mem_nhds hy)).differentiableAt (by simp)).hasFDerivAt)
    · exact ((hC₀.contDiffAt hT).differentiableAt (by simp)).hasFDerivAt.clm_apply
        (α.differentiableAt_mpullback_symm ψ hy).hasFDerivAt
  rw [mpullback_symm_mextDerivₗ ψ _ hy, hev.extDeriv_eq, extDeriv_eq_sum_coordExtProd b, hF.fderiv]
  simp only [← coordExtProd_apply, ← hκ, map_add, map_neg, _root_.map_sum, map_smul,
    Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.smul_sum, _root_.add_apply,
    _root_.neg_apply, _root_.sum_apply, _root_.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.flip_apply]
  -- Bring the sums over the basis to the order of the right side.
  conv_lhs =>
    enter [1, 1, 1]
    rw [Finset.sum_comm]
    enter [2, j]
    rw [Finset.sum_comm]
  conv_lhs => enter [1, 1, 2]; rw [Finset.sum_comm]
  abel


/-- The principal parts of `d^* d` and `d d^*` add up to `-∑ᵢⱼ Gᵢⱼ wᵢⱼ` for a symmetric `w`. -/
private theorem principal_add (b : Basis (Fin m) ℝ E) (G : Matrix (Fin m) (Fin m) ℝ)
    (w : Fin m → Fin m → E [⋀^Fin (k + 1)]→L[ℝ] ℝ) (hw : ∀ i j, w i j = w j i) :
    -∑ j, ∑ l, G j l • ∑ i, (alternatizeUncurryFin
        ((LinearMap.toContinuousLinearMap (b.coord i)).smulRight (w i j))).curryLeft (b l) +
      -∑ j, ∑ l, G j l • ∑ i, alternatizeUncurryFin
        ((LinearMap.toContinuousLinearMap (b.coord i)).smulRight ((w j i).curryLeft (b l))) =
      -∑ i, ∑ j, G i j • w i j := by
  have key (j l : Fin m) : ∑ i, (alternatizeUncurryFin
        ((LinearMap.toContinuousLinearMap (b.coord i)).smulRight (w i j))).curryLeft (b l) +
      ∑ i, alternatizeUncurryFin
        ((LinearMap.toContinuousLinearMap (b.coord i)).smulRight ((w j i).curryLeft (b l))) =
      w j l := by
    simp_rw [hw j]
    rw [← Finset.sum_add_distrib]
    simp only [curryLeft_alternatizeUncurryFin_smulRight_add, LinearMap.coe_toContinuousLinearMap',
      Basis.coord_apply, Basis.repr_self, Finsupp.single_apply, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true, hw l j]
  simp_rw [← neg_add, ← Finset.sum_add_distrib, ← smul_add, key]

/-- **The Hodge Laplacian in a chart has principal part `-G^{ij} ∂ᵢ∂ⱼ`.** For a chart `ψ` and a
basis `b` of `E`, there are `B : Fin m → E → Λ →L[ℝ] Λ` and `C : E → Λ →L[ℝ] Λ`, with
`Λ = E [⋀^Fin k]→L[ℝ] ℝ`, smooth on `ψ.target`, such that for every smooth `k`-form `α`, read in
the chart as `a`, and every `y ∈ ψ.target`, the Hodge Laplacian `Δα` read in the chart is
`-∑ᵢⱼ G⁻¹ᵢⱼ(y) ∂_{b_j} ∂_{b_i} a(y) + ∑ᵢ Bᵢ(y) (∂_{b_i} a(y)) + C(y) a(y)`, where `G(y)` is the Gram
matrix of `b` for the metric in the chart. -/
theorem exists_mpullback_symm_hodgeLaplacian_eq
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    (hkl : k + l = m) (b : Basis (Fin m) ℝ E) :
    ∃ (B : Fin m → E → (E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] E [⋀^Fin k]→L[ℝ] ℝ)
      (C : E → (E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] E [⋀^Fin k]→L[ℝ] ℝ),
      (∀ i, ContDiffOn ℝ ∞ (B i) ψ.target) ∧ ContDiffOn ℝ ∞ C ψ.target ∧
      ∀ (α : SmoothForm I M ℝ k), ∀ y ∈ ψ.target,
        (mpullback 𝓘(ℝ, E) I ψ.symm (SmoothForm.hodgeLaplacian o hkl α).val y :
            E [⋀^Fin k]→L[ℝ] ℝ) =
          -∑ i, ∑ j, (Matrix.of fun i j ↦ gramInChart ψ y (b i) (b j))⁻¹ i j •
              fderiv ℝ (F := E [⋀^Fin k]→L[ℝ] ℝ) (fun z ↦ fderiv ℝ
                (mpullback 𝓘(ℝ, E) I ψ.symm α.val : E → E [⋀^Fin k]→L[ℝ] ℝ) z (b i)) y (b j) +
            ∑ i, B i y (fderiv ℝ (mpullback 𝓘(ℝ, E) I ψ.symm α.val : E → E [⋀^Fin k]→L[ℝ] ℝ) y
              (b i)) +
            C y (mpullback 𝓘(ℝ, E) I ψ.symm α.val y : E [⋀^Fin k]→L[ℝ] ℝ) := by
  -- The second derivatives of a form read in the chart are symmetric.
  have hsymm (α : SmoothForm I M ℝ k) {y : E} (hy : y ∈ ψ.target) :=
    fderiv_fderiv_apply_comm (α.contDiffAt_mpullback_symm ψ hy) (n := ∞) (by simp)
  rcases k with _ | k <;> rcases l with _ | l
  · -- On a zero-dimensional manifold both sides vanish.
    subst hkl
    refine ⟨0, 0, fun _ ↦ contDiffOn_const, contDiffOn_const, fun α y _ ↦ ?_⟩
    simp [SmoothForm.hodgeLaplacian_zero_zero, mpullback_zero]
    -- What is left is `0 = C y (a y)` for the zero map `C`.
    rfl
  · -- In degree `0`, `Δ = d^* d`.
    obtain ⟨B, hB, h⟩ := exists_mpullback_symm_codifferential_mextDeriv_eq o ψ
      (by omega : 0 + 1 + l = m) (by omega) b
    refine ⟨B, 0, hB, contDiffOn_const, fun α y hy ↦ ?_⟩
    rw [SmoothForm.hodgeLaplacian_zero_add_one o hkl (by omega), h α y hy]
    have h0 : (0 : E → (E [⋀^Fin 0]→L[ℝ] ℝ) →L[ℝ] E [⋀^Fin 0]→L[ℝ] ℝ) y
        (mpullback 𝓘(ℝ, E) I ψ.symm α.val y : E [⋀^Fin 0]→L[ℝ] ℝ) = 0 :=
      -- `simp` leaves this open; it holds by unfolding the zero map.
      rfl
    simp only [curryLeft_alternatizeUncurryFin_smulRight_zero, LinearMap.coe_toContinuousLinearMap',
      Basis.coord_apply, Basis.repr_self, Finsupp.single_apply, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true, h0, add_zero]
    congr 2
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hsymm α hy]
  · -- In the top degree, `Δ = d d^*`, and forms of degree `m + 1` vanish.
    obtain ⟨B, C, hB, hC, h⟩ := exists_mpullback_symm_mextDeriv_codifferential_eq o ψ
      (k := k) (l := 0) hkl (by omega) b
    refine ⟨B, C, hB, hC, fun α y hy ↦ ?_⟩
    rw [SmoothForm.hodgeLaplacian_add_one_zero o hkl, h α y hy]
    have hm : finrank ℝ E = k + 1 := by rw [finrank_eq_card_basis b, Fintype.card_fin]; omega
    have hι (i : Fin m) (w : E [⋀^Fin (k + 1)]→L[ℝ] ℝ) (v : E) :
        alternatizeUncurryFin ((LinearMap.toContinuousLinearMap (b.coord i)).smulRight
          (w.curryLeft v)) = LinearMap.toContinuousLinearMap (b.coord i) v • w := by
      have h0 : alternatizeUncurryFin ((LinearMap.toContinuousLinearMap (b.coord i)).smulRight
          w) = 0 := eq_zero_of_finrank_lt _ (by simp [hm])
      simpa [h0] using curryLeft_alternatizeUncurryFin_smulRight_add
        (LinearMap.toContinuousLinearMap (b.coord i)) w v
    simp only [hι, LinearMap.coe_toContinuousLinearMap', Basis.coord_apply, Basis.repr_self,
      Finsupp.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ,
      ite_true]
    -- The two sides agree up to reducible unfolding.
    with_reducible rfl
  · -- Strictly between, `Δ = d^* d + d d^*`.
    obtain ⟨B₁, hB₁, h₁⟩ := exists_mpullback_symm_codifferential_mextDeriv_eq o ψ
      (k := k + 1) (l := l) (by omega) (by omega) b
    obtain ⟨B₂, C, hB₂, hC, h₂⟩ := exists_mpullback_symm_mextDeriv_codifferential_eq o ψ
      (k := k) (l := l + 1) hkl (by omega) b
    refine ⟨fun i z ↦ B₁ i z + B₂ i z, C, fun i ↦ (hB₁ i).add (hB₂ i), hC, fun α y hy ↦ ?_⟩
    rw [SmoothForm.hodgeLaplacian_add_one_add_one o hkl (by omega), Submodule.coe_add,
      mpullback_add, Pi.add_apply, h₁ α y hy, h₂ α y hy]
    have hP := principal_add b (Matrix.of fun i j ↦ gramInChart ψ y (b i) (b j))⁻¹
      (fun i j ↦ fderiv ℝ (F := E [⋀^Fin (k + 1)]→L[ℝ] ℝ) (fun z ↦ fderiv ℝ
        (mpullback 𝓘(ℝ, E) I ψ.symm α.val : E → E [⋀^Fin (k + 1)]→L[ℝ] ℝ) z (b i)) y (b j))
      fun i j ↦ hsymm α hy _ _
    rw [← hP]
    simp only [_root_.add_apply, Finset.sum_add_distrib]
    abel


end SymplecticGeometry
