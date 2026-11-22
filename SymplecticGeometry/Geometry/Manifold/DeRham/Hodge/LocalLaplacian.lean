/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Analysis.InnerProductSpace.HodgeStar.AlternatingForm
public import SymplecticGeometry.Geometry.Manifold.DeRham.Hodge.Chart
import SymplecticGeometry.LinearAlgebra.BilinearForm.Gram
import TauCeti.Analysis.Normed.Module.Alternating.Uncurry.Fin
import TauCeti.Topology.Algebra.Module.Alternating.Basic

/-!
# The codifferential in a chart

Let `ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞` be a chart of an oriented Riemannian manifold `M` of
dimension `m`, and `b` a basis of `E`, with Gram matrix `G(y)` for the metric in the chart
`gramInChart ψ y`. This file shows that the codifferential, read in the chart, is a first-order
operator whose principal part is minus the contraction with the metric dual of the derivative:
for a smooth `(k + 1)`-form `β` read in the chart as `a`,
`(d^* β)_ψ(y) = -∑ᵢⱼ G⁻¹ᵢⱼ(y) ι_{b_j} (∂_{b_i} a)(y) + C₀(y) a(y)`, with `C₀` smooth.

## Main results

* `SymplecticGeometry.smul_hodgeStarInChart_alternatizeUncurryFin_hodgeStarInChart`: the symbol of
  the codifferential in the chart: `± S' ε_ξ S a = -ι_u a`, with `u = ∑ᵢⱼ G⁻¹ᵢⱼ ξ(bᵢ) bⱼ` the
  vector dual to `ξ` (`LinearMap.BilinForm.apply_sum_inv_toMatrix_smul`). This is
  `Orientation.smul_formHodgeStar_alternatizeUncurryFin_formHodgeStar` in the tangent space at
  `ψ.symm y`, read through the differential of `ψ.symm`.
* `SymplecticGeometry.exists_mpullback_symm_codifferential_eq`: the codifferential in the chart is
  a first-order operator with principal part `-∑ᵢⱼ G⁻¹ᵢⱼ ι_{b_j} ∂_{b_i}`.

## References

* F. W. Warner, *Foundations of Differentiable Manifolds and Lie Groups*, Graduate Texts in
  Mathematics 94, Springer, 1983, §6.1.
-/

public section

noncomputable section

open Module TauCeti ContinuousAlternatingMap
open Bundle
open scoped Manifold ContDiff RealInnerProductSpace

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
  set A : E →L[ℝ] TangentSpace I (ψ.symm y) := mfderiv 𝓘(ℝ, E) I ψ.symm y
  set P : TangentSpace I (ψ.symm y) →L[ℝ] E := mfderiv I 𝓘(ℝ, E) ψ (ψ.symm y)
  have hAP : A.comp P = .id ℝ _ := ContinuousLinearMap.ext fun v ↦ by
    have h := ψ.mfderiv_symm_apply_mfderiv_apply (by simp) (ψ.map_target hy) v
    rwa [ψ.right_inv hy] at h
  have hPA : P.comp A = .id ℝ E :=
    ContinuousLinearMap.ext fun v ↦ ψ.mfderiv_apply_mfderiv_symm_apply (by simp) hy v
  have hcomp {j : ℕ} (c : E [⋀^Fin j]→L[ℝ] ℝ) :
      (c.compContinuousLinearMap P).compContinuousLinearMap A = c := by
    ext v
    rw [compContinuousLinearMap_compContinuousLinearMap, hPA]
    -- The two sides differ only in the types `E` and `TangentSpace 𝓘(ℝ, E) y` of the vectors.
    rfl
  have hcomp' {j : ℕ} (c : TangentSpace I (ψ.symm y) [⋀^Fin j]→L[ℝ] ℝ) :
      (c.compContinuousLinearMap A).compContinuousLinearMap P = c := by
    ext v
    rw [compContinuousLinearMap_compContinuousLinearMap, hAP]
    -- The two sides differ only in the types `TangentSpace I (ψ.symm y)` and
    -- `TangentSpace 𝓘(ℝ, E) y` of the vectors.
    rfl
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
          A :=
    -- `hodgeStarInChart_def`, applied to `c`; the composites differ from the right side only
    -- in the types `E` and `TangentSpace 𝓘(ℝ, E) _` of the vectors.
    DFunLike.congr_fun (hodgeStarInChart_def o ψ h y) c
  have hξ : ξ.comp P = innerSL ℝ (E := TangentSpace I (ψ.symm y)) (A u) := by
    ext v
    have h := DFunLike.congr_fun hAP v
    rw [ContinuousLinearMap.comp_apply] at h
    rw [ContinuousLinearMap.comp_apply, innerSL_apply_apply, ← hdual, gramInChart_apply]
    exact congrArg (fun z ↦ ⟪A u, z⟫) h
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
  have ha : DifferentiableAt ℝ a y :=
    ((SmoothForm.contDiffOn_mpullback β ψ.open_target ψ.symm.contMDiffOn).contDiffAt
      hT).differentiableAt (by simp)
  have hS : DifferentiableAt ℝ (hodgeStarInChart o ψ hkl) y :=
    ((contDiffOn_hodgeStarInChart o ψ hkl).contDiffAt hT).differentiableAt (by simp)
  rw [mpullback_symm_codifferential o ψ hkl hlk β hy, extDeriv, fderiv_clm_apply hS ha,
    alternatizeUncurryFin_add, map_add, smul_add]
  refine congrArg₂ (· + ·) ?_ ?_
  swap
  · simp only [_root_.smul_apply, ContinuousLinearMap.comp_apply, alternatizeUncurryFinCLM_apply]
  -- The principal part: expand the derivative of `a` in the dual basis of `b`.
  have hD : hodgeStarInChart o ψ hkl y ∘L fderiv ℝ a y = ∑ i,
      (LinearMap.toContinuousLinearMap (b.coord i)).smulRight
        (hodgeStarInChart o ψ hkl y (fderiv ℝ a y (b i))) := by
    ext1 v
    simp only [ContinuousLinearMap.comp_apply, FunLike.coe_sum, Finset.sum_apply,
      ContinuousLinearMap.smulRight_apply, LinearMap.coe_toContinuousLinearMap', Basis.coord_apply]
    simp_rw [← map_smul, ← _root_.map_sum, b.sum_repr]
  rw [hD, ← alternatizeUncurryFinCLM_apply, _root_.map_sum, _root_.map_sum, Finset.smul_sum]
  simp_rw [alternatizeUncurryFinCLM_apply,
    smul_hodgeStarInChart_alternatizeUncurryFin_hodgeStarInChart o ψ hkl hlk b hy]
  simp [Finset.sum_neg_distrib, Basis.coord_apply, Finsupp.single_apply, ite_smul]

end SymplecticGeometry
