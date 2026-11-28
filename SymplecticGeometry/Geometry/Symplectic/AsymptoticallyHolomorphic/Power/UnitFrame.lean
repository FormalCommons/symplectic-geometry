/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.AsymptoticallyHolomorphic.Power.Connection
import SymplecticGeometry.Topology.FiberBundle.Associated.Basic
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Riemannian.Norm

/-!
# Unit sections of the powers of a principal circle bundle

Let `P → B` be a smooth principal `Circle`-bundle, `α` a real one-form on its total space and
`k` an integer. This file treats sections of norm one of the complex line bundle
`PowerBundle P k`, and the connection `D_k = powerConnection α k` on them.

A smooth section `s` with no zero gives the smooth section `(‖s‖⁻¹ : ℂ) • s` of norm one. This
needs nothing of `PowerBundle P k` beyond its smooth metric: the library's
`ContMDiff.inv_norm_smul_section` (`Geometry/Manifold/VectorBundle/Riemannian/Norm.lean`) gives
the smoothness for every Riemannian bundle, and Mathlib's `norm_smul_inv_norm` the norm. The
`example` below records the instance for `PowerBundle P k`.

On a smooth section `u` of norm one, `D_k u = i β ⊗ u` for a smooth real one-form `β`
(`SymplecticGeometry.exists_powerConnection_eq_smul_of_norm_eq_one`), when `α` is a connection
form. The fibres are complex lines, so `D_k u` is a multiple `⟪u, D_k u⟫_ℂ • u` of `u`; the
coefficient is imaginary, since `D_k` is metric (`isMetricCompatible_powerConnection`) and
`⟪u, u⟫ = 1` is constant. The one-form is `β = Im ⟪u, D_k u⟫_ℂ`, that is `v ↦ ⟪i u, D_k u v⟫`
for the real inner product. Near a point `x`, write `u = [σ_x, f]` in the preferred local section
`σ_x` of `P` at `x`, with `f` smooth and `‖f‖ = 1`. The local formula
`powerConnection_apply_frame` gives `β = ⟪i f, df⟫ + k σ_x^* α` there, which is smooth.

## Main results

* `SymplecticGeometry.exists_powerConnection_eq_smul_of_norm_eq_one`: for a connection form `α`
  and a smooth section `u` of norm one, there is a smooth real one-form `β` with
  `D_k u = (i β) • u`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §7.4.
* [S. K. Donaldson, *Symplectic submanifolds and almost-complex geometry*][Donaldson1996].
-/

public section

noncomputable section

open Bundle Manifold TauCeti TauCeti.Manifold TauCeti.PrincipalBundle
open scoped Manifold ContDiff Topology InnerProductSpace

namespace SymplecticGeometry

variable {EB HB B : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B]
  {P : B → Type*} [TopologicalSpace (TotalSpace Circle P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle Circle P] [∀ b, MulAction Circleᵐᵒᵖ (P b)]
  [PrincipalBundle Circle P] [ContMDiffFiberBundle ∞ Circle P IB (𝓡 1)]

attribute [local instance] finrank_real_complex_fact'

variable (α : SmoothForm (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) ℝ 1) (k : ℤ)

/-- A smooth section of `PowerBundle P k` with no zero, divided by its norm, is a smooth section
of norm one. -/
example {s : Π y, PowerBundle P k y}
    (hs : ContMDiff IB (IB.prod 𝓘(ℝ, PowerModel k)) ∞
      (fun y ↦ TotalSpace.mk' (PowerModel k) y (s y)))
    (h0 : ∀ y, s y ≠ 0) :
    ContMDiff IB (IB.prod 𝓘(ℝ, PowerModel k)) ∞
        (fun y ↦ TotalSpace.mk' (PowerModel k) y (((‖s y‖⁻¹ : ℝ) : ℂ) • s y)) ∧
      ∀ y, ‖((‖s y‖⁻¹ : ℝ) : ℂ) • s y‖ = 1 := by
  simp_rw [Complex.coe_smul]
  exact ⟨hs.inv_norm_smul_section h0, fun y ↦ norm_smul_inv_norm (𝕜 := ℝ) (h0 y)⟩

variable [∀ b, Nonempty (P b)]

/-- **The connection one-form of a unit section.** Let `α` be a connection form and `u` a smooth
section of `PowerBundle P k` of norm one. Then there is a smooth real one-form `β` on the base
with `D_k u = (i β) • u`, that is `powerConnection α k u y v = (i β_y(v)) • u y`. -/
theorem exists_powerConnection_eq_smul_of_norm_eq_one (hα : IsCircleConnectionForm α)
    {u : Π y, PowerBundle P k y}
    (hu : ContMDiff IB (IB.prod 𝓘(ℝ, PowerModel k)) ∞
      (fun y ↦ TotalSpace.mk' (PowerModel k) y (u y)))
    (hnorm : ∀ y, ‖u y‖ = 1) :
    ∃ β : SmoothForm IB B ℝ 1, ∀ y (v : TangentSpace IB y),
      powerConnection α k u y v = (Complex.I * (β.val y ![v] : ℝ)) • u y := by
  -- `ℓ y v = ⟪i u y, D_k u y v⟫` is the imaginary part of `⟪u y, D_k u y v⟫_ℂ`.
  set ℓ : Π y, TangentSpace IB y →L[ℝ] ℝ :=
    fun y ↦ (innerSL ℝ (Complex.I • u y)).comp (powerConnection α k u y) with hℓ
  have hpt (y : B) (v : TangentSpace IB y) :
      powerConnection α k u y v = (Complex.I * (ℓ y v : ℂ)) • u y := by
    have hne : u y ≠ 0 := by
      intro h
      simpa [h] using hnorm y
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_ne_zero' (u y) hne).1
      (PowerBundle.finrank_eq_one P k y) (powerConnection α k u y v)
    -- `D_k` is metric and `⟪u, u⟫ = 1` is constant, so `c` is imaginary.
    have hmc := (isMetricCompatible_powerConnection α k).mvfderiv_inner_eq (fun _ ↦ v)
      ((hu y).mdifferentiableAt (by simp)) ((hu y).mdifferentiableAt (by simp))
    have hone : (fun y ↦ ⟪u y, u y⟫_ℝ) = fun _ ↦ (1 : ℝ) := by
      funext y
      rw [real_inner_self_eq_norm_sq, hnorm, one_pow]
    have huu : ⟪u y, u y⟫_ℂ = 1 := by
      rw [inner_self_eq_norm_sq_to_K, hnorm]
      simp
    -- The real inner product of the fibres is the one `InnerProductSpace.rclikeToReal` makes from
    -- the Hermitian one, up to unfolding the instances of the associated bundle.
    have hre (a b : PowerBundle P k y) : ⟪a, b⟫_ℝ = (⟪a, b⟫_ℂ).re := real_inner_eq_re_inner ℂ a b
    simp only [hone, mvfderiv_const, zero_apply, ← hc, hre, inner_smul_left,
      inner_smul_right, huu] at hmc
    rw [← hc, hℓ, ContinuousLinearMap.comp_apply, innerSL_apply_apply, ← hc, hre,
      inner_smul_left, inner_smul_right, huu]
    congr 1
    apply Complex.ext <;> simp at hmc ⊢
    linarith
  -- The form `v ↦ ℓ y v` is smooth: near `x`, it is `⟪i f, df⟫ + k σ_x^* α`.
  have hsm : IsSmoothForm IB ∞ (fun y ↦
      ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace IB y) ℝ (0 : Fin 1) (ℓ y)) := by
    rw [isSmoothForm_def]
    intro x
    set τ : ∀ y, P y := localSection Circle P x
    set e := trivializationAt (PowerModel k) (PowerBundle P k) x
    set f : B → PowerModel k := fun y ↦ (e ⟨y, u y⟩).2
    set U := (trivializationAt Circle P x).baseSet
    set A := TauCeti.mpullback IB (IB.prod (𝓡 1))
      (fun y ↦ ManifoldTotalSpace.homeomorph Circle P ⟨y, τ y⟩) α.val with hAdef
    have hxU : x ∈ U := mem_baseSet_trivializationAt Circle P x
    have hU : IsOpen U := (trivializationAt Circle P x).open_baseSet
    have heU : e.baseSet = U := AssociatedBundle.baseSet_trivializationAt x
    have hsf (y : B) (hy : y ∈ U) : u y = AssociatedBundle.mk Circle (τ y) (f y) := by
      rw [← AssociatedBundle.trivializationAt_symm_eq_mk hy]
      exact (e.symm_apply_apply_mk (heU ▸ hy) (u y)).symm
    have hτ : ContMDiffOn IB (IB.prod (𝓡 1)) ∞
        (fun y ↦ ManifoldTotalSpace.homeomorph Circle P ⟨y, τ y⟩) U := by
      rw [← funext (PrincipalBundle.manifoldLocalSection_def Circle P x)]
      exact PrincipalBundle.contMDiffOn_manifoldLocalSection (IB := IB) (IG := 𝓡 1) (n := ∞) x
    have hf : ContMDiffAt IB 𝓘(ℝ, PowerModel k) ∞ f x := (contMDiffAt_section_iff x).1 (hu x)
    -- The smoothness of the two terms.
    have hA : ContMDiffAt IB (IB.prod 𝓘(ℝ, EB [⋀^Fin 1]→L[ℝ] ℝ)) ∞
        (fun y ↦ TotalSpace.mk' (EB [⋀^Fin 1]→L[ℝ] ℝ) y (A y)) x :=
      ContMDiffAt.mpullback_form (α.contMDiff _) (hτ.contMDiffAt (hU.mem_nhds hxU)) (by simp)
    have hdf : ContMDiffAt IB (IB.prod 𝓘(ℝ, EB →L[ℝ] PowerModel k)) ∞
        (fun y ↦ TotalSpace.mk' (EB →L[ℝ] PowerModel k)
          (E := fun y : B ↦ TangentSpace IB y →L[ℝ] PowerModel k) y (mvfderiv IB f y)) x := by
      have h := ContMDiffAt.contMDiffAt_totalSpaceMk_mvfderiv_uncurry (J := IB) (n := ∞)
        (f := fun _ : B ↦ f)
        (q := (x, x)) (hf.comp (x, x) contMDiffAt_snd)
      exact h.comp x (contMDiffAt_const.prodMk contMDiffAt_id)
    have hL : ContMDiffAt IB 𝓘(ℝ, PowerModel k →L[ℝ] ℝ) ∞
        (fun y ↦ innerSL ℝ (Complex.I • f y)) x :=
      ((innerSL ℝ).contMDiff.comp
        ((Complex.I • ContinuousLinearMap.id ℝ (PowerModel k)).contMDiff)).contMDiffAt.comp x hf
    have hLdf : ContMDiffAt IB (IB.prod 𝓘(ℝ, EB →L[ℝ] ℝ)) ∞
        (fun y ↦ TotalSpace.mk' (EB →L[ℝ] ℝ) (E := fun y : B ↦ TangentSpace IB y →L[ℝ] ℝ) y
          ((innerSL ℝ (Complex.I • f y)).comp (mvfderiv IB f y))) x := by
      rw [contMDiffAt_hom_bundle] at hdf ⊢
      refine ⟨hdf.1, (hL.clm_comp hdf.2).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun y ↦ ?_)⟩
      simp only [ContinuousLinearMap.inCoordinates, Trivial.fiberBundle_trivializationAt',
        Trivial.continuousLinearMapAt_trivialization, ContinuousLinearMap.id_comp,
        ContinuousLinearMap.comp_assoc]
    refine ((contMDiffAt_ofSubsingleton_iff.2 hLdf).add_section
      (hA.const_smul_section (a := (k : ℝ)))).congr_of_eventuallyEq ?_
    -- Near `x`, the local formula for `D_k` in the frame `τ` computes `ℓ`.
    filter_upwards [hU.mem_nhds hxU,
      ((contMDiffAt_iff_contMDiffAt_nhds (n := 1) (by simp)).1 (hf.of_le (by simp)))] with y hy hfy
    have hfn : ‖f y‖ = 1 := by rw [← hnorm y, hsf y hy, AssociatedBundle.norm_mk]
    have hw (w : Fin 1 → TangentSpace IB y) : w = ![w 0] :=
      funext fun i ↦ by rw [Matrix.cons_val_fin_one, Subsingleton.elim i 0]
    simp only [TotalSpace.mk_inj]
    ext w
    rw [hw w]
    simp only [ContinuousAlternatingMap.ofSubsingleton_apply_apply, hℓ,
      ContinuousLinearMap.comp_apply, innerSL_apply_apply,
      powerConnection_apply_frame α k hα hU hτ hy (hfy.mdifferentiableAt one_ne_zero) hsf,
      hsf y hy, ← AssociatedBundle.mk_smul_scalar, AssociatedBundle.inner_mk]
    simp only [hAdef, Pi.add_apply, Pi.smul_apply, ContinuousAlternatingMap.add_apply,
      ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.ofSubsingleton_apply_apply,
      ContinuousLinearMap.comp_apply, innerSL_apply_apply, Matrix.cons_val_zero, inner_add_right]
    congr 1
    rw [PowerModel.real_inner_eq_re_inner, inner_smul_left, inner_smul_right,
      inner_self_eq_norm_sq_to_K, hfn]
    simp
  refine ⟨⟨_, hsm.mem_smoothBundleForms⟩, fun y v ↦ ?_⟩
  rw [hpt y v, ContinuousAlternatingMap.ofSubsingleton_apply_apply, Matrix.cons_val_zero]

end SymplecticGeometry

end
