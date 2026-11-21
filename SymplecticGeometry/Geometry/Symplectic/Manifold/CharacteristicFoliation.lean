/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.Descent
import SymplecticGeometry.Analysis.Calculus.DifferentialForm.LieDeriv
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.ModelSpace
import TauCeti.LinearAlgebra.Alternating.Conormal
import TauCeti.LinearAlgebra.Alternating.Curry

/-!
# Descent of a closed two-form along a characteristic submersion

Let `σ` be a closed two-form on a boundaryless manifold `M`. A *characteristic submersion* of `σ`
is a surjective smooth submersion `p : M → B` with preconnected fibres whose derivative at each
point has the kernel of `σ` there as its kernel
(`TauCeti.SmoothForm.IsCharacteristicSubmersion`). Its fibres are unions of leaves of the
characteristic foliation of `σ`. On an open subset of `M`, a local version of it is the
foliation-compatible chart that gives the local symplectic quotients of a presymplectic manifold
[McDuffSalamon2017, §3.4].

The main result is that `σ` descends: it is the pullback `p^* τ` of a unique symplectic form `τ`
on `B` (`TauCeti.SmoothForm.IsCharacteristicSubmersion.existsUnique_isSymplectic_mpullback_eq`).
Tau Ceti's `TauCeti.SmoothTwoForm.existsUnique_isSymplectic_mpullback_eq` gives this once `σ` is
basic for `p` (`TauCeti.RoughForm.IsBasic`), that is, once `σ_x (u, v)` depends only on `p x`,
`dp_x u` and `dp_x v`. That is `TauCeti.SmoothForm.IsCharacteristicSubmersion.isBasic`.

The proof of `isBasic` is local along each fibre, followed by connectedness. At one point, `σ_x`
vanishes on the kernel of `dp_x`, so it is determined by the images of its arguments under `dp_x`
(`TauCeti.SmoothForm.IsCharacteristicSubmersion.apply_eq_of_mfderiv_eq`). Near a point `x`, read
`σ` in the chart of the submersion `p` at `x` (Mathlib's `IsSubmersionAt.domChart`), in which `p`
is a linear projection `π`. In this chart `σ` becomes a closed form `α` on an open subset of the
model space whose kernel contains the constant subspace `ker π`. For `w ∈ ker π`, Cartan's formula
`L_w α = ι_w dα + d (ι_w α)` shows that `α` is constant along `w`
(`apply_add_eq_of_extDeriv_eq_zero`), so `α` is constant on the part of the fibre of `π` in a
ball. Hence the form that `σ` induces on `T_{p x} B` is locally constant along the fibre
through `x`, and so constant on the preconnected fibre.

## Main definitions

* `TauCeti.SmoothForm.IsCharacteristicSubmersion`: a surjective submersion with preconnected
  fibres whose vertical spaces are the kernels of `σ`.

## Main results

* `TauCeti.SmoothForm.IsCharacteristicSubmersion.isBasic`: a closed form is basic for each of its
  characteristic submersions.
* `TauCeti.SmoothForm.IsCharacteristicSubmersion.existsUnique_isSymplectic_mpullback_eq`: it is
  the pullback of a unique symplectic form on the base.

The projection `B × F → B` with a form pulled back from a nondegenerate form on `B` is an
example.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §3.4
  (Exercise 3.4.9, characteristic foliations of coisotropic submanifolds)
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Theorem 14.35
  (Cartan's formula)
-/

public section

noncomputable section

open Set Filter Function Manifold Bundle
open scoped Manifold ContDiff Topology

namespace TauCeti.SmoothForm

variable {E H M EB HB B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  (IB : ModelWithCorners ℝ EB HB) [TopologicalSpace B] [ChartedSpace HB B]

/-- A map `p : M → B` is a **characteristic submersion** of a two-form `σ` on `M` if it is a
surjective smooth submersion with preconnected fibres and, at every point `x`, the kernel of the
derivative of `p` is the kernel of `σ_x`. Its fibres are then unions of leaves of the
characteristic foliation of `σ`, and for closed `σ` the form descends to a symplectic form on
`B` (`IsCharacteristicSubmersion.existsUnique_isSymplectic_mpullback_eq`). -/
structure IsCharacteristicSubmersion (σ : SmoothForm I M ℝ 2) (p : M → B) : Prop where
  /-- The map is a smooth submersion. -/
  isSubmersion : IsSubmersion I IB ∞ p
  /-- The map is surjective. -/
  surjective : Surjective p
  /-- Every fibre is preconnected. -/
  isPreconnected_preimage_singleton : ∀ b, IsPreconnected (p ⁻¹' {b})
  /-- The vertical space at each point is the kernel of the form there. -/
  ker_mfderiv : ∀ x, (mfderiv I IB p x).ker = LinearMap.ker (σ.bilinFormAt x)

variable {IB} {σ : SmoothForm I M ℝ 2} {p : M → B}

namespace IsCharacteristicSubmersion

/-- At a point `x`, the value of `σ_x` on two vectors depends only on their images under the
derivative of a characteristic submersion `p` at `x`. -/
theorem apply_eq_of_mfderiv_eq (hp : IsCharacteristicSubmersion IB σ p) {x : M}
    {v w : Fin 2 → TangentSpace I x}
    (h : ∀ i, mfderiv I IB p x (v i) = mfderiv I IB p x (w i)) :
    σ.val x v = σ.val x w := by
  refine Submodule.conormalForms_apply_eq_of_sub_mem (W := (mfderiv I IB p x).ker)
    (α := (σ.val x).toAlternatingMap) (Submodule.mem_conormalForms.2 fun m j hj ↦ ?_)
    fun j ↦ by simp [h j]
  rw [hp.ker_mfderiv x, mem_ker_bilinFormAt_iff] at hj
  refine AlternatingMap.map_eq_zero_of_curryLeft_eq_zero (x := m j) ?_ rfl
  ext u
  have e : Matrix.vecCons (m j) u = ![m j, u 0] := by
    funext i; fin_cases i <;> rfl
  simpa [AlternatingMap.curryLeft_apply_apply, e] using hj (u 0)

/-- The form `σ` read on `T_{p y} B` at a point `y`, through a (non-canonical) right inverse of
the derivative of `p`. -/
private def fibreForm (hp : IsCharacteristicSubmersion IB σ p) (y : M) (a : Fin 2 → EB) : ℝ :=
  σ.val y fun i ↦ surjInv ((hp.isSubmersion.isSubmersionAt y).surjective_mfderiv (by simp)) (a i)

/-- `fibreForm` evaluates on images under the derivative of `p` as `σ`. -/
private theorem fibreForm_mfderiv (hp : IsCharacteristicSubmersion IB σ p) (y : M)
    (v : Fin 2 → TangentSpace I y) :
    hp.fibreForm y (fun i ↦ mfderiv I IB p y (v i)) = σ.val y v :=
  hp.apply_eq_of_mfderiv_eq fun _ ↦ surjInv_eq _ _

variable [I.Boundaryless]

/-- `fibreForm` is locally constant along the fibres of `p`. -/
private theorem eventually_fibreForm_eq (hp : IsCharacteristicSubmersion IB σ p)
    (hσ : σ.IsClosed) (x : M) :
    ∀ᶠ y in 𝓝 x, p y = p x → hp.fibreForm y = hp.fibreForm x := by
  let h := (hp.isSubmersion.isSubmersionAt x).isSubmersionAtOfComplement_complement
  let κ := h.domChart.extend I
  have he : h.domChart ∈ IsManifold.maximalAtlas I 1 M :=
    IsManifold.maximalAtlas_subset_of_le (by simp) h.domChart_mem_maximalAtlas
  have hψ : h.codChart ∈ IsManifold.maximalAtlas IB 1 B :=
    IsManifold.maximalAtlas_subset_of_le (by simp) h.codChart_mem_maximalAtlas
  have hU : IsOpen κ.target := h.domChart.isOpen_extend_target
  have hx : x ∈ κ.source := by simpa [κ] using h.mem_domChart_source
  -- On the chart's image, `κ⁻¹` and `κ` have inverse derivatives.
  have hinv (z : E) (hz : z ∈ κ.target) (c : E) :
      mfderiv I 𝓘(ℝ, E) κ (κ.symm z) (mfderiv 𝓘(ℝ, E) I κ.symm z c) = c := by
    have := mfderiv_extend_comp_mfderivWithin_extend_symm he hz
    rw [I.range_eq_univ, mfderivWithin_univ] at this
    exact congrArg (· c) this
  have hsrc (z : E) (hz : z ∈ κ.target) : κ.symm z ∈ h.domChart.source := by
    simpa [κ] using κ.map_target hz
  -- The form `σ` read in the chart `κ`.
  let α : E → E [⋀^Fin 2]→L[ℝ] ℝ := TauCeti.mpullback 𝓘(ℝ, E) I κ.symm σ.val
  have hα (z : E) (c : Fin 2 → E) :
      α z c = σ.val (κ.symm z) fun i ↦ mfderiv 𝓘(ℝ, E) I κ.symm z (c i) :=
    TauCeti.mpullback_apply _ _ _ _
  -- In the chart, `p` reads as the first component of `h.equiv`, and so does its derivative.
  have hP (z : E) (hz : z ∈ κ.target) (c : E) :
      mfderiv IB 𝓘(ℝ, EB) (h.codChart.extend IB) (p (κ.symm z))
        (mfderiv I IB p (κ.symm z) (mfderiv 𝓘(ℝ, E) I κ.symm z c)) = (h.equiv c).1 := by
    have := DFunLike.congr_fun (h.mfderiv_extend_comp_mfderiv (by simp) (hsrc z hz))
      (mfderiv 𝓘(ℝ, E) I κ.symm z c)
    rw [ContinuousLinearMap.comp_apply] at this
    rw [this]
    -- `ContinuousLinearMap.comp_apply` does not fire on the right side, where the derivative of
    -- `κ` lands in the tangent space of the model space rather than in `E`; `exact` unfolds it.
    exact (congrArg h.projection (hinv z hz c)).trans (h.projection_apply c)
  have hinj (z : E) (hz : z ∈ κ.target) :
      Injective (mfderiv IB 𝓘(ℝ, EB) (h.codChart.extend IB) (p (κ.symm z))) :=
    (isInvertible_mfderiv_extend hψ (h.source_subset_preimage_source (hsrc z hz))).injective
  -- Vectors that `p` reads as vertical lie in the kernel of the form in the chart.
  have hker (z : E) (hz : z ∈ κ.target) (w : E) (hw : (h.equiv w).1 = 0) :
      (α z).curryLeft w = 0 := by
    have h0 : mfderiv I IB p (κ.symm z) (mfderiv 𝓘(ℝ, E) I κ.symm z w) = 0 :=
      hinj z hz ((hP z hz w).trans (hw.trans (map_zero _).symm))
    have hk : mfderiv 𝓘(ℝ, E) I κ.symm z w ∈ LinearMap.ker (σ.bilinFormAt (κ.symm z)) := by
      rw [← hp.ker_mfderiv]
      exact LinearMap.mem_ker.2 h0
    refine ContinuousAlternatingMap.ext fun u ↦ ?_
    rw [ContinuousAlternatingMap.curryLeft_apply_apply, hα, ContinuousAlternatingMap.coe_zero,
      Pi.zero_apply]
    have h1 := LinearMap.congr_fun (LinearMap.mem_ker.1 hk) (mfderiv 𝓘(ℝ, E) I κ.symm z (u 0))
    rw [bilinFormAt_apply, SmoothBundleForm.eval₂_apply] at h1
    convert h1 using 2
    funext i
    fin_cases i <;> simp
  -- At points of the fibre through `x`, `fibreForm` is the form in the chart, evaluated on
  -- fixed lifts of the arguments.
  have hstar (z : E) (hz : z ∈ κ.target) (hpz : p (κ.symm z) = p x) :
      hp.fibreForm (κ.symm z) = fun a ↦ α z fun i ↦
        h.equiv.symm (mfderiv IB 𝓘(ℝ, EB) (h.codChart.extend IB) (p x) (a i), 0) := by
    funext a
    rw [hα, fibreForm]
    refine hp.apply_eq_of_mfderiv_eq fun i ↦ hinj z hz ?_
    rw [hP z hz, ContinuousLinearEquiv.apply_symm_apply]
    refine (congrArg _ (surjInv_eq _ _)).trans ?_
    rw [hpz]
  -- Near `x`, in a ball inside the chart's image, the fibre through `x` is the slice of points
  -- whose image under `h.equiv` has the first component of `κ x`.
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU (κ x) (κ.map_source hx)
  have hnhds : κ ⁻¹' Metric.ball (κ x) r ∩ κ.source ∈ 𝓝 x :=
    inter_mem ((h.domChart.continuousAt_extend h.mem_domChart_source).preimage_mem_nhds
      (Metric.ball_mem_nhds _ hr)) (h.domChart.isOpen_extend_source.mem_nhds hx)
  filter_upwards [hnhds] with y ⟨hyb, hy⟩ hpy
  have hyx : κ.symm (κ y) = y := κ.left_inv hy
  have hxx : κ.symm (κ x) = x := κ.left_inv hx
  have hfst : (h.equiv (κ y - κ x)).1 = 0 := by
    have hy' : y ∈ h.domChart.source := by simpa [κ] using hy
    rw [map_sub, Prod.fst_sub, ← h.projection_apply, ← h.projection_apply,
      ← h.codChart_extend_apply hy', ← h.codChart_extend_apply h.mem_domChart_source, hpy,
      sub_self]
  -- The form in the chart takes the same value at `κ x` and `κ y`.
  have hαeq : α (κ y) = α (κ x) := by
    have hκ : ContMDiffOn 𝓘(ℝ, E) I ∞ κ.symm κ.target := by
      simpa only [κ, h.domChart.extend_target'] using
        contMDiffOn_extend_symm h.domChart_mem_maximalAtlas
    have := apply_add_eq_of_extDeriv_eq_zero hU
      (fun z hz ↦ ((σ.contDiffOn_mpullback hU hκ).contDiffAt (hU.mem_nhds hz)).differentiableAt
        (by simp))
      (fun z hz ↦ hσ.extDeriv_mpullback_eq_zero ((hκ.contMDiffAt (hU.mem_nhds hz)).of_le
        (by simp)))
      (fun z' hz' ↦ hker z' hz' _ hfst) fun t ht ↦
        hball ((convex_ball _ _).add_smul_sub_mem (Metric.mem_ball_self hr) hyb ht)
    rwa [add_sub_cancel] at this
  calc hp.fibreForm y = hp.fibreForm (κ.symm (κ y)) := by rw [hyx]
    _ = hp.fibreForm (κ.symm (κ x)) := by
      rw [hstar _ (hball hyb) (by rw [hyx, hpy]), hstar _ (κ.map_source hx) (by rw [hxx]), hαeq]
    _ = hp.fibreForm x := by rw [hxx]

/-- **A closed form is basic for its characteristic submersions.** If `p` is a characteristic
submersion of a closed two-form `σ` on a boundaryless manifold, then `σ_x (u, v) = σ_y (u', v')`
whenever `p x = p y`, `dp_x u = dp_y u'` and `dp_x v = dp_y v'`. -/
theorem isBasic (hp : IsCharacteristicSubmersion IB σ p) (hσ : σ.IsClosed) :
    RoughForm.IsBasic IB p σ.val := by
  -- `fibreForm` is locally constant along each fibre, which is preconnected.
  have hconst (b : B) (y : M) (hy : p y = b) (y' : M) (hy' : p y' = b) :
      hp.fibreForm y = hp.fibreForm y' := by
    have := isPreconnected_iff_preconnectedSpace.1 (hp.isPreconnected_preimage_singleton b)
    have hlc : IsLocallyConstant fun z : p ⁻¹' {b} ↦ hp.fibreForm z := by
      refine (IsLocallyConstant.iff_eventually_eq _).2 fun z ↦ ?_
      filter_upwards [(continuous_subtypeVal.tendsto z).eventually
        (hp.eventually_fibreForm_eq hσ z)] with z' hz'
      exact hz' (z'.prop.trans z.prop.symm)
    exact hlc.apply_eq_of_preconnectedSpace ⟨y, hy⟩ ⟨y', hy'⟩
  refine RoughForm.isBasic_iff.2 fun x y hxy v w hvw ↦ ?_
  rw [← hp.fibreForm_mfderiv x v, ← hp.fibreForm_mfderiv y w, hconst (p y) x hxy y rfl]
  -- `tangentSpaceCast` is the identity of the model space `EB` of `B`.
  exact congrArg _ (funext hvw)

/-- **Descent along a characteristic submersion.** A closed two-form `σ` on a boundaryless manifold
is the pullback `p^* τ` of a unique symplectic form `τ` on the base of each of its characteristic
submersions `p`. -/
theorem existsUnique_isSymplectic_mpullback_eq [IsManifold IB ∞ B]
    (hp : IsCharacteristicSubmersion IB σ p) (hσ : σ.IsClosed) :
    ∃! τ : SmoothTwoForm IB B, τ.IsSymplectic ∧
      SmoothForm.mpullback p hp.isSubmersion.contMDiff τ = σ :=
  SmoothTwoForm.existsUnique_isSymplectic_mpullback_eq hp.isSubmersion hp.surjective hσ
    (hp.isBasic hσ) fun x ↦ (hp.ker_mfderiv x).symm

end IsCharacteristicSubmersion

/-- For a nondegenerate two-form `τ` on `B` and a real normed space `F`, the projection `B × F → B`
is a characteristic submersion of the pullback of `τ`. -/
example {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [IsManifold IB ∞ B]
    {τ : SmoothTwoForm IB B} (hτ : τ.IsNondegenerate) :
    IsCharacteristicSubmersion IB
      (SmoothForm.mpullback (I := IB.prod 𝓘(ℝ, F)) Prod.fst contMDiff_fst τ)
      (Prod.fst : B × F → B) where
  isSubmersion := Manifold.isSubmersion_fst
  surjective := Prod.fst_surjective
  isPreconnected_preimage_singleton b := by
    rw [← prod_univ]
    exact isPreconnected_singleton.prod isPreconnected_univ
  ker_mfderiv z := ((SmoothTwoForm.isNondegenerate_iff_forall_ker_bilinFormAt_mpullback
    contMDiff_fst Prod.fst_surjective fun _ ↦ by
      rw [mfderiv_fst]; exact fun a ↦ ⟨(a, 0), rfl⟩).1 hτ z).symm

end TauCeti.SmoothForm
