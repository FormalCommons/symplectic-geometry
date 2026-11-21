/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Basic
public import TauCeti.Geometry.Symplectic.Lagrangian.Presymplectic
public import TauCeti.Geometry.Symplectic.Manifold.Descent
import SymplecticGeometry.Analysis.Calculus.DifferentialForm.LieDeriv
import SymplecticGeometry.LinearAlgebra.Symplectic.Subspace
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.ModelSpace
import TauCeti.Geometry.Manifold.Diffeomorph.NormedSpace
import TauCeti.Geometry.Manifold.Distribution.FlatChart
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Manifold.Submersion.Split
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
import TauCeti.Geometry.Symplectic.Manifold.Opens
import TauCeti.LinearAlgebra.Alternating.Conormal
import TauCeti.LinearAlgebra.Alternating.Curry

/-!
# Characteristic foliations and local symplectic quotients

Let `σ` be a closed two-form on a boundaryless manifold `M`. A *characteristic submersion* of `σ`
is a surjective smooth submersion `p : M → B` with preconnected fibres whose derivative at each
point has the kernel of `σ` there as its kernel
(`TauCeti.SmoothForm.IsCharacteristicSubmersion`). Its fibres are unions of leaves of the
characteristic foliation of `σ`. On an open subset of `M`, a local version of it is the
foliation-compatible chart that gives the local symplectic quotients of a presymplectic manifold
[McDuffSalamon2017, §3.4].

The first result is that `σ` descends: it is the pullback `p^* τ` of a unique symplectic form `τ`
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

The second result is that characteristic submersions exist locally when the kernels of `σ` have
constant dimension `k` and `dim M = k + 2r`
(`TauCeti.SmoothForm.exists_isCharacteristicSubmersion`): every point has a neighbourhood `U`
diffeomorphic to the product of the unit balls of `ℝᵏ` and `ℝ²ʳ`, by a diffeomorphism whose second
component is a characteristic submersion of `σ` on `U`. The kernels of `σ` form an involutive
distribution (Tau Ceti's `TauCeti.SmoothForm.isInvolutiveDistribution_ker_bilinFormAt`), so the
Frobenius theorem (`TauCeti.IsInvolutiveDistribution.exists_flatChart`) gives a chart in which
they are a constant subspace `W`. Split the model space as `W ⊕ C`, identify `W` with `ℝᵏ` and `C`
with `ℝ²ʳ`, then translate and rescale so that the chart covers the unit ball, and restrict to its
preimage. In these coordinates the fibres of the second projection are slices `ball × {b}`, which
are convex.

For a coisotropic immersion `f : N → M` into a symplectic manifold, this applies to `f^* ω`, whose
kernels have dimension `dim M - dim N`, and `df` carries those kernels onto isotropic subspaces.
Both statements are in the namespace `TauCeti.SmoothTwoForm.IsNondegenerate`:
`IsCoisotropicMap.exists_isCharacteristicSubmersion` and
`IsCoisotropicMap.isIsotropic_map_ker_bilinFormAt_mpullback`.

## Main definitions

* `TauCeti.SmoothForm.IsCharacteristicSubmersion`: a surjective submersion with preconnected
  fibres whose vertical spaces are the kernels of `σ`.

## Main results

* `TauCeti.SmoothForm.IsCharacteristicSubmersion.isBasic`: a closed form is basic for each of its
  characteristic submersions.
* `TauCeti.SmoothForm.IsCharacteristicSubmersion.existsUnique_isSymplectic_mpullback_eq`: it is
  the pullback of a unique symplectic form on the base.
* `TauCeti.SmoothForm.exists_isCharacteristicSubmersion`: characteristic charts onto a product of
  balls, around every point, for a closed form of constant rank.
* `TauCeti.SmoothForm.exists_isCharacteristicSubmersion_and_existsUnique_mpullback_eq`: the three
  statements together: involutivity, characteristic charts, and local symplectic quotients.
* `IsCoisotropicMap.exists_isCharacteristicSubmersion` and
  `IsCoisotropicMap.isIsotropic_map_ker_bilinFormAt_mpullback`, in the namespace
  `TauCeti.SmoothTwoForm.IsNondegenerate`: the case of a coisotropic submanifold, whose
  characteristic leaves are isotropic.

The projection `B × F → B` with a form pulled back from a nondegenerate form on `B` is an
example.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §3.4
  (Exercise 3.4.9, characteristic foliations of coisotropic submanifolds)
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Theorem 14.35
  (Cartan's formula) and Theorem 19.12 (the Frobenius theorem)
-/

public section

noncomputable section

open Set Filter Function Manifold Bundle Module TopologicalSpace SymplecticGeometry
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

/-! ### Characteristic charts -/

section Charts

variable [FiniteDimensional ℝ E] [I.Boundaryless]
  {F₁ F₂ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [NormedAddCommGroup F₂]
  [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]

/-- A partial diffeomorphism `Φ` onto a neighbourhood of the unit ball of `F₁ × F₂`, whose
derivative carries the kernel of `σ` onto the vectors with second component `0`, restricts to a
diffeomorphism from an open `U ⊆ M` onto the product of the unit balls whose second component is a
characteristic submersion of `σ` on `U`. -/
private theorem exists_isCharacteristicSubmersion_of_partialDiffeomorph
    (σ : SmoothForm I M ℝ 2) (Φ : PartialDiffeomorph I 𝓘(ℝ, F₁ × F₂) M (F₁ × F₂) ∞) {x : M}
    (hx : x ∈ Φ.source) (h0 : Φ x = 0) (hball : Metric.ball 0 1 ⊆ Φ.target)
    (hker : ∀ y ∈ Φ.source, ∀ v : TangentSpace I y,
      (mfderiv I 𝓘(ℝ, F₁ × F₂) Φ y v).2 = 0 ↔ v ∈ LinearMap.ker (σ.bilinFormAt y)) :
    ∃ (U : Opens M) (hxU : x ∈ U) (Ψ : U ≃ₘ^∞⟮I, 𝓘(ℝ, F₁ × F₂)⟯
        (⟨Metric.ball 0 1 ×ˢ Metric.ball 0 1, Metric.isOpen_ball.prod Metric.isOpen_ball⟩ :
          Opens (F₁ × F₂))),
      (Ψ ⟨x, hxU⟩ : F₁ × F₂) = 0 ∧
      IsCharacteristicSubmersion 𝓘(ℝ, F₂)
        (SmoothForm.mpullback (Subtype.val : U → M) contMDiff_subtypeVal σ)
        (fun u ↦ (⟨(Ψ u : F₁ × F₂).2, (Ψ u).property.2⟩ :
          (⟨Metric.ball 0 1, Metric.isOpen_ball⟩ : Opens F₂))) := by
  let V : Opens (F₁ × F₂) :=
    ⟨Metric.ball 0 1 ×ˢ Metric.ball 0 1, Metric.isOpen_ball.prod Metric.isOpen_ball⟩
  have hV : (V : Set (F₁ × F₂)) = Metric.ball 0 1 := ball_prod_same _ _ _
  have hs : IsOpen (Φ.source ∩ Φ ⁻¹' V) :=
    Φ.contMDiffOn.continuousOn.isOpen_inter_preimage Φ.open_source V.isOpen
  let Φ' := Φ.restrOpen _ hs
  have htarget (v) : v ∈ Φ'.target ↔ v ∈ V := by
    rw [Φ.restrOpen_target]
    refine ⟨fun hv ↦ Φ.right_inv hv.1 ▸ hv.2.2, fun hv ↦ ?_⟩
    have hvt : v ∈ Φ.target := hball (hV ▸ hv)
    exact ⟨hvt, Φ.map_target hvt, by simpa [Φ.right_inv hvt] using hv⟩
  let U : Opens M := ⟨Φ'.source, Φ'.open_source⟩
  let Ψ : U ≃ₘ^∞⟮I, 𝓘(ℝ, F₁ × F₂)⟯ V :=
    Φ'.toDiffeomorphSourceTarget.trans
      (Diffeomorph.subtype (Diffeomorph.refl _ _ ∞) fun v ↦ htarget v)
  have hΨ (u : U) : (Ψ u : F₁ × F₂) = Φ u := by
    rw [Diffeomorph.coe_trans, Function.comp_apply]
    refine (Diffeomorph.subtype_apply_coe _ _ _).trans ?_
    rw [Diffeomorph.coe_refl, id, PartialDiffeomorph.toDiffeomorphSourceTarget_apply_coe,
      PartialDiffeomorph.coe_restrOpen]
  have hU (y : M) : y ∈ U ↔ y ∈ Φ.source ∧ Φ y ∈ V := by
    simp [U, Φ']
  have hxU : x ∈ U := (hU x).2 ⟨hx, by simp [h0, V]⟩
  have huΦ (u : U) : (u : M) ∈ Φ.source := ((hU u).1 u.property).1
  refine ⟨U, hxU, Ψ, by rw [hΨ, h0], ?_⟩
  let B : Opens F₂ := ⟨Metric.ball 0 1, Metric.isOpen_ball⟩
  let p : U → B := fun u ↦ ⟨(Ψ u : F₁ × F₂).2, (Ψ u).property.2⟩
  -- The derivative of `p` is the second component of the derivative of `Φ`.
  have hderiv (u : U) (v : TangentSpace I u) :
      mfderiv I 𝓘(ℝ, F₂) p u v = (mfderiv I 𝓘(ℝ, F₁ × F₂) Φ u v).2 := by
    have hD := (ContinuousLinearMap.snd ℝ F₁ F₂).hasMFDerivAt.comp (u : M)
      (Φ.mdifferentiableAt (by simp) (huΦ u)).hasMFDerivAt
    have h := TauCeti.Manifold.tangentSpaceOpenEquiv_mfderiv_apply (I := I) (I' := 𝓘(ℝ, F₂))
      (f := p) (A := ContinuousLinearMap.snd ℝ F₁ F₂ ∘ Φ)
      (funext fun u ↦ congrArg Prod.snd (hΨ u)) v
    rw [TauCeti.Manifold.tangentSpaceOpenEquiv_apply, TauCeti.Manifold.tangentSpaceOpenEquiv_apply,
      hD.mfderiv] at h
    exact h
  have hpc : ContMDiff I 𝓘(ℝ, F₂) ∞ p :=
    (ContMDiff.subtypeVal_comp_iff _ _).1
      ((contDiff_snd.contMDiff.comp contMDiff_subtypeVal).comp Ψ.contMDiff)
  have hsurj (u : U) : Surjective (mfderiv I 𝓘(ℝ, F₂) p u) := fun w ↦ by
    obtain ⟨v, hv⟩ := (Φ.isInvertible_mfderiv (by simp) (huΦ u)).surjective (0, w)
    exact ⟨v, (hderiv u v).trans (congrArg Prod.snd hv)⟩
  refine ⟨(hpc.isSubmersionOfComplement_of_surjective_mfderiv (by simp) hsurj).isSubmersion,
    fun b ↦ ?_, fun b ↦ ?_, fun u ↦ ?_⟩
  · have hb : ((0 : F₁), (b : F₂)) ∈ V := ⟨by simp, b.property⟩
    exact ⟨Ψ.symm ⟨_, hb⟩, Subtype.ext (by simp)⟩
  · -- The fibre is the image under `Ψ⁻¹` of the slice `ball × {b}`, which is convex.
    let S : Set V := {v | (v : F₁ × F₂).2 = b}
    have hS : Subtype.val '' S = Metric.ball 0 1 ×ˢ {(b : F₂)} := by
      ext ⟨a, c⟩
      simp only [S, mem_image, Subtype.exists, exists_and_right, exists_eq_right, mem_prod,
        mem_singleton_iff]
      exact ⟨fun ⟨h, hc⟩ ↦ ⟨h.1, hc⟩, fun ⟨ha, hc⟩ ↦ ⟨⟨ha, hc ▸ b.property⟩, hc⟩⟩
    have hpS : p ⁻¹' {b} = Ψ.toHomeomorph.symm '' S := by
      rw [Homeomorph.image_symm]; ext u; simp [p, S, Subtype.ext_iff]
    rw [hpS]
    refine IsPreconnected.image ?_ _ Ψ.toHomeomorph.symm.continuous.continuousOn
    rw [← Topology.IsInducing.subtypeVal.isPreconnected_image]
    convert (convex_ball (0 : F₁) 1).isPreconnected.prod
      (isPreconnected_singleton (x := (b : F₂)))
  · ext v
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hderiv,
      SmoothTwoForm.bilinFormAt_mpullback_subtype_val]
    exact hker u (huΦ u) v

/-- Near each point, a closed two-form `σ` whose kernels all have dimension `k`, on a manifold of
dimension `k + 2r`, has a chart `Φ` into `ℝᵏ × ℝ²ʳ`, sending the point to `0` and with the unit ball
in its image, whose derivative carries the kernel of `σ` onto the vectors with second component
`0`. -/
private theorem exists_partialDiffeomorph_flat (σ : SmoothForm I M ℝ 2) (hσ : σ.IsClosed)
    {k r : ℕ} (hk : ∀ x, finrank ℝ (LinearMap.ker (σ.bilinFormAt x)) = k)
    (hr : finrank ℝ E = k + 2 * r) (x : M) :
    ∃ Φ : PartialDiffeomorph I 𝓘(ℝ, EuclideanSpace ℝ (Fin k) × StdSpace (Fin r)) M
        (EuclideanSpace ℝ (Fin k) × StdSpace (Fin r)) ∞,
      x ∈ Φ.source ∧ Φ x = 0 ∧ Metric.ball 0 1 ⊆ Φ.target ∧
        ∀ y ∈ Φ.source, ∀ v : TangentSpace I y,
          (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin k) × StdSpace (Fin r)) Φ y v).2 = 0 ↔
            v ∈ LinearMap.ker (σ.bilinFormAt y) := by
  have : IsManifold I (∞ + 1) M := IsManifold.of_le (n := ∞) (by simp)
  -- A flat chart `e` of the kernel distribution at `x`: `d(I ∘ e)` carries the kernels onto `W`.
  obtain ⟨e, W, he, hxe, hW, hflat⟩ :=
    (isInvolutiveDistribution_ker_bilinFormAt σ hσ).exists_flatChart (m := ⊤) le_top
      (n := ∞) (by simp) (isContMDiffDistribution_ker_bilinFormAt σ hk)
      (BoundarylessManifold.isInteriorPoint (I := I) (x := x))
  -- A splitting `A : E ≃ ℝᵏ × ℝ²ʳ` that carries `W` onto the first factor.
  obtain ⟨C, hWC⟩ := W.exists_isCompl
  have hC : finrank ℝ C = finrank ℝ (StdSpace (Fin r)) := by
    have := Submodule.finrank_add_eq_of_isCompl hWC
    rw [finrank_stdSpace, Fintype.card_fin]; omega
  let A : E ≃L[ℝ] EuclideanSpace ℝ (Fin k) × StdSpace (Fin r) :=
    (Submodule.prodEquivOfIsCompl W C hWC).symm.toContinuousLinearEquiv.trans
      ((ContinuousLinearEquiv.ofFinrankEq (by simp [hW])).prodCongr
        (ContinuousLinearEquiv.ofFinrankEq hC))
  have hA (z : E) : (A z).2 = 0 ↔ z ∈ W := by
    simp only [A, ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.prodCongr_apply,
      LinearEquiv.coe_toContinuousLinearEquiv', ContinuousLinearEquiv.map_eq_zero_iff,
      Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero]
  let κ := e.toPartialDiffeomorphOfMemMaximalAtlas he
  have hκ : (κ : M → E) = I ∘ e := e.coe_toPartialDiffeomorphOfMemMaximalAtlas he
  have hxκ : x ∈ κ.source := by simpa [κ] using hxe
  -- `Φ` is `κ` followed by the affine map `z ↦ ε⁻¹ • A (z - κ x)`, with `ε` small enough.
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (A.toHomeomorph.isOpenMap _ κ.open_target)
    (A (κ x)) (mem_image_of_mem _ (κ.map_source hxκ))
  let G : E ≃ₘ^∞⟮𝓘(ℝ, E), 𝓘(ℝ, EuclideanSpace ℝ (Fin k) × StdSpace (Fin r))⟯
      EuclideanSpace ℝ (Fin k) × StdSpace (Fin r) :=
    (A.toContDiffDiffeomorph ∞).trans
      (Diffeomorph.smulAdd ∞ ε⁻¹ (-(ε⁻¹ • A (κ x))) (inv_ne_zero hε.ne'))
  have hG (z : E) : G z = ε⁻¹ • (A z - A (κ x)) := by simp [G, sub_eq_add_neg]
  have hGs (v) : G.symm v = A.symm (ε • v + A (κ x)) := by
    simp [G, smul_add, smul_smul, hε.ne']
  let Φ := κ.trans G.toPartialDiffeomorph
  have hΦ : (Φ : M → EuclideanSpace ℝ (Fin k) × StdSpace (Fin r)) =
      (fun z ↦ ε⁻¹ • (A z - A (κ x))) ∘ (I ∘ e) := by
    ext1 y; simp [Φ, hG, hκ]
  refine ⟨Φ, by simpa [Φ] using hxκ, by simp [hΦ, ← hκ], fun v hv ↦ ?_, fun y hy v ↦ ?_⟩
  · have hv' : ε • v + A (κ x) ∈ Metric.ball (A (κ x)) ε := by
      rw [mem_ball_zero_iff] at hv
      simpa [norm_smul, abs_of_pos hε] using mul_lt_of_lt_one_right hε hv
    obtain ⟨z, hz, hz'⟩ := hball hv'
    have : G.symm v ∈ κ.target := by rw [hGs, ← hz']; simpa using hz
    simpa [Φ] using this
  · have hye : y ∈ e.source := by simpa [Φ, κ] using hy
    have hd : MDifferentiableAt I 𝓘(ℝ, E) (I ∘ e) y := by
      rw [← hκ]
      exact κ.mdifferentiableAt (by simp) (by simpa [κ] using hye)
    have hg : HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin k) × StdSpace (Fin r))
        (fun z ↦ ε⁻¹ • (A z - A (κ x))) ((I ∘ e) y)
        (ε⁻¹ • (A : E →L[ℝ] EuclideanSpace ℝ (Fin k) × StdSpace (Fin r))) :=
      ((A.hasFDerivAt.sub_const _).const_smul ε⁻¹).hasMFDerivAt
    have hinj : Injective (mfderiv I 𝓘(ℝ, E) (I ∘ e) y) := by
      rw [← hκ]; exact (κ.isInvertible_mfderiv (by simp) (by simpa [κ] using hye)).injective
    rw [hΦ, (hg.comp y hd.hasMFDerivAt).mfderiv]
    -- The derivatives land in tangent spaces of normed spaces, which are the spaces themselves;
    -- `change` reads the composite as a plain composite, which `rw` cannot reach through them.
    change (ε⁻¹ • A (mfderiv I 𝓘(ℝ, E) (I ∘ e) y v)).2 = 0 ↔ _
    simp only [Prod.smul_snd,
      smul_eq_zero, inv_eq_zero, hε.ne', false_or]
    refine (hA _).trans ?_
    rw [← hflat y hye]
    exact ⟨fun ⟨w, hw, hwv⟩ ↦ hinj hwv ▸ hw, fun h ↦ ⟨v, h, rfl⟩⟩


/-- **Characteristic charts.** Let `σ` be a closed two-form on a boundaryless manifold of dimension
`k + 2r` whose kernels all have dimension `k`. Every point `x` has an open neighbourhood `U` with a
diffeomorphism `Ψ` onto the product of the open unit balls of `ℝᵏ` and of `ℝ²ʳ = StdSpace (Fin r)`,
sending `x` to `0`, whose second component is a characteristic submersion of the restriction of
`σ` to `U`. The first component gives coordinates along the leaves of the characteristic
foliation. -/
theorem exists_isCharacteristicSubmersion (σ : SmoothForm I M ℝ 2) (hσ : σ.IsClosed) {k r : ℕ}
    (hk : ∀ x, finrank ℝ (LinearMap.ker (σ.bilinFormAt x)) = k)
    (hr : finrank ℝ E = k + 2 * r) (x : M) :
    ∃ (U : Opens M) (hx : x ∈ U)
      (Ψ : U ≃ₘ^∞⟮I, 𝓘(ℝ, EuclideanSpace ℝ (Fin k) × StdSpace (Fin r))⟯
        (⟨Metric.ball 0 1 ×ˢ Metric.ball 0 1, Metric.isOpen_ball.prod Metric.isOpen_ball⟩ :
          Opens (EuclideanSpace ℝ (Fin k) × StdSpace (Fin r)))),
      (Ψ ⟨x, hx⟩ : EuclideanSpace ℝ (Fin k) × StdSpace (Fin r)) = 0 ∧
      IsCharacteristicSubmersion 𝓘(ℝ, StdSpace (Fin r))
        (SmoothForm.mpullback (Subtype.val : U → M) contMDiff_subtypeVal σ)
        (fun u ↦ (⟨(Ψ u : EuclideanSpace ℝ (Fin k) × StdSpace (Fin r)).2, (Ψ u).property.2⟩ :
          (⟨Metric.ball 0 1, Metric.isOpen_ball⟩ : Opens (StdSpace (Fin r))))) := by
  obtain ⟨Φ, hx, h0, hball, hker⟩ := exists_partialDiffeomorph_flat σ hσ hk hr x
  exact exists_isCharacteristicSubmersion_of_partialDiffeomorph σ Φ hx h0 hball hker

/-- **Local symplectic quotients of a presymplectic form.** Let `σ` be a closed two-form on a
boundaryless manifold of dimension `k + 2r` whose kernels all have dimension `k`. Then:
* the kernels of `σ` form an involutive distribution;
* every point `x` has an open neighbourhood `U` with a diffeomorphism `Ψ` onto the product of the
  unit balls of `ℝᵏ` and `ℝ²ʳ`, sending `x` to `0`, whose second component is a characteristic
  submersion of `σ` on `U` (`exists_isCharacteristicSubmersion`): a surjective submersion onto the
  ball with connected fibres whose vertical spaces are the kernels of `σ`;
* for every open `U ⊆ M`, every open `B ⊆ ℝ²ʳ` and every characteristic submersion `p : U → B` of
  `σ` on `U`, there is a unique symplectic form `τ` on `B` with `p^* τ = σ` on `U`.

Milestone: *Characteristic foliations and local symplectic quotients*. -/
theorem exists_isCharacteristicSubmersion_and_existsUnique_mpullback_eq (σ : SmoothForm I M ℝ 2)
    (hσ : σ.IsClosed) {k r : ℕ} (hk : ∀ x, finrank ℝ (LinearMap.ker (σ.bilinFormAt x)) = k)
    (hr : finrank ℝ E = k + 2 * r) :
    IsInvolutiveDistribution I (fun x ↦ LinearMap.ker (σ.bilinFormAt x)) ∧
    (∀ x : M, ∃ (U : Opens M) (hx : x ∈ U)
      (Ψ : U ≃ₘ^∞⟮I, 𝓘(ℝ, EuclideanSpace ℝ (Fin k) × StdSpace (Fin r))⟯
        (⟨Metric.ball 0 1 ×ˢ Metric.ball 0 1, Metric.isOpen_ball.prod Metric.isOpen_ball⟩ :
          Opens (EuclideanSpace ℝ (Fin k) × StdSpace (Fin r)))),
      (Ψ ⟨x, hx⟩ : EuclideanSpace ℝ (Fin k) × StdSpace (Fin r)) = 0 ∧
      IsCharacteristicSubmersion 𝓘(ℝ, StdSpace (Fin r))
        (SmoothForm.mpullback (Subtype.val : U → M) contMDiff_subtypeVal σ)
        (fun u ↦ (⟨(Ψ u : EuclideanSpace ℝ (Fin k) × StdSpace (Fin r)).2, (Ψ u).property.2⟩ :
          (⟨Metric.ball 0 1, Metric.isOpen_ball⟩ : Opens (StdSpace (Fin r)))))) ∧
    ∀ (U : Opens M) (B : Opens (StdSpace (Fin r))) (p : U → B)
      (hp : IsCharacteristicSubmersion 𝓘(ℝ, StdSpace (Fin r))
        (SmoothForm.mpullback (Subtype.val : U → M) contMDiff_subtypeVal σ) p),
      ∃! τ : SmoothTwoForm 𝓘(ℝ, StdSpace (Fin r)) B, τ.IsSymplectic ∧
        SmoothForm.mpullback p hp.isSubmersion.contMDiff τ =
          SmoothForm.mpullback (Subtype.val : U → M) contMDiff_subtypeVal σ :=
  ⟨isInvolutiveDistribution_ker_bilinFormAt σ hσ,
    exists_isCharacteristicSubmersion σ hσ hk hr,
    fun _ _ _ hp ↦ hp.existsUnique_isSymplectic_mpullback_eq (hσ.mpullback _ _)⟩

end Charts

end TauCeti.SmoothForm

/-! ### Coisotropic submanifolds -/

namespace TauCeti.SmoothTwoForm.IsNondegenerate

variable {E H M F H' N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  {σ : SmoothTwoForm I M} {hσ : σ.IsNondegenerate} {f : N → M}

/-- **Characteristic charts of a coisotropic submanifold.** Let `f : N → M` be a coisotropic
immersion of a boundaryless manifold of dimension `(dim M - dim N) + 2r` for a closed nondegenerate
two-form `σ`. Around every point `q` of `N` there is a characteristic chart of the presymplectic
form `f^* σ`, as in `TauCeti.SmoothForm.exists_isCharacteristicSubmersion`, with leaves of
dimension `dim M - dim N`. -/
theorem IsCoisotropicMap.exists_isCharacteristicSubmersion [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] [J.Boundaryless] (h : hσ.IsCoisotropicMap J f)
    (hi : IsImmersion J I ∞ f) (hf : ContMDiff J I ∞ f) (hσc : σ.IsClosed) {r : ℕ}
    (hr : finrank ℝ F = (finrank ℝ E - finrank ℝ F) + 2 * r) (q : N) :
    ∃ (U : Opens N) (hq : q ∈ U)
      (Ψ : U ≃ₘ^∞⟮J, 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E - finrank ℝ F)) ×
          StdSpace (Fin r))⟯
        (⟨Metric.ball 0 1 ×ˢ Metric.ball 0 1, Metric.isOpen_ball.prod Metric.isOpen_ball⟩ :
          Opens (EuclideanSpace ℝ (Fin (finrank ℝ E - finrank ℝ F)) × StdSpace (Fin r)))),
      (Ψ ⟨q, hq⟩ : EuclideanSpace ℝ (Fin (finrank ℝ E - finrank ℝ F)) × StdSpace (Fin r)) = 0 ∧
      SmoothForm.IsCharacteristicSubmersion 𝓘(ℝ, StdSpace (Fin r))
        (SmoothForm.mpullback (Subtype.val : U → N) contMDiff_subtypeVal
          (SmoothForm.mpullback f hf σ))
        (fun u ↦ (⟨(Ψ u : EuclideanSpace ℝ (Fin (finrank ℝ E - finrank ℝ F)) ×
            StdSpace (Fin r)).2, (Ψ u).property.2⟩ :
          (⟨Metric.ball 0 1, Metric.isOpen_ball⟩ : Opens (StdSpace (Fin r))))) :=
  (SmoothForm.mpullback f hf σ).exists_isCharacteristicSubmersion (hσc.mpullback f hf)
    (h.finrank_ker_bilinFormAt_mpullback hi hf) hr q

/-- **The characteristic leaves of a coisotropic submanifold are isotropic.** For a coisotropic map
`f`, the differential `df_x` carries the kernel of `f^* σ` at `x`, the tangent space of the
characteristic foliation, onto an isotropic subspace of `(T_(f x) M, σ_(f x))`. By
`IsCoisotropicMap.map_ker_bilinFormAt_mpullback`, this subspace is `(df_x(T_x N))^σ`.

Milestone: *Characteristic foliations and local symplectic quotients*. -/
theorem IsCoisotropicMap.isIsotropic_map_ker_bilinFormAt_mpullback (h : hσ.IsCoisotropicMap J f)
    (hf : ContMDiff J I ∞ f) (x : N) :
    (hσ.symplecticFormAt (f x)).IsIsotropic
      ((LinearMap.ker ((SmoothForm.mpullback f hf σ).bilinFormAt x)).map
        (mfderiv J I f x).toLinearMap) := by
  rw [h.map_ker_bilinFormAt_mpullback hf x]
  exact (isCoisotropicMap_iff.1 h x).isIsotropic_orthogonal

end TauCeti.SmoothTwoForm.IsNondegenerate
