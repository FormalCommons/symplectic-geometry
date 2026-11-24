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
import SymplecticGeometry.Geometry.Manifold.Distribution.FlatChart
import SymplecticGeometry.Geometry.Manifold.IsManifold.InteriorBoundary
import SymplecticGeometry.LinearAlgebra.Symplectic.Subspace
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.ModelSpace
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Manifold.Submersion.Split
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
import TauCeti.Geometry.Symplectic.Manifold.Darboux
import TauCeti.Geometry.Symplectic.Manifold.Opens
import TauCeti.LinearAlgebra.Alternating.Conormal
import TauCeti.LinearAlgebra.Alternating.Curry
import SymplecticGeometry.Geometry.Manifold.IsManifold.Basic
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Opens

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
distribution (Tau Ceti's `TauCeti.SmoothForm.isInvolutiveDistribution_ker_bilinFormAt`), so
`TauCeti.IsInvolutiveDistribution.exists_flatPartialDiffeomorph`, a form of the Frobenius theorem,
gives a partial diffeomorphism into `ℝᵏ × ℝ²ʳ`, centred at the point and with the unit ball in its
target, whose derivative sends the kernels to the vectors with second component `0`. Restrict it
to the preimage of the unit ball (`PartialDiffeomorph.exists_diffeomorph_ball_prod_ball`).
In these coordinates the fibres of the second projection are slices `ball × {b}`, which are
convex.

Combined with a Darboux chart of the descended form on the ball, a characteristic chart gives
Darboux coordinates for a closed form of constant rank
(`TauCeti.SmoothForm.exists_partialDiffeomorph_eval₂_eq_stdForm`): a chart centred at a given
point in which the form is the pullback of `stdForm (Fin r)` along a linear projection onto
`StdSpace (Fin r)`.

For a coisotropic immersion `f : N → M` into a symplectic manifold, this applies to `f^* ω`, whose
kernels have dimension `dim M - dim N`, and `df` carries those kernels onto isotropic subspaces.
These statements are in the namespace `TauCeti.SmoothTwoForm.IsNondegenerate`:
`IsCoisotropicMap.exists_isCharacteristicSubmersion`, its Darboux form
`IsCoisotropicMap.exists_partialDiffeomorph_eval₂_eq_stdForm`, and
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
* The three statements together, involutivity, characteristic charts and local symplectic
  quotients:
  `TauCeti.SmoothForm.exists_isCharacteristicSubmersion_and_existsUnique_isSymplectic_mpullback_eq`
* `TauCeti.SmoothForm.exists_partialDiffeomorph_eval₂_eq_stdForm`: Darboux coordinates for a
  closed form of constant rank.
* `IsCoisotropicMap.exists_isCharacteristicSubmersion`,
  `IsCoisotropicMap.exists_partialDiffeomorph_eval₂_eq_stdForm` and
  `IsCoisotropicMap.isIsotropic_map_ker_bilinFormAt_mpullback`, in the namespace
  `TauCeti.SmoothTwoForm.IsNondegenerate`: the case of a coisotropic submanifold, with its
  characteristic charts and Darboux coordinates; its characteristic leaves are isotropic.

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
  have e : Matrix.vecCons (m j) u = ![m j, u 0] := (FinVec.etaExpand_eq _).symm
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

variable [BoundarylessManifold I M]

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
  have hU : IsOpen κ.target := h.domChart.isOpen_extend_target_of_mem_maximalAtlas one_ne_zero he
  have hx : x ∈ κ.source := by simpa [κ] using h.mem_domChart_source
  -- On the chart's image, `κ⁻¹` and `κ` have inverse derivatives. The image is open and lies in
  -- the range of `I`, so the derivative of `κ⁻¹` within that range is its derivative.
  have hinv (z : E) (hz : z ∈ κ.target) (c : E) :
      mfderiv I 𝓘(ℝ, E) κ (κ.symm z) (mfderiv 𝓘(ℝ, E) I κ.symm z c) = c := by
    have := mfderiv_extend_comp_mfderivWithin_extend_symm he hz
    rw [mfderivWithin_of_mem_nhds (mem_of_superset (hU.mem_nhds hz)
      h.domChart.extend_target_subset_range)] at this
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
    exact (FinVec.etaExpand_eq _).symm
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

omit [BoundarylessManifold I M] in
/-- **Descent along a characteristic submersion.** A closed two-form `σ` on a manifold modelled
without boundary is the pullback `p^* τ` of a unique symplectic form `τ` on the base of each of
its characteristic submersions `p`. -/
theorem existsUnique_isSymplectic_mpullback_eq [I.Boundaryless] [IsManifold IB ∞ B]
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
  obtain ⟨U, hxU, Ψ, hΨ0, hUΨ⟩ := Φ.exists_diffeomorph_ball_prod_ball hx h0 hball
  have huΦ (u : U) : (u : M) ∈ Φ.source := (hUΨ u).1
  have hΨ (u : U) : (Ψ u : F₁ × F₂) = Φ u := (hUΨ u).2
  refine ⟨U, hxU, Ψ, hΨ0, ?_⟩
  let V : Opens (F₁ × F₂) :=
    ⟨Metric.ball 0 1 ×ˢ Metric.ball 0 1, Metric.isOpen_ball.prod Metric.isOpen_ball⟩
  let B : Opens F₂ := ⟨Metric.ball 0 1, Metric.isOpen_ball⟩
  let p : U → B := fun u ↦ ⟨(Ψ u : F₁ × F₂).2, (Ψ u).property.2⟩
  -- The derivative of `p` is the second component of the derivative of `Φ`.
  have hderiv (u : U) (v : TangentSpace I u) :
      mfderiv I 𝓘(ℝ, F₂) p u v = (mfderiv I 𝓘(ℝ, F₁ × F₂) Φ u v).2 := by
    have hD := (ContinuousLinearMap.snd ℝ F₁ F₂).hasMFDerivAt.comp (u : M)
      (Φ.mdifferentiableAt (by simp) (huΦ u)).hasMFDerivAt
    have h := TauCeti.Manifold.mfderiv_apply_of_subtype_val_comp_eq (I := I) (I' := 𝓘(ℝ, F₂))
      (f := p) (A := ContinuousLinearMap.snd ℝ F₁ F₂ ∘ Φ)
      (funext fun u ↦ congrArg Prod.snd (hΨ u)) v
    rw [hD.mfderiv] at h
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
      rw [Homeomorph.image_symm]; ext u; simp [p, S, V, Subtype.ext_iff]
    rw [hpS]
    refine IsPreconnected.image ?_ _ Ψ.toHomeomorph.symm.continuous.continuousOn
    rw [← Topology.IsInducing.subtypeVal.isPreconnected_image]
    convert (convex_ball (0 : F₁) 1).isPreconnected.prod
      (isPreconnected_singleton (x := (b : F₂)))
  · ext v
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hderiv,
      SmoothTwoForm.bilinFormAt_mpullback_subtype_val]
    exact hker u (huΦ u) v

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
  obtain ⟨Φ, hx, h0, hball, hker⟩ :=
    (isInvolutiveDistribution_ker_bilinFormAt σ hσ).exists_flatPartialDiffeomorph
      (F₁ := EuclideanSpace ℝ (Fin k)) (F₂ := StdSpace (Fin r))
      (isContMDiffDistribution_ker_bilinFormAt σ hk) (by simp)
      (by rw [hr, finrank_stdSpace, Fintype.card_fin]) x
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
theorem exists_isCharacteristicSubmersion_and_existsUnique_isSymplectic_mpullback_eq
    (σ : SmoothForm I M ℝ 2)
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

/-! ### Darboux coordinates for a closed form of constant rank -/

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
/-- Let `g : N → M` and `p : N → B'` be differentiable maps such that `g^* σ = p^* τ`, let `d` be a
chart of `B'` pulling `stdForm (Fin r)` back to `τ`, and let `c` be a chart of `N`, whose source `p`
maps into that of `d`, and `ρ : E' → StdSpace (Fin r)` a linear map with `d ∘ p ∘ c⁻¹ = ρ` on the
target of `c`. Then on the target of `c`, `g ∘ c⁻¹` pulls `σ` back to the pull-back of
`stdForm (Fin r)` along `ρ`. -/
private theorem eval₂_mfderiv_comp_symm_eq_of_darbouxChart {E' H' N B' : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
    [TopologicalSpace N] [ChartedSpace H' N] [TopologicalSpace B'] {r : ℕ}
    [ChartedSpace (StdSpace (Fin r)) B'] [IsManifold 𝓘(ℝ, StdSpace (Fin r)) ∞ B']
    {g : N → M} (hg : MDifferentiable J I g)
    {p : N → B'} (hp : MDifferentiable J 𝓘(ℝ, StdSpace (Fin r)) p)
    {τ : SmoothTwoForm 𝓘(ℝ, StdSpace (Fin r)) B'}
    (hgp : ∀ q (v w : TangentSpace J q),
      SmoothBundleForm.eval₂ σ (g q) (mfderiv J I g q v) (mfderiv J I g q w) =
        τ.eval₂ (p q) (mfderiv J _ p q v) (mfderiv J _ p q w))
    {d : PartialDiffeomorph 𝓘(ℝ, StdSpace (Fin r)) 𝓘(ℝ, StdSpace (Fin r)) B' (StdSpace (Fin r)) ∞}
    (hd : ∀ x ∈ d.source, ∀ v w : TangentSpace 𝓘(ℝ, StdSpace (Fin r)) x,
      τ.eval₂ x v w = stdForm (Fin r) (mvfderiv _ d x v) (mvfderiv _ d x w))
    {c : PartialDiffeomorph J 𝓘(ℝ, E') N E' ∞} {ρ : E' →L[ℝ] StdSpace (Fin r)}
    (hsrc : ∀ q ∈ c.source, p q ∈ d.source) (hdp : ∀ s ∈ c.target, d (p (c.symm s)) = ρ s)
    {s : E'} (hs : s ∈ c.target) (a b : TangentSpace 𝓘(ℝ, E') s) :
    SmoothBundleForm.eval₂ σ (g (c.symm s)) (mfderiv 𝓘(ℝ, E') I (g ∘ c.symm) s a)
      (mfderiv 𝓘(ℝ, E') I (g ∘ c.symm) s b) = stdForm (Fin r) (ρ a) (ρ b) := by
  have hpu : p (c.symm s) ∈ d.source := hsrc _ (c.map_target hs)
  have hcd : MDifferentiableAt 𝓘(ℝ, E') J c.symm s :=
    c.symm.mdifferentiableAt (by simp) (by simpa using hs)
  have hdd := d.mdifferentiableAt (by simp) hpu
  -- The derivative of `d ∘ p ∘ c⁻¹ = ρ` is `ρ`.
  have hρ (v : TangentSpace 𝓘(ℝ, E') s) :
      mvfderiv 𝓘(ℝ, StdSpace (Fin r)) d (p (c.symm s))
        (mfderiv J 𝓘(ℝ, StdSpace (Fin r)) p (c.symm s) (mfderiv 𝓘(ℝ, E') J c.symm s v)) = ρ v := by
    have hev : (d ∘ p) ∘ c.symm =ᶠ[𝓝 s] ρ :=
      Filter.eventually_of_mem (c.open_target.mem_nhds hs) hdp
    rw [← mvfderiv_comp_apply _ hdd (hp _), ← mvfderiv_comp_apply s (hdd.comp _ (hp _)) hcd,
      hev.mvfderiv_eq, mvfderiv_eq_fderiv_apply, ρ.fderiv]
  rw [mfderiv_comp_apply s (hg _) hcd a, mfderiv_comp_apply s (hg _) hcd b, hgp, hd _ hpu,
    hρ a, hρ b]

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E] [I.Boundaryless] in
/-- On an open `U ⊆ M` with a diffeomorphism `Ψ` onto the product of the unit balls of `ℝᵏ` and
`StdSpace (Fin r)`, a chart `d` of the second ball and a linear identification `L` of the model of
`M` with `ℝᵏ × StdSpace (Fin r)` give a chart `c₀ = L⁻¹ ∘ (id × d) ∘ Ψ` of `U`. -/
private theorem exists_partialDiffeomorph_prod_comp {k r : ℕ} {U : Opens M}
    (Ψ : U ≃ₘ^∞⟮I, 𝓘(ℝ, EuclideanSpace ℝ (Fin k) × StdSpace (Fin r))⟯
      (⟨Metric.ball 0 1 ×ˢ Metric.ball 0 1, Metric.isOpen_ball.prod Metric.isOpen_ball⟩ :
        Opens (EuclideanSpace ℝ (Fin k) × StdSpace (Fin r))))
    (d : PartialDiffeomorph 𝓘(ℝ, StdSpace (Fin r)) 𝓘(ℝ, StdSpace (Fin r))
      (⟨Metric.ball 0 1, Metric.isOpen_ball⟩ : Opens (StdSpace (Fin r))) (StdSpace (Fin r)) ∞)
    (L : E ≃L[ℝ] EuclideanSpace ℝ (Fin k) × StdSpace (Fin r)) (u₀ : U) :
    ∃ c₀ : PartialDiffeomorph I 𝓘(ℝ, E) U E ∞,
      (∀ u, u ∈ c₀.source ↔
        (⟨(Ψ u : EuclideanSpace ℝ (Fin k) × StdSpace (Fin r)).2, (Ψ u).property.2⟩ :
          (⟨Metric.ball 0 1, Metric.isOpen_ball⟩ : Opens (StdSpace (Fin r)))) ∈ d.source) ∧
      ∀ u, L (c₀ u) = ((Ψ u : EuclideanSpace ℝ (Fin k) × StdSpace (Fin r)).1,
        d ⟨(Ψ u : EuclideanSpace ℝ (Fin k) × StdSpace (Fin r)).2, (Ψ u).property.2⟩) := by
  -- `D` is `d` read on `StdSpace (Fin r)`, and `Θ = id × D` acts on the second component.
  let D := (PartialDiffeomorph.subtypeVal 𝓘(ℝ, StdSpace (Fin r)) ∞ _
    ⟨⟨(Ψ u₀ : EuclideanSpace ℝ (Fin k) × StdSpace (Fin r)).2, (Ψ u₀).property.2⟩⟩).symm.trans d
  have hD (b : (⟨Metric.ball 0 1, Metric.isOpen_ball⟩ : Opens (StdSpace (Fin r)))) :
      D b = d b := by
    simp [D]
  have hDs (b : (⟨Metric.ball 0 1, Metric.isOpen_ball⟩ : Opens (StdSpace (Fin r)))) :
      (b : StdSpace (Fin r)) ∈ D.source ↔ b ∈ d.source := by
    simp [D]
  let Θ₀ := (OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin k))).prod D.toOpenPartialHomeomorph
  have hDc : ContDiffOn ℝ ∞ D D.source := contMDiffOn_iff_contDiffOn.1 D.contMDiffOn
  have hDsc : ContDiffOn ℝ ∞ D.symm D.target := contMDiffOn_iff_contDiffOn.1 D.symm.contMDiffOn
  let Θ := PartialDiffeomorph.ofOpenPartialHomeomorph Θ₀
    (by
      simp only [Θ₀, OpenPartialHomeomorph.prod_source, OpenPartialHomeomorph.refl_source]
      exact contDiffOn_fst.prodMk (hDc.comp contDiffOn_snd fun x hx ↦ hx.2))
    (by
      simp only [Θ₀, OpenPartialHomeomorph.prod_target, OpenPartialHomeomorph.refl_target]
      exact contDiffOn_fst.prodMk (hDsc.comp contDiffOn_snd fun x hx ↦ hx.2))
  have hΘ (z : EuclideanSpace ℝ (Fin k) × StdSpace (Fin r)) : Θ z = (z.1, D z.2) := by
    simp [Θ, Θ₀]
  have hΘs (z : EuclideanSpace ℝ (Fin k) × StdSpace (Fin r)) :
      z ∈ Θ.source ↔ z.2 ∈ D.source := by
    simp [Θ, Θ₀]
  refine ⟨(Ψ.toPartialDiffeomorph.trans (PartialDiffeomorph.subtypeVal _ ∞ _ ⟨Ψ u₀⟩)).trans
      (Θ.trans L.symm.toPartialDiffeomorph), fun u ↦ ?_, fun u ↦ ?_⟩
  · simp [hΘs, ← hDs]
  · simp [hΘ, ← hD]

/-- **Darboux coordinates for a closed two-form of constant rank.** Let `σ` be a closed two-form
on a boundaryless manifold of dimension `k + 2r` whose kernels all have dimension `k`, and let
`L` identify the model space with `ℝᵏ × StdSpace (Fin r)`. Every point `x` has a chart `c` with
`c x = 0` in which, near `0`, `σ` is the pull-back of `stdForm (Fin r)` along the second
component of `L`. The chart combines the leaf coordinates of a characteristic chart of `σ`
(`exists_isCharacteristicSubmersion`) with a Darboux chart of the symplectic form that `σ`
induces on the local space of leaves
(`IsCharacteristicSubmersion.existsUnique_isSymplectic_mpullback_eq`). -/
theorem exists_partialDiffeomorph_eval₂_eq_stdForm (σ : SmoothForm I M ℝ 2) (hσ : σ.IsClosed)
    {k r : ℕ} (hk : ∀ x, finrank ℝ (LinearMap.ker (σ.bilinFormAt x)) = k)
    (L : E ≃L[ℝ] EuclideanSpace ℝ (Fin k) × StdSpace (Fin r)) (x : M) :
    ∃ c : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞, x ∈ c.source ∧ c x = 0 ∧
      ∀ᶠ s in 𝓝 (0 : E), ∀ a b : TangentSpace 𝓘(ℝ, E) s,
        SmoothBundleForm.eval₂ σ (c.symm s) (mfderiv 𝓘(ℝ, E) I c.symm s a)
          (mfderiv 𝓘(ℝ, E) I c.symm s b) = stdForm (Fin r) (L a).2 (L b).2 := by
  -- A characteristic chart `Ψ` of `σ` on `U ∋ x`, with leaf space the ball `B`, and the
  -- symplectic form `τ` that `σ` induces on `B`.
  have hr : finrank ℝ E = k + 2 * r := by
    rw [L.toLinearEquiv.finrank_eq, Module.finrank_prod, finrank_euclideanSpace, finrank_stdSpace]
    simp
  obtain ⟨U, hx, Ψ, hΨ0, hp⟩ := σ.exists_isCharacteristicSubmersion hσ hk hr x
  set p : U → (⟨Metric.ball 0 1, Metric.isOpen_ball⟩ : Opens (StdSpace (Fin r))) :=
    fun u ↦ ⟨(Ψ u : EuclideanSpace ℝ (Fin k) × StdSpace (Fin r)).2, (Ψ u).property.2⟩ with hp_def
  set u₀ : U := ⟨x, hx⟩
  obtain ⟨τ, ⟨hτs, hτ⟩, -⟩ := hp.existsUnique_isSymplectic_mpullback_eq (hσ.mpullback _ _)
  -- A Darboux chart `d` of `τ`, and the chart `c₀ = L⁻¹ ∘ (id × d) ∘ Ψ` of `U`.
  obtain ⟨d, hd₀, hd0, hd⟩ := hτs.exists_darbouxChart_of_symplecticForm (stdForm (Fin r)) (p u₀)
  obtain ⟨c₀, hc₀s, hc₀⟩ := exists_partialDiffeomorph_prod_comp Ψ d L u₀
  have hu₀ : u₀ ∈ c₀.source := (hc₀s u₀).2 hd₀
  -- `p u₀` is the second component of `Ψ u₀`, which `hc₀` writes out.
  have hc₀0 : c₀ u₀ = 0 := L.injective (by
    rw [hc₀, map_zero]
    exact Prod.ext (by simp [hΨ0]) hd0)
  -- On the target of `c₀`, the second component of `L` is `d ∘ p ∘ c₀⁻¹`.
  let ρ : E →L[ℝ] StdSpace (Fin r) :=
    (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin k)) (StdSpace (Fin r))).comp
      (L : E →L[ℝ] EuclideanSpace ℝ (Fin k) × StdSpace (Fin r))
  have hdp (z : E) (hz : z ∈ c₀.target) : d (p (c₀.symm z)) = ρ z := by
    have h := hc₀ (c₀.symm z)
    simp only [PartialDiffeomorph.symm_toPartialEquiv] at h ⊢
    rw [c₀.right_inv hz] at h
    simp [ρ, h, hp_def]
  -- The chart `c` of `M` that agrees with `c₀` near `x`.
  obtain ⟨c, hcx, -, hcx₀, hct, hcs⟩ := c₀.exists_ambient_of_opens hu₀
  have h0 : (0 : E) ∈ c.target := by
    rw [← hc₀0, ← hcx₀]
    exact c.map_source hcx
  refine ⟨c, hcx, hcx₀.trans hc₀0, ?_⟩
  -- The form computation: on `U`, `σ` is `p^* τ`, and `d` pulls `stdForm (Fin r)` back to `τ`.
  have hgp (u : U) (v w : TangentSpace I u) :
      SmoothBundleForm.eval₂ σ (Subtype.val u) (mfderiv I I Subtype.val u v)
        (mfderiv I I Subtype.val u w) =
      τ.eval₂ (p u) (mfderiv I _ p u v) (mfderiv I _ p u w) := by
    rw [← SmoothForm.eval₂_mpullback Subtype.val contMDiff_subtypeVal, ← hτ,
      SmoothForm.eval₂_mpullback]
  -- `Filter.EventuallyEq.mfderiv_eq` reads the derivative through `tangentSpaceCast`.
  have hcast (y z : M) (hyz : y = z) (v w : TangentSpace I y) :
      SmoothBundleForm.eval₂ σ z (tangentSpaceCast I y z v) (tangentSpaceCast I y z w) =
        SmoothBundleForm.eval₂ σ y v w := by
    subst hyz
    simp
  have hρ (v : E) : ρ v = (L v).2 := by simp [ρ]
  filter_upwards [c.open_target.mem_nhds h0] with s hs a b
  -- Near `s`, `c⁻¹` is `Subtype.val ∘ c₀⁻¹`.
  have heq : (c.symm : E → M) =ᶠ[𝓝 s] Subtype.val ∘ c₀.symm :=
    Filter.eventually_of_mem (c.open_target.mem_nhds hs) fun z hz ↦ hcs z hz
  rw [heq.mfderiv_eq, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  refine (hcast _ _ (hcs s hs).symm _ _).trans ?_
  refine (eval₂_mfderiv_comp_symm_eq_of_darbouxChart mdifferentiable_subtypeVal
    (fun u ↦ hp.isSubmersion.contMDiff.mdifferentiableAt (by simp)) hgp hd
    (fun u hu ↦ (hc₀s u).1 hu) hdp (hct hs) a b).trans ?_
  exact congrArg₂ (stdForm (Fin r) · ·) (hρ a) (hρ b)

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
immersion, for a closed nondegenerate two-form `σ`, of a boundaryless manifold of codimension `k`
and dimension `k + 2r`. Around every point `q` of `N` there is a characteristic chart of the
presymplectic form `f^* σ`, as in `TauCeti.SmoothForm.exists_isCharacteristicSubmersion`, with
leaves of dimension `k`. -/
theorem IsCoisotropicMap.exists_isCharacteristicSubmersion [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] [J.Boundaryless] (h : hσ.IsCoisotropicMap J f)
    (hi : IsImmersion J I ∞ f) (hf : ContMDiff J I ∞ f) (hσc : σ.IsClosed) {k r : ℕ}
    (hk : finrank ℝ F + k = finrank ℝ E) (hr : finrank ℝ F = k + 2 * r) (q : N) :
    ∃ (U : Opens N) (hq : q ∈ U)
      (Ψ : U ≃ₘ^∞⟮J, 𝓘(ℝ, EuclideanSpace ℝ (Fin k) × StdSpace (Fin r))⟯
        (⟨Metric.ball 0 1 ×ˢ Metric.ball 0 1, Metric.isOpen_ball.prod Metric.isOpen_ball⟩ :
          Opens (EuclideanSpace ℝ (Fin k) × StdSpace (Fin r)))),
      (Ψ ⟨q, hq⟩ : EuclideanSpace ℝ (Fin k) × StdSpace (Fin r)) = 0 ∧
      SmoothForm.IsCharacteristicSubmersion 𝓘(ℝ, StdSpace (Fin r))
        (SmoothForm.mpullback (Subtype.val : U → N) contMDiff_subtypeVal
          (SmoothForm.mpullback f hf σ))
        (fun u ↦ (⟨(Ψ u : EuclideanSpace ℝ (Fin k) × StdSpace (Fin r)).2, (Ψ u).property.2⟩ :
          (⟨Metric.ball 0 1, Metric.isOpen_ball⟩ : Opens (StdSpace (Fin r))))) :=
  (SmoothForm.mpullback f hf σ).exists_isCharacteristicSubmersion (hσc.mpullback f hf)
    (fun x ↦ (h.finrank_ker_bilinFormAt_mpullback hi hf x).trans (by omega)) hr q

/-- **Darboux coordinates on a coisotropic submanifold.** Let `f : N → M` be a coisotropic
immersion, for a closed nondegenerate two-form `σ`, of a boundaryless manifold of codimension `k`
and dimension `k + 2r`, and let `L` identify the model space of `N` with
`ℝᵏ × StdSpace (Fin r)`. Every point `q` of `N` has a chart `c` with `c q = 0` in which, near `0`,
the presymplectic form `f^* σ` is the pull-back of `stdForm (Fin r)` along the second component
of `L`, as in `TauCeti.SmoothForm.exists_partialDiffeomorph_eval₂_eq_stdForm`. -/
theorem IsCoisotropicMap.exists_partialDiffeomorph_eval₂_eq_stdForm [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] [J.Boundaryless] (h : hσ.IsCoisotropicMap J f)
    (hi : IsImmersion J I ∞ f) (hf : ContMDiff J I ∞ f) (hσc : σ.IsClosed) {k r : ℕ}
    (hk : finrank ℝ F + k = finrank ℝ E)
    (L : F ≃L[ℝ] EuclideanSpace ℝ (Fin k) × StdSpace (Fin r)) (q : N) :
    ∃ c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞, q ∈ c.source ∧ c q = 0 ∧
      ∀ᶠ s in 𝓝 (0 : F), ∀ a b : TangentSpace 𝓘(ℝ, F) s,
        SmoothBundleForm.eval₂ (SmoothForm.mpullback f hf σ) (c.symm s)
          (mfderiv 𝓘(ℝ, F) J c.symm s a) (mfderiv 𝓘(ℝ, F) J c.symm s b) =
        stdForm (Fin r) (L a).2 (L b).2 :=
  (SmoothForm.mpullback f hf σ).exists_partialDiffeomorph_eval₂_eq_stdForm (hσc.mpullback f hf)
    (fun x ↦ (h.finrank_ker_bilinFormAt_mpullback hi hf x).trans (by omega)) L q

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
