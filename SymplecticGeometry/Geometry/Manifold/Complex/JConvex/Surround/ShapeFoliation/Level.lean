/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.JConvex.Surround.ConvexShape.Basic

import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import SymplecticGeometry.Analysis.Complex.LeviForm.Basic
import SymplecticGeometry.Geometry.Manifold.Complex.JConvex.Hypersurface
import TauCeti.Analysis.Calculus.ParametricFDeriv
import TauCeti.Analysis.Normed.Operator.Prod

/-!
# The level function of a foliation by `i`-convex shapes

Let `χ : ℝ → ℝ → ℝ` be a family of shapes `R = χ ℓ r`, smooth in `(ℓ, r)` on a product of open
intervals, each `χ ℓ` an `i`-convex shape (`SymplecticGeometry.IsConvexShapeAt`) at each point,
with `∂χ/∂ℓ > 0`. Its leaves `{(s, t) = (χ ℓ r ², r ²)}` in the quadrant of the shape coordinates
`(s, t)` are then disjoint, and this file builds the function that is `-ℓ` on the leaf `ℓ`.

* `SymplecticGeometry.exists_contDiff_shapeLevel`: there is `φ : ℝ × ℝ → ℝ`, equal to `-ℓ` at
  `(χ ℓ r ², r ²)` and smooth there, with `∂φ/∂s < 0` and `∂φ/∂t > 0`, such that the Levi form
  of `φ ∘ shape` is positive on the nonzero complex tangencies of its levels at every point over
  the swept region.

The map `(ℓ, r) ↦ (χ ℓ r ², r ²)` has an invertible differential, triangular with diagonal
`2 χ ∂χ/∂ℓ` and `2 r`, so by the inverse function theorem
(`ContDiffAt.to_localInverse`, `HasStrictFDerivAt.to_localInverse`) its local inverses are smooth,
and `φ` is minus their first component. On the level of `φ ∘ shape` through a point of the leaf
`ℓ`, the differential of `φ` is `1 / ∂χ/∂ℓ` times that of `shapeGraph (χ ℓ)`, and the level
contains the hypersurface of the shape `χ ℓ` near the point; so the positivity of the Levi form
passes from `SymplecticGeometry.IsConvexShapeAt.re_leviForm_pos` to `φ ∘ shape` by
`SymplecticGeometry.forall_re_manifoldLeviForm_pos_iff_of_mvfderiv_eq_smul`, with
`SymplecticGeometry.fderiv_shapeGraph_comp_shape_ne_zero` for the nonvanishing of the
differential of `shapeGraph (χ ℓ) ∘ shape`.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Proposition 3.25 (the function of a foliation).
-/

public section

noncomputable section

namespace SymplecticGeometry

open Set Filter Topology Complex TauCeti
open scoped ContDiff Manifold

variable {χ : ℝ → ℝ → ℝ} {ℓ₀ ℓ₁ r₁ r₂ : ℝ}

/-- The point `(χ ℓ r ², r ²)` of the leaf `ℓ` over `r`, as a function of `x = (ℓ, r)`. -/
private def leafPoint (χ : ℝ → ℝ → ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  (χ x.1 x.2 ^ 2, x.2 ^ 2)

private theorem leafPoint_def (χ : ℝ → ℝ → ℝ) (x : ℝ × ℝ) :
    leafPoint χ x = (χ x.1 x.2 ^ 2, x.2 ^ 2) :=
  (rfl)

/-- On a product of open intervals where the family is `C¹` with `∂χ/∂ℓ > 0`, each `χ · r` is
strictly increasing. -/
private theorem strictMonoOn_shapeFamily
    (hχ : ContDiffOn ℝ 1 (Function.uncurry χ) (Ioo ℓ₀ ℓ₁ ×ˢ Ioo r₁ r₂))
    (hmono : ∀ ℓ ∈ Ioo ℓ₀ ℓ₁, ∀ r ∈ Ioo r₁ r₂, 0 < deriv (fun ℓ' ↦ χ ℓ' r) ℓ)
    {r : ℝ} (hr : r ∈ Ioo r₁ r₂) : StrictMonoOn (fun ℓ ↦ χ ℓ r) (Ioo ℓ₀ ℓ₁) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioo _ _) ?_ fun ℓ hℓ ↦
    hmono ℓ (by rwa [interior_Ioo] at hℓ) r hr
  have h := hχ.continuousOn.comp (continuousOn_id.prodMk continuousOn_const)
    fun ℓ hℓ ↦ Set.mk_mem_prod hℓ hr
  simpa [Function.comp_def] using h

/-- The leaf map is injective on the product of intervals. -/
private theorem injOn_leafPoint
    (hχ : ContDiffOn ℝ 1 (Function.uncurry χ) (Ioo ℓ₀ ℓ₁ ×ˢ Ioo r₁ r₂))
    (hconv : ∀ ℓ ∈ Ioo ℓ₀ ℓ₁, ∀ r ∈ Ioo r₁ r₂, IsConvexShapeAt (χ ℓ) r)
    (hmono : ∀ ℓ ∈ Ioo ℓ₀ ℓ₁, ∀ r ∈ Ioo r₁ r₂, 0 < deriv (fun ℓ' ↦ χ ℓ' r) ℓ) :
    InjOn (leafPoint χ) (Ioo ℓ₀ ℓ₁ ×ˢ Ioo r₁ r₂) := by
  rintro ⟨ℓ, r⟩ ⟨hℓ, hr⟩ ⟨ℓ', r'⟩ ⟨hℓ', hr'⟩ h
  simp only [leafPoint_def, Prod.mk.injEq] at h
  have hrr : r = r' := by
    have h0 := (hconv ℓ hℓ r hr).pos
    have h1 := (hconv ℓ' hℓ' r' hr').pos
    nlinarith [h.2]
  subst hrr
  have h0 := (hconv ℓ hℓ r hr).pos_value
  have h1 := (hconv ℓ' hℓ' r hr').pos_value
  have hχχ : χ ℓ r = χ ℓ' r := by nlinarith [h.1]
  exact Prod.ext ((strictMonoOn_shapeFamily hχ hmono hr).injOn hℓ hℓ' hχχ) rfl

open Classical in
/-- The level function of the family: `-ℓ` at the point `(χ ℓ r ², r ²)` of the leaf `ℓ`, and
`0` off the swept region. -/
private def shapeLevelFun (χ : ℝ → ℝ → ℝ) (ℓ₀ ℓ₁ r₁ r₂ : ℝ) (q : ℝ × ℝ) : ℝ :=
  if h : ∃ x ∈ Ioo ℓ₀ ℓ₁ ×ˢ Ioo r₁ r₂, leafPoint χ x = q then -h.choose.1 else 0

private theorem shapeLevelFun_leafPoint
    (hχ : ContDiffOn ℝ 1 (Function.uncurry χ) (Ioo ℓ₀ ℓ₁ ×ˢ Ioo r₁ r₂))
    (hconv : ∀ ℓ ∈ Ioo ℓ₀ ℓ₁, ∀ r ∈ Ioo r₁ r₂, IsConvexShapeAt (χ ℓ) r)
    (hmono : ∀ ℓ ∈ Ioo ℓ₀ ℓ₁, ∀ r ∈ Ioo r₁ r₂, 0 < deriv (fun ℓ' ↦ χ ℓ' r) ℓ)
    {x : ℝ × ℝ} (hx : x ∈ Ioo ℓ₀ ℓ₁ ×ˢ Ioo r₁ r₂) :
    shapeLevelFun χ ℓ₀ ℓ₁ r₁ r₂ (leafPoint χ x) = -x.1 := by
  have h : ∃ y ∈ Ioo ℓ₀ ℓ₁ ×ˢ Ioo r₁ r₂, leafPoint χ y = leafPoint χ x := ⟨x, hx, rfl⟩
  rw [shapeLevelFun, dite_eq_left_of_eq_true (eq_true h),
    injOn_leafPoint hχ hconv hmono h.choose_spec.1 hx h.choose_spec.2]

/-- At `x = (ℓ, r)` with `χ ℓ r`, `r` and `∂χ/∂ℓ` nonzero, the leaf map
`(ℓ, r) ↦ (χ ℓ r ², r ²)` has the invertible differential
`(a, b) ↦ (2 χ (a ∂χ/∂ℓ + b ∂χ/∂r), 2 r b)`, whose inverse has first component
`(a, b) ↦ a / (2 χ ∂χ/∂ℓ) - b ∂χ/∂r / (2 r ∂χ/∂ℓ)`. -/
private theorem hasFDerivAt_leafPoint {x : ℝ × ℝ}
    (hdx : DifferentiableAt ℝ (Function.uncurry χ) x) (hc : χ x.1 x.2 ≠ 0) (hr : x.2 ≠ 0)
    (hA : deriv (fun ℓ ↦ χ ℓ x.2) x.1 ≠ 0) :
    ∃ e : (ℝ × ℝ) ≃L[ℝ] ℝ × ℝ, HasFDerivAt (leafPoint χ) (e : ℝ × ℝ →L[ℝ] ℝ × ℝ) x ∧
      ∀ a b : ℝ, (e.symm (a, b)).1 =
        a / (2 * χ x.1 x.2 * deriv (fun ℓ ↦ χ ℓ x.2) x.1) -
          deriv (χ x.1) x.2 * b / (2 * x.2 * deriv (fun ℓ ↦ χ ℓ x.2) x.1) := by
  have hdx' : DifferentiableAt ℝ (Function.uncurry χ) (x.1, x.2) := by rwa [Prod.mk.eta]
  have hA' := hasDerivAt_parameterCurve_uncurry hdx'
  have hB' := hasDerivAt_timeSlice_uncurry hdx'
  rw [Prod.mk.eta] at hA' hB'
  rw [hA'.deriv] at hA ⊢
  rw [hB'.deriv]
  set A := fderiv ℝ (Function.uncurry χ) x (1, 0)
  set B := fderiv ℝ (Function.uncurry χ) x (0, 1)
  set c := χ x.1 x.2
  have hDlin (a b : ℝ) : fderiv ℝ (Function.uncurry χ) x (a, b) = a * A + b * B := by
    rw [ContinuousLinearMap.apply_mk_eq_smul_add_smul, smul_eq_mul, smul_eq_mul]
  let L : ℝ × ℝ →L[ℝ] ℝ × ℝ := ((2 * c) • fderiv ℝ (Function.uncurry χ) x).prod
    ((2 * x.2) • ContinuousLinearMap.snd ℝ ℝ ℝ)
  let L' : ℝ × ℝ →L[ℝ] ℝ × ℝ := ((1 / (2 * c * A)) • ContinuousLinearMap.fst ℝ ℝ ℝ -
    (B / (2 * x.2 * A)) • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
    ((1 / (2 * x.2)) • ContinuousLinearMap.snd ℝ ℝ ℝ)
  have hL (a b : ℝ) : L (a, b) = (2 * c * (a * A + b * B), 2 * x.2 * b) := by
    simp [L, hDlin, mul_assoc]
  have hL' (a b : ℝ) : L' (a, b) = (a / (2 * c * A) - B * b / (2 * x.2 * A), b / (2 * x.2)) := by
    simp only [L', ContinuousLinearMap.prod_apply, sub_apply,
      smul_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      smul_eq_mul, Prod.mk.injEq]
    constructor <;> ring
  have hL'L : L'.comp L = ContinuousLinearMap.id ℝ (ℝ × ℝ) := by
    refine ContinuousLinearMap.ext ?_
    rintro ⟨a, b⟩
    rw [ContinuousLinearMap.comp_apply, hL, hL', ContinuousLinearMap.id_apply]
    ext
    · field_simp
      ring
    · field_simp
  have hLL' : L.comp L' = ContinuousLinearMap.id ℝ (ℝ × ℝ) := by
    refine ContinuousLinearMap.ext ?_
    rintro ⟨a, b⟩
    rw [ContinuousLinearMap.comp_apply, hL', hL, ContinuousLinearMap.id_apply]
    ext
    · field_simp
      ring
    · field_simp
  refine ⟨ContinuousLinearEquiv.ofContinuousLinearMap L L' hLL' hL'L, ?_, fun a b ↦ ?_⟩
  · rw [ContinuousLinearEquiv.toContinuousLinearMap_ofContinuousLinearMap]
    have hleaf : leafPoint χ = fun y ↦ (Function.uncurry χ y ^ 2, y.2 ^ 2) := by
      funext y
      rw [leafPoint_def, Function.uncurry_apply_pair]
    rw [hleaf]
    refine (hdx.hasFDerivAt.pow 2).prodMk ((hasFDerivAt_snd (p := x)).pow 2) |>.congr_fderiv ?_
    ext <;> simp [L, c, mul_comm, Function.uncurry_def]
  · rw [ContinuousLinearEquiv.symm_ofContinuousLinearMap,
      ContinuousLinearEquiv.coe_ofContinuousLinearMap, hL']

/-- At a point `(χ ℓ r ², r ²)` of the swept region, the level function is smooth, with
differential `(a, b) ↦ -(a / (2 χ) - b ∂χ/∂r / (2 r)) / ∂χ/∂ℓ`: near the point it is minus the
first component of a local inverse of the leaf map. -/
private theorem contDiffAt_shapeLevelFun
    (hχ : ContDiffOn ℝ ∞ (Function.uncurry χ) (Ioo ℓ₀ ℓ₁ ×ˢ Ioo r₁ r₂))
    (hconv : ∀ ℓ ∈ Ioo ℓ₀ ℓ₁, ∀ r ∈ Ioo r₁ r₂, IsConvexShapeAt (χ ℓ) r)
    (hmono : ∀ ℓ ∈ Ioo ℓ₀ ℓ₁, ∀ r ∈ Ioo r₁ r₂, 0 < deriv (fun ℓ' ↦ χ ℓ' r) ℓ)
    {x : ℝ × ℝ} (hx : x ∈ Ioo ℓ₀ ℓ₁ ×ˢ Ioo r₁ r₂) :
    ContDiffAt ℝ ∞ (shapeLevelFun χ ℓ₀ ℓ₁ r₁ r₂) (leafPoint χ x) ∧
      ∀ a b : ℝ, fderiv ℝ (shapeLevelFun χ ℓ₀ ℓ₁ r₁ r₂) (leafPoint χ x) (a, b) =
        -(a / (2 * χ x.1 x.2) - b * deriv (χ x.1) x.2 / (2 * x.2)) /
          deriv (fun ℓ ↦ χ ℓ x.2) x.1 := by
  have hD : IsOpen (Ioo ℓ₀ ℓ₁ ×ˢ Ioo r₁ r₂) := isOpen_Ioo.prod isOpen_Ioo
  have hχ1 : ContDiffOn ℝ 1 (Function.uncurry χ) (Ioo ℓ₀ ℓ₁ ×ˢ Ioo r₁ r₂) :=
    hχ.of_le (by simp)
  have hχx : ContDiffAt ℝ ∞ (Function.uncurry χ) x := hχ.contDiffAt (hD.mem_nhds hx)
  have hconvx := hconv x.1 hx.1 x.2 hx.2
  have hA := hmono x.1 hx.1 x.2 hx.2
  obtain ⟨e, hΦ, he⟩ := hasFDerivAt_leafPoint (hχx.differentiableAt (by simp))
    hconvx.pos_value.ne' hconvx.pos.ne' hA.ne'
  have hcΦ : ContDiffAt ℝ ∞ (leafPoint χ) x := by
    have hleaf : leafPoint χ = fun y ↦ (Function.uncurry χ y ^ 2, y.2 ^ 2) := by
      funext y
      rw [leafPoint_def, Function.uncurry_apply_pair]
    rw [hleaf]
    exact (hχx.pow 2).prodMk (contDiffAt_snd.pow 2)
  have hs := hcΦ.hasStrictFDerivAt hΦ (by simp)
  have heq : shapeLevelFun χ ℓ₀ ℓ₁ r₁ r₂ =ᶠ[𝓝 (leafPoint χ x)]
      fun q ↦ -(hs.localInverse (leafPoint χ) e x q).1 := by
    filter_upwards [hs.eventually_right_inverse, hs.localInverse_tendsto (hD.mem_nhds hx)]
      with q hq₁ hq₂
    have h := shapeLevelFun_leafPoint hχ1 hconv hmono hq₂
    rwa [hq₁] at h
  refine ⟨(contDiffAt_fst.comp _ (hcΦ.to_localInverse hΦ (by simp))).neg.congr_of_eventuallyEq
    heq, fun a b ↦ ?_⟩
  have hd := ((hasFDerivAt_fst.comp _ hs.to_localInverse.hasFDerivAt).neg).congr_of_eventuallyEq
    heq
  rw [hd.fderiv, neg_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearEquiv.coe_coe, he]
  field_simp

/-- Each member `χ ℓ` of a smooth family is smooth at each `r` of the product of intervals. -/
private theorem contDiffAt_shapeFamily
    (hχ : ContDiffOn ℝ ∞ (Function.uncurry χ) (Ioo ℓ₀ ℓ₁ ×ˢ Ioo r₁ r₂))
    {ℓ r : ℝ} (hℓ : ℓ ∈ Ioo ℓ₀ ℓ₁) (hr : r ∈ Ioo r₁ r₂) : ContDiffAt ℝ ∞ (χ ℓ) r :=
  (hχ.contDiffAt ((isOpen_Ioo.prod isOpen_Ioo).mem_nhds ⟨hℓ, hr⟩)).comp r
    (contDiffAt_const.prodMk contDiffAt_id)

/-- At a point `p` over the leaf `ℓ`, the differential of `H ∘ shape`, for the level function `H`,
is `1 / ∂χ/∂ℓ` times that of `shapeGraph (χ ℓ) ∘ shape`. -/
private theorem fderiv_shapeLevelFun_comp_shape
    (hχ : ContDiffOn ℝ ∞ (Function.uncurry χ) (Ioo ℓ₀ ℓ₁ ×ˢ Ioo r₁ r₂))
    (hconv : ∀ ℓ ∈ Ioo ℓ₀ ℓ₁, ∀ r ∈ Ioo r₁ r₂, IsConvexShapeAt (χ ℓ) r)
    (hmono : ∀ ℓ ∈ Ioo ℓ₀ ℓ₁, ∀ r ∈ Ioo r₁ r₂, 0 < deriv (fun ℓ' ↦ χ ℓ' r) ℓ)
    {ℓ r : ℝ} (hℓ : ℓ ∈ Ioo ℓ₀ ℓ₁) (hr : r ∈ Ioo r₁ r₂) {k m : ℕ}
    {p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)} (hp : shape p = (χ ℓ r ^ 2, r ^ 2)) :
    fderiv ℝ (shapeLevelFun χ ℓ₀ ℓ₁ r₁ r₂ ∘ shape) p =
      (1 / deriv (fun ℓ' ↦ χ ℓ' r) ℓ) • fderiv ℝ (shapeGraph (χ ℓ) ∘ shape) p := by
  obtain ⟨hH, hdH⟩ := contDiffAt_shapeLevelFun hχ hconv hmono (x := (ℓ, r)) ⟨hℓ, hr⟩
  rw [leafPoint_def] at hH hdH
  have hconvx := hconv ℓ hℓ r hr
  have hA := hmono ℓ hℓ r hr
  have hc := hconvx.pos_value
  have hr0 := hconvx.pos
  refine ContinuousLinearMap.ext fun u ↦ ?_
  rw [smul_apply, fderiv_shapeGraph_comp_shape_apply_of_shape_eq
      ((contDiffAt_shapeFamily hχ hℓ hr).differentiableAt (by simp)) hc hr0 hp,
    fderiv_comp p ((hp ▸ hH).differentiableAt (by simp))
      ((contDiff_shape (n := 1)).differentiable one_ne_zero p),
    ContinuousLinearMap.comp_apply, fderiv_shape_apply, hp, hdH, smul_eq_mul]
  field_simp
  ring

/-- Near a point `p` over the leaf `ℓ`, the hypersurface of the shape `χ ℓ` lies in the level
`-ℓ` of `H ∘ shape`, for the level function `H`. -/
private theorem eventually_shapeLevelFun_shape_eq
    (hχ : ContDiffOn ℝ 1 (Function.uncurry χ) (Ioo ℓ₀ ℓ₁ ×ˢ Ioo r₁ r₂))
    (hconv : ∀ ℓ ∈ Ioo ℓ₀ ℓ₁, ∀ r ∈ Ioo r₁ r₂, IsConvexShapeAt (χ ℓ) r)
    (hmono : ∀ ℓ ∈ Ioo ℓ₀ ℓ₁, ∀ r ∈ Ioo r₁ r₂, 0 < deriv (fun ℓ' ↦ χ ℓ' r) ℓ)
    {ℓ r : ℝ} (hℓ : ℓ ∈ Ioo ℓ₀ ℓ₁) (hr : r ∈ Ioo r₁ r₂) {k m : ℕ}
    {p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)} (hp : shape p = (χ ℓ r ^ 2, r ^ 2)) :
    ∀ᶠ y in 𝓝 p, (shapeGraph (χ ℓ) ∘ shape) y = 0 →
      shapeLevelFun χ ℓ₀ ℓ₁ r₁ r₂ (shape y) = -ℓ := by
  have hcont : ContinuousAt (fun y ↦ √(shape y).2) p :=
    (Real.continuous_sqrt.comp (contDiff_shape (n := 0)).continuous.snd).continuousAt
  have hev : ∀ᶠ y in 𝓝 p, √(shape y).2 ∈ Ioo r₁ r₂ := by
    refine hcont.preimage_mem_nhds (isOpen_Ioo.mem_nhds ?_)
    rwa [hp, Real.sqrt_sq (hconv ℓ hℓ r hr).pos.le]
  filter_upwards [hev] with y hy hy0
  rw [Function.comp_apply, shapeGraph_def, sub_eq_zero] at hy0
  have hy' : shape y = leafPoint χ (ℓ, √(shape y).2) := by
    rw [leafPoint_def]
    ext
    · rw [hy0, Real.sq_sqrt (shape_fst_nonneg y)]
    · rw [Real.sq_sqrt (shape_snd_nonneg y)]
  rw [hy', shapeLevelFun_leafPoint hχ hconv hmono ⟨hℓ, hy⟩]

/-- At a point `p` over the leaf `ℓ`, the Levi form of `H ∘ shape`, for the level function `H`,
has positive real part on the nonzero complex tangent vectors of its level through `p`: there `dH`
is a positive multiple of `d(shapeGraph (χ ℓ))`, and the level contains the hypersurface of the
shape `χ ℓ` near `p`. -/
private theorem re_leviForm_shapeLevelFun_comp_shape_pos
    (hχ : ContDiffOn ℝ ∞ (Function.uncurry χ) (Ioo ℓ₀ ℓ₁ ×ˢ Ioo r₁ r₂))
    (hconv : ∀ ℓ ∈ Ioo ℓ₀ ℓ₁, ∀ r ∈ Ioo r₁ r₂, IsConvexShapeAt (χ ℓ) r)
    (hmono : ∀ ℓ ∈ Ioo ℓ₀ ℓ₁, ∀ r ∈ Ioo r₁ r₂, 0 < deriv (fun ℓ' ↦ χ ℓ' r) ℓ)
    {ℓ r : ℝ} (hℓ : ℓ ∈ Ioo ℓ₀ ℓ₁) (hr : r ∈ Ioo r₁ r₂) {k m : ℕ}
    {p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)} (hp : shape p = (χ ℓ r ^ 2, r ^ 2))
    {v : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)} (hv : v ≠ 0)
    (hv₁ : fderiv ℝ (shapeLevelFun χ ℓ₀ ℓ₁ r₁ r₂ ∘ shape) p v = 0)
    (hv₂ : fderiv ℝ (shapeLevelFun χ ℓ₀ ℓ₁ r₁ r₂ ∘ shape) p (I • v) = 0) :
    0 < (leviForm (shapeLevelFun χ ℓ₀ ℓ₁ r₁ r₂ ∘ shape) p v v).re := by
  set H := shapeLevelFun χ ℓ₀ ℓ₁ r₁ r₂
  obtain ⟨hH, -⟩ := contDiffAt_shapeLevelFun hχ hconv hmono (x := (ℓ, r)) ⟨hℓ, hr⟩
  rw [leafPoint_def] at hH
  have hconvx := hconv ℓ hℓ r hr
  have hr0 := hconvx.pos
  have hc := hconvx.pos_value
  have hχr := contDiffAt_shapeFamily hχ hℓ hr
  have hG : ContDiffAt ℝ ∞ (shapeGraph (χ ℓ)) (χ ℓ r ^ 2, r ^ 2) :=
    contDiffAt_shapeGraph (by rwa [Real.sqrt_sq hr0.le]) (by positivity) (by positivity)
  have hshape : ContDiffAt ℝ ∞ shape p := contDiff_shape.contDiffAt
  have hHs : ContDiffAt ℝ ∞ (H ∘ shape) p := (hp ▸ hH).comp p hshape
  have hfC : ContDiffAt ℝ 3 (shapeGraph (χ ℓ) ∘ shape) p :=
    ((hp ▸ hG).comp p hshape).of_le (by simp)
  have hgC : ContDiffAt ℝ 3 (H ∘ shape + fun _ ↦ ℓ) p :=
    (hHs.of_le (by simp)).add contDiffAt_const
  have hfp : (shapeGraph (χ ℓ) ∘ shape) p = 0 := by
    rw [Function.comp_apply, hp, shapeGraph_sq_sq hc.le hr0.le]
  have hf' : mvfderiv 𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m))
      (shapeGraph (χ ℓ) ∘ shape) p ≠ 0 := fun h0 ↦
    fderiv_shapeGraph_comp_shape_ne_zero (hχr.differentiableAt (by simp)) hc hr0 hp
      (ContinuousLinearMap.ext fun u ↦ by
        have h := mvfderiv_eq_fderiv_apply (𝕜 := ℝ) (shapeGraph (χ ℓ) ∘ shape) p u
        rw [h0] at h
        exact h.symm.trans (zero_apply _))
  have hdg : fderiv ℝ (H ∘ shape + fun _ ↦ ℓ) p = fderiv ℝ (H ∘ shape) p := by
    rw [Pi.add_def, fderiv_add_const]
  have hgf : mvfderiv 𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m))
      (H ∘ shape + fun _ ↦ ℓ) p = (1 / deriv (fun ℓ' ↦ χ ℓ' r) ℓ) •
        mvfderiv 𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m))
          (shapeGraph (χ ℓ) ∘ shape) p := by
    rw [mvfderiv_eq_fderiv, mvfderiv_eq_fderiv, hdg,
      fderiv_shapeLevelFun_comp_shape hχ hconv hmono hℓ hr hp, ContinuousLinearMap.smul_comp]
  have hfg : ∀ᶠ y in 𝓝 p, (shapeGraph (χ ℓ) ∘ shape) y = 0 →
      (H ∘ shape + fun _ ↦ ℓ : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) → ℝ) y = 0 := by
    filter_upwards [eventually_shapeLevelFun_shape_eq (hχ.of_le (by simp)) hconv hmono hℓ hr hp]
      with y hy hy0
    simp only [Pi.add_apply, Function.comp_apply, H, hy hy0, neg_add_cancel]
  have hiff := forall_re_manifoldLeviForm_pos_iff_of_mvfderiv_eq_smul
    (contMDiffAt_iff_contDiffAt.2 hfC) (contMDiffAt_iff_contDiffAt.2 hgC) hfp hf'
    (one_div_pos.2 (hmono ℓ hℓ r hr)) hgf hfg
  have hpos := hiff.2 (fun u hu₁ hu₂ hu ↦ by
    rw [manifoldLeviForm_eq_leviForm]
    exact hconvx.re_leviForm_pos (hχr.of_le (by simp)) hp hu
      ((mvfderiv_eq_fderiv_apply _ _ _).symm.trans hu₁)
      ((mvfderiv_eq_fderiv_apply _ _ _).symm.trans hu₂)) v
    ((mvfderiv_eq_fderiv_apply _ _ _).trans (by rw [hdg]; exact hv₁))
    ((mvfderiv_eq_fderiv_apply _ _ _).trans (by rw [hdg]; exact hv₂)) hv
  rwa [manifoldLeviForm_eq_leviForm, Pi.add_def, leviForm_add_const] at hpos

/-- **The level function of a foliation by `i`-convex shapes.** Let `χ : ℝ → ℝ → ℝ` be smooth in
`(ℓ, r)` on `Ioo ℓ₀ ℓ₁ ×ˢ Ioo r₁ r₂`, with each `χ ℓ` an `i`-convex shape at each `r` there and
`∂χ/∂ℓ > 0` there. Then there is `φ : ℝ × ℝ → ℝ` such that at each point `q = (χ ℓ r ², r ²)`
of the region swept by the leaves, `φ q = -ℓ`, `φ` is smooth at `q` with `∂φ/∂s < 0` and
`∂φ/∂t > 0`, and at every `p ∈ ℂᵏ × ℂᵐ` with `shape p = q` the Levi form of `φ ∘ shape` has
positive real part on the nonzero `v` with `d(φ ∘ shape)_p v = 0` and `d(φ ∘ shape)_p (i v) = 0`,
the nonzero complex tangent vectors of its level through `p`. -/
theorem exists_contDiff_shapeLevel
    (hχ : ContDiffOn ℝ ∞ (Function.uncurry χ) (Ioo ℓ₀ ℓ₁ ×ˢ Ioo r₁ r₂))
    (hconv : ∀ ℓ ∈ Ioo ℓ₀ ℓ₁, ∀ r ∈ Ioo r₁ r₂, IsConvexShapeAt (χ ℓ) r)
    (hmono : ∀ ℓ ∈ Ioo ℓ₀ ℓ₁, ∀ r ∈ Ioo r₁ r₂, 0 < deriv (fun ℓ' ↦ χ ℓ' r) ℓ) :
    ∃ φ : ℝ × ℝ → ℝ, ∀ ℓ ∈ Ioo ℓ₀ ℓ₁, ∀ r ∈ Ioo r₁ r₂,
      φ (χ ℓ r ^ 2, r ^ 2) = -ℓ ∧ ContDiffAt ℝ ∞ φ (χ ℓ r ^ 2, r ^ 2) ∧
      fderiv ℝ φ (χ ℓ r ^ 2, r ^ 2) (1, 0) < 0 ∧ 0 < fderiv ℝ φ (χ ℓ r ^ 2, r ^ 2) (0, 1) ∧
      ∀ {k m : ℕ} (p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)),
        shape p = (χ ℓ r ^ 2, r ^ 2) → ∀ v, v ≠ 0 → fderiv ℝ (φ ∘ shape) p v = 0 →
          fderiv ℝ (φ ∘ shape) p (I • v) = 0 → 0 < (leviForm (φ ∘ shape) p v v).re := by
  have hχ1 : ContDiffOn ℝ 1 (Function.uncurry χ) (Ioo ℓ₀ ℓ₁ ×ˢ Ioo r₁ r₂) :=
    hχ.of_le (by simp)
  refine ⟨shapeLevelFun χ ℓ₀ ℓ₁ r₁ r₂, fun ℓ hℓ r hr ↦ ?_⟩
  have hx : (ℓ, r) ∈ Ioo ℓ₀ ℓ₁ ×ˢ Ioo r₁ r₂ := ⟨hℓ, hr⟩
  obtain ⟨hH, hdH⟩ := contDiffAt_shapeLevelFun hχ hconv hmono hx
  have hval := shapeLevelFun_leafPoint hχ1 hconv hmono hx
  rw [leafPoint_def] at hH hdH hval
  have hconvx := hconv ℓ hℓ r hr
  have hr0 := hconvx.pos
  have hc := hconvx.pos_value
  have hd := hconvx.deriv_pos
  have hA := hmono ℓ hℓ r hr
  refine ⟨hval, hH, ?_, ?_, ?_⟩
  · rw [hdH]
    refine div_neg_of_neg_of_pos ?_ hA
    simp only [zero_mul, zero_div, sub_zero, neg_neg_iff_pos]
    positivity
  · rw [hdH]
    refine div_pos ?_ hA
    simp only [zero_div, zero_sub, one_mul, neg_neg]
    positivity
  exact fun p hp v hv hv₁ hv₂ ↦
    re_leviForm_shapeLevelFun_comp_shape_pos hχ hconv hmono hℓ hr hp hv hv₁ hv₂

end SymplecticGeometry

end
