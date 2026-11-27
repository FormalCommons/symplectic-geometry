/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.JConvex.Surround.ConvexShape

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import SymplecticGeometry.Geometry.Manifold.Complex.JConvex.Hypersurface
import TauCeti.Analysis.Calculus.ParametricFDeriv

/-!
# Foliations by `i`-convex shapes and their level functions

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
(`OpenPartialHomeomorph.contDiffAt_symm`) its local inverses are smooth, and `φ` is minus their
first component. On the level of `φ ∘ shape` through a point of the leaf `ℓ`, the differential of
`φ` is `1 / ∂χ/∂ℓ` times that of `shapeGraph (χ ℓ)`, and the level contains the hypersurface of
the shape `χ ℓ` near the point; so the positivity of the Levi form passes from
`SymplecticGeometry.IsConvexShapeAt.re_leviForm_pos` to `φ ∘ shape` by
`SymplecticGeometry.forall_re_manifoldLeviForm_pos_iff_of_mvfderiv_eq_smul`.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Proposition 3.25 (the function of a foliation) and Corollary 4.29.
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

/-- At a point `(χ ℓ r ², r ²)` of the swept region, the level function is smooth, with
differential `(a, b) ↦ -(a / (2 χ) - b ∂χ/∂r / (2 r)) / ∂χ/∂ℓ`. The leaf map
`(ℓ, r) ↦ (χ ℓ r ², r ²)` has the invertible differential
`(a, b) ↦ (2 χ (a ∂χ/∂ℓ + b ∂χ/∂r), 2 r b)`, and near the point the level function is minus
the first component of its local inverse. -/
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
  have hdx : DifferentiableAt ℝ (Function.uncurry χ) (x.1, x.2) := hχx.differentiableAt (by simp)
  have hA := hasDerivAt_parameterCurve_uncurry hdx
  have hB := hasDerivAt_timeSlice_uncurry hdx
  rw [Prod.mk.eta] at hA hB
  rw [hA.deriv, hB.deriv]
  set A := fderiv ℝ (Function.uncurry χ) x (1, 0)
  set B := fderiv ℝ (Function.uncurry χ) x (0, 1)
  set c := χ x.1 x.2
  have hconvx := hconv x.1 hx.1 x.2 hx.2
  have hr : 0 < x.2 := hconvx.pos
  have hc : 0 < c := hconvx.pos_value
  have hApos : 0 < A := hA.deriv ▸ hmono x.1 hx.1 x.2 hx.2
  have hDlin (a b : ℝ) : fderiv ℝ (Function.uncurry χ) x (a, b) = a * A + b * B := by
    have hab : ((a, b) : ℝ × ℝ) = a • ((1 : ℝ), (0 : ℝ)) + b • ((0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    rw [hab, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
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
  have hL'L : Function.LeftInverse L' L := by
    rintro ⟨a, b⟩
    rw [hL, hL']
    ext
    · field_simp
      ring
    · field_simp
  have hLL' : Function.RightInverse L' L := by
    rintro ⟨a, b⟩
    rw [hL', hL]
    ext
    · field_simp
      ring
    · field_simp
  set e := ContinuousLinearEquiv.ofContinuousLinearMap L L' (ContinuousLinearMap.ext hLL')
    (ContinuousLinearMap.ext hL'L)
  have he : (e : ℝ × ℝ →L[ℝ] ℝ × ℝ) = L :=
    ContinuousLinearMap.ext fun v ↦ by
      rw [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.coe_ofContinuousLinearMap]
  have hleaf : leafPoint χ = fun y ↦ (Function.uncurry χ y ^ 2, y.2 ^ 2) := by
    funext y
    rw [leafPoint_def, Function.uncurry_apply_pair]
  have hΦL : HasFDerivAt (leafPoint χ) L x := by
    rw [hleaf]
    have h₁ : HasFDerivAt (fun y ↦ Function.uncurry χ y ^ 2)
        ((2 • Function.uncurry χ x ^ (2 - 1)) • fderiv ℝ (Function.uncurry χ) x) x :=
      (hχx.differentiableAt (by simp)).hasFDerivAt.pow 2
    have h₂ : HasFDerivAt (fun y : ℝ × ℝ ↦ y.2 ^ 2)
        ((2 • x.2 ^ (2 - 1)) • ContinuousLinearMap.snd ℝ ℝ ℝ) x :=
      (hasFDerivAt_snd (p := x)).pow 2
    have h := h₁.prodMk h₂
    refine h.congr_fderiv ?_
    ext <;> simp [L, c, mul_comm, Function.uncurry_def]
  have hΦ : HasFDerivAt (leafPoint χ) (e : ℝ × ℝ →L[ℝ] ℝ × ℝ) x := he ▸ hΦL
  have hcΦ : ContDiffAt ℝ ∞ (leafPoint χ) x := by
    rw [hleaf]
    exact (hχx.pow 2).prodMk (contDiffAt_snd.pow 2)
  have hs := hcΦ.hasStrictFDerivAt hΦ (by simp)
  set E := hs.toOpenPartialHomeomorph (leafPoint χ)
  have hcoe : (E : ℝ × ℝ → ℝ × ℝ) = leafPoint χ := hs.toOpenPartialHomeomorph_coe
  have hsrc : x ∈ E.source := hs.mem_toOpenPartialHomeomorph_source
  have htgt : leafPoint χ x ∈ E.target := hs.image_mem_toOpenPartialHomeomorph_target
  have hinv : E.symm (leafPoint χ x) = x := by
    have h := E.left_inv hsrc
    rwa [hcoe] at h
  have hsymm : ContDiffAt ℝ ∞ E.symm (leafPoint χ x) :=
    E.contDiffAt_symm htgt (by rw [hinv, hcoe]; exact hΦ) (by rw [hinv, hcoe]; exact hcΦ)
  have heq : shapeLevelFun χ ℓ₀ ℓ₁ r₁ r₂ =ᶠ[𝓝 (leafPoint χ x)] fun q ↦ -(E.symm q).1 := by
    have h1 : E.target ∈ 𝓝 (leafPoint χ x) := E.open_target.mem_nhds htgt
    have h2 : E.symm ⁻¹' (Ioo ℓ₀ ℓ₁ ×ˢ Ioo r₁ r₂) ∈ 𝓝 (leafPoint χ x) :=
      (E.continuousAt_symm htgt).preimage_mem_nhds (by rw [hinv]; exact hD.mem_nhds hx)
    filter_upwards [h1, h2] with q hq1 hq2
    have h := shapeLevelFun_leafPoint hχ1 hconv hmono hq2
    rwa [← hcoe, E.right_inv hq1] at h
  have hH : ContDiffAt ℝ ∞ (shapeLevelFun χ ℓ₀ ℓ₁ r₁ r₂) (leafPoint χ x) :=
    (contDiffAt_fst.comp _ hsymm).neg.congr_of_eventuallyEq heq
  refine ⟨hH, fun a b ↦ ?_⟩
  have hcomp : shapeLevelFun χ ℓ₀ ℓ₁ r₁ r₂ ∘ leafPoint χ =ᶠ[𝓝 x] fun y ↦ -y.1 := by
    filter_upwards [hD.mem_nhds hx] with y hy using shapeLevelFun_leafPoint hχ1 hconv hmono hy
  have hk := fderiv_comp x (hH.differentiableAt (by simp)) hΦL.differentiableAt
  rw [hΦL.fderiv, hcomp.fderiv_eq, (hasFDerivAt_fst (p := x)).fun_neg.fderiv] at hk
  have hk' := congrArg (fun T : ℝ × ℝ →L[ℝ] ℝ ↦ T (L' (a, b))) hk
  simp only [ContinuousLinearMap.comp_apply, hLL' (a, b), neg_apply,
    ContinuousLinearMap.coe_fst'] at hk'
  rw [← hk', hL']
  field_simp

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
  have hD : IsOpen (Ioo ℓ₀ ℓ₁ ×ˢ Ioo r₁ r₂) := isOpen_Ioo.prod isOpen_Ioo
  have hχ1 : ContDiffOn ℝ 1 (Function.uncurry χ) (Ioo ℓ₀ ℓ₁ ×ˢ Ioo r₁ r₂) :=
    hχ.of_le (by simp)
  set H := shapeLevelFun χ ℓ₀ ℓ₁ r₁ r₂ with hH_def
  have hx : (ℓ, r) ∈ Ioo ℓ₀ ℓ₁ ×ˢ Ioo r₁ r₂ := ⟨hℓ, hr⟩
  obtain ⟨hH, hdH⟩ := contDiffAt_shapeLevelFun hχ hconv hmono hx
  rw [leafPoint_def] at hH hdH
  have hconvx := hconv ℓ hℓ r hr
  have hr0 := hconvx.pos
  have hc := hconvx.pos_value
  have hA := hmono ℓ hℓ r hr
  have hs : 0 < χ ℓ r ^ 2 := by positivity
  have ht : 0 < r ^ 2 := by positivity
  have hsR : √(χ ℓ r ^ 2) = χ ℓ r := Real.sqrt_sq hc.le
  have hsr : √(r ^ 2) = r := Real.sqrt_sq hr0.le
  have hχr : ContDiffAt ℝ ∞ (χ ℓ) r :=
    (hχ.contDiffAt (hD.mem_nhds hx)).comp r (contDiffAt_const.prodMk contDiffAt_id)
  have hχr' : ContDiffAt ℝ ∞ (χ ℓ) (√(r ^ 2)) := by rwa [hsr]
  have hG : ContDiffAt ℝ ∞ (shapeGraph (χ ℓ)) (χ ℓ r ^ 2, r ^ 2) :=
    contDiffAt_shapeGraph hχr' hs ht
  have hdG (a b : ℝ) : fderiv ℝ (shapeGraph (χ ℓ)) (χ ℓ r ^ 2, r ^ 2) (a, b) =
      -a / (2 * χ ℓ r) + b * deriv (χ ℓ) r / (2 * r) := by
    rw [fderiv_shapeGraph_apply (hχr'.differentiableAt (by simp)) hs ht, hsR, hsr]
  -- The differential of the level function is `1 / ∂χ/∂ℓ` times that of `shapeGraph (χ ℓ)`.
  have hHG : fderiv ℝ H (χ ℓ r ^ 2, r ^ 2) =
      (1 / deriv (fun ℓ' ↦ χ ℓ' r) ℓ) • fderiv ℝ (shapeGraph (χ ℓ)) (χ ℓ r ^ 2, r ^ 2) := by
    refine ContinuousLinearMap.ext fun w ↦ ?_
    obtain ⟨a, b⟩ := w
    rw [hdH, smul_apply, hdG, smul_eq_mul]
    field_simp
    ring
  have hshape : ContDiffAt ℝ ∞ shape p := contDiff_shape.contDiffAt
  have hHs : ContDiffAt ℝ ∞ (H ∘ shape) p := (hp ▸ hH).comp p hshape
  have hGs : ContDiffAt ℝ ∞ (shapeGraph (χ ℓ) ∘ shape) p := (hp ▸ hG).comp p hshape
  have hdHs : fderiv ℝ (H ∘ shape) p =
      (1 / deriv (fun ℓ' ↦ χ ℓ' r) ℓ) • fderiv ℝ (shapeGraph (χ ℓ) ∘ shape) p := by
    rw [fderiv_comp p ((hp ▸ hH).differentiableAt (by simp)) (hshape.differentiableAt (by simp)),
      fderiv_comp p ((hp ▸ hG).differentiableAt (by simp)) (hshape.differentiableAt (by simp)),
      hp, hHG, ContinuousLinearMap.smul_comp]
  -- The differential of `shapeGraph (χ ℓ) ∘ shape` at `p`.
  have htan (u : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) :
      fderiv ℝ (shapeGraph (χ ℓ) ∘ shape) p u =
        -fderiv ℝ (fun y ↦ (shape y).1) p u / (2 * χ ℓ r) +
          fderiv ℝ (fun y ↦ (shape y).2) p u * deriv (χ ℓ) r / (2 * r) := by
    rw [fderiv_comp p ((hp ▸ hG).differentiableAt (by simp)) (hshape.differentiableAt (by simp)),
      ContinuousLinearMap.comp_apply, fderiv_shape_apply, hp, hdG]
  have hfp : (shapeGraph (χ ℓ) ∘ shape) p = 0 := by
    rw [Function.comp_apply, hp, shapeGraph_def, hsR, hsr, sub_self]
  -- `df_p ≠ 0`: it takes the value `-χ ℓ r` on the real part of `p₁`.
  have hf' : mvfderiv 𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m))
      (shapeGraph (χ ℓ) ∘ shape) p ≠ 0 := by
    intro h0
    have h1 : fderiv ℝ (shapeGraph (χ ℓ) ∘ shape) p
        (WithLp.toLp 2 (fun j ↦ ((p.1 j).re : ℂ)), 0) = 0 := by
      have h := mvfderiv_eq_fderiv_apply (𝕜 := ℝ) (shapeGraph (χ ℓ) ∘ shape) p
        (WithLp.toLp 2 (fun j ↦ ((p.1 j).re : ℂ)), 0)
      rw [h0] at h
      exact h.symm.trans (zero_apply _)
    rw [htan, fderiv_shape_fst_apply, fderiv_shape_snd_apply] at h1
    have hsum : ∑ j, (p.1 j).re * (p.1 j).re = χ ℓ r ^ 2 := by
      have h2 : (shape p).1 = χ ℓ r ^ 2 := by rw [hp]
      rw [shape_fst] at h2
      rw [← h2]
      exact Finset.sum_congr rfl fun j _ ↦ (sq _).symm
    simp only [ofReal_re, ofReal_im, mul_zero, Finset.sum_const_zero,
      inner_zero_right, zero_re, add_zero, hsum] at h1
    field_simp at h1
    exact hc.ne' (by nlinarith [h1])
  -- Near `p`, the hypersurface of the shape `χ ℓ` lies in the level `-ℓ` of `H`.
  have hev : ∀ᶠ y in 𝓝 p, √(shape y).2 ∈ Ioo r₁ r₂ := by
    have hcont : ContinuousAt (fun y ↦ √(shape y).2) p :=
      (Real.continuous_sqrt.comp (contDiff_shape (n := 0)).continuous.snd).continuousAt
    refine hcont.preimage_mem_nhds (isOpen_Ioo.mem_nhds ?_)
    rw [hp, hsr]
    exact hr
  have hfg : ∀ᶠ y in 𝓝 p,
      (shapeGraph (χ ℓ) ∘ shape) y = 0 → (H ∘ shape + fun _ ↦ ℓ :
        EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) → ℝ) y = 0 := by
    filter_upwards [hev] with y hy hy0
    rw [Function.comp_apply, shapeGraph_def, sub_eq_zero] at hy0
    have hy' : shape y = leafPoint χ (ℓ, √(shape y).2) := by
      rw [leafPoint_def]
      ext
      · rw [hy0, Real.sq_sqrt (shape_fst_nonneg y)]
      · rw [Real.sq_sqrt (shape_snd_nonneg y)]
    rw [Pi.add_apply, Function.comp_apply, hy', hH_def,
      shapeLevelFun_leafPoint hχ1 hconv hmono ⟨hℓ, hy⟩, neg_add_cancel]
  have hfC : ContDiffAt ℝ 3 (shapeGraph (χ ℓ) ∘ shape) p := hGs.of_le (by simp)
  have hHs3 : ContDiffAt ℝ 3 (H ∘ shape) p := hHs.of_le (by simp)
  have hgC : ContDiffAt ℝ 3 (H ∘ shape + fun _ ↦ ℓ) p := hHs3.add contDiffAt_const
  have hdg : fderiv ℝ (H ∘ shape + fun _ ↦ ℓ) p = fderiv ℝ (H ∘ shape) p := by
    rw [Pi.add_def, fderiv_add_const]
  have hgf : mvfderiv 𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m))
      (H ∘ shape + fun _ ↦ ℓ) p = (1 / deriv (fun ℓ' ↦ χ ℓ' r) ℓ) •
        mvfderiv 𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m))
          (shapeGraph (χ ℓ) ∘ shape) p := by
    rw [mvfderiv_eq_fderiv, mvfderiv_eq_fderiv, hdg, hdHs, ContinuousLinearMap.smul_comp]
  have hiff := forall_re_manifoldLeviForm_pos_iff_of_mvfderiv_eq_smul
    (contMDiffAt_iff_contDiffAt.2 hfC) (contMDiffAt_iff_contDiffAt.2 hgC) hfp hf'
    (by positivity) hgf hfg
  have hpos := hiff.2 (fun u hu₁ hu₂ hu ↦ by
    rw [manifoldLeviForm_eq_leviForm]
    exact hconvx.re_leviForm_pos (hχr.of_le (by simp)) hp hu
      ((mvfderiv_eq_fderiv_apply _ _ _).symm.trans hu₁)
      ((mvfderiv_eq_fderiv_apply _ _ _).symm.trans hu₂)) v
    ((mvfderiv_eq_fderiv_apply _ _ _).trans (by rw [hdg]; exact hv₁))
    ((mvfderiv_eq_fderiv_apply _ _ _).trans (by rw [hdg]; exact hv₂)) hv
  rwa [manifoldLeviForm_eq_leviForm, leviForm_add (hHs.of_le (by simp)) contDiffAt_const,
    leviForm_const, add_zero] at hpos

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
