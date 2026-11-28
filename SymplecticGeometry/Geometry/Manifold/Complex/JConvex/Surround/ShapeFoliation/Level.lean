/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.JConvex.Surround.ConvexShape.Basic

import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.Deriv.Shift
import SymplecticGeometry.Topology.Algebra.Module.Equiv.Prod
import TauCeti.Analysis.Calculus.ContDiff.Prod
import TauCeti.Analysis.Calculus.ParametricFDeriv
import TauCeti.Analysis.Normed.Operator.Prod

/-!
# The level function of a foliation by `i`-convex shapes

Let `χ : ℝ → ℝ → ℝ` be a family of shapes `R = χ ℓ r`, smooth in `(ℓ, r)` on a product of open
intervals, each `χ ℓ` an `i`-convex shape (`SymplecticGeometry.IsConvexShapeAt`) at each point,
with `∂χ/∂ℓ > 0`. Its leaves `{(s, t) = (χ ℓ r ², r ²)}` in the quadrant of the shape coordinates
`(s, t)` are then disjoint, and this file builds the function that is `-ℓ` on the leaf `ℓ`, and
its form for families of curves `r = ρ ℓ R` over `R`.

* `SymplecticGeometry.exists_contDiff_shapeLevel`: there is `φ : ℝ × ℝ → ℝ`, equal to `-ℓ` at
  `(χ ℓ r ², r ²)` and smooth there, with `∂φ/∂s < 0` and `∂φ/∂t > 0`, such that the Levi form
  of `φ ∘ shape` is positive on the nonzero complex tangencies of its levels at every point over
  the swept region.
* `SymplecticGeometry.exists_contDiff_shapeLevel_overR`: the same for a smooth family of curves
  `r = ρ ℓ R` satisfying `SymplecticGeometry.IsConvexShapeOverRAt`, with `∂ρ/∂ℓ < 0`: `φ` is
  `-ℓ` at `(R ², ρ ℓ R ²)`, with `∂φ/∂t > 0` and `∂φ/∂s = ρ' / (2 R ∂ρ/∂ℓ)`. Unlike the form
  over `r`, `∂φ/∂s` has the sign of `-ρ'`, which the criterion over `R` leaves free.

Both proofs share two steps.

* `SymplecticGeometry.exists_contDiffAt_familyLevel`: the part that needs no convexity, only
  `0 < r`, `0 < χ ℓ r` and `∂χ/∂ℓ > 0`: the value `-ℓ`, the smoothness and the differential of
  `φ`. The map `(ℓ, r) ↦ (χ ℓ r ², r ²)` has an invertible differential, triangular with
  diagonal `2 χ ∂χ/∂ℓ` and `2 r`, so by the inverse function theorem
  (`ContDiffAt.to_localInverse`, `HasStrictFDerivAt.to_localInverse`) its local inverses are
  smooth, and `φ` is minus their first component. Over `R` it is applied to `ℓ ↦ ρ (-ℓ)`, with
  the two coordinates exchanged.
* `SymplecticGeometry.re_leviForm_comp_shape_pos_of_fderiv_eq_smul`: if `dφ = c • dG` with
  `c > 0` at a zero of `G`, and the level of `φ` contains `{G = 0}` nearby, the positivity of the
  Levi form on complex tangencies passes from `G ∘ shape` to `φ ∘ shape`, by
  `SymplecticGeometry.forall_re_manifoldLeviForm_pos_iff_of_mvfderiv_eq_smul`. It is applied with
  `G = shapeGraph (χ ℓ)` and `c = 1 / ∂χ/∂ℓ`, using
  `SymplecticGeometry.IsConvexShapeAt.re_leviForm_pos` and
  `SymplecticGeometry.fderiv_shapeGraph_comp_shape_ne_zero`, and with `G = shapeGraphOverR (ρ ℓ)`
  and `c = -1 / ∂ρ/∂ℓ`, using `SymplecticGeometry.IsConvexShapeOverRAt.re_leviForm_pos` and
  `SymplecticGeometry.fderiv_shapeGraphOverR_comp_shape_ne_zero`. The level condition comes from
  `SymplecticGeometry.eventually_eq_of_shapeGraph_eq_zero` and
  `SymplecticGeometry.eventually_eq_of_shapeGraphOverR_eq_zero`.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Proposition 3.25 (the function of a foliation), and Corollary 4.29 for the curves over `R`.
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

/-- The positivity of `r` and of `χ ℓ r` that the criterion gives. -/
private theorem forall_pos_of_isConvexShapeAt
    (hconv : ∀ ℓ ∈ Ioo ℓ₀ ℓ₁, ∀ r ∈ Ioo r₁ r₂, IsConvexShapeAt (χ ℓ) r) :
    ∀ ℓ ∈ Ioo ℓ₀ ℓ₁, ∀ r ∈ Ioo r₁ r₂, 0 < r ∧ 0 < χ ℓ r :=
  fun ℓ hℓ r hr ↦ ⟨(hconv ℓ hℓ r hr).pos, (hconv ℓ hℓ r hr).pos_value⟩

/-- The leaf map is injective on the product of intervals. -/
private theorem injOn_leafPoint
    (hχ : ContDiffOn ℝ 1 (Function.uncurry χ) (Ioo ℓ₀ ℓ₁ ×ˢ Ioo r₁ r₂))
    (hpos : ∀ ℓ ∈ Ioo ℓ₀ ℓ₁, ∀ r ∈ Ioo r₁ r₂, 0 < r ∧ 0 < χ ℓ r)
    (hmono : ∀ ℓ ∈ Ioo ℓ₀ ℓ₁, ∀ r ∈ Ioo r₁ r₂, 0 < deriv (fun ℓ' ↦ χ ℓ' r) ℓ) :
    InjOn (leafPoint χ) (Ioo ℓ₀ ℓ₁ ×ˢ Ioo r₁ r₂) := by
  rintro ⟨ℓ, r⟩ ⟨hℓ, hr⟩ ⟨ℓ', r'⟩ ⟨hℓ', hr'⟩ h
  simp only [leafPoint_def, Prod.mk.injEq] at h
  have hrr : r = r' := by
    have h0 := (hpos ℓ hℓ r hr).1
    have h1 := (hpos ℓ' hℓ' r' hr').1
    nlinarith [h.2]
  subst hrr
  have h0 := (hpos ℓ hℓ r hr).2
  have h1 := (hpos ℓ' hℓ' r hr').2
  have hχχ : χ ℓ r = χ ℓ' r := by nlinarith [h.1]
  exact Prod.ext ((strictMonoOn_shapeFamily hχ hmono hr).injOn hℓ hℓ' hχχ) rfl

open Classical in
/-- The level function of the family: `-ℓ` at the point `(χ ℓ r ², r ²)` of the leaf `ℓ`, and
`0` off the swept region. -/
private def shapeLevelFun (χ : ℝ → ℝ → ℝ) (ℓ₀ ℓ₁ r₁ r₂ : ℝ) (q : ℝ × ℝ) : ℝ :=
  if h : ∃ x ∈ Ioo ℓ₀ ℓ₁ ×ˢ Ioo r₁ r₂, leafPoint χ x = q then -h.choose.1 else 0

private theorem shapeLevelFun_leafPoint
    (hχ : ContDiffOn ℝ 1 (Function.uncurry χ) (Ioo ℓ₀ ℓ₁ ×ˢ Ioo r₁ r₂))
    (hpos : ∀ ℓ ∈ Ioo ℓ₀ ℓ₁, ∀ r ∈ Ioo r₁ r₂, 0 < r ∧ 0 < χ ℓ r)
    (hmono : ∀ ℓ ∈ Ioo ℓ₀ ℓ₁, ∀ r ∈ Ioo r₁ r₂, 0 < deriv (fun ℓ' ↦ χ ℓ' r) ℓ)
    {x : ℝ × ℝ} (hx : x ∈ Ioo ℓ₀ ℓ₁ ×ˢ Ioo r₁ r₂) :
    shapeLevelFun χ ℓ₀ ℓ₁ r₁ r₂ (leafPoint χ x) = -x.1 := by
  have h : ∃ y ∈ Ioo ℓ₀ ℓ₁ ×ˢ Ioo r₁ r₂, leafPoint χ y = leafPoint χ x := ⟨x, hx, rfl⟩
  rw [shapeLevelFun, dite_eq_left_of_eq_true (eq_true h),
    injOn_leafPoint hχ hpos hmono h.choose_spec.1 hx h.choose_spec.2]

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
    (hpos : ∀ ℓ ∈ Ioo ℓ₀ ℓ₁, ∀ r ∈ Ioo r₁ r₂, 0 < r ∧ 0 < χ ℓ r)
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
  have hposx := hpos x.1 hx.1 x.2 hx.2
  have hA := hmono x.1 hx.1 x.2 hx.2
  obtain ⟨e, hΦ, he⟩ := hasFDerivAt_leafPoint (hχx.differentiableAt (by simp))
    hposx.2.ne' hposx.1.ne' hA.ne'
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
    have h := shapeLevelFun_leafPoint hχ1 hpos hmono hq₂
    rwa [hq₁] at h
  refine ⟨(contDiffAt_fst.comp _ (hcΦ.to_localInverse hΦ (by simp))).neg.congr_of_eventuallyEq
    heq, fun a b ↦ ?_⟩
  have hd := ((hasFDerivAt_fst.comp _ hs.to_localInverse.hasFDerivAt).neg).congr_of_eventuallyEq
    heq
  rw [hd.fderiv, neg_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearEquiv.coe_coe, he]
  field_simp

/-- **The level function of a family of curves.** Let `χ : ℝ → ℝ → ℝ` be smooth in `(ℓ, r)` on
`Ioo ℓ₀ ℓ₁ ×ˢ Ioo r₁ r₂`, with `0 < r`, `0 < χ ℓ r` and `∂χ/∂ℓ > 0` there. Then there is
`φ : ℝ × ℝ → ℝ` such that at each point `q = (χ ℓ r ², r ²)` of the swept region, `φ q = -ℓ`,
`φ` is smooth at `q`, and its differential there is
`(a, b) ↦ -(a / (2 χ ℓ r) - b ∂χ/∂r / (2 r)) / ∂χ/∂ℓ`. No convexity is assumed: this is the
part of `exists_contDiff_shapeLevel` that the inverse function theorem gives, shared with its
form over `R`. -/
theorem exists_contDiffAt_familyLevel
    (hχ : ContDiffOn ℝ ∞ (Function.uncurry χ) (Ioo ℓ₀ ℓ₁ ×ˢ Ioo r₁ r₂))
    (hpos : ∀ ℓ ∈ Ioo ℓ₀ ℓ₁, ∀ r ∈ Ioo r₁ r₂, 0 < r ∧ 0 < χ ℓ r)
    (hmono : ∀ ℓ ∈ Ioo ℓ₀ ℓ₁, ∀ r ∈ Ioo r₁ r₂, 0 < deriv (fun ℓ' ↦ χ ℓ' r) ℓ) :
    ∃ φ : ℝ × ℝ → ℝ, ∀ ℓ ∈ Ioo ℓ₀ ℓ₁, ∀ r ∈ Ioo r₁ r₂,
      φ (χ ℓ r ^ 2, r ^ 2) = -ℓ ∧ ContDiffAt ℝ ∞ φ (χ ℓ r ^ 2, r ^ 2) ∧
      ∀ a b : ℝ, fderiv ℝ φ (χ ℓ r ^ 2, r ^ 2) (a, b) =
        -(a / (2 * χ ℓ r) - b * deriv (χ ℓ) r / (2 * r)) / deriv (fun ℓ' ↦ χ ℓ' r) ℓ := by
  refine ⟨shapeLevelFun χ ℓ₀ ℓ₁ r₁ r₂, fun ℓ hℓ r hr ↦ ?_⟩
  have hx : (ℓ, r) ∈ Ioo ℓ₀ ℓ₁ ×ˢ Ioo r₁ r₂ := ⟨hℓ, hr⟩
  obtain ⟨hH, hdH⟩ := contDiffAt_shapeLevelFun hχ hpos hmono hx
  have hval := shapeLevelFun_leafPoint (hχ.of_le (by simp)) hpos hmono hx
  rw [leafPoint_def] at hH hdH hval
  exact ⟨hval, hH, hdH⟩

/-! ### The level function of a foliation by shapes -/

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
  obtain ⟨φ, hφ⟩ := exists_contDiffAt_familyLevel hχ (forall_pos_of_isConvexShapeAt hconv) hmono
  refine ⟨φ, fun ℓ hℓ r hr ↦ ?_⟩
  obtain ⟨hval, hH, hdH⟩ := hφ ℓ hℓ r hr
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
  intro k m p hp v hv hv₁ hv₂
  have hχr : ContDiffAt ℝ ∞ (χ ℓ) r :=
    (hχ.contDiffAt (x := (ℓ, r)) ((isOpen_Ioo.prod isOpen_Ioo).mem_nhds ⟨hℓ, hr⟩)).uncurry_left
  have hG : ContDiffAt ℝ ∞ (shapeGraph (χ ℓ)) (χ ℓ r ^ 2, r ^ 2) :=
    contDiffAt_shapeGraph (by rwa [Real.sqrt_sq hr0.le]) (by positivity) (by positivity)
  -- At the point of the leaf, `dφ` is `1 / ∂χ/∂ℓ` times the differential of `shapeGraph (χ ℓ)`.
  have hdφ : fderiv ℝ φ (χ ℓ r ^ 2, r ^ 2) =
      (1 / deriv (fun ℓ' ↦ χ ℓ' r) ℓ) • fderiv ℝ (shapeGraph (χ ℓ)) (χ ℓ r ^ 2, r ^ 2) := by
    refine ContinuousLinearMap.ext fun ⟨a, b⟩ ↦ ?_
    rw [smul_apply, hdH, fderiv_shapeGraph_apply (by
        rw [Real.sqrt_sq hr0.le]; exact hχr.differentiableAt (by simp))
        (by positivity) (by positivity), Real.sqrt_sq hc.le, Real.sqrt_sq hr0.le, smul_eq_mul]
    field_simp
    ring
  refine re_leviForm_comp_shape_pos_of_fderiv_eq_smul hp (hG.of_le (by simp))
    (hH.of_le (by simp)) (shapeGraph_sq_sq hc.le hr0.le)
    (fderiv_shapeGraph_comp_shape_ne_zero (hχr.differentiableAt (by simp)) hc hr0 hp)
    (one_div_pos.2 hA) hdφ (eventually_eq_of_shapeGraph_eq_zero (c₀ := -ℓ) hr0 hc ?_)
    (fun u hu hu₁ hu₂ ↦ hconvx.re_leviForm_pos (hχr.of_le (by simp)) hp hu hu₁ hu₂) hv hv₁ hv₂
  filter_upwards [Ioo_mem_nhds hr.1 hr.2] with r' hr' using (hφ ℓ hℓ r' hr').1

/-! ### The level function of a foliation by shapes over `R` -/

/-- **The level function of a foliation by shapes over `R`.** Let `ρ : ℝ → ℝ → ℝ` be smooth in
`(ℓ, R)` on `Ioo ℓ₀ ℓ₁ ×ˢ Ioo R₁ R₂`, with each curve `r = ρ ℓ R` satisfying the criterion over
`R` (`SymplecticGeometry.IsConvexShapeOverRAt`) at each `R` there and `∂ρ/∂ℓ < 0` there. Then
there is `φ : ℝ × ℝ → ℝ` such that at each point `q = (R ², ρ ℓ R ²)` of the region swept by the
leaves, `φ q = -ℓ`, `φ` is smooth at `q` with `∂φ/∂t > 0` and
`∂φ/∂s = ρ' / (2 R ∂ρ/∂ℓ)`, for `ρ' = ∂ρ/∂R` (so `∂φ/∂s ≤ 0` where `ρ' ≥ 0`, and `< 0` where
`ρ' > 0`), and at every `p ∈ ℂᵏ × ℂᵐ` with `shape p = q` the Levi form of `φ ∘ shape` has
positive real part on the nonzero `v` with `d(φ ∘ shape)_p v = 0` and `d(φ ∘ shape)_p (i v) = 0`,
the nonzero complex tangent vectors of its level through `p`. -/
theorem exists_contDiff_shapeLevel_overR {ρ : ℝ → ℝ → ℝ} {R₁ R₂ : ℝ}
    (hρ : ContDiffOn ℝ ∞ (Function.uncurry ρ) (Ioo ℓ₀ ℓ₁ ×ˢ Ioo R₁ R₂))
    (hconv : ∀ ℓ ∈ Ioo ℓ₀ ℓ₁, ∀ R ∈ Ioo R₁ R₂, IsConvexShapeOverRAt (ρ ℓ) R)
    (hmono : ∀ ℓ ∈ Ioo ℓ₀ ℓ₁, ∀ R ∈ Ioo R₁ R₂, deriv (fun ℓ' ↦ ρ ℓ' R) ℓ < 0) :
    ∃ φ : ℝ × ℝ → ℝ, ∀ ℓ ∈ Ioo ℓ₀ ℓ₁, ∀ R ∈ Ioo R₁ R₂,
      φ (R ^ 2, ρ ℓ R ^ 2) = -ℓ ∧ ContDiffAt ℝ ∞ φ (R ^ 2, ρ ℓ R ^ 2) ∧
      0 < fderiv ℝ φ (R ^ 2, ρ ℓ R ^ 2) (0, 1) ∧
      fderiv ℝ φ (R ^ 2, ρ ℓ R ^ 2) (1, 0) =
        deriv (ρ ℓ) R / (2 * R * deriv (fun ℓ' ↦ ρ ℓ' R) ℓ) ∧
      ∀ {k m : ℕ} (p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)),
        shape p = (R ^ 2, ρ ℓ R ^ 2) → ∀ v, v ≠ 0 → fderiv ℝ (φ ∘ shape) p v = 0 →
          fderiv ℝ (φ ∘ shape) p (I • v) = 0 → 0 < (leviForm (φ ∘ shape) p v v).re := by
  -- The family `ℓ ↦ ρ (-ℓ)`, with the coordinates swapped, is a family as in
  -- `exists_contDiffAt_familyLevel`.
  have hneg' : ∀ ℓ ∈ Ioo (-ℓ₁) (-ℓ₀), -ℓ ∈ Ioo ℓ₀ ℓ₁ := fun ℓ hℓ ↦
    ⟨lt_neg_of_lt_neg hℓ.2, neg_lt.1 hℓ.1⟩
  have hneg : MapsTo (fun x : ℝ × ℝ ↦ (-x.1, x.2)) (Ioo (-ℓ₁) (-ℓ₀) ×ˢ Ioo R₁ R₂)
      (Ioo ℓ₀ ℓ₁ ×ˢ Ioo R₁ R₂) := fun x hx ↦ ⟨hneg' x.1 hx.1, hx.2⟩
  obtain ⟨ψ, hψ⟩ := exists_contDiffAt_familyLevel (χ := fun ℓ R ↦ ρ (-ℓ) R)
    (hρ.comp (contDiff_fst.neg.prodMk contDiff_snd).contDiffOn hneg)
    (fun ℓ hℓ R hR ↦ ⟨(hconv (-ℓ) (hneg' ℓ hℓ) R hR).pos,
      (hconv (-ℓ) (hneg' ℓ hℓ) R hR).pos_value⟩)
    (fun ℓ hℓ R hR ↦ by
      rw [deriv_comp_neg (f := fun ℓ' ↦ ρ ℓ' R)]
      exact neg_pos.2 (hmono (-ℓ) (hneg' ℓ hℓ) R hR))
  set L := ContinuousLinearEquiv.prodComm ℝ ℝ ℝ with hLdef
  refine ⟨fun q ↦ -ψ (L q), fun ℓ hℓ R hR ↦ ?_⟩
  have hℓ' : -ℓ ∈ Ioo (-ℓ₁) (-ℓ₀) := ⟨neg_lt_neg hℓ.2, neg_lt_neg hℓ.1⟩
  obtain ⟨hv, hc, hd⟩ := hψ (-ℓ) hℓ' R hR
  have hconvx := hconv ℓ hℓ R hR
  have hR0 := hconvx.pos
  have hr0 := hconvx.pos_value
  have hA := hmono ℓ hℓ R hR
  have hAeq : deriv (fun ℓ' ↦ ρ (-ℓ') R) (-ℓ) = -deriv (fun ℓ' ↦ ρ ℓ' R) ℓ := by
    rw [deriv_comp_neg (f := fun ℓ' ↦ ρ ℓ' R), neg_neg]
  simp only [neg_neg] at hv hc hd
  rw [hAeq] at hd
  have hLq : L (R ^ 2, ρ ℓ R ^ 2) = (ρ ℓ R ^ 2, R ^ 2) := by
    rw [hLdef, ContinuousLinearEquiv.coe_prodComm, Prod.swap_prod_mk]
  have hφd : HasFDerivAt (fun q ↦ -ψ (L q))
      (-(fderiv ℝ ψ (ρ ℓ R ^ 2, R ^ 2)).comp (L : ℝ × ℝ →L[ℝ] ℝ × ℝ)) (R ^ 2, ρ ℓ R ^ 2) := by
    have h := (hc.differentiableAt (by simp)).hasFDerivAt
    rw [← hLq] at h
    exact (h.comp _ L.hasFDerivAt).neg
  have hdφ (a b : ℝ) : fderiv ℝ (fun q ↦ -ψ (L q)) (R ^ 2, ρ ℓ R ^ 2) (a, b) =
      (b / (2 * ρ ℓ R) - a * deriv (ρ ℓ) R / (2 * R)) / -deriv (fun ℓ' ↦ ρ ℓ' R) ℓ := by
    rw [hφd.fderiv, neg_apply, ContinuousLinearMap.comp_apply]
    have hL : (L : ℝ × ℝ →L[ℝ] ℝ × ℝ) (a, b) = (b, a) := by
      rw [ContinuousLinearEquiv.coe_coe, hLdef, ContinuousLinearEquiv.coe_prodComm,
        Prod.swap_prod_mk]
    rw [hL, hd]
    ring
  have hφc : ContDiffAt ℝ ∞ (fun q ↦ -ψ (L q)) (R ^ 2, ρ ℓ R ^ 2) :=
    ((hLq ▸ hc).comp _ L.contDiff.contDiffAt).neg
  have hval : ∀ R' ∈ Ioo R₁ R₂, -ψ (L (R' ^ 2, ρ ℓ R' ^ 2)) = -ℓ := fun R' hR' ↦ by
    have h := (hψ (-ℓ) hℓ' R' hR').1
    simp only [neg_neg] at h
    rw [hLdef, ContinuousLinearEquiv.coe_prodComm, Prod.swap_prod_mk, h]
  refine ⟨hval R hR, hφc, ?_, ?_, ?_⟩
  · rw [hdφ]
    refine div_pos ?_ (neg_pos.2 hA)
    simp only [zero_mul, zero_div, sub_zero]
    positivity
  · rw [hdφ]
    field_simp
    ring
  intro k m p hp v hv0 hv₁ hv₂
  have hρℓ : ContDiffAt ℝ ∞ (ρ ℓ) R :=
    (hρ.contDiffAt (x := (ℓ, R)) ((isOpen_Ioo.prod isOpen_Ioo).mem_nhds ⟨hℓ, hR⟩)).uncurry_left
  have hG : ContDiffAt ℝ ∞ (shapeGraphOverR (ρ ℓ)) (R ^ 2, ρ ℓ R ^ 2) :=
    contDiffAt_shapeGraphOverR (by rwa [Real.sqrt_sq hR0.le]) (by positivity) (by positivity)
  refine re_leviForm_comp_shape_pos_of_fderiv_eq_smul hp (hG.of_le (by simp)) (hφc.of_le (by simp))
    (shapeGraphOverR_sq_sq hR0.le hr0.le)
    (fderiv_shapeGraphOverR_comp_shape_ne_zero (hρℓ.differentiableAt (by simp)) hR0 hr0 hp)
    (c := 1 / -deriv (fun ℓ' ↦ ρ ℓ' R) ℓ) (one_div_pos.2 (neg_pos.2 hA)) ?_
    (eventually_eq_of_shapeGraphOverR_eq_zero hR0 hr0
      (Filter.eventually_of_mem (Ioo_mem_nhds hR.1 hR.2) hval))
    (fun u hu hu₁ hu₂ ↦ hconvx.re_leviForm_pos (hρℓ.of_le (by simp)) hp hu hu₁ hu₂) hv0 hv₁ hv₂
  refine ContinuousLinearMap.ext fun ⟨a, b⟩ ↦ ?_
  rw [smul_apply, hdφ, fderiv_shapeGraphOverR_apply (by
      rw [Real.sqrt_sq hR0.le]; exact hρℓ.differentiableAt (by simp)) (by positivity)
      (by positivity), Real.sqrt_sq hR0.le, Real.sqrt_sq hr0.le, smul_eq_mul]
  field_simp
  ring

end SymplecticGeometry

end
