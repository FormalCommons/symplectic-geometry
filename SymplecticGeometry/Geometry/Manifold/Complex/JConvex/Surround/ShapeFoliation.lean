/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Analysis.SpecialFunctions.SmoothedMax
public import SymplecticGeometry.Geometry.Manifold.Complex.JConvex.Surround.ConvexShape.Basic
public import TauCeti.Geometry.Manifold.Instances.Icc.CollaredSmoothTransition

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import SymplecticGeometry.Algebra.BigOperators.Module
import SymplecticGeometry.Analysis.Calculus.BumpFunction.SmoothApprox
import SymplecticGeometry.Analysis.Calculus.Deriv.Rectangle
import SymplecticGeometry.Analysis.Calculus.IteratedDeriv.Lemmas
import SymplecticGeometry.Analysis.SpecialFunctions.SmoothTransition.Basic
import SymplecticGeometry.Geometry.Manifold.Complex.JConvex.Hypersurface
import SymplecticGeometry.Geometry.Manifold.Complex.JConvex.Surround.ConvexShape.SmoothedMax
import TauCeti.Analysis.Calculus.ParametricFDeriv
import TauCeti.Analysis.Normed.Operator.Prod

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
(`ContDiffAt.to_localInverse`, `HasStrictFDerivAt.to_localInverse`) its local inverses are smooth,
and `φ` is minus their first component. On the level of `φ ∘ shape` through a point of the leaf
`ℓ`, the differential of `φ` is `1 / ∂χ/∂ℓ` times that of `shapeGraph (χ ℓ)`, and the level
contains the hypersurface of the shape `χ ℓ` near the point; so the positivity of the Levi form
passes from `SymplecticGeometry.IsConvexShapeAt.re_leviForm_pos` to `φ ∘ shape` by
`SymplecticGeometry.forall_re_manifoldLeviForm_pos_iff_of_mvfderiv_eq_smul`, with
`SymplecticGeometry.fderiv_shapeGraph_comp_shape_ne_zero` for the nonvanishing of the
differential of `shapeGraph (χ ℓ) ∘ shape`.

The file also gives one step of a weakly increasing chain of shapes:

* `SymplecticGeometry.smoothedMaxPath δ η M A`: the path
  `σ ↦ (r ↦ smoothedMax δ (M r) (A r - (1 - ρ σ) η))`, `ρ = TauCeti.collaredSmoothTransition`,
  from the smoothed maximum of `M` and `A - η` (up to `σ = 1 / 4`,
  `SymplecticGeometry.smoothedMaxPath_of_le`) to that of `M` and `A` (from `σ = 3 / 4`,
  `SymplecticGeometry.smoothedMaxPath_of_ge`). It is smooth in `(σ, r)`
  (`SymplecticGeometry.contDiff_smoothedMaxPath`) and, for `η ≥ 0`, monotone in `σ`
  (`SymplecticGeometry.monotone_smoothedMaxPath`, so `Monotone.deriv_nonneg` makes its
  `σ`-derivative nonnegative), since `smoothedMax` is monotone in its second
  argument and `ρ` is monotone (`TauCeti.monotone_collaredSmoothTransition`). It consists of
  `i`-convex shapes where `M` and `A - η` are and `δ (M' + A') ≤ 2 r`
  (`SymplecticGeometry.isConvexShapeAt_smoothedMaxPath`, from
  `SymplecticGeometry.isConvexShapeAt_smoothedMax`), with margins at least the smaller of those
  of `M` and of `A - η` (`SymplecticGeometry.min_le_deriv_smoothedMaxPath_div_sub_one_div`,
  `SymplecticGeometry.min_le_iteratedDeriv_two_smoothedMaxPath_add_pow_three_div_sub_one_div`).
  Each shape of the path is the smoothed maximum of `M` and some `A - c` with `c ∈ [0, η]`
  (`SymplecticGeometry.exists_mem_Icc_smoothedMaxPath_eq`). The margins of `A - η` are those of
  `A` less `η / (A (A - η))` (`SymplecticGeometry.deriv_sub_const_div_sub_one_div_sub_const`),
  which lets a caller choose `η` from a margin of `A`.

These paths, between consecutive members `M i` and `M (i + 1)` of the chain of smoothed maxima
`M = SymplecticGeometry.smoothedMaxChain δ A`, string together into one family:

* `SymplecticGeometry.shapeChain δ η a h A N`: on the mesh `a + i h`, `i ≤ N`, the sum of `M 0`
  and, for each `i < N`, the increment of the `i`-th path at the parameter `(ℓ - a - i h) / h`
  over its value at `0`. Written as a sum rather than glued piece by piece, it is smooth on all of
  `ℝ²` (`SymplecticGeometry.contDiff_shapeChain`), monotone in `ℓ` for `h > 0` and `η ≥ 0`
  (`SymplecticGeometry.monotone_shapeChain`), `A 0` up to `ℓ = a + h / 4`
  (`SymplecticGeometry.shapeChain_of_le`) and constant in `ℓ` from `ℓ = a + (N - 1 / 4) h` on
  (`SymplecticGeometry.shapeChain_eq_of_ge`). Where the joints match,
  `A (i + 1) - η + δ ≤ M i` for `i < N`, the sum telescopes: between `a + j h` and
  `a + (j + 1) h` it is the `j`-th path (`SymplecticGeometry.shapeChain_eq_smoothedMaxPath`), and
  from `a + N h` on it is `M N` (`SymplecticGeometry.shapeChain_eq_smoothedMaxChain`), also as
  germs along a filter on which the joints eventually match
  (`SymplecticGeometry.shapeChain_eventuallyEq_smoothedMaxPath`,
  `SymplecticGeometry.shapeChain_eventuallyEq_smoothedMaxChain`). Its members are then
  `i`-convex shapes at each `r` where the joints match nearby, the `A i` are `C²` and `i`-convex
  shapes at `r` with `deriv (A i) r ≤ G` and `δ G ≤ r`, and the `A (i + 1) - η` are `i`-convex
  shapes at `r` (`SymplecticGeometry.isConvexShapeAt_shapeChain`): `A 0` before the mesh, `M N`
  after it, and a path between smoothed maxima on each of its intervals. Where moreover
  `A 0, …, A j` climb by `δ` near `r`, so that `M j = A j` there, a member on the `j`-th interval
  is the smoothed maximum of `A j` and some `A (j + 1) - c`, `c ∈ [0, η]`, near `r`; its value and
  first two derivatives at `r` are then within the farther of those of `A j` and `A (j + 1)` of
  any given values, up to `η + δ / 2` and a curvature term of order `1 / δ`
  (`SymplecticGeometry.abs_iteratedDeriv_shapeChain_sub_le`, from
  `SymplecticGeometry.abs_iteratedDeriv_two_smoothedMax_sub_le` and its analogues).

The members `A i` of such a chain are smooth stand-ins for members `χ ℓ` of a family that is only
`C²` away from an open set where it is smooth:

* `SymplecticGeometry.exists_contDiff_abs_iteratedDeriv_sub_lt_of_mem_Icc`: a smooth `g` within
  `θ` of `χ ℓ` in value and two derivatives on `[r₁, r₂]`, equal to `χ ℓ` near the band
  `[r₃, r₂]`, and equal to `χ a` near all of `[r₁, r₂]` when `ℓ = a`. It applies
  `ContDiffOn.exists_contDiff_abs_iteratedDeriv_sub_lt` to the slice of the open set at `ℓ`.

Together they give the chain itself:

* `SymplecticGeometry.exists_monotone_shapeChain`: for a family `χ` of `i`-convex shapes on
  `[a, b] × [r₁, r₂]`, smooth with `∂χ/∂ℓ > 0` near the band `[a, b] × [r₃, r₂]`, a family `C`
  smooth on `ℝ²`, of `i`-convex shapes and weakly increasing in `ℓ` there, constant in `ℓ` near
  `a` and `b` with `C a` equal to `χ a` near `[r₁, r₂]`, with `C b` at most `ε` above the members
  of `χ`, and within `τ` of `χ` in value and two `r`-derivatives on the band. It is the
  `shapeChain` of the stand-ins of `χ (a + i h)` on a mesh of size `h = (b - a) / N` with width
  `δ = c h`: first the margin of stability of the shapes (step 1 of the design,
  `SymplecticGeometry.exists_forall_isConvexShapeAt_of_abs_sub_lt`) fixes the lowering `η` and
  the error of the stand-ins, then `c` is taken below the rate of increase of `χ` on the band
  (`IsCompact.exists_pos_mul_sub_le_sub_of_deriv_pos`), and last `h` small by uniform continuity
  in `ℓ` (`IsCompact.exists_pos_abs_sub_lt_of_continuousOn`) and against the Lipschitz constant
  of `∂χ/∂r` in `ℓ` (`IsCompact.exists_abs_deriv_sub_le_mul`), which makes the curvature term
  of `SymplecticGeometry.abs_iteratedDeriv_shapeChain_sub_le` of order `h / c`.

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

/-! ### The path between consecutive smoothed maxima -/

/-- The **path between consecutive smoothed maxima**: for `σ` from `0` to `1`, the shape
`r ↦ smoothedMax δ (M r) (A r - (1 - ρ σ) η)`, where `ρ = collaredSmoothTransition`. It runs
from the smoothed maximum of `M` and `A - η` to that of `M` and `A`, and is constant in `σ` near
both ends. -/
def smoothedMaxPath (δ η : ℝ) (M A : ℝ → ℝ) (σ r : ℝ) : ℝ :=
  smoothedMax δ (M r) (A r - (1 - collaredSmoothTransition σ) * η)

theorem smoothedMaxPath_def (δ η : ℝ) (M A : ℝ → ℝ) (σ r : ℝ) :
    smoothedMaxPath δ η M A σ r =
      smoothedMax δ (M r) (A r - (1 - collaredSmoothTransition σ) * η) :=
  (rfl)

variable {δ η σ r : ℝ} {M A : ℝ → ℝ}

/-- The path between smoothed maxima of `Cⁿ` functions is `Cⁿ` in `(σ, r)`. -/
theorem contDiff_smoothedMaxPath {n : ℕ∞} (hM : ContDiff ℝ n M) (hA : ContDiff ℝ n A) :
    ContDiff ℝ n (Function.uncurry (smoothedMaxPath δ η M A)) := by
  have hρ : ContDiff ℝ n collaredSmoothTransition :=
    contDiff_collaredSmoothTransition (WithTop.coe_le_coe.2 le_top)
  have h : ContDiff ℝ n fun x : ℝ × ℝ ↦
      smoothedMax δ (M x.2) (A x.2 - (1 - collaredSmoothTransition x.1) * η) :=
    (contDiff_smoothedMax δ).comp ((hM.comp contDiff_snd).prodMk ((hA.comp contDiff_snd).sub
      ((contDiff_const.sub (hρ.comp contDiff_fst)).mul contDiff_const)))
  convert h using 1
  funext ⟨σ, r⟩
  rw [Function.uncurry_apply_pair, smoothedMaxPath_def]

/-- Up to `σ = 1 / 4`, the path is the smoothed maximum of `M` and `A - η`. -/
theorem smoothedMaxPath_of_le (hσ : σ ≤ 1 / 4) :
    smoothedMaxPath δ η M A σ = fun r ↦ smoothedMax δ (M r) (A r - η) := by
  funext r
  rw [smoothedMaxPath_def, collaredSmoothTransition_eq_zero_of_le hσ, sub_zero, one_mul]

/-- From `σ = 3 / 4` on, the path is the smoothed maximum of `M` and `A`. -/
theorem smoothedMaxPath_of_ge (hσ : 3 / 4 ≤ σ) :
    smoothedMaxPath δ η M A σ = fun r ↦ smoothedMax δ (M r) (A r) := by
  funext r
  rw [smoothedMaxPath_def, collaredSmoothTransition_eq_one_of_ge hσ, sub_self, zero_mul,
    sub_zero]

/-- From `σ = 3 / 4` on, the path from the `i`-th member of the chain of smoothed maxima towards
`A (i + 1)` is the `(i + 1)`-st member. -/
theorem smoothedMaxPath_smoothedMaxChain_of_ge {A : ℕ → ℝ → ℝ} {i : ℕ} (hσ : 3 / 4 ≤ σ) :
    smoothedMaxPath δ η (smoothedMaxChain δ A i) (A (i + 1)) σ = smoothedMaxChain δ A (i + 1) := by
  rw [smoothedMaxPath_of_ge hσ, smoothedMaxChain_succ]

/-- Up to `σ = 1 / 4`, the path is `M` wherever `A - η` lies at least `δ` below `M`. -/
theorem smoothedMaxPath_eq_left (hδ : 0 < δ) (hσ : σ ≤ 1 / 4) (h : A r - η + δ ≤ M r) :
    smoothedMaxPath δ η M A σ r = M r := by
  rw [smoothedMaxPath_of_le hσ]
  exact smoothedMax_eq_left hδ h

/-- For `η ≥ 0`, the path is monotone in `σ` at each `r`. -/
theorem monotone_smoothedMaxPath (hη : 0 ≤ η) (r : ℝ) :
    Monotone fun σ ↦ smoothedMaxPath δ η M A σ r := fun σ σ' hσ ↦ by
  simp only [smoothedMaxPath_def]
  refine monotone_smoothedMax_right δ (M r) ?_
  have := monotone_collaredSmoothTransition hσ
  nlinarith

/-- For `η ≥ 0`, the shape of the path at `σ` is the smoothed maximum of `M` and `A - c` for some
`c ∈ [0, η]`, namely `c = (1 - collaredSmoothTransition σ) * η`. -/
theorem exists_mem_Icc_smoothedMaxPath_eq (hη : 0 ≤ η) (σ : ℝ) :
    ∃ c ∈ Icc 0 η, smoothedMaxPath δ η M A σ = fun r ↦ smoothedMax δ (M r) (A r - c) :=
  ⟨_, one_sub_collaredSmoothTransition_mul_mem_Icc hη σ,
    funext fun r ↦ smoothedMaxPath_def δ η M A σ r⟩

/-- For `η ≥ 0`, the path consists of `i`-convex shapes at `r` if `M` and `A` are `C²`, `M` and
`A - η` are `i`-convex shapes at `r`, and `δ (M' r + A' r) ≤ 2 r`. -/
theorem isConvexShapeAt_smoothedMaxPath (hδ : 0 < δ) (hη : 0 ≤ η) (hM : ContDiff ℝ 2 M)
    (hA : ContDiff ℝ 2 A) (hcM : IsConvexShapeAt M r)
    (hcA : IsConvexShapeAt (fun r ↦ A r - η) r)
    (hδr : δ * (deriv M r + deriv A r) ≤ 2 * r) (σ : ℝ) :
    IsConvexShapeAt (smoothedMaxPath δ η M A σ) r := by
  obtain ⟨c, hc, he⟩ := exists_mem_Icc_smoothedMaxPath_eq (δ := δ) (M := M) (A := A) hη σ
  rw [he]
  have hAc : IsConvexShapeAt (fun r ↦ A r - c) r := by
    convert hcA.add_const (c := η - c) (by linarith [hc.2]) using 2
    ring
  exact isConvexShapeAt_smoothedMax hM (hA.sub contDiff_const) hδ hcM hAc
    (by rwa [deriv_sub_const])

/-- **The path keeps the smaller margin in (4.3).** For `δ > 0`, `0 ≤ η < A r`, `M r > 0` and
`M`, `A` differentiable at `r`, the margin `χ' / r - 1 / χ` of each shape `χ` of the path at `r`
is at least the smaller of those of `M` and of `A - η`. The latter is that of `A` less
`η / (A r (A r - η))` (`deriv_sub_const_div_sub_one_div_sub_const`). -/
theorem min_le_deriv_smoothedMaxPath_div_sub_one_div (hδ : 0 < δ) (hη : 0 ≤ η)
    (hηA : η < A r) (hM₀ : 0 < M r) (hMd : DifferentiableAt ℝ M r)
    (hAd : DifferentiableAt ℝ A r) (σ : ℝ) :
    min (deriv M r / r - 1 / M r) (deriv A r / r - 1 / (A r - η)) ≤
      deriv (smoothedMaxPath δ η M A σ) r / r - 1 / smoothedMaxPath δ η M A σ r := by
  obtain ⟨c, ⟨-, hcη⟩, he⟩ := exists_mem_Icc_smoothedMaxPath_eq (δ := δ) (M := M) (A := A) hη σ
  have hAc : 0 < A r - c := by linarith
  have h := min_le_deriv_smoothedMax_div_sub_one_div hMd (hAd.sub_const c) hδ hM₀ hAc
  rw [deriv_sub_const] at h
  have hb : 1 / (A r - c) ≤ 1 / (A r - η) := one_div_le_one_div_of_le (by linarith) (by linarith)
  rw [he]
  exact (min_le_min_left _ (by linarith)).trans h

/-- **The path keeps the smaller margin in the case `σ = r` of (4.4).** For `δ > 0`, `r > 0`,
`0 ≤ η < A r`, `M r > 0`, `M` and `A` of class `C²` with `M' r, A' r ≥ 0` and
`δ (M' r + A' r) ≤ 2 r`, the margin `χ'' + χ'³ / r - 1 / χ` of each shape `χ` of the path at
`r` is at least the smaller of those of `M` and of `A - η`. The latter is that of `A` less
`η / (A r (A r - η))` (`iteratedDeriv_two_sub_const_add_pow_three_div_sub_one_div_sub_const`). -/
theorem min_le_iteratedDeriv_two_smoothedMaxPath_add_pow_three_div_sub_one_div (hδ : 0 < δ)
    (hr : 0 < r) (hη : 0 ≤ η) (hηA : η < A r) (hM₀ : 0 < M r) (hM : ContDiff ℝ 2 M)
    (hA : ContDiff ℝ 2 A) (hMd : 0 ≤ deriv M r) (hAd : 0 ≤ deriv A r)
    (hδr : δ * (deriv M r + deriv A r) ≤ 2 * r) (σ : ℝ) :
    min (iteratedDeriv 2 M r + deriv M r ^ 3 / r - 1 / M r)
        (iteratedDeriv 2 A r + deriv A r ^ 3 / r - 1 / (A r - η)) ≤
      iteratedDeriv 2 (smoothedMaxPath δ η M A σ) r +
        deriv (smoothedMaxPath δ η M A σ) r ^ 3 / r - 1 / smoothedMaxPath δ η M A σ r := by
  obtain ⟨c, ⟨-, hcη⟩, he⟩ := exists_mem_Icc_smoothedMaxPath_eq (δ := δ) (M := M) (A := A) hη σ
  have hAc : 0 < A r - c := by linarith
  have h := min_le_iteratedDeriv_two_smoothedMax_add_pow_three_div_sub_one_div hM
    (hA.sub contDiff_const) hδ hr hM₀ hAc hMd (by rwa [deriv_sub_const]) (by rwa [deriv_sub_const])
  rw [deriv_sub_const, iteratedDeriv_sub_const two_pos] at h
  have hb : 1 / (A r - c) ≤ 1 / (A r - η) := one_div_le_one_div_of_le (by linarith) (by linarith)
  rw [he]
  exact (min_le_min_left _ (by linarith)).trans h

/-! ### A chain of paths between smoothed maxima -/

/-- A point `ℓ` of `[a, a + N h]`, for `h > 0` and `N > 0`, lies in one of the intervals
`[a + j h, a + (j + 1) h]` of the mesh with `j < N`. -/
theorem exists_lt_mem_Icc_add_mul {a h ℓ : ℝ} {N : ℕ} (hh : 0 < h) (hN : 0 < N)
    (hℓ : ℓ ∈ Icc a (a + N * h)) : ∃ j < N, ℓ ∈ Icc (a + j * h) (a + (j + 1) * h) := by
  rcases hℓ.2.lt_or_eq with hlt | heq
  · have hx : 0 ≤ (ℓ - a) / h := div_nonneg (by linarith [hℓ.1]) hh.le
    refine ⟨⌊(ℓ - a) / h⌋₊, (Nat.floor_lt hx).2 ((div_lt_iff₀ hh).2 (by linarith)), ?_, ?_⟩
    · linarith [(le_div_iff₀ hh).1 (Nat.floor_le hx)]
    · linarith [(div_lt_iff₀ hh).1 (Nat.lt_floor_add_one ((ℓ - a) / h))]
  · refine ⟨N - 1, Nat.sub_lt hN one_pos, ?_⟩
    rw [Nat.cast_pred hN, heq]
    exact ⟨by nlinarith, le_of_eq (by ring)⟩

section shapeChain

variable {a h ℓ ℓ' : ℝ} {A : ℕ → ℝ → ℝ} {N : ℕ}

/-- The **chain of paths between smoothed maxima** on the mesh `a + i h`, `i ≤ N`: the family
`(ℓ, r) ↦ shapeChain δ η a h A N ℓ r`, starting from `smoothedMaxChain δ A 0 = A 0`, that adds for
each `i < N` the increment of the path `smoothedMaxPath δ η (M i) (A (i + 1))` at the parameter
`(ℓ - a - i h) / h` over its value at the start, where `M = smoothedMaxChain δ A`. For `h > 0`,
each increment vanishes up to `ℓ = a + (i + 1 / 4) h` and is constant in `ℓ` from
`ℓ = a + (i + 3 / 4) h` on, and where the joints match the family runs along the path from `M j`
to `M (j + 1)` while `ℓ` runs from `a + j h` to `a + (j + 1) h`
(`shapeChain_eq_smoothedMaxPath`). -/
def shapeChain (δ η a h : ℝ) (A : ℕ → ℝ → ℝ) (N : ℕ) (ℓ r : ℝ) : ℝ :=
  smoothedMaxChain δ A 0 r + ∑ i ∈ Finset.range N,
    (smoothedMaxPath δ η (smoothedMaxChain δ A i) (A (i + 1)) ((ℓ - a - i * h) / h) r -
      smoothedMax δ (smoothedMaxChain δ A i r) (A (i + 1) r - η))

theorem shapeChain_def (δ η a h : ℝ) (A : ℕ → ℝ → ℝ) (N : ℕ) (ℓ r : ℝ) :
    shapeChain δ η a h A N ℓ r = smoothedMaxChain δ A 0 r + ∑ i ∈ Finset.range N,
      (smoothedMaxPath δ η (smoothedMaxChain δ A i) (A (i + 1)) ((ℓ - a - i * h) / h) r -
        smoothedMax δ (smoothedMaxChain δ A i r) (A (i + 1) r - η)) :=
  (rfl)

/-- The chain of paths between smoothed maxima of `Cⁿ` functions is `Cⁿ` in `(ℓ, r)`. -/
theorem contDiff_shapeChain {n : ℕ∞} (hA : ∀ i ≤ N, ContDiff ℝ n (A i)) :
    ContDiff ℝ n (Function.uncurry (shapeChain δ η a h A N)) := by
  have hM {i : ℕ} (hi : i ≤ N) : ContDiff ℝ n (smoothedMaxChain δ A i) :=
    contDiff_smoothedMaxChain δ fun j hj ↦ hA j (hj.trans hi)
  have hσ (i : ℕ) : ContDiff ℝ n fun x : ℝ × ℝ ↦ ((x.1 - a - i * h) / h, x.2) :=
    (((contDiff_fst.sub contDiff_const).sub contDiff_const).div_const h).prodMk contDiff_snd
  have key : ContDiff ℝ n fun x : ℝ × ℝ ↦ smoothedMaxChain δ A 0 x.2 + ∑ i ∈ Finset.range N,
      (Function.uncurry (smoothedMaxPath δ η (smoothedMaxChain δ A i) (A (i + 1)))
          ((x.1 - a - i * h) / h, x.2) -
        smoothedMax δ (smoothedMaxChain δ A i x.2) (A (i + 1) x.2 - η)) :=
    ((hM (Nat.zero_le N)).comp contDiff_snd).add (ContDiff.sum fun i hi ↦ by
      have hi : i < N := Finset.mem_range.1 hi
      exact ((contDiff_smoothedMaxPath (hM hi.le) (hA (i + 1) hi)).comp (hσ i)).sub
        ((contDiff_smoothedMax δ).comp (((hM hi.le).comp contDiff_snd).prodMk
          (((hA (i + 1) hi).comp contDiff_snd).sub contDiff_const))))
  convert key using 1
  funext ⟨ℓ, r⟩
  simp only [Function.uncurry_apply_pair, shapeChain_def]

/-- For `h > 0` and `η ≥ 0`, the chain of paths between smoothed maxima is monotone in `ℓ` at each
`r`; so its `ℓ`-derivative is nonnegative (`Monotone.deriv_nonneg`). -/
theorem monotone_shapeChain (hh : 0 < h) (hη : 0 ≤ η) (r : ℝ) :
    Monotone fun ℓ ↦ shapeChain δ η a h A N ℓ r := fun ℓ ℓ' hℓ ↦ by
  simp only [shapeChain_def]
  gcongr with i
  exact monotone_smoothedMaxPath hη r (div_le_div_of_nonneg_right
    (sub_le_sub_right (sub_le_sub_right hℓ a) _) hh.le)

/-- For `h > 0`, the chain of paths between smoothed maxima is `A 0` up to `ℓ = a + h / 4`. -/
theorem shapeChain_of_le (hh : 0 < h) (hℓ : ℓ ≤ a + h / 4) :
    shapeChain δ η a h A N ℓ = A 0 := by
  funext r
  rw [shapeChain_def, smoothedMaxChain_zero, add_eq_left]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  have hi := mul_nonneg i.cast_nonneg hh.le
  rw [smoothedMaxPath_of_le ((div_le_iff₀ hh).2 (by linarith)), sub_self]

/-- For `h > 0`, the chain of paths between smoothed maxima does not depend on `ℓ` from
`ℓ = a + (N - 1 / 4) h` on. -/
theorem shapeChain_eq_of_ge (hh : 0 < h) (hℓ : a + (N - 1 / 4) * h ≤ ℓ)
    (hℓ' : a + (N - 1 / 4) * h ≤ ℓ') :
    shapeChain δ η a h A N ℓ = shapeChain δ η a h A N ℓ' := by
  funext r
  simp only [shapeChain_def]
  congr 1
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hiN : (i : ℝ) + 1 ≤ N := by exact_mod_cast Finset.mem_range.1 hi
  have hle : a + (i + 3 / 4) * h ≤ a + (N - 1 / 4) * h := by nlinarith
  rw [smoothedMaxPath_smoothedMaxChain_of_ge ((le_div_iff₀ hh).2 (by linarith)),
    smoothedMaxPath_smoothedMaxChain_of_ge ((le_div_iff₀ hh).2 (by linarith))]

/-- **The local form of the chain of paths.** For `δ > 0` and `h > 0`, at an `r` where the joints
match, `A (i + 1) r - η + δ ≤ M i r` for `i < N` with `M = smoothedMaxChain δ A`, the chain of
paths between smoothed maxima is, for `ℓ ∈ [a + j h, a + (j + 1) h]` and `j < N`, the path from
`M j` to `M (j + 1)` at the parameter `(ℓ - a - j h) / h`. -/
theorem shapeChain_eq_smoothedMaxPath (hδ : 0 < δ) (hh : 0 < h)
    (hJ : ∀ i < N, A (i + 1) r - η + δ ≤ smoothedMaxChain δ A i r) {j : ℕ} (hj : j < N)
    (hℓ : ℓ ∈ Icc (a + j * h) (a + (j + 1) * h)) :
    shapeChain δ η a h A N ℓ r =
      smoothedMaxPath δ η (smoothedMaxChain δ A j) (A (j + 1)) ((ℓ - a - j * h) / h) r := by
  rw [shapeChain_def, Finset.add_sum_range_eq_of_lt (v := fun i ↦ smoothedMaxChain δ A i r) hj
    (fun i hij ↦ ?_) (fun i hij hiN ↦ ?_), smoothedMax_eq_left hδ (hJ j hj), add_sub_cancel]
  · have hij' : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij
    rw [smoothedMax_eq_left hδ (hJ i (hij.trans hj)),
      smoothedMaxPath_smoothedMaxChain_of_ge ((le_div_iff₀ hh).2 (by nlinarith [hℓ.1]))]
  · have hij' : (j : ℝ) + 1 ≤ i := by exact_mod_cast hij
    have hσ : (ℓ - a - i * h) / h ≤ 1 / 4 := (div_le_iff₀ hh).2 (by nlinarith [hℓ.2])
    rw [smoothedMaxPath_eq_left hδ hσ (hJ i hiN), smoothedMax_eq_left hδ (hJ i hiN), sub_self]

/-- For `δ > 0` and `h > 0`, at an `r` where the joints match, `A (i + 1) r - η + δ ≤ M i r` for
`i < N` with `M = smoothedMaxChain δ A`, the chain of paths between smoothed maxima is `M N` from
`ℓ = a + N h` on. -/
theorem shapeChain_eq_smoothedMaxChain (hδ : 0 < δ) (hh : 0 < h)
    (hJ : ∀ i < N, A (i + 1) r - η + δ ≤ smoothedMaxChain δ A i r) (hℓ : a + N * h ≤ ℓ) :
    shapeChain δ η a h A N ℓ r = smoothedMaxChain δ A N r := by
  have key : ∀ i ∈ Finset.range N,
      smoothedMaxPath δ η (smoothedMaxChain δ A i) (A (i + 1)) ((ℓ - a - i * h) / h) r -
        smoothedMax δ (smoothedMaxChain δ A i r) (A (i + 1) r - η) =
          smoothedMaxChain δ A (i + 1) r - smoothedMaxChain δ A i r := by
    intro i hi
    have hiN : (i : ℝ) + 1 ≤ N := by exact_mod_cast Finset.mem_range.1 hi
    rw [smoothedMax_eq_left hδ (hJ i (Finset.mem_range.1 hi)),
      smoothedMaxPath_smoothedMaxChain_of_ge ((le_div_iff₀ hh).2 (by nlinarith))]
  rw [shapeChain_def, Finset.sum_congr rfl key,
    Finset.sum_range_sub fun i ↦ smoothedMaxChain δ A i r]
  ring

/-- For `δ > 0` and `h > 0`, along a filter on which the joints eventually match,
`A (i + 1) - η + δ ≤ M i` for `i < N` with `M = smoothedMaxChain δ A`, the shape of the chain of
paths between smoothed maxima at `ℓ ∈ [a + j h, a + (j + 1) h]`, `j < N`, is eventually that of
the path from `M j` to `M (j + 1)` at the parameter `(ℓ - a - j h) / h`. -/
theorem shapeChain_eventuallyEq_smoothedMaxPath {l : Filter ℝ} (hδ : 0 < δ) (hh : 0 < h)
    (hJ : ∀ᶠ r in l, ∀ i < N, A (i + 1) r - η + δ ≤ smoothedMaxChain δ A i r) {j : ℕ}
    (hj : j < N) (hℓ : ℓ ∈ Icc (a + j * h) (a + (j + 1) * h)) :
    shapeChain δ η a h A N ℓ =ᶠ[l]
      smoothedMaxPath δ η (smoothedMaxChain δ A j) (A (j + 1)) ((ℓ - a - j * h) / h) :=
  hJ.mono fun _ hr ↦ shapeChain_eq_smoothedMaxPath hδ hh hr hj hℓ

/-- For `δ > 0` and `h > 0`, along a filter on which the joints eventually match,
`A (i + 1) - η + δ ≤ M i` for `i < N` with `M = smoothedMaxChain δ A`, the shape of the chain of
paths between smoothed maxima at `ℓ ≥ a + N h` is eventually `M N`. -/
theorem shapeChain_eventuallyEq_smoothedMaxChain {l : Filter ℝ} (hδ : 0 < δ) (hh : 0 < h)
    (hJ : ∀ᶠ r in l, ∀ i < N, A (i + 1) r - η + δ ≤ smoothedMaxChain δ A i r)
    (hℓ : a + N * h ≤ ℓ) :
    shapeChain δ η a h A N ℓ =ᶠ[l] smoothedMaxChain δ A N :=
  hJ.mono fun _ hr ↦ shapeChain_eq_smoothedMaxChain hδ hh hr hℓ

/-- **The chain of paths consists of `i`-convex shapes.** For `δ, h > 0` and `η ≥ 0`, let the
`A i`, `i ≤ N`, be `C²` and `i`-convex shapes at `r` with `deriv (A i) r ≤ G` and `δ G ≤ r`, let
the `A (i + 1) - η`, `i < N`, be `i`-convex shapes at `r`, and let the joints match near `r`:
`A (i + 1) - η + δ ≤ M i` for `i < N`, with `M = smoothedMaxChain δ A`. Then every member of the
chain of paths between smoothed maxima is an `i`-convex shape at `r`. -/
theorem isConvexShapeAt_shapeChain {G : ℝ} (hδ : 0 < δ) (hh : 0 < h) (hη : 0 ≤ η)
    (hA : ∀ i ≤ N, ContDiff ℝ 2 (A i))
    (hJ : ∀ᶠ r' in 𝓝 r, ∀ i < N, A (i + 1) r' - η + δ ≤ smoothedMaxChain δ A i r')
    (hc : ∀ i ≤ N, IsConvexShapeAt (A i) r)
    (hcη : ∀ i < N, IsConvexShapeAt (fun r ↦ A (i + 1) r - η) r)
    (hG : ∀ i ≤ N, deriv (A i) r ≤ G) (hδG : δ * G ≤ r) (ℓ : ℝ) :
    IsConvexShapeAt (shapeChain δ η a h A N ℓ) r := by
  have hM {j : ℕ} (hj : j ≤ N) : IsConvexShapeAt (smoothedMaxChain δ A j) r :=
    isConvexShapeAt_smoothedMaxChain hδ (fun i hi ↦ hA i (hi.trans hj))
      (fun i hi ↦ hc i (hi.trans hj)) (fun i hi ↦ hG i (hi.trans hj)) hδG
  rcases le_or_gt ℓ a with hℓa | hℓa
  · rw [shapeChain_of_le hh (by linarith)]
    exact hc 0 (Nat.zero_le N)
  rcases le_or_gt (a + N * h) ℓ with hℓN | hℓN
  · exact (hM le_rfl).congr_of_eventuallyEq
      (shapeChain_eventuallyEq_smoothedMaxChain hδ hh hJ hℓN)
  -- `ℓ` lies in the `j`-th interval of the mesh for some `j < N`.
  have hN : 0 < N := Nat.pos_of_ne_zero fun h0 ↦ by simp [h0] at hℓN; linarith
  obtain ⟨j, hj, hℓj⟩ := exists_lt_mem_Icc_add_mul hh hN ⟨hℓa.le, hℓN.le⟩
  refine IsConvexShapeAt.congr_of_eventuallyEq ?_
    (shapeChain_eventuallyEq_smoothedMaxPath hδ hh hJ hj hℓj)
  have hd : ∀ i ≤ j, DifferentiableAt ℝ (A i) r := fun i hi ↦
    ((hA i (hi.trans hj.le)).differentiable two_ne_zero).differentiableAt
  have hdM := deriv_smoothedMaxChain_le δ hd fun i hi ↦ hG i (hi.trans hj.le)
  have hdA := hG (j + 1) hj
  refine isConvexShapeAt_smoothedMaxPath hδ hη
    (contDiff_smoothedMaxChain δ fun i hi ↦ hA i (hi.trans hj.le)) (hA (j + 1) hj) (hM hj.le)
    (hcη j hj) ?_ _
  nlinarith

/-- **The chain of paths stays `C²`-close to what its ends are close to.** For `δ, h > 0` and
`η ≥ 0`, let `A j` and `A (j + 1)` be `C²`, let the joints match near `r`,
`A (i + 1) - η + δ ≤ M i` for `i < N` with `M = smoothedMaxChain δ A`, and let `A 0, …, A j` each
lie at least `δ` below the next near `r`, so that `M j = A j` near `r`. If `C / δ` bounds the
curvature of `smoothedAbs δ`, then for `ℓ ∈ [a + j h, a + (j + 1) h]` and any values `φ 0`,
`φ 1`, `φ 2`, the value and the first two derivatives at `r` of the member of the chain at `ℓ`
are as close to `φ 0`, `φ 1`, `φ 2` as the farther of those of `A j` and `A (j + 1)`, up to
`η + δ / 2` for the value and `C (A j' r - A (j + 1)' r)² / (2 δ)` for the second derivative. -/
theorem abs_iteratedDeriv_shapeChain_sub_le {C : ℝ} {j : ℕ} (hδ : 0 < δ) (hh : 0 < h)
    (hη : 0 ≤ η) (hAj : ContDiff ℝ 2 (A j)) (hAj₁ : ContDiff ℝ 2 (A (j + 1)))
    (hJ : ∀ᶠ r' in 𝓝 r, ∀ i < N, A (i + 1) r' - η + δ ≤ smoothedMaxChain δ A i r')
    (hup : ∀ᶠ r' in 𝓝 r, ∀ i < j, A i r' + δ ≤ A (i + 1) r')
    (hC : ∀ t, iteratedDeriv 2 (smoothedAbs δ) t ≤ C / δ) (hj : j < N)
    (hℓ : ℓ ∈ Icc (a + j * h) (a + (j + 1) * h)) (φ : ℕ → ℝ) :
    |shapeChain δ η a h A N ℓ r - φ 0| ≤
        max |A j r - φ 0| |A (j + 1) r - φ 0| + η + δ / 2 ∧
      |deriv (shapeChain δ η a h A N ℓ) r - φ 1| ≤
        max |deriv (A j) r - φ 1| |deriv (A (j + 1)) r - φ 1| ∧
      |iteratedDeriv 2 (shapeChain δ η a h A N ℓ) r - φ 2| ≤
        max |iteratedDeriv 2 (A j) r - φ 2| |iteratedDeriv 2 (A (j + 1)) r - φ 2| +
          C * (deriv (A j) r - deriv (A (j + 1)) r) ^ 2 / (2 * δ) := by
  obtain ⟨c, ⟨hc₀, hcη⟩, he⟩ := exists_mem_Icc_smoothedMaxPath_eq
    (δ := δ) (M := smoothedMaxChain δ A j) (A := A (j + 1)) hη ((ℓ - a - j * h) / h)
  -- Near `r`, the member of the chain at `ℓ` is the smoothed maximum of `A j` and `A (j + 1) - c`.
  have hloc : shapeChain δ η a h A N ℓ =ᶠ[𝓝 r]
      fun r' ↦ smoothedMax δ (A j r') (A (j + 1) r' - c) := by
    filter_upwards [shapeChain_eventuallyEq_smoothedMaxPath hδ hh hJ hj hℓ,
      smoothedMaxChain_eventuallyEq hδ hup] with r' h₁ h₂
    rw [h₁, he]
    exact congrArg (smoothedMax δ · (A (j + 1) r' - c)) h₂
  have hd : DifferentiableAt ℝ (A j) r := (hAj.differentiable two_ne_zero).differentiableAt
  have hd₁ : DifferentiableAt ℝ (A (j + 1)) r :=
    (hAj₁.differentiable two_ne_zero).differentiableAt
  refine ⟨?_, ?_, ?_⟩
  · rw [hloc.eq_of_nhds]
    have hc : |A (j + 1) r - c - φ 0| ≤ |A (j + 1) r - φ 0| + η := by
      rw [sub_right_comm]
      exact (abs_sub _ _).trans (by rw [abs_of_nonneg hc₀]; linarith)
    have hm : max |A j r - φ 0| |A (j + 1) r - c - φ 0| ≤
        max |A j r - φ 0| |A (j + 1) r - φ 0| + η :=
      max_le (by linarith [le_max_left |A j r - φ 0| |A (j + 1) r - φ 0|])
        (hc.trans (by linarith [le_max_right |A j r - φ 0| |A (j + 1) r - φ 0|]))
    linarith [abs_smoothedMax_sub_le hδ (A j r) (A (j + 1) r - c) (φ 0)]
  · rw [hloc.deriv_eq]
    simpa only [deriv_sub_const] using abs_deriv_smoothedMax_sub_le hd (hd₁.sub_const c) (φ 1)
  · rw [hloc.iteratedDeriv_eq 2]
    simpa only [deriv_sub_const, iteratedDeriv_sub_const two_pos] using
      abs_iteratedDeriv_two_smoothedMax_sub_le hAj (hAj₁.sub contDiff_const) hδ.le (hC _) (φ 2)

end shapeChain

/-- A member `χ ℓ` of a family that is `C²` in `r` over `[a, b] × [r₁, r₂]` and smooth on an open
set `U` containing `[a, b] × [r₃, r₂]` and `{a} × [r₁, r₂]` has, for every `θ > 0`, a smooth
replacement `g` whose value and first two derivatives are within `θ` of those of `χ ℓ` on
`[r₁, r₂]`, which agrees with `χ ℓ` near `[r₃, r₂]`, and which for `ℓ = a` agrees with `χ a`
near `[r₁, r₂]`. -/
theorem exists_contDiff_abs_iteratedDeriv_sub_lt_of_mem_Icc {a b r₃ ℓ θ : ℝ} {U : Set (ℝ × ℝ)}
    (hC2 : ∀ x ∈ Icc a b ×ˢ Icc r₁ r₂, ContDiffAt ℝ 2 (χ x.1) x.2) (hU : IsOpen U)
    (hEU : {a} ×ˢ Icc r₁ r₂ ∪ Icc a b ×ˢ Icc r₃ r₂ ⊆ U)
    (hsmooth : ContDiffOn ℝ ∞ (Function.uncurry χ) U) (hℓ : ℓ ∈ Icc a b) (hθ : 0 < θ) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧
      (∀ k ≤ 2, ∀ r ∈ Icc r₁ r₂, |iteratedDeriv k g r - iteratedDeriv k (χ ℓ) r| < θ) ∧
      g =ᶠ[𝓝ˢ (Icc r₃ r₂)] χ ℓ ∧ (ℓ = a → g =ᶠ[𝓝ˢ (Icc r₁ r₂)] χ a) := by
  -- The slice of `U` at `ℓ` is open, and `χ ℓ` is smooth on it.
  have hcont : Continuous fun r : ℝ ↦ (ℓ, r) := by fun_prop
  have hS : IsOpen {r | (ℓ, r) ∈ U} := hU.preimage hcont
  have hχS : ContDiffOn ℝ ∞ (χ ℓ) {r | (ℓ, r) ∈ U} :=
    hsmooth.comp (contDiffOn_const.prodMk contDiffOn_id) fun _ hr ↦ hr
  -- `χ ℓ` is `C²` on a neighbourhood of `[r₁, r₂]`.
  have hU₂ : {r | ContDiffAt ℝ 2 (χ ℓ) r} ∈ 𝓝ˢ (Icc r₁ r₂) :=
    mem_nhdsSet_iff_forall.2 fun r hr ↦
      (hC2 (ℓ, r) ⟨hℓ, hr⟩).eventually (by simp)
  have hχ₂ : ContDiffOn ℝ 2 (χ ℓ) {r | ContDiffAt ℝ 2 (χ ℓ) r} :=
    fun _ hr ↦ hr.contDiffWithinAt
  -- The approximation that agrees with `χ ℓ` near `[c, r₂]`, for `[c, r₂]` in the slice.
  have key : ∀ c, Icc c r₂ ⊆ {r | (ℓ, r) ∈ U} → ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧
      (∀ k ≤ 2, ∀ r ∈ Icc r₁ r₂, |iteratedDeriv k g r - iteratedDeriv k (χ ℓ) r| < θ) ∧
      g =ᶠ[𝓝ˢ (Icc c r₂)] χ ℓ := fun c hc ↦
    hχ₂.exists_contDiff_abs_iteratedDeriv_sub_lt hU₂ (hS.mem_nhdsSet.2 hc) hχS hθ
  by_cases ha : ℓ = a
  · subst ha
    obtain ⟨g, hg, hgθ, hgc⟩ := key (min r₁ r₃) fun r hr ↦ by
      rcases le_or_gt r₁ r with h | h
      · exact hEU (Or.inl ⟨rfl, h, hr.2⟩)
      · exact hEU (Or.inr ⟨⟨le_rfl, hℓ.2⟩, (min_le_iff.1 hr.1).resolve_left h.not_ge, hr.2⟩)
    exact ⟨g, hg, hgθ, hgc.filter_mono (nhdsSet_mono (Icc_subset_Icc_left (min_le_right _ _))),
      fun _ ↦ hgc.filter_mono (nhdsSet_mono (Icc_subset_Icc_left (min_le_left _ _)))⟩
  · obtain ⟨g, hg, hgθ, hgc⟩ := key r₃ fun r hr ↦ hEU (Or.inr ⟨hℓ, hr⟩)
    exact ⟨g, hg, hgθ, hgc, fun h ↦ absurd h ha⟩

/-- **A smooth weakly increasing chain of `i`-convex shapes.** Let `χ ℓ`, `ℓ ∈ [a, b]`, be
`i`-convex shapes on `[r₁, r₂]`, `r₁ > 0`, `C²` there with value and first two derivatives
continuous in `(ℓ, r)`, and let the family be smooth on an open set `U` that contains
`{a} × [r₁, r₂]` and the band `[a, b] × [r₃, r₂]`, `r₁ ≤ r₃`, with `∂χ/∂ℓ > 0` on the band.
Then for all `τ, ε > 0` there is a family `C`, smooth on all of `ℝ²`, such that on
`[a, b] × [r₁, r₂]` each `C ℓ` is an `i`-convex shape and `∂C/∂ℓ ≥ 0`; `C` is constant in `ℓ`
near `a` and near `b`, and `C a` equals `χ a` near `[r₁, r₂]`; at each `r ∈ [r₁, r₂]`, `C b r`
is at most `ε` above some `χ ℓ r`, `ℓ ∈ [a, b]`; and on the band, `C ℓ` is within `τ` of `χ ℓ`
in value and first two derivatives. -/
theorem exists_monotone_shapeChain {a b r₃ τ ε : ℝ} {U : Set (ℝ × ℝ)} (hr₁ : 0 < r₁)
    (hab : a < b) (hr₁₃ : r₁ ≤ r₃)
    (hC2 : ∀ x ∈ Icc a b ×ˢ Icc r₁ r₂, ContDiffAt ℝ 2 (χ x.1) x.2)
    (hc : ∀ x ∈ Icc a b ×ˢ Icc r₁ r₂, IsConvexShapeAt (χ x.1) x.2)
    (hcont : ∀ k ≤ 2, ContinuousOn (fun x : ℝ × ℝ ↦ iteratedDeriv k (χ x.1) x.2)
      (Icc a b ×ˢ Icc r₁ r₂))
    (hU : IsOpen U) (hEU : {a} ×ˢ Icc r₁ r₂ ∪ Icc a b ×ˢ Icc r₃ r₂ ⊆ U)
    (hsmooth : ContDiffOn ℝ ∞ (Function.uncurry χ) U)
    (hmono : ∀ x ∈ Icc a b ×ˢ Icc r₃ r₂, 0 < deriv (fun ℓ' ↦ χ ℓ' x.2) x.1)
    (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ C : ℝ → ℝ → ℝ, ContDiff ℝ ∞ (Function.uncurry C) ∧
      (∀ x ∈ Icc a b ×ˢ Icc r₁ r₂, IsConvexShapeAt (C x.1) x.2) ∧
      (∀ x ∈ Icc a b ×ˢ Icc r₁ r₂, 0 ≤ deriv (fun ℓ' ↦ C ℓ' x.2) x.1) ∧
      ((∀ᶠ ℓ in 𝓝 a, C ℓ = C a) ∧ C a =ᶠ[𝓝ˢ (Icc r₁ r₂)] χ a) ∧
      (∀ᶠ ℓ in 𝓝 b, C ℓ = C b) ∧
      (∀ r ∈ Icc r₁ r₂, ∃ ℓ ∈ Icc a b, C b r ≤ χ ℓ r + ε) ∧
      ∀ x ∈ Icc a b ×ˢ Icc r₃ r₂, ∀ k ≤ 2,
        |iteratedDeriv k (C x.1) x.2 - iteratedDeriv k (χ x.1) x.2| < τ := by
  have hK : IsCompact (Icc a b ×ˢ Icc r₁ r₂) := isCompact_Icc.prod isCompact_Icc
  have hband : Icc a b ×ˢ Icc r₃ r₂ ⊆ U := fun x hx ↦ hEU (Or.inr hx)
  have hba : 0 < b - a := sub_pos.2 hab
  -- The margin of stability of the convex shapes `χ ℓ` on the rectangle, a bound for their
  -- slopes there, and on the band a rate of increase in `ℓ` and a Lipschitz bound in `ℓ` for
  -- the slopes; last, a bound `C₀ / δ` for the curvature of `smoothedAbs δ`.
  obtain ⟨η₁, hη₁, hstab⟩ := exists_forall_isConvexShapeAt_of_abs_sub_lt hK hc hcont
  obtain ⟨G₀, hG₀⟩ := hK.exists_bound_of_continuousOn (hcont 1 (by norm_num))
  obtain ⟨m, hm, hrate⟩ := isCompact_Icc.exists_pos_mul_sub_le_sub_of_deriv_pos hU hband
    (hsmooth.of_le (by norm_cast)) hmono
  obtain ⟨L, hL⟩ := isCompact_Icc.exists_abs_deriv_sub_le_mul hU hband
    (hsmooth.of_le (by norm_cast))
  obtain ⟨C₀, hC₀⟩ := exists_forall_iteratedDeriv_two_smoothedAbs_le
  set G := |G₀| + 1
  have hG : 0 < G := by positivity
  set Q := max C₀ 0
  have hQ : 0 ≤ Q := le_max_right _ _
  -- The constants: the lowering `η`, the error `θ` of the smooth stand-ins, the ratio `c` of the
  -- width `δ = c h` to the mesh `h`, and the error `ε₀` of uniform continuity in `ℓ`.
  set η := min (η₁ / 2) (τ / 4)
  have hη : 0 < η := by positivity
  set θ := min (min (η₁ / 4) (ε / 2)) (min (η / 8) 1) with hθ_def
  have hθ : 0 < θ := by positivity
  set c := min (min (m / 2) (ε / (b - a))) (min (r₁ / G) (η / 4)) with hc_def
  have hc0 : 0 < c := by positivity
  set ε₀ := min (η / 2) (τ / 4)
  have hε₀ : 0 < ε₀ := by positivity
  have huc (k : ℕ) (hk : k ≤ 2) : ∃ h > 0, ∀ r ∈ Icc r₁ r₂, ∀ ℓ ∈ Icc a b, ∀ ℓ' ∈ Icc a b,
      |ℓ' - ℓ| ≤ h → |iteratedDeriv k (χ ℓ') r - iteratedDeriv k (χ ℓ) r| < ε₀ :=
    isCompact_Icc.exists_pos_abs_sub_lt_of_continuousOn (hcont k hk) hε₀
  obtain ⟨h₀', hh₀', hu₀⟩ := huc 0 (by norm_num)
  obtain ⟨h₁', hh₁', hu₁⟩ := huc 1 (by norm_num)
  obtain ⟨h₂', hh₂', hu₂⟩ := huc 2 le_rfl
  set h₀ := min (min h₀' h₁') (min h₂' (min 1 (τ * c / (Q * L ^ 2 + 1))))
  have hh₀ : 0 < h₀ := by positivity
  -- The mesh `t i = a + i h`, `i ≤ N`, of size `h = (b - a) / N < h₀`, and the width `δ = c h`.
  obtain ⟨N, hN⟩ := exists_nat_gt ((b - a) / h₀)
  have hN0 : 0 < N := by exact_mod_cast (div_pos hba hh₀).trans hN
  have hN0' : (0 : ℝ) < N := by exact_mod_cast hN0
  set h := (b - a) / N with hh_def
  have hh : 0 < h := div_pos hba hN0'
  have hNh : (N : ℝ) * h = b - a := by rw [hh_def]; field_simp
  have hhh₀ : h < h₀ := by
    rw [hh_def, div_lt_iff₀ hN0']
    rw [div_lt_iff₀ hh₀] at hN
    linarith
  have hh₀le : h₀ ≤ h₀' ∧ h₀ ≤ h₁' ∧ h₀ ≤ h₂' ∧ h₀ ≤ 1 ∧ h₀ ≤ τ * c / (Q * L ^ 2 + 1) := by
    exact ⟨(min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _),
      (min_le_right _ _).trans (min_le_left _ _),
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)),
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  set δ := c * h with hδ_def
  have hδ : 0 < δ := mul_pos hc0 hh
  have hcle : c ≤ m / 2 ∧ c ≤ ε / (b - a) ∧ c ≤ r₁ / G ∧ c ≤ η / 4 := by
    simp only [hc_def]
    exact ⟨(min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _),
      (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
  have hδc : δ ≤ c := by
    rw [hδ_def]
    exact mul_le_of_le_one_right hc0.le (hhh₀.le.trans hh₀le.2.2.2.1)
  set t : ℕ → ℝ := fun i ↦ a + (min i N : ℕ) * h with ht_def
  have ht (i : ℕ) (hi : i ≤ N) : t i = a + i * h := by simp [ht_def, hi]
  have htI (i : ℕ) : t i ∈ Icc a b := by
    have h₁ : ((min i N : ℕ) : ℝ) ≤ N := by exact_mod_cast min_le_right i N
    have h₂ : (0 : ℝ) ≤ (min i N : ℕ) := Nat.cast_nonneg _
    simp only [ht_def]
    exact ⟨le_add_of_nonneg_right (mul_nonneg h₂ hh.le),
      by linarith [mul_le_mul_of_nonneg_right h₁ hh.le]⟩
  have ht0 : t 0 = a := by simp [ht_def]
  have hstep (i : ℕ) (hi : i < N) : t (i + 1) - t i = h := by
    rw [ht _ hi, ht _ hi.le]
    push_cast
    ring
  -- The smooth stand-ins `A i` for the members `χ (t i)`.
  choose A hAs hAθ hAb hAa using fun i ↦
    exists_contDiff_abs_iteratedDeriv_sub_lt_of_mem_Icc hC2 hU hEU hsmooth (htI i) hθ
  have hA2 (i : ℕ) : ContDiff ℝ 2 (A i) := (hAs i).of_le (by norm_cast)
  have hAc (i : ℕ) : Continuous (A i) := (hAs i).continuous
  have hθle : θ ≤ η₁ / 4 ∧ θ ≤ ε / 2 ∧ θ ≤ η / 8 ∧ θ ≤ 1 := by
    simp only [hθ_def]
    exact ⟨(min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _),
      (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
  have hηle : η ≤ η₁ / 2 ∧ η ≤ τ / 4 := ⟨min_le_left _ _, min_le_right _ _⟩
  have hε₀le : ε₀ ≤ η / 2 ∧ ε₀ ≤ τ / 4 := ⟨min_le_left _ _, min_le_right _ _⟩
  -- The stand-ins and their lowerings by `η` are convex shapes, with slopes at most `G`.
  have hcA (i : ℕ) (r : ℝ) (hr : r ∈ Icc r₁ r₂) : IsConvexShapeAt (A i) r :=
    hstab (A i) (t i, r) ⟨htI i, hr⟩ fun k hk ↦ (hAθ i k hk r hr).trans (by linarith)
  have hcAη (i : ℕ) (r : ℝ) (hr : r ∈ Icc r₁ r₂) : IsConvexShapeAt (fun r ↦ A i r - η) r :=
    hstab _ (t i, r) ⟨htI i, hr⟩ fun k hk ↦ by
      have h := hAθ i k hk r hr
      interval_cases k
      · simp only [iteratedDeriv_zero] at h ⊢
        have h' : |A i r - η - χ (t i) r| ≤ |A i r - χ (t i) r| + η := by
          rw [sub_right_comm]
          exact (abs_sub _ _).trans (by rw [abs_of_pos hη])
        linarith
      · simp only [iteratedDeriv_one, deriv_sub_const] at h ⊢
        linarith
      · rw [iteratedDeriv_sub_const two_pos]
        linarith
  have hGA (i : ℕ) (r : ℝ) (hr : r ∈ Icc r₁ r₂) : deriv (A i) r ≤ G := by
    have h₁ := (abs_lt.1 (hAθ i 1 (by norm_num) r hr)).2
    have h₂ := hG₀ (t i, r) ⟨htI i, hr⟩
    simp only [iteratedDeriv_one, Real.norm_eq_abs] at h₁ h₂
    linarith [le_abs_self (deriv (χ (t i)) r), le_abs_self G₀]
  -- The joints match on `[r₁, r₂]`, with room to spare.
  have hJs (r : ℝ) (hr : r ∈ Icc r₁ r₂) (i : ℕ) (hi : i < N) :
      A (i + 1) r - η + δ < A i r := by
    have h₁ := (abs_lt.1 (hAθ (i + 1) 0 (by norm_num) r hr)).2
    have h₂ := (abs_lt.1 (hAθ i 0 (by norm_num) r hr)).1
    have h₃ := (abs_lt.1 (hu₀ r hr (t i) (htI i) (t (i + 1)) (htI _)
      (by rw [hstep i hi, abs_of_pos hh]; linarith [hh₀le.1]))).2
    simp only [iteratedDeriv_zero] at h₁ h₂ h₃
    linarith [hcle.2.2.2]
  have hJ (r : ℝ) (hr : r ∈ Icc r₁ r₂) :
      ∀ᶠ r' in 𝓝 r, ∀ i < N, A (i + 1) r' - η + δ ≤ smoothedMaxChain δ A i r' := by
    have h : ∀ᶠ r' in 𝓝 r, ∀ i ∈ Iio N, A (i + 1) r' - η + δ < A i r' :=
      (finite_Iio N).eventually_all.2 fun i hi ↦
        (((hAc (i + 1)).sub continuous_const).add continuous_const).continuousAt.eventually_lt
          (hAc i).continuousAt (hJs r hr i hi)
    filter_upwards [h] with r' hr' i hi
    exact (hr' i hi).le.trans (le_smoothedMaxChain hδ A i r')
  refine ⟨shapeChain δ η a h A N, contDiff_shapeChain fun i _ ↦ hAs i, fun x hx ↦ ?_,
    fun x _ ↦ (monotone_shapeChain hh hη.le x.2).deriv_nonneg, ⟨?_, ?_⟩, ?_, fun r hr ↦ ?_,
    ?_⟩
  · -- The members are convex shapes.
    have hδG : δ * G ≤ x.2 := by
      have := (le_div_iff₀ hG).1 hcle.2.2.1
      linarith [hx.2.1, mul_le_mul_of_nonneg_right hδc hG.le]
    exact isConvexShapeAt_shapeChain hδ hh hη.le (fun i _ ↦ hA2 i) (hJ x.2 hx.2)
      (fun i _ ↦ hcA i x.2 hx.2) (fun i _ ↦ hcAη (i + 1) x.2 hx.2) (fun i _ ↦ hGA i x.2 hx.2)
      hδG x.1
  · -- Flat near `a`.
    filter_upwards [Iio_mem_nhds (by linarith : a < a + h / 4)] with ℓ hℓ
    rw [shapeChain_of_le hh hℓ.le, shapeChain_of_le hh (by linarith)]
  · rw [shapeChain_of_le hh (by linarith)]
    exact hAa 0 ht0
  · -- Flat near `b`.
    have he : a + (N - 1 / 4) * h = b - h / 4 := by linear_combination hNh
    filter_upwards [Ioi_mem_nhds (by linarith : b - h / 4 < b)] with ℓ hℓ
    exact shapeChain_eq_of_ge hh (by rw [he]; exact hℓ.le) (by rw [he]; linarith)
  · -- The last member lies at most `ε` above some member of `χ`.
    obtain ⟨j, -, hj⟩ := exists_smoothedMaxChain_le_add hδ A N r
    refine ⟨t j, htI j, ?_⟩
    rw [shapeChain_eq_smoothedMaxChain hδ hh
      (fun i hi ↦ (hJs r hr i hi).le.trans (le_smoothedMaxChain hδ A i r)) (by linarith)]
    have h₁ := (abs_lt.1 (hAθ j 0 (by norm_num) r hr)).2
    simp only [iteratedDeriv_zero] at h₁
    have h₂ : N * δ ≤ ε := by
      have := (le_div_iff₀ hba).1 hcle.2.1
      rw [hδ_def, mul_left_comm, hNh]
      linarith
    linarith [hθle.2.1]
  · -- Near `r₂`, the chain follows `χ`.
    rintro ⟨ℓ, r⟩ ⟨hℓ, hr₃⟩ k hk
    have hr : r ∈ Icc r₁ r₂ := ⟨hr₁₃.trans hr₃.1, hr₃.2⟩
    obtain ⟨j, hj, hℓj⟩ := exists_lt_mem_Icc_add_mul hh hN0 ⟨hℓ.1, by linarith [hℓ.2]⟩
    have hAe (i : ℕ) : A i =ᶠ[𝓝 r] χ (t i) := (hAb i).filter_mono (nhds_le_nhdsSet hr₃)
    have hup : ∀ᶠ r' in 𝓝 r, ∀ i < j, A i r' + δ ≤ A (i + 1) r' := by
      have h : ∀ᶠ r' in 𝓝 r, ∀ i ∈ Iio j, A i r' + δ < A (i + 1) r' :=
        (finite_Iio j).eventually_all.2 fun i hi ↦
          ((hAc i).add continuous_const).continuousAt.eventually_lt (hAc (i + 1)).continuousAt
            (by
              have hiN : i < N := lt_trans hi hj
              simp only [Pi.add_apply]
              rw [(hAe i).eq_of_nhds, (hAe (i + 1)).eq_of_nhds]
              have h₁ := hrate r hr₃ (t i) (htI i) (t (i + 1)) (htI _)
                (by linarith [hstep i hiN])
              rw [hstep i hiN] at h₁
              linarith [mul_lt_mul_of_pos_right (hcle.1.trans_lt (half_lt_self hm)) hh])
      filter_upwards [h] with r' hr' i hi using (hr' i hi).le
    have hQδ (s : ℝ) : iteratedDeriv 2 (smoothedAbs δ) s ≤ Q / δ :=
      (hC₀ δ hδ s).trans (div_le_div_of_nonneg_right (le_max_left _ _) hδ.le)
    obtain ⟨e₀, e₁, e₂⟩ := abs_iteratedDeriv_shapeChain_sub_le hδ hh hη.le (hA2 j) (hA2 (j + 1))
      (hJ r hr) hup hQδ hj hℓj (fun k ↦ iteratedDeriv k (χ ℓ) r)
    rw [(hAe j).eq_of_nhds, (hAe (j + 1)).eq_of_nhds] at e₀
    rw [(hAe j).deriv_eq, (hAe (j + 1)).deriv_eq] at e₁ e₂
    rw [(hAe j).iteratedDeriv_eq 2, (hAe (j + 1)).iteratedDeriv_eq 2] at e₂
    have hjh : ((j : ℝ) + 1) * h = j * h + h := by ring
    have hj₁ : |t j - ℓ| ≤ h := by
      rw [ht j hj.le, abs_le]
      constructor <;> linarith [hℓj.1, hℓj.2, hjh]
    have hj₂ : |t (j + 1) - ℓ| ≤ h := by
      rw [ht (j + 1) hj, abs_le]
      push_cast
      constructor <;> linarith [hℓj.1, hℓj.2, hjh]
    have hj₁' : |t j - ℓ| ≤ h₀' := hj₁.trans (hhh₀.le.trans hh₀le.1)
    have hj₂' : |t (j + 1) - ℓ| ≤ h₀' := hj₂.trans (hhh₀.le.trans hh₀le.1)
    simp only [iteratedDeriv_zero] at e₀
    simp only [iteratedDeriv_one] at e₁
    interval_cases k
    · have a₁ := hu₀ r hr ℓ hℓ (t j) (htI j) hj₁'
      have a₂ := hu₀ r hr ℓ hℓ (t (j + 1)) (htI _) hj₂'
      simp only [iteratedDeriv_zero] at a₁ a₂ ⊢
      linarith [max_lt a₁ a₂]
    · have a₁ := hu₁ r hr ℓ hℓ (t j) (htI j) (hj₁.trans (hhh₀.le.trans hh₀le.2.1))
      have a₂ := hu₁ r hr ℓ hℓ (t (j + 1)) (htI _) (hj₂.trans (hhh₀.le.trans hh₀le.2.1))
      simp only [iteratedDeriv_one] at a₁ a₂ ⊢
      linarith [max_lt a₁ a₂]
    · have a₁ := hu₂ r hr ℓ hℓ (t j) (htI j) (hj₁.trans (hhh₀.le.trans hh₀le.2.2.1))
      have a₂ := hu₂ r hr ℓ hℓ (t (j + 1)) (htI _) (hj₂.trans (hhh₀.le.trans hh₀le.2.2.1))
      have hd := hL r hr₃ (t (j + 1)) (htI _) (t j) (htI j)
      rw [abs_sub_comm (t j), hstep j hj, abs_of_pos hh] at hd
      have hd2 : (deriv (χ (t j)) r - deriv (χ (t (j + 1))) r) ^ 2 ≤ (L * h) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hd 2
      have hX : h * (Q * L ^ 2 + 1) < τ * c :=
        (lt_div_iff₀ (by positivity)).1 (hhh₀.trans_le hh₀le.2.2.2.2)
      have hkey : Q * (deriv (χ (t j)) r - deriv (χ (t (j + 1))) r) ^ 2 / (2 * δ) ≤ τ / 2 := by
        rw [div_le_iff₀ (by positivity), hδ_def]
        linarith [mul_le_mul_of_nonneg_left hd2 hQ, mul_lt_mul_of_pos_left hX hh, sq_nonneg h]
      linarith [max_lt a₁ a₂]

end SymplecticGeometry

end
