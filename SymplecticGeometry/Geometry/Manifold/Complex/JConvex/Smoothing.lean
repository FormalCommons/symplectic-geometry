/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.LeviForm
public import SymplecticGeometry.Analysis.SpecialFunctions.SmoothedMax
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Smoothing the maximum of strictly plurisubharmonic functions

The maximum of two strictly plurisubharmonic functions on a complex manifold is not smooth where
they agree. Replacing it by the smoothed maximum `SymplecticGeometry.smoothedMax δ` keeps strict
plurisubharmonicity, and changes nothing where the two functions differ by at least `δ`.

Write `h = smoothedAbs δ`, so that `smoothedMax δ (f y) (g y) = (f + g + h ∘ (f - g)) / 2`. Since
`h` is convex, the Levi form of `h ∘ (f - g)` is at least `h'(f - g)` times that of `f - g`, so
twice the Levi form of the smoothed maximum is at least `(1 + h') L_f + (1 - h') L_g`. As
`|h'| ≤ 1`, both coefficients are nonnegative and their sum is `2`, so this is positive when
`L_f` and `L_g` are.

The gluing result: if `φ` is strictly plurisubharmonic on an open set `U`, and `ψ` on an open set
`V`, and near the points of `U` outside `V` the function `φ` exceeds `ψ` by at least `δ` (and
symmetrically near the points of `V` outside `U`), then the function equal to `φ` on `U \ V`, to
`ψ` on `V \ U` and to the smoothed maximum on `U ∩ V` is smooth and strictly plurisubharmonic on
`U ∪ V`. Typically `U` and `V` lie on the two sides of a hypersurface and overlap in a collar of
it, `φ` dominating on the side of `U` and `ψ` on the side of `V`.

## Main declarations

* `ContMDiffAt.smoothedMax`: the smoothed maximum of two `C^n` functions is `C^n`.
* `TauCeti.IsManifoldStrictlyPlurisubharmonicAt.smoothedMax`: the smoothed maximum of two
  functions that are `C²` and strictly plurisubharmonic at `x` is strictly plurisubharmonic at
  `x`.
* `SymplecticGeometry.exists_isManifoldStrictlyPlurisubharmonicAt_glue`: gluing two strictly
  plurisubharmonic functions by a smoothed maximum where they overlap.

## References

* [K. Cieliebak, Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Chapter 3, smoothing of maxima of `J`-convex functions.
-/

public section

open Set Filter Topology
open scoped Manifold ContDiff

open SymplecticGeometry

section ContMDiff

variable {H : Type*} [TopologicalSpace H]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {I : ModelWithCorners ℝ F H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞} {f g : M → ℝ} {x : M}

/-- The smoothed maximum of two functions that are `C^n` at `x` is `C^n` at `x`. -/
theorem ContMDiffAt.smoothedMax (hf : ContMDiffAt I 𝓘(ℝ) n f x) (hg : ContMDiffAt I 𝓘(ℝ) n g x)
    (δ : ℝ) : ContMDiffAt I 𝓘(ℝ) n (fun y ↦ smoothedMax δ (f y) (g y)) x :=
  (contDiff_smoothedMax δ).comp_contMDiffAt (f := fun y ↦ (f y, g y)) (hf.prodMk_space hg)

/-- The smoothed maximum of two `C^n` functions is `C^n`. -/
theorem ContMDiff.smoothedMax (hf : ContMDiff I 𝓘(ℝ) n f) (hg : ContMDiff I 𝓘(ℝ) n g)
    (δ : ℝ) : ContMDiff I 𝓘(ℝ) n fun y ↦ smoothedMax δ (f y) (g y) :=
  fun x ↦ (hf x).smoothedMax (hg x) δ

end ContMDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

namespace TauCeti.IsManifoldStrictlyPlurisubharmonicAt

/-- **The smoothed maximum of strictly plurisubharmonic functions.** For `δ ≥ 0`, if `f` and `g`
are `C²` and strictly plurisubharmonic at `x`, then so is `y ↦ smoothedMax δ (f y) (g y)`. -/
theorem smoothedMax {f g : M → ℝ} {x : M} {δ : ℝ} (hδ : 0 ≤ δ)
    (hf : IsManifoldStrictlyPlurisubharmonicAt E f x)
    (hg : IsManifoldStrictlyPlurisubharmonicAt E g x)
    (hf' : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 f x) (hg' : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 g x) :
    IsManifoldStrictlyPlurisubharmonicAt E
      (fun y ↦ SymplecticGeometry.smoothedMax δ (f y) (g y)) x := by
  have hfg : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 (f - g) x := hf'.sub hg'
  have hh : ContDiffAt ℝ 2 (smoothedAbs δ) ((f - g) x) :=
    (contDiff_smoothedAbs (n := 2) δ).contDiffAt
  have hF : (fun y ↦ SymplecticGeometry.smoothedMax δ (f y) (g y)) =
      (1 / 2 : ℝ) • (f + g + smoothedAbs δ ∘ (f - g)) := by
    funext y
    simp only [smoothedMax_def, Pi.smul_apply, Pi.add_apply, Function.comp_apply, Pi.sub_apply,
      smul_eq_mul]
    ring
  rw [isManifoldStrictlyPlurisubharmonicAt_iff] at hf hg ⊢
  intro v hv
  have hsub : (manifoldLeviForm E (f - g) x v v).re =
      (manifoldLeviForm E f x v v).re - (manifoldLeviForm E g x v v).re := by
    rw [sub_eq_add_neg f, manifoldLeviForm_add (g := -g) hf' hg'.neg, manifoldLeviForm_neg]
    simp [sub_eq_add_neg]
  have hL := le_re_manifoldLeviForm_scalar_comp_apply_self hh hfg
    (iteratedDeriv_two_smoothedAbs_nonneg hδ _) v
  rw [hsub] at hL
  rw [hF, manifoldLeviForm_smul, manifoldLeviForm_add (hf'.add hg')
    (hh.comp_contMDiffAt hfg), manifoldLeviForm_add hf' hg']
  simp only [LinearMap.smul_apply, LinearMap.add_apply, Complex.add_re, smul_eq_mul,
    Complex.re_ofReal_mul]
  have hd := abs_le.1 (abs_deriv_smoothedAbs_le_one δ ((f - g) x))
  have ha := hf v hv
  have hb := hg v hv
  set d := deriv (smoothedAbs δ) ((f - g) x)
  rcases le_total 0 d with h | h
  · nlinarith [mul_nonneg h ha.le, mul_nonneg (sub_nonneg.2 hd.2) hb.le]
  · nlinarith [mul_nonneg (neg_nonneg.2 h) hb.le, mul_nonneg (neg_le_iff_add_nonneg.1 hd.1) ha.le]

end TauCeti.IsManifoldStrictlyPlurisubharmonicAt

namespace SymplecticGeometry

open TauCeti

/-- **Gluing strictly plurisubharmonic functions by a smoothed maximum.** Let `φ` be `C^n`
(`n ≥ 2`) and strictly plurisubharmonic on an open set `U`, and `ψ` on an open set `V`. Suppose
that every point of `U \ V` has a neighbourhood on whose points in `V` we have `ψ + δ ≤ φ`, and
every point of `V \ U` one on whose points in `U` we have `φ + δ ≤ ψ`, with `δ > 0`. Then there is
a function `F` equal to `φ` on `U \ V`, to `ψ` on `V \ U` and to `smoothedMax δ φ ψ` on `U ∩ V`
that is `C^n` and strictly plurisubharmonic at every point of `U ∪ V`. -/
theorem exists_isManifoldStrictlyPlurisubharmonicAt_glue {n : ℕ∞} (hn : 2 ≤ n) {φ ψ : M → ℝ}
    {U V : Set M} {δ : ℝ} (hδ : 0 < δ) (hU : IsOpen U) (hV : IsOpen V)
    (hφ : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) n φ U) (hψ : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) n ψ V)
    (hφU : ∀ x ∈ U, IsManifoldStrictlyPlurisubharmonicAt E φ x)
    (hψV : ∀ x ∈ V, IsManifoldStrictlyPlurisubharmonicAt E ψ x)
    (hUV : ∀ x ∈ U \ V, ∀ᶠ y in 𝓝 x, y ∈ V → ψ y + δ ≤ φ y)
    (hVU : ∀ x ∈ V \ U, ∀ᶠ y in 𝓝 x, y ∈ U → φ y + δ ≤ ψ y) :
    ∃ F : M → ℝ, (∀ x ∈ U ∪ V, ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) n F x ∧
        IsManifoldStrictlyPlurisubharmonicAt E F x) ∧
      EqOn F φ (U \ V) ∧ EqOn F ψ (V \ U) ∧ ∀ x ∈ U ∩ V, F x = smoothedMax δ (φ x) (ψ x) := by
  classical
  have hn' : (2 : WithTop ℕ∞) ≤ n := WithTop.coe_le_coe.2 hn
  set F : M → ℝ := fun y ↦ if y ∈ U then (if y ∈ V then smoothedMax δ (φ y) (ψ y) else φ y)
    else ψ y
  refine ⟨F, fun x hx ↦ ?_, fun y hy ↦ by simp [F, hy.1, hy.2],
    fun y hy ↦ by simp [F, hy.2], fun y hy ↦ by simp [F, hy.1, hy.2]⟩
  by_cases hxU : x ∈ U <;> by_cases hxV : x ∈ V
  · -- Near a point of `U ∩ V`, `F` is the smoothed maximum.
    have hφx := hφ.contMDiffAt (hU.mem_nhds hxU)
    have hψx := hψ.contMDiffAt (hV.mem_nhds hxV)
    have hEq : F =ᶠ[𝓝 x] fun y ↦ smoothedMax δ (φ y) (ψ y) := by
      filter_upwards [hU.mem_nhds hxU, hV.mem_nhds hxV] with y hyU hyV
      simp [F, hyU, hyV]
    exact ⟨(hφx.smoothedMax hψx δ).congr_of_eventuallyEq hEq,
      ((hφU x hxU).smoothedMax hδ.le (hψV x hxV) (hφx.of_le hn')
        (hψx.of_le hn')).congr_of_eventuallyEq hEq⟩
  · -- Near a point of `U \ V`, `F` is `φ`.
    have hEq : F =ᶠ[𝓝 x] φ := by
      filter_upwards [hUV x ⟨hxU, hxV⟩, hU.mem_nhds hxU] with y hy hyU
      by_cases hyV : y ∈ V
      · simp [F, hyU, hyV, smoothedMax_eq_left hδ (hy hyV)]
      · simp [F, hyU, hyV]
    exact ⟨(hφ.contMDiffAt (hU.mem_nhds hxU)).congr_of_eventuallyEq hEq,
      (hφU x hxU).congr_of_eventuallyEq hEq⟩
  · -- Near a point of `V \ U`, `F` is `ψ`.
    have hEq : F =ᶠ[𝓝 x] ψ := by
      filter_upwards [hVU x ⟨hxV, hxU⟩, hV.mem_nhds hxV] with y hy hyV
      by_cases hyU : y ∈ U
      · simp [F, hyU, hyV, smoothedMax_eq_right hδ (hy hyU)]
      · simp [F, hyU]
    exact ⟨(hψ.contMDiffAt (hV.mem_nhds hxV)).congr_of_eventuallyEq hEq,
      (hψV x hxV).congr_of_eventuallyEq hEq⟩
  · exact absurd hx (by simp [hxU, hxV])

end SymplecticGeometry

end
