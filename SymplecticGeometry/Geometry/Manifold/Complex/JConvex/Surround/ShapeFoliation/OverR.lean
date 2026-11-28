/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Analysis.SpecialFunctions.SmoothedMax
public import SymplecticGeometry.Geometry.Manifold.Complex.JConvex.Surround.ConvexShape.Basic

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import TauCeti.Analysis.Calculus.ContDiff.Prod
import SymplecticGeometry.Analysis.Calculus.Deriv.Mul
import SymplecticGeometry.Analysis.Calculus.IteratedDeriv.Prod
import SymplecticGeometry.Analysis.SpecialFunctions.SmoothTransition.Basic
import SymplecticGeometry.Geometry.Manifold.Complex.JConvex.Surround.ConvexShape.SmoothedMax
import SymplecticGeometry.Geometry.Manifold.Complex.JConvex.Surround.ShapeFoliation.Smoothing

/-!
# Strictly monotone families of shapes over `R`: the end pieces and the blend

This file gives the three pieces of `ShapeFoliation/Smoothing.lean` for a family of curves
`r = ρ ℓ R`, graphs over `R`, with the criterion `SymplecticGeometry.IsConvexShapeOverRAt` in
place of `SymplecticGeometry.IsConvexShapeAt`. Over `R` the inside of a curve is the side of
small `r`, so the leaves rise as `ρ` falls: the families here have `∂ρ/∂ℓ < 0`, functions are
lowered where those over `r` are raised, and the smoothed minimum
`-smoothedMax δ (-ρ₁) (-ρ₂)` takes the place of the smoothed maximum.

* `SymplecticGeometry.exists_smoothedMin_shapeFamilyOverR`: the piece next to `ℓ₁`, the smoothed
  minimum of a fixed curve `M` lowered by a nondecreasing `q ≥ 0` and a reparametrized member of
  `ρ`. Its value, slope and second derivative are bounded by those of the two curves, in the
  directions opposite to those of `SymplecticGeometry.exists_smoothedMax_shapeFamily`; in
  particular the second derivative is bounded above.
* `SymplecticGeometry.exists_comp_sub_shapeFamilyOverR`: the piece next to `ℓ₀`, a reparametrized
  member of `ρ` lowered by `q`. It keeps the criterion by
  `SymplecticGeometry.IsConvexShapeOverRAt.sub_const`, which asks `q` to stay below `ρ`.
* `SymplecticGeometry.exists_blend_shapeFamilyOverR`: the blend with `ρ` near the end `R₂` by a
  cutoff in `R`, for families close to `ρ` in value and slope whose second derivative is less
  than that of `ρ` plus a tolerance. It uses the one-sided blend lemma
  `exists_forall_isConvexShapeOverRAt_mul_add_one_sub_mul_of_iteratedDeriv_two_lt_add`.

The first two pieces are `SymplecticGeometry.exists_smoothedMax_family` and
`SymplecticGeometry.exists_comp_add_family`, which do not involve a convexity criterion, applied
to `-ρ` and negated; the criterion comes from the uniform smoothed minimum
`SymplecticGeometry.exists_forall_isConvexShapeOverRAt_smoothedMin`, applied to the pairs of
curves that the smoothed minima combine, and from `IsConvexShapeOverRAt.sub_const`. The blend is
smooth by `SymplecticGeometry.contDiffOn_blend`. The estimates
`SymplecticGeometry.abs_sub_lt_of_eventuallyEq_add_const` and
`SymplecticGeometry.abs_sub_lt_of_max_le_of_le_max`, and
`SymplecticGeometry.blend_eventuallyEq_nhdsSet_union`, apply to these pieces as they are, after
negation where needed.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Proposition 3.25 and Corollary 4.29.
-/

public section

noncomputable section

namespace SymplecticGeometry

open Set Filter Topology
open scoped ContDiff

/-- **The piece of a strictly monotone family of shapes over `R` next to `ℓ₁`.** Let
`ρ : ℝ → ℝ → ℝ` be smooth in `(ℓ, R)` on an open set containing `[b, ℓ₁] × [R₁, R₂]`, with
`ρ ℓ` satisfying the criterion over `R` at `R` and `∂ρ/∂ℓ < 0` at each point of the rectangle.
Let `M` be a smooth function satisfying the criterion over `R` on `[R₁, R₂]`, and `q` a smooth
nondecreasing function with `q b ≥ 0`, `q ℓ₁ < M` on `[R₁, R₂]` and `q' > 0` on `[b, c)`, where
`b < c ≤ ℓ₁`. Suppose that `M - q b < ρ b` and that `ρ ℓ < M - q ℓ` for `ℓ ∈ [c, ℓ₁]`, on
`[R₁, R₂]`. Then for each `ε > 0` there are `δ ∈ (0, ε]` and `T : ℝ → ℝ → ℝ`, smooth on `ℝ²`,
such that on the rectangle `T ℓ` satisfies the criterion over `R` at `R` with `∂T/∂ℓ < 0`; `T`
equals `M R - q ℓ` near `{b} × [R₁, R₂]` and `ρ` near `{ℓ₁} × [R₁, R₂]`; and at each point
`(ℓ, R)` of the rectangle, `T ℓ` is the smoothed minimum
`-smoothedMax δ (-(M - q ℓ)) (-ρ ℓ')` near `R` for some `ℓ' ∈ [b, ℓ₁]`, so that `T ℓ R` lies
between `min (M R - q ℓ) (ρ ℓ' R) - δ / 2` and that minimum, its first `R`-derivative between
those of `M` and `ρ ℓ'`, and its second `R`-derivative is at most the larger of those of `M` and
`ρ ℓ'`. -/
theorem exists_smoothedMin_shapeFamilyOverR {ρ : ℝ → ℝ → ℝ} {M q : ℝ → ℝ} {U : Set (ℝ × ℝ)}
    {b c ℓ₁ R₁ R₂ ε : ℝ} (hbc : b < c) (hcℓ : c ≤ ℓ₁) (hU : IsOpen U)
    (hRU : Icc b ℓ₁ ×ˢ Icc R₁ R₂ ⊆ U) (hρ : ContDiffOn ℝ ∞ (Function.uncurry ρ) U)
    (hρc : ∀ x ∈ Icc b ℓ₁ ×ˢ Icc R₁ R₂, IsConvexShapeOverRAt (ρ x.1) x.2)
    (hρℓ : ∀ x ∈ Icc b ℓ₁ ×ˢ Icc R₁ R₂, deriv (fun ℓ ↦ ρ ℓ x.2) x.1 < 0)
    (hM : ContDiff ℝ ∞ M) (hMc : ∀ R ∈ Icc R₁ R₂, IsConvexShapeOverRAt M R)
    (hq : ContDiff ℝ ∞ q) (hqm : Monotone q) (hqb : 0 ≤ q b)
    (hqM : ∀ R ∈ Icc R₁ R₂, q ℓ₁ < M R) (hq' : ∀ ℓ ∈ Ico b c, 0 < deriv q ℓ)
    (hgb : ∀ R ∈ Icc R₁ R₂, M R - q b < ρ b R)
    (hgc : ∀ ℓ ∈ Icc c ℓ₁, ∀ R ∈ Icc R₁ R₂, ρ ℓ R < M R - q ℓ) (hε : 0 < ε) :
    ∃ δ ∈ Ioc 0 ε, ∃ T : ℝ → ℝ → ℝ, ContDiff ℝ ∞ (Function.uncurry T) ∧
      (∀ x ∈ Icc b ℓ₁ ×ˢ Icc R₁ R₂, IsConvexShapeOverRAt (T x.1) x.2) ∧
      (∀ x ∈ Icc b ℓ₁ ×ˢ Icc R₁ R₂, deriv (fun ℓ ↦ T ℓ x.2) x.1 < 0) ∧
      Function.uncurry T =ᶠ[𝓝ˢ ({b} ×ˢ Icc R₁ R₂)] (fun x ↦ M x.2 - q x.1) ∧
      Function.uncurry T =ᶠ[𝓝ˢ ({ℓ₁} ×ˢ Icc R₁ R₂)] Function.uncurry ρ ∧
      ∀ x ∈ Icc b ℓ₁ ×ˢ Icc R₁ R₂, ∃ ℓ' ∈ Icc b ℓ₁,
        T x.1 =ᶠ[𝓝 x.2] (fun R ↦ -smoothedMax δ (-(M R - q x.1)) (-ρ ℓ' R)) ∧
        min (M x.2 - q x.1) (ρ ℓ' x.2) - δ / 2 ≤ T x.1 x.2 ∧
        T x.1 x.2 ≤ min (M x.2 - q x.1) (ρ ℓ' x.2) ∧
        min (deriv M x.2) (deriv (ρ ℓ') x.2) ≤ deriv (T x.1) x.2 ∧
        deriv (T x.1) x.2 ≤ max (deriv M x.2) (deriv (ρ ℓ') x.2) ∧
        iteratedDeriv 2 (T x.1) x.2 ≤
          max (iteratedDeriv 2 M x.2) (iteratedDeriv 2 (ρ ℓ') x.2) := by
  -- The width `δ₀` below which the smoothed minima of `M - q ℓ` and a member of `ρ` are shapes
  -- over `R`.
  have hFM : ContDiff ℝ ∞ fun x : (ℝ × ℝ) × ℝ ↦ M x.2 - q x.1.1 :=
    (hM.comp contDiff_snd).sub (hq.comp (contDiff_fst.comp contDiff_fst))
  have hAx : ∀ p ∈ Icc b ℓ₁ ×ˢ Icc b ℓ₁, ∀ R ∈ Icc R₁ R₂,
      ContDiffAt ℝ ∞ (Function.uncurry fun (p : ℝ × ℝ) R ↦ ρ p.2 R) (p, R) := fun p hp R hR ↦
    (hρ.contDiffAt (hU.mem_nhds (hRU ⟨hp.2, hR⟩))).comp (p, R)
      ((contDiffAt_snd.comp _ contDiffAt_fst).prodMk contDiffAt_snd)
  obtain ⟨δ₀, hδ₀, hconv⟩ := exists_forall_isConvexShapeOverRAt_smoothedMin
    (K := Icc b ℓ₁ ×ˢ Icc b ℓ₁) (isCompact_Icc.prod isCompact_Icc)
    (M := fun p R ↦ M R - q p.1) (A := fun p R ↦ ρ p.2 R) (R₁ := R₁) (R₂ := R₂)
    (fun p _ _ _ ↦ ((hFM.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)).contDiffAt)
    (fun p hp R hR ↦ (hAx p hp R hR).uncurry_left.of_le (by simp))
    (fun p hp R hR ↦ (hMc R hR).sub_const (hqb.trans (hqm hp.1.1))
      ((hqm hp.1.2).trans_lt (hqM R hR)))
    (fun p hp R hR ↦ hρc (p.2, R) ⟨hp.2, hR⟩)
    (fun _ _ _ _ ↦ (hFM.contDiffAt.continuousAt_iteratedDeriv_prod_right
      (by exact_mod_cast le_top)).continuousWithinAt)
    (fun _ _ x hx ↦ ((hAx x.1 hx.1 x.2 hx.2).continuousAt_iteratedDeriv_prod_right
      (by exact_mod_cast le_top)).continuousWithinAt)
  -- The smoothed maximum of `-M + q ℓ` and `-ρ`, a family over `r` with `∂(-ρ)/∂ℓ > 0`.
  obtain ⟨δ, hδ, T, hT, hTℓ, hTb, hTℓ₁, hTx⟩ := exists_smoothedMax_family
    (χ := fun ℓ R ↦ -ρ ℓ R) (M := fun R ↦ -M R) hbc hcℓ hU hRU hρ.neg
    (fun x hx ↦ by rw [deriv.fun_neg]; linarith [hρℓ x hx]) hM.neg hq hqm hq'
    (fun R hR ↦ by linarith [hgb R hR]) (fun ℓ hℓ R hR ↦ by linarith [hgc ℓ hℓ R hR])
    (lt_min hε hδ₀)
  have hloc : ∀ x : ℝ × ℝ, ∀ ℓ',
      T x.1 =ᶠ[𝓝 x.2] (fun R ↦ smoothedMax δ (-M R + q x.1) (-ρ ℓ' R)) →
        (fun R ↦ -T x.1 R) =ᶠ[𝓝 x.2] fun R ↦ -smoothedMax δ (-(M R - q x.1)) (-ρ ℓ' R) :=
    fun x ℓ' h ↦ h.mono fun R hR ↦ by dsimp only at hR ⊢; rw [hR, neg_sub, neg_add_eq_sub]
  refine ⟨δ, ⟨hδ.1, hδ.2.trans (min_le_left _ _)⟩, fun ℓ R ↦ -T ℓ R, hT.neg, fun x hx ↦ ?_,
    fun x hx ↦ ?_, ?_, ?_, fun x hx ↦ ?_⟩
  · -- The members satisfy the criterion over `R`.
    obtain ⟨ℓ', hℓ', h, -⟩ := hTx x hx
    exact (hconv δ ⟨hδ.1, hδ.2.trans (min_le_right _ _)⟩ (x.1, ℓ') ⟨hx.1, hℓ'⟩ x.2
      hx.2).congr_of_eventuallyEq (hloc x ℓ' h)
  · -- The `ℓ`-derivative.
    beta_reduce
    rw [deriv.fun_neg]
    linarith [hTℓ x hx]
  · -- Near `b`, the family is `M - q ℓ`.
    filter_upwards [hTb] with y hy
    simp only [Function.uncurry_def] at hy ⊢
    rw [hy]
    ring
  · -- Near `ℓ₁`, the family is `ρ`.
    filter_upwards [hTℓ₁] with y hy
    simp only [Function.uncurry_def] at hy ⊢
    rw [hy, neg_neg]
  · -- The pointwise comparison with `M - q ℓ` and `ρ ℓ'`, from that of the family over `r`.
    obtain ⟨ℓ', hℓ', h, hv₁, hv₂, hd₁, hd₂, hdd⟩ := hTx x hx
    beta_reduce at hv₁ hv₂ hd₁ hd₂ hdd ⊢
    rw [show -M x.2 + q x.1 = -(M x.2 - q x.1) by ring, max_neg_neg] at hv₁ hv₂
    rw [deriv.fun_neg, deriv.fun_neg, min_neg_neg] at hd₁
    rw [deriv.fun_neg, deriv.fun_neg, max_neg_neg] at hd₂
    rw [iteratedDeriv_fun_neg, iteratedDeriv_fun_neg, min_neg_neg] at hdd
    rw [deriv.fun_neg, iteratedDeriv_fun_neg]
    exact ⟨ℓ', hℓ', hloc x ℓ' h, by linarith, by linarith, by linarith, by linarith,
      by linarith⟩

/-- **The piece of a strictly monotone family of shapes over `R` next to `ℓ₀`.** Let
`ρ : ℝ → ℝ → ℝ` be smooth in `(ℓ, R)` on an open set containing `[ℓ₀, a] × [R₁, R₂]`, with
`ρ ℓ` satisfying the criterion over `R` at `R` and `∂ρ/∂ℓ < 0` at each point of the rectangle,
and let `q` be a smooth nondecreasing function that vanishes near `ℓ₀`, has `q' > 0` on
`[a₁, a]`, where `ℓ₀ < a₁ < a`, and has `q a < ρ` on the rectangle. Then there is
`T : ℝ → ℝ → ℝ`, smooth on `ℝ²`, such that on the rectangle `T ℓ` satisfies the criterion over
`R` at `R` with `∂T/∂ℓ < 0`; `T` equals `ρ` near `{ℓ₀} × [R₁, R₂]` and `ρ a R - q ℓ` near
`{a} × [R₁, R₂]`; and at each point `(ℓ, R)` of the rectangle, `T ℓ` agrees near `R` with
`ρ ℓ' - q ℓ` for some `ℓ' ∈ [ℓ₀, a]`. -/
theorem exists_comp_sub_shapeFamilyOverR {ρ : ℝ → ℝ → ℝ} {q : ℝ → ℝ} {U : Set (ℝ × ℝ)}
    {ℓ₀ a₁ a R₁ R₂ : ℝ} (hℓa₁ : ℓ₀ < a₁) (ha₁a : a₁ < a) (hU : IsOpen U)
    (hRU : Icc ℓ₀ a ×ˢ Icc R₁ R₂ ⊆ U) (hρ : ContDiffOn ℝ ∞ (Function.uncurry ρ) U)
    (hρc : ∀ x ∈ Icc ℓ₀ a ×ˢ Icc R₁ R₂, IsConvexShapeOverRAt (ρ x.1) x.2)
    (hρℓ : ∀ x ∈ Icc ℓ₀ a ×ˢ Icc R₁ R₂, deriv (fun ℓ ↦ ρ ℓ x.2) x.1 < 0)
    (hq : ContDiff ℝ ∞ q) (hqm : Monotone q) (hq₀ : q =ᶠ[𝓝 ℓ₀] fun _ ↦ 0)
    (hqa : ∀ ℓ ∈ Icc a₁ a, 0 < deriv q ℓ)
    (hqρ : ∀ x ∈ Icc ℓ₀ a ×ˢ Icc R₁ R₂, q a < ρ x.1 x.2) :
    ∃ T : ℝ → ℝ → ℝ, ContDiff ℝ ∞ (Function.uncurry T) ∧
      (∀ x ∈ Icc ℓ₀ a ×ˢ Icc R₁ R₂, IsConvexShapeOverRAt (T x.1) x.2) ∧
      (∀ x ∈ Icc ℓ₀ a ×ˢ Icc R₁ R₂, deriv (fun ℓ ↦ T ℓ x.2) x.1 < 0) ∧
      Function.uncurry T =ᶠ[𝓝ˢ ({ℓ₀} ×ˢ Icc R₁ R₂)] Function.uncurry ρ ∧
      Function.uncurry T =ᶠ[𝓝ˢ ({a} ×ˢ Icc R₁ R₂)] (fun x ↦ ρ a x.2 - q x.1) ∧
      ∀ x ∈ Icc ℓ₀ a ×ˢ Icc R₁ R₂, ∃ ℓ' ∈ Icc ℓ₀ a,
        T x.1 =ᶠ[𝓝 x.2] fun R ↦ ρ ℓ' R - q x.1 := by
  -- The family over `r` of `exists_comp_add_family` for `-ρ`, negated.
  obtain ⟨T, hT, hTℓ, hT₀, hTa, hTx⟩ := exists_comp_add_family (χ := fun ℓ R ↦ -ρ ℓ R)
    hℓa₁ ha₁a hU hRU hρ.neg (fun x hx ↦ by rw [deriv.fun_neg]; linarith [hρℓ x hx]) hq hqm hq₀
    hqa
  have hloc : ∀ x ∈ Icc ℓ₀ a ×ˢ Icc R₁ R₂, ∃ ℓ' ∈ Icc ℓ₀ a,
      (fun R ↦ -T x.1 R) =ᶠ[𝓝 x.2] fun R ↦ ρ ℓ' R - q x.1 := fun x hx ↦ by
    obtain ⟨ℓ', hℓ', h⟩ := hTx x hx
    exact ⟨ℓ', hℓ', h.mono fun R hR ↦ by dsimp only at hR ⊢; rw [hR, neg_add_eq_sub, neg_sub]⟩
  refine ⟨fun ℓ R ↦ -T ℓ R, hT.neg, fun x hx ↦ ?_, fun x hx ↦ ?_, ?_, ?_, hloc⟩
  · -- The members satisfy the criterion over `R`, since `0 ≤ q ℓ ≤ q a < ρ`.
    obtain ⟨ℓ', hℓ', h⟩ := hloc x hx
    exact ((hρc (ℓ', x.2) ⟨hℓ', hx.2⟩).sub_const (hq₀.eq_of_nhds ▸ hqm hx.1.1)
      ((hqm hx.1.2).trans_lt (hqρ (ℓ', x.2) ⟨hℓ', hx.2⟩))).congr_of_eventuallyEq h
  · -- The `ℓ`-derivative.
    beta_reduce
    rw [deriv.fun_neg]
    linarith [hTℓ x hx]
  · -- Near `ℓ₀`, the family is `ρ`.
    filter_upwards [hT₀] with y hy
    simp only [Function.uncurry_def] at hy ⊢
    rw [hy, neg_neg]
  · -- Near `a`, the family is `ρ a - q`.
    filter_upwards [hTa] with y hy
    simp only [Function.uncurry_def] at hy ⊢
    rw [hy]
    ring

/-- **Blending a family of shapes over `R` with `ρ` near `R₂`.** Let `ρ : ℝ → ℝ → ℝ` be smooth
in `(ℓ, R)` on an open set `V` containing the band `[ℓ₀, ℓ₁] × [R₃, R₂]`, with `ρ ℓ` satisfying
the criterion over `R` at `R` and `∂ρ/∂ℓ < 0` at each point of the band, where `R₃ < R₂`. Then
there are a smooth cutoff `β` with values in `[0, 1]`, equal to `1` on `(-∞, R₃]` and to `0` near
`R₂`, and a tolerance `τ > 0`, such that the following holds for every family `ψ₀` smooth on
`ℝ²` whose members satisfy the criterion over `R` with `∂ψ₀/∂ℓ < 0` on `[ℓ₀, ℓ₁] × [R₁, R₂]`,
and which on the band is within `τ` of `ρ` in value and first `R`-derivative and has second
`R`-derivative less than that of `ρ` plus `τ`. The blend
`ψ ℓ R = β R * ψ₀ ℓ R + (1 - β R) * ρ ℓ R` is smooth on `(ℝ × (-∞, R₃)) ∪ V`, and on
`[ℓ₀, ℓ₁] × [R₁, R₂]` its members satisfy the criterion over `R` and `∂ψ/∂ℓ < 0`. The cutoff
and the tolerance depend only on `ρ` and the band, not on `ψ₀`. -/
theorem exists_blend_shapeFamilyOverR {ρ : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)}
    {ℓ₀ ℓ₁ R₁ R₃ R₂ : ℝ} (hR₃₂ : R₃ < R₂) (hV : IsOpen V)
    (hBV : Icc ℓ₀ ℓ₁ ×ˢ Icc R₃ R₂ ⊆ V) (hρ : ContDiffOn ℝ ∞ (Function.uncurry ρ) V)
    (hρc : ∀ x ∈ Icc ℓ₀ ℓ₁ ×ˢ Icc R₃ R₂, IsConvexShapeOverRAt (ρ x.1) x.2)
    (hρℓ : ∀ x ∈ Icc ℓ₀ ℓ₁ ×ˢ Icc R₃ R₂, deriv (fun ℓ ↦ ρ ℓ x.2) x.1 < 0) :
    ∃ β : ℝ → ℝ, ContDiff ℝ ∞ β ∧ (∀ R, β R ∈ Icc 0 1) ∧ EqOn β 1 (Iic R₃) ∧
      β =ᶠ[𝓝 R₂] 0 ∧ ∃ τ > 0, ∀ ψ₀ : ℝ → ℝ → ℝ, ContDiff ℝ ∞ (Function.uncurry ψ₀) →
        (∀ x ∈ Icc ℓ₀ ℓ₁ ×ˢ Icc R₁ R₂, IsConvexShapeOverRAt (ψ₀ x.1) x.2) →
        (∀ x ∈ Icc ℓ₀ ℓ₁ ×ˢ Icc R₁ R₂, deriv (fun ℓ ↦ ψ₀ ℓ x.2) x.1 < 0) →
        (∀ x ∈ Icc ℓ₀ ℓ₁ ×ˢ Icc R₃ R₂, |ψ₀ x.1 x.2 - ρ x.1 x.2| < τ ∧
          |deriv (ψ₀ x.1) x.2 - deriv (ρ x.1) x.2| < τ ∧
          iteratedDeriv 2 (ψ₀ x.1) x.2 < iteratedDeriv 2 (ρ x.1) x.2 + τ) →
        ContDiffOn ℝ ∞ (fun x : ℝ × ℝ ↦ β x.2 * ψ₀ x.1 x.2 + (1 - β x.2) * ρ x.1 x.2)
            (univ ×ˢ Iio R₃ ∪ V) ∧
          (∀ x ∈ Icc ℓ₀ ℓ₁ ×ˢ Icc R₁ R₂,
            IsConvexShapeOverRAt (fun R ↦ β R * ψ₀ x.1 R + (1 - β R) * ρ x.1 R) x.2) ∧
          ∀ x ∈ Icc ℓ₀ ℓ₁ ×ˢ Icc R₁ R₂,
            deriv (fun ℓ ↦ β x.2 * ψ₀ ℓ x.2 + (1 - β x.2) * ρ ℓ x.2) x.1 < 0 := by
  -- The cutoff: `1` up to `R₃`, `0` from the midpoint of `[R₃, R₂]` on.
  obtain ⟨β, hβs, hβI, -, hβ1, hβ0, -⟩ :=
    exists_contDiff_antitone_cutoff_mul_abs_deriv_le_deriv_deriv
      (show R₃ < (R₃ + R₂) / 2 by linarith)
  replace hβ0 : β =ᶠ[𝓝 R₂] 0 :=
    eventually_of_mem (Ici_mem_nhds (show (R₃ + R₂) / 2 < R₂ by linarith)) hβ0
  -- The tolerance, from the one-sided blend lemma over `R` on the band.
  have hK : IsCompact (Icc ℓ₀ ℓ₁ ×ˢ Icc R₃ R₂) := isCompact_Icc.prod isCompact_Icc
  have hρx : ∀ x ∈ Icc ℓ₀ ℓ₁ ×ˢ Icc R₃ R₂, ContDiffAt ℝ ∞ (Function.uncurry ρ) x :=
    fun x hx ↦ hρ.contDiffAt (hV.mem_nhds (hBV hx))
  obtain ⟨τ, hτ, hblend⟩ :=
    exists_forall_isConvexShapeOverRAt_mul_add_one_sub_mul_of_iteratedDeriv_two_lt_add hK hρc
      (fun _ _ x hx ↦ ((hρx x hx).continuousAt_iteratedDeriv_prod_right
        (by exact_mod_cast le_top)).continuousWithinAt)
      (hβs.of_le (by simp)) fun x _ ↦ (hβI x.2).1
  refine ⟨β, hβs, hβI, hβ1, hβ0, τ, hτ, fun ψ₀ hψ₀ hψ₀c hψ₀ℓ hclose ↦
    ⟨contDiffOn_blend hβs hβ1 hψ₀ hV hρ, fun x hx ↦ ?_, fun x hx ↦ ?_⟩⟩
  · -- The criterion: below `R₃` the blend is `ψ₀` near `R`; on the band, the blend lemma.
    rcases lt_or_ge x.2 R₃ with h | h
    · refine (hψ₀c x hx).congr_of_eventuallyEq ?_
      filter_upwards [Iio_mem_nhds h] with R hR
      simp [hβ1 (mem_Iic.2 (mem_Iio.1 hR).le)]
    · have hxK : x ∈ Icc ℓ₀ ℓ₁ ×ˢ Icc R₃ R₂ := ⟨hx.1, h, hx.2.2⟩
      obtain ⟨h₀, h₁, h₂⟩ := hclose x hxK
      exact hblend (ψ₀ x.1) x hxK (hψ₀.contDiffAt.uncurry_left.of_le (by simp))
        ((hρx x hxK).uncurry_left.of_le (by simp)) h₀ h₁ h₂
  · -- The `ℓ`-derivative: below `R₃` it is that of `ψ₀`; on the band, a convex combination of
    -- two negative numbers.
    rcases lt_or_ge x.2 R₃ with h | h
    · simpa [hβ1 (mem_Iic.2 h.le)] using hψ₀ℓ x hx
    · exact deriv_mul_add_one_sub_mul_neg (hψ₀ℓ x hx) (hρℓ x ⟨hx.1, h, hx.2.2⟩) (hβI x.2).1
        (hβI x.2).2

end SymplecticGeometry
