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
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import SymplecticGeometry.Analysis.Calculus.BumpFunction.Gluing
import SymplecticGeometry.Analysis.Calculus.Deriv.Mul
import SymplecticGeometry.Analysis.Calculus.Deriv.Rectangle
import SymplecticGeometry.Analysis.Calculus.IteratedDeriv.Prod
import SymplecticGeometry.Analysis.SpecialFunctions.SmoothTransition.Basic
import SymplecticGeometry.Geometry.Manifold.Complex.JConvex.Surround.ConvexShape.SmoothedMax
import SymplecticGeometry.Geometry.Manifold.Complex.JConvex.Surround.ShapeFoliation.Chain
import SymplecticGeometry.Geometry.Manifold.Complex.JConvex.Surround.ShapeFoliation.Smoothing
import SymplecticGeometry.Topology.Constructions.SumProd

/-!
# Strictly monotone families of shapes over `R`

This file gives the form over `R` of `ShapeFoliation/Smoothing.lean`, for a family of curves
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

With these pieces the file proves the theorem itself:

* `SymplecticGeometry.exists_shapeFoliation_overR`: the form over `R` of
  `SymplecticGeometry.exists_shapeFoliation`. A family `ρ` of curves that satisfy the criterion
  over `R` on `[ℓ₀, ℓ₁] × [R₁, R₂]`, `C²` in `R` with value and first two `R`-derivatives
  continuous in `(ℓ, R)`, lying above `ρ ℓ₁` for `ℓ < ℓ₁` and smooth with `∂ρ/∂ℓ < 0` near
  `{ℓ₀, ℓ₁} × [R₁, R₂] ∪ [ℓ₀, ℓ₁] × {R₂}`, is replaced by a family smooth on the rectangle with
  the same properties and `∂ψ/∂ℓ < 0` everywhere, equal to `ρ` near that part of the boundary.
  The proof follows that of `SymplecticGeometry.exists_shapeFoliation` step by step: the piece
  next to `ℓ₀`, the weakly decreasing chain
  `SymplecticGeometry.exists_antitone_shapeChain_overR` lowered by `q` in the middle, the
  piece next to `ℓ₁` below the last member of the chain, glued by
  `SymplecticGeometry.exists_contDiff_eventuallyEq_of_eventuallyEq_Icc` and blended with `ρ`
  near `R₂`. Over `R` the lowering `q` must stay below `ρ` and the chain, so it is also bounded
  by half a positive lower bound of `ρ` on the rectangle; the chain stays above that bound less
  its error, being antitone in `ℓ`.

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

/-- The closeness that `SymplecticGeometry.abs_sub_lt_of_eventuallyEq_add_const` and
`SymplecticGeometry.abs_sub_lt_of_max_le_of_le_max` give for `-f` and `-h` at `R` is the
closeness that `SymplecticGeometry.exists_blend_shapeFamilyOverR` asks of `f` and `h`. -/
private theorem abs_sub_lt_of_neg {f h : ℝ → ℝ} {R τ : ℝ}
    (H : |-f R - -h R| < τ ∧ |deriv (fun R ↦ -f R) R - deriv (fun R ↦ -h R) R| < τ ∧
      iteratedDeriv 2 (fun R ↦ -h R) R - τ < iteratedDeriv 2 (fun R ↦ -f R) R) :
    |f R - h R| < τ ∧ |deriv f R - deriv h R| < τ ∧
      iteratedDeriv 2 f R < iteratedDeriv 2 h R + τ := by
  obtain ⟨h₀, h₁, h₂⟩ := H
  rw [deriv.fun_neg, deriv.fun_neg] at h₁
  rw [iteratedDeriv_fun_neg, iteratedDeriv_fun_neg] at h₂
  rw [neg_sub_neg, abs_sub_comm] at h₀ h₁
  exact ⟨h₀, h₁, by linarith⟩

/-- Closeness of `g` to `h` at `R` in value and first two derivatives is that of `-g` to `-h`. -/
private theorem abs_iteratedDeriv_neg_sub_neg_lt {g h : ℝ → ℝ} {R ε : ℝ}
    (H : ∀ k ≤ 2, |iteratedDeriv k g R - iteratedDeriv k h R| < ε) :
    ∀ k ≤ 2, |iteratedDeriv k (fun R ↦ -g R) R - iteratedDeriv k (fun R ↦ -h R) R| < ε :=
  fun k hk ↦ by
    rw [iteratedDeriv_fun_neg, iteratedDeriv_fun_neg, neg_sub_neg, abs_sub_comm]
    exact H k hk

/-- **A strictly decreasing smooth family of shapes over `R` with prescribed ends.** Let
`Q = [ℓ₀, ℓ₁] × [R₁, R₂]` with `ℓ₀ < ℓ₁` and `R₁ < R₂`, and let `E` be the part
`{ℓ₀, ℓ₁} × [R₁, R₂] ∪ [ℓ₀, ℓ₁] × {R₂}` of its boundary. Let `ρ : ℝ → ℝ → ℝ` be a family of
functions such that at each point of `Q`, `ρ ℓ` is `C²` and satisfies the criterion over `R` at
`R`, with value and first two `R`-derivatives continuous in `(ℓ, R)` on `Q`; such that
`ρ ℓ₁ R < ρ ℓ R` for `ℓ ∈ [ℓ₀, ℓ₁)` and `R ∈ [R₁, R₂]`; and such that on a neighbourhood `U`
of `E` the family is smooth in `(ℓ, R)` with `∂ρ/∂ℓ < 0`. Then there is a family `ψ`, smooth in
`(ℓ, R)` on `Q`, whose members satisfy the criterion over `R` with `∂ψ/∂ℓ < 0` at each point of
`Q`, and which equals `ρ` on a neighbourhood of `E`.

This is `SymplecticGeometry.exists_shapeFoliation` for curves `r = ρ ℓ R`: over `R` the leaves
rise as `ρ` falls, so the family decreases in `ℓ` and ends on its lowest member. -/
theorem exists_shapeFoliation_overR {ρ : ℝ → ℝ → ℝ} {ℓ₀ ℓ₁ R₁ R₂ : ℝ} {U : Set (ℝ × ℝ)}
    (hℓ : ℓ₀ < ℓ₁) (hR : R₁ < R₂)
    (hC2 : ∀ x ∈ Icc ℓ₀ ℓ₁ ×ˢ Icc R₁ R₂, ContDiffAt ℝ 2 (ρ x.1) x.2)
    (hc : ∀ x ∈ Icc ℓ₀ ℓ₁ ×ˢ Icc R₁ R₂, IsConvexShapeOverRAt (ρ x.1) x.2)
    (hcont : ∀ k ≤ 2, ContinuousOn (fun x : ℝ × ℝ ↦ iteratedDeriv k (ρ x.1) x.2)
      (Icc ℓ₀ ℓ₁ ×ˢ Icc R₁ R₂))
    (htop : ∀ ℓ ∈ Ico ℓ₀ ℓ₁, ∀ R ∈ Icc R₁ R₂, ρ ℓ₁ R < ρ ℓ R)
    (hU : U ∈ 𝓝ˢ ({ℓ₀, ℓ₁} ×ˢ Icc R₁ R₂ ∪ Icc ℓ₀ ℓ₁ ×ˢ {R₂}))
    (hsmooth : ContDiffOn ℝ ∞ (Function.uncurry ρ) U)
    (hmono : ∀ x ∈ U, deriv (fun ℓ' ↦ ρ ℓ' x.2) x.1 < 0) :
    ∃ ψ : ℝ → ℝ → ℝ, ContDiffOn ℝ ∞ (Function.uncurry ψ) (Icc ℓ₀ ℓ₁ ×ˢ Icc R₁ R₂) ∧
      (∀ x ∈ Icc ℓ₀ ℓ₁ ×ˢ Icc R₁ R₂, IsConvexShapeOverRAt (ψ x.1) x.2) ∧
      (∀ x ∈ Icc ℓ₀ ℓ₁ ×ˢ Icc R₁ R₂, deriv (fun ℓ' ↦ ψ ℓ' x.2) x.1 < 0) ∧
      Function.uncurry ψ =ᶠ[𝓝ˢ ({ℓ₀, ℓ₁} ×ˢ Icc R₁ R₂ ∪ Icc ℓ₀ ℓ₁ ×ˢ {R₂})]
        Function.uncurry ρ := by
  set Q := Icc ℓ₀ ℓ₁ ×ˢ Icc R₁ R₂
  set E := ({ℓ₀, ℓ₁} : Set ℝ) ×ˢ Icc R₁ R₂ ∪ Icc ℓ₀ ℓ₁ ×ˢ {R₂}
  have hR₁ : 0 < R₁ := (hc (ℓ₀, R₁) ⟨left_mem_Icc.2 hℓ.le, left_mem_Icc.2 hR.le⟩).pos
  -- An open `U'` around `E`, and a thickening of `E` of size `d` inside it.
  obtain ⟨U', hU'o, hEU', hU'U⟩ := mem_nhdsSet_iff_exists.1 hU
  have hsm' : ContDiffOn ℝ ∞ (Function.uncurry ρ) U' := hsmooth.mono hU'U
  have hmono' : ∀ x ∈ U', deriv (fun ℓ' ↦ ρ ℓ' x.2) x.1 < 0 := fun x hx ↦ hmono x (hU'U hx)
  have hEc : IsCompact E :=
    ((Set.toFinite _).isCompact.prod isCompact_Icc).union (isCompact_Icc.prod isCompact_singleton)
  obtain ⟨d, hd, hdU⟩ := hEc.exists_cthickening_subset_open hU'o hEU'
  have hnear : ∀ x y : ℝ × ℝ, y ∈ E → |x.1 - y.1| ≤ d → |x.2 - y.2| ≤ d → x ∈ U' :=
    fun x y hy h₁ h₂ ↦ hdU (Metric.mem_cthickening_of_dist_le x y d E hy (by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      exact max_le h₁ h₂))
  -- The band `[ℓ₀, ℓ₁] × [R₃, R₂]` inside `U'`, and the cutoff `β` and tolerance `τ` of the
  -- blend there.
  set R₃ := max R₁ (R₂ - d)
  have hR₁₃ : R₁ ≤ R₃ := le_max_left _ _
  have hR₃₂ : R₃ < R₂ := max_lt hR (by linarith)
  have hBQ : Icc ℓ₀ ℓ₁ ×ˢ Icc R₃ R₂ ⊆ Q := fun x hx ↦ ⟨hx.1, hR₁₃.trans hx.2.1, hx.2.2⟩
  have hBU : Icc ℓ₀ ℓ₁ ×ˢ Icc R₃ R₂ ⊆ U' := fun x hx ↦
    hnear x (x.1, R₂) (Or.inr ⟨hx.1, rfl⟩) (by simp [hd.le]) (by
      rw [abs_le]
      constructor <;> linarith [hx.2.1, hx.2.2, le_max_right R₁ (R₂ - d)])
  obtain ⟨β, -, -, -, hβ0, τ, hτ, hblend⟩ := exists_blend_shapeFamilyOverR (R₁ := R₁) hR₃₂
    hU'o hBU hsm' (fun x hx ↦ hc x (hBQ hx)) fun x hx ↦ hmono' x (hBU hx)
  -- A step `w` in `ℓ` over which the value and first two `R`-derivatives of `ρ` move by less
  -- than `τ / 4`.
  obtain ⟨w, hw, hu⟩ := isCompact_Icc.exists_pos_abs_iteratedDeriv_sub_lt_of_continuousOn
    (n := 2) hcont (by positivity : 0 < τ / 4)
  -- The inner ends `a = ℓ₀ + s`, `b = ℓ₁ - s` of the pieces next to `ℓ₀` and `ℓ₁`.
  set s := min (min d w) ((ℓ₁ - ℓ₀) / 3)
  have hs0 : 0 < s := by
    have := sub_pos.2 hℓ
    positivity
  have hsd : s ≤ d := (min_le_left _ _).trans (min_le_left _ _)
  have hsw : s ≤ w := (min_le_left _ _).trans (min_le_right _ _)
  have hs3 : s ≤ (ℓ₁ - ℓ₀) / 3 := min_le_right _ _
  set a := ℓ₀ + s
  set b := ℓ₁ - s
  have hℓa : ℓ₀ < a := by linarith
  have hab : a < b := by linarith
  have hbℓ : b < ℓ₁ := by linarith
  have hLQ : Icc ℓ₀ a ⊆ Icc ℓ₀ ℓ₁ := Icc_subset_Icc_right (by linarith)
  have hMQ : Icc a b ⊆ Icc ℓ₀ ℓ₁ := Icc_subset_Icc (by linarith) (by linarith)
  have hRQ : Icc b ℓ₁ ⊆ Icc ℓ₀ ℓ₁ := Icc_subset_Icc_left (by linarith)
  have hLU : Icc ℓ₀ a ×ˢ Icc R₁ R₂ ⊆ U' := fun x hx ↦
    hnear x (ℓ₀, x.2) (Or.inl ⟨Or.inl rfl, hx.2⟩) (by
      rw [abs_le]
      constructor <;> linarith [hx.1.1, hx.1.2]) (by simp [hd.le])
  have hRU : Icc b ℓ₁ ×ˢ Icc R₁ R₂ ⊆ U' := fun x hx ↦
    hnear x (ℓ₁, x.2) (Or.inl ⟨Or.inr rfl, hx.2⟩) (by
      rw [abs_le]
      constructor <;> linarith [hx.1.1, hx.1.2]) (by simp [hd.le])
  -- A positive lower bound `μ` of `ρ` on `Q`, below which the lowerings stay.
  have hρcont : ContinuousOn (fun x : ℝ × ℝ ↦ ρ x.1 x.2) Q := by
    simpa [iteratedDeriv_zero] using hcont 0 (by norm_num)
  obtain ⟨μ, hμ, hμQ⟩ := (isCompact_Icc.prod isCompact_Icc).exists_forall_le' hρcont
    fun x hx ↦ (hc x hx).pos_value
  -- The gap `g` between the members over `[a, b]` and `ρ ℓ₁`.
  obtain ⟨g, hg, hgap⟩ : ∃ g > 0, ∀ ℓ ∈ Icc a b, ∀ R ∈ Icc R₁ R₂, ρ ℓ₁ R + g ≤ ρ ℓ R := by
    have hcf : ContinuousOn (fun x : ℝ × ℝ ↦ ρ x.1 x.2 - ρ ℓ₁ x.2) (Icc a b ×ˢ Icc R₁ R₂) := by
      refine ContinuousOn.sub (hρcont.mono fun x hx ↦ ⟨hMQ hx.1, hx.2⟩) ?_
      exact hρcont.comp (continuous_const.prodMk continuous_snd).continuousOn
        fun x hx ↦ ⟨right_mem_Icc.2 hℓ.le, hx.2⟩
    obtain ⟨g, hg, hgK⟩ := (isCompact_Icc.prod isCompact_Icc).exists_forall_le' hcf
      fun x hx ↦ sub_pos.2 (htop x.1 ⟨(hMQ hx.1).1, by linarith [hx.1.2]⟩ x.2 hx.2)
    exact ⟨g, hg, fun ℓ hℓ' R hR' ↦ by linarith [hgK (ℓ, R) ⟨hℓ', hR'⟩]⟩
  -- The point `c ∈ (b, ℓ₁)` from which on the members are within `g / 4` of `ρ ℓ₁`.
  obtain ⟨w', hw', hu'⟩ := isCompact_Icc.exists_pos_abs_sub_lt_of_continuousOn
    (hcont 0 (by norm_num)) (by positivity : 0 < g / 4)
  set c := ℓ₁ - min w' (s / 2)
  have hbc : b < c := by
    have : min w' (s / 2) ≤ s / 2 := min_le_right _ _
    linarith
  have hcℓ : c < ℓ₁ := by
    have : 0 < min w' (s / 2) := by positivity
    linarith
  have hnearℓ₁ : ∀ ℓ ∈ Icc c ℓ₁, ∀ R ∈ Icc R₁ R₂, ρ ℓ R < ρ ℓ₁ R + g / 4 := by
    intro ℓ hℓ' R hR'
    have := hu' R hR' ℓ₁ (right_mem_Icc.2 hℓ.le) ℓ ⟨by linarith [hℓ'.1], hℓ'.2⟩ (by
      rw [abs_le]
      constructor <;> linarith [hℓ'.1, hℓ'.2, min_le_left w' (s / 2)])
    simp only [iteratedDeriv_zero] at this
    linarith [(abs_lt.1 this).2]
  -- The lowering `q`, a smooth step from `0` at `a₀ = ℓ₀ + s / 4` to `κ` at `c`.
  set κ := min (min (τ / 4) (g / 4)) (μ / 2)
  have hκ0 : 0 < κ := by positivity
  have hκτ : κ ≤ τ / 4 := (min_le_left _ _).trans (min_le_left _ _)
  have hκg : κ ≤ g / 4 := (min_le_left _ _).trans (min_le_right _ _)
  have hκμ : κ ≤ μ / 2 := min_le_right _ _
  set a₀ := ℓ₀ + s / 4 with ha₀
  have ha₀c : a₀ < c := by linarith
  obtain ⟨q, hq, hqm, hqI, hqa₀, -, hqpos, hq'⟩ :=
    Real.exists_contDiff_monotone_eqOn_zero_Iic_deriv_pos_Ioo ha₀c hκ0
  have hq0 : ∀ ℓ, 0 ≤ q ℓ := fun ℓ ↦ (hqI ℓ).1
  have hqκ : ∀ ℓ, q ℓ ≤ κ := fun ℓ ↦ (hqI ℓ).2
  have hq₀ : q =ᶠ[𝓝 ℓ₀] fun _ ↦ 0 :=
    eventuallyEq_of_mem (Iic_mem_nhds (show ℓ₀ < a₀ by linarith)) hqa₀
  have hqb : 0 < q b := hqpos b (by linarith)
  -- The chain over `[a, b]`, with error `ε` in its end.
  set ε := min (min (q b / 2) (g / 4)) (μ / 4)
  have hε0 : 0 < ε := by positivity
  have hεq : ε < q b := ((min_le_left _ _).trans (min_le_left _ _)).trans_lt (by linarith)
  have hεg : ε ≤ g / 4 := (min_le_left _ _).trans (min_le_right _ _)
  have hεμ : ε ≤ μ / 4 := min_le_right _ _
  have hab' : ∀ x ∈ Icc a b ×ˢ Icc R₁ R₂, x ∈ Q := fun x hx ↦ ⟨hMQ hx.1, hx.2⟩
  obtain ⟨C, hCs, hCc, hCℓ, ⟨hCa, hCaρ⟩, hCb, hCblow, hCbup, hCclose⟩ :=
    exists_antitone_shapeChain_overR (τ := τ / 4) hR₁ hab hR₁₃ (fun x hx ↦ hC2 x (hab' x hx))
      (fun x hx ↦ hc x (hab' x hx))
      (fun k hk ↦ (hcont k hk).mono fun x hx ↦ hab' x hx) hU'o
      (union_subset (fun x hx ↦ hLU ⟨by rw [hx.1]; exact right_mem_Icc.2 hℓa.le, hx.2⟩)
        fun x hx ↦ hBU ⟨hMQ hx.1, hx.2⟩) hsm'
      (fun x hx ↦ hmono' x (hBU ⟨hMQ hx.1, hx.2⟩)) (by positivity) hε0
  -- The chain decreases in `ℓ`, so it stays above `μ - ε` on `[a, b]`.
  have hClow : ∀ ℓ ∈ Icc a b, ∀ R ∈ Icc R₁ R₂, μ - ε ≤ C ℓ R := by
    intro ℓ hℓ' R hR'
    have hCR : ContDiff ℝ ∞ fun ℓ ↦ C ℓ R := hCs.comp (contDiff_id.prodMk contDiff_const)
    have hanti : AntitoneOn (fun ℓ ↦ C ℓ R) (Icc a b) :=
      antitoneOn_of_deriv_nonpos (convex_Icc a b) hCR.continuous.continuousOn
        (hCR.differentiable (by simp)).differentiableOn
        fun ℓ hℓ'' ↦ hCℓ (ℓ, R) ⟨interior_subset hℓ'', hR'⟩
    obtain ⟨ℓ', hℓ'm, hle⟩ := hCblow R hR'
    have h₁ := hanti hℓ' (right_mem_Icc.2 hab.le) hℓ'.2
    have h₂ := hμQ (ℓ', R) ⟨hMQ hℓ'm, hR'⟩
    simp only at h₁ h₂
    linarith
  -- The piece next to `ℓ₀`.
  obtain ⟨T₀, hT₀s, hT₀c, hT₀ℓ, hT₀ℓ₀, hT₀a, hT₀m⟩ :=
    exists_comp_sub_shapeFamilyOverR (a₁ := ℓ₀ + s / 2) (by linarith) (by linarith) hU'o hLU
      hsm' (fun x hx ↦ hc x ⟨hLQ hx.1, hx.2⟩) (fun x hx ↦ hmono' x (hLU hx)) hq hqm hq₀
      (fun ℓ hℓ' ↦ hq' ℓ ⟨by linarith [hℓ'.1], by linarith [hℓ'.2]⟩)
      fun x hx ↦ by linarith [hqκ a, hμQ x ⟨hLQ hx.1, hx.2⟩]
  -- The piece next to `ℓ₁`, below `C b`.
  have hCbs : ContDiff ℝ ∞ (C b) := hCs.comp (contDiff_const.prodMk contDiff_id)
  obtain ⟨δ, ⟨-, hδτ⟩, T₁, hT₁s, hT₁c, hT₁ℓ, hT₁b, hT₁ℓ₁, hT₁m⟩ :=
    exists_smoothedMin_shapeFamilyOverR (ε := τ / 4) hbc hcℓ.le hU'o hRU hsm'
      (fun x hx ↦ hc x ⟨hRQ hx.1, hx.2⟩) (fun x hx ↦ hmono' x (hRU hx)) hCbs
      (fun R hR' ↦ hCc (b, R) ⟨right_mem_Icc.2 hab.le, hR'⟩) hq hqm (hq0 b)
      (fun R hR' ↦ by linarith [hqκ ℓ₁, hClow b (right_mem_Icc.2 hab.le) R hR'])
      (fun ℓ hℓ' ↦ hq' ℓ ⟨by linarith [hℓ'.1], hℓ'.2⟩)
      (fun R hR' ↦ by linarith [hCbup R hR'])
      (fun ℓ hℓ' R hR' ↦ by
        obtain ⟨ℓ', hℓ'm, hle⟩ := hCblow R hR'
        linarith [hgap ℓ' hℓ'm R hR', hnearℓ₁ ℓ hℓ' R hR', hqκ ℓ])
      (by positivity)
  -- The middle piece `C ℓ - q ℓ`, and the gluing of the three pieces along `ℓ = a` and `ℓ = b`.
  set Cq : ℝ → ℝ → ℝ := fun ℓ R ↦ C ℓ R - q ℓ with hCq
  have hCqs : ContDiff ℝ ∞ (Function.uncurry Cq) := hCs.sub (hq.comp contDiff_fst)
  have hTa : ∀ R ∈ Icc R₁ R₂, Function.uncurry T₀ =ᶠ[𝓝 (a, R)] Function.uncurry Cq := by
    intro R hR'
    filter_upwards [hT₀a.filter_mono (nhds_le_nhdsSet (show (a, R) ∈ ({a} : Set ℝ) ×ˢ Icc R₁ R₂
        from ⟨rfl, hR'⟩)), (continuous_fst.tendsto (a, R)).eventually hCa,
      (continuous_snd.tendsto (a, R)).eventually (hCaρ.filter_mono (nhds_le_nhdsSet hR'))]
      with y hy1 hy2 hy3
    simp only [Function.uncurry_def, hCq] at hy1 ⊢
    rw [hy1, hy2, hy3]
  have hTb : ∀ R ∈ Icc R₁ R₂, Function.uncurry T₁ =ᶠ[𝓝 (b, R)] Function.uncurry Cq := by
    intro R hR'
    filter_upwards [hT₁b.filter_mono (nhds_le_nhdsSet (show (b, R) ∈ ({b} : Set ℝ) ×ˢ Icc R₁ R₂
        from ⟨rfl, hR'⟩)), (continuous_fst.tendsto (b, R)).eventually hCb] with y hy1 hy2
    simp only [Function.uncurry_def, hCq] at hy1 ⊢
    rw [hy1, hy2]
  obtain ⟨ψ', hψ's, hψ'₀, hψ'm, hψ'₁⟩ := exists_contDiff_eventuallyEq_of_eventuallyEq_Icc
    (ℓ₀ := ℓ₀) (ℓ₁ := ℓ₁) hab isCompact_Icc hT₀s hCqs hT₁s hTa hTb
  -- Near each point of `Q`, `ψ'` is the piece of its interval in `ℓ`.
  have hloc' : ∀ x ∈ Q,
      (x.1 ∈ Icc ℓ₀ a ∧ Function.uncurry ψ' =ᶠ[𝓝 x] Function.uncurry T₀) ∨
      (x.1 ∈ Icc a b ∧ Function.uncurry ψ' =ᶠ[𝓝 x] Function.uncurry Cq) ∨
      (x.1 ∈ Icc b ℓ₁ ∧ Function.uncurry ψ' =ᶠ[𝓝 x] Function.uncurry T₁) := by
    intro x hx
    rcases le_or_gt x.1 a with h | h
    · exact Or.inl ⟨⟨hx.1.1, h⟩, hψ'₀.filter_mono (nhds_le_nhdsSet ⟨⟨hx.1.1, h⟩, hx.2⟩)⟩
    rcases le_or_gt x.1 b with h' | h'
    · exact Or.inr (Or.inl ⟨⟨h.le, h'⟩, hψ'm.filter_mono (nhds_le_nhdsSet ⟨⟨h.le, h'⟩, hx.2⟩)⟩)
    · exact Or.inr (Or.inr ⟨⟨h'.le, hx.1.2⟩,
        hψ'₁.filter_mono (nhds_le_nhdsSet ⟨⟨h'.le, hx.1.2⟩, hx.2⟩)⟩)
  -- The members of `ψ'` satisfy the criterion over `R` and have negative `ℓ`-derivative.
  have hψ'c : ∀ x ∈ Q, IsConvexShapeOverRAt (ψ' x.1) x.2 := by
    intro x hx
    rcases hloc' x hx with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact (hT₀c x ⟨h1, hx.2⟩).congr_of_eventuallyEq h2.uncurry_left
    · exact ((hCc x ⟨h1, hx.2⟩).sub_const (hq0 x.1)
        (by linarith [hqκ x.1, hClow x.1 h1 x.2 hx.2])).congr_of_eventuallyEq h2.uncurry_left
    · exact (hT₁c x ⟨h1, hx.2⟩).congr_of_eventuallyEq h2.uncurry_left
  have hψ'ℓ : ∀ x ∈ Q, deriv (fun ℓ ↦ ψ' ℓ x.2) x.1 < 0 := by
    intro x hx
    rcases hloc' x hx with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h2.uncurry_right.deriv_eq]
      exact hT₀ℓ x ⟨h1, hx.2⟩
    · rw [h2.uncurry_right.deriv_eq]
      have hCd : DifferentiableAt ℝ (fun ℓ ↦ C ℓ x.2) x.1 :=
        ((hCs.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp)) x.1
      have hqd : DifferentiableAt ℝ q x.1 := (hq.differentiable (by simp)) x.1
      simp only [hCq]
      rw [deriv_fun_sub hCd hqd]
      linarith [hCℓ x ⟨h1, hx.2⟩, hq' x.1 ⟨by linarith [h1.1], by linarith [h1.2]⟩]
    · rw [h2.uncurry_right.deriv_eq]
      exact hT₁ℓ x ⟨h1, hx.2⟩
  -- On the band, `ψ'` is close to `ρ`: each piece is close to members of `ρ` at most `s` away
  -- in `ℓ`, or to the chain, which is close to `ρ`. The estimates over `r` apply to the
  -- negated functions.
  have hclose : ∀ x ∈ Icc ℓ₀ ℓ₁ ×ˢ Icc R₃ R₂, |ψ' x.1 x.2 - ρ x.1 x.2| < τ ∧
      |deriv (ψ' x.1) x.2 - deriv (ρ x.1) x.2| < τ ∧
      iteratedDeriv 2 (ψ' x.1) x.2 < iteratedDeriv 2 (ρ x.1) x.2 + τ := by
    intro x hx
    have hR' : x.2 ∈ Icc R₁ R₂ := (hBQ hx).2
    have hstep : ∀ ℓ ∈ Icc ℓ₀ ℓ₁, ℓ ∈ Icc (x.1 - s) (x.1 + s) → ∀ k ≤ 2,
        |iteratedDeriv k (ρ ℓ) x.2 - iteratedDeriv k (ρ x.1) x.2| < τ / 4 :=
      fun ℓ hℓ' hl k hk ↦ hu k hk x.2 hR' x.1 hx.1 ℓ hℓ'
        ((abs_sub_le_iff.2 ⟨by linarith [hl.2], by linarith [hl.1]⟩).trans hsw)
    rcases hloc' x (hBQ hx) with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain ⟨ℓ', hℓ'm, hT⟩ := hT₀m x ⟨h1, hR'⟩
      refine abs_sub_lt_of_neg (abs_sub_lt_of_eventuallyEq_add_const (τ := τ) (c := q x.1)
        (f := fun R ↦ -ψ' x.1 R) (g := fun R ↦ -ρ ℓ' R)
        ((h2.uncurry_left.trans hT).mono fun R hR ↦ ?_) (hq0 x.1)
        (by linarith [hqκ x.1]) (abs_iteratedDeriv_neg_sub_neg_lt fun k hk ↦
          (hstep ℓ' (hLQ hℓ'm) ⟨by linarith [h1.2, hℓ'm.1], by linarith [h1.1, hℓ'm.2]⟩
            k hk).trans (by linarith)))
      simp only at hR ⊢
      rw [hR]
      ring
    · refine abs_sub_lt_of_neg (abs_sub_lt_of_eventuallyEq_add_const (τ := τ) (c := q x.1)
        (f := fun R ↦ -ψ' x.1 R) (g := fun R ↦ -C x.1 R)
        (h2.uncurry_left.mono fun R hR ↦ ?_) (hq0 x.1)
        (by linarith [hqκ x.1]) (abs_iteratedDeriv_neg_sub_neg_lt fun k hk ↦
          (hCclose x ⟨h1, hx.2⟩ k hk).trans (by linarith)))
      simp only [hCq] at hR ⊢
      rw [hR]
      ring
    · obtain ⟨ℓ', hℓ'm, -, hv₁, hv₂, hd₁, hd₂, hdd⟩ := hT₁m x ⟨h1, hR'⟩
      rw [h2.uncurry_left.eq_of_nhds, h2.uncurry_left.deriv_eq,
        h2.uncurry_left.iteratedDeriv_eq 2]
      have hCbx : ∀ k ≤ 2, |iteratedDeriv k (C b) x.2 - iteratedDeriv k (ρ x.1) x.2| < τ / 2 := by
        intro k hk
        have hCb : |iteratedDeriv k (C b) x.2 - iteratedDeriv k (ρ b) x.2| < τ / 4 :=
          hCclose (b, x.2) ⟨⟨hab.le, le_rfl⟩, hx.2⟩ k hk
        have hρb := hstep b (hRQ ⟨le_rfl, hbℓ.le⟩) ⟨by linarith [h1.2], by linarith [h1.1]⟩ k hk
        exact (abs_sub_le _ (iteratedDeriv k (ρ b) x.2) _).trans_lt (by linarith)
      have hρx : ∀ k ≤ 2, |iteratedDeriv k (ρ ℓ') x.2 - iteratedDeriv k (ρ x.1) x.2| < τ / 2 :=
        fun k hk ↦ (hstep ℓ' (hRQ hℓ'm) ⟨by linarith [h1.2, hℓ'm.1], by linarith [h1.1, hℓ'm.2]⟩
          k hk).trans (by linarith)
      have hneg : -C b x.2 + q x.1 = -(C b x.2 - q x.1) := by ring
      refine abs_sub_lt_of_neg (abs_sub_lt_of_max_le_of_le_max (τ := τ)
        (f := fun R ↦ -T₁ x.1 R) (M := fun R ↦ -C b R)
        (g := fun R ↦ -ρ ℓ' R) (c := q x.1) (δ := δ) (hqκ x.1 |>.trans hκτ) (by linarith)
        (abs_iteratedDeriv_neg_sub_neg_lt hCbx) (abs_iteratedDeriv_neg_sub_neg_lt hρx)
        ?_ ?_ ?_ ?_ ?_)
      · rw [hneg, max_neg_neg]
        linarith
      · rw [hneg, max_neg_neg]
        linarith
      · rw [deriv.fun_neg, deriv.fun_neg, deriv.fun_neg, min_neg_neg]
        exact neg_le_neg hd₂
      · rw [deriv.fun_neg, deriv.fun_neg, deriv.fun_neg, max_neg_neg]
        exact neg_le_neg hd₁
      · rw [iteratedDeriv_fun_neg, iteratedDeriv_fun_neg, iteratedDeriv_fun_neg, min_neg_neg]
        exact neg_le_neg hdd
  -- The blend with `ρ` near `R₂`; it is `ρ` near `{ℓ₀, ℓ₁} × [R₁, R₂]`, where `ψ'` is.
  obtain ⟨hψs, hψc, hψℓ⟩ := hblend ψ' hψ's hψ'c hψ'ℓ hclose
  refine ⟨fun ℓ R ↦ β R * ψ' ℓ R + (1 - β R) * ρ ℓ R, hψs.mono fun x hx ↦ ?_, hψc, hψℓ,
    blend_eventuallyEq_nhdsSet_union ?_ hβ0⟩
  · rcases lt_or_ge x.2 R₃ with h | h
    · exact Or.inl ⟨mem_univ _, h⟩
    · exact Or.inr (hBU ⟨hx.1, h, hx.2.2⟩)
  rw [insert_eq, union_prod, EventuallyEq, nhdsSet_union, eventually_sup]
  exact ⟨((hψ'₀.filter_mono (nhdsSet_mono (prod_mono (singleton_subset_iff.2
      ⟨le_rfl, hℓa.le⟩) le_rfl))).trans hT₀ℓ₀),
    ((hψ'₁.filter_mono (nhdsSet_mono (prod_mono (singleton_subset_iff.2
      ⟨hbℓ.le, le_rfl⟩) le_rfl))).trans hT₁ℓ₁)⟩

end SymplecticGeometry
