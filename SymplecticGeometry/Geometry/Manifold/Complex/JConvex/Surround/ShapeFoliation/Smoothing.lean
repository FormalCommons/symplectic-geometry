/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Analysis.SpecialFunctions.SmoothedMax
public import SymplecticGeometry.Geometry.Manifold.Complex.JConvex.Surround.ConvexShape.Basic

import TauCeti.Analysis.Calculus.ContDiff.Prod
import SymplecticGeometry.Analysis.Calculus.BumpFunction.Gluing
import SymplecticGeometry.Analysis.Calculus.BumpFunction.FiniteDimension
import SymplecticGeometry.Analysis.Calculus.Deriv.Mul
import SymplecticGeometry.Analysis.Calculus.Deriv.Prod
import SymplecticGeometry.Analysis.Calculus.IteratedDeriv.Lemmas
import SymplecticGeometry.Analysis.Calculus.IteratedDeriv.Prod
import SymplecticGeometry.Analysis.SpecialFunctions.SmoothTransition.Basic
import SymplecticGeometry.Analysis.Calculus.Deriv.Rectangle
import SymplecticGeometry.Geometry.Manifold.Complex.JConvex.Surround.ConvexShape.SmoothedMax
import SymplecticGeometry.Geometry.Manifold.Complex.JConvex.Surround.ShapeFoliation.Chain
import SymplecticGeometry.Topology.Constructions.SumProd

/-!
# Smooth, strictly increasing families of `i`-convex shapes

This file is for the last step of the construction of a family of `i`-convex shapes
`R = T ℓ r`, smooth in `(ℓ, r)` and with positive derivative in `ℓ`, out of a family that is
only weakly increasing in `ℓ` (`SymplecticGeometry.exists_monotone_shapeChain`).

* `SymplecticGeometry.exists_smoothedMax_shapeFamily`: the piece next to the end `ℓ₁` of the
  parameter interval `[b, ℓ₁]`. A smooth family `χ` of shapes with `∂χ/∂ℓ > 0` is joined to the
  family `M + q ℓ`, a fixed shape `M` raised by a smooth nondecreasing `q` with `q' > 0` on
  `[b, c)`, by `T ℓ r = smoothedMax δ (M r + q ℓ) (χ (λ ℓ) r)`. Here `λ` is Tau Ceti's smooth
  lower truncation `TauCeti.smoothLowerTruncation b b'`, `b < b' < c`, which is `b` up to `b`,
  the identity from `b'` on, and has positive derivative on `(b, ∞)`
  (`TauCeti.deriv_smoothLowerTruncation_pos`). The `ℓ`-derivative of `T` is a weighted
  combination of `q' ≥ 0` and `∂χ/∂ℓ · λ' ≥ 0` in which the larger of the two arguments has
  weight at least `1 / 2` (`SymplecticGeometry.deriv_smoothedMax_pos_left`,
  `SymplecticGeometry.deriv_smoothedMax_pos_right`). It is positive: on `[b, c)` because
  `q' > 0` there, and `χ` is the larger only away from `b` (by the gap `χ b < M + q b`), where
  `λ' > 0`; on `[c, ℓ₁]` because there `χ ℓ > M + q ℓ` and `λ' > 0`. The family is `M + q ℓ`
  near `ℓ = b` and `χ` near `ℓ = ℓ₁`, and at each point it is the smoothed maximum of `M + q ℓ`
  and a member of `χ`, which bounds its value and its first two `r`-derivatives by theirs. All of
  this holds without a convexity criterion, and is stated as
  `SymplecticGeometry.exists_smoothedMax_family`. For small `δ` the members are `i`-convex shapes
  by `SymplecticGeometry.exists_forall_isConvexShapeAt_smoothedMax`, applied to the pairs
  `(M + q ℓ, χ ℓ')` with `ℓ, ℓ' ∈ [b, ℓ₁]`.
* `SymplecticGeometry.exists_comp_add_shapeFamily`: the piece next to the end `ℓ₀` of the
  parameter interval `[ℓ₀, a]`. It is `T ℓ r = χ (λ ℓ) r + q ℓ`, where `q` is smooth,
  nondecreasing, `0` near `ℓ₀` and with `q' > 0` on `[a₁, a]`, and `λ` is a smooth monotone map
  that is the identity up to a point of `(ℓ₀, a₁)`, equal to `a` from a point `a'' ∈ (a₁, a)`
  on, and with positive derivative below `a''`
  (`Real.exists_contDiff_monotone_eqOn_id_Iic_eqOn_const_Ici`). The `ℓ`-derivative
  `∂χ/∂ℓ (λ ℓ) · λ' ℓ + q' ℓ` is positive, by its first term below `a''` and by its second on
  `[a'', a]`. The family is `χ` near `ℓ = ℓ₀` and `χ a + q ℓ` near `ℓ = a`, where it meets the
  family of `SymplecticGeometry.exists_monotone_shapeChain`; these facts, which do not involve
  a convexity criterion, are `SymplecticGeometry.exists_comp_add_family`. The members are shapes
  by `SymplecticGeometry.IsConvexShapeAt.add_const`, since `q ≥ 0` on `[ℓ₀, ∞)`.
* `SymplecticGeometry.exists_blend_shapeFamily`: the blend with `χ` near the end `r₂` of the
  `r`-interval. On a band `[ℓ₀, ℓ₁] × [r₃, r₂]` where `χ` is a smooth family of shapes with
  `∂χ/∂ℓ > 0`, a cutoff `ρ` in `r`, `1` up to `r₃` and `0` near `r₂`
  (`SymplecticGeometry.exists_contDiff_antitone_cutoff_mul_abs_deriv_le_deriv_deriv`), and a
  tolerance `τ > 0` are chosen first. Then any smooth family
  `ψ₀` of shapes with `∂ψ₀/∂ℓ > 0` that is `τ`-close to `χ` on the band, in value and first
  `r`-derivative and from below in second `r`-derivative, gives the family
  `ρ r * ψ₀ ℓ r + (1 - ρ r) * χ ℓ r`. Its members are shapes by the one-sided blend lemma of
  `ConvexShape/Basic.lean`, its `ℓ`-derivative is a convex combination of `∂ψ₀/∂ℓ` and `∂χ/∂ℓ`,
  and it is smooth below `r₃` and where `χ` is (`SymplecticGeometry.contDiffOn_blend`).
* `SymplecticGeometry.abs_sub_lt_of_eventuallyEq_add_const` and
  `SymplecticGeometry.abs_sub_lt_of_max_le_of_le_max`: a function that is locally `g + c`, or
  that is bounded as a smoothed maximum of `M + c` and `g` is, is close to `h` in the sense
  that `SymplecticGeometry.exists_blend_shapeFamily` asks for, when `g` and `M` are close to `h`
  in value and first two derivatives and `c` is small. These are the estimates for the pieces
  next to `ℓ₀` and in the middle, and for the piece next to `ℓ₁`.
* `SymplecticGeometry.blend_eventuallyEq_nhdsSet_union`: the blend
  `ρ r * ψ ℓ r + (1 - ρ r) * χ ℓ r` is `χ` near every set where `ψ` is `χ`, and near every
  set in `r = r₂` when `ρ` vanishes near `r₂`.
* `SymplecticGeometry.exists_shapeFoliation`: the assembly. Given a family `χ` on
  `Q = [ℓ₀, ℓ₁] × [r₁, r₂]` that is smooth with `∂χ/∂ℓ > 0` near the part
  `E = {ℓ₀, ℓ₁} × [r₁, r₂] ∪ [ℓ₀, ℓ₁] × {r₂}` of the boundary and whose members lie below
  `χ ℓ₁`, it gives a family smooth on `Q`, of shapes with positive `ℓ`-derivative, equal to `χ`
  near `E`. The constants are chosen in this order: a band `[r₃, r₂]` and the cutoff and tolerance
  `τ` of `SymplecticGeometry.exists_blend_shapeFamily` there; the ends `a = ℓ₀ + s`,
  `b = ℓ₁ - s`, with `s` so small that `χ` and its first two `r`-derivatives move by less than
  `τ / 4` over a step `s` in `ℓ`; the gap `g` between `χ ℓ₁` and the members over `[a, b]`, and a
  point `c ∈ (b, ℓ₁)` after which the members are within `g / 4` of `χ ℓ₁`; the raise `q`, a
  smooth step from `0` to `κ ≤ min (τ / 4) (g / 4)` that rises on `(ℓ₀ + s / 4, c)`
  (`Real.exists_contDiff_monotone_eqOn_zero_Iic_deriv_pos_Ioo`); and last the error `ε < q b` of
  the chain. The family
  is the piece of `SymplecticGeometry.exists_comp_add_shapeFamily` on `[ℓ₀, a]`, `C ℓ + q ℓ` with
  `C` from `SymplecticGeometry.exists_monotone_shapeChain` on `[a, b]`, and the piece of
  `SymplecticGeometry.exists_smoothedMax_shapeFamily` on top of `C b` on `[b, ℓ₁]`; these agree
  near the joints, and are glued to a smooth family on `ℝ²` that is each of them near its
  rectangle (`SymplecticGeometry.exists_contDiff_eventuallyEq_of_eventuallyEq_Icc`). The result
  is blended with `χ` near `r₂`.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Proposition 3.25 and Corollary 4.29.
-/

public section

noncomputable section

namespace SymplecticGeometry

open Set Filter Topology
open scoped ContDiff

/-- **Joining a strictly increasing family to a raised function by a smoothed maximum.** Let
`χ : ℝ → ℝ → ℝ` be smooth in `(ℓ, r)` on an open set containing `[b, ℓ₁] × [r₁, r₂]`, with
`∂χ/∂ℓ > 0` at each point of the rectangle. Let `M` be a smooth function and `q` a smooth
nondecreasing function with `q' > 0` on `[b, c)`, where `b < c ≤ ℓ₁`. Suppose that
`χ b < M + q b` and that `M + q ℓ < χ ℓ` for `ℓ ∈ [c, ℓ₁]`, on `[r₁, r₂]`. Then for each
`ε > 0` there are `δ ∈ (0, ε]` and `T : ℝ → ℝ → ℝ`, smooth on `ℝ²`, such that `∂T/∂ℓ > 0` on
the rectangle; `T` equals `M r + q ℓ` near `{b} × [r₁, r₂]` and `χ` near `{ℓ₁} × [r₁, r₂]`; and
at each point `(ℓ, r)` of the rectangle, `T ℓ` is the smoothed maximum
`smoothedMax δ (M + q ℓ) (χ ℓ')` near `r` for some `ℓ' ∈ [b, ℓ₁]`, so that `T ℓ r` lies between
`max (M r + q ℓ) (χ ℓ' r)` and that maximum plus `δ / 2`, its first `r`-derivative between
those of `M` and `χ ℓ'`, and its second `r`-derivative is at least the smaller of those of `M`
and `χ ℓ'`.

No convexity is assumed or claimed: `exists_smoothedMax_shapeFamily` and its form over `R`,
`exists_smoothedMin_shapeFamilyOverR`, add it. -/
theorem exists_smoothedMax_family {χ : ℝ → ℝ → ℝ} {M q : ℝ → ℝ} {U : Set (ℝ × ℝ)}
    {b c ℓ₁ r₁ r₂ ε : ℝ} (hbc : b < c) (hcℓ : c ≤ ℓ₁) (hU : IsOpen U)
    (hRU : Icc b ℓ₁ ×ˢ Icc r₁ r₂ ⊆ U) (hχ : ContDiffOn ℝ ∞ (Function.uncurry χ) U)
    (hχℓ : ∀ x ∈ Icc b ℓ₁ ×ˢ Icc r₁ r₂, 0 < deriv (fun ℓ ↦ χ ℓ x.2) x.1)
    (hM : ContDiff ℝ ∞ M) (hq : ContDiff ℝ ∞ q) (hqm : Monotone q)
    (hq' : ∀ ℓ ∈ Ico b c, 0 < deriv q ℓ)
    (hgb : ∀ r ∈ Icc r₁ r₂, χ b r < M r + q b)
    (hgc : ∀ ℓ ∈ Icc c ℓ₁, ∀ r ∈ Icc r₁ r₂, M r + q ℓ < χ ℓ r) (hε : 0 < ε) :
    ∃ δ ∈ Ioc 0 ε, ∃ T : ℝ → ℝ → ℝ, ContDiff ℝ ∞ (Function.uncurry T) ∧
      (∀ x ∈ Icc b ℓ₁ ×ˢ Icc r₁ r₂, 0 < deriv (fun ℓ ↦ T ℓ x.2) x.1) ∧
      Function.uncurry T =ᶠ[𝓝ˢ ({b} ×ˢ Icc r₁ r₂)] (fun x ↦ M x.2 + q x.1) ∧
      Function.uncurry T =ᶠ[𝓝ˢ ({ℓ₁} ×ˢ Icc r₁ r₂)] Function.uncurry χ ∧
      ∀ x ∈ Icc b ℓ₁ ×ˢ Icc r₁ r₂, ∃ ℓ' ∈ Icc b ℓ₁,
        T x.1 =ᶠ[𝓝 x.2] (fun r ↦ smoothedMax δ (M r + q x.1) (χ ℓ' r)) ∧
        max (M x.2 + q x.1) (χ ℓ' x.2) ≤ T x.1 x.2 ∧
        T x.1 x.2 ≤ max (M x.2 + q x.1) (χ ℓ' x.2) + δ / 2 ∧
        min (deriv M x.2) (deriv (χ ℓ') x.2) ≤ deriv (T x.1) x.2 ∧
        deriv (T x.1) x.2 ≤ max (deriv M x.2) (deriv (χ ℓ') x.2) ∧
        min (iteratedDeriv 2 M x.2) (iteratedDeriv 2 (χ ℓ') x.2) ≤
          iteratedDeriv 2 (T x.1) x.2 := by
  have hbℓ : b ≤ ℓ₁ := hbc.le.trans hcℓ
  -- A globally smooth `χ'` that agrees with `uncurry χ` near the rectangle.
  obtain ⟨χ', hχ', hχ'eq⟩ := hχ.exists_contDiff_eventuallyEq_nhdsSet
    (isCompact_Icc.prod isCompact_Icc) (hU.mem_nhdsSet.2 hRU)
  have hloc : ∀ x ∈ Icc b ℓ₁ ×ˢ Icc r₁ r₂, χ' =ᶠ[𝓝 x] Function.uncurry χ := fun _ hx ↦
    hχ'eq.filter_mono (nhds_le_nhdsSet hx)
  have hval : ∀ x ∈ Icc b ℓ₁ ×ˢ Icc r₁ r₂, χ' x = χ x.1 x.2 := fun x hx ↦
    (hloc x hx).eq_of_nhds
  have hsliceR : ∀ x ∈ Icc b ℓ₁ ×ˢ Icc r₁ r₂, (fun r ↦ χ' (x.1, r)) =ᶠ[𝓝 x.2] χ x.1 :=
    fun x hx ↦ (hloc x hx).uncurry_left (f := fun ℓ r ↦ χ' (ℓ, r))
  have hχ'c : Continuous χ' := hχ'.continuous
  have hMcont : Continuous M := hM.continuous
  have hqcont : Continuous q := hq.continuous
  -- The reparametrization `L`: `b` up to `b`, the identity from `b'` on.
  set b' := (b + c) / 2 with hb'
  have hbb' : b < b' := by linarith
  have hb'c : b' < c := by linarith
  set L := TauCeti.smoothLowerTruncation b b'
  have hLs : ContDiff ℝ ∞ L := TauCeti.contDiff_smoothLowerTruncation b b'
  have hLmem : ∀ ℓ ∈ Icc b ℓ₁, L ℓ ∈ Icc b ℓ₁ := fun ℓ hℓ ↦
    ⟨TauCeti.le_smoothLowerTruncation hbb'.le ℓ,
      (TauCeti.smoothLowerTruncation_le_self hℓ.1).trans hℓ.2⟩
  have hLb : L b = b := TauCeti.smoothLowerTruncation_of_le_left hbb'.le le_rfl
  have hLid : ∀ ℓ, b' ≤ ℓ → L ℓ = ℓ := fun ℓ hℓ ↦
    TauCeti.smoothLowerTruncation_of_right_le hbb' hℓ
  -- The gaps at `b` and at `ℓ₁`.
  obtain ⟨g₀, hg₀, hg₀le⟩ := isCompact_Icc.exists_forall_le' (a := (0 : ℝ))
    (f := fun r ↦ M r + q b - χ' (b, r)) (s := Icc r₁ r₂) (by fun_prop) fun r hr' ↦ by
      have := hval (b, r) ⟨left_mem_Icc.2 hbℓ, hr'⟩
      simp only at this ⊢
      linarith [hgb r hr']
  obtain ⟨g₁, hg₁, hg₁le⟩ := isCompact_Icc.exists_forall_le' (a := (0 : ℝ))
    (f := fun r ↦ χ' (ℓ₁, r) - (M r + q ℓ₁)) (s := Icc r₁ r₂) (by fun_prop) fun r hr' ↦ by
      have := hval (ℓ₁, r) ⟨right_mem_Icc.2 hbℓ, hr'⟩
      simp only at this ⊢
      linarith [hgc ℓ₁ ⟨hcℓ, le_rfl⟩ r hr']
  have hFM : ContDiff ℝ ∞ fun x : ℝ × ℝ ↦ M x.2 + q x.1 :=
    (hM.comp contDiff_snd).add (hq.comp contDiff_fst)
  have hFA : ContDiff ℝ ∞ fun x : ℝ × ℝ ↦ χ' (L x.1, x.2) :=
    hχ'.comp ((hLs.comp contDiff_fst).prodMk contDiff_snd)
  have hA2 : ∀ p : ℝ, ContDiff ℝ 2 fun r ↦ χ' (L p, r) := fun p ↦
    (hFA.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)
  have hM2 : ∀ p : ℝ, ContDiff ℝ 2 fun r ↦ M r + q p := fun p ↦
    (hFM.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)
  set δ := min ε (min (g₀ / 2) (g₁ / 2))
  have hδ : 0 < δ := lt_min hε (lt_min (half_pos hg₀) (half_pos hg₁))
  have hδε : δ ≤ ε := min_le_left _ _
  have hδg₀ : δ < g₀ := (min_le_right _ _).trans_lt ((min_le_left _ _).trans_lt (half_lt_self hg₀))
  have hδg₁ : δ < g₁ :=
    (min_le_right _ _).trans_lt ((min_le_right _ _).trans_lt (half_lt_self hg₁))
  refine ⟨δ, ⟨hδ, hδε⟩, fun ℓ r ↦ smoothedMax δ (M r + q ℓ) (χ' (L ℓ, r)),
    (contDiff_smoothedMax δ).comp (hFM.prodMk hFA), ?_, ?_, ?_, ?_⟩
  · -- The `ℓ`-derivative.
    intro x hx
    obtain ⟨⟨hb, hℓ⟩, hr'⟩ := hx
    have hx₁ : (L x.1, x.2) ∈ Icc b ℓ₁ ×ˢ Icc r₁ r₂ := ⟨hLmem x.1 ⟨hb, hℓ⟩, hr'⟩
    have hχd : HasDerivAt (fun ℓ ↦ χ' (ℓ, x.2)) (deriv (fun ℓ ↦ χ ℓ x.2) (L x.1)) (L x.1) :=
      (hχ'.differentiable (by simp) _).hasDerivAt_slice_left_of_eventuallyEq (hloc _ hx₁)
    have hpos : 0 < deriv (fun ℓ ↦ χ ℓ x.2) (L x.1) := hχℓ (L x.1, x.2) hx₁
    have hg := hχd.comp x.1 (hLs.differentiable (by simp) x.1).hasDerivAt
    have hf := ((hq.differentiable (by simp) x.1).hasDerivAt).const_add (M x.2)
    beta_reduce
    have hg0 : 0 ≤ deriv (fun ℓ ↦ χ ℓ x.2) (L x.1) * deriv L x.1 :=
      mul_nonneg hpos.le (TauCeti.monotone_smoothLowerTruncation b b').deriv_nonneg
    rcases lt_or_ge x.1 c with hc | hc
    · -- On `[b, c)`, `q' > 0`; the slope of the second term is positive except at `b`, where
      -- the first term is the larger.
      rcases le_total (χ' (L x.1, x.2)) (M x.2 + q x.1) with h | h
      · exact deriv_smoothedMax_pos_left hδ hf hg h (hq' x.1 ⟨hb, hc⟩) hg0
      · have hbx : b < x.1 := hb.lt_of_ne fun hxb ↦ by
          rw [← hxb, hLb, hval (b, x.2) ⟨left_mem_Icc.2 hbℓ, hr'⟩] at h
          linarith [hgb x.2 hr']
        exact deriv_smoothedMax_pos_right hδ hf hg h hqm.deriv_nonneg
          (mul_pos hpos (TauCeti.deriv_smoothLowerTruncation_pos hbb' hbx))
    · -- On `[c, ℓ₁]`, the second term is the larger and has positive slope.
      have hle : M x.2 + q x.1 ≤ χ' (L x.1, x.2) := by
        rw [hLid x.1 (hb'c.le.trans hc)] at hx₁ ⊢
        rw [hval _ hx₁]
        exact (hgc x.1 ⟨hc, hℓ⟩ x.2 hr').le
      exact deriv_smoothedMax_pos_right hδ hf hg hle hqm.deriv_nonneg
        (mul_pos hpos (TauCeti.deriv_smoothLowerTruncation_pos hbb' (hbc.trans_le hc)))
  · -- Near `b`, the family is `M + q ℓ`.
    refine smoothedMax_eventuallyEq_left hδ (by fun_prop) (by fun_prop) ?_
    rintro x ⟨hx₁, hx₂⟩
    rw [mem_singleton_iff] at hx₁
    have := hg₀le x.2 hx₂
    simp only [hx₁, hLb] at this ⊢
    linarith
  · -- Near `ℓ₁`, the family is `χ`.
    refine (smoothedMax_eventuallyEq_right hδ (by fun_prop) (by fun_prop) ?_).trans ?_
    · rintro ⟨ℓ, r⟩ ⟨hx₁, hx₂⟩
      rw [mem_singleton_iff] at hx₁
      subst hx₁
      have := hg₁le r hx₂
      simp only [hLid ℓ (by linarith)] at this ⊢
      linarith
    · have hsub : {ℓ₁} ×ˢ Icc r₁ r₂ ⊆ Ioi b' ×ˢ univ := fun x hx ↦
        ⟨show b' < x.1 by rw [mem_singleton_iff.1 hx.1]; linarith, mem_univ _⟩
      have hsubR : {ℓ₁} ×ˢ Icc r₁ r₂ ⊆ Icc b ℓ₁ ×ˢ Icc r₁ r₂ :=
        prod_mono (singleton_subset_iff.2 (right_mem_Icc.2 hbℓ)) subset_rfl
      filter_upwards [(isOpen_Ioi.prod isOpen_univ).mem_nhdsSet.2 hsub,
        hχ'eq.filter_mono (nhdsSet_mono hsubR)] with x hx hχx
      rw [hLid x.1 hx.1.le]
      exact hχx
  · -- The pointwise comparison with `M + q ℓ` and `χ (L ℓ)`.
    intro x hx
    have hx₁ : (L x.1, x.2) ∈ Icc b ℓ₁ ×ˢ Icc r₁ r₂ := ⟨hLmem x.1 hx.1, hx.2⟩
    have heq := hsliceR _ hx₁
    have hloc' : (fun r ↦ smoothedMax δ (M r + q x.1) (χ' (L x.1, r))) =ᶠ[𝓝 x.2]
        fun r ↦ smoothedMax δ (M r + q x.1) (χ (L x.1) r) :=
      heq.mono fun r hr' ↦ congrArg (smoothedMax δ (M r + q x.1)) hr'
    have hv : χ' (L x.1, x.2) = χ (L x.1) x.2 := hval _ hx₁
    have hdM : deriv (fun r ↦ M r + q x.1) x.2 = deriv M x.2 := deriv_add_const _
    have hd2M : iteratedDeriv 2 (fun r ↦ M r + q x.1) x.2 = iteratedDeriv 2 M x.2 :=
      by rw [iteratedDeriv_add_const (by norm_num : 0 < 2)]
    have hdA : deriv (fun r ↦ χ' (L x.1, r)) x.2 = deriv (χ (L x.1)) x.2 := heq.deriv_eq
    have hd2A : iteratedDeriv 2 (fun r ↦ χ' (L x.1, r)) x.2 = iteratedDeriv 2 (χ (L x.1)) x.2 :=
      heq.iteratedDeriv_eq 2
    have hdiffM := (hM2 x.1).differentiable two_ne_zero x.2
    have hdiffA := (hA2 x.1).differentiable two_ne_zero x.2
    refine ⟨L x.1, hLmem x.1 hx.1, hloc', ?_, ?_, ?_, ?_, ?_⟩
    · rw [← hv]
      exact max_le_smoothedMax hδ _ _
    · rw [← hv]
      exact smoothedMax_le_max_add hδ _ _
    · rw [← hdM, ← hdA]
      exact min_deriv_le_deriv_smoothedMax hdiffM hdiffA
    · rw [← hdM, ← hdA]
      exact deriv_smoothedMax_le_max hdiffM hdiffA
    · rw [← hd2M, ← hd2A]
      exact min_iteratedDeriv_two_le_iteratedDeriv_two_smoothedMax (hM2 x.1).contDiffAt
        (hA2 x.1).contDiffAt hδ.le

/-- **The piece of a strictly increasing family of `i`-convex shapes next to `ℓ₁`.** Let
`χ : ℝ → ℝ → ℝ` be smooth in `(ℓ, r)` on an open set containing `[b, ℓ₁] × [r₁, r₂]`, with
`χ ℓ` an `i`-convex shape at `r` and `∂χ/∂ℓ > 0` at each point of the rectangle. Let `M` be a
smooth function that is an `i`-convex shape on `[r₁, r₂]`, and `q` a smooth nondecreasing
function with `q b ≥ 0` and `q' > 0` on `[b, c)`, where `b < c ≤ ℓ₁`. Suppose that
`χ b < M + q b` and that `M + q ℓ < χ ℓ` for `ℓ ∈ [c, ℓ₁]`, on `[r₁, r₂]`. Then for each
`ε > 0` there are `δ ∈ (0, ε]` and `T : ℝ → ℝ → ℝ`, smooth on `ℝ²`, such that on the rectangle
`T ℓ` is an `i`-convex shape at `r` with `∂T/∂ℓ > 0`; `T` equals `M r + q ℓ` near
`{b} × [r₁, r₂]` and `χ` near `{ℓ₁} × [r₁, r₂]`; and at each point `(ℓ, r)` of the rectangle,
`T ℓ` is the smoothed maximum `smoothedMax δ (M + q ℓ) (χ ℓ')` near `r` for some `ℓ' ∈ [b, ℓ₁]`,
so that `T ℓ r` lies between `max (M r + q ℓ) (χ ℓ' r)` and that maximum plus `δ / 2`, its first
`r`-derivative between those of `M` and `χ ℓ'`, and its second `r`-derivative is at least the
smaller of those of `M` and `χ ℓ'`. -/
theorem exists_smoothedMax_shapeFamily {χ : ℝ → ℝ → ℝ} {M q : ℝ → ℝ} {U : Set (ℝ × ℝ)}
    {b c ℓ₁ r₁ r₂ ε : ℝ} (hbc : b < c) (hcℓ : c ≤ ℓ₁) (hU : IsOpen U)
    (hRU : Icc b ℓ₁ ×ˢ Icc r₁ r₂ ⊆ U) (hχ : ContDiffOn ℝ ∞ (Function.uncurry χ) U)
    (hχc : ∀ x ∈ Icc b ℓ₁ ×ˢ Icc r₁ r₂, IsConvexShapeAt (χ x.1) x.2)
    (hχℓ : ∀ x ∈ Icc b ℓ₁ ×ˢ Icc r₁ r₂, 0 < deriv (fun ℓ ↦ χ ℓ x.2) x.1)
    (hM : ContDiff ℝ ∞ M) (hMc : ∀ r ∈ Icc r₁ r₂, IsConvexShapeAt M r)
    (hq : ContDiff ℝ ∞ q) (hqm : Monotone q) (hqb : 0 ≤ q b)
    (hq' : ∀ ℓ ∈ Ico b c, 0 < deriv q ℓ)
    (hgb : ∀ r ∈ Icc r₁ r₂, χ b r < M r + q b)
    (hgc : ∀ ℓ ∈ Icc c ℓ₁, ∀ r ∈ Icc r₁ r₂, M r + q ℓ < χ ℓ r) (hε : 0 < ε) :
    ∃ δ ∈ Ioc 0 ε, ∃ T : ℝ → ℝ → ℝ, ContDiff ℝ ∞ (Function.uncurry T) ∧
      (∀ x ∈ Icc b ℓ₁ ×ˢ Icc r₁ r₂, IsConvexShapeAt (T x.1) x.2) ∧
      (∀ x ∈ Icc b ℓ₁ ×ˢ Icc r₁ r₂, 0 < deriv (fun ℓ ↦ T ℓ x.2) x.1) ∧
      Function.uncurry T =ᶠ[𝓝ˢ ({b} ×ˢ Icc r₁ r₂)] (fun x ↦ M x.2 + q x.1) ∧
      Function.uncurry T =ᶠ[𝓝ˢ ({ℓ₁} ×ˢ Icc r₁ r₂)] Function.uncurry χ ∧
      ∀ x ∈ Icc b ℓ₁ ×ˢ Icc r₁ r₂, ∃ ℓ' ∈ Icc b ℓ₁,
        T x.1 =ᶠ[𝓝 x.2] (fun r ↦ smoothedMax δ (M r + q x.1) (χ ℓ' r)) ∧
        max (M x.2 + q x.1) (χ ℓ' x.2) ≤ T x.1 x.2 ∧
        T x.1 x.2 ≤ max (M x.2 + q x.1) (χ ℓ' x.2) + δ / 2 ∧
        min (deriv M x.2) (deriv (χ ℓ') x.2) ≤ deriv (T x.1) x.2 ∧
        deriv (T x.1) x.2 ≤ max (deriv M x.2) (deriv (χ ℓ') x.2) ∧
        min (iteratedDeriv 2 M x.2) (iteratedDeriv 2 (χ ℓ') x.2) ≤
          iteratedDeriv 2 (T x.1) x.2 := by
  -- The width `δ₀` below which the smoothed maxima of `M + q ℓ` and a member of `χ` are
  -- `i`-convex shapes.
  have hFM : ContDiff ℝ ∞ fun x : (ℝ × ℝ) × ℝ ↦ M x.2 + q x.1.1 :=
    (hM.comp contDiff_snd).add (hq.comp (contDiff_fst.comp contDiff_fst))
  have hAx : ∀ p ∈ Icc b ℓ₁ ×ˢ Icc b ℓ₁, ∀ r ∈ Icc r₁ r₂,
      ContDiffAt ℝ ∞ (Function.uncurry fun (p : ℝ × ℝ) r ↦ χ p.2 r) (p, r) := fun p hp r hr' ↦
    (hχ.contDiffAt (hU.mem_nhds (hRU ⟨hp.2, hr'⟩))).comp (p, r)
      ((contDiffAt_snd.comp _ contDiffAt_fst).prodMk contDiffAt_snd)
  obtain ⟨δ₀, hδ₀, hconv⟩ := exists_forall_isConvexShapeAt_smoothedMax
    (K := Icc b ℓ₁ ×ˢ Icc b ℓ₁) (isCompact_Icc.prod isCompact_Icc)
    (M := fun p r ↦ M r + q p.1) (A := fun p r ↦ χ p.2 r) (r₁ := r₁) (r₂ := r₂)
    (fun p _ _ _ ↦ ((hFM.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)).contDiffAt)
    (fun p hp r hr' ↦ (hAx p hp r hr').uncurry_left.of_le (by simp))
    (fun p hp r hr' ↦ (hMc r hr').add_const (hqb.trans (hqm hp.1.1)))
    (fun p hp r hr' ↦ hχc (p.2, r) ⟨hp.2, hr'⟩)
    (fun _ _ _ _ ↦ (hFM.contDiffAt.continuousAt_iteratedDeriv_prod_right
      (by exact_mod_cast le_top)).continuousWithinAt)
    (fun _ _ x hx ↦ ((hAx x.1 hx.1 x.2 hx.2).continuousAt_iteratedDeriv_prod_right
      (by exact_mod_cast le_top)).continuousWithinAt)
  obtain ⟨δ, hδ, T, hT, hTℓ, hTb, hTℓ₁, hTx⟩ := exists_smoothedMax_family hbc hcℓ hU hRU hχ hχℓ
    hM hq hqm hq' hgb hgc (lt_min hε hδ₀)
  refine ⟨δ, ⟨hδ.1, hδ.2.trans (min_le_left _ _)⟩, T, hT, fun x hx ↦ ?_, hTℓ, hTb, hTℓ₁, hTx⟩
  obtain ⟨ℓ', hℓ', hloc, -⟩ := hTx x hx
  exact (hconv δ ⟨hδ.1, hδ.2.trans (min_le_right _ _)⟩ (x.1, ℓ') ⟨hx.1, hℓ'⟩ x.2
    hx.2).congr_of_eventuallyEq hloc

/-- **Reparametrizing a strictly increasing family and raising it.** Let `χ : ℝ → ℝ → ℝ` be
smooth in `(ℓ, r)` on an open set containing `[ℓ₀, a] × [r₁, r₂]`, with `∂χ/∂ℓ > 0` at each
point of the rectangle, and let `q` be a smooth nondecreasing function that vanishes near `ℓ₀`
and has `q' > 0` on `[a₁, a]`, where `ℓ₀ < a₁ < a`. Then there is `T : ℝ → ℝ → ℝ`, smooth on
`ℝ²`, such that `∂T/∂ℓ > 0` on the rectangle; `T` equals `χ` near `{ℓ₀} × [r₁, r₂]` and
`χ a r + q ℓ` near `{a} × [r₁, r₂]`; and at each point `(ℓ, r)` of the rectangle, `T ℓ` agrees
near `r` with `χ ℓ' + q ℓ` for some `ℓ' ∈ [ℓ₀, a]`.

No convexity is assumed or claimed: `exists_comp_add_shapeFamily` and its form over `R`,
`exists_comp_sub_shapeFamilyOverR`, add it. -/
theorem exists_comp_add_family {χ : ℝ → ℝ → ℝ} {q : ℝ → ℝ} {U : Set (ℝ × ℝ)}
    {ℓ₀ a₁ a r₁ r₂ : ℝ} (hℓa₁ : ℓ₀ < a₁) (ha₁a : a₁ < a) (hU : IsOpen U)
    (hRU : Icc ℓ₀ a ×ˢ Icc r₁ r₂ ⊆ U) (hχ : ContDiffOn ℝ ∞ (Function.uncurry χ) U)
    (hχℓ : ∀ x ∈ Icc ℓ₀ a ×ˢ Icc r₁ r₂, 0 < deriv (fun ℓ ↦ χ ℓ x.2) x.1)
    (hq : ContDiff ℝ ∞ q) (hqm : Monotone q) (hq₀ : q =ᶠ[𝓝 ℓ₀] fun _ ↦ 0)
    (hqa : ∀ ℓ ∈ Icc a₁ a, 0 < deriv q ℓ) :
    ∃ T : ℝ → ℝ → ℝ, ContDiff ℝ ∞ (Function.uncurry T) ∧
      (∀ x ∈ Icc ℓ₀ a ×ˢ Icc r₁ r₂, 0 < deriv (fun ℓ ↦ T ℓ x.2) x.1) ∧
      Function.uncurry T =ᶠ[𝓝ˢ ({ℓ₀} ×ˢ Icc r₁ r₂)] Function.uncurry χ ∧
      Function.uncurry T =ᶠ[𝓝ˢ ({a} ×ˢ Icc r₁ r₂)] (fun x ↦ χ a x.2 + q x.1) ∧
      ∀ x ∈ Icc ℓ₀ a ×ˢ Icc r₁ r₂, ∃ ℓ' ∈ Icc ℓ₀ a,
        T x.1 =ᶠ[𝓝 x.2] fun r ↦ χ ℓ' r + q x.1 := by
  -- A globally smooth `χ'` that agrees with `uncurry χ` near the rectangle.
  obtain ⟨χ', hχ', hχ'eq⟩ := hχ.exists_contDiff_eventuallyEq_nhdsSet
    (isCompact_Icc.prod isCompact_Icc) (hU.mem_nhdsSet.2 hRU)
  have hloc : ∀ x ∈ Icc ℓ₀ a ×ˢ Icc r₁ r₂, χ' =ᶠ[𝓝 x] Function.uncurry χ := fun _ hx ↦
    hχ'eq.filter_mono (nhds_le_nhdsSet hx)
  have hsliceR : ∀ x ∈ Icc ℓ₀ a ×ˢ Icc r₁ r₂, (fun r ↦ χ' (x.1, r)) =ᶠ[𝓝 x.2] χ x.1 :=
    fun x hx ↦ (hloc x hx).uncurry_left (f := fun ℓ r ↦ χ' (ℓ, r))
  -- The reparametrization `L`: the identity up to `a'`, equal to `a` from `a''` on.
  set a' := (ℓ₀ + a₁) / 2 with ha'
  set a'' := (a₁ + a) / 2 with ha''
  have hℓa' : ℓ₀ < a' := by linarith [ha']
  have ha'a'' : a' < a'' := by linarith [ha', ha'']
  have ha₁a'' : a₁ < a'' := by linarith [ha'']
  obtain ⟨L, hLs, hLm, hLid, hLa, hLle, hL'⟩ :=
    Real.exists_contDiff_monotone_eqOn_id_Iic_eqOn_const_Ici ha'a''
      (show a'' ≤ a by linarith [ha''])
  have hLℓ₀ : L ℓ₀ = ℓ₀ := hLid (mem_Iic.2 hℓa'.le)
  have hLmem : ∀ ℓ ∈ Icc ℓ₀ a, L ℓ ∈ Icc ℓ₀ a := fun ℓ hℓ ↦
    ⟨hLℓ₀ ▸ hLm hℓ.1, hLle ℓ⟩
  refine ⟨fun ℓ r ↦ χ' (L ℓ, r) + q ℓ,
    (hχ'.comp ((hLs.comp contDiff_fst).prodMk contDiff_snd)).add (hq.comp contDiff_fst),
    fun x hx ↦ ?_, ?_, ?_, fun x hx ↦ ⟨L x.1, hLmem x.1 hx.1, ?_⟩⟩
  · -- The `ℓ`-derivative.
    obtain ⟨⟨hℓ₀x, hxa⟩, hr'⟩ := hx
    have hx₁ : (L x.1, x.2) ∈ Icc ℓ₀ a ×ˢ Icc r₁ r₂ := ⟨hLmem x.1 ⟨hℓ₀x, hxa⟩, hr'⟩
    have hχd : HasDerivAt (fun ℓ ↦ χ' (ℓ, x.2)) (deriv (fun ℓ ↦ χ ℓ x.2) (L x.1)) (L x.1) :=
      (hχ'.differentiable (by simp) _).hasDerivAt_slice_left_of_eventuallyEq (hloc _ hx₁)
    have hpos : 0 < deriv (fun ℓ ↦ χ ℓ x.2) (L x.1) := hχℓ (L x.1, x.2) hx₁
    have hd : HasDerivAt (fun ℓ ↦ χ' (L ℓ, x.2) + q ℓ)
        (deriv (fun ℓ ↦ χ ℓ x.2) (L x.1) * deriv L x.1 + deriv q x.1) x.1 :=
      (hχd.comp x.1 (hLs.differentiable (by simp) x.1).hasDerivAt).add
        (hq.differentiable (by simp) x.1).hasDerivAt
    beta_reduce
    rw [hd.deriv]
    rcases lt_or_ge x.1 a'' with h | h
    · exact add_pos_of_pos_of_nonneg (mul_pos hpos (hL' _ h)) hqm.deriv_nonneg
    · exact add_pos_of_nonneg_of_pos (mul_nonneg hpos.le hLm.deriv_nonneg)
        (hqa x.1 ⟨ha₁a''.le.trans h, hxa⟩)
  · -- Near `ℓ₀`, the family is `χ`.
    obtain ⟨t, htq, ht, hℓ₀t⟩ := eventually_nhds_iff.1 hq₀
    have hsub : {ℓ₀} ×ˢ Icc r₁ r₂ ⊆ (t ∩ Iio a') ×ˢ univ := fun x hx ↦
      ⟨by rw [mem_singleton_iff.1 hx.1]; exact ⟨hℓ₀t, hℓa'⟩, mem_univ _⟩
    have hsubR : {ℓ₀} ×ˢ Icc r₁ r₂ ⊆ Icc ℓ₀ a ×ˢ Icc r₁ r₂ :=
      prod_mono (singleton_subset_iff.2 (left_mem_Icc.2 (by linarith))) subset_rfl
    filter_upwards [((ht.inter isOpen_Iio).prod isOpen_univ).mem_nhdsSet.2 hsub,
      hχ'eq.filter_mono (nhdsSet_mono hsubR)] with x hx hχx
    simp only [Function.uncurry_def]
    rw [hLid (mem_Iic.2 hx.1.2.le), id, htq _ hx.1.1, add_zero]
    exact hχx
  · -- Near `a`, the family is `χ a + q`.
    have hsub : {a} ×ˢ Icc r₁ r₂ ⊆ Ioi a'' ×ˢ univ := fun x hx ↦
      ⟨show a'' < x.1 by rw [mem_singleton_iff.1 hx.1]; linarith [ha''], mem_univ _⟩
    have hsubR : {a} ×ˢ Icc r₁ r₂ ⊆ Icc ℓ₀ a ×ˢ Icc r₁ r₂ :=
      prod_mono (singleton_subset_iff.2 (right_mem_Icc.2 (by linarith))) subset_rfl
    have hmaps : MapsTo (fun x : ℝ × ℝ ↦ (a, x.2)) ({a} ×ˢ Icc r₁ r₂) ({a} ×ˢ Icc r₁ r₂) :=
      fun x hx ↦ ⟨mem_singleton a, hx.2⟩
    filter_upwards [(isOpen_Ioi.prod isOpen_univ).mem_nhdsSet.2 hsub,
      ((Continuous.tendsto_nhdsSet (by fun_prop) hmaps).eventually
        (hχ'eq.filter_mono (nhdsSet_mono hsubR)))] with x hx hχx
    simp only [Function.uncurry_def]
    rw [hLa (mem_Ici.2 (le_of_lt hx.1))]
    exact congrArg (· + q x.1) hχx
  · -- At each point, the family is a member of `χ` raised by `q ℓ`.
    exact (hsliceR (L x.1, x.2) ⟨hLmem x.1 hx.1, hx.2⟩).mono fun r hr' ↦
      congrArg (· + q x.1) hr'

/-- **The piece of a strictly increasing family of `i`-convex shapes next to `ℓ₀`.** Let
`χ : ℝ → ℝ → ℝ` be smooth in `(ℓ, r)` on an open set containing `[ℓ₀, a] × [r₁, r₂]`, with
`χ ℓ` an `i`-convex shape at `r` and `∂χ/∂ℓ > 0` at each point of the rectangle, and let `q` be
a smooth nondecreasing function that vanishes near `ℓ₀` and has `q' > 0` on `[a₁, a]`, where
`ℓ₀ < a₁ < a`. Then there is `T : ℝ → ℝ → ℝ`, smooth on `ℝ²`, such that on the rectangle `T ℓ`
is an `i`-convex shape at `r` with `∂T/∂ℓ > 0`; `T` equals `χ` near `{ℓ₀} × [r₁, r₂]` and
`χ a r + q ℓ` near `{a} × [r₁, r₂]`; and at each point `(ℓ, r)` of the rectangle, `T ℓ` agrees
near `r` with `χ ℓ' + q ℓ` for some `ℓ' ∈ [ℓ₀, a]`. -/
theorem exists_comp_add_shapeFamily {χ : ℝ → ℝ → ℝ} {q : ℝ → ℝ} {U : Set (ℝ × ℝ)}
    {ℓ₀ a₁ a r₁ r₂ : ℝ} (hℓa₁ : ℓ₀ < a₁) (ha₁a : a₁ < a) (hU : IsOpen U)
    (hRU : Icc ℓ₀ a ×ˢ Icc r₁ r₂ ⊆ U) (hχ : ContDiffOn ℝ ∞ (Function.uncurry χ) U)
    (hχc : ∀ x ∈ Icc ℓ₀ a ×ˢ Icc r₁ r₂, IsConvexShapeAt (χ x.1) x.2)
    (hχℓ : ∀ x ∈ Icc ℓ₀ a ×ˢ Icc r₁ r₂, 0 < deriv (fun ℓ ↦ χ ℓ x.2) x.1)
    (hq : ContDiff ℝ ∞ q) (hqm : Monotone q) (hq₀ : q =ᶠ[𝓝 ℓ₀] fun _ ↦ 0)
    (hqa : ∀ ℓ ∈ Icc a₁ a, 0 < deriv q ℓ) :
    ∃ T : ℝ → ℝ → ℝ, ContDiff ℝ ∞ (Function.uncurry T) ∧
      (∀ x ∈ Icc ℓ₀ a ×ˢ Icc r₁ r₂, IsConvexShapeAt (T x.1) x.2) ∧
      (∀ x ∈ Icc ℓ₀ a ×ˢ Icc r₁ r₂, 0 < deriv (fun ℓ ↦ T ℓ x.2) x.1) ∧
      Function.uncurry T =ᶠ[𝓝ˢ ({ℓ₀} ×ˢ Icc r₁ r₂)] Function.uncurry χ ∧
      Function.uncurry T =ᶠ[𝓝ˢ ({a} ×ˢ Icc r₁ r₂)] (fun x ↦ χ a x.2 + q x.1) ∧
      ∀ x ∈ Icc ℓ₀ a ×ˢ Icc r₁ r₂, ∃ ℓ' ∈ Icc ℓ₀ a,
        T x.1 =ᶠ[𝓝 x.2] fun r ↦ χ ℓ' r + q x.1 := by
  obtain ⟨T, hT, hTℓ, hT₀, hTa, hTx⟩ :=
    exists_comp_add_family hℓa₁ ha₁a hU hRU hχ hχℓ hq hqm hq₀ hqa
  refine ⟨T, hT, fun x hx ↦ ?_, hTℓ, hT₀, hTa, hTx⟩
  obtain ⟨ℓ', hℓ', hloc⟩ := hTx x hx
  exact ((hχc (ℓ', x.2) ⟨hℓ', hx.2⟩).add_const
    (hq₀.eq_of_nhds ▸ hqm hx.1.1)).congr_of_eventuallyEq hloc

/-- **Smoothness of the blend by a cutoff in `r`.** Let `ρ` be smooth and equal to `1` on
`(-∞, r₃]`, let `ψ₀` be smooth on `ℝ²`, and let `χ` be smooth in `(ℓ, r)` on an open set `V`.
Then the blend `ρ r * ψ₀ ℓ r + (1 - ρ r) * χ ℓ r` is smooth on `(ℝ × (-∞, r₃)) ∪ V`: below `r₃`
it is `ψ₀`, and on `V` both terms are smooth. -/
theorem contDiffOn_blend {ψ₀ χ : ℝ → ℝ → ℝ} {ρ : ℝ → ℝ} {V : Set (ℝ × ℝ)} {r₃ : ℝ}
    (hρs : ContDiff ℝ ∞ ρ) (hρ1 : EqOn ρ 1 (Iic r₃)) (hψ₀ : ContDiff ℝ ∞ (Function.uncurry ψ₀))
    (hV : IsOpen V) (hχ : ContDiffOn ℝ ∞ (Function.uncurry χ) V) :
    ContDiffOn ℝ ∞ (fun x : ℝ × ℝ ↦ ρ x.2 * ψ₀ x.1 x.2 + (1 - ρ x.2) * χ x.1 x.2)
      (univ ×ˢ Iio r₃ ∪ V) := by
  refine fun x hx ↦ ContDiffAt.contDiffWithinAt ?_
  rcases hx with ⟨-, hx⟩ | hx
  · refine hψ₀.contDiffAt.congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_univ.prod isOpen_Iio).mem_nhds ⟨mem_univ x.1, hx⟩] with y hy
    simp [hρ1 (mem_Iic.2 (mem_Iio.1 hy.2).le), Function.uncurry_def]
  · have hχV : ContDiffAt ℝ ∞ (Function.uncurry χ) x := hχ.contDiffAt (hV.mem_nhds hx)
    have hρ' : ContDiffAt ℝ ∞ (fun y : ℝ × ℝ ↦ ρ y.2) x := (hρs.comp contDiff_snd).contDiffAt
    exact (hρ'.mul hψ₀.contDiffAt).add ((contDiffAt_const.sub hρ').mul hχV)

/-- **Blending a family of `i`-convex shapes with `χ` near `r₂`.** Let `χ : ℝ → ℝ → ℝ` be
smooth in `(ℓ, r)` on an open set `V` containing the band `[ℓ₀, ℓ₁] × [r₃, r₂]`, with `χ ℓ` an
`i`-convex shape at `r` and `∂χ/∂ℓ > 0` at each point of the band, where `r₃ < r₂`. Then there
are a smooth cutoff `ρ` with values in `[0, 1]`, equal to `1` on `(-∞, r₃]` and to `0` near
`r₂`, and a tolerance `τ > 0`, such that the following holds for every family `ψ₀` smooth on
`ℝ²` whose members are `i`-convex shapes with `∂ψ₀/∂ℓ > 0` on `[ℓ₀, ℓ₁] × [r₁, r₂]`, and
which on the band is within `τ` of `χ` in value and first `r`-derivative and has second
`r`-derivative greater than that of `χ` minus `τ`. The blend
`ψ ℓ r = ρ r * ψ₀ ℓ r + (1 - ρ r) * χ ℓ r` is smooth on `(ℝ × (-∞, r₃)) ∪ V`, and on
`[ℓ₀, ℓ₁] × [r₁, r₂]` its members are `i`-convex shapes and `∂ψ/∂ℓ > 0`. The cutoff and the
tolerance depend only on `χ` and the band, not on `ψ₀`. -/
theorem exists_blend_shapeFamily {χ : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)}
    {ℓ₀ ℓ₁ r₁ r₃ r₂ : ℝ} (hr₃₂ : r₃ < r₂) (hV : IsOpen V)
    (hBV : Icc ℓ₀ ℓ₁ ×ˢ Icc r₃ r₂ ⊆ V) (hχ : ContDiffOn ℝ ∞ (Function.uncurry χ) V)
    (hχc : ∀ x ∈ Icc ℓ₀ ℓ₁ ×ˢ Icc r₃ r₂, IsConvexShapeAt (χ x.1) x.2)
    (hχℓ : ∀ x ∈ Icc ℓ₀ ℓ₁ ×ˢ Icc r₃ r₂, 0 < deriv (fun ℓ ↦ χ ℓ x.2) x.1) :
    ∃ ρ : ℝ → ℝ, ContDiff ℝ ∞ ρ ∧ (∀ r, ρ r ∈ Icc 0 1) ∧ EqOn ρ 1 (Iic r₃) ∧
      ρ =ᶠ[𝓝 r₂] 0 ∧ ∃ τ > 0, ∀ ψ₀ : ℝ → ℝ → ℝ, ContDiff ℝ ∞ (Function.uncurry ψ₀) →
        (∀ x ∈ Icc ℓ₀ ℓ₁ ×ˢ Icc r₁ r₂, IsConvexShapeAt (ψ₀ x.1) x.2) →
        (∀ x ∈ Icc ℓ₀ ℓ₁ ×ˢ Icc r₁ r₂, 0 < deriv (fun ℓ ↦ ψ₀ ℓ x.2) x.1) →
        (∀ x ∈ Icc ℓ₀ ℓ₁ ×ˢ Icc r₃ r₂, |ψ₀ x.1 x.2 - χ x.1 x.2| < τ ∧
          |deriv (ψ₀ x.1) x.2 - deriv (χ x.1) x.2| < τ ∧
          iteratedDeriv 2 (χ x.1) x.2 - τ < iteratedDeriv 2 (ψ₀ x.1) x.2) →
        ContDiffOn ℝ ∞ (fun x : ℝ × ℝ ↦ ρ x.2 * ψ₀ x.1 x.2 + (1 - ρ x.2) * χ x.1 x.2)
            (univ ×ˢ Iio r₃ ∪ V) ∧
          (∀ x ∈ Icc ℓ₀ ℓ₁ ×ˢ Icc r₁ r₂,
            IsConvexShapeAt (fun r ↦ ρ r * ψ₀ x.1 r + (1 - ρ r) * χ x.1 r) x.2) ∧
          ∀ x ∈ Icc ℓ₀ ℓ₁ ×ˢ Icc r₁ r₂,
            0 < deriv (fun ℓ ↦ ρ x.2 * ψ₀ ℓ x.2 + (1 - ρ x.2) * χ ℓ x.2) x.1 := by
  -- The cutoff: `1` up to `r₃`, `0` from the midpoint of `[r₃, r₂]` on.
  obtain ⟨ρ, hρs, hρI, -, hρ1, hρ0, -⟩ :=
    exists_contDiff_antitone_cutoff_mul_abs_deriv_le_deriv_deriv
      (show r₃ < (r₃ + r₂) / 2 by linarith)
  replace hρ0 : ρ =ᶠ[𝓝 r₂] 0 :=
    eventually_of_mem (Ici_mem_nhds (show (r₃ + r₂) / 2 < r₂ by linarith)) hρ0
  -- The tolerance, from the one-sided blend lemma on the band.
  have hK : IsCompact (Icc ℓ₀ ℓ₁ ×ˢ Icc r₃ r₂) := isCompact_Icc.prod isCompact_Icc
  have hχx : ∀ x ∈ Icc ℓ₀ ℓ₁ ×ˢ Icc r₃ r₂, ContDiffAt ℝ ∞ (Function.uncurry χ) x :=
    fun x hx ↦ hχ.contDiffAt (hV.mem_nhds (hBV hx))
  obtain ⟨τ, hτ, hblend⟩ :=
    exists_forall_isConvexShapeAt_mul_add_one_sub_mul_of_sub_lt_iteratedDeriv_two hK hχc
      (fun _ _ x hx ↦ ((hχx x hx).continuousAt_iteratedDeriv_prod_right
        (by exact_mod_cast le_top)).continuousWithinAt)
      (hρs.of_le (by simp)) fun x _ ↦ (hρI x.2).1
  refine ⟨ρ, hρs, hρI, hρ1, hρ0, τ, hτ, fun ψ₀ hψ₀ hψ₀c hψ₀ℓ hclose ↦ ⟨?_, ?_, ?_⟩⟩
  · exact contDiffOn_blend hρs hρ1 hψ₀ hV hχ
  · -- Convexity: below `r₃` the blend is `ψ₀` near `r`; on the band, the blend lemma.
    intro x hx
    rcases lt_or_ge x.2 r₃ with h | h
    · refine (hψ₀c x hx).congr_of_eventuallyEq ?_
      filter_upwards [Iio_mem_nhds h] with r hr
      simp [hρ1 (mem_Iic.2 (mem_Iio.1 hr).le)]
    · have hxK : x ∈ Icc ℓ₀ ℓ₁ ×ˢ Icc r₃ r₂ := ⟨hx.1, h, hx.2.2⟩
      obtain ⟨h₀, h₁, h₂⟩ := hclose x hxK
      exact hblend (ψ₀ x.1) x hxK (hψ₀.contDiffAt.uncurry_left.of_le (by simp))
        ((hχx x hxK).uncurry_left.of_le (by simp)) h₀ h₁ h₂
  · -- The `ℓ`-derivative: below `r₃` it is that of `ψ₀`; on the band, a convex combination of
    -- two positive numbers.
    intro x hx
    rcases lt_or_ge x.2 r₃ with h | h
    · simpa [hρ1 (mem_Iic.2 h.le)] using hψ₀ℓ x hx
    · exact deriv_mul_add_one_sub_mul_pos (hψ₀ℓ x hx) (hχℓ x ⟨hx.1, h, hx.2.2⟩) (hρI x.2).1
        (hρI x.2).2

/-- **Closeness of a raised family to `χ`.** Let `f` agree near `r` with `g + c`, where
`0 ≤ c ≤ τ / 2`, and let `g` be within `τ / 2` of `h` at `r` in value and first two
derivatives. Then at `r` the function `f` is within `τ` of `h` in value and first derivative,
and its second derivative is greater than that of `h` minus `τ`, as
`SymplecticGeometry.exists_blend_shapeFamily` asks of the family it blends. -/
theorem abs_sub_lt_of_eventuallyEq_add_const {f g h : ℝ → ℝ} {r c τ : ℝ}
    (hf : f =ᶠ[𝓝 r] fun r ↦ g r + c) (hc₀ : 0 ≤ c) (hc : c ≤ τ / 2)
    (hg : ∀ k ≤ 2, |iteratedDeriv k g r - iteratedDeriv k h r| < τ / 2) :
    |f r - h r| < τ ∧ |deriv f r - deriv h r| < τ ∧
      iteratedDeriv 2 h r - τ < iteratedDeriv 2 f r := by
  rw [hf.eq_of_nhds, hf.deriv_eq, hf.iteratedDeriv_eq 2, deriv_add_const,
    iteratedDeriv_add_const two_pos]
  obtain ⟨h₀, h₀'⟩ := abs_lt.1 (hg 0 (by norm_num))
  obtain ⟨h₁, h₁'⟩ := abs_lt.1 (hg 1 (by norm_num))
  obtain ⟨h₂, -⟩ := abs_lt.1 (hg 2 le_rfl)
  simp only [iteratedDeriv_zero, iteratedDeriv_one] at h₀ h₀' h₁ h₁'
  exact ⟨abs_lt.2 ⟨by linarith, by linarith⟩, abs_lt.2 ⟨by linarith, by linarith⟩, by linarith⟩

/-- **Closeness of a smoothed maximum to `χ`.** Let `M` and `g` be within `τ / 2` of `h` at `r`
in value and first two derivatives, and let `c ≤ τ / 4` and `δ ≤ τ / 2`. Let `f` at `r` lie
between `max (M r + c) (g r)` and `max (M r + c) (g r) + δ / 2`, have first derivative between
the smaller and the larger of those of `M` and `g`, and second derivative at least the smaller
of theirs, as `smoothedMax δ (M + c) g` does. Then at `r` the function `f` is within `τ` of `h`
in value and first derivative, and its second derivative is greater than that of `h` minus `τ`,
as `SymplecticGeometry.exists_blend_shapeFamily` asks of the family it blends. -/
theorem abs_sub_lt_of_max_le_of_le_max {f M g h : ℝ → ℝ} {r c δ τ : ℝ} (hc : c ≤ τ / 4)
    (hδ : δ ≤ τ / 2) (hM : ∀ k ≤ 2, |iteratedDeriv k M r - iteratedDeriv k h r| < τ / 2)
    (hg : ∀ k ≤ 2, |iteratedDeriv k g r - iteratedDeriv k h r| < τ / 2)
    (hv₁ : max (M r + c) (g r) ≤ f r) (hv₂ : f r ≤ max (M r + c) (g r) + δ / 2)
    (hd₁ : min (deriv M r) (deriv g r) ≤ deriv f r)
    (hd₂ : deriv f r ≤ max (deriv M r) (deriv g r))
    (hdd : min (iteratedDeriv 2 M r) (iteratedDeriv 2 g r) ≤ iteratedDeriv 2 f r) :
    |f r - h r| < τ ∧ |deriv f r - deriv h r| < τ ∧
      iteratedDeriv 2 h r - τ < iteratedDeriv 2 f r := by
  obtain ⟨m₀, m₀'⟩ := abs_lt.1 (hM 0 (by norm_num))
  obtain ⟨m₁, m₁'⟩ := abs_lt.1 (hM 1 (by norm_num))
  obtain ⟨m₂, -⟩ := abs_lt.1 (hM 2 le_rfl)
  obtain ⟨g₀, g₀'⟩ := abs_lt.1 (hg 0 (by norm_num))
  obtain ⟨g₁, g₁'⟩ := abs_lt.1 (hg 1 (by norm_num))
  obtain ⟨g₂, -⟩ := abs_lt.1 (hg 2 le_rfl)
  simp only [iteratedDeriv_zero, iteratedDeriv_one] at m₀ m₀' m₁ m₁' g₀ g₀' g₁ g₁'
  have hv : max (M r + c) (g r) < h r + 3 * τ / 4 := max_lt (by linarith) (by linarith)
  have hmax : max (deriv M r) (deriv g r) < deriv h r + τ := max_lt (by linarith) (by linarith)
  have hmin : deriv h r - τ < min (deriv M r) (deriv g r) := lt_min (by linarith) (by linarith)
  have hmin₂ : iteratedDeriv 2 h r - τ < min (iteratedDeriv 2 M r) (iteratedDeriv 2 g r) :=
    lt_min (by linarith) (by linarith)
  have := le_max_right (M r + c) (g r)
  exact ⟨abs_lt.2 ⟨by linarith, by linarith⟩, abs_lt.2 ⟨by linarith, by linarith⟩, by linarith⟩

/-- **The blend with `χ` keeps `χ` where it was.** Let `ψ` agree with `χ` near a set `S` of the
plane, and let `ρ` vanish near `r₂`. Then the blend `ρ r * ψ ℓ r + (1 - ρ r) * χ ℓ r` agrees with
`χ` near `S ∪ A ×ˢ {r₂}`, for every set `A`. -/
theorem blend_eventuallyEq_nhdsSet_union {ψ χ : ℝ → ℝ → ℝ} {ρ : ℝ → ℝ} {S : Set (ℝ × ℝ)}
    {A : Set ℝ} {r₂ : ℝ} (hψ : Function.uncurry ψ =ᶠ[𝓝ˢ S] Function.uncurry χ)
    (hρ : ρ =ᶠ[𝓝 r₂] 0) :
    (Function.uncurry fun ℓ r ↦ ρ r * ψ ℓ r + (1 - ρ r) * χ ℓ r) =ᶠ[𝓝ˢ (S ∪ A ×ˢ {r₂})]
      Function.uncurry χ := by
  rw [EventuallyEq, nhdsSet_union, eventually_sup]
  refine ⟨hψ.mono fun y hy ↦ ?_, ?_⟩
  · simp only [Function.uncurry_def] at hy ⊢
    rw [hy]
    ring
  · rw [eventually_nhdsSet_iff_forall]
    rintro x ⟨-, hx⟩
    filter_upwards [(continuous_snd.tendsto x).eventually
      (by rw [mem_singleton_iff.1 hx]; exact hρ)] with y hy
    simp [Function.uncurry_def, hy]

/-- **A strictly increasing smooth family of `i`-convex shapes with prescribed ends.** Let
`Q = [ℓ₀, ℓ₁] × [r₁, r₂]` with `0 < r₁`, `ℓ₀ < ℓ₁` and `r₁ < r₂`, and let `E` be the part
`{ℓ₀, ℓ₁} × [r₁, r₂] ∪ [ℓ₀, ℓ₁] × {r₂}` of its boundary. Let `χ : ℝ → ℝ → ℝ` be a family of
functions such that at each point of `Q`, `χ ℓ` is `C²` and an `i`-convex shape at `r`, with
value and first two `r`-derivatives continuous in `(ℓ, r)` on `Q`; such that
`χ ℓ r < χ ℓ₁ r` for `ℓ ∈ [ℓ₀, ℓ₁)` and `r ∈ [r₁, r₂]`; and such that on a neighbourhood `U`
of `E` the family is smooth in `(ℓ, r)` with `∂χ/∂ℓ > 0`. Then there is a family `ψ`, smooth in
`(ℓ, r)` on `Q`, whose members are `i`-convex shapes with `∂ψ/∂ℓ > 0` at each point of `Q`,
and which equals `χ` on a neighbourhood of `E`. -/
theorem exists_shapeFoliation {χ : ℝ → ℝ → ℝ} {ℓ₀ ℓ₁ r₁ r₂ : ℝ} {U : Set (ℝ × ℝ)}
    (hr₁ : 0 < r₁) (hℓ : ℓ₀ < ℓ₁) (hr : r₁ < r₂)
    (hC2 : ∀ x ∈ Icc ℓ₀ ℓ₁ ×ˢ Icc r₁ r₂, ContDiffAt ℝ 2 (χ x.1) x.2)
    (hc : ∀ x ∈ Icc ℓ₀ ℓ₁ ×ˢ Icc r₁ r₂, IsConvexShapeAt (χ x.1) x.2)
    (hcont : ∀ k ≤ 2, ContinuousOn (fun x : ℝ × ℝ ↦ iteratedDeriv k (χ x.1) x.2)
      (Icc ℓ₀ ℓ₁ ×ˢ Icc r₁ r₂))
    (htop : ∀ ℓ ∈ Ico ℓ₀ ℓ₁, ∀ r ∈ Icc r₁ r₂, χ ℓ r < χ ℓ₁ r)
    (hU : U ∈ 𝓝ˢ ({ℓ₀, ℓ₁} ×ˢ Icc r₁ r₂ ∪ Icc ℓ₀ ℓ₁ ×ˢ {r₂}))
    (hsmooth : ContDiffOn ℝ ∞ (Function.uncurry χ) U)
    (hmono : ∀ x ∈ U, 0 < deriv (fun ℓ' ↦ χ ℓ' x.2) x.1) :
    ∃ ψ : ℝ → ℝ → ℝ, ContDiffOn ℝ ∞ (Function.uncurry ψ) (Icc ℓ₀ ℓ₁ ×ˢ Icc r₁ r₂) ∧
      (∀ x ∈ Icc ℓ₀ ℓ₁ ×ˢ Icc r₁ r₂, IsConvexShapeAt (ψ x.1) x.2) ∧
      (∀ x ∈ Icc ℓ₀ ℓ₁ ×ˢ Icc r₁ r₂, 0 < deriv (fun ℓ' ↦ ψ ℓ' x.2) x.1) ∧
      Function.uncurry ψ =ᶠ[𝓝ˢ ({ℓ₀, ℓ₁} ×ˢ Icc r₁ r₂ ∪ Icc ℓ₀ ℓ₁ ×ˢ {r₂})]
        Function.uncurry χ := by
  set Q := Icc ℓ₀ ℓ₁ ×ˢ Icc r₁ r₂
  set E := ({ℓ₀, ℓ₁} : Set ℝ) ×ˢ Icc r₁ r₂ ∪ Icc ℓ₀ ℓ₁ ×ˢ {r₂}
  -- An open `U'` around `E`, and a thickening of `E` of size `d` inside it.
  obtain ⟨U', hU'o, hEU', hU'U⟩ := mem_nhdsSet_iff_exists.1 hU
  have hsm' : ContDiffOn ℝ ∞ (Function.uncurry χ) U' := hsmooth.mono hU'U
  have hmono' : ∀ x ∈ U', 0 < deriv (fun ℓ' ↦ χ ℓ' x.2) x.1 := fun x hx ↦ hmono x (hU'U hx)
  have hEc : IsCompact E :=
    ((Set.toFinite _).isCompact.prod isCompact_Icc).union (isCompact_Icc.prod isCompact_singleton)
  obtain ⟨d, hd, hdU⟩ := hEc.exists_cthickening_subset_open hU'o hEU'
  have hnear : ∀ x y : ℝ × ℝ, y ∈ E → |x.1 - y.1| ≤ d → |x.2 - y.2| ≤ d → x ∈ U' :=
    fun x y hy h₁ h₂ ↦ hdU (Metric.mem_cthickening_of_dist_le x y d E hy (by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      exact max_le h₁ h₂))
  -- The band `[ℓ₀, ℓ₁] × [r₃, r₂]` inside `U'`, and the cutoff `ρ` and tolerance `τ` of the
  -- blend there.
  set r₃ := max r₁ (r₂ - d)
  have hr₁₃ : r₁ ≤ r₃ := le_max_left _ _
  have hr₃₂ : r₃ < r₂ := max_lt hr (by linarith)
  have hBQ : Icc ℓ₀ ℓ₁ ×ˢ Icc r₃ r₂ ⊆ Q := fun x hx ↦ ⟨hx.1, hr₁₃.trans hx.2.1, hx.2.2⟩
  have hBU : Icc ℓ₀ ℓ₁ ×ˢ Icc r₃ r₂ ⊆ U' := fun x hx ↦
    hnear x (x.1, r₂) (Or.inr ⟨hx.1, rfl⟩) (by simp [hd.le]) (by
      rw [abs_le]
      constructor <;> linarith [hx.2.1, hx.2.2, le_max_right r₁ (r₂ - d)])
  obtain ⟨ρ, -, -, -, hρ0, τ, hτ, hblend⟩ := exists_blend_shapeFamily (r₁ := r₁) hr₃₂ hU'o hBU hsm'
    (fun x hx ↦ hc x (hBQ hx)) fun x hx ↦ hmono' x (hBU hx)
  -- A step `w` in `ℓ` over which the value and first two `r`-derivatives of `χ` move by less
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
  have hLU : Icc ℓ₀ a ×ˢ Icc r₁ r₂ ⊆ U' := fun x hx ↦
    hnear x (ℓ₀, x.2) (Or.inl ⟨Or.inl rfl, hx.2⟩) (by
      rw [abs_le]
      constructor <;> linarith [hx.1.1, hx.1.2]) (by simp [hd.le])
  have hRU : Icc b ℓ₁ ×ˢ Icc r₁ r₂ ⊆ U' := fun x hx ↦
    hnear x (ℓ₁, x.2) (Or.inl ⟨Or.inr rfl, hx.2⟩) (by
      rw [abs_le]
      constructor <;> linarith [hx.1.1, hx.1.2]) (by simp [hd.le])
  -- The gap `g` between `χ ℓ₁` and the members over `[a, b]`.
  have hχcont : ContinuousOn (fun x : ℝ × ℝ ↦ χ x.1 x.2) Q := by
    simpa [iteratedDeriv_zero] using hcont 0 (by norm_num)
  obtain ⟨g, hg, hgap⟩ : ∃ g > 0, ∀ ℓ ∈ Icc a b, ∀ r ∈ Icc r₁ r₂, χ ℓ r + g ≤ χ ℓ₁ r := by
    have hKab : IsCompact (Icc a b ×ˢ Icc r₁ r₂) := isCompact_Icc.prod isCompact_Icc
    have hcf : ContinuousOn (fun x : ℝ × ℝ ↦ χ ℓ₁ x.2 - χ x.1 x.2) (Icc a b ×ˢ Icc r₁ r₂) := by
      refine ContinuousOn.sub ?_ (hχcont.mono fun x hx ↦ ⟨hMQ hx.1, hx.2⟩)
      exact hχcont.comp (continuous_const.prodMk continuous_snd).continuousOn
        fun x hx ↦ ⟨right_mem_Icc.2 hℓ.le, hx.2⟩
    obtain ⟨x₀, hx₀, hmin⟩ := hKab.exists_isMinOn
      ⟨(a, r₁), left_mem_Icc.2 hab.le, left_mem_Icc.2 hr.le⟩ hcf
    refine ⟨χ ℓ₁ x₀.2 - χ x₀.1 x₀.2, sub_pos.2 (htop _ ⟨hMQ hx₀.1 |>.1, by linarith [hx₀.1.2]⟩
      _ hx₀.2), fun ℓ hℓ' r hr' ↦ ?_⟩
    have : χ ℓ₁ x₀.2 - χ x₀.1 x₀.2 ≤ χ ℓ₁ r - χ ℓ r :=
      hmin (show (ℓ, r) ∈ Icc a b ×ˢ Icc r₁ r₂ from ⟨hℓ', hr'⟩)
    linarith
  -- The point `c ∈ (b, ℓ₁)` from which on the members are within `g / 4` of `χ ℓ₁`.
  obtain ⟨w', hw', hu'⟩ := isCompact_Icc.exists_pos_abs_sub_lt_of_continuousOn
    (hcont 0 (by norm_num)) (by positivity : 0 < g / 4)
  set c := ℓ₁ - min w' (s / 2)
  have hbc : b < c := by
    have : min w' (s / 2) ≤ s / 2 := min_le_right _ _
    linarith
  have hcℓ : c < ℓ₁ := by
    have : 0 < min w' (s / 2) := by positivity
    linarith
  have hnearℓ₁ : ∀ ℓ ∈ Icc c ℓ₁, ∀ r ∈ Icc r₁ r₂, χ ℓ₁ r - g / 4 < χ ℓ r := by
    intro ℓ hℓ' r hr'
    have := hu' r hr' ℓ₁ (right_mem_Icc.2 hℓ.le) ℓ ⟨by linarith [hℓ'.1], hℓ'.2⟩ (by
      rw [abs_le]
      constructor <;> linarith [hℓ'.1, hℓ'.2, min_le_left w' (s / 2)])
    simp only [iteratedDeriv_zero] at this
    linarith [(abs_lt.1 this).1]
  -- The raise `q`, a smooth step from `0` at `a₀ = ℓ₀ + s / 4` to `κ` at `c`.
  set κ := min (τ / 4) (g / 4)
  have hκ0 : 0 < κ := by positivity
  have hκτ : κ ≤ τ / 4 := min_le_left _ _
  have hκg : κ ≤ g / 4 := min_le_right _ _
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
  set ε := min (q b / 2) (g / 4)
  have hε0 : 0 < ε := by positivity
  have hεq : ε < q b := (min_le_left _ _).trans_lt (by linarith)
  have hεg : ε ≤ g / 4 := min_le_right _ _
  have hab' : ∀ x ∈ Icc a b ×ˢ Icc r₁ r₂, x ∈ Q := fun x hx ↦ ⟨hMQ hx.1, hx.2⟩
  obtain ⟨C, hCs, hCc, hCℓ, ⟨hCa, hCaχ⟩, hCb, hCbup, hCblow, hCclose⟩ :=
    exists_monotone_shapeChain (τ := τ / 4) hr₁ hab hr₁₃ (fun x hx ↦ hC2 x (hab' x hx))
      (fun x hx ↦ hc x (hab' x hx))
      (fun k hk ↦ (hcont k hk).mono fun x hx ↦ hab' x hx) hU'o
      (union_subset (fun x hx ↦ hLU ⟨by rw [hx.1]; exact right_mem_Icc.2 hℓa.le, hx.2⟩)
        fun x hx ↦ hBU ⟨hMQ hx.1, hx.2⟩) hsm'
      (fun x hx ↦ hmono' x (hBU ⟨hMQ hx.1, hx.2⟩)) (by positivity) hε0
  -- The piece next to `ℓ₀`.
  obtain ⟨T₀, hT₀s, hT₀c, hT₀ℓ, hT₀ℓ₀, hT₀a, hT₀m⟩ :=
    exists_comp_add_shapeFamily (a₁ := ℓ₀ + s / 2) (by linarith) (by linarith) hU'o hLU hsm'
      (fun x hx ↦ hc x ⟨hLQ hx.1, hx.2⟩) (fun x hx ↦ hmono' x (hLU hx)) hq hqm hq₀
      fun ℓ hℓ' ↦ hq' ℓ ⟨by linarith [hℓ'.1], by linarith [hℓ'.2]⟩
  -- The piece next to `ℓ₁`, on top of `C b`.
  have hCbs : ContDiff ℝ ∞ (C b) := hCs.comp (contDiff_const.prodMk contDiff_id)
  obtain ⟨δ, ⟨-, hδτ⟩, T₁, hT₁s, hT₁c, hT₁ℓ, hT₁b, hT₁ℓ₁, hT₁m⟩ :=
    exists_smoothedMax_shapeFamily (ε := τ / 4) hbc hcℓ.le hU'o hRU hsm'
      (fun x hx ↦ hc x ⟨hRQ hx.1, hx.2⟩) (fun x hx ↦ hmono' x (hRU hx)) hCbs
      (fun r hr' ↦ hCc (b, r) ⟨right_mem_Icc.2 hab.le, hr'⟩) hq hqm (hq0 b)
      (fun ℓ hℓ' ↦ hq' ℓ ⟨by linarith [hℓ'.1], hℓ'.2⟩)
      (fun r hr' ↦ by linarith [hCblow r hr'])
      (fun ℓ hℓ' r hr' ↦ by
        obtain ⟨ℓ', hℓ'm, hle⟩ := hCbup r hr'
        linarith [hgap ℓ' hℓ'm r hr', hnearℓ₁ ℓ hℓ' r hr', hqκ ℓ])
      (by positivity)
  -- The middle piece `C ℓ + q ℓ`, and the gluing of the three pieces along `ℓ = a` and `ℓ = b`.
  set Cq : ℝ → ℝ → ℝ := fun ℓ r ↦ C ℓ r + q ℓ with hCq
  have hCqs : ContDiff ℝ ∞ (Function.uncurry Cq) := hCs.add (hq.comp contDiff_fst)
  have hTa : ∀ r ∈ Icc r₁ r₂, Function.uncurry T₀ =ᶠ[𝓝 (a, r)] Function.uncurry Cq := by
    intro r hr'
    filter_upwards [hT₀a.filter_mono (nhds_le_nhdsSet (show (a, r) ∈ ({a} : Set ℝ) ×ˢ Icc r₁ r₂
        from ⟨rfl, hr'⟩)), (continuous_fst.tendsto (a, r)).eventually hCa,
      (continuous_snd.tendsto (a, r)).eventually (hCaχ.filter_mono (nhds_le_nhdsSet hr'))]
      with y hy1 hy2 hy3
    simp only [Function.uncurry_def, hCq] at hy1 ⊢
    rw [hy1, hy2, hy3]
  have hTb : ∀ r ∈ Icc r₁ r₂, Function.uncurry T₁ =ᶠ[𝓝 (b, r)] Function.uncurry Cq := by
    intro r hr'
    filter_upwards [hT₁b.filter_mono (nhds_le_nhdsSet (show (b, r) ∈ ({b} : Set ℝ) ×ˢ Icc r₁ r₂
        from ⟨rfl, hr'⟩)), (continuous_fst.tendsto (b, r)).eventually hCb] with y hy1 hy2
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
  -- The members of `ψ'` are convex shapes with positive `ℓ`-derivative.
  have hψ'c : ∀ x ∈ Q, IsConvexShapeAt (ψ' x.1) x.2 := by
    intro x hx
    rcases hloc' x hx with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact (hT₀c x ⟨h1, hx.2⟩).congr_of_eventuallyEq h2.uncurry_left
    · exact ((hCc x ⟨h1, hx.2⟩).add_const (hq0 x.1)).congr_of_eventuallyEq
        h2.uncurry_left
    · exact (hT₁c x ⟨h1, hx.2⟩).congr_of_eventuallyEq h2.uncurry_left
  have hψ'ℓ : ∀ x ∈ Q, 0 < deriv (fun ℓ ↦ ψ' ℓ x.2) x.1 := by
    intro x hx
    rcases hloc' x hx with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h2.uncurry_right.deriv_eq]
      exact hT₀ℓ x ⟨h1, hx.2⟩
    · rw [h2.uncurry_right.deriv_eq]
      have hCd : DifferentiableAt ℝ (fun ℓ ↦ C ℓ x.2) x.1 :=
        ((hCs.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp)) x.1
      have hqd : DifferentiableAt ℝ q x.1 := (hq.differentiable (by simp)) x.1
      simp only [hCq]
      rw [deriv_fun_add hCd hqd]
      exact add_pos_of_nonneg_of_pos (hCℓ x ⟨h1, hx.2⟩)
        (hq' x.1 ⟨by linarith [h1.1], by linarith [h1.2]⟩)
    · rw [h2.uncurry_right.deriv_eq]
      exact hT₁ℓ x ⟨h1, hx.2⟩
  -- On the band, `ψ'` is close to `χ`: each piece is close to members of `χ` at most `s` away
  -- in `ℓ`, or to the chain, which is close to `χ`.
  have hclose : ∀ x ∈ Icc ℓ₀ ℓ₁ ×ˢ Icc r₃ r₂, |ψ' x.1 x.2 - χ x.1 x.2| < τ ∧
      |deriv (ψ' x.1) x.2 - deriv (χ x.1) x.2| < τ ∧
      iteratedDeriv 2 (χ x.1) x.2 - τ < iteratedDeriv 2 (ψ' x.1) x.2 := by
    intro x hx
    have hr' : x.2 ∈ Icc r₁ r₂ := (hBQ hx).2
    have hstep : ∀ ℓ ∈ Icc ℓ₀ ℓ₁, ℓ ∈ Icc (x.1 - s) (x.1 + s) → ∀ k ≤ 2,
        |iteratedDeriv k (χ ℓ) x.2 - iteratedDeriv k (χ x.1) x.2| < τ / 4 :=
      fun ℓ hℓ' hl k hk ↦ hu k hk x.2 hr' x.1 hx.1 ℓ hℓ'
        ((abs_sub_le_iff.2 ⟨by linarith [hl.2], by linarith [hl.1]⟩).trans hsw)
    rcases hloc' x (hBQ hx) with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain ⟨ℓ', hℓ'm, hT⟩ := hT₀m x ⟨h1, hr'⟩
      exact abs_sub_lt_of_eventuallyEq_add_const (h2.uncurry_left.trans hT) (hq0 x.1)
        (by linarith [hqκ x.1]) fun k hk ↦ (hstep ℓ' (hLQ hℓ'm)
          ⟨by linarith [h1.2, hℓ'm.1], by linarith [h1.1, hℓ'm.2]⟩ k hk).trans (by linarith)
    · exact abs_sub_lt_of_eventuallyEq_add_const h2.uncurry_left (hq0 x.1)
        (by linarith [hqκ x.1]) fun k hk ↦ (hCclose x ⟨h1, hx.2⟩ k hk).trans (by linarith)
    · obtain ⟨ℓ', hℓ'm, -, hv₁, hv₂, hd₁, hd₂, hdd⟩ := hT₁m x ⟨h1, hr'⟩
      rw [h2.uncurry_left.eq_of_nhds, h2.uncurry_left.deriv_eq,
        h2.uncurry_left.iteratedDeriv_eq 2]
      refine abs_sub_lt_of_max_le_of_le_max (hqκ x.1 |>.trans hκτ) (by linarith)
        (fun k hk ↦ ?_) (fun k hk ↦ ?_) hv₁ hv₂ hd₁ hd₂ hdd
      · have hCb : |iteratedDeriv k (C b) x.2 - iteratedDeriv k (χ b) x.2| < τ / 4 :=
          hCclose (b, x.2) ⟨⟨hab.le, le_rfl⟩, hx.2⟩ k hk
        have hχb := hstep b (hRQ ⟨le_rfl, hbℓ.le⟩) ⟨by linarith [h1.2], by linarith [h1.1]⟩ k hk
        exact (abs_sub_le _ (iteratedDeriv k (χ b) x.2) _).trans_lt (by linarith)
      · exact (hstep ℓ' (hRQ hℓ'm) ⟨by linarith [h1.2, hℓ'm.1], by linarith [h1.1, hℓ'm.2]⟩
          k hk).trans (by linarith)
  -- The blend with `χ` near `r₂`; it is `χ` near `{ℓ₀, ℓ₁} × [r₁, r₂]`, where `ψ'` is.
  obtain ⟨hψs, hψc, hψℓ⟩ := hblend ψ' hψ's hψ'c hψ'ℓ hclose
  refine ⟨fun ℓ r ↦ ρ r * ψ' ℓ r + (1 - ρ r) * χ ℓ r, hψs.mono fun x hx ↦ ?_, hψc, hψℓ,
    blend_eventuallyEq_nhdsSet_union ?_ hρ0⟩
  · rcases lt_or_ge x.2 r₃ with h | h
    · exact Or.inl ⟨mem_univ _, h⟩
    · exact Or.inr (hBU ⟨hx.1, h, hx.2.2⟩)
  rw [insert_eq, union_prod, EventuallyEq, nhdsSet_union, eventually_sup]
  exact ⟨((hψ'₀.filter_mono (nhdsSet_mono (prod_mono (singleton_subset_iff.2
      ⟨le_rfl, hℓa.le⟩) le_rfl))).trans hT₀ℓ₀),
    ((hψ'₁.filter_mono (nhdsSet_mono (prod_mono (singleton_subset_iff.2
      ⟨hbℓ.le, le_rfl⟩) le_rfl))).trans hT₁ℓ₁)⟩

end SymplecticGeometry
