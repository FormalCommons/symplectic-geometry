/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Analysis.SpecialFunctions.SmoothedMax
public import SymplecticGeometry.Geometry.Manifold.Complex.JConvex.Surround.ConvexShape.Basic

import TauCeti.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Analysis.Calculus.ContDiff.Prod
import SymplecticGeometry.Analysis.Calculus.Deriv.Mul
import SymplecticGeometry.Analysis.Calculus.IteratedDeriv.Lemmas
import SymplecticGeometry.Analysis.Calculus.IteratedDeriv.Prod
import SymplecticGeometry.Analysis.SpecialFunctions.SmoothTransition.Basic
import SymplecticGeometry.Geometry.Manifold.Complex.JConvex.Surround.ConvexShape.SmoothedMax

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
  `λ' > 0`; on `[c, ℓ₁]` because there `χ ℓ > M + q ℓ` and `λ' > 0`. For small `δ` the members
  are `i`-convex shapes by
  `SymplecticGeometry.exists_forall_isConvexShapeAt_smoothedMax`, applied to a globally smooth
  family that agrees with `χ` near the rectangle (Tau Ceti's
  `ContDiffOn.exists_contDiff_eventuallyEq_on_isCompact`). The family is `M + q ℓ` near
  `ℓ = b` and `χ` near `ℓ = ℓ₁`, and at each point it is the smoothed maximum of `M + q ℓ` and a
  member of `χ`, which bounds its value and its first two `r`-derivatives by theirs.
* `SymplecticGeometry.exists_comp_add_shapeFamily`: the piece next to the end `ℓ₀` of the
  parameter interval `[ℓ₀, a]`. It is `T ℓ r = χ (λ ℓ) r + q ℓ`, where `q` is smooth,
  nondecreasing, `0` near `ℓ₀` and with `q' > 0` on `[a₁, a]`, and `λ` is a smooth monotone map
  that is the identity up to a point of `(ℓ₀, a₁)`, equal to `a` from a point `a'' ∈ (a₁, a)`
  on, and with positive derivative below `a''`
  (`Real.exists_contDiff_monotone_eqOn_id_Iic_eqOn_const_Ici_of_le`). The members are shapes
  by `SymplecticGeometry.IsConvexShapeAt.add_const`, since `q ≥ 0` on `[ℓ₀, ∞)`; the
  `ℓ`-derivative `∂χ/∂ℓ (λ ℓ) · λ' ℓ + q' ℓ` is positive, by its first term below `a''` and by
  its second on `[a'', a]`. The family is `χ` near `ℓ = ℓ₀` and `χ a + q ℓ` near `ℓ = a`, where
  it meets the family of `SymplecticGeometry.exists_monotone_shapeChain`.
* `SymplecticGeometry.exists_blend_shapeFamily`: the blend with `χ` near the end `r₂` of the
  `r`-interval. On a band `[ℓ₀, ℓ₁] × [r₃, r₂]` where `χ` is a smooth family of shapes with
  `∂χ/∂ℓ > 0`, a cutoff `ρ` in `r`, `1` up to `r₃` and `0` near `r₂`
  (`SymplecticGeometry.exists_contDiff_antitone_cutoff_mul_abs_deriv_le_deriv_deriv`), and a
  tolerance `τ > 0` are chosen first. Then any smooth family
  `ψ₀` of shapes with `∂ψ₀/∂ℓ > 0` that is `τ`-close to `χ` on the band, in value and first
  `r`-derivative and from below in second `r`-derivative, gives the family
  `ρ r * ψ₀ ℓ r + (1 - ρ r) * χ ℓ r`. Its members are shapes by the one-sided blend lemma of
  `ConvexShape/Basic.lean`, and its `ℓ`-derivative is a convex combination of `∂ψ₀/∂ℓ` and `∂χ/∂ℓ`.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Proposition 3.25 and Corollary 4.29.
-/

public section

noncomputable section

namespace SymplecticGeometry

open Set Filter Topology
open scoped ContDiff

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
  have hbℓ : b ≤ ℓ₁ := hbc.le.trans hcℓ
  -- A globally smooth `χ'` that agrees with `uncurry χ` on an open set `O` containing the
  -- rectangle.
  obtain ⟨χ', hχ', -, -, -, hχ'eq⟩ := hχ.exists_contDiff_eventuallyEq_on_isCompact
    (isCompact_Icc.prod isCompact_Icc) hU hRU
  set O := interior {x | χ' x = Function.uncurry χ x}
  have hO : IsOpen O := isOpen_interior
  have hRO : Icc b ℓ₁ ×ˢ Icc r₁ r₂ ⊆ O := fun x hx ↦ mem_interior_iff_mem_nhds.2 (hχ'eq x hx)
  have hloc : ∀ x ∈ O, χ' =ᶠ[𝓝 x] Function.uncurry χ := fun x hx ↦
    mem_interior_iff_mem_nhds.1 hx
  have hval : ∀ x ∈ O, χ' x = χ x.1 x.2 := fun x hx ↦ interior_subset hx
  have hsliceR : ∀ x ∈ O, (fun r ↦ χ' (x.1, r)) =ᶠ[𝓝 x.2] χ x.1 := fun x hx ↦
    (hloc x hx).comp_tendsto (Continuous.tendsto (by fun_prop) x.2)
  have hsliceL : ∀ x ∈ O, (fun ℓ ↦ χ' (ℓ, x.2)) =ᶠ[𝓝 x.1] fun ℓ ↦ χ ℓ x.2 := fun x hx ↦
    (hloc x hx).comp_tendsto (Continuous.tendsto (by fun_prop) x.1)
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
      have := hval (b, r) (hRO ⟨left_mem_Icc.2 hbℓ, hr'⟩)
      simp only at this ⊢
      linarith [hgb r hr']
  obtain ⟨g₁, hg₁, hg₁le⟩ := isCompact_Icc.exists_forall_le' (a := (0 : ℝ))
    (f := fun r ↦ χ' (ℓ₁, r) - (M r + q ℓ₁)) (s := Icc r₁ r₂) (by fun_prop) fun r hr' ↦ by
      have := hval (ℓ₁, r) (hRO ⟨right_mem_Icc.2 hbℓ, hr'⟩)
      simp only at this ⊢
      linarith [hgc ℓ₁ ⟨hcℓ, le_rfl⟩ r hr']
  -- The width `δ₀` below which the smoothed maxima are `i`-convex shapes.
  have hFM : ContDiff ℝ ∞ fun x : ℝ × ℝ ↦ M x.2 + q x.1 :=
    (hM.comp contDiff_snd).add (hq.comp contDiff_fst)
  have hFA : ContDiff ℝ ∞ fun x : ℝ × ℝ ↦ χ' (L x.1, x.2) :=
    hχ'.comp ((hLs.comp contDiff_fst).prodMk contDiff_snd)
  have hA2 : ∀ p : ℝ, ContDiff ℝ 2 fun r ↦ χ' (L p, r) := fun p ↦
    (hFA.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)
  have hM2 : ∀ p : ℝ, ContDiff ℝ 2 fun r ↦ M r + q p := fun p ↦
    (hFM.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)
  have hAc : ∀ p ∈ Icc b ℓ₁, ∀ r ∈ Icc r₁ r₂, IsConvexShapeAt (fun r ↦ χ' (L p, r)) r :=
    fun p hp r hr' ↦ (hχc (L p, r) ⟨hLmem p hp, hr'⟩).congr_of_eventuallyEq
      (hsliceR (L p, r) (hRO ⟨hLmem p hp, hr'⟩))
  obtain ⟨δ₀, hδ₀, hconv⟩ := exists_forall_isConvexShapeAt_smoothedMax (P := ℝ)
    (K := Icc b ℓ₁) isCompact_Icc (M := fun p r ↦ M r + q p) (A := fun p r ↦ χ' (L p, r))
    (r₁ := r₁) (r₂ := r₂) (fun p _ _ _ ↦ (hM2 p).contDiffAt) (fun p _ _ _ ↦ (hA2 p).contDiffAt)
    (fun p hp r hr' ↦ (hMc r hr').add_const (hqb.trans (hqm hp.1))) hAc
    (fun _ _ _ _ ↦ (hFM.contDiffAt.continuousAt_iteratedDeriv_prod_right
      (by exact_mod_cast le_top)).continuousWithinAt)
    (fun _ _ _ _ ↦ (hFA.contDiffAt.continuousAt_iteratedDeriv_prod_right
      (by exact_mod_cast le_top)).continuousWithinAt)
  set δ := min (min ε δ₀) (min (g₀ / 2) (g₁ / 2))
  have hδ : 0 < δ := lt_min (lt_min hε hδ₀) (lt_min (half_pos hg₀) (half_pos hg₁))
  have hδε : δ ≤ ε := (min_le_left _ _).trans (min_le_left _ _)
  have hδδ₀ : δ ≤ δ₀ := (min_le_left _ _).trans (min_le_right _ _)
  have hδg₀ : δ < g₀ := (min_le_right _ _).trans_lt ((min_le_left _ _).trans_lt (half_lt_self hg₀))
  have hδg₁ : δ < g₁ :=
    (min_le_right _ _).trans_lt ((min_le_right _ _).trans_lt (half_lt_self hg₁))
  refine ⟨δ, ⟨hδ, hδε⟩, fun ℓ r ↦ smoothedMax δ (M r + q ℓ) (χ' (L ℓ, r)),
    (contDiff_smoothedMax δ).comp (hFM.prodMk hFA),
    fun x hx ↦ hconv δ ⟨hδ, hδδ₀⟩ x.1 hx.1 x.2 hx.2, ?_, ?_, ?_, ?_⟩
  · -- The `ℓ`-derivative.
    intro x hx
    obtain ⟨⟨hb, hℓ⟩, hr'⟩ := hx
    have hx₁ : (L x.1, x.2) ∈ O := hRO ⟨hLmem x.1 ⟨hb, hℓ⟩, hr'⟩
    have hχd : HasDerivAt (fun ℓ ↦ χ' (ℓ, x.2)) (deriv (fun ℓ ↦ χ ℓ x.2) (L x.1)) (L x.1) := by
      have hd : DifferentiableAt ℝ (fun ℓ ↦ χ' (ℓ, x.2)) (L x.1) :=
        (hχ'.comp (contDiff_id.prodMk contDiff_const)).differentiable
          (by simp) _
      have := hd.hasDerivAt
      rwa [(hsliceL _ hx₁).deriv_eq] at this
    have hpos : 0 < deriv (fun ℓ ↦ χ ℓ x.2) (L x.1) := hχℓ (L x.1, x.2) ⟨hLmem x.1 ⟨hb, hℓ⟩, hr'⟩
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
          rw [← hxb, hLb, hval (b, x.2) (hRO ⟨left_mem_Icc.2 hbℓ, hr'⟩)] at h
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
    · have hsub : {ℓ₁} ×ˢ Icc r₁ r₂ ⊆ Ioi b' ×ˢ univ ∩ O := by
        rintro ⟨ℓ, r⟩ ⟨hx₁, hx₂⟩
        rw [mem_singleton_iff] at hx₁
        subst hx₁
        exact ⟨⟨show b' < ℓ by linarith, mem_univ _⟩, hRO ⟨right_mem_Icc.2 hbℓ, hx₂⟩⟩
      filter_upwards [((isOpen_Ioi.prod isOpen_univ).inter hO).mem_nhdsSet.2 hsub] with x hx
      rw [hLid x.1 hx.1.1.le, Function.uncurry_def]
      exact hval x hx.2
  · -- The pointwise comparison with `M + q ℓ` and `χ (L ℓ)`.
    intro x hx
    have hx₁ : (L x.1, x.2) ∈ O := hRO ⟨hLmem x.1 hx.1, hx.2⟩
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
  -- A globally smooth `χ'` that agrees with `uncurry χ` on an open set `O` containing the
  -- rectangle.
  obtain ⟨χ', hχ', -, -, -, hχ'eq⟩ := hχ.exists_contDiff_eventuallyEq_on_isCompact
    (isCompact_Icc.prod isCompact_Icc) hU hRU
  set O := interior {x | χ' x = Function.uncurry χ x}
  have hO : IsOpen O := isOpen_interior
  have hRO : Icc ℓ₀ a ×ˢ Icc r₁ r₂ ⊆ O := fun x hx ↦ mem_interior_iff_mem_nhds.2 (hχ'eq x hx)
  have hloc : ∀ x ∈ O, χ' =ᶠ[𝓝 x] Function.uncurry χ := fun x hx ↦
    mem_interior_iff_mem_nhds.1 hx
  have hval : ∀ x ∈ O, χ' x = χ x.1 x.2 := fun x hx ↦ interior_subset hx
  have hsliceR : ∀ x ∈ O, (fun r ↦ χ' (x.1, r)) =ᶠ[𝓝 x.2] χ x.1 := fun x hx ↦
    (hloc x hx).comp_tendsto (Continuous.tendsto (by fun_prop) x.2)
  have hsliceL : ∀ x ∈ O, (fun ℓ ↦ χ' (ℓ, x.2)) =ᶠ[𝓝 x.1] fun ℓ ↦ χ ℓ x.2 := fun x hx ↦
    (hloc x hx).comp_tendsto (Continuous.tendsto (by fun_prop) x.1)
  -- The reparametrization `L`: the identity up to `a'`, equal to `a` from `a''` on.
  set a' := (ℓ₀ + a₁) / 2 with ha'
  set a'' := (a₁ + a) / 2 with ha''
  have hℓa' : ℓ₀ < a' := by linarith [ha']
  have ha'a'' : a' < a'' := by linarith [ha', ha'']
  have ha₁a'' : a₁ < a'' := by linarith [ha'']
  obtain ⟨L, hLs, hLm, hLid, hLa, hLle, hL'⟩ :=
    Real.exists_contDiff_monotone_eqOn_id_Iic_eqOn_const_Ici_of_le ha'a''
      (show a'' ≤ a by linarith [ha''])
  have hLℓ₀ : L ℓ₀ = ℓ₀ := hLid (mem_Iic.2 hℓa'.le)
  have hLmem : ∀ ℓ ∈ Icc ℓ₀ a, L ℓ ∈ Icc ℓ₀ a := fun ℓ hℓ ↦
    ⟨hLℓ₀ ▸ hLm hℓ.1, hLle ℓ⟩
  have hqnn : ∀ ℓ, ℓ₀ ≤ ℓ → 0 ≤ q ℓ := fun ℓ hℓ ↦ hq₀.eq_of_nhds ▸ hqm hℓ
  refine ⟨fun ℓ r ↦ χ' (L ℓ, r) + q ℓ,
    (hχ'.comp ((hLs.comp contDiff_fst).prodMk contDiff_snd)).add (hq.comp contDiff_fst),
    fun x hx ↦ ?_, fun x hx ↦ ?_, ?_, ?_, fun x hx ↦ ⟨L x.1, hLmem x.1 hx.1, ?_⟩⟩
  · -- The members are `i`-convex shapes.
    have hx₁ : (L x.1, x.2) ∈ O := hRO ⟨hLmem x.1 hx.1, hx.2⟩
    exact ((hχc (L x.1, x.2) ⟨hLmem x.1 hx.1, hx.2⟩).congr_of_eventuallyEq
      (hsliceR _ hx₁)).add_const (hqnn x.1 hx.1.1)
  · -- The `ℓ`-derivative.
    obtain ⟨⟨hℓ₀x, hxa⟩, hr'⟩ := hx
    have hx₁ : (L x.1, x.2) ∈ O := hRO ⟨hLmem x.1 ⟨hℓ₀x, hxa⟩, hr'⟩
    have hχd : HasDerivAt (fun ℓ ↦ χ' (ℓ, x.2)) (deriv (fun ℓ ↦ χ ℓ x.2) (L x.1)) (L x.1) := by
      have hd : DifferentiableAt ℝ (fun ℓ ↦ χ' (ℓ, x.2)) (L x.1) :=
        (hχ'.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) _
      rw [← (hsliceL _ hx₁).deriv_eq]
      exact hd.hasDerivAt
    have hpos : 0 < deriv (fun ℓ ↦ χ ℓ x.2) (L x.1) :=
      hχℓ (L x.1, x.2) ⟨hLmem x.1 ⟨hℓ₀x, hxa⟩, hr'⟩
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
    have hsub : {ℓ₀} ×ˢ Icc r₁ r₂ ⊆ (t ∩ Iio a') ×ˢ univ ∩ O := by
      rintro ⟨ℓ, r⟩ ⟨hx₁, hx₂⟩
      rw [mem_singleton_iff] at hx₁
      subst hx₁
      exact ⟨⟨⟨hℓ₀t, hℓa'⟩, mem_univ _⟩, hRO ⟨left_mem_Icc.2 (by linarith), hx₂⟩⟩
    filter_upwards [(((ht.inter isOpen_Iio).prod isOpen_univ).inter hO).mem_nhdsSet.2 hsub]
      with x hx
    simp only [Function.uncurry_def]
    rw [hLid (mem_Iic.2 hx.1.1.2.le), id, htq _ hx.1.1.1, add_zero]
    exact hval x hx.2
  · -- Near `a`, the family is `χ a + q`.
    have hsub : {a} ×ˢ Icc r₁ r₂ ⊆ Ioi a'' ×ˢ {r | (a, r) ∈ O} := by
      rintro ⟨ℓ, r⟩ ⟨hx₁, hx₂⟩
      rw [mem_singleton_iff] at hx₁
      subst hx₁
      exact ⟨show a'' < ℓ by linarith [ha''], hRO ⟨right_mem_Icc.2 (by linarith), hx₂⟩⟩
    filter_upwards [(isOpen_Ioi.prod (hO.preimage (by fun_prop))).mem_nhdsSet.2 hsub]
      with x hx
    simp only [Function.uncurry_def]
    rw [hLa (mem_Ici.2 (le_of_lt hx.1))]
    exact congrArg (· + q x.1) (hval _ hx.2)
  · -- At each point, the family is a member of `χ` raised by `q ℓ`.
    exact (hsliceR (L x.1, x.2) (hRO ⟨hLmem x.1 hx.1, hx.2⟩)).mono fun r hr' ↦
      congrArg (· + q x.1) hr'

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
  · -- Smoothness: below `r₃` the blend is `ψ₀`, and on `V` both terms are smooth.
    refine fun x hx ↦ ContDiffAt.contDiffWithinAt ?_
    rcases hx with ⟨-, hx⟩ | hx
    · refine hψ₀.contDiffAt.congr_of_eventuallyEq ?_
      filter_upwards [(isOpen_univ.prod isOpen_Iio).mem_nhds ⟨mem_univ x.1, hx⟩] with y hy
      simp [hρ1 (mem_Iic.2 (mem_Iio.1 hy.2).le), Function.uncurry_def]
    · have hχV : ContDiffAt ℝ ∞ (Function.uncurry χ) x := hχ.contDiffAt (hV.mem_nhds hx)
      have hρ' : ContDiffAt ℝ ∞ (fun y : ℝ × ℝ ↦ ρ y.2) x := (hρs.comp contDiff_snd).contDiffAt
      exact (hρ'.mul hψ₀.contDiffAt).add ((contDiffAt_const.sub hρ').mul hχV)
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

end SymplecticGeometry
