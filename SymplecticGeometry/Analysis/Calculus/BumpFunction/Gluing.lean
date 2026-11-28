/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Topology.NhdsSet
import SymplecticGeometry.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Gluing smooth families of functions along two lines `ℓ = a` and `ℓ = b`

Let `T₀`, `T` and `T₁` be families `ℝ → ℝ → F`, of class `Cⁿ` on `ℝ²`, such that `T₀` agrees
with `T` near each point of `{a} × K` and `T₁` agrees with `T` near each point of `{b} × K`,
where `a < b` and `K` is compact. Then one `Cⁿ` family agrees with `T₀` near
`[ℓ₀, a] × K`, with `T` near `[a, b] × K`, and with `T₁` near `[b, ℓ₁] × K`
(`SymplecticGeometry.exists_contDiff_eventuallyEq_of_eventuallyEq_Icc`).

The family that is `T₀` for `ℓ ≤ a`, `T` for `a < ℓ ≤ b` and `T₁` for `b < ℓ` agrees near each
point of the three rectangles with the piece of that rectangle, so it is `Cⁿ` on the open set
where it agrees locally with one of the pieces. The library's
`ContDiffOn.exists_contDiff_eventuallyEq_nhdsSet`, which rests on Tau Ceti's
`ContDiffOn.exists_contDiff_eventuallyEq_on_isCompact`, then gives a `Cⁿ` family on `ℝ²` that
agrees with it near the union of the rectangles.
-/

public section

namespace SymplecticGeometry

open Set Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Gluing three `Cⁿ` families along `ℓ = a` and `ℓ = b`.** Let `T₀`, `T` and `T₁` be
families `ℝ → ℝ → F` of class `Cⁿ` on `ℝ²`, let `a < b` and let `K` be compact, and suppose
that `T₀` equals `T` near each point of `{a} × K` and `T₁` equals `T` near each point of
`{b} × K`. Then there is a family `ψ` of class `Cⁿ` on `ℝ²` that equals `T₀` near
`[ℓ₀, a] × K`, `T` near `[a, b] × K` and `T₁` near `[b, ℓ₁] × K`. -/
theorem exists_contDiff_eventuallyEq_of_eventuallyEq_Icc {n : ℕ∞} {T₀ T T₁ : ℝ → ℝ → F}
    {ℓ₀ a b ℓ₁ : ℝ} {K : Set ℝ} (hab : a < b) (hK : IsCompact K)
    (hT₀ : ContDiff ℝ n (Function.uncurry T₀)) (hT : ContDiff ℝ n (Function.uncurry T))
    (hT₁ : ContDiff ℝ n (Function.uncurry T₁))
    (hTa : ∀ r ∈ K, Function.uncurry T₀ =ᶠ[𝓝 (a, r)] Function.uncurry T)
    (hTb : ∀ r ∈ K, Function.uncurry T₁ =ᶠ[𝓝 (b, r)] Function.uncurry T) :
    ∃ ψ : ℝ → ℝ → F, ContDiff ℝ n (Function.uncurry ψ) ∧
      Function.uncurry ψ =ᶠ[𝓝ˢ (Icc ℓ₀ a ×ˢ K)] Function.uncurry T₀ ∧
      Function.uncurry ψ =ᶠ[𝓝ˢ (Icc a b ×ˢ K)] Function.uncurry T ∧
      Function.uncurry ψ =ᶠ[𝓝ˢ (Icc b ℓ₁ ×ˢ K)] Function.uncurry T₁ := by
  -- The glued family `P`.
  set P : ℝ → ℝ → F := fun ℓ r ↦ if ℓ ≤ a then T₀ ℓ r else if ℓ ≤ b then T ℓ r else T₁ ℓ r
    with hP
  -- Away from the lines `ℓ = a` and `ℓ = b`, `P` is one of the pieces near each point.
  have hlt : ∀ x : ℝ × ℝ, x.1 < a → Function.uncurry P =ᶠ[𝓝 x] Function.uncurry T₀ :=
    fun x hx ↦ by
      filter_upwards [(continuous_fst.tendsto x).eventually (Iio_mem_nhds hx)] with y hy
      simp [hP, Function.uncurry_def, (mem_Iio.1 hy).le]
  have hmid : ∀ x : ℝ × ℝ, a < x.1 → x.1 < b →
      Function.uncurry P =ᶠ[𝓝 x] Function.uncurry T := fun x h₁ h₂ ↦ by
    filter_upwards [(continuous_fst.tendsto x).eventually (Ioi_mem_nhds h₁),
      (continuous_fst.tendsto x).eventually (Iio_mem_nhds h₂)] with y hy₁ hy₂
    simp [hP, Function.uncurry_def, not_le.2 (mem_Ioi.1 hy₁), (mem_Iio.1 hy₂).le]
  have hgt : ∀ x : ℝ × ℝ, b < x.1 → Function.uncurry P =ᶠ[𝓝 x] Function.uncurry T₁ :=
    fun x hx ↦ by
      filter_upwards [(continuous_fst.tendsto x).eventually (Ioi_mem_nhds hx)] with y hy
      simp [hP, Function.uncurry_def, not_le.2 (mem_Ioi.1 hy),
        not_le.2 (hab.trans (mem_Ioi.1 hy))]
  -- On the lines, `P` is `T₀` near `{a} × K` and `T₁` near `{b} × K`.
  have ha : ∀ r ∈ K, Function.uncurry P =ᶠ[𝓝 (a, r)] Function.uncurry T₀ := fun r hr ↦ by
    filter_upwards [hTa r hr, (continuous_fst.tendsto (a, r)).eventually (Iio_mem_nhds hab)]
      with y hy hyb
    by_cases h : y.1 ≤ a
    · simp [hP, Function.uncurry_def, h]
    · simp only [Function.uncurry_def] at hy ⊢
      simp [hP, h, (mem_Iio.1 hyb).le, hy]
  have hb : ∀ r ∈ K, Function.uncurry P =ᶠ[𝓝 (b, r)] Function.uncurry T₁ := fun r hr ↦ by
    filter_upwards [hTb r hr, (continuous_fst.tendsto (b, r)).eventually (Ioi_mem_nhds hab)]
      with y hy hya
    simp only [Function.uncurry_def] at hy ⊢
    by_cases h : y.1 ≤ b
    · simp [hP, h, not_le.2 (mem_Ioi.1 hya), hy]
    · simp [hP, h, not_le.2 (mem_Ioi.1 hya)]
  -- Near each point of a rectangle, `P` is the piece of that rectangle.
  have h₀ : ∀ x ∈ Icc ℓ₀ a ×ˢ K, Function.uncurry P =ᶠ[𝓝 x] Function.uncurry T₀ := by
    rintro ⟨ℓ, r⟩ ⟨hℓ, hr⟩
    simp only at hℓ hr
    rcases hℓ.2.lt_or_eq with h | h
    · exact hlt _ h
    · rw [h]
      exact ha r hr
  have hm : ∀ x ∈ Icc a b ×ˢ K, Function.uncurry P =ᶠ[𝓝 x] Function.uncurry T := by
    rintro ⟨ℓ, r⟩ ⟨hℓ, hr⟩
    simp only at hℓ hr
    rcases hℓ.1.lt_or_eq with h | h
    · rcases hℓ.2.lt_or_eq with h' | h'
      · exact hmid _ h h'
      · rw [h']
        exact (hb r hr).trans (hTb r hr)
    · rw [← h]
      exact (ha r hr).trans (hTa r hr)
  have h₁ : ∀ x ∈ Icc b ℓ₁ ×ˢ K, Function.uncurry P =ᶠ[𝓝 x] Function.uncurry T₁ := by
    rintro ⟨ℓ, r⟩ ⟨hℓ, hr⟩
    simp only at hℓ hr
    rcases hℓ.1.lt_or_eq with h | h
    · exact hgt _ h
    · rw [← h]
      exact hb r hr
  -- `P` is `Cⁿ` on the open set `W` where it agrees locally with a piece, and `W` contains the
  -- rectangles; extend it from near them.
  set W := {y | Function.uncurry P =ᶠ[𝓝 y] Function.uncurry T₀} ∪
    {y | Function.uncurry P =ᶠ[𝓝 y] Function.uncurry T} ∪
    {y | Function.uncurry P =ᶠ[𝓝 y] Function.uncurry T₁}
  have hWo : IsOpen W :=
    (isOpen_setOfPred_eventually_nhds.union isOpen_setOfPred_eventually_nhds).union
      isOpen_setOfPred_eventually_nhds
  have hQW : Icc ℓ₀ a ×ˢ K ∪ Icc a b ×ˢ K ∪ Icc b ℓ₁ ×ˢ K ⊆ W :=
    union_subset_union (union_subset_union h₀ hm) h₁
  have hPW : ContDiffOn ℝ n (Function.uncurry P) W := fun y hy ↦ by
    rcases hy with (h | h) | h
    exacts [(hT₀.contDiffAt.congr_of_eventuallyEq h).contDiffWithinAt,
      (hT.contDiffAt.congr_of_eventuallyEq h).contDiffWithinAt,
      (hT₁.contDiffAt.congr_of_eventuallyEq h).contDiffWithinAt]
  obtain ⟨ψ₀, hψ₀, hψ₀P⟩ := hPW.exists_contDiff_eventuallyEq_nhdsSet
    (((isCompact_Icc.prod hK).union (isCompact_Icc.prod hK)).union (isCompact_Icc.prod hK))
    (hWo.mem_nhdsSet.2 hQW)
  refine ⟨Function.curry ψ₀, ?_, ?_, ?_, ?_⟩ <;> rw [Function.uncurry_curry]
  · exact hψ₀
  · exact (hψ₀P.filter_mono (nhdsSet_mono (subset_union_left.trans subset_union_left))).trans
      (eventually_nhdsSet_iff_forall.2 h₀)
  · exact (hψ₀P.filter_mono (nhdsSet_mono (subset_union_right.trans subset_union_left))).trans
      (eventually_nhdsSet_iff_forall.2 hm)
  · exact (hψ₀P.filter_mono (nhdsSet_mono subset_union_right)).trans
      (eventually_nhdsSet_iff_forall.2 h₁)

end SymplecticGeometry

end
