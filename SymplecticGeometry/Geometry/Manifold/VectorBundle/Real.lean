/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Analysis.SpecialFunctions.SmoothTransition
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.LocalFrame

/-!
# Gluing smooth local frames of a vector bundle over the line

This file proves the gluing step behind the smooth triviality of vector bundles over `ℝ`.

Two local frames `s` on `U` and `s'` on `U'` glue along a map `φ` into their overlap that is the
identity on one side (`IsLocalFrameOn.exists_isLocalFrameOn_union`). Over `ℝ`, with `c < c₁ < b`
and `Set.Ioo c b ⊆ U ∩ U'`, a map `φ` that is the identity up to `c₁` and maps `Ioi c` into
`Ioo c b` (`Real.exists_contDiff_eq_self_mapsTo_Ioo`) gives a
frame on `(U ∩ Iio c₁) ∪ (U' ∩ Ioi c)` that is `s` on `U ∩ Iio c₁`
(`IsLocalFrameOn.exists_isLocalFrameOn_union_Iio`), and the mirror image gives one on
`(U ∩ Iio b) ∪ (U' ∩ Ioi c₁)` that is `s'` on `U' ∩ Ioi c₁`
(`IsLocalFrameOn.exists_isLocalFrameOn_union_Ioi`). For intervals `U = Ioo a b` and
`U' = Ioo c d` with `a ≤ c` and `b ≤ d` the union is `Ioo a d`
(`IsLocalFrameOn.exists_isLocalFrameOn_Ioo_eqOn_Ioo_left`,
`IsLocalFrameOn.exists_isLocalFrameOn_Ioo_eqOn_Ioo_right`).

## Main results

* `IsLocalFrameOn.exists_isLocalFrameOn_union_Iio`,
  `IsLocalFrameOn.exists_isLocalFrameOn_union_Ioi`:
  over `ℝ`, a frame on the union that keeps the first, resp. the second, frame on its side.
* `IsLocalFrameOn.exists_isLocalFrameOn_Ioo_eqOn_Ioo_left`,
  `IsLocalFrameOn.exists_isLocalFrameOn_Ioo_eqOn_Ioo_right`: the same for two open intervals.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Theorem 7.3.1.
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963.
-/

public section

open Bundle Set
open scoped Manifold ContDiff

namespace IsLocalFrameOn

section Real

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {T : ℝ → Type*} [TopologicalSpace (TotalSpace F T)]
  [∀ x, AddCommGroup (T x)] [∀ x, Module ℝ (T x)] [∀ x, TopologicalSpace (T x)]
  [FiberBundle F T] [VectorBundle ℝ F T] [ContMDiffVectorBundle ∞ F T 𝓘(ℝ)]
  {ι : Type*} [Finite ι] {s s' : ι → Π x, T x} {U U' : Set ℝ} {c c₁ b : ℝ}

/-- Over `ℝ`, smooth local frames `s` on an open set `U` and `s'` on an open set `U'` with
`Ioo c b ⊆ U ∩ U'` glue, for `c < c₁ < b`, to a smooth local frame on
`(U ∩ Iio c₁) ∪ (U' ∩ Ioi c)` that is `s` on `U ∩ Iio c₁`. -/
theorem exists_isLocalFrameOn_union_Iio (hs : IsLocalFrameOn 𝓘(ℝ) F ∞ s U)
    (hs' : IsLocalFrameOn 𝓘(ℝ) F ∞ s' U') (hU : IsOpen U) (hU' : IsOpen U') (hc : c < c₁)
    (hb : c₁ < b) (hcb : Ioo c b ⊆ U ∩ U') :
    ∃ t : ι → Π x, T x, IsLocalFrameOn 𝓘(ℝ) F ∞ t (U ∩ Iio c₁ ∪ U' ∩ Ioi c) ∧
      ∀ i, ∀ x ∈ U ∩ Iio c₁, t i x = s i x := by
  obtain ⟨φ, hφ, hφid, hφmaps, -⟩ := Real.exists_contDiff_eq_self_mapsTo_Ioo hc hb
  exact hs.exists_isLocalFrameOn_union hs' hU hU' (hU.inter isOpen_Iio) (hU'.inter isOpen_Ioi)
    inter_subset_left inter_subset_left hφ.contMDiff.contMDiffOn
    (fun x hx ↦ hcb (hφmaps hx.2)) fun x hx ↦ hφid x hx.1.2.le

/-- Over `ℝ`, smooth local frames `s` on an open set `U` and `s'` on an open set `U'` with
`Ioo c b ⊆ U ∩ U'` glue, for `c < c₁ < b`, to a smooth local frame on
`(U ∩ Iio b) ∪ (U' ∩ Ioi c₁)` that is `s'` on `U' ∩ Ioi c₁`. This is the mirror image of
`IsLocalFrameOn.exists_isLocalFrameOn_union_Iio`. -/
theorem exists_isLocalFrameOn_union_Ioi (hs : IsLocalFrameOn 𝓘(ℝ) F ∞ s U)
    (hs' : IsLocalFrameOn 𝓘(ℝ) F ∞ s' U') (hU : IsOpen U) (hU' : IsOpen U') (hc : c < c₁)
    (hb : c₁ < b) (hcb : Ioo c b ⊆ U ∩ U') :
    ∃ t : ι → Π x, T x, IsLocalFrameOn 𝓘(ℝ) F ∞ t (U ∩ Iio b ∪ U' ∩ Ioi c₁) ∧
      ∀ i, ∀ x ∈ U' ∩ Ioi c₁, t i x = s' i x := by
  obtain ⟨φ, hφ, hφid, hφmaps, -⟩ :=
    Real.exists_contDiff_eq_self_mapsTo_Ioo (neg_lt_neg hb) (neg_lt_neg hc)
  have hψ : ContDiff ℝ ∞ fun x ↦ -φ (-x) := by fun_prop
  rw [union_comm]
  refine hs'.exists_isLocalFrameOn_union hs hU' hU (hU'.inter isOpen_Ioi) (hU.inter isOpen_Iio)
    inter_subset_left inter_subset_left hψ.contMDiff.contMDiffOn (fun x hx ↦ ?_) fun x hx ↦ ?_
  · have h := hφmaps (mem_Ioi.2 (neg_lt_neg hx.2))
    rw [inter_comm]
    exact hcb ⟨by linarith [h.2], by linarith [h.1]⟩
  · rw [hφid (-x) (neg_le_neg hx.1.2.le), neg_neg]

/-- Smooth local frames `s` on `Ioo a b` and `s'` on `Ioo c d`, where `a ≤ c < c₁ < b ≤ d`, glue
to a smooth local frame on `Ioo a d` that is `s` on `Ioo a c₁`. -/
theorem exists_isLocalFrameOn_Ioo_eqOn_Ioo_left {a d : ℝ}
    (hs : IsLocalFrameOn 𝓘(ℝ) F ∞ s (Ioo a b)) (hs' : IsLocalFrameOn 𝓘(ℝ) F ∞ s' (Ioo c d))
    (ha : a ≤ c) (hc : c < c₁) (hb : c₁ < b) (hd : b ≤ d) :
    ∃ t : ι → Π x, T x, IsLocalFrameOn 𝓘(ℝ) F ∞ t (Ioo a d) ∧
      ∀ i, ∀ x ∈ Ioo a c₁, t i x = s i x := by
  obtain ⟨t, ht, hts⟩ := hs.exists_isLocalFrameOn_union_Iio hs' isOpen_Ioo isOpen_Ioo hc hb
    fun x hx ↦ ⟨⟨by linarith [hx.1], hx.2⟩, ⟨hx.1, by linarith [hx.2]⟩⟩
  refine ⟨t, ht.mono ?_, fun i x hx ↦ hts i x ⟨⟨hx.1, by linarith [hx.2]⟩, hx.2⟩⟩
  rintro x ⟨h₁, h₂⟩
  rcases lt_or_ge x c₁ with h | h
  · exact .inl ⟨⟨h₁, by linarith⟩, h⟩
  · exact .inr ⟨⟨by linarith, h₂⟩, mem_Ioi.2 (by linarith)⟩

/-- Smooth local frames `s` on `Ioo a b` and `s'` on `Ioo c d`, where `a ≤ c < c₁ < b ≤ d`, glue
to a smooth local frame on `Ioo a d` that is `s'` on `Ioo c₁ d`. -/
theorem exists_isLocalFrameOn_Ioo_eqOn_Ioo_right {a d : ℝ}
    (hs : IsLocalFrameOn 𝓘(ℝ) F ∞ s (Ioo a b)) (hs' : IsLocalFrameOn 𝓘(ℝ) F ∞ s' (Ioo c d))
    (ha : a ≤ c) (hc : c < c₁) (hb : c₁ < b) (hd : b ≤ d) :
    ∃ t : ι → Π x, T x, IsLocalFrameOn 𝓘(ℝ) F ∞ t (Ioo a d) ∧
      ∀ i, ∀ x ∈ Ioo c₁ d, t i x = s' i x := by
  obtain ⟨t, ht, hts⟩ := hs.exists_isLocalFrameOn_union_Ioi hs' isOpen_Ioo isOpen_Ioo hc hb
    fun x hx ↦ ⟨⟨by linarith [hx.1], hx.2⟩, ⟨hx.1, by linarith [hx.2]⟩⟩
  refine ⟨t, ht.mono ?_, fun i x hx ↦ hts i x ⟨⟨by linarith [hx.1], hx.2⟩, hx.1⟩⟩
  rintro x ⟨h₁, h₂⟩
  rcases lt_or_ge x b with h | h
  · exact .inl ⟨⟨h₁, h⟩, h⟩
  · exact .inr ⟨⟨by linarith, h₂⟩, mem_Ioi.2 (by linarith)⟩

end Real

end IsLocalFrameOn
