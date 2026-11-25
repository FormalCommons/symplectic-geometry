/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import TauCeti.Geometry.Manifold.VectorBundle.FrameTrivialization

/-!
# Gluing smooth local frames of a vector bundle over the line

This file proves the gluing step behind the smooth triviality of vector bundles over `ℝ`.

Let `s` and `s'` be `C^n` local frames of a vector bundle `V` with finite-dimensional fibre on
open sets `U` and `U'` of a manifold, indexed by the same finite type. On `U ∩ U'` each `s i` is a
combination `∑ j, A i j • s' j` with `C^n` coefficients `A i j`, by Tau Ceti's
`IsLocalFrameOn.contMDiffOn_coeff`. Given a `C^n` map `φ` that sends an open set `W' ⊆ U'` into
`U ∩ U'`, the sections `x ↦ ∑ j, A i j (φ x) • s' j x` form a frame on `W'`: at each point they
are the image of the basis `s · (φ x)` under the linear map that sends `s' j (φ x)` to `s' j x`.
Where `φ` is the identity, they agree with `s`. So, if `φ` is the identity on `W ∩ W'` for an open
`W ⊆ U`, they glue with `s` to a frame on `W ∪ W'` that is `s` on `W`
(`IsLocalFrameOn.exists_isLocalFrameOn_union`).

Over `ℝ`, with `c < c₁ < b` and `Set.Ioo c b ⊆ U ∩ U'`, a map `φ` that is the identity up to `c₁`
and maps `Ioi c` into `Ioo c b` (`Real.exists_contDiff_eq_self_mapsTo_Ioo`) gives a
frame on `(U ∩ Iio c₁) ∪ (U' ∩ Ioi c)` that is `s` on `U ∩ Iio c₁`
(`IsLocalFrameOn.exists_isLocalFrameOn_union_Iio`), and the mirror image gives one on
`(U ∩ Iio b) ∪ (U' ∩ Ioi c₁)` that is `s'` on `U' ∩ Ioi c₁`
(`IsLocalFrameOn.exists_isLocalFrameOn_union_Ioi`). For intervals `U = Ioo a b` and
`U' = Ioo c d` with `a ≤ c` and `b ≤ d` the union is `Ioo a d`
(`IsLocalFrameOn.exists_isLocalFrameOn_Ioo_eqOn_Ioo_left`,
`IsLocalFrameOn.exists_isLocalFrameOn_Ioo_eqOn_Ioo_right`).

## Main results

* `IsLocalFrameOn.exists_isLocalFrameOn_union`: two local frames glued along a map `φ` into their
  overlap.
* `IsLocalFrameOn.exists_isLocalFrameOn_union_Iio`,
  `IsLocalFrameOn.exists_isLocalFrameOn_union_Ioi`:
  over `ℝ`, a frame on the union that keeps the first, resp. the second, frame on its side.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Theorem 7.3.1.
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963.
-/

public section

open Bundle Set Function
open scoped Manifold ContDiff

/-- For `c < c₁ < b` there is a smooth function `φ : ℝ → ℝ` that is the identity on `Iic c₁` and
maps `Ioi c` into `Ioo c b`. One choice is
`x ↦ c₁ + (x - c₁) * (1 - smoothTransition ((x - c₁) / (b - c₁)))`, which is constant on
`Ici b`. -/
theorem Real.exists_contDiff_eq_self_mapsTo_Ioo {c c₁ b : ℝ} (hc : c < c₁) (hb : c₁ < b) :
    ∃ φ : ℝ → ℝ, ContDiff ℝ ∞ φ ∧ (∀ x ≤ c₁, φ x = x) ∧ MapsTo φ (Ioi c) (Ioo c b) := by
  have hδ : 0 < b - c₁ := sub_pos.2 hb
  refine ⟨fun x ↦ c₁ + (x - c₁) * (1 - smoothTransition ((x - c₁) / (b - c₁))), ?_, ?_, ?_⟩
  · fun_prop
  · intro x hx
    dsimp only
    rw [smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le)]
    ring
  · intro x hx
    dsimp only
    rcases le_or_gt x c₁ with hx₁ | hx₁
    · rw [smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le)]
      exact ⟨by simp only [mem_Ioi] at hx; linarith, by linarith⟩
    have h0 := smoothTransition.le_one ((x - c₁) / (b - c₁))
    have h1 := smoothTransition.nonneg ((x - c₁) / (b - c₁))
    refine ⟨by nlinarith, ?_⟩
    rcases lt_or_ge x b with hxb | hxb
    · nlinarith
    · rw [smoothTransition.one_of_one_le ((one_le_div hδ).2 (sub_le_sub_right hxb c₁))]
      linarith

namespace IsLocalFrameOn

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]
  {n : ℕ∞ω} [ContMDiffVectorBundle n F V IB]
  {ι : Type*} [Finite ι] {s s' : ι → Π x, V x} {U U' : Set B}

/-- Two `C^n` local frames `s` on `U` and `s'` on `U'`, indexed by the same finite type, glue to a
`C^n` local frame on `W ∪ W'` that is `s` on `W`, for open sets `W ⊆ U` and `W' ⊆ U'` that admit
a `C^n` map `φ` from `W'` into `U ∩ U'` that is the identity on `W ∩ W'`. -/
theorem exists_isLocalFrameOn_union (hs : IsLocalFrameOn IB F n s U)
    (hs' : IsLocalFrameOn IB F n s' U') (hU : IsOpen U) (hU' : IsOpen U') {W W' : Set B}
    (hW : IsOpen W) (hW' : IsOpen W') (hWU : W ⊆ U) (hW'U' : W' ⊆ U') {φ : B → B}
    (hφ : ContMDiffOn IB IB n φ W') (hφW' : MapsTo φ W' (U ∩ U'))
    (hφid : ∀ x ∈ W ∩ W', φ x = x) :
    ∃ t : ι → Π x, V x, IsLocalFrameOn IB F n t (W ∪ W') ∧ ∀ i, ∀ x ∈ W, t i x = s i x := by
  classical
  let := Fintype.ofFinite ι
  -- The coefficients are taken in `s'` restricted to the overlap, where they are `C^n`.
  have hs'' : IsLocalFrameOn IB F n s' (U ∩ U') := hs'.mono inter_subset_right
  -- The frame `s` rewritten in `s'` at the point `φ x`.
  set g : ι → Π x, V x := fun i x ↦ ∑ j, hs''.coeff j (φ x) (s i (φ x)) • s' j x with hg
  -- At a point of `W'`, `g · x` is the image of the basis `s · (φ x)` under the linear map
  -- sending `s' j (φ x)` to `s' j x`.
  have hbasis {x : B} (hx : x ∈ W') : ∃ b : Module.Basis ι 𝕜 (V x), ⇑b = (g · x) := by
    have hy := hφW' hx
    refine ⟨(hs.toBasisAt hy.1).map ((hs''.toBasisAt hy).equiv
      (hs'.toBasisAt (hW'U' hx)) (Equiv.refl ι)), funext fun i ↦ ?_⟩
    rw [Module.Basis.map_apply, toBasisAt_coe, hs''.coeff_sum_eq (s i) hy, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_smul, ← toBasisAt_coe hs'' hy, Module.Basis.equiv_apply, Equiv.refl_apply,
      toBasisAt_coe]
  have hgs {x : B} (hx : x ∈ W ∩ W') (i : ι) : g i x = s i x := by
    simp only [hg]
    rw [hφid x hx]
    exact (hs''.coeff_sum_eq (s i) ⟨hWU hx.1, hW'U' hx.2⟩).symm
  have hgsmooth (i : ι) : ContMDiffOn IB (IB.prod 𝓘(𝕜, F)) n (T% (g i)) W' := by
    have hA (j : ι) : ContMDiffOn IB 𝓘(𝕜) n (fun y ↦ hs''.coeff j y (s i y)) (U ∩ U') :=
      hs''.contMDiffOn_coeff (hU.inter hU') le_rfl ((hs.contMDiffOn i).mono inter_subset_left) j
    exact ContMDiffOn.sum_section fun j _ ↦
      ((hA j).comp hφ hφW').smul_section ((hs'.contMDiffOn j).mono hW'U')
  -- Off `W`, the glued family at a point of `W'` is the basis given by `hbasis`.
  have hfam {x : B} (hxW : x ∉ W) (hx : x ∈ W') : ∃ b : Module.Basis ι 𝕜 (V x),
      (fun i ↦ if x ∈ W then s i x else g i x) = ⇑b := by
    obtain ⟨b, hb⟩ := hbasis hx
    exact ⟨b, by simp [hxW, hb]⟩
  refine ⟨fun i x ↦ if x ∈ W then s i x else g i x, ⟨fun {x} hx ↦ ?_, fun {x} hx ↦ ?_, fun i ↦ ?_⟩,
    fun i x hx ↦ by simp [hx]⟩
  · by_cases hxW : x ∈ W
    · simpa [hxW] using hs.linearIndependent (hWU hxW)
    · obtain ⟨b, hb⟩ := hfam hxW (hx.resolve_left hxW)
      rw [hb]
      exact b.linearIndependent
  · by_cases hxW : x ∈ W
    · simpa [hxW] using hs.generating (hWU hxW)
    · obtain ⟨b, hb⟩ := hfam hxW (hx.resolve_left hxW)
      rw [hb]
      exact b.span_eq.ge
  · refine ContMDiffOn.union_of_isOpen ?_ ?_ hW hW'
    · exact ((hs.contMDiffOn i).mono hWU).congr fun x hx ↦ by simp [hx]
    · refine (hgsmooth i).congr fun x hx ↦ ?_
      by_cases hxW : x ∈ W
      · simp [hxW, hgs ⟨hxW, hx⟩ i]
      · simp [hxW]


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
  obtain ⟨φ, hφ, hφid, hφmaps⟩ := Real.exists_contDiff_eq_self_mapsTo_Ioo hc hb
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
  obtain ⟨φ, hφ, hφid, hφmaps⟩ :=
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
