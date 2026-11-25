/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Analysis.SpecialFunctions.SmoothTransition
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.LocalFrame
public import TauCeti.Geometry.Manifold.VectorBundle.Trivialization

/-!
# Smooth vector bundles over the line are trivial

A smooth vector bundle over `ℝ` with finite-dimensional fibre `F` is smoothly isomorphic to the
product bundle `ℝ × F` (`Bundle.exists_diffeomorph_prod_of_real`). The proof builds a global
smooth frame by gluing local frames and turns it into a trivialization over all of `ℝ`.

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

Every point of `ℝ` lies in an interval that carries a frame, that of the bundle's trivialization
there. Gluing such a frame onto a frame on `Ioo a R` gives a frame on a longer interval that keeps
the old one away from its right end, so a supremum argument extends a frame on `Ioo a b` to any
`Ioo a R` without changing it on `Ioo a c₁`, for `c₁ < b`
(`IsLocalFrameOn.exists_isLocalFrameOn_Ioo_extend_right`), and likewise to the left
(`IsLocalFrameOn.exists_isLocalFrameOn_Ioo_extend_left`). This gives frames on
`Ioo (-(k + 2)) (k + 2)`, each agreeing with the previous one on `Ioo (-(k + 1)) (k + 1)`, whose
limit (`IsLocalFrameOn.exists_isLocalFrameOn_iUnion`) is a global frame
(`Bundle.exists_isLocalFrameOn_univ_of_real`). Tau Ceti's
`ContMDiffVectorBundle.exists_trivialization_baseSet_eq_iff_exists_isLocalFrameOn` turns it into a
trivialization over `ℝ` in the maximal atlas, and
`Bundle.Trivialization.toDiffeomorphOfBaseSetEqUniv`
into a diffeomorphism. The statement is the smooth counterpart of Tau Ceti's
`TauCeti.exists_homeomorph_prod_of_contractibleSpace`.

## Main results

* `IsLocalFrameOn.exists_isLocalFrameOn_union_Iio`,
  `IsLocalFrameOn.exists_isLocalFrameOn_union_Ioi`:
  over `ℝ`, a frame on the union that keeps the first, resp. the second, frame on its side.
* `IsLocalFrameOn.exists_isLocalFrameOn_Ioo_eqOn_Ioo_left`,
  `IsLocalFrameOn.exists_isLocalFrameOn_Ioo_eqOn_Ioo_right`: the same for two open intervals.
* `IsLocalFrameOn.exists_isLocalFrameOn_Ioo_extend_right`,
  `IsLocalFrameOn.exists_isLocalFrameOn_Ioo_extend_left`: a frame on an open interval extends
  to the right, resp. the left, as far as wanted.
* `Bundle.exists_isLocalFrameOn_univ_of_real`: a smooth vector bundle over `ℝ` has a global frame.
* `Bundle.exists_diffeomorph_prod_of_real`: a smooth vector bundle over `ℝ` is diffeomorphic to
  `ℝ × F` by a map over `ℝ` that is linear on each fibre.

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

omit [FiniteDimensional ℝ F] [Finite ι] in
/-- Every point of `ℝ` has an open interval around it that carries a smooth local frame indexed
by `ι`, given a basis of the model fibre indexed by `ι`: the frame of the trivialization at the
point. -/
private theorem exists_isLocalFrameOn_Ioo_sub_add (b : Module.Basis ι ℝ F) (x : ℝ) :
    ∃ ε > 0, ∃ s : ι → Π x, T x, IsLocalFrameOn 𝓘(ℝ) F ∞ s (Ioo (x - ε) (x + ε)) := by
  set e := trivializationAt F T x
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 e.open_baseSet x (mem_baseSet_trivializationAt F T x)
  refine ⟨ε, hε, _, (e.isLocalFrameOn_symm_of_mem_maximalAtlas
    (Trivialization.mem_maximalAtlas_of_memTrivializationAtlas 𝓘(ℝ) ∞ e) b).mono ?_⟩
  rwa [← Real.ball_eq_Ioo]

/-- The same as `exists_isLocalFrameOn_Ioo_sub_add`, with the basis of the model fibre taken from
a local frame on a nonempty set. -/
private theorem exists_isLocalFrameOn_Ioo_sub_add_of_mem (hs : IsLocalFrameOn 𝓘(ℝ) F ∞ s U)
    {y : ℝ} (hy : y ∈ U) (x : ℝ) :
    ∃ ε > 0, ∃ s' : ι → Π x, T x, IsLocalFrameOn 𝓘(ℝ) F ∞ s' (Ioo (x - ε) (x + ε)) := by
  let := Fintype.ofFinite ι
  exact exists_isLocalFrameOn_Ioo_sub_add ((Module.finBasisOfFinrankEq ℝ F
    (hs.card_eq_finrank hy).symm).reindex (Fintype.equivFin ι).symm) x

/-- A set of reals that contains `b`, is closed downwards, and, near each `x`, contains `x + ε`
as soon as it contains a point of `Ioc (x - ε) x` above `c < b`, is all of `ℝ`. -/
private theorem eq_univ_of_forall_exists_add_mem {S : Set ℝ} {c : ℝ} (hcb : c < b) (hb : b ∈ S)
    (hS : IsLowerSet S)
    (hstep : ∀ x, ∃ ε > 0, ∀ R ∈ S, c < R → x - ε < R → R ≤ x → x + ε ∈ S) : S = univ := by
  refine eq_univ_of_forall fun y ↦ ?_
  by_contra hy
  have hbdd : BddAbove S := ⟨y, fun R hR ↦ le_of_not_ge fun h ↦ hy (hS h hR)⟩
  obtain ⟨ε, hε, h⟩ := hstep (sSup S)
  have hb' := le_csSup hbdd hb
  obtain ⟨R, hR, hlt⟩ := exists_lt_of_lt_csSup ⟨b, hb⟩
    (max_lt (by linarith) (by linarith) : max (sSup S - ε) c < sSup S)
  have := le_csSup hbdd (h R hR ((le_max_right _ _).trans_lt hlt) ((le_max_left _ _).trans_lt hlt)
    (le_csSup hbdd hR))
  linarith

/-- A smooth local frame `s` on `Ioo a b` extends to the right: for `a < c₁ < b` and every `R`,
there is a smooth local frame on `Ioo a R` that is `s` on `Ioo a c₁`. -/
theorem exists_isLocalFrameOn_Ioo_extend_right {a : ℝ}
    (hs : IsLocalFrameOn 𝓘(ℝ) F ∞ s (Ioo a b)) (ha : a < c₁) (hb : c₁ < b) (R : ℝ) :
    ∃ t : ι → Π x, T x, IsLocalFrameOn 𝓘(ℝ) F ∞ t (Ioo a R) ∧
      ∀ i, ∀ x ∈ Ioo a c₁, t i x = s i x := by
  set S := {R : ℝ | ∃ t : ι → Π x, T x, IsLocalFrameOn 𝓘(ℝ) F ∞ t (Ioo a R) ∧
    ∀ i, ∀ x ∈ Ioo a c₁, t i x = s i x}
  suffices hS : S = univ by
    have hR : R ∈ S := hS ▸ mem_univ R
    exact hR
  refine eq_univ_of_forall_exists_add_mem hb ⟨s, hs, fun _ _ _ ↦ rfl⟩ ?_ fun x ↦ ?_
  · rintro R₁ R₂ h ⟨t, ht, hts⟩
    exact ⟨t, ht.mono (Ioo_subset_Ioo_right h), hts⟩
  obtain ⟨ε, hε, s', hs'⟩ := hs.exists_isLocalFrameOn_Ioo_sub_add_of_mem ⟨ha, hb⟩ x
  refine ⟨ε, hε, fun R ⟨t, ht, hts⟩ hcR hxR hRx ↦ ?_⟩
  -- Glue `t` with `s'`, cut down to the part of its interval to the right of `c₁`.
  have hm : max (x - ε) c₁ < R := max_lt hxR hcR
  obtain ⟨u, hu, hut⟩ := ht.exists_isLocalFrameOn_Ioo_eqOn_Ioo_left
    (hs'.mono (Ioo_subset_Ioo_left (le_max_left _ (c₁ : ℝ)))) (c₁ := (max (x - ε) c₁ + R) / 2)
    (ha.le.trans (le_max_right _ _)) (by linarith) (by linarith) (by linarith)
  refine ⟨u, hu, fun i y hy ↦ (hut i y ⟨hy.1, ?_⟩).trans (hts i y hy)⟩
  linarith [hy.2, le_max_right (x - ε) c₁]

/-- A smooth local frame `s` on `Ioo a b` extends to the left: for `a < c₀ < b` and every `R`,
there is a smooth local frame on `Ioo R b` that is `s` on `Ioo c₀ b`. -/
theorem exists_isLocalFrameOn_Ioo_extend_left {a c₀ : ℝ}
    (hs : IsLocalFrameOn 𝓘(ℝ) F ∞ s (Ioo a b)) (ha : a < c₀) (hb : c₀ < b) (R : ℝ) :
    ∃ t : ι → Π x, T x, IsLocalFrameOn 𝓘(ℝ) F ∞ t (Ioo R b) ∧
      ∀ i, ∀ x ∈ Ioo c₀ b, t i x = s i x := by
  set S := {R : ℝ | ∃ t : ι → Π x, T x, IsLocalFrameOn 𝓘(ℝ) F ∞ t (Ioo (-R) b) ∧
    ∀ i, ∀ x ∈ Ioo c₀ b, t i x = s i x}
  suffices hS : S = univ by
    have hR : -R ∈ S := hS ▸ mem_univ (-R)
    simpa [S] using hR
  refine eq_univ_of_forall_exists_add_mem (neg_lt_neg ha) ⟨s, by rwa [neg_neg],
    fun _ _ _ ↦ rfl⟩ ?_ fun x ↦ ?_
  · rintro R₁ R₂ h ⟨t, ht, hts⟩
    exact ⟨t, ht.mono (Ioo_subset_Ioo_left (neg_le_neg h)), hts⟩
  obtain ⟨ε, hε, s', hs'⟩ := hs.exists_isLocalFrameOn_Ioo_sub_add_of_mem ⟨ha, hb⟩ (-x)
  refine ⟨ε, hε, fun R ⟨t, ht, hts⟩ hcR hxR hRx ↦ ?_⟩
  -- Glue `s'`, cut down to the part of its interval to the left of `c₀`, with `t`.
  have hm : -R < min (-x + ε) c₀ := lt_min (by linarith) (by linarith)
  obtain ⟨u, hu, hut⟩ := exists_isLocalFrameOn_Ioo_eqOn_Ioo_right
    (hs'.mono (Ioo_subset_Ioo_right (min_le_left _ c₀)))
    ht (c₁ := (-R + min (-x + ε) c₀) / 2) (by linarith) (by linarith) (by linarith)
    ((min_le_right _ _).trans hb.le)
  refine ⟨u, by rwa [neg_add'], fun i y hy ↦ (hut i y ⟨?_, hy.2⟩).trans (hts i y hy)⟩
  linarith [hy.1, min_le_right (-x + ε) c₀]

/-- A smooth local frame `s` on `Ioo a b` gives, for `a < c₀ < c₁ < b` and every `R`, a smooth local
frame on `Ioo (-R) R` that is `s` on `Ioo c₀ c₁`. -/
private theorem exists_isLocalFrameOn_Ioo_neg_self {a c₀ : ℝ}
    (hs : IsLocalFrameOn 𝓘(ℝ) F ∞ s (Ioo a b)) (ha : a < c₀) (hc : c₀ < c₁) (hb : c₁ < b)
    (R : ℝ) :
    ∃ t : ι → Π x, T x, IsLocalFrameOn 𝓘(ℝ) F ∞ t (Ioo (-R) R) ∧
      ∀ i, ∀ x ∈ Ioo c₀ c₁, t i x = s i x := by
  have hbR : b ≤ max R b := le_max_right R b
  obtain ⟨t₁, ht₁, hts₁⟩ := hs.exists_isLocalFrameOn_Ioo_extend_right (ha.trans hc) hb (max R b)
  obtain ⟨t₂, ht₂, hts₂⟩ :=
    ht₁.exists_isLocalFrameOn_Ioo_extend_left ha (by linarith) (-R)
  exact ⟨t₂, ht₂.mono (Ioo_subset_Ioo_right (le_max_left _ _)), fun i x hx ↦
    (hts₂ i x ⟨hx.1, by linarith [hx.2]⟩).trans (hts₁ i x ⟨ha.trans hx.1, hx.2⟩)⟩

end Real

end IsLocalFrameOn

namespace Bundle

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {T : ℝ → Type*} [TopologicalSpace (TotalSpace F T)]
  [∀ x, AddCommGroup (T x)] [∀ x, Module ℝ (T x)] [∀ x, TopologicalSpace (T x)]
  [FiberBundle F T] [VectorBundle ℝ F T] [ContMDiffVectorBundle ∞ F T 𝓘(ℝ)]

/-- A smooth vector bundle over `ℝ` with finite-dimensional fibre has a smooth global frame,
indexed by any type that indexes a basis of the model fibre. -/
theorem exists_isLocalFrameOn_univ_of_real {ι : Type*} [Finite ι] (b : Module.Basis ι ℝ F) :
    ∃ s : ι → Π x, T x, IsLocalFrameOn 𝓘(ℝ) F ∞ s univ := by
  obtain ⟨ε, hε, s₀, hs₀⟩ := IsLocalFrameOn.exists_isLocalFrameOn_Ioo_sub_add (T := T) b 0
  -- Frames `t k` on `Ioo (-(k + 2)) (k + 2)`, each agreeing with the previous one on
  -- `Ioo (-(k + 1)) (k + 1)`.
  have step (k : ℕ) (t : ι → Π x, T x)
      (ht : IsLocalFrameOn 𝓘(ℝ) F ∞ t (Ioo (-(k + 2 : ℝ)) (k + 2))) :
      ∃ t' : ι → Π x, T x, IsLocalFrameOn 𝓘(ℝ) F ∞ t' (Ioo (-(k + 3 : ℝ)) (k + 3)) ∧
        ∀ i, ∀ x ∈ Ioo (-(k + 1 : ℝ)) (k + 1), t' i x = t i x :=
    ht.exists_isLocalFrameOn_Ioo_neg_self (by linarith) (by linarith) (by linarith) _
  choose! g hg using step
  obtain ⟨t₀, ht₀, -⟩ := hs₀.exists_isLocalFrameOn_Ioo_neg_self (c₀ := 0 - ε / 2) (c₁ := ε / 2)
    (by linarith) (by linarith) (by linarith) 2
  let t : ℕ → ι → Π x, T x := fun k ↦ Nat.rec (motive := fun _ ↦ ι → Π x, T x) t₀ g k
  have ht (k : ℕ) : IsLocalFrameOn 𝓘(ℝ) F ∞ (t k) (Ioo (-(k + 2 : ℝ)) (k + 2)) := by
    induction k with
    | zero => simpa [t] using ht₀
    | succ k ih =>
      rw [show ((k + 1 : ℕ) : ℝ) + 2 = k + 3 by push_cast; ring]
      exact (hg k (t k) ih).1
  have hmono : Monotone fun k : ℕ ↦ Ioo (-(k + 1 : ℝ)) (k + 1) := fun k l hkl ↦ by
    have : (k : ℝ) ≤ l := by exact_mod_cast hkl
    exact Ioo_subset_Ioo (by linarith) (by linarith)
  obtain ⟨s, hs, -⟩ := IsLocalFrameOn.exists_isLocalFrameOn_iUnion hmono (fun _ ↦ isOpen_Ioo)
    (fun k ↦ (ht k).mono (Ioo_subset_Ioo (by linarith) (by linarith)))
    fun k i x hx ↦ (hg k (t k) (ht k)).2 i x hx
  refine ⟨s, hs.mono fun x _ ↦ mem_iUnion.2 ?_⟩
  obtain ⟨k, hk⟩ := exists_nat_gt |x|
  exact ⟨k, by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩

/-- A smooth vector bundle over `ℝ` with finite-dimensional fibre `F` is smoothly trivial: its
total space is diffeomorphic to `ℝ × F` by a map that covers the identity of `ℝ` and is a
continuous linear isomorphism on each fibre. -/
theorem exists_diffeomorph_prod_of_real :
    ∃ (h : TotalSpace F T ≃ₘ^∞⟮𝓘(ℝ).prod 𝓘(ℝ, F), 𝓘(ℝ).prod 𝓘(ℝ, F)⟯ ℝ × F)
      (L : ∀ t, T t ≃L[ℝ] F), ∀ (t : ℝ) (v : T t), h ⟨t, v⟩ = (t, L t v) := by
  let b := Module.finBasis ℝ F
  obtain ⟨e, _, hem, he⟩ :=
    (ContMDiffVectorBundle.exists_trivialization_baseSet_eq_iff_exists_isLocalFrameOn
      isOpen_univ b).2 (exists_isLocalFrameOn_univ_of_real (T := T) b)
  have hmem (t : ℝ) : t ∈ e.baseSet := he ▸ mem_univ t
  have hsrc : e.source = univ := by rw [e.source_eq, he, preimage_univ]
  have h₁ : ContMDiff (𝓘(ℝ).prod 𝓘(ℝ, F)) (𝓘(ℝ).prod 𝓘(ℝ, F)) ∞ e := by
    rw [← contMDiffOn_univ, ← hsrc]
    exact Trivialization.contMDiffOn_of_mem_maximalAtlas hem
  have h₂ : ContMDiff (𝓘(ℝ).prod 𝓘(ℝ, F)) (𝓘(ℝ).prod 𝓘(ℝ, F)) ∞
      e.toOpenPartialHomeomorph.symm := by
    intro q
    rw [Trivialization.contMDiffAt_iff_of_mem_maximalAtlas hem (hsrc ▸ mem_univ _)]
    refine ⟨contMDiffAt_fst.congr_of_eventuallyEq (.of_forall fun q' ↦ ?_),
      contMDiffAt_snd.congr_of_eventuallyEq (.of_forall fun q' ↦ ?_)⟩
    · exact e.proj_symm_apply' (hmem q'.1)
    · exact congrArg Prod.snd (e.apply_symm_apply' (hmem q'.1))
  refine ⟨e.toDiffeomorphOfBaseSetEqUniv he h₁ h₂, fun t ↦ e.continuousLinearEquivAt ℝ t (hmem t),
    fun t v ↦ ?_⟩
  rw [Trivialization.coe_toDiffeomorphOfBaseSetEqUniv]
  exact e.apply_eq_prod_continuousLinearEquivAt ℝ t (hmem t) v

end Bundle
