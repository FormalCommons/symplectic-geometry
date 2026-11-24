/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Image

/-!
# Composition of semialgebraic functions through `x ↦ Sum.elim x (f x)`

Tau Ceti's `TauCeti.IsSemialgebraicOn.comp` composes semialgebraic functions when the
intermediate coordinate space is finite, since its proof forgets the intermediate coordinates.
For a composite `x ↦ g (Sum.elim x (f x))`, whose intermediate point keeps the input `x`, this
file needs no finiteness of the input coordinates.

* `TauCeti.IsSemialgebraicOn.sumElim_comp_sumElim`: if `f` is semialgebraic on `s` and `g` on `t`,
  with `Sum.elim x (f x) ∈ t` for `x ∈ s`, then `x ↦ Sum.elim (f x) (g (Sum.elim x (f x)))` is
  semialgebraic on `s`. Its graph is the intersection of inverse images of the graphs of `f`
  and `g`, so no coordinate is eliminated: the statement needs neither finiteness nor projection
  closure. The proof follows that of `TauCeti.IsSemialgebraicOn.sumElim`.
* `TauCeti.IsSemialgebraicOn.of_sumElim_right`: given projection closure, if
  `x ↦ Sum.elim (f x) (g x)` is semialgebraic on `s` and `f` has finitely many output
  coordinates, then `g` is semialgebraic on `s`, with no finiteness of the other coordinates.
  The proof forgets the coordinates of `f x`, as that of `TauCeti.IsSemialgebraicOn.comp`
  forgets the intermediate ones.
* `TauCeti.IsSemialgebraicOn.comp_sumElim`: given projection closure and finitely many
  coordinates for the values of `f`, the composite `x ↦ g (Sum.elim x (f x))` itself is
  semialgebraic on `s`, for any set of input coordinates. It follows from the two lemmas above.

## References

* S. Basu, R. Pollack, M.-F. Roy, *Algorithms in Real Algebraic Geometry*, second edition,
  Springer, 2006, Chapter 2.
-/

public section

open Set

namespace TauCeti

variable {σ α υ R : Type*} [CommRing R] [LinearOrder R]

/-- If `f` is semialgebraic on `s`, `g` is semialgebraic on `t`, and `Sum.elim x (f x) ∈ t` for
every `x ∈ s`, then `x ↦ Sum.elim (f x) (g (Sum.elim x (f x)))` is semialgebraic on `s`. No
coordinate type needs to be finite. -/
theorem IsSemialgebraicOn.sumElim_comp_sumElim {f : (σ → R) → (α → R)}
    {g : (σ ⊕ α → R) → (υ → R)} {s : Set (σ → R)} {t : Set (σ ⊕ α → R)}
    (hg : IsSemialgebraicOn g t) (hf : IsSemialgebraicOn f s)
    (hst : ∀ x ∈ s, Sum.elim x (f x) ∈ t) :
    IsSemialgebraicOn (fun x ↦ Sum.elim (f x) (g (Sum.elim x (f x)))) s := by
  refine isSemialgebraicOn_def.2 ⟨hf.isSemialgebraic, ?_⟩
  -- In the coordinates `σ ⊕ (α ⊕ υ)`, the graph is cut out by the graphs of `f` and `g`.
  convert (hf.graph.preimage_comp (Sum.elim Sum.inl (Sum.inr ∘ Sum.inl))).inter
    (hg.graph.preimage_comp
      (Sum.elim (Sum.elim Sum.inl (Sum.inr ∘ Sum.inl)) (Sum.inr ∘ Sum.inr))) using 1
  ext z
  rw [mem_preimage_sumArrowEquivProdArrow_graphOn, mem_inter_iff, mem_preimage,
    mem_preimage_sumArrowEquivProdArrow_graphOn, mem_preimage,
    mem_preimage_sumArrowEquivProdArrow_graphOn]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, Sum.comp_elim]
  rw [← Sum.elim_comp_inl_inr (z ∘ Sum.inr), Sum.elim_eq_iff]
  constructor
  · rintro ⟨hz, hf', hg'⟩
    exact ⟨⟨hz, hf'⟩, hf' ▸ hst _ hz, hf' ▸ hg'⟩
  · rintro ⟨⟨hz, hf'⟩, -, hg'⟩
    exact ⟨hz, hf', hf' ▸ hg'⟩

/-- Given projection closure, if `x ↦ Sum.elim (f x) (g x)` is semialgebraic on `s` and `f` has
finitely many output coordinates, then `g` is semialgebraic on `s`. The coordinates `σ` and `υ`
need not be finite. -/
theorem IsSemialgebraicOn.of_sumElim_right [HasSemialgebraicProjections R] [Finite α]
    {f : (σ → R) → (α → R)} {g : (σ → R) → (υ → R)} {s : Set (σ → R)}
    (h : IsSemialgebraicOn (fun x ↦ Sum.elim (f x) (g x)) s) : IsSemialgebraicOn g s := by
  refine isSemialgebraicOn_def.2 ⟨h.isSemialgebraic, ?_⟩
  -- In the coordinates `α ⊕ (σ ⊕ υ)`, forget the coordinates `α` of `f x`.
  convert (h.graph.preimage_comp
    (Sum.elim (Sum.inr ∘ Sum.inl) (Sum.elim Sum.inl (Sum.inr ∘ Sum.inr)))).image_comp_inr
    using 1
  ext z
  rw [mem_preimage_sumArrowEquivProdArrow_graphOn, mem_image]
  constructor
  · rintro ⟨hz, hgz⟩
    refine ⟨Sum.elim (f (z ∘ Sum.inl)) z, ?_, rfl⟩
    rw [mem_preimage, mem_preimage_sumArrowEquivProdArrow_graphOn]
    simp only [Sum.comp_elim, Sum.elim_comp_inl, Sum.elim_comp_inr, ← Function.comp_assoc]
    exact ⟨hz, by rw [hgz]⟩
  · rintro ⟨w, hw, rfl⟩
    rw [mem_preimage, mem_preimage_sumArrowEquivProdArrow_graphOn] at hw
    simp only [Sum.comp_elim, Sum.elim_comp_inl, Sum.elim_comp_inr] at hw
    obtain ⟨hw, hfw⟩ := hw
    rw [Sum.elim_eq_iff] at hfw
    rw [Function.comp_assoc, Function.comp_assoc]
    exact ⟨hw, hfw.2⟩

/-- Given projection closure, if `f` is semialgebraic on `s` with finitely many output
coordinates, `g` is semialgebraic on `t`, and `Sum.elim x (f x) ∈ t` for every `x ∈ s`, then
`x ↦ g (Sum.elim x (f x))` is semialgebraic on `s`. The input coordinates `σ` need not be
finite. -/
theorem IsSemialgebraicOn.comp_sumElim [HasSemialgebraicProjections R] [Finite α]
    {f : (σ → R) → (α → R)} {g : (σ ⊕ α → R) → (υ → R)} {s : Set (σ → R)}
    {t : Set (σ ⊕ α → R)} (hg : IsSemialgebraicOn g t) (hf : IsSemialgebraicOn f s)
    (hst : ∀ x ∈ s, Sum.elim x (f x) ∈ t) :
    IsSemialgebraicOn (fun x ↦ g (Sum.elim x (f x))) s :=
  (hg.sumElim_comp_sumElim hf hst).of_sumElim_right

end TauCeti

end
