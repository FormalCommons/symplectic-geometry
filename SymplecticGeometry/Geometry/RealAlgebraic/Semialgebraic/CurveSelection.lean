/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.RealAlgebraic.Semialgebraic.Choice
public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Topology

/-!
# The curve selection lemma

A point `x` in the closure of a semialgebraic set `A ⊆ σ → ℝ`, `σ` finite, is reached by a
semialgebraic curve through `A`: there are `ε > 0` and `γ : ℝ → (σ → ℝ)` with `γ 0 = x`, `γ`
continuous on `[0, ε)`, `γ t ∈ A` for `0 < t < ε`, and `γ` semialgebraic on `(0, ε)`
(`TauCeti.IsSemialgebraic.exists_curve_of_mem_closure`). Semialgebraicity of `γ` is meant in Tau
Ceti's sense, for the function `s ↦ γ (s 0)` of the line `Fin 1 → ℝ`.

## Proof

The set of pairs `(t, y)` with `0 < t`, `y ∈ A` and `dist y x < t` is semialgebraic, and its
fiber over every `t > 0` is nonempty since `x ∈ closure A`. Semialgebraic choice
(`TauCeti.IsSemialgebraic.exists_isSemialgebraicOn_sumElim_mem`) gives a semialgebraic section
`f`, which is continuous on some interval `(0, δ)`
(`TauCeti.IsSemialgebraicOn.exists_pos_forall_Ioo_continuousAt`). Set `γ 0 = x` and
`γ t = f ![t]` otherwise; then `dist (γ t) x < t` for `0 < t < δ`, so `γ` is continuous at `0`
from the right.

## References

* J. Bochnak, M. Coste, M.-F. Roy, *Real Algebraic Geometry*, Springer, 1998, Theorem 2.5.5.
* L. van den Dries, *Tame Topology and o-minimal Structures*, Cambridge University Press, 1998,
  Chapter 6, Section 1.
-/

public section

open Set MvPolynomial

namespace TauCeti

variable {σ : Type*}

/-- The set of pairs `(t, y)`, written as points of `Fin 1 ⊕ σ → ℝ`, with `0 < t`, `y ∈ A` and
`dist y x < t`, is semialgebraic when `A` is. -/
private theorem isSemialgebraic_curveSelectionSet [Fintype σ] {A : Set (σ → ℝ)}
    (hA : IsSemialgebraic A) (x : σ → ℝ) :
    IsSemialgebraic {z : Fin 1 ⊕ σ → ℝ |
      0 < z (.inl 0) ∧ z ∘ Sum.inr ∈ A ∧ dist (z ∘ Sum.inr) x < z (.inl 0)} := by
  have h := ((isSemialgebraic_eval_pos (X (.inl 0) : MvPolynomial (Fin 1 ⊕ σ) ℝ)).inter
    (hA.preimage_comp Sum.inr)).inter
    (isSemialgebraic_setOf_dist_eval_lt (fun i ↦ X (.inr i)) (fun i ↦ C (x i)) (X (.inl 0)))
  convert h using 1
  ext z
  simp [and_assoc, Function.comp_def]

/-- **Curve selection**: a point `x` in the closure of a semialgebraic set `A ⊆ σ → ℝ` is the
starting point of a curve `γ`, continuous on `[0, ε)` for some `ε > 0`, which lies in `A` on
`(0, ε)` and is semialgebraic there, as the function `s ↦ γ (s 0)` of the line `Fin 1 → ℝ`. -/
theorem IsSemialgebraic.exists_curve_of_mem_closure [Finite σ] {A : Set (σ → ℝ)}
    (hA : IsSemialgebraic A) {x : σ → ℝ} (hx : x ∈ _root_.closure A) :
    ∃ ε > 0, ∃ γ : ℝ → σ → ℝ, γ 0 = x ∧ ContinuousOn γ (Ico 0 ε) ∧ (∀ t ∈ Ioo 0 ε, γ t ∈ A) ∧
      IsSemialgebraicOn (fun s : Fin 1 → ℝ ↦ γ (s 0)) {s | s 0 ∈ Ioo 0 ε} := by
  have := Fintype.ofFinite σ
  obtain ⟨f, hf, hfS⟩ :=
    (isSemialgebraic_curveSelectionSet hA x).exists_isSemialgebraicOn_sumElim_mem
  -- Every parameter `![t]` with `t > 0` has a nonempty fiber.
  have hD {t : ℝ} (ht : 0 < t) :
      ![t] ∈ {s : Fin 1 → ℝ | ∃ y, Sum.elim s y ∈ {z : Fin 1 ⊕ σ → ℝ |
        0 < z (.inl 0) ∧ z ∘ Sum.inr ∈ A ∧ dist (z ∘ Sum.inr) x < z (.inl 0)}} := by
    obtain ⟨y, hyA, hy⟩ := Metric.mem_closure_iff.1 hx t ht
    exact ⟨y, by simpa [dist_comm] using ⟨ht, hyA, hy⟩⟩
  have hf_mem {t : ℝ} (ht : 0 < t) : f ![t] ∈ A ∧ dist (f ![t]) x < t := by
    simpa [ht] using hfS _ (hD ht)
  have hline (s : Fin 1 → ℝ) : ![s 0] = s := by ext i; fin_cases i; rfl
  obtain ⟨δ, hδ, hcont⟩ := hf.exists_pos_forall_Ioo_continuousAt one_pos fun t ht ↦ hD ht.1
  set γ : ℝ → σ → ℝ := Function.update (fun t ↦ f ![t]) 0 x
  have hγ0 : γ 0 = x := Function.update_self ..
  have hγ {t : ℝ} (ht : t ≠ 0) : γ t = f ![t] := Function.update_of_ne ht _ _
  refine ⟨δ, hδ, γ, hγ0, ?_, fun t ht ↦ hγ ht.1.ne' ▸ (hf_mem ht.1).1, ?_⟩
  · intro t ht
    rcases ht.1.eq_or_lt with rfl | ht₀
    · -- At `0`, `dist (γ s) x < s` for `0 < s < δ`.
      refine Metric.continuousWithinAt_iff.2 fun ε hε ↦ ⟨ε, hε, fun {s} hs hsε ↦ ?_⟩
      rcases hs.1.eq_or_lt with rfl | hs₀
      · simpa using hε
      rw [hγ hs₀.ne', hγ0]
      rw [Real.dist_0_eq_abs, abs_of_pos hs₀] at hsε
      exact (hf_mem hs₀).2.trans hsε
    · have hc : ContinuousAt (f ∘ fun t : ℝ ↦ ![t]) t :=
        ContinuousAt.comp (g := f) (hcont t ⟨ht₀, ht.2⟩) (by fun_prop)
      refine (hc.congr ?_).continuousWithinAt
      filter_upwards [lt_mem_nhds ht₀] with s hs
      exact (hγ hs.ne').symm
  · have hI : IsSemialgebraic {s : Fin 1 → ℝ | s 0 ∈ Ioo 0 δ} := by
      have h : {s : Fin 1 → ℝ | s 0 ∈ Ioo 0 δ} =
          {s | eval s (C 0) < eval s (X 0)} ∩ {s | eval s (X 0) < eval s (C δ)} := by
        ext s; simp
      exact h ▸ (isSemialgebraic_eval_lt _ _).inter (isSemialgebraic_eval_lt _ _)
    refine (hf.mono hI fun s hs ↦ hline s ▸ hD hs.1).congr fun s hs ↦ ?_
    simp only [hγ hs.1.ne', hline]

end TauCeti

end
