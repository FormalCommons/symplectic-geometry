/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DeRham.GoodCover.Basic
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.HomotopyOperator

/-!
# The Poincaré lemma for smooth families of forms

Let `Φ : M × [0, 1] → M` be a smooth contraction of `M` to a point `c`, with `Φ (x, 0) = c` and
`Φ (x, 1) = x`, and let `α_t`, `t ∈ N`, be a smooth family of closed `(k + 1)`-forms on `M` with
values in a Banach space, over any parameter manifold `N`
(`SymplecticGeometry.IsSmoothFamily`). Then the forms `β_t = h (Φ^* α_t)`, the homotopy
operator after pullback along `Φ`, form a smooth family
(`SymplecticGeometry.IsSmoothFamily.mpullback` and
`SymplecticGeometry.IsSmoothFamily.homotopyOperator`), and they are primitives of the `α_t`
(`TauCeti.SmoothForm.mextDerivₗ_homotopyOperator_mpullback_of_contraction`).

On an open set `U` of a real normed space, star-convex about `c`, the contraction is the
straight-line contraction `(x, s) ↦ c + s • (x - c)` (`StarConvex.lineContraction`). The value
of `β_t` at `x` then only involves `α_t` at the points of the segment from `c` to `x`, so `β_t`
vanishes at `x` when `α_t` vanishes along that segment.

## Main results

* `SymplecticGeometry.isSmoothFamily_homotopyOperator_mpullback_and_mextDerivₗ_eq`: for a smooth
  contraction `Φ` and a smooth family `α_t` of closed forms, `t ↦ h (Φ^* α_t)` is a smooth family
  of primitives of the `α_t`.
* `SymplecticGeometry.IsSmoothlyContractible.exists_isSmoothFamily_mextDerivₗ_eq`: on a smoothly
  contractible manifold, a smooth family of closed forms of positive degree has a smooth family
  of primitives.
* `SymplecticGeometry.exists_isSmoothFamily_mextDerivₗ_eq_of_starConvex`: on a star-convex open
  set of a normed space, a smooth family of closed forms of positive degree has a smooth family
  of primitives, which vanishes at every point where the form vanishes along the segment to the
  centre, and is `0` where the form is `0`.

## References

* [A. Weil, *Sur les théorèmes de de Rham*][Weil1952], §2 (the homotopy operator of a
  contraction).
* [R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §4.
-/

public section

open TopologicalSpace TauCeti
open scoped Manifold ContDiff

namespace SymplecticGeometry

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {EN HN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  {J : ModelWithCorners ℝ EN HN} {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]
  [IsManifold J ∞ N] {k : ℕ}

/-- **The parametric Poincaré lemma, through a contraction.** Let `Φ : M × [0, 1] → M` be a
smooth contraction of `M` to `c`, with `Φ (x, 0) = c` and `Φ (x, 1) = x`, and let `α_t`, `t ∈ N`,
be a smooth family of closed `(k + 1)`-forms on `M` with values in a Banach space, over a
parameter manifold `N`. Then `t ↦ h (Φ^* α_t)`, the homotopy operator after pullback along `Φ`,
is a smooth family of `k`-forms, and `d (h (Φ^* α_t)) = α_t` for every `t`. -/
theorem isSmoothFamily_homotopyOperator_mpullback_and_mextDerivₗ_eq {c : M}
    {Φ : M × unitInterval → M} (hΦ : ContMDiff (I.prod (𝓡∂ 1)) I ∞ Φ) (h₀ : ∀ x, Φ (x, 0) = c)
    (h₁ : ∀ x, Φ (x, 1) = x) {α : N → SmoothForm I M F (k + 1)} (hα : IsSmoothFamily J α)
    (hcl : ∀ t, mextDerivₗ I (k + 1) (α t) = 0) :
    IsSmoothFamily J (fun t ↦ SmoothForm.homotopyOperator (SmoothForm.mpullback Φ hΦ (α t))) ∧
      ∀ t, mextDerivₗ I k (SmoothForm.homotopyOperator (SmoothForm.mpullback Φ hΦ (α t))) =
        α t :=
  ⟨(hα.mpullback Φ hΦ).homotopyOperator, fun t ↦
    SmoothForm.mextDerivₗ_homotopyOperator_mpullback_of_contraction hΦ h₀ h₁ (hcl t)⟩

/-- **The parametric Poincaré lemma.** On a smoothly contractible manifold `M`, a smooth family
`α_t`, `t ∈ N`, of closed `(k + 1)`-forms with values in a Banach space, over a parameter
manifold `N`, has a smooth family `β_t` of primitives: `d β_t = α_t` for every `t`. -/
theorem IsSmoothlyContractible.exists_isSmoothFamily_mextDerivₗ_eq
    (hM : IsSmoothlyContractible I M) {α : N → SmoothForm I M F (k + 1)}
    (hα : IsSmoothFamily J α) (hcl : ∀ t, mextDerivₗ I (k + 1) (α t) = 0) :
    ∃ β : N → SmoothForm I M F k, IsSmoothFamily J β ∧ ∀ t, mextDerivₗ I k (β t) = α t := by
  obtain ⟨c, Φ, hΦ, h₀, h₁⟩ := isSmoothlyContractible_def.1 hM
  exact ⟨_, isSmoothFamily_homotopyOperator_mpullback_and_mextDerivₗ_eq hΦ h₀ h₁ hα hcl⟩

section StarConvex

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **Parametric radial primitives.** Let `U` be an open subset of a real normed space,
star-convex about `c`, and `α_t`, `t ∈ N`, a smooth family of closed `(k + 1)`-forms on `U` with
values in a Banach space, over a parameter manifold `N`. Then there is a smooth family `β_t` of
`k`-forms on `U` with `d β_t = α_t` for every `t`, such that `β_t` vanishes at `x` whenever `α_t`
vanishes at every point of the segment from `c` to `x`, and `β_t = 0` whenever `α_t = 0`. -/
theorem exists_isSmoothFamily_mextDerivₗ_eq_of_starConvex {U : Opens V} {c : V}
    (hU : StarConvex ℝ c (U : Set V)) {α : N → SmoothForm 𝓘(ℝ, V) U F (k + 1)}
    (hα : IsSmoothFamily J α) (hcl : ∀ t, mextDerivₗ 𝓘(ℝ, V) (k + 1) (α t) = 0) :
    ∃ β : N → SmoothForm 𝓘(ℝ, V) U F k, IsSmoothFamily J β ∧
      (∀ t, mextDerivₗ 𝓘(ℝ, V) k (β t) = α t) ∧
      (∀ t (x : U), (∀ y : U, (y : V) ∈ segment ℝ c (x : V) → (α t).val y = 0) →
        (β t).val x = 0) ∧
      ∀ t, α t = 0 → β t = 0 := by
  rcases isEmpty_or_nonempty U with hU₀ | ⟨⟨x₀⟩⟩
  · -- On the empty set, all forms vanish.
    have h0 : ∀ {m : ℕ} (γ : SmoothForm 𝓘(ℝ, V) U F m), γ = 0 := fun _ ↦
      Subtype.ext (funext fun x ↦ isEmptyElim x)
    exact ⟨fun _ ↦ 0, isSmoothFamily_const 0, fun t ↦ (h0 _).trans (h0 _).symm,
      fun _ x ↦ isEmptyElim x, fun _ _ ↦ rfl⟩
  obtain ⟨hβ, hdβ⟩ := isSmoothFamily_homotopyOperator_mpullback_and_mextDerivₗ_eq
    hU.contMDiff_lineContraction (hU.lineContraction_zero (hU.mem ⟨x₀, x₀.property⟩))
    hU.lineContraction_one hα hcl
  refine ⟨_, hβ, hdβ, fun t x hx ↦ ?_, fun t ht ↦ by simp only [ht, map_zero]⟩
  rw [SmoothForm.coe_homotopyOperator]
  refine homotopyOperator_apply_eq_zero fun s v ↦ ?_
  rw [SmoothForm.mpullback_apply, hx (hU.lineContraction (x, s)) (by
    simpa using lineMap_mem_segment ℝ c (x : V) s.property), ContinuousAlternatingMap.coe_zero,
    Pi.zero_apply]

end StarConvex

end SymplecticGeometry

end
