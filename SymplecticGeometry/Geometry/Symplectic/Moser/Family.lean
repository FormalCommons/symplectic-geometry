/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.HomotopyOperator

/-!
# Moser's argument along a family and with a parameter

This file holds two forms of Moser's argument near a compact set: along a family of two-forms
running in the Moser time and fixing a compact submanifold, and for the segments
`ω₀ + s dβ_t`, `s ∈ [0, 1]`, for every value of a parameter `t`, relative to a compact set. Both
use the cut-off Moser field `SymplecticGeometry.moserField`. They also need primitives of closed
forms on a star-shaped open set of a normed space that depend smoothly on a parameter, which the
file gives first.

## Parametric radial primitives

Let `U` be an open subset of a real normed space `V`, star-shaped about `0`, and let `α_t`,
`t ∈ N`, be a smooth family of closed `(k + 1)`-forms on `U` over a parameter manifold `N`
(`SymplecticGeometry.IsSmoothFamily`). With the radial contraction
`Φ : U × [0, 1] → U`, `Φ (x, s) = s • x`, the forms `β_t = h (Φ^* α_t)`, the homotopy operator
after pullback along `Φ`, are primitives of the `α_t`
(`TauCeti.SmoothForm.mextDerivₗ_homotopyOperator_mpullback_of_contraction`), and they form a
smooth family (`SymplecticGeometry.IsSmoothFamily.homotopyOperator`). The value of `β_t` at `x`
only involves `α_t` at the points `s • x` of the segment from `0` to `x`, so it vanishes where
`α_t` vanishes along that segment, and `β_t = 0` when `α_t = 0`.

## Main results

* `TauCeti.exists_contMDiff_parametric_radialPrimitive`: a smooth family of closed forms of
  positive degree on a star-shaped open set has a smooth family of primitives, which vanishes at
  every point where the form vanishes along the segment to the centre, and is `0` where the form
  is `0`.

## References

* [A. Weil, *Sur les théorèmes de de Rham*][Weil1952], §2 (the homotopy operator of a
  contraction).
* [R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §4.
* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §3.2
  (Moser's argument).
-/

public section

open Set TopologicalSpace SymplecticGeometry
open scoped Manifold ContDiff

namespace TauCeti

section RadialPrimitive

variable {V F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {EN HN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  {J : ModelWithCorners ℝ EN HN} {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]
  [IsManifold J ∞ N] {k : ℕ}

/-- **Parametric radial primitives.** Let `U` be an open subset of a real normed space,
star-shaped about `0`, and `α_t`, `t ∈ N`, a smooth family of closed `(k + 1)`-forms on `U` with
values in a Banach space, over a parameter manifold `N`. Then there is a smooth family `β_t` of
`k`-forms on `U` with `d β_t = α_t` for every `t`, such that `β_t` vanishes at `x` whenever `α_t`
vanishes at every point of the segment from `0` to `x`, and `β_t = 0` whenever `α_t = 0`. -/
theorem exists_contMDiff_parametric_radialPrimitive {U : Opens V}
    (hU : StarConvex ℝ 0 (U : Set V)) {α : N → SmoothForm 𝓘(ℝ, V) U F (k + 1)}
    (hα : IsSmoothFamily J α) (hcl : ∀ t, mextDerivₗ 𝓘(ℝ, V) (k + 1) (α t) = 0) :
    ∃ β : N → SmoothForm 𝓘(ℝ, V) U F k, IsSmoothFamily J β ∧
      (∀ t, mextDerivₗ 𝓘(ℝ, V) k (β t) = α t) ∧
      (∀ t (x : U), (∀ y : U, (y : V) ∈ segment ℝ 0 (x : V) → (α t).val y = 0) →
        (β t).val x = 0) ∧
      ∀ t, α t = 0 → β t = 0 := by
  -- The radial contraction `Φ (x, s) = s • x` of `U` onto `0`.
  let Φ : U × unitInterval → U := fun p ↦ ⟨(p.2 : ℝ) • (p.1 : V), hU.smul_mem p.1.property
    p.2.property.1 p.2.property.2⟩
  have hΦ : ContMDiff (𝓘(ℝ, V).prod (𝓡∂ 1)) 𝓘(ℝ, V) ∞ Φ := by
    rw [← ContMDiff.subtypeVal_comp_iff]
    exact (contMDiff_subtypeVal_Icc.comp contMDiff_snd).smul
      (contMDiff_subtypeVal.comp contMDiff_fst)
  refine ⟨fun t ↦ SmoothForm.homotopyOperator (SmoothForm.mpullback Φ hΦ (α t)),
    (hα.mpullback Φ hΦ).homotopyOperator, fun t ↦ ?_, fun t x hx ↦ ?_, fun t ht ↦ ?_⟩
  · -- `U` contains `x`, so also `0`, the end point of the contraction.
    refine Subtype.ext (funext fun x ↦ ?_)
    have h0 : (0 : V) ∈ U := by simpa using hU.smul_mem x.property le_rfl zero_le_one
    have hd := SmoothForm.mextDerivₗ_homotopyOperator_mpullback_of_contraction (c := ⟨0, h0⟩) hΦ
      (fun y ↦ Subtype.ext (zero_smul ℝ (y : V))) (fun y ↦ Subtype.ext (one_smul ℝ (y : V)))
      (hcl t)
    rw [hd]
  · rw [SmoothForm.coe_homotopyOperator]
    refine homotopyOperator_apply_eq_zero fun s v ↦ ?_
    rw [SmoothForm.mpullback_apply, hx (Φ (x, s)) ⟨1 - s, s, by simp [s.property.2],
      s.property.1, by simp, by simp [Φ]⟩, ContinuousAlternatingMap.coe_zero, Pi.zero_apply]
  · simp only [ht, map_zero]

end RadialPrimitive

end TauCeti
