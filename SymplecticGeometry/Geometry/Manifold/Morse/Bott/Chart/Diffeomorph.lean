/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import TauCeti.Geometry.Manifold.Morse.Bott.Chart.Basic
import TauCeti.Geometry.Manifold.PullbackGroupoid

/-!
# Morse–Bott charts under diffeomorphisms

For a diffeomorphism `σ : M' ≃ M` between boundaryless manifolds modelled on `E`, a Morse–Bott
chart `φ` for `f` at `σ x'` pulls back to the Morse–Bott chart `φ ∘ σ` for `f ∘ σ` at `x'`, with
the same coordinates and weights.

## Main declarations

* `TauCeti.MorseBottChart.pullback`: the pull-back `φ ∘ σ` of a Morse–Bott chart along a
  diffeomorphism, with `TauCeti.MorseBottChart.pullback_toChart`,
  `TauCeti.MorseBottChart.pullback_source`, `TauCeti.MorseBottChart.pullback_target`,
  `TauCeti.MorseBottChart.pullback_coord` and `TauCeti.MorseBottChart.pullback_weight`.

## Implementation notes

The declarations are in the namespace `TauCeti`, since they concern only Tau Ceti's notions. The
construction follows Tau Ceti's `TauCeti.MorseChart.pullback`, which does the same for Morse
charts: the chart is composed with the diffeomorphism, and the coordinates and weights are kept.
A Morse–Bott chart may have weights `0`, as the Morse–Bott chart of the quadratic part of a
birth–death chart does, so `TauCeti.MorseChart.pullback` does not apply to it.
-/

public section

open Function
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace E M'] [IsManifold 𝓘(ℝ, E) ∞ M']
  (σ : M' ≃ₘ^∞⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M) {x' : M'}

namespace MorseBottChart

/-- The pull-back of a Morse–Bott chart `φ` for `f` at `σ x'` along a diffeomorphism
`σ : M' ≃ M`: the Morse–Bott chart `φ ∘ σ` for `f ∘ σ` at `x'`, with the coordinates and the
weights of `φ`. -/
noncomputable def pullback (φ : MorseBottChart E f (σ x')) : MorseBottChart E (f ∘ σ) x' where
  toChart := σ.toHomeomorph.transOpenPartialHomeomorph φ.toChart
  mem_maximalAtlas := σ.transOpenPartialHomeomorph_mem_maximalAtlas le_rfl φ.mem_maximalAtlas
  mem_source := φ.mem_source
  apply_self := φ.apply_self
  coord := φ.coord
  weight := φ.weight
  weight_eq_neg_one_or_eq_zero_or_eq_one := φ.weight_eq_neg_one_or_eq_zero_or_eq_one
  eq_quadratic y hy := by
    simpa using φ.eq_quadratic (σ y) hy

variable (φ : MorseBottChart E f (σ x'))

/-- The chart of the pull-back of a Morse–Bott chart is `φ` composed with `σ`. -/
theorem pullback_toChart :
    (φ.pullback σ).toChart = σ.toHomeomorph.transOpenPartialHomeomorph φ.toChart :=
  (rfl)

/-- The chart of the pull-back of a Morse–Bott chart is `φ ∘ σ`, as a function. -/
@[simp]
theorem coe_pullback_toChart : ⇑(φ.pullback σ).toChart = φ.toChart ∘ σ :=
  (rfl)

/-- The source of the pull-back of a Morse–Bott chart is the preimage of the source. -/
@[simp]
theorem pullback_source : (φ.pullback σ).toChart.source = σ ⁻¹' φ.toChart.source :=
  (rfl)

/-- The target of the pull-back of a Morse–Bott chart is the target of `φ`. -/
@[simp]
theorem pullback_target : (φ.pullback σ).toChart.target = φ.toChart.target :=
  (rfl)

/-- The pull-back of a Morse–Bott chart keeps the coordinates. -/
@[simp]
theorem pullback_coord : (φ.pullback σ).coord = φ.coord :=
  (rfl)

/-- The pull-back of a Morse–Bott chart keeps the weights. -/
@[simp]
theorem pullback_weight : (φ.pullback σ).weight = φ.weight :=
  (rfl)

end MorseBottChart

end TauCeti

end
