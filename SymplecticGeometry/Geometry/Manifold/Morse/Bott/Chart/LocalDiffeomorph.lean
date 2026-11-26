/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.Morse.Bott.Chart.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv

/-!
# Morse–Bott charts along local diffeomorphisms

Let `Φ : M' → M` be a smooth local diffeomorphism at `y`, where `M'` is modelled on `E'` and `M`
on `E`, and let `A : E' ≃L[ℝ] E` be the derivative of `Φ` at `y`. A Morse–Bott chart `φ` for `f`
at `Φ y`, with chart `ψ`, pulls back to a Morse–Bott chart for `f ∘ Φ` at `y` whose chart is
`A⁻¹ ∘ ψ ∘ Φ` near `y`. Its coordinates are those of `φ` after `A`, and its weights those of `φ`,
both reindexed along `finrank E' = finrank E`.

## Main declarations

* `TauCeti.MorseBottChart.congr`: a Morse–Bott chart for `f` is one for any function that agrees
  with `f` on its source, with the same chart, coordinates and weights.
* `TauCeti.MorseBottChart.pullback`: the pull-back of a Morse–Bott chart along a local
  diffeomorphism at a point, with `TauCeti.MorseBottChart.mem_pullback_source`,
  `TauCeti.MorseBottChart.pullback_apply`, `TauCeti.MorseBottChart.pullback_coord_apply` and
  `TauCeti.MorseBottChart.pullback_weight`.

## Implementation notes

The declarations are in the namespace `TauCeti`, since they concern Tau Ceti's notions. The chart
`A⁻¹ ∘ ψ ∘ Φ` is built from the chosen local inverse of `Φ`; it lies in the maximal atlas by Tau
Ceti's `IsManifold.mem_maximalAtlas_iff_forall_isLocalDiffeomorphAt`. Along a diffeomorphism
between manifolds with the same model, this replaces a pull-back in the style of Tau Ceti's
`TauCeti.MorseChart.pullback`. A Morse–Bott chart may have weights `0`, as the Morse–Bott chart
of the quadratic part of a birth–death chart does, so Tau Ceti's results on Morse charts do not
apply to it.
-/

public section

open Function Set
open scoped ContDiff Manifold

namespace TauCeti

namespace MorseBottChart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}

/-! ### Changing the function off the source -/

section Congr

variable {x : M} (φ : MorseBottChart E f x) {g : M → ℝ} (h : EqOn g f φ.toChart.source)

/-- A Morse–Bott chart `φ` for `f` at `x` is a Morse–Bott chart for any `g` that agrees with `f`
on the source of `φ`, with the chart, the coordinates and the weights of `φ`. -/
noncomputable def congr : MorseBottChart E g x where
  toChart := φ.toChart
  mem_maximalAtlas := φ.mem_maximalAtlas
  mem_source := φ.mem_source
  apply_self := φ.apply_self
  coord := φ.coord
  weight := φ.weight
  weight_eq_neg_one_or_eq_zero_or_eq_one := φ.weight_eq_neg_one_or_eq_zero_or_eq_one
  eq_quadratic y hy := by rw [h hy, h φ.mem_source]; exact φ.eq_quadratic y hy

/-- The chart of `φ.congr h` is that of `φ`. -/
@[simp]
theorem congr_toChart : (φ.congr h).toChart = φ.toChart :=
  (rfl)

/-- The coordinates of `φ.congr h` are those of `φ`. -/
@[simp]
theorem congr_coord : (φ.congr h).coord = φ.coord :=
  (rfl)

/-- The weights of `φ.congr h` are those of `φ`. -/
@[simp]
theorem congr_weight : (φ.congr h).weight = φ.weight :=
  (rfl)

end Congr

/-! ### Pull-back along a local diffeomorphism -/

section Pullback

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace E' M'] [IsManifold 𝓘(ℝ, E') ∞ M']
  {Φ : M' → M} {y : M'} (φ : MorseBottChart E f (Φ y))
  (hΦ : IsLocalDiffeomorphAt 𝓘(ℝ, E') 𝓘(ℝ, E) ∞ Φ y) (A : E' ≃L[ℝ] E)

/-- The chart `A⁻¹ ∘ ψ ∘ Φ` of `TauCeti.MorseBottChart.pullback`, as a partial diffeomorphism. -/
private noncomputable def pullbackChart : PartialDiffeomorph 𝓘(ℝ, E') 𝓘(ℝ, E') M' E' ∞ :=
  (hΦ.localInverse.symm.trans (φ.toChart.toPartialDiffeomorph φ.mem_maximalAtlas)).trans
    A.symm.toPartialDiffeomorph

omit [IsManifold 𝓘(ℝ, E') ∞ M'] in
private theorem mem_pullbackChart_source_iff {z : M'} :
    z ∈ (pullbackChart φ hΦ A).toOpenPartialHomeomorph.source ↔
      z ∈ hΦ.localInverse.target ∧ Φ z ∈ φ.toChart.source := by
  simp only [pullbackChart, PartialDiffeomorph.toOpenPartialHomeomorph_source,
    PartialDiffeomorph.trans_source, OpenPartialHomeomorph.toPartialDiffeomorph_toPartialEquiv,
    ContinuousLinearEquiv.toPartialDiffeomorph_toPartialEquiv, Equiv.toPartialEquiv_source,
    mem_inter_iff, mem_preimage, mem_univ, and_true]
  exact and_congr_right fun h ↦ by rw [hΦ.eqOn_localInverse_symm h]

omit [IsManifold 𝓘(ℝ, E') ∞ M'] in
private theorem pullbackChart_apply {z : M'}
    (hz : z ∈ (pullbackChart φ hΦ A).toOpenPartialHomeomorph.source) :
    A ((pullbackChart φ hΦ A).toOpenPartialHomeomorph z) = φ.toChart (Φ z) := by
  simp [pullbackChart, hΦ.eqOn_localInverse_symm ((mem_pullbackChart_source_iff φ hΦ A).1 hz).1]

/-- The **pull-back of a Morse–Bott chart along a local diffeomorphism.** If `Φ : M' → M` is a
smooth local diffeomorphism at `y`, where `M'` is modelled on `E'` and `M` on `E`, and
`A : E' ≃L[ℝ] E` is a linear equivalence of the models, such as the derivative of `Φ` at `y`, then
a Morse–Bott chart `φ` for `f` at `Φ y` with chart `ψ` gives the Morse–Bott chart for `f ∘ Φ` at
`y` with chart `A⁻¹ ∘ ψ ∘ Φ` near `y`, with the coordinates of `φ` after `A` and the weights of
`φ`, both reindexed along `finrank E' = finrank E`. -/
noncomputable def pullback : MorseBottChart E' (f ∘ Φ) y where
  toChart := (pullbackChart φ hΦ A).toOpenPartialHomeomorph
  mem_maximalAtlas := (IsManifold.mem_maximalAtlas_iff_forall_isLocalDiffeomorphAt _).2
    fun _ hz ↦ (pullbackChart φ hΦ A).isLocalDiffeomorphAt _ _ _ hz
  mem_source := (mem_pullbackChart_source_iff φ hΦ A).2
    ⟨hΦ.localInverse_mem_target, φ.mem_source⟩
  apply_self := A.injective <| by
    rw [pullbackChart_apply φ hΦ A ((mem_pullbackChart_source_iff φ hΦ A).2
      ⟨hΦ.localInverse_mem_target, φ.mem_source⟩), map_zero]
    exact φ.apply_self
  coord := A.toLinearEquiv ≪≫ₗ φ.coord ≪≫ₗ
    LinearEquiv.funCongrLeft ℝ ℝ (finCongr A.toLinearEquiv.finrank_eq)
  weight := φ.weight ∘ finCongr A.toLinearEquiv.finrank_eq
  weight_eq_neg_one_or_eq_zero_or_eq_one _ := φ.weight_eq_neg_one_or_eq_zero_or_eq_one _
  eq_quadratic z hz := by
    have hz' := (mem_pullbackChart_source_iff φ hΦ A).1 hz
    rw [comp_apply, comp_apply, φ.eq_quadratic (Φ z) hz'.2]
    simp only [comp_apply, LinearEquiv.trans_apply, LinearEquiv.funCongrLeft_apply,
      LinearMap.funLeft_apply, ContinuousLinearEquiv.coe_toLinearEquiv,
      pullbackChart_apply φ hΦ A hz]
    congr 2
    exact ((finCongr A.toLinearEquiv.finrank_eq).sum_comp fun j ↦
      φ.weight j * φ.coord (φ.toChart (Φ z)) j ^ 2).symm

/-- A point lies in the source of the pull-back of a Morse–Bott chart along `Φ` if and only if it
lies in the target of the chosen local inverse of `Φ` and `Φ` maps it into the source of `φ`. -/
theorem mem_pullback_source {z : M'} :
    z ∈ (φ.pullback hΦ A).toChart.source ↔
      z ∈ hΦ.localInverse.target ∧ Φ z ∈ φ.toChart.source :=
  mem_pullbackChart_source_iff φ hΦ A

/-- The source of the pull-back of a Morse–Bott chart along `Φ` lies in the preimage of the
source of `φ`. -/
theorem pullback_source_subset : (φ.pullback hΦ A).toChart.source ⊆ Φ ⁻¹' φ.toChart.source :=
  fun _ hz ↦ ((φ.mem_pullback_source hΦ A).1 hz).2

/-- On its source, the chart of the pull-back of a Morse–Bott chart along `Φ`, followed by `A`,
is the chart of `φ` after `Φ`. -/
theorem pullback_apply {z : M'} (hz : z ∈ (φ.pullback hΦ A).toChart.source) :
    A ((φ.pullback hΦ A).toChart z) = φ.toChart (Φ z) :=
  pullbackChart_apply φ hΦ A hz

/-- The coordinates of the pull-back of a Morse–Bott chart along `Φ` are those of `φ` after `A`,
reindexed along `finrank E' = finrank E`. -/
theorem pullback_coord_apply (v : E') (i : Fin (Module.finrank ℝ E')) :
    (φ.pullback hΦ A).coord v i = φ.coord (A v) (finCongr A.toLinearEquiv.finrank_eq i) := by
  simp [pullback]

/-- The weights of the pull-back of a Morse–Bott chart along `Φ` are those of `φ`, reindexed
along `finrank E' = finrank E`. -/
theorem pullback_weight :
    (φ.pullback hΦ A).weight = φ.weight ∘ finCongr A.toLinearEquiv.finrank_eq :=
  (rfl)

end Pullback

end MorseBottChart

end TauCeti

end
