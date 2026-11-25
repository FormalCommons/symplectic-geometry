/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Basic
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Diffeomorph
public import TauCeti.Geometry.Manifold.SmoothIsotopy.Basic

/-!
# Smooth isotopies from diffeotopies of the source

A smooth embedding `f : P → M` and a diffeotopy `Φ` of `P` give the smooth isotopy
`(t, x) ↦ f (Φ (t, x))`, from `f` to `f ∘ Φ₁`: each slice is `f` precomposed with the
diffeomorphism `Φ_t` (Tau Ceti's `TauCeti.isSmoothEmbedding_comp_diffeomorph`). The construction
follows Tau Ceti's `TauCeti.Diffeotopy.smoothIsotopy`
(`TauCeti/Geometry/Manifold/SmoothIsotopy/Diffeotopy.lean`), which moves `f` by a diffeotopy of
`M` instead.

## Main definitions

* `TauCeti.Diffeotopy.precompSmoothIsotopy Φ f`: the isotopy `(t, x) ↦ f (Φ (t, x))` of a smooth
  embedding `f` by a diffeotopy `Φ` of its source, from `f` to `f ∘ Φ₁`.

## References

* M. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Chapter 8, §8.1.
-/

public noncomputable section

open scoped Manifold ContDiff

namespace TauCeti.Diffeotopy

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {P : Type*} [TopologicalSpace P] [ChartedSpace H' P]
  {n : ℕ∞ω} [IsManifold J n P]

/-- The smooth isotopy `(t, x) ↦ f (Φ (t, x))` of a smooth embedding `f : P → M` given by a
diffeotopy `Φ` of its source, from `f` to `f ∘ Φ₁`. It is the source-side counterpart of Tau
Ceti's `TauCeti.Diffeotopy.smoothIsotopy`, which moves `f` by a diffeotopy of its target. -/
def precompSmoothIsotopy (Φ : Diffeotopy J n P) (f : SmoothEmbedding J I n P M) :
    SmoothIsotopy f.toContMDiffMap (f.compDiffeomorph Φ.final).toContMDiffMap where
  toContMDiffMap := ⟨fun p ↦ f (Φ p), f.contMDiff.comp Φ.contMDiff⟩
  map_zero_left x := congrArg f (Φ.apply_zero x)
  map_one_left x := by simp [Φ.final_apply]
  isSmoothEmbedding t := by
    dsimp
    simpa only [Function.comp_def, Diffeotopy.timeSlice_apply] using
      isSmoothEmbedding_comp_diffeomorph (Φ.timeSlice t) f.isSmoothEmbedding

@[simp]
theorem precompSmoothIsotopy_apply (Φ : Diffeotopy J n P) (f : SmoothEmbedding J I n P M)
    (p : unitInterval × P) : Φ.precompSmoothIsotopy f p = f (Φ p) :=
  (rfl)

end TauCeti.Diffeotopy

end
