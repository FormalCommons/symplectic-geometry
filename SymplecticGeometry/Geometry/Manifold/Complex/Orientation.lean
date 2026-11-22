/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Orientation.Preserving.FromTauCeti
public import TauCeti.Geometry.Manifold.Complex.Orientation

/-!
# The canonical orientation of a complex curve, indexed by `Fin 2`

Tau Ceti's `TauCeti.complexManifoldOrientation E M` orients a complex manifold `M` modelled on
`𝓘(ℂ, E)` as a real manifold, with index type `Fin (2 * finrank ℂ E)`. For a complex curve,
`finrank ℂ E = 1`, statements about real surfaces use the index type `Fin 2` instead. This file
reindexes the canonical orientation once, for every such `E` and `M`:

* `SymplecticGeometry.complexCurveOrientation`: the canonical orientation of a complex curve,
  indexed by `Fin 2`, with `SymplecticGeometry.complexCurveOrientation_def`;
* `SymplecticGeometry.orientationAt_complexCurveOrientation`: at every point it is Tau Ceti's
  complex orientation `TauCeti.complexOrientation E` of the model, reindexed to `Fin 2`;
* `Diffeomorph.isOrientationPreservingAt_complexCurveOrientation`: biholomorphisms preserve it.

Tau Ceti's `TauCeti.complexHomologicalOrientation` (in
`TauCeti/Geometry/Manifold/Complex/FundamentalClass.lean`) reindexes the same orientation to
`Fin 2` for Riemann surfaces modelled on `ℂ`, as a homological orientation.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §1.5.
-/

public section

open Module TauCeti
open scoped Manifold ContDiff TauCeti.ComplexManifold

namespace SymplecticGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) 1 M]

variable (E M) in
/-- The canonical orientation of a complex curve `M`, a complex manifold modelled on `𝓘(ℂ, E)`
with `finrank ℂ E = 1`, as an orientation of the underlying real surface indexed by `Fin 2`: Tau
Ceti's `complexManifoldOrientation E M`, reindexed from `Fin (2 * finrank ℂ E)`. When `h` is
omitted, `simp` proves it, as it does for `ℂ` and `Fin 1 → ℂ`. -/
noncomputable def complexCurveOrientation (h : finrank ℂ E = 1 := by simp) :
    Manifold.Orientation 𝓘(ℝ, E) M (Fin 2) :=
  (complexManifoldOrientation E M).reindex (finCongr (by rw [h]))

theorem complexCurveOrientation_def (h : finrank ℂ E = 1) :
    complexCurveOrientation E M h =
      (complexManifoldOrientation E M).reindex (finCongr (by rw [h])) :=
  (rfl)

/-- At every point of a complex curve, `complexCurveOrientation` is the complex orientation of
the model space `E`, reindexed to `Fin 2`. -/
@[simp]
theorem orientationAt_complexCurveOrientation (h : finrank ℂ E = 1) (x : M) :
    (complexCurveOrientation E M h).orientationAt x =
      Orientation.reindex ℝ (TangentSpace 𝓘(ℝ, E) x) (finCongr (by rw [h]))
        (complexOrientation E) := by
  rw [complexCurveOrientation_def, Manifold.Orientation.orientationAt_reindex,
    orientationAt_complexManifoldOrientation_eq_complexOrientation]

/-- A biholomorphism `Φ : M → N` of complex curves (a `C^n` diffeomorphism for the complex
models, `n ≠ 0`) carries `complexCurveOrientation` of `M` to that of `N` at every point. -/
theorem _root_.Diffeomorph.isOrientationPreservingAt_complexCurveOrientation
    {N : Type*} [TopologicalSpace N] [ChartedSpace E N] [IsManifold 𝓘(ℂ, E) 1 N]
    (h : finrank ℂ E = 1) (n : ℕ∞ω) [NeZero n] (Φ : M ≃ₘ^n⟮𝓘(ℂ, E), 𝓘(ℂ, E)⟯ N) (x : M) :
    Manifold.Orientation.IsOrientationPreservingAt (complexCurveOrientation E M h)
      (complexCurveOrientation E N h) Φ x := by
  rw [complexCurveOrientation_def, complexCurveOrientation_def]
  exact (Φ.isOrientationPreservingAt_complexManifoldOrientation n x).reindex _

end SymplecticGeometry

end
