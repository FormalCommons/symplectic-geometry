/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.Pullback

/-!
# Orientations carried along a diffeomorphism

Let `e : M ≃ₘ^n⟮I, I'⟯ N` be a `C^n` diffeomorphism of real manifolds with corners, `n ≠ 0`. An
orientation `o` of `M` is carried to an orientation `o.map e hn hι` of `N`: the pullback of `o`
along `e.symm`, in the sense of Tau Ceti's `TauCeti.Manifold.Orientation.pullback`. The map `e`
preserves orientation from `o` to it, and it is the unique orientation of `N` from which `e.symm`
preserves orientation at every point [Lee, Prop. 15.15].

The hypothesis `hι` says that `ι` indexes orientations of the model of `N`. It follows from
`o.card_eq` when `M` is nonempty, but not when `M` and `N` are empty, so it is a hypothesis; when
`M` and `N` have the same model vector space, it is `o.card_eq`.

## Main definitions

* `TauCeti.Manifold.Orientation.map o e hn hι`: the orientation `o` of `M`, carried to `N` along
  the diffeomorphism `e`.

## Main results

* `TauCeti.Manifold.Orientation.isOrientationPreservingAt_map`,
  `TauCeti.Manifold.Orientation.isOrientationPreservingAt_map_symm`: `e` preserves orientation
  from `o` to the carried orientation, and `e.symm` from the carried orientation to `o`.
* `TauCeti.Manifold.Orientation.eq_map_iff`: the carried orientation is the only one from which
  `e.symm` preserves orientation at every point.
* `TauCeti.Manifold.Orientation.map_neg`: carrying commutes with reversing the orientation.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 15.
-/

public section

open Module

open scoped Manifold ContDiff

namespace TauCeti.Manifold.Orientation

variable {E E' H H' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [TopologicalSpace H]
  [TopologicalSpace H'] {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [TopologicalSpace N]
  [ChartedSpace H' N] [IsManifold I' 1 N] {ι : Type*} [Fintype ι] {n : ℕ∞ω}

/-- An orientation `o` of `M`, carried to `N` along a `C^n` diffeomorphism `e : M → N`, `n ≠ 0`:
the pullback of `o` along `e.symm`. It is the orientation of `N` for which `e` preserves
orientation (`isOrientationPreservingAt_map`), and the only one for which `e.symm` does
(`eq_map_iff`). -/
noncomputable def map (o : Orientation I M ι) (e : M ≃ₘ^n⟮I, I'⟯ N) (hn : n ≠ 0)
    (hι : Fintype.card ι = finrank ℝ E') : Orientation I' N ι :=
  o.pullback (e.symm.contMDiff.of_le (ENat.one_le_iff_ne_zero_withTop.2 hn))
    (fun _ ↦ e.symm.isInvertible_mfderiv hn) hι

theorem map_def (o : Orientation I M ι) (e : M ≃ₘ^n⟮I, I'⟯ N) (hn : n ≠ 0)
    (hι : Fintype.card ι = finrank ℝ E') :
    o.map e hn hι = o.pullback (e.symm.contMDiff.of_le (ENat.one_le_iff_ne_zero_withTop.2 hn))
      (fun _ ↦ e.symm.isInvertible_mfderiv hn) hι :=
  (rfl)

/-- The inverse of `e` preserves orientation at every point, from the carried orientation to
`o`. -/
theorem isOrientationPreservingAt_map_symm (o : Orientation I M ι) (e : M ≃ₘ^n⟮I, I'⟯ N)
    (hn : n ≠ 0) (hι : Fintype.card ι = finrank ℝ E') (y : N) :
    IsOrientationPreservingAt (o.map e hn hι) o e.symm y := by
  rw [map_def]
  exact isOrientationPreservingAt_pullback _ _ _ _ y

/-- The diffeomorphism `e` preserves orientation at every point, from `o` to the carried
orientation. -/
theorem isOrientationPreservingAt_map (o : Orientation I M ι) (e : M ≃ₘ^n⟮I, I'⟯ N) (hn : n ≠ 0)
    (hι : Fintype.card ι = finrank ℝ E') (x : M) :
    IsOrientationPreservingAt o (o.map e hn hι) e x := by
  -- `e.symm.symm` is `e` up to structure eta.
  exact (isOrientationPreservingAt_map_symm o e hn hι (e.symm.symm x)).diffeomorph_symm hn

/-- The carried orientation is the only orientation of `N` from which the inverse of `e`
preserves orientation at every point. -/
theorem eq_map_iff {o : Orientation I M ι} {o' : Orientation I' N ι} {e : M ≃ₘ^n⟮I, I'⟯ N}
    (hn : n ≠ 0) (hι : Fintype.card ι = finrank ℝ E') :
    o' = o.map e hn hι ↔ ∀ y, IsOrientationPreservingAt o' o e.symm y := by
  rw [map_def, eq_pullback_iff]

/-- Carrying the opposite orientation gives the opposite of the carried orientation. -/
@[simp]
theorem map_neg (o : Orientation I M ι) (e : M ≃ₘ^n⟮I, I'⟯ N) (hn : n ≠ 0)
    (hι : Fintype.card ι = finrank ℝ E') : (-o).map e hn hι = -o.map e hn hι := by
  simp only [map_def, pullback_neg]

end TauCeti.Manifold.Orientation

end
