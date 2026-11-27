/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.Pullback
import TauCeti.Geometry.Manifold.Diffeomorph.Basic

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
* `TauCeti.Manifold.Orientation.eq_map_iff`, `TauCeti.Manifold.Orientation.eq_map_iff'`: the
  carried orientation is the only one from which `e.symm` preserves orientation at every point,
  and the only one to which `e` does.
* `TauCeti.Manifold.Orientation.map_neg`: carrying commutes with reversing the orientation.
* `TauCeti.Manifold.Orientation.map_refl`, `TauCeti.Manifold.Orientation.map_trans`,
  `TauCeti.Manifold.Orientation.map_symm_map`, `TauCeti.Manifold.Orientation.map_map_symm`:
  carrying along the identity, along a composite, along `e` and then back, and along `e.symm`
  and then back.

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
  {E'' H'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E''] [FiniteDimensional ℝ E'']
  [TopologicalSpace H''] {I'' : ModelWithCorners ℝ E'' H''} {P : Type*} [TopologicalSpace P]
  [ChartedSpace H'' P] [IsManifold I'' 1 P]

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
@[simp]
theorem isOrientationPreservingAt_map_symm (o : Orientation I M ι) (e : M ≃ₘ^n⟮I, I'⟯ N)
    (hn : n ≠ 0) (hι : Fintype.card ι = finrank ℝ E') (y : N) :
    IsOrientationPreservingAt (o.map e hn hι) o e.symm y := by
  rw [map_def]
  exact isOrientationPreservingAt_pullback _ _ _ _ y

/-- The diffeomorphism `e` preserves orientation at every point, from `o` to the carried
orientation. -/
@[simp]
theorem isOrientationPreservingAt_map (o : Orientation I M ι) (e : M ≃ₘ^n⟮I, I'⟯ N) (hn : n ≠ 0)
    (hι : Fintype.card ι = finrank ℝ E') (x : M) :
    IsOrientationPreservingAt o (o.map e hn hι) e x := by
  simpa only [Diffeomorph.symm_symm] using
    (isOrientationPreservingAt_map_symm o e hn hι (e.symm.symm x)).diffeomorph_symm hn

/-- The carried orientation is the only orientation of `N` from which the inverse of `e`
preserves orientation at every point. -/
theorem eq_map_iff {o : Orientation I M ι} {o' : Orientation I' N ι} {e : M ≃ₘ^n⟮I, I'⟯ N}
    (hn : n ≠ 0) (hι : Fintype.card ι = finrank ℝ E') :
    o' = o.map e hn hι ↔ ∀ y, IsOrientationPreservingAt o' o e.symm y := by
  rw [map_def, eq_pullback_iff]

/-- The carried orientation is the only orientation of `N` to which `e` preserves orientation at
every point. -/
theorem eq_map_iff' {o : Orientation I M ι} {o' : Orientation I' N ι} {e : M ≃ₘ^n⟮I, I'⟯ N}
    (hn : n ≠ 0) (hι : Fintype.card ι = finrank ℝ E') :
    o' = o.map e hn hι ↔ ∀ x, IsOrientationPreservingAt o o' e x :=
  ⟨fun h ↦ h ▸ isOrientationPreservingAt_map o e hn hι,
    fun h ↦ (eq_map_iff hn hι).2 fun y ↦ (h (e.symm y)).diffeomorph_symm hn⟩

/-- Carrying the opposite orientation gives the opposite of the carried orientation. -/
@[simp]
theorem map_neg (o : Orientation I M ι) (e : M ≃ₘ^n⟮I, I'⟯ N) (hn : n ≠ 0)
    (hι : Fintype.card ι = finrank ℝ E') : (-o).map e hn hι = -o.map e hn hι := by
  simp only [map_def, pullback_neg]

/-- Carrying an orientation along the identity gives it back. -/
@[simp]
theorem map_refl (o : Orientation I M ι) (hn : n ≠ 0) :
    o.map (Diffeomorph.refl I M n) hn o.card_eq = o := by
  refine ((eq_map_iff' hn o.card_eq).2 fun x ↦ ?_).symm
  rw [Diffeomorph.coe_refl]
  exact isOrientationPreservingAt_id o x

/-- Carrying an orientation along a composite of diffeomorphisms is carrying it along each in
turn. -/
theorem map_trans (o : Orientation I M ι) (e : M ≃ₘ^n⟮I, I'⟯ N) (f : N ≃ₘ^n⟮I', I''⟯ P)
    (hn : n ≠ 0) (hι : Fintype.card ι = finrank ℝ E') (hι' : Fintype.card ι = finrank ℝ E'') :
    o.map (e.trans f) hn hι' = (o.map e hn hι).map f hn hι' := by
  refine ((eq_map_iff' hn hι').2 fun x ↦ ?_).symm
  rw [Diffeomorph.coe_trans]
  exact (isOrientationPreservingAt_map _ f hn hι' (e x)).comp
    (isOrientationPreservingAt_map o e hn hι x)

/-- Carrying an orientation along `e` and then back along `e.symm` gives it back. -/
@[simp]
theorem map_symm_map (o : Orientation I M ι) (e : M ≃ₘ^n⟮I, I'⟯ N) (hn : n ≠ 0)
    (hι : Fintype.card ι = finrank ℝ E') : (o.map e hn hι).map e.symm hn o.card_eq = o :=
  ((eq_map_iff' hn o.card_eq).2 (isOrientationPreservingAt_map_symm o e hn hι)).symm

/-- Carrying an orientation of `N` along `e.symm` and then back along `e` gives it back. -/
@[simp]
theorem map_map_symm (o : Orientation I' N ι) (e : M ≃ₘ^n⟮I, I'⟯ N) (hn : n ≠ 0)
    (hι : Fintype.card ι = finrank ℝ E) : (o.map e.symm hn hι).map e hn o.card_eq = o :=
  ((eq_map_iff hn o.card_eq).2 (isOrientationPreservingAt_map o e.symm hn hι)).symm

end TauCeti.Manifold.Orientation

end
