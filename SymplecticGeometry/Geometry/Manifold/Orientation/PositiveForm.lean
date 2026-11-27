/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.Preserving
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Basic
public import TauCeti.Geometry.Manifold.Orientation.TopForm
public import Mathlib.Analysis.Convex.Basic
import TauCeti.LinearAlgebra.Orientation.Basis
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.Smooth

/-!
# Top forms positive for an orientation

A top form `φ` on a manifold of positive dimension `k` with an orientation `o` is *positive for
`o` at `x`* (`TauCeti.Manifold.Orientation.IsPositiveAt`) when it takes a positive value on every
basis of the tangent space at `x` whose orientation is that of `o` there, and *positive for `o`*
(`TauCeti.Manifold.Orientation.IsPositive`) when it is so at every point.

The definitions ask for `NeZero k`. In dimension zero the only basis is the empty one, whose
orientation is always the positive one, so at a point where `o` is the negative orientation the
condition above would hold for every form, `0` included.

A positive top form vanishes nowhere (`IsPositiveAt.ne_zero`), and a nowhere-vanishing top form
is positive for the orientation it defines (`isPositive_ofTopForm`). The orientation for which a
top form is positive is unique (`IsPositiveAt.orientationAt_eq`, `IsPositive.eq`), since a form
positive for `o` at `x` is positive exactly on the bases with the orientation of `o` there
(`IsPositiveAt.apply_pos_iff`). If `φ` is positive for `o`, then `-φ` is positive for `-o`
(`IsPositiveAt.neg`).

Positivity is kept by positive multiples, sums, and combinations with nonnegative weights of
which one is positive. So the top forms positive for `o` at `x` form a convex set
(`convex_setOfPred_isPositiveAt`), and the segment `φ + s (ψ - φ)`, `s ∈ [0, 1]`, between two of
them stays positive (`IsPositiveAt.add_smul_sub`).

Positivity is carried back along maps that preserve orientation: if `f` preserves the
orientations `o` and `o'` at `x`, and `φ` is positive for `o'` at `f x`, then `f^* φ` is positive
for `o` at `x`, since the derivative of `f` at `x` carries a positively oriented basis to
one. Conversely, when the derivative of `f` at `x` is invertible and `φ` is positive for `o'` at
`f x`, a pull-back `f^* φ` that is positive on one basis with the orientation of `o` shows that
`f` preserves the orientations at `x`: the derivative carries that basis to one on which `φ` is
positive, and a top form positive on two bases gives them the same orientation.

## Main definitions

* `TauCeti.Manifold.Orientation.IsPositiveAt o φ x`: the top form `φ` is positive for `o` at `x`.
* `TauCeti.Manifold.Orientation.IsPositive o φ`: the top form `φ` is positive for `o` everywhere.

## Main results

* `TauCeti.Manifold.Orientation.IsPositiveAt.sum_smul`: a combination of positive top forms with
  nonnegative weights, one of them positive, is positive.
* `TauCeti.Manifold.Orientation.convex_setOfPred_isPositiveAt`: the top forms positive for `o` at
  `x` form a convex set.
* `TauCeti.Manifold.Orientation.IsOrientationPreservingAt.isPositiveAt_mpullback`: pull-backs
  along orientation-preserving maps keep top forms positive.
* `TauCeti.Manifold.Orientation.isOrientationPreservingAt_iff_isPositiveAt_mpullback`: a map with
  invertible derivative preserves the orientations exactly when it pulls a positive top form back
  to a positive one.
* `Diffeomorph.mem_orientationPreservingSubgroup_iff_isPositive_mpullback`: a diffeomorphism
  preserves an orientation exactly when it pulls a positive top form back to a positive one.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 15.
-/

public section

open scoped Manifold

namespace TauCeti.Manifold.Orientation

variable {E H M E' H' M' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M'] [ChartedSpace H' M'] {k : ℕ}

section Positive

variable [FiniteDimensional ℝ E] [IsManifold I 1 M] (o : Manifold.Orientation I M (Fin k))

/-- The top form `φ`, of positive degree `k`, is *positive for the orientation `o` at `x`*: it
takes a positive value on every basis of the tangent space at `x` with the orientation of `o`
there. -/
def IsPositiveAt [NeZero k] (φ : RoughForm I M ℝ k) (x : M) : Prop :=
  ∀ c : Module.Basis (Fin k) ℝ (TangentSpace I x), c.orientation = o.orientationAt x → 0 < φ x c

/-- The top form `φ`, of positive degree `k`, is *positive for the orientation `o`*: it is
positive for `o` at every point. -/
def IsPositive [NeZero k] (φ : RoughForm I M ℝ k) : Prop :=
  ∀ x, IsPositiveAt o φ x

variable [NeZero k] {o} {φ ψ : RoughForm I M ℝ k} {x : M}

theorem isPositiveAt_iff : IsPositiveAt o φ x ↔
    ∀ c : Module.Basis (Fin k) ℝ (TangentSpace I x),
      c.orientation = o.orientationAt x → 0 < φ x c := Iff.rfl

theorem isPositive_iff : IsPositive o φ ↔ ∀ x, IsPositiveAt o φ x := Iff.rfl

theorem isPositive_iff_forall_apply_pos : IsPositive o φ ↔
    ∀ x (c : Module.Basis (Fin k) ℝ (TangentSpace I x)),
      c.orientation = o.orientationAt x → 0 < φ x c := Iff.rfl

theorem IsPositiveAt.apply_pos (h : IsPositiveAt o φ x)
    {c : Module.Basis (Fin k) ℝ (TangentSpace I x)} (hc : c.orientation = o.orientationAt x) :
    0 < φ x c :=
  h c hc

theorem IsPositive.isPositiveAt (h : IsPositive o φ) (x : M) : IsPositiveAt o φ x :=
  h x

theorem IsPositive.apply_pos (h : IsPositive o φ) {x : M}
    {c : Module.Basis (Fin k) ℝ (TangentSpace I x)} (hc : c.orientation = o.orientationAt x) :
    0 < φ x c :=
  h x c hc

/-- A top form positive for `o` at `x` does not vanish at `x`. -/
theorem IsPositiveAt.ne_zero (h : IsPositiveAt o φ x) : φ x ≠ 0 := fun h0 ↦ by
  classical
  have hc := h.apply_pos ((o.orientationAt x).someBasis_orientation
    (o.finrank_tangentSpace_eq x).symm)
  simp [h0] at hc

/-- A top form positive for `o` vanishes nowhere. -/
theorem IsPositive.ne_zero (h : IsPositive o φ) (x : M) : φ x ≠ 0 :=
  (h x).ne_zero

/-- A nowhere-vanishing continuous top form is positive for the orientation it defines. -/
theorem isPositive_ofTopForm (hk : Module.finrank ℝ E = k) (hφ : IsSmoothForm I 0 φ)
    (h0 : ∀ x, φ x ≠ 0) : IsPositive (ofTopForm hk φ hφ h0) φ := fun _ c hc ↦
  (orientation_eq_orientationAt_ofTopForm_iff hk hφ h0 c).1 hc

theorem IsPositiveAt.smul (h : IsPositiveAt o φ x) {a : ℝ} (ha : 0 < a) :
    IsPositiveAt o (a • φ) x := fun c hc ↦ by
  simpa using mul_pos ha (h c hc)

theorem IsPositive.smul (h : IsPositive o φ) {a : ℝ} (ha : 0 < a) : IsPositive o (a • φ) :=
  fun x ↦ (h x).smul ha

theorem IsPositiveAt.add (hφ : IsPositiveAt o φ x) (hψ : IsPositiveAt o ψ x) :
    IsPositiveAt o (φ + ψ) x := fun c hc ↦ by
  simpa using add_pos (hφ c hc) (hψ c hc)

theorem IsPositive.add (hφ : IsPositive o φ) (hψ : IsPositive o ψ) : IsPositive o (φ + ψ) :=
  fun x ↦ (hφ x).add (hψ x)

/-- A combination of top forms positive for `o` at `x`, with nonnegative weights of which one is
positive, is positive for `o` at `x`. -/
theorem IsPositiveAt.sum_smul {ι : Type*} {s : Finset ι} {w : ι → ℝ} {φ : ι → RoughForm I M ℝ k}
    (hφ : ∀ i ∈ s, IsPositiveAt o (φ i) x) (hw : ∀ i ∈ s, 0 ≤ w i) (hw' : ∃ i ∈ s, 0 < w i) :
    IsPositiveAt o (∑ i ∈ s, w i • φ i) x := fun c hc ↦ by
  rw [Finset.sum_apply, ContinuousAlternatingMap.sum_apply]
  simp only [Pi.smul_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  obtain ⟨j, hj, hwj⟩ := hw'
  exact Finset.sum_pos' (fun i hi ↦ mul_nonneg (hw i hi) (hφ i hi c hc).le)
    ⟨j, hj, mul_pos hwj (hφ j hj c hc)⟩

/-- A combination of top forms positive for `o`, with nonnegative weights of which one is
positive, is positive for `o`. -/
theorem IsPositive.sum_smul {ι : Type*} {s : Finset ι} {w : ι → ℝ} {φ : ι → RoughForm I M ℝ k}
    (hφ : ∀ i ∈ s, IsPositive o (φ i)) (hw : ∀ i ∈ s, 0 ≤ w i) (hw' : ∃ i ∈ s, 0 < w i) :
    IsPositive o (∑ i ∈ s, w i • φ i) :=
  fun x ↦ IsPositiveAt.sum_smul (fun i hi ↦ hφ i hi x) hw hw'

/-- If `φ` is positive for `o` at `x`, then `-φ` is positive for the opposite orientation `-o`
at `x`. -/
theorem IsPositiveAt.neg (h : IsPositiveAt o φ x) : IsPositiveAt (-o) (-φ) x := fun c hc ↦ by
  classical
  -- Compare `c` with a basis `d` that is positive for `o`, on which `φ` is positive.
  set d := (o.orientationAt x).someBasis (o.finrank_tangentSpace_eq x).symm
  have hd : d.orientation = o.orientationAt x :=
    (o.orientationAt x).someBasis_orientation (o.finrank_tangentSpace_eq x).symm
  rw [Manifold.Orientation.orientationAt_neg, ← hd] at hc
  -- `c` has the orientation opposite to `d`.
  have key : -φ x c = |d.det c| * φ x d := by
    simpa [Orientation.signBasis_eq_neg_of_orientation_eq_neg _ d c hc] using
      (φ x).toAlternatingMap.signBasis_mul_apply_eq_abs_det_mul d c
  rw [Pi.neg_apply, ContinuousAlternatingMap.neg_apply, key]
  exact mul_pos (abs_pos.2 (d.isUnit_det c).ne_zero) (h.apply_pos hd)

/-- If `φ` is positive for `o` at `x`, then `φ` is positive on a basis `c` of the tangent space
at `x` exactly when `c` has the orientation of `o` there. -/
theorem IsPositiveAt.apply_pos_iff (h : IsPositiveAt o φ x)
    (c : Module.Basis (Fin k) ℝ (TangentSpace I x)) :
    0 < φ x c ↔ c.orientation = o.orientationAt x := by
  refine ⟨fun hc ↦ ?_, h.apply_pos⟩
  rcases c.orientation_eq_or_eq_neg (o.orientationAt x) with hc' | hc'
  · exact hc'.symm
  · -- Otherwise `c` is positive for `-o`, on which `-φ` is positive, so `φ` is negative on `c`.
    have hneg := h.neg.apply_pos (c := c)
      (by rw [Manifold.Orientation.orientationAt_neg, hc']; exact (neg_neg c.orientation).symm)
    rw [Pi.neg_apply, ContinuousAlternatingMap.neg_apply] at hneg
    linarith

/-- An orientation on which a top form is positive at `x` is unique there: if `φ` is positive
for both `o` and `o'` at `x`, then `o` and `o'` agree at `x`. -/
theorem IsPositiveAt.orientationAt_eq {o' : Manifold.Orientation I M (Fin k)}
    (h : IsPositiveAt o φ x) (h' : IsPositiveAt o' φ x) :
    o.orientationAt x = o'.orientationAt x := by
  classical
  have hd := (o.orientationAt x).someBasis_orientation (o.finrank_tangentSpace_eq x).symm
  exact hd.symm.trans ((h'.apply_pos_iff _).1 (h.apply_pos hd))

/-- An orientation on which a top form is positive is unique: if `φ` is positive for both `o`
and `o'`, then `o = o'`. -/
theorem IsPositive.eq {o' : Manifold.Orientation I M (Fin k)} (h : IsPositive o φ)
    (h' : IsPositive o' φ) : o = o' :=
  Manifold.Orientation.ext fun x ↦ (h x).orientationAt_eq (h' x)

/-- If `φ` is positive for `o`, then `-φ` is positive for the opposite orientation `-o`. -/
theorem IsPositive.neg (h : IsPositive o φ) : IsPositive (-o) (-φ) :=
  fun x ↦ (h x).neg

variable (o x) in
/-- The top forms positive for `o` at `x` form a convex set. -/
theorem convex_setOfPred_isPositiveAt : Convex ℝ {φ : RoughForm I M ℝ k | IsPositiveAt o φ x} :=
  convex_iff_forall_pos.2 fun _ hφ _ hψ _ _ ha hb _ ↦ (hφ.smul ha).add (hψ.smul hb)

/-- The segment `φ + s (ψ - φ)`, `s ∈ [0, 1]`, between two top forms positive for `o` at `x` stays
positive for `o` at `x`. -/
theorem IsPositiveAt.add_smul_sub (hφ : IsPositiveAt o φ x) (hψ : IsPositiveAt o ψ x) {s : ℝ}
    (hs : s ∈ Set.Icc 0 1) : IsPositiveAt o (φ + s • (ψ - φ)) x :=
  (convex_setOfPred_isPositiveAt o x).add_smul_sub_mem hφ hψ hs

/-- The segment `φ + s (ψ - φ)`, `s ∈ [0, 1]`, between two top forms positive for `o` stays
positive for `o`. -/
theorem IsPositive.add_smul_sub (hφ : IsPositive o φ) (hψ : IsPositive o ψ) {s : ℝ}
    (hs : s ∈ Set.Icc 0 1) : IsPositive o (φ + s • (ψ - φ)) :=
  fun x ↦ (hφ x).add_smul_sub (hψ x) hs

end Positive

variable [FiniteDimensional ℝ E] [IsManifold I 1 M] [FiniteDimensional ℝ E'] [IsManifold I' 1 M']
  [NeZero k]
  {o : Manifold.Orientation I M (Fin k)} {o' : Manifold.Orientation I' M' (Fin k)} {f : M → M'}

/-- **Pull-backs of positive top forms.** If `f` preserves the orientations `o` and `o'` at `x`
and the top form `φ` is positive for `o'` at `f x`, then its pull-back `f^* φ` is positive for `o`
at `x`. -/
theorem IsOrientationPreservingAt.isPositiveAt_mpullback {x : M}
    (hf : IsOrientationPreservingAt o o' f x) {φ : RoughForm I' M' ℝ k}
    (hφ : IsPositiveAt o' φ (f x)) : IsPositiveAt o (mpullback I I' f φ) x := fun c hc ↦ by
  obtain ⟨e, he, hmap⟩ := (isOrientationPreservingAt_iff _ _ _ _).1 hf
  -- The derivative carries `c` to the basis `c.map e`, which has the orientation of `o'`.
  rw [mpullback_apply_basis_map he]
  exact hφ (c.map e.toLinearEquiv) (by rw [Module.Basis.orientation_map, hc, hmap])

/-- **Pull-backs of positive top forms.** If `f` preserves the orientations `o` and `o'` at every
point and the top form `φ` is positive for `o'`, then its pull-back `f^* φ` is positive for
`o`. -/
theorem IsPositive.mpullback (hf : ∀ x, IsOrientationPreservingAt o o' f x)
    {φ : RoughForm I' M' ℝ k} (hφ : IsPositive o' φ) : IsPositive o (mpullback I I' f φ) :=
  fun x ↦ (hf x).isPositiveAt_mpullback (hφ (f x))

/-- **Orientation from a positive pull-back.** Let `f` have an invertible derivative at `x`, and
let the top form `φ` be positive for `o'` at `f x`. If the pull-back `f^* φ` takes a positive value
on one basis of the tangent space at `x` with the orientation of `o`, then `f` preserves the
orientations `o` and `o'` at `x`. -/
theorem isOrientationPreservingAt_of_mpullback_apply_pos {x : M}
    (hf : (mfderiv I I' f x).IsInvertible) {φ : RoughForm I' M' ℝ k}
    (hφ : IsPositiveAt o' φ (f x)) {c : Module.Basis (Fin k) ℝ (TangentSpace I x)}
    (hc : c.orientation = o.orientationAt x) (h : 0 < mpullback I I' f φ x c) :
    IsOrientationPreservingAt o o' f x := by
  obtain ⟨e, he⟩ := hf
  rw [isOrientationPreservingAt_iff_of_coe_eq o o' f x e he, ← hc,
    ← Module.Basis.orientation_map]
  -- The derivative carries `c` to a basis on which `φ` is positive, so that basis has the
  -- orientation of `o'` at `f x`.
  exact (hφ.apply_pos_iff _).1 (by rwa [← mpullback_apply_basis_map he])

/-- **Orientation from a positive pull-back.** For a map `f` with an invertible derivative at `x`
and a top form `φ` positive for `o'` at `f x`, `f` preserves the orientations `o` and `o'` at `x`
exactly when the pull-back `f^* φ` is positive for `o` at `x`. -/
theorem isOrientationPreservingAt_iff_isPositiveAt_mpullback {x : M}
    (hf : (mfderiv I I' f x).IsInvertible) {φ : RoughForm I' M' ℝ k}
    (hφ : IsPositiveAt o' φ (f x)) :
    IsOrientationPreservingAt o o' f x ↔ IsPositiveAt o (mpullback I I' f φ) x := by
  classical
  refine ⟨fun h ↦ h.isPositiveAt_mpullback hφ, fun h ↦ ?_⟩
  have hc := (o.orientationAt x).someBasis_orientation (o.finrank_tangentSpace_eq x).symm
  exact isOrientationPreservingAt_of_mpullback_apply_pos hf hφ hc (h.apply_pos hc)

section Diffeomorph

open scoped ContDiff

variable {n : ℕ∞ω}

/-- **Orientation-preserving diffeomorphisms from a positive pull-back.** Let `φ` be a top form
positive for the orientation `o`. A `Cⁿ` diffeomorphism `f` of `M`, for `n ≠ 0`, preserves `o`
exactly when the pull-back `f^* φ` is positive for `o`. -/
theorem _root_.Diffeomorph.mem_orientationPreservingSubgroup_iff_isPositive_mpullback {hn : n ≠ 0}
    {o : TauCeti.Manifold.Orientation I M (Fin k)} {φ : RoughForm I M ℝ k} (hφ : IsPositive o φ)
    {f : TauCeti.Diff I M n} :
    f ∈ Diffeomorph.orientationPreservingSubgroup hn o ↔ IsPositive o (mpullback I I f φ) := by
  rw [Diffeomorph.mem_orientationPreservingSubgroup_iff]
  exact forall_congr' fun x ↦
    isOrientationPreservingAt_iff_isPositiveAt_mpullback (f.isInvertible_mfderiv hn) (hφ (f x))

end Diffeomorph

end TauCeti.Manifold.Orientation

end
