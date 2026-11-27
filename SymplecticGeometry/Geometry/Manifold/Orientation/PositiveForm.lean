/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.Preserving
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Basic

/-!
# Top forms positive for an orientation

A top form `φ` on a manifold with an orientation `o` is *positive for `o` at `x`*
(`TauCeti.Manifold.Orientation.IsPositiveAt`) when it takes a positive value on every basis of
the tangent space at `x` whose orientation is that of `o` there, and *positive for `o`*
(`TauCeti.Manifold.Orientation.IsPositive`) when it is so at every point.

Positivity is kept by positive multiples, sums, and combinations with nonnegative weights of
which one is positive. It is carried back along maps that preserve orientation: if `f` preserves
the orientations `o` and `o'` at `x`, and `φ` is positive for `o'` at `f x`, then `f^* φ` is
positive for `o` at `x`, since the derivative of `f` at `x` carries a positively oriented basis to
one.

## Main definitions

* `TauCeti.Manifold.Orientation.IsPositiveAt o φ x`: the top form `φ` is positive for `o` at `x`.
* `TauCeti.Manifold.Orientation.IsPositive o φ`: the top form `φ` is positive for `o` everywhere.

## Main results

* `TauCeti.Manifold.Orientation.IsPositiveAt.sum_smul`: a combination of positive top forms with
  nonnegative weights, one of them positive, is positive.
* `TauCeti.Manifold.Orientation.IsOrientationPreservingAt.isPositiveAt_mpullback`: pull-backs
  along orientation-preserving maps keep top forms positive.

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

/-- The top form `φ` is *positive for the orientation `o` at `x`*: it takes a positive value on
every basis of the tangent space at `x` with the orientation of `o` there. -/
def IsPositiveAt (φ : RoughForm I M ℝ k) (x : M) : Prop :=
  ∀ c : Module.Basis (Fin k) ℝ (TangentSpace I x), c.orientation = o.orientationAt x → 0 < φ x c

/-- The top form `φ` is *positive for the orientation `o`*: it is positive for `o` at every
point. -/
def IsPositive (φ : RoughForm I M ℝ k) : Prop :=
  ∀ x, IsPositiveAt o φ x

variable {o} {φ ψ : RoughForm I M ℝ k} {x : M}

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

end Positive

variable [FiniteDimensional ℝ E] [IsManifold I 1 M] [FiniteDimensional ℝ E'] [IsManifold I' 1 M']
  {o : Manifold.Orientation I M (Fin k)} {o' : Manifold.Orientation I' M' (Fin k)} {f : M → M'}

/-- **Pull-backs of positive top forms.** If `f` preserves the orientations `o` and `o'` at `x`
and the top form `φ` is positive for `o'` at `f x`, then its pull-back `f^* φ` is positive for `o`
at `x`. -/
theorem IsOrientationPreservingAt.isPositiveAt_mpullback {x : M}
    (hf : IsOrientationPreservingAt o o' f x) {φ : RoughForm I' M' ℝ k}
    (hφ : IsPositiveAt o' φ (f x)) : IsPositiveAt o (mpullback I I' f φ) x := fun c hc ↦ by
  obtain ⟨e, he, hmap⟩ := (isOrientationPreservingAt_iff _ _ _ _).1 hf
  -- The derivative carries `c` to the basis `c.map e`, which has the orientation of `o'`.
  have h := hφ (c.map e.toLinearEquiv) (by rw [Module.Basis.orientation_map, hc, hmap])
  rw [mpullback_apply]
  convert h using 2
  funext i
  simp [← he]

/-- **Pull-backs of positive top forms.** If `f` preserves the orientations `o` and `o'` at every
point and the top form `φ` is positive for `o'`, then its pull-back `f^* φ` is positive for
`o`. -/
theorem IsPositive.mpullback (hf : ∀ x, IsOrientationPreservingAt o o' f x)
    {φ : RoughForm I' M' ℝ k} (hφ : IsPositive o' φ) : IsPositive o (mpullback I I' f φ) :=
  fun x ↦ (hf x).isPositiveAt_mpullback (hφ (f x))

end TauCeti.Manifold.Orientation

end
