/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.RegularValue
public import TauCeti.Geometry.Manifold.Submersion.Basic

/-!
# Regular values of submersions

The manifold derivative of a `C^n` submersion, `n ≠ 0`, is surjective at every point
(`Manifold.IsSubmersionAt.surjective_mfderiv`). So every point is a regular point of a
submersion (`Manifold.IsSubmersionAt.isRegularPoint`), and every point of the target, in the
range or not, is a regular value (`Manifold.IsSubmersion.isRegularValue`).

These are the counterparts for submersions of Tau Ceti's `IsLocalDiffeomorphAt.isRegularPoint`
and `IsLocalDiffeomorph.isRegularValue`, which they follow.

## Main results

* `Manifold.IsSubmersionAt.isRegularPoint`: a submersion at `x` has `x` as a regular point.
* `Manifold.IsSubmersion.isRegularValue`: every value of a submersion is a regular value.
-/

public section

open TauCeti

namespace Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type*} [TopologicalSpace G]
  {J : ModelWithCorners 𝕜 F G} {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {n : WithTop ℕ∞} {f : M → N} {x : M}

/-- A `C^n` submersion at `x`, with `n ≠ 0`, has `x` as a regular point. -/
theorem IsSubmersionAt.isRegularPoint (h : IsSubmersionAt I J n f x) (hn : n ≠ 0) :
    IsRegularPoint I J f x :=
  isRegularPoint_iff.2 (h.surjective_mfderiv hn)

/-- Every point of the target of a `C^n` submersion, with `n ≠ 0`, is a regular value of it. -/
theorem IsSubmersion.isRegularValue (hf : IsSubmersion I J n f) (hn : n ≠ 0) (y : N) :
    IsRegularValue I J f y :=
  isRegularValue_iff.2 fun x _ ↦ (hf.isSubmersionAt x).isRegularPoint hn

end Manifold

end
