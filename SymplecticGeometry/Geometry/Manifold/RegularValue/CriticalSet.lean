/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
public import TauCeti.Geometry.Manifold.RegularValue
import TauCeti.Geometry.Manifold.RegularValue.Open

/-!
# The critical set of a map between manifolds

The critical set `criticalSet I I' f` of a map `f : M → N` between manifolds over a nontrivially
normed field is the set of points at which `f` is not a regular point in the sense of Tau Ceti's
`TauCeti.IsRegularPoint`, that is, at which the manifold derivative of `f` is not surjective.
Tau Ceti's own `criticalPoints` is the corresponding notion for real-valued functions only, and
`SymplecticGeometry.criticalSet_eq_criticalPoints` identifies the two for maps into `ℝ`.

## Main results

* `SymplecticGeometry.mem_criticalSet_iff` and `SymplecticGeometry.compl_criticalSet`: the
  critical set is the complement of the regular points.
* `SymplecticGeometry.isClosed_criticalSet`: the critical set of a `C¹` map into a
  finite-dimensional manifold is closed, by Tau Ceti's `TauCeti.isOpen_setOf_isRegularPoint`.
* `SymplecticGeometry.criticalSet_eq_criticalPoints`: for a real-valued function the critical
  set is Tau Ceti's `TauCeti.criticalPoints`, by
  `TauCeti.isRegularPoint_iff_notMem_criticalPoints`.
-/

public section

open TauCeti
open scoped Manifold

namespace SymplecticGeometry

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] (I' : ModelWithCorners 𝕜 E' H')
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]

/-- The critical set of a map `f : M → N` between manifolds: the points at which the manifold
derivative of `f` is not surjective, the complement of the regular points of Tau Ceti's
`IsRegularPoint`. -/
def criticalSet (f : M → N) : Set M :=
  {x | ¬ IsRegularPoint I I' f x}

theorem criticalSet_def (f : M → N) : criticalSet I I' f = {x | ¬ IsRegularPoint I I' f x} :=
  (rfl)

variable {I I'}

@[simp]
theorem mem_criticalSet_iff {f : M → N} {x : M} :
    x ∈ criticalSet I I' f ↔ ¬ IsRegularPoint I I' f x := by
  rw [criticalSet_def, Set.mem_ofPred_eq]

/-- The complement of the critical set is the set of regular points. -/
theorem compl_criticalSet (f : M → N) :
    (criticalSet I I' f)ᶜ = {x | IsRegularPoint I I' f x} := by
  ext x
  simp

/-- The critical set of a `C¹` map into a finite-dimensional manifold is closed. -/
theorem isClosed_criticalSet [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E'] [IsManifold I 1 M]
    [IsManifold I' 1 N] {f : M → N} {n : WithTop ℕ∞} (hf : ContMDiff I I' n f) (hn : 1 ≤ n) :
    IsClosed (criticalSet I I' f) := by
  rw [← isOpen_compl_iff, compl_criticalSet]
  exact isOpen_setOf_isRegularPoint hf hn

/-- For a real-valued function, the critical set is Tau Ceti's `criticalPoints`, the set of points
where the manifold derivative vanishes. -/
theorem criticalSet_eq_criticalPoints {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] (f : M → ℝ) :
    criticalSet I 𝓘(ℝ) f = criticalPoints I f := by
  ext x
  rw [mem_criticalSet_iff, isRegularPoint_iff_notMem_criticalPoints, not_not]

end SymplecticGeometry

end
