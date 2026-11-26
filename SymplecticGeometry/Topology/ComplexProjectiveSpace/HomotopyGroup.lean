/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Topology.ComplexProjectiveSpace.Homeomorph
public import TauCeti.AlgebraicTopology.Sphere.PointedMap
public import TauCeti.Analysis.Normed.Module.Ball.Homeomorph
public import TauCeti.Topology.ComplexProjectiveSpace.Hopf.Exact
public import TauCeti.Topology.Homotopy.HomotopyGroup.LoopSpace

/-!
# Maps from spheres of dimension `3` to `2n` into complex projective space

Tau Ceti shows that the homotopy groups `πₖ(ℂPⁿ)` vanish for `3 ≤ k ≤ 2n`, with `πₖ` modelled on
the cube `I^(Option N)` for an index type `N` with at least two and fewer than `2n` elements
(`TauCeti.ComplexProjectiveSpace.subsingleton_homotopyGroup`). This file deduces that every map
from a `k`-sphere to the projectivization `ℙ ℂ V` of a complex vector space of dimension `n + 1`
is null-homotopic in that range, along `Projectivization.complexProjectiveSpaceHomeomorph`. The
sphere is the unit sphere of any real normed space of dimension `k + 1`, such as the spheres of
the characteristic maps of a CW complex, which are taken with the sup norm.

## Main results

* `Projectivization.nullhomotopic_of_three_le_of_le`: every map from the unit sphere of a real
  normed space of dimension `k + 1` to `ℙ ℂ V` is null-homotopic when `3 ≤ k ≤ 2n`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 4.2 (the long exact
  sequence of the Hopf fibration `S¹ → S²ⁿ⁺¹ → ℂPⁿ`).
-/

public section

open Metric Module TauCeti
open scoped LinearAlgebra.Projectivization

namespace Projectivization

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousSMul ℂ V] [T2Space V] {n : ℕ}

/-- **Maps from spheres of dimension `3` to `2n` into `ℂPⁿ` are null-homotopic.** Let `V` be a
complex vector space of dimension `n + 1` and `E` a real normed space of dimension `k + 1`, with
`3 ≤ k ≤ 2n`. Every continuous map from the unit sphere of `E` to `ℙ ℂ V` is null-homotopic. -/
theorem nullhomotopic_of_three_le_of_le (hV : finrank ℂ V = n + 1) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ} (hE : finrank ℝ E = k + 1) (hk : 3 ≤ k)
    (hkn : k ≤ 2 * n) (g : C(sphere (0 : E) 1, ℙ ℂ V)) : g.Nullhomotopic := by
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_eq_succ hE
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  let e : sphere (0 : EuclideanSpace ℝ (Fin (j + 1 + 1))) 1 ≃ₜ sphere (0 : E) 1 :=
    sphereHomeomorphOfFinrankEq (by rw [finrank_euclideanSpace_fin, hE])
  let c := complexProjectiveSpaceHomeomorph hV
  let g' : C(sphere (0 : EuclideanSpace ℝ (Fin (j + 1 + 1))) 1, ComplexProjectiveSpace n) :=
    (c.symm : C(ℙ ℂ V, ComplexProjectiveSpace n)).comp (g.comp e)
  have hg' : g'.Nullhomotopic := by
    refine ContinuousMap.nullhomotopic_of_subsingleton_homotopyGroup g' ?_
    obtain ⟨v, hv⟩ := ComplexProjectiveSpace.mk_surjective n (g' (sphereNorthPole (j + 1)))
    have : Nontrivial (Fin j) := Fin.nontrivial_iff_two_le.2 (by omega)
    have := ComplexProjectiveSpace.subsingleton_homotopyGroup (N := Fin j) v (by simp; omega)
    rw [← hv]
    exact (HomotopyGroup.congrEquiv (finSuccEquiv j)).subsingleton
  have h := (hg'.comp_right (c : C(ComplexProjectiveSpace n, ℙ ℂ V))).comp_left
    (e.symm : C(sphere (0 : E) 1, sphere (0 : EuclideanSpace ℝ (Fin (j + 1 + 1))) 1))
  convert h using 1
  ext y
  simp [g']

end Projectivization

end
