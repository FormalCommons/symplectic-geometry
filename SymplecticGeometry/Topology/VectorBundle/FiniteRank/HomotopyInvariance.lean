/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Homotopy.Affine
public import Mathlib.Topology.Homotopy.Product
public import TauCeti.Topology.VectorBundle.FiniteRank.HomotopyInvariance

/-!
# A finite-rank core over a product with a normed space

For a real normed space `E`, a point-indexed finite-rank core over `Y × E` is the pullback along
the projection of its restriction to `Y × {c}`
(`TauCeti.FiniteRankBundleCore.nonempty_iso_pullback_fst`). The segments to `c` contract `E`, so
the identity of `Y × E` is homotopic to `(y, e) ↦ (y, c)`, and Tau Ceti's homotopy invariance of
pullbacks of cores, `TauCeti.FiniteRankBundleCore.nonempty_pullback_iso_pullback_of_homotopic`,
applies.

## References

* [A. Hatcher, *Vector Bundles and K-Theory*][Hatcher2017], §1.2, Theorem 1.6.
-/

public section

namespace TauCeti.FiniteRankBundleCore

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜] [CompleteSpace 𝕜]
  {Y : Type*} [TopologicalSpace Y]

/-- **A core over a product with a real normed space is pulled back from the base.** For a real
normed space `E` with `Y × E` paracompact and R₁, a finite-rank core `A` over `Y × E` is isomorphic
to the pullback along the projection `Y × E → Y` of its restriction to `Y × {c}`, for any
`c : E`. The segments to `c` contract `E`. -/
theorem nonempty_iso_pullback_fst {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ParacompactSpace (Y × E)] [R1Space (Y × E)] (A : FiniteRankBundleCore 𝕜 (Y × E)) (c : E) :
    Nonempty (A ≅ (A.pullback ((ContinuousMap.id Y).prodMk (.const Y c))).pullback
      ContinuousMap.fst) := by
  have h : (ContinuousMap.id (Y × E)).Homotopic
      (((ContinuousMap.id Y).prodMk (.const Y c)).comp ContinuousMap.fst) :=
    ⟨(ContinuousMap.Homotopy.refl ContinuousMap.fst).prod (.affine ContinuousMap.snd (.const _ c))⟩
  obtain ⟨e⟩ := A.nonempty_pullback_iso_pullback_of_homotopic h
  rw [pullback_id, ← pullback_comp] at e
  exact ⟨e⟩

end TauCeti.FiniteRankBundleCore

end
