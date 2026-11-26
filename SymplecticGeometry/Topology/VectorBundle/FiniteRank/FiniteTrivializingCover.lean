/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Topology.VectorBundle.FiniteTrivializingCover
public import TauCeti.Topology.VectorBundle.FiniteRank.Basic
import SymplecticGeometry.Topology.VectorBundle.FiniteRank.Basic

/-!
# Finite trivializing covers of finite-rank cores

This file transfers a finite trivializing cover along an isomorphism of Tau Ceti's point-indexed
finite-rank cores.

## Main results

* `SymplecticGeometry.Bundle.HasFiniteTrivializingCover.of_iso`: if a core `A` has a finite
  trivializing cover with model `Fin A.rank → 𝕜` and `A ≅ A'`, then `A'` has one with model
  `Fin A'.rank → 𝕜`. The proof applies
  `SymplecticGeometry.Bundle.HasFiniteTrivializingCover.of_continuousLinearEquiv` to the fibrewise
  equivalences `TauCeti.FiniteRankBundleCore.isoFiberEquiv` of the isomorphism.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press, 1974, §2.
-/

public section

open TauCeti CategoryTheory

namespace SymplecticGeometry.Bundle

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]

/-- A finite trivializing cover of a point-indexed finite-rank core passes along an isomorphism
of cores. -/
theorem HasFiniteTrivializingCover.of_iso {A A' : FiniteRankBundleCore 𝕜 B}
    (h : HasFiniteTrivializingCover 𝕜 (Fin A.rank → 𝕜) A.core.Fiber) (f : A ≅ A') :
    HasFiniteTrivializingCover 𝕜 (Fin A'.rank → 𝕜) A'.core.Fiber := by
  rcases isEmpty_or_nonempty B with hB | hB
  · exact (hasFiniteTrivializingCover_def ..).2 ⟨∅, by simp, Subsingleton.elim _ _⟩
  have hr := FiniteRankBundleCore.rank_eq_of_iso f
  have hom := FiniteRankBundleCore.continuous_isoFiberEquiv f
  have inv := FiniteRankBundleCore.continuous_isoFiberEquiv f.symm
  simp only [← FiniteRankBundleCore.isoFiberEquiv_symm] at inv
  generalize FiniteRankBundleCore.isoFiberEquiv f = Φ at hom inv
  -- Over a nonempty base the two ranks agree; identify them so that both cores have the model
  -- `Fin A.rank → 𝕜`.
  obtain ⟨n, c, hc⟩ := A'
  subst hr
  -- `exact` identifies the fibres `A.core.Fiber x` and `c.Fiber x` with the coordinates
  -- `Fin A.rank → 𝕜`, which they are by definition.
  exact h.of_continuousLinearEquiv (E' := c.Fiber) Φ hom inv

end SymplecticGeometry.Bundle

end
