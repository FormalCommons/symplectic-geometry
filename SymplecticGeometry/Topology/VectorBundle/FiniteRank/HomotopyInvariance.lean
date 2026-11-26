/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Pullback
public import TauCeti.Topology.VectorBundle.HomotopyInvariance

/-!
# Homotopy invariance of pullbacks of finite-rank cores

For a point-indexed finite-rank core `A` over `Y` and homotopic maps `f₀ f₁ : C(X, Y)` out of a
paracompact R₁ space, the pullbacks `A.pullback f₀` and `A.pullback f₁` are isomorphic
(`TauCeti.FiniteRankBundleCore.nonempty_pullback_iso_of_homotopic`). This is Tau Ceti's
`ContinuousMap.Homotopic.exists_continuousLinearEquiv_pullback`, for Mathlib's pullbacks of the
bundle of `A`, carried to the pulled-back cores by `TauCeti.FiniteRankBundleCore.pullbackHomeomorph`
and `TauCeti.FiniteRankBundleCore.isoOfContinuousEquiv`.

As a consequence, a core over `Y × E`, for a real normed space `E`, is the pullback along the
projection of its restriction to `Y × {c}`, since the segments to `c` contract `E`
(`TauCeti.FiniteRankBundleCore.nonempty_iso_pullback_fst`).

## References

* [A. Hatcher, *Vector Bundles and K-Theory*][Hatcher2017], §1.2, Theorem 1.6.
-/

public section

namespace TauCeti.FiniteRankBundleCore

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜] [CompleteSpace 𝕜]
  {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [ParacompactSpace X] [R1Space X]

/-- **Homotopy invariance of pullbacks of cores.** Over a paracompact R₁ space `X`, the pullbacks
of a finite-rank core `A` along homotopic maps `f₀ f₁ : C(X, Y)` are isomorphic. -/
theorem nonempty_pullback_iso_of_homotopic (A : FiniteRankBundleCore 𝕜 Y) {f₀ f₁ : C(X, Y)}
    (h : f₀.Homotopic f₁) : Nonempty (A.pullback f₀ ≅ A.pullback f₁) := by
  obtain ⟨Φ, hΦ, -⟩ :=
    h.exists_continuousLinearEquiv_pullback (𝕜 := 𝕜) (F := Fin A.rank → 𝕜) (E := A.core.Fiber)
  refine ⟨isoOfContinuousEquiv (A := A.pullback f₀) (D := A.pullback f₁) Φ ?_⟩
  refine ((A.pullbackHomeomorph f₁).symm.continuous.comp
    (hΦ.comp (A.pullbackHomeomorph f₀).continuous)).congr fun p ↦ ?_
  simp only [Function.comp_apply, pullbackHomeomorph_symm_apply, Bundle.TotalSpace.mk']
  rw [pullbackHomeomorph_apply]
  rfl

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
    ⟨⟨⟨fun q ↦ (q.2.1, c + (1 - q.1 : ℝ) • (q.2.2 - c)), by fun_prop⟩,
      fun q ↦ by simp, fun q ↦ by simp⟩⟩
  obtain ⟨e⟩ := A.nonempty_pullback_iso_of_homotopic h
  rw [pullback_id, ← pullback_comp] at e
  exact ⟨e⟩

end TauCeti.FiniteRankBundleCore

end
