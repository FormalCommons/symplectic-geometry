/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

/-!
# Vector fields along open subsets, moved to the ambient manifold

Let `U` be an open subset of a manifold `M` and `N` another manifold. A family of tangent vectors
`Y p ∈ T_{p.2} U`, for `p : N × U`, is read on `M` through the canonical identification
`TauCeti.Manifold.tangentSpaceOpenEquiv` of the tangent spaces of `U` with those of `M`, and
extended by `0` to the points of `N × M` outside `N × U`. If the family is smooth as a map into the
tangent bundle of `U`, the family on `N × M` is smooth on `N × U`
(`TauCeti.Manifold.contMDiffOn_tangentSpaceOpenEquiv_dite`). With `N = ℝ`, this moves a
time-dependent vector field on `U` to `M`.

The proof of `TauCeti.Manifold.contMDiffOn_tangentSpaceOpenEquiv_dite` adapts that of
`TauCeti.IsContactDistributionFamily.contMDiff_distributionGrayVectorField`, in Tau Ceti's file
`TauCeti/Geometry/Contact/Gray/Distribution.lean` at commit
034344347f0ca1144bf5ae35c82e3edaf848fca5 (Tau Ceti pull request #773), which the pinned version
of Tau Ceti does not have. Both proofs read the open subset of the product as a manifold, map it
into `N × U` by `q ↦ (q.1, ⟨q.2, _⟩)`, and compose with the tangent map of the inclusion `U → M`.
-/

public section

open Bundle Set TopologicalSpace
open scoped Manifold ContDiff

namespace TauCeti.Manifold

variable {E H M EN HN N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  {J : ModelWithCorners ℝ EN HN} [TopologicalSpace N] [ChartedSpace HN N]

open Classical in
/-- **A family of tangent vectors of an open subset, read on the ambient manifold.** Let `U` be
an open subset of `M` and `Y p ∈ T_{p.2} U`, for `p : N × U`, a family of tangent vectors that is
smooth as a map into the tangent bundle of `U`. Then the family on `N × M` equal to `Y`, under the
identification of the tangent spaces of `U` with those of `M`, on `N × U`, and to `0` elsewhere, is
smooth on `N × U` as a map into the tangent bundle of `M`. -/
theorem contMDiffOn_tangentSpaceOpenEquiv_dite {U : Opens M} {Y : (p : N × U) → TangentSpace I p.2}
    (hY : ContMDiff (J.prod I) I.tangent ∞ fun p : N × U ↦ (⟨p.2, Y p⟩ : TangentBundle I U)) :
    ContMDiffOn (J.prod I) I.tangent ∞
      (fun p : N × M ↦ (⟨p.2, if h : p.2 ∈ U then
        tangentSpaceOpenEquiv (I := I) ⟨p.2, h⟩ (Y (p.1, ⟨p.2, h⟩)) else 0⟩ : TangentBundle I M))
      (Prod.snd ⁻¹' (U : Set M)) := by
  set W : Opens (N × M) := ⟨Prod.snd ⁻¹' (U : Set M), U.isOpen.preimage continuous_snd⟩
  -- The points of `W`, read in `N × U`.
  set φ : W → N × U := fun q ↦ (q.val.1, ⟨q.val.2, q.property⟩)
  have hφ : ContMDiff (J.prod I) (J.prod I) ∞ φ :=
    (contMDiff_fst.comp contMDiff_subtypeVal).prodMk
      ((ContMDiff.subtypeVal_comp_iff U _).1 (contMDiff_snd.comp contMDiff_subtypeVal))
  have hcomp := (ContMDiff.contMDiff_tangentMap (m := ∞)
    (contMDiff_subtypeVal (I := I) (U := U) (n := ∞)) (by simp)).comp (hY.comp hφ)
  intro p hp
  refine (contMDiffAt_subtype_iff (U := W) (x := ⟨p, hp⟩)).1
    ((hcomp ⟨p, hp⟩).congr_of_eventuallyEq (.of_forall fun q ↦ ?_)) |>.contMDiffWithinAt
  have hq : (q : N × M).2 ∈ U := q.property
  simp only [Function.comp_apply, tangentMap_subtype_val, φ, hq, ↓reduceDIte]

end TauCeti.Manifold

end
