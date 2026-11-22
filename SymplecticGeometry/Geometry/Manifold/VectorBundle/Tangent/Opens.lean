/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import SymplecticGeometry.Geometry.Manifold.ContMDiff.Opens
public import TauCeti.Geometry.Manifold.ContMDiff.Subtype
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

Conversely, a smooth family of tangent vectors of `M` along a map `f : N → U`, read in the tangent
spaces of `U`, is smooth as a map into the tangent bundle of `U`
(`TauCeti.Manifold.contMDiff_tangentSpaceOpenEquiv_symm`). With `N = ℝ × U` and `f = Prod.snd`,
this restricts a time-dependent vector field on `M` to `U`. Its proof compares the coordinates of
a vector in the tangent charts of `U` and of `M`, as the proof of Tau Ceti's
`TauCeti.Manifold.inCoordinates_openTangentSpaceHom_eq` does for linear maps.

The proof of `TauCeti.Manifold.contMDiffOn_tangentSpaceOpenEquiv_dite` adapts that of
`TauCeti.IsContactDistributionFamily.contMDiff_distributionGrayVectorField`, in Tau Ceti's file
`TauCeti/Geometry/Contact/Gray/Distribution.lean` at commit
034344347f0ca1144bf5ae35c82e3edaf848fca5 (Tau Ceti pull request #773), which the pinned version
of Tau Ceti does not have. Both proofs read the open subset of the product as a manifold, map it
into `N × U` by `q ↦ (q.1, ⟨q.2, _⟩)`, and compose with the tangent map of the inclusion `U → M`;
here the first two steps are those of `ContMDiff.contMDiffOn_prod_opens_of_eq`.
-/

public section

open Bundle Set TopologicalSpace
open scoped Manifold ContDiff

namespace TauCeti.Manifold

variable {E H M EN HN N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  {J : ModelWithCorners ℝ EN HN} [TopologicalSpace N] [ChartedSpace HN N]

open Classical in
/-- **A family of tangent vectors of an open subset, read on the ambient manifold.** Let `U` be
an open subset of `M` and `Y p ∈ T_{p.2} U`, for `p : N × U`, a family of tangent vectors that is
smooth as a map into the tangent bundle of `U`. Then the family on `N × M` equal to `Y`, under the
identification of the tangent spaces of `U` with those of `M`, on `N × U`, and to `0` elsewhere, is
smooth on `N × U` as a map into the tangent bundle of `M`. -/
theorem contMDiffOn_tangentSpaceOpenEquiv_dite [IsManifold I ∞ M] {U : Opens M}
    {Y : (p : N × U) → TangentSpace I p.2}
    (hY : ContMDiff (J.prod I) I.tangent ∞ fun p : N × U ↦ (⟨p.2, Y p⟩ : TangentBundle I U)) :
    ContMDiffOn (J.prod I) I.tangent ∞
      (fun p : N × M ↦ (⟨p.2, if h : p.2 ∈ U then
        tangentSpaceOpenEquiv (I := I) ⟨p.2, h⟩ (Y (p.1, ⟨p.2, h⟩)) else 0⟩ : TangentBundle I M))
      (Prod.snd ⁻¹' (U : Set M)) := by
  rw [← univ_prod]
  refine ContMDiff.contMDiffOn_prod_opens_of_eq ((ContMDiff.contMDiff_tangentMap (m := ∞)
    (contMDiff_subtypeVal (I := I) (U := U) (n := ∞)) (by simp)).comp hY) fun t x hx ↦ ?_
  simp only [Function.comp_apply, tangentMap_subtype_val, hx, ↓reduceDIte]

/-- **A tangent vector field of `M`, read on an open subset.** Let `f : N → U` be a map into an
open subset `U` of `M` and `V z ∈ T_{f z} M` a family of tangent vectors of `M` along it, smooth
as a `C^n` map into the tangent bundle of `M`. Then the same vectors, read in the tangent spaces
of `U` through `tangentSpaceOpenEquiv`, form a `C^n` map into the tangent bundle of `U`. With
`N = ℝ × U` and `f = Prod.snd`, this restricts a `C^n` time-dependent vector field to `U`. -/
theorem contMDiff_tangentSpaceOpenEquiv_symm [IsManifold I 1 M] {n : WithTop ℕ∞} {U : Opens M}
    {f : N → U} {V : (z : N) → TangentSpace I (f z : M)}
    (hV : ContMDiff J I.tangent n fun z ↦ (⟨f z, V z⟩ : TangentBundle I M)) :
    ContMDiff J I.tangent n fun z ↦
      (⟨f z, (tangentSpaceOpenEquiv (f z)).symm (V z)⟩ : TangentBundle I U) := by
  intro z₀
  have h := contMDiffAt_totalSpace_iff.1 (hV z₀)
  have hf := (TauCeti.ContMDiffAt.subtypeVal_comp_iff U f z₀).1 h.1
  refine contMDiffAt_totalSpace_iff.2 ⟨hf, h.2.congr_of_eventuallyEq ?_⟩
  set tU := trivializationAt E (TangentSpace I : U → Type _) (f z₀)
  set tM := trivializationAt E (TangentSpace I : M → Type _) (f z₀ : M)
  -- Near `z₀`, the coordinates of a vector of `U` in the chart of `U` are those of the same vector
  -- of `M` in the chart of `M`.
  filter_upwards [hf.continuousAt.eventually
      (eventually_tangentSpaceOpenEquiv_symmL_trivializationAt_eq (I := I) (f z₀)),
    hf.continuousAt.eventually (tU.open_baseSet.mem_nhds (mem_baseSet_trivializationAt E _ _)),
    (continuousAt_subtypeVal.comp hf.continuousAt).eventually
      (tM.open_baseSet.mem_nhds (mem_baseSet_trivializationAt E _ _))] with z hs hU hM
  rw [← tU.continuousLinearMapAt_apply_of_mem (R := ℝ) hU,
    ← tM.continuousLinearMapAt_apply_of_mem (R := ℝ) (b := (f z : M)) hM]
  have hw : (tangentSpaceOpenEquiv (I := I) (f z)).symm (V z) =
      tU.symmL ℝ (f z) (tM.continuousLinearMapAt ℝ (f z : M) (V z)) := by
    apply (tangentSpaceOpenEquiv (I := I) (f z)).injective
    rw [ContinuousLinearEquiv.apply_symm_apply, hs]
    exact (tM.symmL_continuousLinearMapAt hM (V z)).symm
  rw [hw, tU.continuousLinearMapAt_symmL hU]

end TauCeti.Manifold

end
