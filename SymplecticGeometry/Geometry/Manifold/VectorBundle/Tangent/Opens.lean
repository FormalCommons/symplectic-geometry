/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import SymplecticGeometry.Geometry.Manifold.ContMDiff.Opens
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
public import TauCeti.Topology.VectorBundle.ContinuousAlternatingMap

/-!
# Tangent vectors and alternating maps of open subsets, read on the ambient manifold

Let `U` be an open subset of a manifold `M` and `N` another manifold. A family of tangent vectors
`Y p ∈ T_{p.2} U`, for `p : N × U`, is read on `M` through the canonical identification
`TauCeti.Manifold.tangentSpaceOpenEquiv` of the tangent spaces of `U` with those of `M`, and
extended by `0` to the points of `N × M` outside `N × U`. If the family is smooth as a map into the
tangent bundle of `U`, the family on `N × M` is smooth on `N × U`
(`TauCeti.Manifold.contMDiffOn_tangentSpaceOpenEquiv_dite`). With `N = ℝ`, this moves a
time-dependent vector field on `U` to `M`.

Near each point `x` of `U`, the trivialization at `x` of the bundle of continuous alternating
maps from the tangent spaces of `U` to a fixed space `G` gives the same coordinates as the
trivialization at `x` of the corresponding bundle over `M`
(`TauCeti.Manifold.eventually_trivializationAt_continuousAlternatingMap_tangentSpace_opens_eq`).
This is the analogue, for alternating maps, of Tau Ceti's
`TauCeti.Manifold.eventually_trivializationAt_tangentSpace_opens_eq`. Its proof adapts that of
`TauCeti.CotangentBundle.inCoordinates_open_eventuallyEq`, in Tau Ceti's file
`TauCeti/Geometry/Manifold/VectorBundle/Cotangent/Opens.lean`, from covectors to alternating
maps. Both apply `TauCeti.Manifold.eventually_tangentSpaceOpenEquiv_symmL_trivializationAt_eq`,
since such a trivialization precomposes with the inverse trivialization of the tangent bundle;
here that precomposition is Tau Ceti's
`FiberBundle.trivializationAt_continuousAlternatingMap_apply_snd`.

The proof of `TauCeti.Manifold.contMDiffOn_tangentSpaceOpenEquiv_dite` adapts that of
`TauCeti.IsContactDistributionFamily.contMDiff_distributionGrayVectorField`, in Tau Ceti's file
`TauCeti/Geometry/Contact/Gray/Distribution.lean`. Both proofs read the open subset of the
product as a manifold, map it into `N × U` by `q ↦ (q.1, ⟨q.2, _⟩)`, and compose with the tangent
map of the inclusion `U → M`; here the first two steps are those of
`ContMDiff.contMDiffOn_prod_opens_of_eq`.
-/

public section

open Bundle Filter Set TopologicalSpace
open scoped Manifold ContDiff Topology

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

section ContinuousAlternatingMap

variable {𝕜 E H M G ι : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I 1 M] [NormedAddCommGroup G] [NormedSpace 𝕜 G] [Fintype ι]

/-- Near a point `x` of an open submanifold `U` of `M`, the trivialization at `x` of the bundle
of continuous alternating maps `T_y U [⋀^ι]→L G` reads every such map as the trivialization at `x`
of the bundle of continuous alternating maps `T_y M [⋀^ι]→L G` does; the tangent spaces of `U`
and `M` at `y` are the same space. -/
theorem eventually_trivializationAt_continuousAlternatingMap_tangentSpace_opens_eq
    {U : Opens M} (x : U) :
    ∀ᶠ y in 𝓝 x, ∀ φ : TangentSpace I y [⋀^ι]→L[𝕜] G,
      (trivializationAt (E [⋀^ι]→L[𝕜] G)
          (fun y : U ↦ TangentSpace I y [⋀^ι]→L[𝕜] Trivial U G y) x ⟨y, φ⟩).2 =
        (trivializationAt (E [⋀^ι]→L[𝕜] G)
          (fun y : M ↦ TangentSpace I y [⋀^ι]→L[𝕜] Trivial M G y) (x : M) ⟨(y : M), φ⟩).2 := by
  filter_upwards [eventually_tangentSpaceOpenEquiv_symmL_trivializationAt_eq (I := I) x]
    with y hy φ
  simp only [tangentSpaceOpenEquiv_apply] at hy
  rw [FiberBundle.trivializationAt_continuousAlternatingMap_apply_snd,
    FiberBundle.trivializationAt_continuousAlternatingMap_apply_snd (V := TangentSpace I)
      (F := G) (x : M) (x := (y : M)) φ]
  ext v
  exact congrArg φ (funext fun i ↦ hy (v i))

end ContinuousAlternatingMap

end TauCeti.Manifold

end
