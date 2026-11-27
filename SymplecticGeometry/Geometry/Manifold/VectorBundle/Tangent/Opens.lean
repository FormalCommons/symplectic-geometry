/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
public import TauCeti.Topology.VectorBundle.ContinuousAlternatingMap
import SymplecticGeometry.Geometry.Manifold.ContMDiff.Opens
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Restriction

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

A field of endomorphisms `A y` of the tangent spaces of `M` is `C^n` at a point `x` of `U`
exactly when the field it induces on `U` through the same identification is
(`TauCeti.Manifold.contMDiffAt_restrictOpen_tangentEnd_iff`): near `x`, the two read alike in
coordinates (`TauCeti.Manifold.eventually_inCoordinates_openTangentSpaceHom_eq`). Its proof adapts
that of Tau Ceti's `TauCeti.Manifold.contMDiffAt_tangentBundle_opens_iff` from tangent vectors to
fields of endomorphisms: both sides are unfolded into conditions on the total space, the
continuity parts are matched on the subtype, and the coordinate parts agree near `x`. Tau Ceti's
`TauCeti.Manifold.contMDiff_restrictOpenTangentSpaceEnd` gives the direction from `M` to `U`
for a whole field; the converse lets a field be built from its values on an open cover.

Likewise, a family of linear maps into the tangent spaces along a map `g` into `U`, continuous at
`x₀`, reads near `x₀` the same in the tangent coordinates of `U` as in those of `M`
(`TauCeti.Manifold.inTangentCoordinates_subtypeVal_comp_eventuallyEq`), since the tangent
trivializations of `U` and of `M` agree near each point of `U` (Tau Ceti's
`TauCeti.Manifold.eventually_trivializationAt_tangentSpace_opens_eq`).

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

section Endomorphism

variable {𝕜 E H M : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I 1 M]

/-- A field `A` of endomorphisms of the tangent spaces of `M` is `C^n` at a point `x` of an
open subset `U` exactly when the field that it induces on `U`, through the identification
`tangentSpaceOpenEquiv` of the tangent spaces of `U` with those of `M`, is `C^n` at `x`. -/
theorem contMDiffAt_restrictOpen_tangentEnd_iff {n : ℕ∞ω}
    {A : ∀ y : M, TangentSpace I y →L[𝕜] TangentSpace I y} {U : Opens M} {x : U} :
    ContMDiffAt I (I.prod 𝓘(𝕜, E →L[𝕜] E)) n
        (fun y : U ↦ TotalSpace.mk' (E →L[𝕜] E)
          (E := fun y : U ↦ TangentSpace I y →L[𝕜] TangentSpace I y) y
          ((tangentSpaceOpenEquiv (I := I) y).symm.toContinuousLinearMap.comp
            ((A y).comp (tangentSpaceOpenEquiv (I := I) y).toContinuousLinearMap))) x ↔
      ContMDiffAt I (I.prod 𝓘(𝕜, E →L[𝕜] E)) n
        (fun y : M ↦ TotalSpace.mk' (E →L[𝕜] E)
          (E := fun y : M ↦ TangentSpace I y →L[𝕜] TangentSpace I y) y (A y)) x := by
  rw [contMDiffAt_hom_bundle, contMDiffAt_hom_bundle]
  refine and_congr (iff_of_true contMDiffAt_id contMDiffAt_id) ?_
  rw [← contMDiffAt_subtype_iff]
  refine Filter.EventuallyEq.contMDiffAt_iff ?_
  have hdiag : ContinuousAt (fun y : U ↦ (y, y)) x :=
    (continuous_id.prodMk continuous_id).continuousAt
  filter_upwards [hdiag.eventually
    (eventually_inCoordinates_openTangentSpaceHom_eq (I := I) (I' := I) x x)] with y hy
  exact hy (A y)

end Endomorphism

section InTangentCoordinates

variable {𝕜 E H M E' H' N X : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I 1 M] [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold I' 1 N] [TopologicalSpace X]

/-- A family of linear maps `ϕ x` into the tangent spaces of `M` along a map `g` into an open
subset `U` of `M`, continuous at `x₀`, reads near `x₀` the same in the tangent coordinates of `U`
as in those of `M`. -/
theorem inTangentCoordinates_subtypeVal_comp_eventuallyEq {U : Opens M} {f : X → N} {g : X → U}
    (ϕ : ∀ x, TangentSpace I' (f x) →L[𝕜] TangentSpace I (g x : M)) {x₀ : X}
    (hg : ContinuousAt g x₀) :
    inTangentCoordinates I' I f g ϕ x₀ =ᶠ[𝓝 x₀]
      inTangentCoordinates I' I f (fun x ↦ (g x : M)) ϕ x₀ := by
  have hU : ∀ᶠ x in 𝓝 x₀,
      g x ∈ (trivializationAt E (TangentSpace I : U → Type _) (g x₀)).baseSet :=
    hg.eventually ((trivializationAt E (TangentSpace I : U → Type _) (g x₀)).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt E (TangentSpace I : U → Type _) (g x₀)))
  have hM : ∀ᶠ x in 𝓝 x₀,
      (g x : M) ∈ (trivializationAt E (TangentSpace I : M → Type _) (g x₀ : M)).baseSet :=
    (continuousAt_subtypeVal.comp hg).eventually
      ((trivializationAt E (TangentSpace I : M → Type _) (g x₀ : M)).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt E (TangentSpace I : M → Type _) (g x₀ : M)))
  filter_upwards [hg.eventually (eventually_trivializationAt_tangentSpace_opens_eq (I := I) (g x₀)),
    hU, hM] with x hx hxU hxM
  refine ContinuousLinearMap.ext fun v ↦ ?_
  simp only [inTangentCoordinates, ContinuousLinearMap.inCoordinates]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    Trivialization.continuousLinearMapAt_apply_of_mem (R := 𝕜) _ hxU,
    Trivialization.continuousLinearMapAt_apply_of_mem (R := 𝕜) _ hxM]
  exact hx _

end InTangentCoordinates

end TauCeti.Manifold

end
