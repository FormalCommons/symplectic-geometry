/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Topology
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Section.Hom
public import SymplecticGeometry.Geometry.Manifold.ContMDiffMap.Chart.TangentMap
public import TauCeti.Geometry.Diffeomorphism.Topology
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Pullback
import TauCeti.Geometry.Diffeomorphism.Inversion
import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Comp
import TauCeti.Geometry.Manifold.Diffeomorph.Basic

/-!
# Continuity of almost complex structures from their action on the tangent bundle

A smooth almost complex structure `J` acts on the tangent bundle by the smooth map
`v ↦ ⟨v.proj, J v.proj v.snd⟩` (`TauCeti.SmoothAlmostComplexStructure.tangentBundleMap`). For a
finite-dimensional model, a family of smooth almost complex structures is continuous for Tau
Ceti's `C^∞` topology `TauCeti.SmoothAlmostComplexStructure.frameTopology`, in any frame system,
as soon as these maps depend continuously on the parameter for the weak Whitney topology
(`TauCeti.SmoothAlmostComplexStructure.continuous_frameTopology_of_continuous_tangentBundleMap`).
The map is `ContMDiffSection.totalSpaceMap` of the endomorphism section of `J`, and the result is
the case of the tangent endomorphism bundle of
`ContMDiffSection.continuous_frameTopology_of_continuous_totalSpaceMap`, through Tau Ceti's
`TauCeti.SmoothAlmostComplexStructure.continuous_frameTopology_iff`.

For a diffeomorphism `φ : M → N`, the map of the tangent bundle given by the pull-back `φ^* J` is
`Tφ⁻¹ ∘ J ∘ Tφ` (`TauCeti.SmoothAlmostComplexStructure.tangentBundleMap_pullback`). So, for
compact manifolds with finite-dimensional models, `N` Hausdorff, `φ ↦ φ^* J` is continuous from the
diffeomorphisms with the weak Whitney topology to the `C^∞` topology
(`TauCeti.SmoothAlmostComplexStructure.continuous_pullback`): the tangent map is continuous
(`ContMDiffMap.continuous_tangentMap_manifoldWeakWhitney`), and so are inversion
(`Diffeomorph.continuous_symm`) and composition
(`ContMDiffMap.continuous_comp_manifoldWeakWhitney`) in Tau Ceti.

## Main definitions and results

* `TauCeti.SmoothAlmostComplexStructure.tangentBundleMap`, with
  `TauCeti.SmoothAlmostComplexStructure.tangentBundleMap_def` and
  `TauCeti.SmoothAlmostComplexStructure.tangentBundleMap_apply`
* `TauCeti.SmoothAlmostComplexStructure.continuous_frameTopology_of_continuous_tangentBundleMap`
* `TauCeti.SmoothAlmostComplexStructure.tangentBundleMap_pullback`
* `TauCeti.SmoothAlmostComplexStructure.continuous_pullback`

## References

* [M. W. Hirsch, *Differential Topology*][Hirsch1976], Chapter 2, §1 (the weak topology on
  spaces of `C^r` maps, as Tau Ceti builds it)
* [D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*][McDuffSalamon2012],
  Section 3.2 (the `C^∞` topology on almost complex structures)
-/

public section

open Bundle TopologicalSpace
open scoped ContDiff Manifold TauCeti.ManifoldWeakWhitney TauCeti.DiffeomorphWeakWhitney

namespace TauCeti.SmoothAlmostComplexStructure

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- A smooth almost complex structure, as the smooth map `v ↦ ⟨v.proj, J v.proj v.snd⟩` of the
tangent bundle to itself: the map of total spaces of its endomorphism section. -/
noncomputable def tangentBundleMap (J : SmoothAlmostComplexStructure I M) :
    C^∞⟮I.tangent, TangentBundle I M; I.tangent, TangentBundle I M⟯ :=
  J.toEndomorphism.totalSpaceMap

/-- The map of the tangent bundle given by `J` is that of total spaces of its endomorphism
section. -/
theorem tangentBundleMap_def (J : SmoothAlmostComplexStructure I M) :
    J.tangentBundleMap = J.toEndomorphism.totalSpaceMap :=
  (rfl)

/-- The map of the tangent bundle given by `J` sends `v` to `J v` in the same fibre. -/
@[simp]
theorem tangentBundleMap_apply (J : SmoothAlmostComplexStructure I M) (v : TangentBundle I M) :
    J.tangentBundleMap v = ⟨v.proj, J v.proj v.snd⟩ := by
  simp [tangentBundleMap_def]

/-- For a finite-dimensional model and any frame system of `End(TM)`, a family of smooth
almost complex structures is continuous for the `C^∞` topology as soon as the maps of the tangent
bundle `v ↦ ⟨v.proj, J p v.proj v.snd⟩` depend continuously on `p` for the weak Whitney
topology. -/
theorem continuous_frameTopology_of_continuous_tangentBundleMap [FiniteDimensional ℝ E]
    {ι : Type*}
    (e : ι → Trivialization (E →L[ℝ] E)
      (π (E →L[ℝ] E) (fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)))
    [∀ i, MemTrivializationAtlas (e i)]
    (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)
    {P : Type*} [TopologicalSpace P] {J : P → SmoothAlmostComplexStructure I M}
    (hJ : Continuous fun p ↦ (J p).tangentBundleMap) :
    letI := frameTopology e U hU
    Continuous J := by
  let _ := ContMDiffSection.frameTopology (I := I) (n := ∞) e U hU
  let _ := frameTopology e U hU
  exact (continuous_frameTopology_iff e U hU).mpr
    (ContMDiffSection.continuous_frameTopology_of_continuous_totalSpaceMap e U hU
      (by simpa only [tangentBundleMap_def] using hJ))

variable [FiniteDimensional ℝ E] {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' ∞ N]

/-- The map of the tangent bundle given by the pull-back `φ^* J` is `Tφ⁻¹ ∘ J ∘ Tφ`. -/
theorem tangentBundleMap_pullback (φ : M ≃ₘ⟮I, I'⟯ N) (J : SmoothAlmostComplexStructure I' N) :
    (J.pullback φ).tangentBundleMap =
      (φ.symm.toContMDiffMap.tangentMap ENat.coe_top_add_one.le).comp
        (J.tangentBundleMap.comp (φ.toContMDiffMap.tangentMap ENat.coe_top_add_one.le)) := by
  refine ContMDiffMap.ext fun ⟨x, v⟩ ↦ ?_
  simp only [ContMDiffMap.comp_apply, ContMDiffMap.coe_tangentMap, tangentBundleMap_apply,
    pullback_apply]
  exact (φ.tangentMap_symm_mk (by simp) x _).symm

/-- Let `M` and `N` be compact manifolds with finite-dimensional models, `N` Hausdorff. For any
frame system of `End(TM)`, the pull-back `φ ↦ φ^* J` of a smooth almost complex structure `J` on
`N` along diffeomorphisms `φ : M → N` is continuous from the weak Whitney topology to the `C^∞`
topology. -/
theorem continuous_pullback [CompactSpace M] [CompactSpace N] [T2Space N] {ι : Type*}
    (e : ι → Trivialization (E →L[ℝ] E)
      (π (E →L[ℝ] E) (fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)))
    [∀ i, MemTrivializationAtlas (e i)]
    (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)
    (J : SmoothAlmostComplexStructure I' N) :
    letI := frameTopology e U hU
    Continuous fun φ : M ≃ₘ⟮I, I'⟯ N ↦ J.pullback φ := by
  refine continuous_frameTopology_of_continuous_tangentBundleMap e U hU ?_
  simp only [tangentBundleMap_pullback]
  exact ContMDiffMap.continuous_comp_manifoldWeakWhitney.comp
    ((ContMDiffMap.continuous_tangentMap_manifoldWeakWhitney.comp
      (Diffeomorph.continuous_toContMDiffMap.comp Diffeomorph.continuous_symm)).prodMk
      ((ContMDiffMap.continuous_postcomp_manifoldWeakWhitney _).comp
        (ContMDiffMap.continuous_tangentMap_manifoldWeakWhitney.comp
          Diffeomorph.continuous_toContMDiffMap)))

end TauCeti.SmoothAlmostComplexStructure

end
