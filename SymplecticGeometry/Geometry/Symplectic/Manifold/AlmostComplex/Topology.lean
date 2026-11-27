/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Topology
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Section.Hom

/-!
# Continuity of almost complex structures from their action on the tangent bundle

A smooth almost complex structure `J` acts on the tangent bundle by the smooth map
`v ↦ ⟨v.proj, J v.proj v.snd⟩` (`TauCeti.SmoothAlmostComplexStructure.tangentBundleMap`). For a
finite-dimensional model, a family of smooth almost complex structures is continuous for Tau
Ceti's `C^∞` topology `TauCeti.SmoothAlmostComplexStructure.frameTopology`, in any covering frame
system, as soon as these maps depend continuously on the parameter for the weak Whitney topology
(`TauCeti.SmoothAlmostComplexStructure.continuous_frameTopology_of_continuous_tangentBundleMap`).
This is the case of the tangent endomorphism bundle of
`ContMDiffSection.continuous_frameTopology_of_continuous_totalSpaceMap`, through Tau Ceti's
`TauCeti.SmoothAlmostComplexStructure.continuous_frameTopology_iff`.

## Main definitions and results

* `TauCeti.SmoothAlmostComplexStructure.tangentBundleMap`
* `TauCeti.SmoothAlmostComplexStructure.continuous_frameTopology_of_continuous_tangentBundleMap`

## References

* [M. W. Hirsch, *Differential Topology*][Hirsch1976], Chapter 2, §1 (the weak topology on
  spaces of `C^r` maps, as Tau Ceti builds it)
* [D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*][McDuffSalamon2012],
  Section 3.2 (the `C^∞` topology on almost complex structures)
-/

public section

open Bundle TopologicalSpace
open scoped ContDiff Manifold TauCeti.ManifoldWeakWhitney

namespace TauCeti.SmoothAlmostComplexStructure

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- A smooth almost complex structure, as the smooth map `v ↦ ⟨v.proj, J v.proj v.snd⟩` of the
tangent bundle to itself. -/
noncomputable def tangentBundleMap (J : SmoothAlmostComplexStructure I M) :
    C^∞⟮I.tangent, TangentBundle I M; I.tangent, TangentBundle I M⟯ :=
  ⟨fun v ↦ ⟨v.proj, J v.proj v.snd⟩, J.contMDiff_apply contMDiff_id⟩

/-- The map of the tangent bundle given by `J` sends `v` to `J v` in the same fibre. -/
@[simp]
theorem tangentBundleMap_apply (J : SmoothAlmostComplexStructure I M) (v : TangentBundle I M) :
    J.tangentBundleMap v = ⟨v.proj, J v.proj v.snd⟩ :=
  (rfl)

/-- For a finite-dimensional model and a covering frame system of `End(TM)`, a family of smooth
almost complex structures is continuous for the `C^∞` topology as soon as the maps of the tangent
bundle `v ↦ ⟨v.proj, J p v.proj v.snd⟩` depend continuously on `p` for the weak Whitney
topology. -/
theorem continuous_frameTopology_of_continuous_tangentBundleMap [FiniteDimensional ℝ E]
    {ι : Type*}
    (e : ι → Trivialization (E →L[ℝ] E)
      (π (E →L[ℝ] E) (fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)))
    [∀ i, MemTrivializationAtlas (e i)]
    (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet) (hcover : ∀ x, ∃ i, x ∈ U i)
    {P : Type*} [TopologicalSpace P] {J : P → SmoothAlmostComplexStructure I M}
    (hJ : Continuous fun p ↦ (J p).tangentBundleMap) :
    letI := frameTopology e U hU
    Continuous J := by
  let _ := ContMDiffSection.frameTopology (I := I) (n := ∞) e U hU
  let _ := frameTopology e U hU
  exact (continuous_frameTopology_iff e U hU).mpr
    (ContMDiffSection.continuous_frameTopology_of_continuous_totalSpaceMap e U hU hcover
      (fun p ↦ (J p).tangentBundleMap) (fun _ _ ↦ rfl) hJ)

end TauCeti.SmoothAlmostComplexStructure

end
