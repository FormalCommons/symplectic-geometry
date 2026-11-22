/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.Orientation.Linear
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Chart
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Smooth
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

/-!
# The local orientation of the identity chart

Let `E` be a real inner product space of dimension `n + 1`, oriented by `o`, and `p` a point of
`E`. Tau Ceti's local orientation of `E` at `p` selected by the identity chart and `o`
(`OpenPartialHomeomorph.localOrientationOfOrientedChart`) is a class of `H_{n+1}(E, E ∖ {p})`.
This file computes its image under the connecting morphism of the pair `(E, E ∖ {p})` followed by
radial projection about `p` onto the unit sphere: it is the generator of the reduced homology of
the unit sphere selected by `o` (`TauCeti.reducedSingularHomologySphereIsoOfOrientation`).

It then reads the local orientations of an oriented `C¹` manifold `M`, modelled on a real normed
space `E` that need not carry an inner product, in the centered chart at `z` with values in `E`:
there they become the local orientation of `E` at the origin selected by the orientation of the
fibre at `z`, read in the trivialization of the tangent bundle at `z`.

## Main results

* `OpenPartialHomeomorph.map_reducedSingularHomologyδ_localOrientationOfOrientedChart_refl`: the
  local orientation of the identity chart, sent through the connecting morphism and radial
  projection, is the oriented generator of the unit sphere.
* `TauCeti.Manifold.Orientation.localHomologyMap_sub_toHomologicalOrientation`: the centered chart
  of `M` at `z` carries the local orientation of `o.toHomologicalOrientation` at `z` to the local
  orientation of `E` at the origin selected by `o` at `z`.

## Implementation notes

For `TauCeti.Manifold.Orientation.localHomologyMap_sub_toHomologicalOrientation`, the chart is
followed by a linear identification `L` of `E` with a Euclidean space; Tau Ceti's
`TauCeti.localOrientationOfManifoldOrientation_eq_localOrientationOfOrientedChart_transHomeomorph`
reads the local orientation of `M` in that chart, and
`OpenPartialHomeomorph.localHomologyMap_chart_localOrientationOfOrientedChart`, from
`SymplecticGeometry/AlgebraicTopology/Singular/LocalHomology/Orientation/Linear.lean` (a copy of
Tau Ceti's main branch at commit 55525ca), applied to that chart and `L⁻¹`, carries it back to
`E`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.3 (local
  orientations and the generators of the homology of spheres).
-/

public section

noncomputable section

open CategoryTheory TauCeti AlgebraicTopology Module Set Topology TopologicalSpace

universe w

namespace OpenPartialHomeomorph

variable {E : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The local orientation of the identity chart, through the sphere.** The local orientation
of `E` at `p` selected by the identity chart and the orientation `o`, sent through the connecting
morphism of the pair `(E, E ∖ {p})` and radial projection about `p`, is the generator of the
reduced homology of the unit sphere selected by `o`. -/
theorem map_reducedSingularHomologyδ_localOrientationOfOrientedChart_refl {p : E}
    (hp : p ∈ (OpenPartialHomeomorph.refl E).source) {n : ℕ}
    (o : Orientation ℝ E (Fin (n + 1))) (hE : finrank ℝ E = n + 1) :
    (reducedSingularHomologyFunctor (ModuleCat.of ℤ (ULift.{w} ℤ)) n).map
        (TopCat.ofHom (complSingletonHomotopyEquivSphere p).toFun)
      ((TopPair.ofSubset ({p}ᶜ : Set (TopCat.of E))).reducedSingularHomologyδ
        (ModuleCat.of ℤ (ULift.{w} ℤ)) n
        ((OpenPartialHomeomorph.refl E).localOrientationOfOrientedChart hp o hE).val) =
      (reducedSingularHomologySphereIsoOfOrientation (ModuleCat.of ℤ (ULift.{w} ℤ)) o hE).inv
        1 := by
  have h := singularHomologyComplSingletonIsoOfOrientation_refl_hom
    (ModuleCat.of ℤ (ULift.{w} ℤ)) hp o hE
  rw [OpenPartialHomeomorph.coe_localOrientationOfOrientedChart]
  set e := singularHomologyComplSingletonIsoOfOrientation (ModuleCat.of ℤ (ULift.{w} ℤ))
    (OpenPartialHomeomorph.refl E) hp o hE
  set s := reducedSingularHomologySphereIsoOfOrientation (ModuleCat.of ℤ (ULift.{w} ℤ)) o hE
  apply (ConcreteCategory.bijective_of_isIso s.hom).1
  calc s.hom _ = e.hom (e.inv 1) := by
        rw [h, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
        -- The two sides differ only in how the degree of the local homology class is written,
        -- as `n + 1` or as the degree of the pair's homology.
        rfl
    _ = s.hom (s.inv 1) := by rw [Iso.inv_hom_id_apply, Iso.inv_hom_id_apply]

end OpenPartialHomeomorph

namespace TauCeti.Manifold.Orientation

open Bundle

variable {E H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [ChartedSpace E M]
  [IsManifold I 1 M] {m : ℕ} (hE : finrank ℝ E = m + 1)
  (o : Manifold.Orientation I M (Fin (m + 1)))

/-- In the chart `φ` of `M` at `z` with values in the model `E`, the map `x ↦ φ x - φ z` carries
the local orientation of `M` at `z` given by `o` to the local orientation of `E` at the origin
given by `o` at `z`, read in the trivialization of the tangent bundle at `z`. -/
theorem localHomologyMap_sub_toHomologicalOrientation (z : M) :
    localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ))
        (⟨fun x : ((chartAt H z).transHomeomorph I.toHomeomorph).source ↦
            (chartAt H z).transHomeomorph I.toHomeomorph x -
              (chartAt H z).transHomeomorph I.toHomeomorph z,
          ((chartAt H z).transHomeomorph I.toHomeomorph).continuousOn.domRestrict.sub
            continuous_const⟩ :
          C(((chartAt H z).transHomeomorph I.toHomeomorph).source, E))
        (S := {⟨z, by simp⟩}) (T := {0})
        (by
          rintro x hx
          exact Subtype.ext (((chartAt H z).transHomeomorph I.toHomeomorph).injOn x.property
            (by simp) (sub_eq_zero.1 hx))) (m + 1)
        ((((chartAt H z).transHomeomorph I.toHomeomorph).open_source.isOpenEmbedding_subtypeVal
          |>.localOrientationEquiv ⟨z, by simp⟩ (m + 1)).symm
          (o.toHomologicalOrientation hE z)).val =
      (((trivializationAt E (TangentSpace I) z).mapOrientation (Fin (m + 1))
        (FiberBundle.mem_baseSet_trivializationAt' z)
        (o.toVectorBundleOrientation z)).localOrientation hE).val := by
  set φ : OpenPartialHomeomorph M E := (chartAt H z).transHomeomorph I.toHomeomorph
  set ν := (trivializationAt E (TangentSpace I) z).mapOrientation (Fin (m + 1))
    (FiberBundle.mem_baseSet_trivializationAt' z) (o.toVectorBundleOrientation z)
  -- A linear identification `L` of `E` with a Euclidean space, and the chart `φ'` it gives.
  have hF : finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1 := finrank_euclideanSpace_fin
  let L : E ≃L[ℝ] EuclideanSpace ℝ (Fin (m + 1)) :=
    ContinuousLinearEquiv.ofFinrankEq (hE.trans hF.symm)
  set φ' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (m + 1))) :=
    (chartAt H z).transHomeomorph (I.toHomeomorph.trans L.toHomeomorph)
  have hz' : z ∈ φ'.source := by simp [φ']
  -- The trivialization at `z` is the identity on the fibre at `z`.
  have hν : o.orientationAt z = ν := by
    simp only [ν, Trivialization.mapOrientation_apply, toVectorBundleOrientation_apply]
    have hid : (trivializationAt E (TangentSpace I) z).linearEquivAt ℝ z
        (FiberBundle.mem_baseSet_trivializationAt' z) = LinearEquiv.refl ℝ E :=
      LinearEquiv.ext fun v ↦ by
        rw [Trivialization.linearEquivAt_apply, ← Trivialization.continuousLinearMapAt_apply_of_mem
          ℝ _ (FiberBundle.mem_baseSet_trivializationAt' z)]
        exact continuousLinearMapAt_trivializationAt_self z v
    rw [hid]
    exact (congrFun (congrArg DFunLike.coe (Orientation.map_refl (Fin (m + 1)))) _).symm
  have h₁ : o.toHomologicalOrientation hE z =
      φ'.localOrientationOfOrientedChart hz' (ν.map (Fin (m + 1)) L.toLinearEquiv) hF := by
    rw [toHomologicalOrientation_apply]
    exact localOrientationOfManifoldOrientation_eq_localOrientationOfOrientedChart_transHomeomorph
      o hE z hν L hF
  -- The chart `φ'`, centred and followed by `L⁻¹`, carries this local orientation to `ν`.
  have h₂ := φ'.localHomologyMap_chart_localOrientationOfOrientedChart hz' L.symm
    (ν.map (Fin (m + 1)) L.toLinearEquiv) hF hE (by
      rintro x hx
      exact Subtype.ext (φ'.injOn x.property hz'
        (sub_eq_zero.1 (L.symm.map_eq_zero_iff.1 (by simpa using hx)))))
  rw [← h₁, show (ν.map (Fin (m + 1)) L.toLinearEquiv).map (Fin (m + 1)) L.symm.toLinearEquiv = ν
    from Orientation.map_symm_map L.toLinearEquiv ν] at h₂
  rw [← h₂]
  congr 3
  ext x
  -- The sources of `φ` and `φ'` are the same set only after unfolding `transHomeomorph`, so
  -- `rw` does not match the application lemmas.
  erw [ContinuousMap.comp_apply, ContinuousMap.comp_apply, φ'.sourceRestrict_apply]
  simp [φ']

end TauCeti.Manifold.Orientation
