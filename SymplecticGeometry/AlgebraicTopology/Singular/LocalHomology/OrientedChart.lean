/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Linear
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Chart
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Smooth
public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.Orientation.Smooth
import SymplecticGeometry.Topology.Algebra.Module.Equiv.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

/-!
# Local orientations of a manifold in its charts

This file reads the local orientations of an oriented `C¹` manifold `M`, modelled on a real normed
space `E` that need not carry an inner product, in a chart `ψ` at `z` with values in a real normed
space `F`, translated so that `z` goes to the origin. If `ψ`, read in the preferred chart of `M` at
`z`, has as derivative a linear identification `D` of `E` with `F`, the local orientation at `z`
becomes the local orientation of `F` at the origin selected by the image under `D` of the tangent
orientation at `z`. The preferred chart at `z` followed by `D` is such a chart; for `D` the
identity, the result is the local orientation of `E` selected by the orientation of the fibre at
`z`, read in the trivialization of the tangent bundle at `z`.

## Main results

* `TauCeti.Manifold.Orientation.localHomologyMap_sub_toHomologicalOrientation_of_hasFDerivAt`: a
  chart `ψ` of `M` at `z` whose derivative in the preferred chart at `z` is `D` carries the local
  orientation of `o.toHomologicalOrientation` at `z` to the local orientation of `F` at the origin
  selected by the image of `o` at `z` under `D`.
* `TauCeti.Manifold.Orientation.localHomologyMap_sub_toHomologicalOrientation_transHomeomorph`:
  the centered chart of `M` at `z` followed by `D` carries the local orientation of
  `o.toHomologicalOrientation` at `z` to the local orientation of `F` at the origin selected by
  the image of `o` at `z` under `D`.
* `TauCeti.Manifold.Orientation.localHomologyMap_sub_toHomologicalOrientation`: the case of the
  identity of `E`, with the orientation at `z` read in the trivialization of the tangent bundle.

## Implementation notes

For `TauCeti.Manifold.Orientation.localHomologyMap_sub_toHomologicalOrientation_of_hasFDerivAt`,
`ψ` is followed by a linear identification `L` of `F` with a Euclidean space;
`TauCeti.Manifold.Orientation.toHomologicalOrientation_apply_eq_localOrientationOfOrientedChart`
reads the local orientation of `M` in the resulting chart, whose derivative is `D` followed by `L`,
and `OpenPartialHomeomorph.localHomologyMap_chart_localOrientationOfOrientedChart`, from Tau Ceti's
`TauCeti/AlgebraicTopology/Singular/LocalHomology/Orientation/Linear.lean`, applied to that chart
and `L⁻¹`, carries it to `F`. The case of the preferred chart followed by `D` follows, since there
the derivative is `D`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.3 (local
  orientations).
-/

public section

noncomputable section

open TauCeti Module

namespace TauCeti.Manifold.Orientation

open Bundle

variable {E H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [ChartedSpace E M]
  [IsManifold I 1 M] {m : ℕ} (hE : finrank ℝ E = m + 1)
  (o : Manifold.Orientation I M (Fin (m + 1)))

/-- Let `ψ` be a chart of `M` at `z` with values in a real normed space `F`, and suppose that `ψ`,
read in the extended preferred chart of `M` at `z`, has at the image of `z` the derivative of a
linear equivalence `D : E ≃L[ℝ] F`. Then the map `x ↦ ψ x - ψ z` carries the local orientation
of `M` at `z` given by `o` to the local orientation of `F` at the origin selected by the image of
`o.orientationAt z` under `D`. -/
theorem localHomologyMap_sub_toHomologicalOrientation_of_hasFDerivAt {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (hF : finrank ℝ F = m + 1)
    (ψ : OpenPartialHomeomorph M F) {z : M} (hz : z ∈ ψ.source) {D : E ≃L[ℝ] F}
    (hD : HasFDerivAt (ψ ∘ (extChartAt I z).symm) (D : E →L[ℝ] F) (extChartAt I z z)) :
    localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ))
        (⟨fun x : ψ.source ↦ ψ x - ψ z, ψ.continuousOn.domRestrict.sub continuous_const⟩ :
          C(ψ.source, F))
        (S := {⟨z, hz⟩}) (T := {0})
        (by
          rintro x hx
          exact Subtype.ext (ψ.injOn x.property hz (sub_eq_zero.1 hx))) (m + 1)
        ((ψ.open_source.isOpenEmbedding_subtypeVal.localOrientationEquiv ⟨z, hz⟩ (m + 1)).symm
          (o.toHomologicalOrientation hE z)).val =
      (((o.orientationAt z).map (Fin (m + 1)) D.toLinearEquiv).localOrientation hF).val := by
  have : FiniteDimensional ℝ F := Module.finite_of_finrank_eq_succ hF
  set ν : _root_.Orientation ℝ E (Fin (m + 1)) := o.orientationAt z
  -- A linear identification `L` of `F` with a Euclidean space, and the chart it gives.
  have hF' : finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1 := finrank_euclideanSpace_fin
  let L : F ≃L[ℝ] EuclideanSpace ℝ (Fin (m + 1)) :=
    ContinuousLinearEquiv.ofFinrankEq (hF.trans hF'.symm)
  set ω := ν.map (Fin (m + 1)) (D.trans L).toLinearEquiv
  set χ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (m + 1))) :=
    ψ.transHomeomorph L.toHomeomorph
  have hzχ : z ∈ χ.source := by simpa [χ] using hz
  -- In the chart `χ`, whose derivative is `D` followed by `L`, `o` selects `ω`.
  have h₁ : o.toHomologicalOrientation hE z = χ.localOrientationOfOrientedChart hzχ ω hF' :=
    toHomologicalOrientation_apply_eq_localOrientationOfOrientedChart hE o hF' χ hzχ (D.trans L)
      (L.hasFDerivAt.comp _ hD) rfl
  -- The chart `χ`, centred and followed by `L⁻¹`, carries this local orientation to `D ν`.
  have h₂ := χ.localHomologyMap_chart_localOrientationOfOrientedChart hzχ L.symm ω hF' hF (by
      rintro x hx
      exact Subtype.ext (χ.injOn x.property hzχ
        (sub_eq_zero.1 (L.symm.map_eq_zero_iff.1 (by simpa using hx)))))
  have hν : ω.map (Fin (m + 1)) L.symm.toLinearEquiv = ν.map (Fin (m + 1)) D.toLinearEquiv := by
    simp only [ω, ContinuousLinearEquiv.trans_toLinearEquiv, Orientation.map_trans]
    exact Orientation.map_symm_map L.toLinearEquiv _
  rw [← h₁, hν] at h₂
  rw [← h₂]
  congr 3
  ext x
  -- The sources of `ψ` and `χ` are the same set only after unfolding `transHomeomorph`, so
  -- `rw` does not match the application lemmas.
  erw [ContinuousMap.comp_apply, ContinuousMap.comp_apply, χ.sourceRestrict_apply,
    ContinuousMap.coe_mk]
  simp [χ]

/-- In the chart `φ` of `M` at `z` followed by a linear identification `D` of the model `E` with a
real normed space `F`, the map `x ↦ φ x - φ z` carries the local orientation of `M` at `z` given by
`o` to the local orientation of `F` at the origin selected by the image of `o.orientationAt z`
under `D`. -/
theorem localHomologyMap_sub_toHomologicalOrientation_transHomeomorph {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (hF : finrank ℝ F = m + 1) (D : E ≃L[ℝ] F) (z : M) :
    localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ))
        (⟨fun x : ((chartAt H z).transHomeomorph (I.toHomeomorph.trans D.toHomeomorph)).source ↦
            (chartAt H z).transHomeomorph (I.toHomeomorph.trans D.toHomeomorph) x -
              (chartAt H z).transHomeomorph (I.toHomeomorph.trans D.toHomeomorph) z,
          ((chartAt H z).transHomeomorph
            (I.toHomeomorph.trans D.toHomeomorph)).continuousOn.domRestrict.sub
            continuous_const⟩ :
          C(((chartAt H z).transHomeomorph (I.toHomeomorph.trans D.toHomeomorph)).source, F))
        (S := {⟨z, by simp⟩}) (T := {0})
        (by
          rintro x hx
          exact Subtype.ext (((chartAt H z).transHomeomorph
            (I.toHomeomorph.trans D.toHomeomorph)).injOn x.property (by simp) (sub_eq_zero.1 hx)))
        (m + 1)
        ((((chartAt H z).transHomeomorph
          (I.toHomeomorph.trans D.toHomeomorph)).open_source.isOpenEmbedding_subtypeVal
          |>.localOrientationEquiv ⟨z, by simp⟩ (m + 1)).symm
          (o.toHomologicalOrientation hE z)).val =
      (((o.orientationAt z).map (Fin (m + 1)) D.toLinearEquiv).localOrientation hF).val := by
  refine localHomologyMap_sub_toHomologicalOrientation_of_hasFDerivAt hE o hF _ (by simp) ?_
  -- Read in the preferred chart, the chart followed by `D` is `D` near the point.
  refine D.hasFDerivAt.congr_of_eventuallyEq ?_
  filter_upwards [extChartAt_target_mem_nhds (I := I) z] with y hy
  simpa using congrArg D ((extChartAt I z).right_inv hy)

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
  -- The trivialization at `z` is the identity on the fibre at `z`.
  have hν : (o.orientationAt z).map (Fin (m + 1)) (ContinuousLinearEquiv.refl ℝ E).toLinearEquiv =
      (trivializationAt E (TangentSpace I) z).mapOrientation (Fin (m + 1))
        (FiberBundle.mem_baseSet_trivializationAt' z) (o.toVectorBundleOrientation z) := by
    simp only [Trivialization.mapOrientation_apply, toVectorBundleOrientation_apply]
    have hid : (trivializationAt E (TangentSpace I) z).linearEquivAt ℝ z
        (FiberBundle.mem_baseSet_trivializationAt' z) = LinearEquiv.refl ℝ E :=
      LinearEquiv.ext fun v ↦ by
        rw [Trivialization.linearEquivAt_apply, ← Trivialization.continuousLinearMapAt_apply_of_mem
          ℝ _ (FiberBundle.mem_baseSet_trivializationAt' z)]
        exact continuousLinearMapAt_trivializationAt_self z v
    rw [hid, ContinuousLinearEquiv.toLinearEquiv_refl]
    -- The two sides differ only in reading the tangent space at `z` as `E`.
    rfl
  rw [← hν, ← localHomologyMap_sub_toHomologicalOrientation_transHomeomorph hE o hE
    (ContinuousLinearEquiv.refl ℝ E) z]
  -- The chart followed by the identity of `E` is the chart, by definition of `Homeomorph.trans`;
  -- the proofs in the statement depend on the chart, so `rw` cannot replace it.
  congr 3

end TauCeti.Manifold.Orientation
