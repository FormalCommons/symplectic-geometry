/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.LocalIndex
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Smooth
public import TauCeti.Geometry.Manifold.Degree.Homological

/-!
# Local orientations of a smooth orientation

Tau Ceti's `TauCeti.Manifold.Orientation.toHomologicalOrientation` turns an orientation `o` of a
`C¹` manifold `M` with a boundaryless model `I` into a homological orientation, whose local
orientation at `x` is read in the preferred chart at `x`. This file reads it in an arbitrary chart
`χ` at `x` with values in a real inner product space `F`: if `D` is the derivative at `x` of `χ`
read in the extended preferred chart, then the local orientation of `o` at `x` is the one that `χ`
selects for the image of the tangent orientation of `o` at `x` under `D`.

It also shows that a continuous map `f : M → N` that preserves orientation at `x`, the only point
of its fibre, carries the local orientation of `o` at `x` to that of `o'` at `f x`, through the
map that `f` itself induces on local homology.

## Main results

* `TauCeti.Manifold.Orientation.toHomologicalOrientation_apply_eq_localOrientationOfOrientedChart`.
* `TauCeti.Manifold.Orientation.localHomologyMap_toHomologicalOrientation`: orientation-preserving
  maps carry local orientations to local orientations.

## Implementation notes

The proof of the first result is the change of chart of Tau Ceti's
`TauCeti.complexHomologicalOrientation_apply_of_mem_maximalAtlas`: it compares `χ` with the
preferred chart followed by `D`
(`TauCeti.localOrientationOfManifoldOrientation_eq_localOrientationOfOrientedChart_transHomeomorph`)
by `OpenPartialHomeomorph.coe_localOrientationOfOrientedChart_eq_sign_det_smul`, for a transition
map whose derivative is the identity.

The proof of `TauCeti.Manifold.Orientation.localHomologyMap_toHomologicalOrientation` reads Tau
Ceti's `TauCeti.Manifold.Orientation.localIndex_toHomologicalOrientation`, a local index of `1`,
on the whole source by `TauCeti.HomologicalOrientation.localIndex_eq_iff_of_preimage_subset`,
which `SymplecticGeometry/AlgebraicTopology/Singular/LocalHomology/LocalIndex.lean` copies from
Tau Ceti's main branch.
-/

public section

universe w v

open Module
open scoped Manifold

namespace TauCeti.Manifold.Orientation

variable {M E F : Type w} {H : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I 1 M] [ChartedSpace E M]
  {n : ℕ} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **The local orientations of a smooth orientation, read in any chart.** Let `χ` be a chart of
`M` at `x` with values in an inner product space `F`, and `D` the derivative at `x` of `χ` read
in the extended preferred chart at `x`. Then the local orientation of `o` at `x` is the one
selected in `χ` by the image of the tangent orientation `o.orientationAt x` under `D`. -/
theorem toHomologicalOrientation_apply_eq_localOrientationOfOrientedChart
    (hE : finrank ℝ E = n + 1) (o : Manifold.Orientation I M (Fin (n + 1)))
    (hF : finrank ℝ F = n + 1) (χ : OpenPartialHomeomorph M F) {x : M} (hx : x ∈ χ.source)
    (D : E ≃L[ℝ] F)
    (hD : HasFDerivAt (χ ∘ (extChartAt I x).symm) (D : E →L[ℝ] F) (extChartAt I x x))
    {ω : _root_.Orientation ℝ F (Fin (n + 1))}
    (hω : (o.orientationAt x).map (Fin (n + 1)) D.toLinearEquiv = ω) :
    o.toHomologicalOrientation hE x = χ.localOrientationOfOrientedChart hx ω hF := by
  have : FiniteDimensional ℝ F := Module.finite_of_finrank_eq_succ hF
  -- The preferred chart at `x` followed by `D`, in which `o` selects its local orientation.
  let φ := (chartAt H x).transHomeomorph (I.toHomeomorph.trans D.toHomeomorph)
  have hxφ : x ∈ φ.source := by simp [φ]
  -- The transition from `φ` to `χ` has derivative the identity at `φ x`.
  have hd : HasFDerivAt (χ ∘ φ.symm) (ContinuousLinearMap.id ℝ F) (φ x) := by
    have h1 : D.symm (φ x) = extChartAt I x x := by simp [φ]
    convert HasFDerivAt.comp (φ x) (h1.symm ▸ hD) D.symm.hasFDerivAt using 1
    · ext y
      simp [φ, extChartAt]
    · ext y
      simp
  rw [toHomologicalOrientation_apply,
    localOrientationOfManifoldOrientation_eq_localOrientationOfOrientedChart_transHomeomorph
      o hE x rfl D hF hxφ, hω]
  have hdet : (ContinuousLinearMap.id ℝ F).det = 1 := LinearMap.det_id
  apply Subtype.ext
  rw [OpenPartialHomeomorph.coe_localOrientationOfOrientedChart_eq_sign_det_smul _ _ φ χ hxφ hx
    hd (hdet ▸ one_ne_zero), hdet, sign_one, SignType.coe_one, one_smul]


section LocalHomologyMap

variable {M N E F : Type} {H H' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'} [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [ChartedSpace E M] [T2Space M] [IsManifold I 1 M]
  [TopologicalSpace N] [ChartedSpace H' N] [ChartedSpace F N] [T2Space N] [IsManifold J 1 N]
  {n : ℕ} (hE : finrank ℝ E = n + 1) (hF : finrank ℝ F = n + 1)
  {o : Manifold.Orientation I M (Fin (n + 1))} {o' : Manifold.Orientation J N (Fin (n + 1))}

/-- **Orientation-preserving maps carry local orientations to local orientations.** Let
`f : M → N` be continuous and preserve the orientations `o` and `o'` at `x`, the only point of
its fibre through `x`. Then the map of local homology `Hₙ₊₁(M, M ∖ {x}) ⟶ Hₙ₊₁(N, N ∖ {f x})`
induced by `f` carries the local orientation of `o` at `x` to that of `o'` at `f x`. -/
theorem localHomologyMap_toHomologicalOrientation (f : C(M, N)) {x : M}
    (hfx : f ⁻¹' {f x} ⊆ {x}) (hf : IsOrientationPreservingAt o o' f x) :
    localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) f hfx (n + 1)
        (o.toHomologicalOrientation hE x).val =
      (o'.toHomologicalOrientation hF (f x)).val := by
  have hi := localIndex_toHomologicalOrientation hE hF o o' f hf.isInvertible_mfderiv
  rw [orientationSign_of_isOrientationPreservingAt hf] at hi
  simpa using (HomologicalOrientation.localIndex_eq_iff_of_preimage_subset _ _ hF f rfl hfx).1 hi

end LocalHomologyMap
end TauCeti.Manifold.Orientation

end
