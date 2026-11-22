/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Smooth

/-!
# Local orientations of a smooth orientation, read in any chart

Tau Ceti's `TauCeti.Manifold.Orientation.toHomologicalOrientation` turns an orientation `o` of a
`C¹` manifold `M` with a boundaryless model `I` into a homological orientation, whose local
orientation at `x` is read in the preferred chart at `x`. This file reads it in an arbitrary chart
`χ` at `x` with values in a real inner product space `F`: if `D` is the derivative at `x` of `χ`
read in the extended preferred chart, then the local orientation of `o` at `x` is the one that `χ`
selects for the image of the tangent orientation of `o` at `x` under `D`.

## Main results

* `TauCeti.Manifold.Orientation.toHomologicalOrientation_apply_eq_localOrientationOfOrientedChart`.

## Implementation notes

The proof is the change of chart of Tau Ceti's
`TauCeti.complexHomologicalOrientation_apply_of_mem_maximalAtlas`: it compares `χ` with the
preferred chart followed by `D`
(`TauCeti.localOrientationOfManifoldOrientation_eq_localOrientationOfOrientedChart_transHomeomorph`)
by `OpenPartialHomeomorph.coe_localOrientationOfOrientedChart_eq_sign_det_smul`, for a transition
map whose derivative is the identity.
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

end TauCeti.Manifold.Orientation

end
