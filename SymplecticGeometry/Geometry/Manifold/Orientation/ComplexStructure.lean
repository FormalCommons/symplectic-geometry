/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.ContMDiff
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.ComplexTangentBundle
public import TauCeti.Geometry.Symplectic.Manifold.Orientation
public import TauCeti.Topology.VectorBundle.Complex.Orientation

/-!
# The orientation of a manifold given by a complex structure on its tangent bundle

A continuous complex structure `J` on the tangent bundle of a manifold `M` (Tau Ceti's
`TauCeti.Bundle.ContinuousComplexStructure`) orients each tangent space by its complex
orientation `J.orientation`, and so orients `M`
(`TauCeti.Manifold.Orientation.ofVectorBundleOrientation`).

* `TauCeti.Bundle.ContinuousComplexStructure.tangentOrientation`: that orientation of `M`, with
  `TauCeti.Bundle.ContinuousComplexStructure.tangentOrientation_def`;
* `TauCeti.Bundle.ContinuousComplexStructure.toVectorBundleOrientation_tangentOrientation`: its
  tangent orientations are those of `J.orientation`;
* `TauCeti.SmoothAlmostComplexStructure.orientation_eq_tangentOrientation`: for a smooth almost
  complex structure, Tau Ceti's `TauCeti.SmoothAlmostComplexStructure.orientation` is this
  orientation of the underlying continuous structure.

## Proof

Tau Ceti's `TauCeti.SmoothAlmostComplexStructure.orientation` is defined by the same term as
`tangentOrientation`, but its body is not exposed to other modules, so
`TauCeti.SmoothAlmostComplexStructure.orientation_eq_tangentOrientation` compares the two
orientations at each point, adapting the proof of Tau Ceti's
`TauCeti.SmoothAlmostComplexStructure.orientationAt_orientation`.
-/

public section

open Bundle Module
open scoped Manifold ContDiff

namespace TauCeti.Bundle.ContinuousComplexStructure

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  (J : ContinuousComplexStructure E (TangentSpace I : M → Type _)) {k : ℕ}

/-- **The orientation of a manifold given by a complex structure on its tangent bundle.** A
continuous complex structure `J` on the tangent bundle of `M`, with `finrank ℝ E = k`, orients
`M`: this is the orientation of `M` whose tangent orientation at each point is the complex
orientation `J.orientation hk` of the tangent space there. -/
noncomputable def tangentOrientation (hk : finrank ℝ E = k) : Manifold.Orientation I M (Fin k) :=
  Manifold.Orientation.ofVectorBundleOrientation (finBasisOfFinrankEq ℝ E hk).orientation
    ((Fintype.card_fin k).trans hk.symm) (J.orientation hk)

theorem tangentOrientation_def (hk : finrank ℝ E = k) :
    J.tangentOrientation hk =
      Manifold.Orientation.ofVectorBundleOrientation (finBasisOfFinrankEq ℝ E hk).orientation
        ((Fintype.card_fin k).trans hk.symm) (J.orientation hk) :=
  (rfl)

/-- The tangent bundle orientation of `J.tangentOrientation hk` is the complex orientation
`J.orientation hk`. -/
@[simp]
theorem toVectorBundleOrientation_tangentOrientation (hk : finrank ℝ E = k) :
    (J.tangentOrientation hk).toVectorBundleOrientation = J.orientation hk := by
  rw [tangentOrientation_def,
    Manifold.Orientation.toVectorBundleOrientation_ofVectorBundleOrientation]

end TauCeti.Bundle.ContinuousComplexStructure

namespace TauCeti.SmoothAlmostComplexStructure

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- For a smooth almost complex structure `J` on `M`, Tau Ceti's complex orientation
`J.orientation hk` is `tangentOrientation` of `J` seen as a continuous complex structure on the
tangent bundle. -/
theorem orientation_eq_tangentOrientation (J : SmoothAlmostComplexStructure I M) {k : ℕ}
    (hk : finrank ℝ E = k) :
    J.orientation hk = (J.toContMDiff 0).toContinuousComplexStructure.tangentOrientation hk := by
  ext x
  rw [orientationAt_orientation, ← Manifold.Orientation.toVectorBundleOrientation_apply,
    Bundle.ContinuousComplexStructure.toVectorBundleOrientation_tangentOrientation,
    Bundle.ContinuousComplexStructure.orientation_apply,
    ContMDiffAlmostComplexStructure.toContinuousComplexStructure_almostComplexStructureAt,
    almostComplexStructureAt_toContMDiff]

end TauCeti.SmoothAlmostComplexStructure

end
