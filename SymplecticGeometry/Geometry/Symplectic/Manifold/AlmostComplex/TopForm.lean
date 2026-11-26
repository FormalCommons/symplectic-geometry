/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.IsManifold.Basic
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Basic
import SymplecticGeometry.LinearAlgebra.Complex.TopForm

/-!
# Top forms on the tangent planes of an almost complex surface

Take a manifold `C` modelled on a real plane, with an almost complex structure `j`. For a
nonzero tangent vector `e`, the pair `(e, j e)` is a basis of the tangent plane. So a top form on
that plane is determined by its value on `(e, j e)`
(`TauCeti.SmoothAlmostComplexStructure.topForm_ext`), and the ratio of two top forms takes the
same value on every such pair (`TauCeti.SmoothAlmostComplexStructure.topForm_apply_div_apply_eq`).
Neither statement needs an orientation of `C`. Both are the statements of
`SymplecticGeometry.LinearAlgebra.Complex.TopForm` for the complex structure `j c` on the tangent
plane at `c`, read for continuous alternating maps.

## References

* [D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*][McDuffSalamon2012],
  §2.2.
-/

public section

open Module
open scoped Manifold ContDiff

noncomputable section

namespace TauCeti

namespace SmoothAlmostComplexStructure

variable {E H C : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace C] [ChartedSpace H C] [IsManifold I ∞ C]
  (j : SmoothAlmostComplexStructure I C) {c : C}

/-- On a surface, two top forms on a tangent plane that agree on one pair `(e, j e)` with
`e ≠ 0` are equal. -/
theorem topForm_ext (h2 : finrank ℝ E = 2) {e : TangentSpace I c} (he : e ≠ 0)
    {η μ : TangentSpace I c [⋀^Fin 2]→L[ℝ] ℝ} (h : η ![e, j c e] = μ ![e, j c e]) : η = μ := by
  refine ContinuousAlternatingMap.toAlternatingMap_injective <|
    (j.almostComplexStructureAt c).alternatingMap_ext h2 he ?_
  simpa only [ContinuousAlternatingMap.coe_toAlternatingMap, almostComplexStructureAt_apply]
    using h

/-- On a surface, the ratio of two top forms on a tangent plane takes the same value on all pairs
`(e, j e)` with `e ≠ 0`. -/
theorem topForm_apply_div_apply_eq (h2 : finrank ℝ E = 2) {e e' : TangentSpace I c} (he : e ≠ 0)
    (he' : e' ≠ 0) (η μ : TangentSpace I c [⋀^Fin 2]→L[ℝ] ℝ) :
    η ![e', j c e'] / μ ![e', j c e'] = η ![e, j c e] / μ ![e, j c e] := by
  simpa only [ContinuousAlternatingMap.coe_toAlternatingMap, almostComplexStructureAt_apply] using
    (j.almostComplexStructureAt c).alternatingMap_apply_div_apply_eq h2 he he' η.toAlternatingMap
      μ.toAlternatingMap

end SmoothAlmostComplexStructure

end TauCeti
