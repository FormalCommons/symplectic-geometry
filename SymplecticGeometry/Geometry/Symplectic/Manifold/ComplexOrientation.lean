/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Orientation.ComplexStructure
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Symplectic.ComplexStructure.Basic
public import TauCeti.Geometry.Symplectic.Manifold.Volume
public import TauCeti.Topology.VectorBundle.Orientation.Complex.EulerClass
import SymplecticGeometry.Topology.VectorBundle.Orientation.Complex.Structure

/-!
# The symplectic orientation is the orientation of a tamed complex structure

Let `σ` be a nondegenerate smooth two-form on a manifold `M` of dimension `2 n`, and `J` a
complex structure on the tangent bundle of `M` tamed by `σ`: `σ(v, J v) > 0` for every nonzero
tangent vector `v`. Then every tangent space carries two orientations: the symplectic orientation
of `σ` (`TauCeti.SmoothTwoForm.IsNondegenerate.volumeOrientation`), and the complex orientation
of `J` (`TauCeti.Bundle.ContinuousComplexStructure.orientation`). They agree.

## Main results

All three are in the namespace `TauCeti.SmoothTwoForm`.

* `IsNondegenerate.orientation_eq_toVectorBundleOrientation_volumeOrientation`: the complex
  orientation of `J` on the tangent bundle is the symplectic orientation of `σ`.
* `IsNondegenerate.tangentOrientation_eq_volumeOrientation`: the same statement for the
  orientations of `M`, through `TauCeti.Bundle.ContinuousComplexStructure.tangentOrientation`.
* `IsNondegenerate.complexEulerClass_eq_eulerClass`: on a surface, the
  Euler class `TauCeti.complexEulerClass` of the complex line bundle `(TM, J)` is the Euler class
  of the tangent bundle oriented by the symplectic orientation of `σ`. It follows from
  `TauCeti.Bundle.ContinuousComplexStructure.complexEulerClass_eq_eulerClass` for `J` and the
  first result.

## Proof

At a point `x`, the symplectic orientation of `σ` is the orientation of the symplectic vector
space `(T_x M, σ_x)` (`TauCeti.SmoothTwoForm.IsNondegenerate.orientationAt_volumeOrientation`),
and the complex orientation of `J` is that of the almost complex structure `J_x`
(`TauCeti.Bundle.ContinuousComplexStructure.orientation_apply`). Since `σ_x` tames `J_x`, these
agree by Tau Ceti's linear statement `TauCeti.AlmostComplexStructure.orientation_eq_of_tames`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.5
  (complex structures tamed by a symplectic form).
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §14 (the canonical orientation of a complex vector space).
-/

public section

open Bundle Module SymplecticGeometry.Bundle
open scoped Manifold ContDiff

namespace TauCeti.SmoothTwoForm

section Orientation

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {σ : SmoothTwoForm I M} {m : ℕ∞}
  {J : ContMDiffComplexStructure I m E (TangentSpace I : M → Type _)} {n : ℕ}

/-- **A tamed complex structure induces the symplectic orientation.** Let `σ` be a nondegenerate
smooth two-form on a manifold of dimension `2 n`, and `J` a complex structure on the tangent
bundle, of any regularity, tamed by `σ`. Then the complex orientation of `J` on the tangent
bundle is the symplectic orientation of `σ`. -/
theorem IsNondegenerate.orientation_eq_toVectorBundleOrientation_volumeOrientation
    (h : σ.IsNondegenerate) (hE : finrank ℝ E = 2 * n)
    (hJ : (ContMDiffTwoForm.tangentEquiv.symm σ).Tames J) :
    J.toContinuousComplexStructure.orientation hE =
      (h.volumeOrientation hE).toVectorBundleOrientation := by
  ext x
  rw [Manifold.Orientation.toVectorBundleOrientation_apply,
    h.orientationAt_volumeOrientation, Bundle.ContinuousComplexStructure.orientation_apply]
  refine AlmostComplexStructure.orientation_eq_of_tames (fun v hv ↦ ?_) _
  simpa [ContMDiffComplexStructure.toContinuousComplexStructure_apply] using hJ.apply_pos hv

/-- **A tamed complex structure orients a manifold as the symplectic form does.** Let `σ` be a
nondegenerate smooth two-form on a manifold `M` of dimension `2 n`, and `J` a complex structure
on the tangent bundle, of any regularity, tamed by `σ`. Then the orientation of `M` given by `J`
is the symplectic orientation of `σ`. -/
theorem IsNondegenerate.tangentOrientation_eq_volumeOrientation (h : σ.IsNondegenerate)
    (hE : finrank ℝ E = 2 * n) (hJ : (ContMDiffTwoForm.tangentEquiv.symm σ).Tames J) :
    J.toContinuousComplexStructure.tangentOrientation hE = h.volumeOrientation hE := by
  ext x
  rw [← Manifold.Orientation.toVectorBundleOrientation_apply,
    Bundle.ContinuousComplexStructure.toVectorBundleOrientation_tangentOrientation,
    h.orientation_eq_toVectorBundleOrientation_volumeOrientation hE hJ,
    Manifold.Orientation.toVectorBundleOrientation_apply]

end Orientation

section EulerClass

/-! Euler classes need the base and the fibres in `Type`. -/

variable {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {σ : SmoothTwoForm I M} {m : ℕ∞}
  {J : ContMDiffComplexStructure I m E (TangentSpace I : M → Type)}
  [Fact (finrank ℝ E = 2 * finrank ℂ ℂ)]

open scoped VectorBundle.ComplexToReal

/-- **The Euler class of a tamed complex structure on a surface.** Let `σ` be a nondegenerate
smooth two-form on a manifold `M` modelled on a plane, and `J` a complex structure on the tangent
bundle, of any regularity, tamed by `σ`. Then the Euler class of the complex line bundle
`(TM, J)` is the Euler class of the tangent bundle oriented by the symplectic orientation of
`σ`. -/
theorem IsNondegenerate.complexEulerClass_eq_eulerClass (h : σ.IsNondegenerate)
    (hE : finrank ℝ E = 2) (hJ : (ContMDiffTwoForm.tangentEquiv.symm σ).Tames J) :
    complexEulerClass ℂ J.toContinuousComplexStructure.Fiber (r := 0) (finrank_self ℂ) =
      (h.volumeOrientation (n := 1) hE).toVectorBundleOrientation.eulerClass hE := by
  rw [J.toContinuousComplexStructure.complexEulerClass_eq_eulerClass ℂ hE,
    h.orientation_eq_toVectorBundleOrientation_volumeOrientation (n := 1) hE hJ]

end EulerClass

end TauCeti.SmoothTwoForm

end
