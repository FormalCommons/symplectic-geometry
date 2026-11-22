/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.VectorBundle.Riemannian
public import TauCeti.Geometry.Manifold.DifferentialForm.AlmostComplexType
import SymplecticGeometry.Analysis.Normed.Module.Alternating.Derivation

/-!
# The real derivation of smooth forms along an endomorphism field, pointwise

Tau Ceti's `ContMDiffSection.realAlternatingDerivation` lets a smooth endomorphism field `A` of the
tangent bundle act on smooth real forms. This file identifies its value at each point with the
derivation `ContinuousAlternatingMap.fderivCompContinuousLinearMap` of the value of the form, at
the identity and in the direction `A x`. That derivation needs a norm on the tangent spaces,
which a `RiemannianBundle` metric supplies.

## Main results

* `ContMDiffSection.coe_realAlternatingDerivation`: the value of `𝒜 φ` at `x` is
  `(φ x).fderivCompContinuousLinearMap (id) (A x)`.
-/

public section

noncomputable section

open Bundle TauCeti
open scoped Manifold ContDiff

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] {k : ℕ}

namespace ContMDiffSection

/-- At each point, the real derivation of a smooth form along an endomorphism field `A` is the
derivation `ContinuousAlternatingMap.fderivCompContinuousLinearMap` of the value at the identity in
the direction `A x`. The metric only supplies the norm on the tangent spaces that
`fderivCompContinuousLinearMap` requires. -/
theorem coe_realAlternatingDerivation
    (A : ContMDiffSection I (E →L[ℝ] E) ∞ fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
    (φ : SmoothForm I M ℝ k) :
    (A.realAlternatingDerivation φ).val =
      fun x ↦ (φ.val x).fderivCompContinuousLinearMap (.id ℝ (TangentSpace I x)) (A x) := by
  ext x v
  rw [realAlternatingDerivation_apply,
    ContinuousAlternatingMap.fderivCompContinuousLinearMap_id_apply]

end ContMDiffSection

end
