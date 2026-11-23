/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-!
# Constant endomorphisms of the tangent bundle in tangent coordinates

On a manifold `M` modelled on `E`, a continuous linear endomorphism `J₀` of `E` gives the
constant family `y ↦ J₀` of endomorphisms of the tangent spaces `T_x M = E`. Read in the tangent
coordinates of the chart at a point `x₀`, this family is `J₀` at each point `x` of the chart's
source at which `J₀` commutes with the tangent coordinate change from the chart at `x₀` to the
chart at `x` (`inTangentCoordinates_const`).

The proof writes the reading by Mathlib's `inTangentCoordinates_eq` as a conjugate of `J₀` by
tangent coordinate changes, and cancels them with `tangentCoordChange_comp` and
`tangentCoordChange_self`. It follows that of the private lemma
`inTangentCoordinates_I_smul_id` of Tau Ceti's
`TauCeti/Geometry/Symplectic/Manifold/AlmostComplex/Basic.lean`, the case of multiplication by
`i` on a complex model space.
-/

public section

open scoped Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E H M : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I 1 M]

/-- Let `x` be in the source of the chart at `x₀`. If a continuous linear endomorphism `J₀` of the
model space commutes with the tangent coordinate change at `x` from the chart at `x₀` to the chart
at `x`, then the constant family `y ↦ J₀` of endomorphisms of the tangent spaces, read in the
tangent coordinates of the chart at `x₀`, is `J₀` at `x`. -/
theorem inTangentCoordinates_const (J₀ : E →L[𝕜] E) {x₀ x : M} (hx : x ∈ (chartAt H x₀).source)
    (h : ∀ v : E, tangentCoordChange I x x₀ x (J₀ v) = J₀ (tangentCoordChange I x x₀ x v)) :
    inTangentCoordinates I I id id
        (fun x : M ↦ (J₀ : TangentSpace I x →L[𝕜] TangentSpace I x)) x₀ x = J₀ := by
  refine (inTangentCoordinates_eq (I := I) (I' := I) id id _ hx hx).trans
    (ContinuousLinearMap.ext fun v ↦ ?_)
  have hx' : x ∈ (extChartAt I x₀).source ∩ (extChartAt I x).source ∩
      (extChartAt I x₀).source := by
    simp [hx]
  simp only [ContinuousLinearMap.comp_apply]
  exact (h _).trans
    (congrArg J₀ ((tangentCoordChange_comp hx').trans (tangentCoordChange_self (by simp [hx]))))

end
