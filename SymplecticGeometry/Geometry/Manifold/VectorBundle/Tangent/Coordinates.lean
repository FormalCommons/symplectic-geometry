/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic

/-!
# Constant endomorphisms of the tangent bundle in tangent coordinates

On a manifold `M` modelled on `E`, a continuous linear endomorphism `J₀` of `E` gives the
constant family `y ↦ J₀` of endomorphisms of the tangent spaces `T_x M = E`. Read in the tangent
coordinates of the chart at a point `x₀`, this family is `J₀` at each point `x` of the chart's
source at which `J₀` commutes with the tangent coordinate change from the chart at `x` to the
chart at `x₀` (`inTangentCoordinates_const`).

The proof writes the reading by Mathlib's `inTangentCoordinates_eq` as a conjugate of `J₀` by
tangent coordinate changes, and cancels them with Tau Ceti's
`TauCeti.tangentCoordChange_tangentCoordChange`. It follows that of the private lemma
`inTangentCoordinates_I_smul_id` of Tau Ceti's
`TauCeti/Geometry/Symplectic/Manifold/AlmostComplex/Basic.lean`, the case of multiplication by
`i` on a complex model space.

For a family of maps from a model space into the tangent spaces, the coordinates on the source
play no role: in tangent coordinates the family is its composite with the tangent coordinate
changes of `M` (`inTangentCoordinates_eq_tangentCoordChange_comp`).
-/

public section

namespace SymplecticGeometry

open scoped Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E H M : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I 1 M]

/-- Let `x` be in the source of the chart at `x₀`. If a continuous linear endomorphism `J₀` of the
model space commutes with the tangent coordinate change at `x` from the chart at `x` to the chart
at `x₀`, then the constant family `y ↦ J₀` of endomorphisms of the tangent spaces, read in the
tangent coordinates of the chart at `x₀`, is `J₀` at `x`. -/
theorem inTangentCoordinates_const (J₀ : E →L[𝕜] E) {x₀ x : M} (hx : x ∈ (chartAt H x₀).source)
    (h : ∀ v : E, tangentCoordChange I x x₀ x (J₀ v) = J₀ (tangentCoordChange I x x₀ x v)) :
    inTangentCoordinates I I id id
        (fun x : M ↦ (J₀ : TangentSpace I x →L[𝕜] TangentSpace I x)) x₀ x = J₀ := by
  refine (inTangentCoordinates_eq (I := I) (I' := I) id id _ hx hx).trans
    (ContinuousLinearMap.ext fun v ↦ ?_)
  simp only [ContinuousLinearMap.comp_apply]
  exact (h _).trans
    (congrArg J₀ (TauCeti.tangentCoordChange_tangentCoordChange (by simp [hx]) (by simp) _))

/-- Read in the tangent coordinates at `x₀`, a family of maps `ϕ x` from a model space `G` into
the tangent spaces `T_(g x) M` is, at each `x` with `g x` in the source of the chart at `g x₀`,
the map `ϕ x` followed by the tangent coordinate change from the chart at `g x` to the chart at
`g x₀`. The coordinates on the model space `G` play no role. -/
theorem inTangentCoordinates_eq_tangentCoordChange_comp {G X : Type*} [NormedAddCommGroup G]
    [NormedSpace 𝕜 G] {f : X → G} {g : X → M} (ϕ : ∀ x, G →L[𝕜] TangentSpace I (g x))
    {x₀ x : X} (hx : g x ∈ (chartAt H (g x₀)).source) :
    inTangentCoordinates 𝓘(𝕜, G) I f g ϕ x₀ x =
      tangentCoordChange I (g x) (g x₀) (g x) ∘L ϕ x := by
  rw [inTangentCoordinates_eq f g ϕ (by simp) hx, tangentBundleCore_coordChange_model_space]
  -- The identity on the right is that of `TangentSpace 𝓘(𝕜, G) (f x)`, which is `G` only up to
  -- unfolding, so `ContinuousLinearMap.comp_id` does not rewrite it.
  rfl

end SymplecticGeometry

end
