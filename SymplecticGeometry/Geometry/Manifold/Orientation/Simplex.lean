/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Real
public import TauCeti.Geometry.Convex.FullSimplex
public import TauCeti.Geometry.Manifold.Orientation.Euclidean
public import TauCeti.Geometry.Manifold.Orientation.Preserving
import SymplecticGeometry.Geometry.Manifold.Orientation.Preserving
import TauCeti.Geometry.Manifold.Orientation.Chart
import TauCeti.Topology.Algebra.Module.Determinant
import TauCeti.Topology.OpenPartialHomeomorph.Constructions

/-!
# Positively oriented simplices in an oriented manifold

Every point `x` of an oriented smooth manifold `C` of positive dimension `p` lies in the image of
the interior of the standard simplex `Δᵖ ⊆ ℝᵖ` (Tau Ceti's `fullSimplex p`) under a map
`g : ℝᵖ → C` that, on an open neighbourhood of `Δᵖ`, is smooth, an open embedding, and orientation
preserving from the standard orientation of `ℝᵖ`
(`TauCeti.Manifold.Orientation.exists_isOpenEmbedding_isOrientationPreservingAt_fullSimplex`).

The map is the inverse of an oriented chart at `x`, from Tau Ceti's
`TauCeti.Manifold.Orientation.exists_partialDiffeomorph_isOrientationPreservingAt`, composed with
a homothety of positive ratio that moves a small copy of `Δᵖ` into the chart's target.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 15.
-/

public section

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

namespace TauCeti.Manifold.Orientation

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {C : Type*} [TopologicalSpace C] [ChartedSpace E' C] [IsManifold 𝓘(ℝ, E') ∞ C]
  {p : ℕ} [NeZero p]


/-- **Positively oriented simplices.** Every point `x` of a smooth manifold of positive dimension
`p`, oriented by `o`, lies in the image of the interior of the standard simplex `Δᵖ` under a map
`g : ℝᵖ → C` which, on an open neighbourhood `U` of `Δᵖ`, is smooth, an open embedding, and
orientation preserving from the standard orientation of `ℝᵖ` to `o`. -/
theorem exists_isOpenEmbedding_isOrientationPreservingAt_fullSimplex
    (o : Manifold.Orientation 𝓘(ℝ, E') C (Fin p)) (x : C) :
    ∃ (U : Opens (EuclideanSpace ℝ (Fin p))) (g : EuclideanSpace ℝ (Fin p) → C),
      fullSimplex p ⊆ U ∧ ContMDiffOn (𝓡 p) 𝓘(ℝ, E') ∞ g U ∧
      IsOpenEmbedding (g ∘ ((↑) : U → EuclideanSpace ℝ (Fin p))) ∧
      (∀ y ∈ U, IsOrientationPreservingAt (euclideanSpace p) o g y) ∧
      x ∈ g '' interior (fullSimplex p) := by
  -- An oriented chart `φ : C → ℝᵖ` at `x`; its inverse preserves orientation on its target.
  obtain ⟨φ, hxφ, -, hφo⟩ := o.exists_partialDiffeomorph_isOrientationPreservingAt
    (n := ∞) (euclideanSpace p) isOpen_univ (mem_univ x)
  have hsymm (z) (hz : z ∈ φ.target) : IsOrientationPreservingAt (euclideanSpace p) o φ.symm z :=
    (hφo _ (φ.map_target hz)).partialDiffeomorph_symm hz (by simp)
  -- A ball about `φ x` inside the target of `φ`.
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 φ.open_target (φ x) (φ.map_source hxφ)
  -- Shrink `Δᵖ` into that ball by `A y = φ x + ε • (y - p₀)` around an interior point `p₀`.
  obtain ⟨p₀, hp₀⟩ := nonempty_interior_fullSimplex p
  obtain ⟨R, hR, hsub⟩ := (isCompact_fullSimplex p).isBounded.subset_ball_lt 0 p₀
  set ε := r / R
  have hε : 0 < ε := div_pos hr hR
  set A : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p) := fun y ↦ φ x + ε • (y - p₀)
    with hAdef
  have hA (y) (hy : y ∈ Metric.ball p₀ R) : A y ∈ φ.target := by
    refine hball ?_
    rw [Metric.mem_ball, hAdef, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg hε.le]
    rw [Metric.mem_ball, dist_eq_norm] at hy
    calc ε * ‖y - p₀‖ < ε * R := by gcongr
      _ = r := div_mul_cancel₀ r hR.ne'
  have hAd (y : EuclideanSpace ℝ (Fin p)) :
      HasFDerivAt A (ε • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin p))) y :=
    (((hasFDerivAt_id y).sub_const p₀).const_smul ε).const_add (φ x)
  let T : EuclideanSpace ℝ (Fin p) ≃ₜ EuclideanSpace ℝ (Fin p) := (Homeomorph.subRight p₀).trans
    ((Homeomorph.smulOfNeZero ε hε.ne').trans (Homeomorph.addLeft (φ x)))
  refine ⟨⟨Metric.ball p₀ R, Metric.isOpen_ball⟩, φ.symm ∘ A, hsub, fun y hy ↦ ?_, ?_,
    fun y hy ↦ ?_, ⟨p₀, hp₀, by simpa [A] using φ.left_inv hxφ⟩⟩
  · exact ((φ.symm.contMDiffOn.contMDiffAt (φ.open_target.mem_nhds (hA y hy))).comp y
      (contDiff_const.add
        ((contDiff_id.sub contDiff_const).const_smul ε)).contMDiff.contMDiffAt).contMDiffWithinAt
  · -- On the ball, `φ.symm ∘ A` is the inverse of `φ` after the affine homeomorphism `T`.
    refine φ.symm.toOpenPartialHomeomorph.isOpenEmbedding_comp
      (g := T ∘ ((↑) : Metric.ball p₀ R → _))
      (T.isOpenEmbedding.comp Metric.isOpen_ball.isOpenEmbedding_subtypeVal) ?_
    rintro _ ⟨y, rfl⟩
    exact hA y y.prop
  · refine (hsymm _ (hA y hy)).comp (isOrientationPreservingAt_of_det_fderiv_pos _ ?_)
    rw [(hAd y).fderiv, ContinuousLinearMap.det_smul, ContinuousLinearMap.det_id, mul_one]
    positivity

end TauCeti.Manifold.Orientation

end
