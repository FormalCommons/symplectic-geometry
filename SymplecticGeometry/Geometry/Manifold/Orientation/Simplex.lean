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
public import TauCeti.Geometry.Manifold.Complex.Orientation
public import TauCeti.Geometry.Manifold.SmoothSingular.Basic
public import SymplecticGeometry.LinearAlgebra.Complex.Finrank
import SymplecticGeometry.Analysis.Normed.Module.Ball.Homeomorph
import SymplecticGeometry.Geometry.Convex.FullSimplex
import SymplecticGeometry.Geometry.Manifold.Complex.Orientation
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.Basic
import SymplecticGeometry.Geometry.Manifold.Orientation.AddCircle
import SymplecticGeometry.Geometry.Manifold.Orientation.Preserving
import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.UnivBall
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

For `0 < b` and `a < b` there is also a single smooth open embedding `g : ℝᵖ → ℝᵖ`, orientation
preserving everywhere, with image in the open ball of radius `b` and with `g (interior Δᵖ)`
containing the closed ball of radius `a`
(`TauCeti.Manifold.Orientation.exists_isOpenEmbedding_isOrientationPreservingAt_fullSimplex_ball`).
For `p = 2` no affine map does this when `b ≤ 2a`: a triangle in the ball of radius `b` has
inradius at most `b / 2`. So `g` is Mathlib's diffeomorphism `OpenPartialHomeomorph.univBall 0 b`
of `ℝᵖ` onto that ball, after a homothety that blows a ball inside `interior Δᵖ` up past the
compact preimage of the closed ball of radius `a`; it preserves orientation everywhere
(`OpenPartialHomeomorph.isOrientationPreservingAt_univBall_of_pos`). Read in `ℂ` through
`Complex.orthonormalBasisOneI.repr.symm`, it gives a smooth `2`-simplex of `ℂ`, positively
oriented for the complex orientation, whose faces avoid the closed disc of radius `a`
(`TauCeti.Manifold.Orientation.exists_smoothSimplex_complex_closedBall_subset_image`).

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
  · exact ((φ.symm.contMDiffAt (hA y hy)).comp y
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

namespace TauCeti.Manifold.Orientation

open Metric

/-- **A positively oriented simplex covering a disc inside a larger ball.** For `0 < b` and
`a < b`, there is a smooth open embedding `g : ℝᵖ → ℝᵖ`, orientation preserving at every point
for the standard orientation of `ℝᵖ`, whose image lies in the open ball of radius `b` about `0`
and maps the interior of the standard simplex `Δᵖ` onto a set containing the closed ball of
radius `a` about `0`. -/
theorem exists_isOpenEmbedding_isOrientationPreservingAt_fullSimplex_ball {p : ℕ} {a b : ℝ}
    (hb : 0 < b) (hab : a < b) :
    ∃ g : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p), ContDiff ℝ ∞ g ∧
      IsOpenEmbedding g ∧
      (∀ y, IsOrientationPreservingAt (euclideanSpace p) (euclideanSpace p) g y) ∧
      closedBall 0 a ⊆ g '' interior (fullSimplex p) ∧ range g ⊆ ball 0 b := by
  set F := OpenPartialHomeomorph.univBall (0 : EuclideanSpace ℝ (Fin p)) b
  have hFs : F.source = univ := OpenPartialHomeomorph.univBall_source _ _
  have hFt : F.target = ball 0 b := OpenPartialHomeomorph.univBall_target _ hb
  -- The preimage of the closed disc of radius `a` is compact, so inside a ball of radius `R`.
  have hK : IsCompact (F.symm '' closedBall 0 a) :=
    (isCompact_closedBall 0 a).image_of_continuousOn
      ((OpenPartialHomeomorph.continuousOn_univBall_symm 0 b).mono (closedBall_subset_ball hab))
  obtain ⟨R, hR, hKR⟩ := hK.isBounded.subset_ball_lt 0 0
  -- Blow a ball `B(p₀, δ) ⊆ interior Δᵖ` up onto `B(0, R)` by `A y = c • (y - p₀)`.
  obtain ⟨p₀, hp₀⟩ := nonempty_interior_fullSimplex p
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 isOpen_interior p₀ hp₀
  set c := R / δ
  have hc : 0 < c := div_pos hR hδ
  set A : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p) := fun y ↦ c • (y - p₀) with hAdef
  have hAd (y : EuclideanSpace ℝ (Fin p)) :
      HasFDerivAt A (c • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin p))) y :=
    ((hasFDerivAt_id y).sub_const p₀).const_smul c
  let T : EuclideanSpace ℝ (Fin p) ≃ₜ EuclideanSpace ℝ (Fin p) :=
    (Homeomorph.subRight p₀).trans (Homeomorph.smulOfNeZero c hc.ne')
  refine ⟨F ∘ A, OpenPartialHomeomorph.contDiff_univBall.comp
      ((contDiff_id.sub contDiff_const).const_smul c),
    (F.isOpenEmbedding hFs).comp T.isOpenEmbedding, fun y ↦
      (OpenPartialHomeomorph.isOrientationPreservingAt_univBall_of_pos hb _ (A y)).comp ?_, ?_, ?_⟩
  · refine isOrientationPreservingAt_of_det_fderiv_pos _ ?_
    rw [(hAd y).fderiv, ContinuousLinearMap.det_smul, ContinuousLinearMap.det_id, mul_one]
    positivity
  · intro w hw
    have hz : F.symm w ∈ ball (0 : EuclideanSpace ℝ (Fin p)) R := hKR ⟨w, hw, rfl⟩
    refine ⟨p₀ + c⁻¹ • F.symm w, hball ?_, ?_⟩
    · rw [mem_ball_zero_iff] at hz
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg
        (inv_nonneg.2 hc.le)]
      calc c⁻¹ * ‖F.symm w‖ < c⁻¹ * R := by gcongr
        _ = δ := by rw [inv_mul_eq_div, div_div_cancel₀ hR.ne']
    · simp only [Function.comp_apply, hAdef, add_sub_cancel_left, smul_inv_smul₀ hc.ne']
      exact F.right_inv (hFt ▸ closedBall_subset_ball hab hw)
  · exact (range_comp_subset_range _ _).trans (OpenPartialHomeomorph.range_univBall 0 hb).le

/-- **A positively oriented smooth `2`-simplex of `ℂ` around a disc.** For `0 < b` and `a < b`,
there are a smooth `2`-simplex `τ` of `ℂ` and a smooth open embedding `g : ℝ² → ℂ` restricting to
`τ` on `Δ²`, orientation preserving at every point from the standard orientation of `ℝ²` to the
complex orientation of `ℂ`, such that `g (interior Δ²)` contains the closed disc of radius `a`
about `0`, every face of `τ` misses that disc, and the image of `g` lies in the open disc of
radius `b` about `0`. -/
theorem exists_smoothSimplex_complex_closedBall_subset_image {a b : ℝ} (hb : 0 < b)
    (hab : a < b) :
    ∃ (g : EuclideanSpace ℝ (Fin 2) → ℂ) (τ : SmoothSimplex 𝓘(ℝ, ℂ) ℂ 2),
      (∀ x : fullSimplex 2, g x = τ.toContinuousMap x) ∧ ContDiff ℝ ∞ g ∧ IsOpenEmbedding g ∧
      (∀ y, IsOrientationPreservingAt (euclideanSpace 2)
        ((complexManifoldOrientation ℂ ℂ).reindex (finCongr Complex.two_mul_finrank_self)) g y) ∧
      closedBall 0 a ⊆ g '' interior (fullSimplex 2) ∧
      (∀ (i : Fin 3) (x : fullSimplex 1), τ.toContinuousMap (simplexFace 1 i x) ∉ closedBall 0 a) ∧
      range g ⊆ ball 0 b := by
  obtain ⟨g, hgs, hge, hgo, hga, hgb⟩ :=
    exists_isOpenEmbedding_isOrientationPreservingAt_fullSimplex_ball (p := 2) hb hab
  set L := Complex.orthonormalBasisOneI.repr.symm
  have hO : (complexManifoldOrientation ℂ ℂ).reindex (finCongr Complex.two_mul_finrank_self) =
      complex :=
    (SymplecticGeometry.complexCurveOrientation_def _).symm.trans
      SymplecticGeometry.complexCurveOrientation_complex
  have hs : ContDiff ℝ ∞ (L ∘ g) := L.contDiff.comp hgs
  have he : IsOpenEmbedding (L ∘ g) := L.toHomeomorph.isOpenEmbedding.comp hge
  have hdisc : closedBall 0 a ⊆ (L ∘ g) '' interior (fullSimplex 2) := by
    intro w hw
    obtain ⟨y, hy, hyw⟩ := hga (show L.symm w ∈ closedBall 0 a by simpa using hw)
    exact ⟨y, hy, by simp [hyw]⟩
  refine ⟨L ∘ g, SmoothSimplex.ofContMDiff hs.contMDiff, fun x ↦ by simp, hs, he, fun y ↦ ?_,
    hdisc, fun i x hx ↦ ?_, ?_⟩
  · rw [hO]
    exact (Complex.isOrientationPreservingAt_orthonormalBasisOneI_repr_symm (g y)).comp (hgo y)
  · -- A face point of `Δ²` is not in its interior, and `L ∘ g` is injective.
    rw [SmoothSimplex.toContinuousMap_ofContMDiff_apply] at hx
    obtain ⟨y, hy, hyx⟩ := hdisc hx
    exact simplexFace_coe_notMem_interior i x (he.injective hyx ▸ hy)
  · rintro _ ⟨y, rfl⟩
    simpa using hgb ⟨y, rfl⟩

end TauCeti.Manifold.Orientation

end
