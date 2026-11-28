/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Riemannian.Basic
public import SymplecticGeometry.Geometry.Manifold.FiberBundle.Principal.CircleConnection
public import SymplecticGeometry.Geometry.Symplectic.AsymptoticallyHolomorphic.ModelConnection
public import SymplecticGeometry.Geometry.Symplectic.AsymptoticallyHolomorphic.RescaledDist
public import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.TransAffine
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Chart
import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.Chart
import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.TransAffine
import SymplecticGeometry.Geometry.Symplectic.Manifold.Darboux
import SymplecticGeometry.LinearAlgebra.Symplectic.UnitaryNormalForm
import SymplecticGeometry.Analysis.Normed.Module.Ball.Pointwise
import SymplecticGeometry.Geometry.Manifold.FiberBundle.Principal.LocalSection
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.Basic
import SymplecticGeometry.Geometry.Manifold.Riemannian.Distance
import SymplecticGeometry.Geometry.Symplectic.Liouville.RadialPrimitive
import SymplecticGeometry.Topology.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Order.Star.Real
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Smooth

/-!
# Centred Darboux charts with uniform bounds, their rescalings, and rescaled unitary charts

Let `σ` be a two-form on a boundaryless manifold `M`, `J` a smooth almost complex structure
compatible with `σ`, and `φ` a smooth chart of `M` into the standard model `StdSpace ι` that pulls
the standard form `stdForm ι` back to `σ`. For a compact set `K` in the source of `φ`, this file
recentres `φ` at every point `x ∈ K`: the chart at `x` is `φ` followed by `z ↦ A x (z - φ x)`,
where `(A x)⁻¹` is a unitary normal form of the structure `J` read in `φ` at `φ x`. The new chart
sends `x` to `0`, still pulls `stdForm ι` back to `σ`, and reads `J` at `0` as the standard complex
structure. One radius `ρ > 0` works for all `x ∈ K`: the ball of radius `ρ` about `0` lies in the
target of each of these charts, and for each `r` one constant bounds the `r`-th derivatives of `J`
read in all of them on that ball.

The uniformity comes from two inputs: the uniform bound on the normal forms,
`SymplecticGeometry.exists_forall_isSymplectomorphism_stdForm_norm_le`, applied to the structures
`φ.pushforwardAt J` on the compact set `φ '' K`; and the radius and derivative bounds that
`SmoothAlmostComplexStructure.exists_forall_norm_iteratedFDeriv_chartPushforward_transAffine_le`
gives for any family of recentred charts whose linear parts are bounded with their inverses.

On a compact manifold of dimension `2 * card ι` with `σ` closed, the structure
`CenteredDarbouxCharts σ J ι` collects such charts centred at every point, with one radius and one
bound for each order of derivative. They exist: Darboux charts into `StdSpace ι` at every point
(`TauCeti.SmoothTwoForm.IsSymplectic.exists_darbouxChart_stdForm`) give compact neighbourhoods of
every point on which the recentred charts have uniform bounds, finitely many of these cover `M`,
and the smallest of their radii and the largest of their bounds work for all centres. Taking each
Darboux chart with source inside a given neighbourhood `U p` of its point `p` puts the source of
every centred chart inside one of the sets `U p`.

Rescaling a centred chart `D.chart x` by a nonzero real `c`, that is, following it by
`z ↦ c • z`, gives the chart `D.rescaledChart c x`. It is still centred at `x`, its target contains
the ball of radius `|c| * D.radius`, and it pulls `stdForm ι` back to `c ^ 2` times `σ`. The
structure `J` read in it at `z` is `J` read in `D.chart x` at `c⁻¹ • z`, so each derivative of
order `r` gains a factor `|c|⁻¹ ^ r`. With the mean value inequality and the value
`stdComplexStructure ι` at `0`, this bounds the distance from `J` read in the rescaled chart to
`stdComplexStructure ι` by a constant times `|c|⁻¹ * ‖z‖`, the constant not depending on `x` or
`c`. For `c = √(2π k)` the rescaled chart pulls `stdForm ι` back to `k` times `2π σ`.

Over a chart `χ` that pulls `stdForm ι` back to `σ`, a principal `Circle`-bundle with a connection
form `α` of curvature `-2π σ` has, over any open star-convex subset `s` of the target, a section
in which `α` read in `χ` is the model form `stdConnectionForm ι` of
`AsymptoticallyHolomorphic/ModelConnection.lean`. Starting from a section `τ₀` smooth on the
image `χ⁻¹ '' s`, the reading of `τ₀^* α` in `χ` has exterior derivative `-2π ω₀` on `s`, since the
curvature is `d (τ₀^* α)` and the inverse of `χ` pulls `σ` back to `ω₀`
(`TauCeti.SmoothTwoForm.mpullback_symm_apply_eq_constSmooth`). The gauge lemma
`SymplecticGeometry.exists_contDiffOn_add_mextDeriv_eq_stdConnectionForm` gives `θ` on `s` with
that reading plus `dθ` equal to the model, and rotating `τ₀` by `exp (i θ ∘ χ)` adds `d (θ ∘ χ)`
to `τ₀^* α`
(`SymplecticGeometry.IsCircleConnectionForm.mpullback_apply_op_circleExp_smul_eq_mextDeriv_add`).

The structure `RescaledUnitaryCharts P σ J α ι k₀ ρ₀` collects, for every power `k ≥ k₀` and
every point `x`, a chart centred at `x` whose target contains the ball of radius `ρ₀ * √k`, which
pulls `stdForm ι` back to `2π k σ`, and a section of `P` over the image of that ball in which `k`
times the pull-back of `α`, read in the chart, is `-λ₀`, for `λ₀ = (stdForm ι).radialPrimitive`
the radial primitive `λ₀(z)(v) = ω₀(z, v) / 2` of `ω₀`, so that its exterior derivative is `-ω₀`
(`TauCeti.SymplecticForm.mextDeriv_radialPrimitive`). On that ball, `J` read in these charts
differs from `stdComplexStructure ι` by at most a constant times `k^{-1/2} ‖z‖` at `z`, and its
derivatives of order `r ≥ 1` are `O(k^{-1/2})`, with constants that do not depend on `k` or `x`.
They exist on a compact manifold (`SymplecticGeometry.exists_rescaledUnitaryCharts`): take centred
Darboux charts whose sources lie in base sets of trivializations of `P`, rescale them by
`√(2π k)`, and rotate the preferred local sections of `P` into frames with the model connection
form over the balls of radius `D.radius`. The frames do not depend on `k`, since rescaling the
chart by `c` multiplies the model form read in it by `c⁻²`
(`SymplecticGeometry.CenteredDarbouxCharts.mpullback_rescaledChart_symm_apply` and
`TauCeti.SymplecticForm.mpullback_const_smul_radialPrimitive`, in
`SymplecticGeometry.Geometry.Symplectic.Liouville.RadialPrimitive`). The construction follows
Auroux's local normalization of the charts for `k Ω` [Auroux2002, Lemma 1].

In these charts the quadratic form `2π k σ(v, J v)`, which for `J` compatible with `σ` is `2π k`
times the square of the `g_J`-norm of `v`, is close to `‖u‖ ^ 2`, `u` the image of `v` under the
derivative of the chart: since `ω₀(u, J₀ u) = ‖u‖ ^ 2`, the two differ by at most
`bound 1 * ‖z‖ / √k * ‖u‖ ^ 2` at a point with image `z`, so on the ball of radius `ρ₁ * √k`, for
`ρ₁ ≤ ρ₀` with `|bound 1| * ρ₁ ≤ 1 / 2`, the form lies between `‖u‖ ^ 2 / 2` and `3 / 2 * ‖u‖ ^ 2`.

With the metric `g_J` installed on `M`, the upper half of this comparison bounds distances from
the centre: for `z` in the ball of radius `ρ₁ * √k`, the image under the inverse of the chart of
the segment from `0` to `z` has `g_J`-speed at most `√(3 / 2) * ‖z‖ / √(2π k)`, so
`√(2π k)` times the Riemannian distance from `x` to the inverse image of `z` is at most
`√(3 / 2) * ‖z‖` (`Manifold.riemannianEDist_le_of_norm_mfderiv_le`). The speed bound holds for
every direction, not only `z`
(`SymplecticGeometry.RescaledUnitaryCharts.mul_norm_mfderiv_symm_le`).

For the lower half, let `d_k = √(2π k) · d_{g_J}` (`SymplecticGeometry.rescaledEDist`, and
`SymplecticGeometry.rescaledDist` as a real number). On the same ball, the differential of each
chart stretches `g_J`-norms by at most `√2 * √(2π k)`
(`SymplecticGeometry.RescaledUnitaryCharts.norm_mvfderiv_le_mul`), so
`‖z‖ / √2 ≤ d_k(x, (D.chart k x).symm z)`
(`SymplecticGeometry.RescaledUnitaryCharts.ofReal_mul_norm_le_rescaledEDist_symm`,
from `PartialDiffeomorph.ofReal_norm_sub_le_mul_riemannianEDist`). Each of these bounds is stated
for one `k`, one point `x` and a radius `ρ₁` on which the comparison above holds in
`D.chart k x` (`SymplecticGeometry.RescaledUnitaryCharts.IsComparisonRadius`), with `ρ₁ ≤ ρ₀`
where the ball must lie in the target of the chart. Together the two halves give the two-sided
bound `‖z‖ / √2 ≤ d_k(x, (D.chart k x).symm z) ≤ √(3 / 2) * ‖z‖`
(`SymplecticGeometry.RescaledUnitaryCharts.rescaledEDist_symm_mem_Icc`).
Conversely, a point `y` that is not `(D.chart k x).symm z` for any `z` in that ball has
`ρ₁ * √k / √2 ≤ d_k(x, y)`, since a path from `x` to `y` must leave the ball, and the same
stretching bound makes the part of it inside the ball long
(`SymplecticGeometry.RescaledUnitaryCharts.ofReal_le_rescaledEDist_of_notMem`,
from `PartialDiffeomorph.ofReal_le_mul_riemannianEDist_of_notMem`). So every `y` with
`d_k(x, y) < R ≤ ρ₁ * √k / √2` is `(D.chart k x).symm z` for some `z` with `‖z‖ < √2 * R`.

## Main definitions

* `SymplecticGeometry.CenteredDarbouxCharts`: centred Darboux charts at every point of `M`, with
  derivative at the centre complex linear for `J`, one radius, and uniform bounds on the
  derivatives of `J` read in them.
* `SymplecticGeometry.CenteredDarbouxCharts.rescaledChart`: the centred chart at a point followed by
  the scaling by a unit `c : ℝˣ`.
* `SymplecticGeometry.RescaledUnitaryCharts`: for every large power `k` and every point, a chart
  centred there, rescaled so that it pulls `stdForm ι` back to `2π k σ`, with a frame of `P` in
  which the connection form read in the chart is the model, and bounds on `J` read in it.
* `SymplecticGeometry.RescaledUnitaryCharts.IsComparisonRadius`: a radius `ρ₁` such that, at
  every point of the source of `D.chart k x` whose image lies in the ball of radius `ρ₁ * √k`,
  `2π k σ(v, J v)` lies between `‖u‖ ^ 2 / 2` and `3 / 2 * ‖u‖ ^ 2` for every tangent vector
  `v`, `u` the image of `v` under the derivative of the chart.

## Main results

* `SymplecticGeometry.exists_transAffine_darbouxCharts_of_isCompact`: the recentred charts on a
  compact subset of the source of one Darboux chart, with the uniform radius and the uniform
  bounds.
* `SymplecticGeometry.exists_centeredDarbouxCharts_source_subset`: centred Darboux charts with
  uniform bounds whose sources lie in the sets of a given family of neighbourhoods.
* `SymplecticGeometry.nonempty_centeredDarbouxCharts`: centred Darboux charts with uniform bounds
  exist on a compact manifold.
* `SymplecticGeometry.CenteredDarbouxCharts.eval₂_rescaledChart`: the rescaled chart pulls
  `stdForm ι` back to `c ^ 2` times `σ`.
* `SymplecticGeometry.CenteredDarbouxCharts.chartPushforward_rescaledChart`: `J` read in the
  rescaled chart, as `J` read in the centred chart at the scaled point.
* `SymplecticGeometry.CenteredDarbouxCharts.norm_chartPushforward_rescaledChart_sub_le`,
  `SymplecticGeometry.CenteredDarbouxCharts.norm_iteratedFDeriv_chartPushforward_rescaledChart_le`
  and its corollary for `c ≥ 1` and `r ≥ 1`: the bounds on `J` read in the rescaled charts.
* `SymplecticGeometry.IsCircleConnectionForm.exists_mpullback_symm_mpullback_eq_stdConnectionForm`:
  over an open star-convex subset of the target of a Darboux chart, a section of the circle bundle
  in which the connection form read in the chart is the model.
* `SymplecticGeometry.exists_rescaledUnitaryCharts`: rescaled unitary charts exist on a compact
  manifold with a two-form `σ`, a compatible almost complex structure, and a connection form
  of curvature `-2π σ`.
* `SymplecticGeometry.RescaledUnitaryCharts.abs_eval₂_apply_sub_norm_sq_le` and
  `SymplecticGeometry.RescaledUnitaryCharts.exists_forall_isComparisonRadius`: `2π k σ(v, J v)`
  is `‖u‖ ^ 2` up to `bound 1 * ‖z‖ / √k * ‖u‖ ^ 2`, `u` the image of `v` in the chart, and some
  `ρ₁ ≤ ρ₀` is a comparison radius for every `k ≥ k₀` and every point.
* `SymplecticGeometry.RescaledUnitaryCharts.sqrt_eval₂_apply_le`: hence
  `√(σ(v, J v)) ≤ (2π k)^(-1/2) (1 + max (bound 1) 0 * ‖z‖ / √k) ‖u‖` on the ball of radius
  `ρ₀ * √k`.
* `SymplecticGeometry.RescaledUnitaryCharts.mul_norm_mfderiv_symm_le` and
  `SymplecticGeometry.RescaledUnitaryCharts.norm_mvfderiv_le_mul`: for the metric `g_J` and a
  comparison radius `ρ₁` for `D.chart k x` (with `ρ₁ ≤ ρ₀` for the first), on the
  ball of radius `ρ₁ * √k` the derivative of the inverse of each
  chart has operator norm at most `√(3 / 2) / √(2π k)`, and that of the chart at most
  `√2 * √(2π k)`.
* `SymplecticGeometry.RescaledUnitaryCharts.rescaledEDist_symm_symm_le` and
  `SymplecticGeometry.RescaledUnitaryCharts.rescaledEDist_symm_le`:
  for the metric `g_J`, `√(2π k)` times the distance between the points with images `a` and `b`
  is at most `√(3 / 2) * ‖a - b‖` on a ball of radius `ρ₁ * √k`; in particular, that from the
  centre `x` to the point with image `z` is at most `√(3 / 2) * ‖z‖`.
* `SymplecticGeometry.RescaledUnitaryCharts.ofReal_mul_norm_le_rescaledEDist_symm`:
  on a ball of radius `ρ₁ * √k`, `‖z‖ / √2` is at most the rescaled distance `d_k` from `x` to
  the point with image `z`.
* `SymplecticGeometry.RescaledUnitaryCharts.rescaledEDist_symm_mem_Icc`:
  the two bounds together, on the same ball of radius `ρ₁ * √k`: `d_k` from `x` to the point with
  image `z` lies between `‖z‖ / √2` and `√(3 / 2) * ‖z‖`; its two halves as real inequalities,
  `RescaledUnitaryCharts.norm_le_sqrt_two_mul_rescaledDist_symm` and
  `RescaledUnitaryCharts.rescaledDist_symm_le`.
* `SymplecticGeometry.RescaledUnitaryCharts.ofReal_le_rescaledEDist_of_notMem` and
  `SymplecticGeometry.RescaledUnitaryCharts.exists_norm_lt_symm_eq_of_rescaledEDist_lt`:
  the points outside the image of the ball of radius `ρ₁ * √k` are at rescaled distance at least
  `ρ₁ * √k / √2` from `x`, so the points at rescaled distance less than `R ≤ ρ₁ * √k / √2` are
  images of points of norm less than `√2 * R`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Sections 2.5, 2.7, 3.2 and 7.4.
* [S. K. Donaldson, *Symplectic submanifolds and almost-complex geometry*][Donaldson1996].
* [D. Auroux, *A remark about Donaldson's construction of symplectic submanifolds*][Auroux2002],
  Lemma 1.
-/

public section

open scoped Manifold ContDiff Topology
open TauCeti TauCeti.SymplecticForm Metric

namespace SymplecticGeometry

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {ι : Type*} [Fintype ι]
/-- **Recentred Darboux charts on a compact set, with uniform bounds.** Let `J` be a smooth almost
complex structure compatible with the two-form `σ` on a boundaryless manifold `M`, and `φ` a
smooth chart of `M` into `StdSpace ι` that pulls `stdForm ι` back to `σ`. Let `K` be a compact
subset of the source of `φ`. Then there are linear symplectomorphisms `A x` of
`(StdSpace ι, stdForm ι)`, for `x : M`, with `‖A x‖` and `‖(A x)⁻¹‖` bounded on `K`, and a
radius `ρ > 0`, such that for every `x ∈ K` the chart `ψ x := φ.transAffine (φ x) (A x)`, which
is `φ` followed by `z ↦ A x (z - φ x)`,
* contains `x` in its source and sends it to `0`;
* contains the ball of radius `ρ` about `0` in its target;
* pulls `stdForm ι` back to `σ` on its source;
* reads `J` at `0` as `stdComplexStructure ι`;

and for every `r` the `r`-th iterated derivatives of `J` read in the charts `ψ x` are bounded on
that ball, uniformly in `x ∈ K`. -/
theorem exists_transAffine_darbouxCharts_of_isCompact {σ : SmoothTwoForm I M}
    {J : SmoothAlmostComplexStructure I M} (hJ : σ.Compatible J)
    (φ : PartialDiffeomorph I 𝓘(ℝ, StdSpace ι) M (StdSpace ι) ∞)
    (hφ : ∀ x ∈ φ.source, ∀ v w : TangentSpace I x,
      σ.eval₂ x v w = stdForm ι (mvfderiv I φ x v) (mvfderiv I φ x w))
    {K : Set M} (hK : IsCompact K) (hKφ : K ⊆ φ.source) :
    ∃ A : M → StdSpace ι ≃L[ℝ] StdSpace ι, ∃ C₀ : ℝ, ∃ ρ > 0,
      (∀ x ∈ K,
        IsSymplectomorphism (stdForm ι) (stdForm ι) (A x).toLinearEquiv ∧
        ‖(A x : StdSpace ι →L[ℝ] StdSpace ι)‖ ≤ C₀ ∧
        ‖((A x).symm : StdSpace ι →L[ℝ] StdSpace ι)‖ ≤ C₀ ∧
        x ∈ (φ.transAffine (φ x) (A x)).source ∧ φ.transAffine (φ x) (A x) x = 0 ∧
        ball 0 ρ ⊆ (φ.transAffine (φ x) (A x)).target ∧
        (∀ y ∈ (φ.transAffine (φ x) (A x)).source, ∀ v w : TangentSpace I y,
          σ.eval₂ y v w = stdForm ι (mvfderiv I (φ.transAffine (φ x) (A x)) y v)
            (mvfderiv I (φ.transAffine (φ x) (A x)) y w)) ∧
        ∀ w, J.chartPushforward (φ.transAffine (φ x) (A x)).toOpenPartialHomeomorph 0 w =
          stdComplexStructure ι w) ∧
      ∀ r : ℕ, ∃ C, ∀ x ∈ K, ∀ z ∈ ball (0 : StdSpace ι) ρ,
        ‖iteratedFDeriv ℝ r (J.chartPushforward (φ.transAffine (φ x) (A x)).toOpenPartialHomeomorph)
          z‖ ≤ C := by
  classical
  -- Unitary normal forms of `J` read in `φ`, with norms bounded on `φ '' K`.
  have hLt : φ '' K ⊆ φ.target := Set.image_subset_iff.2 fun x hx ↦ φ.map_source (hKφ hx)
  have hLX : IsCompact ((↑) ⁻¹' (φ '' K) : Set φ.target) := by
    rw [Subtype.isCompact_iff, Subtype.image_preimage_coe, Set.inter_eq_right.2 hLt]
    exact hK.image_of_continuousOn (φ.contMDiffOn.continuousOn.mono hKφ)
  obtain ⟨C₁, hC₁⟩ := exists_forall_isSymplectomorphism_stdForm_norm_le
    (J := fun p : φ.target ↦ φ.pushforwardAt J p.property) finrank_stdSpace hLX
    (φ.continuous_toContinuousLinearMap_pushforwardAt J).continuousOn
    fun p _ ↦ hJ.compatible_pushforwardAt φ hφ p.property
  have hex (x : M) : ∃ Ψ : StdSpace ι ≃L[ℝ] StdSpace ι, x ∈ K →
      IsSymplectomorphism (stdForm ι) (stdForm ι) Ψ.toLinearEquiv ∧
      (∀ w, Ψ (stdComplexStructure ι w) =
        J.chartPushforward φ.toOpenPartialHomeomorph (φ x) (Ψ w)) ∧
      ‖(Ψ : StdSpace ι →L[ℝ] StdSpace ι)‖ ≤ C₁ ∧
      ‖(Ψ.symm : StdSpace ι →L[ℝ] StdSpace ι)‖ ≤ C₁ := by
    by_cases hx : x ∈ K
    · obtain ⟨Ψ, h₁, h₂, h₃, h₄⟩ := hC₁ ⟨φ x, φ.map_source (hKφ hx)⟩ (Set.mem_image_of_mem φ hx)
      refine ⟨Ψ, fun _ ↦ ⟨h₁, fun w ↦ ?_, h₃, h₄⟩⟩
      exact (LinearMap.congr_fun h₂ w).trans
        (φ.pushforwardAt_apply_eq_chartPushforward_apply J _ (Ψ w))
    · exact ⟨ContinuousLinearEquiv.refl ℝ _, fun h ↦ absurd h hx⟩
  choose Ψ hΨ using hex
  -- The radius and the derivative bounds, from the bounds on `Ψ x` and its inverse.
  obtain ⟨ρ, hρ, hball, hbound⟩ :=
    J.exists_forall_norm_iteratedFDeriv_chartPushforward_transAffine_le φ hK hKφ
      (fun x ↦ (Ψ x).symm) (C := C₁) fun x hx ↦ by
        simpa only [ContinuousLinearEquiv.symm_symm] using ⟨(hΨ x hx).2.2.2, (hΨ x hx).2.2.1⟩
  refine ⟨fun x ↦ (Ψ x).symm, C₁, ρ, hρ, fun x hx ↦ ?_, hbound⟩
  obtain ⟨h₁, h₂, h₃, h₄⟩ := hΨ x hx
  have hA : IsSymplectomorphism (stdForm ι) (stdForm ι) (Ψ x).symm.toLinearEquiv := by
    rw [ContinuousLinearEquiv.toLinearEquiv_symm]
    exact h₁.symm
  refine ⟨hA, h₄, by rwa [ContinuousLinearEquiv.symm_symm], by simpa using hKφ hx, by simp,
    hball x hx, fun y hy v w ↦
      SmoothTwoForm.transAffine_darbouxChart hφ (φ x) hA y (by simpa using hy) v w, fun w ↦ ?_⟩
  rw [J.chartPushforward_transAffine φ _ _ (hball x hx (mem_ball_self hρ))]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_symm, map_zero, zero_add, ← h₂,
    ContinuousLinearEquiv.symm_apply_apply]

/-- Centred Darboux charts with uniform bounds on `M`, for a two-form `σ` and an almost complex
structure `J`: for every point `x`, a chart `chart x` of `M` into `StdSpace ι` that sends `x` to
`0`, pulls `stdForm ι` back to `σ` on its source, and reads `J` at `0` as `stdComplexStructure ι`,
that is, whose derivative at `x` is complex linear from `J` to `stdComplexStructure ι`. One radius
works for every centre: the ball of that radius about `0` lies in the target of every chart, and
on it the `r`-th iterated derivatives of `J` read in any of the charts are at most `bound r`. -/
@[ext]
structure CenteredDarbouxCharts (σ : SmoothTwoForm I M) (J : SmoothAlmostComplexStructure I M)
    (ι : Type*) [Fintype ι] where
  /-- The chart centred at a point. -/
  chart : M → PartialDiffeomorph I 𝓘(ℝ, StdSpace ι) M (StdSpace ι) ∞
  /-- The radius of a ball about `0` in the target of every chart. -/
  radius : ℝ
  /-- The bound on the `r`-th iterated derivatives of `J` read in the charts. -/
  bound : ℕ → ℝ
  radius_pos : 0 < radius
  mem_source (x : M) : x ∈ (chart x).source
  apply_self (x : M) : chart x x = 0
  ball_subset_target (x : M) : ball 0 radius ⊆ (chart x).target
  eval₂_eq (x : M) : ∀ y ∈ (chart x).source, ∀ v w : TangentSpace I y,
    σ.eval₂ y v w = stdForm ι (mvfderiv I (chart x) y v) (mvfderiv I (chart x) y w)
  chartPushforward_zero (x : M) (w : StdSpace ι) :
    J.chartPushforward (chart x).toOpenPartialHomeomorph 0 w = stdComplexStructure ι w
  norm_iteratedFDeriv_le (r : ℕ) (x : M) : ∀ z ∈ ball (0 : StdSpace ι) radius,
    ‖iteratedFDeriv ℝ r (J.chartPushforward (chart x).toOpenPartialHomeomorph) z‖ ≤ bound r

/-- **Centred Darboux charts with sources in given neighbourhoods.** On a compact boundaryless
manifold `M` of dimension `2 * card ι`, with a closed two-form `σ` and a smooth almost complex
structure `J` compatible with `σ`, let `U x` be a neighbourhood of each point `x`. Then there
are centred Darboux charts `D` into `StdSpace ι` with one radius and uniform bounds on the
derivatives of `J` read in them, and a map `c : M → M` such that the source of the chart centred
at `x` lies in `U (c x)` for every `x`. -/
theorem exists_centeredDarbouxCharts_source_subset [FiniteDimensional ℝ E] [CompactSpace M]
    (hE : Module.finrank ℝ E = 2 * Fintype.card ι) {σ : SmoothTwoForm I M} (hσ : σ.IsClosed)
    {J : SmoothAlmostComplexStructure I M} (hJ : σ.Compatible J) {U : M → Set M}
    (hU : ∀ x, U x ∈ 𝓝 x) :
    ∃ (D : CenteredDarbouxCharts σ J ι) (c : M → M), ∀ x, (D.chart x).source ⊆ U (c x) := by
  classical
  have := Manifold.locallyCompact_of_finiteDimensional (M := M) I
  -- A Darboux chart `φ p` at every point `p`, with source in `U p`, and a compact neighbourhood
  -- `K p` of `p` in its source, on which the charts recentred from `φ p` have uniform bounds.
  choose φ hpφ hφU _ hφ using fun p ↦
    SmoothTwoForm.IsSymplectic.exists_darbouxChart_stdForm hE ⟨hσ, hJ.isNondegenerate⟩ (hU p)
  choose K hK hpK hKφ using fun p ↦ exists_compact_subset (φ p).open_source (hpφ p)
  choose A C₀ ρ hρ hA hC using fun p ↦
    exists_transAffine_darbouxCharts_of_isCompact hJ (φ p) (hφ p) (hK p) (hKφ p)
  choose C hC using hC
  -- Finitely many of the `K p` cover `M`.
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun p ↦ interior (K p))
    (fun _ ↦ isOpen_interior) fun p _ ↦ Set.mem_iUnion.2 ⟨p, hpK p⟩
  have hcov (x : M) : ∃ p ∈ t, x ∈ K p := by
    obtain ⟨p, hp, hx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    exact ⟨p, hp, interior_subset hx⟩
  choose c hct hcK using hcov
  -- The smallest radius and the largest bounds over `t`.
  set ρ₀ := (insert 1 (t.image ρ)).min' (Finset.insert_nonempty _ _)
  have hρ₀ : 0 < ρ₀ := by
    rw [Finset.lt_min'_iff]
    simp only [Finset.mem_insert, Finset.mem_image]
    rintro _ (rfl | ⟨p, -, rfl⟩)
    exacts [one_pos, hρ p]
  have hρ₀le (x : M) : ball (0 : StdSpace ι) ρ₀ ⊆ ball 0 (ρ (c x)) :=
    ball_subset_ball <| Finset.min'_le _ _ <|
      Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (hct x))
  choose B hB using fun r ↦ (t.image fun p ↦ C p r).bddAbove
  refine ⟨{
    chart x := (φ (c x)).transAffine (φ (c x) x) (A (c x) x)
    radius := ρ₀
    bound := B
    radius_pos := hρ₀
    mem_source x := (hA _ x (hcK x)).2.2.2.1
    apply_self x := (hA _ x (hcK x)).2.2.2.2.1
    ball_subset_target x := (hρ₀le x).trans (hA _ x (hcK x)).2.2.2.2.2.1
    eval₂_eq x := (hA _ x (hcK x)).2.2.2.2.2.2.1
    chartPushforward_zero x := (hA _ x (hcK x)).2.2.2.2.2.2.2
    norm_iteratedFDeriv_le r x z hz := (hC _ r x (hcK x) z (hρ₀le x hz)).trans
      (hB r (Finset.mem_image_of_mem _ (hct x))) }, c, fun x ↦ ?_⟩
  rw [PartialDiffeomorph.transAffine_source]
  exact hφU (c x)

/-- **Centred Darboux charts with uniform bounds.** On a compact boundaryless manifold `M` of
dimension `2 * card ι`, with a closed two-form `σ` and a smooth almost complex structure `J`
compatible with `σ`, there are centred Darboux charts into `StdSpace ι` with one radius and
uniform bounds on the derivatives of `J` read in them. -/
theorem nonempty_centeredDarbouxCharts [FiniteDimensional ℝ E] [CompactSpace M]
    (hE : Module.finrank ℝ E = 2 * Fintype.card ι) {σ : SmoothTwoForm I M} (hσ : σ.IsClosed)
    {J : SmoothAlmostComplexStructure I M} (hJ : σ.Compatible J) :
    Nonempty (CenteredDarbouxCharts σ J ι) :=
  let ⟨D, _⟩ := exists_centeredDarbouxCharts_source_subset hE hσ hJ (U := fun _ ↦ Set.univ)
    fun _ ↦ Filter.univ_mem
  ⟨D⟩

namespace CenteredDarbouxCharts

omit [I.Boundaryless]

variable {σ : SmoothTwoForm I M} {J : SmoothAlmostComplexStructure I M}
  (D : CenteredDarbouxCharts σ J ι) (c : ℝˣ) (x : M)

/-- On a nonempty manifold, each bound of centred Darboux charts is nonnegative, since it bounds
a norm. -/
theorem bound_nonneg [Nonempty M] (r : ℕ) : 0 ≤ D.bound r :=
  (norm_nonneg _).trans
    (D.norm_iteratedFDeriv_le r (Classical.arbitrary M) 0 (mem_ball_self D.radius_pos))

/-- The centred chart at `x` rescaled by `c`: the chart `D.chart x` followed by `z ↦ c • z`. -/
noncomputable def rescaledChart : PartialDiffeomorph I 𝓘(ℝ, StdSpace ι) M (StdSpace ι) ∞ :=
  (D.chart x).transAffine 0 (ContinuousLinearEquiv.smulLeft c)

theorem rescaledChart_def :
    D.rescaledChart c x = (D.chart x).transAffine 0 (ContinuousLinearEquiv.smulLeft c) :=
  (rfl)

@[simp]
theorem rescaledChart_source : (D.rescaledChart c x).source = (D.chart x).source := by
  rw [rescaledChart_def, PartialDiffeomorph.transAffine_source]

theorem mem_rescaledChart_source : x ∈ (D.rescaledChart c x).source := by
  simpa using D.mem_source x

@[simp]
theorem rescaledChart_apply (y : M) : D.rescaledChart c x y = (c : ℝ) • D.chart x y := by
  simp [rescaledChart_def, Units.smul_def]

theorem rescaledChart_apply_self : D.rescaledChart c x x = 0 := by
  simp [D.apply_self x]

theorem rescaledChart_symm_apply (z : StdSpace ι) :
    (D.rescaledChart c x).symm z = (D.chart x).symm ((c : ℝ)⁻¹ • z) := by
  rw [rescaledChart_def, PartialDiffeomorph.transAffine_symm_apply,
    ContinuousLinearEquiv.smulLeft_symm_apply, add_zero, Units.smul_def, Units.val_inv_eq_inv_val]

/-- The form of `rescaledChart_symm_apply` that `simp` uses, since `simp` writes the inverse of a
partial diffeomorphism through its underlying partial equivalence. -/
@[simp]
theorem rescaledChart_toPartialEquiv_symm_apply (z : StdSpace ι) :
    (D.rescaledChart c x).toPartialEquiv.symm z =
      (D.chart x).toPartialEquiv.symm ((c : ℝ)⁻¹ • z) := by
  simp [rescaledChart_def, Units.smul_def]

@[simp]
theorem mem_rescaledChart_target_iff {z : StdSpace ι} :
    z ∈ (D.rescaledChart c x).target ↔ (c : ℝ)⁻¹ • z ∈ (D.chart x).target := by
  simp [rescaledChart_def, Units.smul_def]

/-- The derivative of the chart rescaled by `c` is `c` times that of `D.chart x`, at every
point. -/
theorem mvfderiv_rescaledChart (y : M) :
    mvfderiv I (D.rescaledChart c x) y = (c : ℝ) • mvfderiv I (D.chart x) y := by
  rw [rescaledChart_def, PartialDiffeomorph.mvfderiv_transAffine,
    ContinuousLinearEquiv.coe_smulLeft, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.id_comp]

/-- The target of the chart rescaled by `c` contains the ball of radius `|c| * D.radius`
about `0`. -/
theorem ball_subset_rescaledChart_target :
    ball 0 (|(c : ℝ)| * D.radius) ⊆ (D.rescaledChart c x).target := fun _ hz ↦
  (D.mem_rescaledChart_target_iff c x).2 (D.ball_subset_target x
    ((inv_smul_mem_ball_zero_iff c.ne_zero).2 (by rwa [Real.norm_eq_abs])))

/-- The chart rescaled by `c` pulls `stdForm ι` back to `c ^ 2 • σ` on its source. -/
theorem eval₂_rescaledChart (y : M) (hy : y ∈ (D.rescaledChart c x).source)
    (v w : TangentSpace I y) :
    (c : ℝ) ^ 2 * σ.eval₂ y v w =
      stdForm ι (mvfderiv I (D.rescaledChart c x) y v)
        (mvfderiv I (D.rescaledChart c x) y w) := by
  rw [mvfderiv_rescaledChart, D.eval₂_eq x y (by simpa using hy) v w]
  simp only [smul_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

/-- At a point `z` of the target of the chart rescaled by `c`, the pull-back of a form along its
inverse is the pull-back, along the dilation `w ↦ c⁻¹ • w`, of the pull-back along the inverse of
`D.chart x`. -/
theorem mpullback_rescaledChart_symm_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {k : ℕ} (η : RoughForm I M F k) {z : StdSpace ι} (hz : z ∈ (D.rescaledChart c x).target) :
    mpullback 𝓘(ℝ, StdSpace ι) I (D.rescaledChart c x).symm η z =
      mpullback 𝓘(ℝ, StdSpace ι) 𝓘(ℝ, StdSpace ι) ((c : ℝ)⁻¹ • ·)
        (mpullback 𝓘(ℝ, StdSpace ι) I (D.chart x).symm η) z := by
  rw [mem_rescaledChart_target_iff] at hz
  have hsymm : ⇑(D.rescaledChart c x).symm = ⇑(D.chart x).symm ∘ ((c : ℝ)⁻¹ • ·) :=
    funext (D.rescaledChart_symm_apply c x)
  rw [hsymm]
  exact mpullback_comp_at
    ((hasFDerivAt_id z).const_smul (c : ℝ)⁻¹).differentiableAt.mdifferentiableAt
    (((D.chart x).symm.contMDiffAt hz).mdifferentiableAt (by simp)) η

/-- `J` read in the chart rescaled by `c`, at a point `z` of its target, is `J` read in
`D.chart x` at `c⁻¹ • z`. -/
theorem chartPushforward_rescaledChart {z : StdSpace ι}
    (hz : z ∈ (D.rescaledChart c x).target) :
    J.chartPushforward (D.rescaledChart c x).toOpenPartialHomeomorph z =
      J.chartPushforward (D.chart x).toOpenPartialHomeomorph ((c : ℝ)⁻¹ • z) := by
  rw [rescaledChart_def] at hz ⊢
  rw [J.chartPushforward_transAffine _ _ _ hz]
  refine ContinuousLinearMap.ext fun w ↦ ?_
  simp [Units.smul_def]

/-- On the ball of radius `|c| * D.radius` about `0`, `J` read in the chart rescaled by `c`
differs from `stdComplexStructure ι` by at most `D.bound 1 * |c|⁻¹ * ‖z‖` at `z`. -/
theorem norm_chartPushforward_rescaledChart_sub_le [I.Boundaryless] {z : StdSpace ι}
    (hz : z ∈ ball 0 (|(c : ℝ)| * D.radius)) :
    ‖J.chartPushforward (D.rescaledChart c x).toOpenPartialHomeomorph z -
        LinearMap.toContinuousLinearMap (stdComplexStructure ι).toLinearMap‖ ≤
      D.bound 1 * |(c : ℝ)|⁻¹ * ‖z‖ := by
  set ψ := (D.chart x).toOpenPartialHomeomorph
  have hz' : (c : ℝ)⁻¹ • z ∈ ball (0 : StdSpace ι) D.radius :=
    (inv_smul_mem_ball_zero_iff c.ne_zero).2 (by rwa [Real.norm_eq_abs])
  have h0 : J.chartPushforward ψ 0 =
      LinearMap.toContinuousLinearMap (stdComplexStructure ι).toLinearMap := by
    exact ContinuousLinearMap.ext (D.chartPushforward_zero x)
  have hdiff : ∀ y ∈ ball (0 : StdSpace ι) D.radius, DifferentiableAt ℝ (J.chartPushforward ψ) y :=
    fun y hy ↦ (J.contDiffAt_chartPushforward (D.chart x)
      (D.ball_subset_target x hy)).differentiableAt (by simp)
  rw [D.chartPushforward_rescaledChart c x (D.ball_subset_rescaledChart_target c x hz), ← h0]
  calc ‖J.chartPushforward ψ ((c : ℝ)⁻¹ • z) - J.chartPushforward ψ 0‖
      ≤ D.bound 1 * ‖(c : ℝ)⁻¹ • z - 0‖ :=
        (convex_ball 0 D.radius).norm_image_sub_le_of_norm_fderiv_le hdiff
          (fun y hy ↦ by
            simpa only [norm_iteratedFDeriv_one] using D.norm_iteratedFDeriv_le 1 x y hy)
          (mem_ball_self D.radius_pos) hz'
    _ = D.bound 1 * |(c : ℝ)|⁻¹ * ‖z‖ := by
        rw [sub_zero, norm_smul, norm_inv, Real.norm_eq_abs, mul_assoc]

/-- For every `r`, on the ball of radius `|c| * D.radius` about `0`, the `r`-th iterated
derivative of `J` read in the chart rescaled by `c` has norm at most `D.bound r * |c|⁻¹ ^ r`. -/
theorem norm_iteratedFDeriv_chartPushforward_rescaledChart_le (r : ℕ) {z : StdSpace ι}
    (hz : z ∈ ball 0 (|(c : ℝ)| * D.radius)) :
    ‖iteratedFDeriv ℝ r (J.chartPushforward (D.rescaledChart c x).toOpenPartialHomeomorph) z‖ ≤
      D.bound r * |(c : ℝ)|⁻¹ ^ r := by
  have hc : 0 < |(c : ℝ)| := abs_pos.2 c.ne_zero
  have hz' : (c : ℝ)⁻¹ • z ∈ ball (0 : StdSpace ι) D.radius :=
    (inv_smul_mem_ball_zero_iff c.ne_zero).2 (by rwa [Real.norm_eq_abs])
  have h := J.norm_iteratedFDeriv_chartPushforward_transAffine_le (D.chart x) 0
    (ContinuousLinearEquiv.smulLeft c) r (D.ball_subset_rescaledChart_target c x hz)
  rw [← rescaledChart_def, ContinuousLinearEquiv.smulLeft_symm, ContinuousLinearEquiv.coe_smulLeft,
    ContinuousLinearEquiv.coe_smulLeft, ContinuousLinearEquiv.smulLeft_apply_apply, add_zero,
    Units.smul_def, Units.val_inv_eq_inv_val] at h
  calc _ ≤ _ := h
    _ ≤ |(c : ℝ)| * |(c : ℝ)|⁻¹ ^ (r + 1) * D.bound r := by
        gcongr
        · exact (ContinuousLinearMap.opNorm_smul_le _ _).trans
            (by simpa using ContinuousLinearMap.norm_id_le)
        · exact (ContinuousLinearMap.opNorm_smul_le _ _).trans
            (by simpa using ContinuousLinearMap.norm_id_le)
        · exact D.norm_iteratedFDeriv_le r x _ hz'
    _ = D.bound r * |(c : ℝ)|⁻¹ ^ r * (|(c : ℝ)| * |(c : ℝ)|⁻¹) := by ring
    _ = D.bound r * |(c : ℝ)|⁻¹ ^ r := by rw [mul_inv_cancel₀ hc.ne', mul_one]

/-- For a scale `c ≥ 1` and every order `r ≥ 1`, on the ball of radius `c * D.radius` about `0`,
the `r`-th iterated derivative of `J` read in the chart rescaled by `c` has norm at most
`D.bound r * c⁻¹`. -/
theorem norm_iteratedFDeriv_chartPushforward_rescaledChart_le_of_one_le {r : ℕ} (hr : r ≠ 0)
    (hc : 1 ≤ (c : ℝ)) {z : StdSpace ι} (hz : z ∈ ball 0 ((c : ℝ) * D.radius)) :
    ‖iteratedFDeriv ℝ r (J.chartPushforward (D.rescaledChart c x).toOpenPartialHomeomorph) z‖ ≤
      D.bound r * (c : ℝ)⁻¹ := by
  have hc₀ : 0 < (c : ℝ) := zero_lt_one.trans_le hc
  rw [← abs_of_pos hc₀] at hz ⊢
  refine (D.norm_iteratedFDeriv_chartPushforward_rescaledChart_le c x r hz).trans ?_
  have : Nonempty M := ⟨x⟩
  gcongr
  · exact D.bound_nonneg r
  exact pow_le_of_le_one (inv_nonneg.2 (abs_nonneg _))
    (inv_le_one_of_one_le₀ (by rwa [abs_of_pos hc₀])) hr

end CenteredDarbouxCharts

/-! ### Frames in which the connection form is the model -/

section ModelFrame

open Bundle MulOpposite

variable {P : M → Type*} [TopologicalSpace (TotalSpace Circle P)] [∀ x, TopologicalSpace (P x)]
  [FiberBundle Circle P] [∀ x, MulAction Circleᵐᵒᵖ (P x)] [PrincipalBundle Circle P]
  [ContMDiffFiberBundle ∞ Circle P I (𝓡 1)]

/-- **A frame with the model connection form over a Darboux set.** Let `α` be a connection form on
a principal `Circle`-bundle `P` over a boundaryless manifold `M`, with curvature `-2π σ`, and let
`χ` be a chart of `M` into `StdSpace ι` that pulls `stdForm ι` back to `σ` on its source. Let `s`
be an open subset of the target of `χ`, star-convex with respect to some point, such as a ball,
and `τ₀` a section of `P` that is smooth on `χ⁻¹ '' s`. Then there is a section `τ` of `P`,
smooth on `χ⁻¹ '' s`, such that `χ⁻¹^* (τ^* α)` is the model connection form
`stdConnectionForm ι` at every point of `s`.

The section is `τ₀ · exp (i θ ∘ χ)`, where `θ` is a primitive on `s` of the difference between the
model and `χ⁻¹^* (τ₀^* α)`, two forms whose exterior derivative on `s` is `-2π` times the
constant form `stdForm ι`. -/
theorem IsCircleConnectionForm.exists_mpullback_symm_mpullback_eq_stdConnectionForm
    {α : SmoothForm (I.prod (𝓡 1)) (ManifoldTotalSpace Circle P) ℝ 1}
    (hα : IsCircleConnectionForm α) {σ : SmoothTwoForm I M}
    (hασ : hα.curvature = -(2 * Real.pi) • σ)
    (χ : PartialDiffeomorph I 𝓘(ℝ, StdSpace ι) M (StdSpace ι) ∞)
    (hχ : ∀ x ∈ χ.source, ∀ v w : TangentSpace I x,
      σ.eval₂ x v w = stdForm ι (mvfderiv I χ x v) (mvfderiv I χ x w))
    {s : Set (StdSpace ι)} {z₀ : StdSpace ι} (hs : StarConvex ℝ z₀ s) (hso : IsOpen s)
    (hsχ : s ⊆ χ.target) {τ₀ : ∀ x, P x}
    (hτ₀ : ContMDiffOn I (I.prod (𝓡 1)) ∞
      (fun x ↦ ManifoldTotalSpace.homeomorph Circle P ⟨x, τ₀ x⟩) (χ.symm '' s)) :
    ∃ τ : ∀ x, P x, ContMDiffOn I (I.prod (𝓡 1)) ∞
        (fun x ↦ ManifoldTotalSpace.homeomorph Circle P ⟨x, τ x⟩) (χ.symm '' s) ∧
      ∀ z ∈ s, mpullback 𝓘(ℝ, StdSpace ι) I χ.symm (mpullback I (I.prod (𝓡 1))
          (fun x ↦ ManifoldTotalSpace.homeomorph Circle P ⟨x, τ x⟩) α.val) z =
        (stdConnectionForm ι).val z := by
  set t₀ := fun x ↦ ManifoldTotalSpace.homeomorph Circle P ⟨x, τ₀ x⟩
  -- The connection form read in `χ` through `τ₀`.
  set β := mpullback 𝓘(ℝ, StdSpace ι) I χ.symm (mpullback I (I.prod (𝓡 1)) t₀ α.val)
  have hχs {z} (hz : z ∈ χ.target) : ContMDiffAt 𝓘(ℝ, StdSpace ι) I ∞ χ.symm z :=
    χ.symm.contMDiffAt hz
  have hU : IsOpen (χ.symm '' s) :=
    χ.toOpenPartialHomeomorph.isOpen_image_symm_of_subset_target hso hsχ
  have ht₀ {z} (hz : z ∈ s) : ContMDiffAt I (I.prod (𝓡 1)) ∞ t₀ (χ.symm z) :=
    hτ₀.contMDiffAt (hU.mem_nhds ⟨z, hz, rfl⟩)
  have hα₀ {z} (hz : z ∈ s) :=
    (α.isSmoothForm.contMDiff _).mpullback_form (ht₀ hz) le_rfl
  have hβ : ContDiffOn ℝ (E := StdSpace ι) (F := StdSpace ι [⋀^Fin 1]→L[ℝ] ℝ) (⊤ : ℕ∞) β s :=
    fun z hz ↦ (RoughForm.contDiffWithinAt_of_contMDiffWithinAt_modelSpace
      ((hα₀ hz).mpullback_form (hχs (hsχ hz)) le_rfl).contMDiffWithinAt).mono
        (Set.subset_univ s)
  -- `dβ` is the curvature read in `χ`, that is `-2π ω₀`.
  have hdβ : ∀ z ∈ s, mextDeriv β z = (-(2 * Real.pi) • (stdForm ι).constSmooth).val z := by
    intro z hz
    have hz' := hsχ hz
    rw [← mpullback_mextDeriv_at ((hχs hz').of_le (by simp)) ((hα₀ hz).of_le (by simp)),
      mpullback_apply_congr (hα.curvature_apply_eq_mextDeriv_mpullback (ht₀ hz)).symm, hασ,
      SetLike.val_smul, mpullback_smul, Pi.smul_apply,
      SmoothTwoForm.mpullback_symm_apply_eq_constSmooth hχ hz', SmoothBundleForm.smul_apply]
  obtain ⟨θ, hθ, hθβ⟩ :=
    exists_contDiffOn_add_mextDeriv_eq_stdConnectionForm hs hso le_top hβ hdβ
  have hθ' : ContDiffOn ℝ ∞ θ s := by simpa using hθ
  have hsrc : χ.symm '' s ⊆ χ.source :=
    Set.image_subset_iff.2 fun z hz ↦ χ.map_target (hsχ hz)
  have hθχ : ContMDiffOn I 𝓘(ℝ) ∞ (fun x ↦ θ (χ x)) (χ.symm '' s) :=
    hθ'.contMDiffOn.comp (χ.contMDiffOn.mono hsrc) (by
      rintro _ ⟨z, hz, rfl⟩
      simpa [χ.toPartialEquiv.right_inv (hsχ hz)] using hz)
  refine ⟨fun x ↦ op (Circle.exp (θ (χ x))) • τ₀ x,
    hτ₀.totalSpaceMk_smul (contMDiff_circleExp.comp_contMDiffOn hθχ), fun z hz ↦ ?_⟩
  have hz' := hsχ hz
  have hθχz : ContMDiffAt I 𝓘(ℝ) ∞ (fun x ↦ θ (χ x)) (χ.symm z) := by
    have hθz : ContMDiffAt 𝓘(ℝ, StdSpace ι) 𝓘(ℝ) ∞ θ (χ (χ.symm z)) := by
      rw [show χ (χ.symm z) = z from χ.right_inv hz']
      exact (hθ'.contDiffAt (hso.mem_nhds hz)).contMDiffAt
    exact hθz.comp (χ.symm z)
      (χ.contMDiffAt (χ.map_target hz'))
  -- The change of section adds `d (θ ∘ χ)`, which reads as `dθ` in `χ`.
  rw [mpullback_apply_congr (η := mextDeriv (RoughForm.ofFunction I fun x ↦ θ (χ x)) +
      mpullback I (I.prod (𝓡 1)) t₀ α.val)
      (hα.mpullback_apply_op_circleExp_smul_eq_mextDeriv_add (x := χ.symm.toPartialEquiv z)
        hU hτ₀ ⟨z, hz, rfl⟩ (hθχz.of_le (by simp))),
    mpullback_add, Pi.add_apply, mpullback_mextDeriv_ofFunction_apply
      ((hχs hz').mdifferentiableAt (by simp)) (hθχz.mdifferentiableAt (by simp)),
    add_comm, ← hθβ z hz]
  congr 1
  refine mextDeriv_congr_of_eventuallyEq ?_
  filter_upwards [χ.open_target.mem_nhds hz'] with y hy
  ext v
  rw [RoughForm.ofFunction_apply, RoughForm.ofFunction_apply, Function.comp_apply]
  exact congrArg θ (χ.right_inv hy)

end ModelFrame

/-! ### Rescaled unitary charts -/

section RescaledUnitaryCharts

open Bundle MulOpposite

variable {P : M → Type*} [TopologicalSpace (TotalSpace Circle P)] [∀ x, TopologicalSpace (P x)]
  [FiberBundle Circle P] [∀ x, MulAction Circleᵐᵒᵖ (P x)] [PrincipalBundle Circle P]
  [ContMDiffFiberBundle ∞ Circle P I (𝓡 1)]

variable (P) in
/-- Rescaled unitary charts for a two-form `σ`, an almost complex structure `J` and a one-form
`α` on the total space of a principal `Circle`-bundle `P`, from the power `k₀` on, with radius
`ρ₀`. For every `k ≥ k₀` and every point `x`, they give a chart `chart k x` of `M` into
`StdSpace ι` and a local section `frame k x` of `P`, such that:
* the chart sends `x` to `0`, and its target contains the ball `B` of radius `ρ₀ * √k`
  about `0`;
* it pulls `stdForm ι` back to `2π k σ` on its source;
* it reads `J` at `0` as `stdComplexStructure ι`;
* the section is smooth over the image of `B`, and on `B` the form `k α`, pulled back along the
  section and read in the chart, is the model `-λ₀`, minus the radial primitive
  `λ₀ = (stdForm ι).radialPrimitive`, `λ₀(z)(v) = ω₀(z, v) / 2`, whose exterior derivative is
  `ω₀` (`TauCeti.SymplecticForm.mextDeriv_radialPrimitive`). For a connection form `α`,
  `powerConnection α k` reads in the frame `[frame k x, 1]` of `PowerBundle P k` as
  `d + i k (frame k x)^* α` (`SymplecticGeometry.powerConnection_apply_frame`), so its connection
  form read in the chart is `i` times this model;
* on `B`, `J` read in the chart differs from `stdComplexStructure ι` by at most
  `bound 1 * ‖z‖ / √k` at `z`, and its derivatives of order `r ≥ 1` are at most
  `bound r / √k`.

The constants `bound r` depend neither on `k` nor on `x`. -/
@[ext]
structure RescaledUnitaryCharts (σ : SmoothTwoForm I M) (J : SmoothAlmostComplexStructure I M)
    (α : SmoothForm (I.prod (𝓡 1)) (ManifoldTotalSpace Circle P) ℝ 1) (ι : Type*) [Fintype ι]
    (k₀ : ℕ) (ρ₀ : ℝ) where
  /-- The chart centred at `x` for the power `k`. -/
  chart : ℕ → M → PartialDiffeomorph I 𝓘(ℝ, StdSpace ι) M (StdSpace ι) ∞
  /-- The local section of `P` over the chart centred at `x` for the power `k`. -/
  frame : ℕ → M → ∀ y, P y
  /-- The bounds on `J` read in the charts. -/
  bound : ℕ → ℝ
  mem_source {k : ℕ} (hk : k₀ ≤ k) (x : M) : x ∈ (chart k x).source
  apply_self {k : ℕ} (hk : k₀ ≤ k) (x : M) : chart k x x = 0
  ball_subset_target {k : ℕ} (hk : k₀ ≤ k) (x : M) : ball 0 (ρ₀ * √k) ⊆ (chart k x).target
  eval₂_eq {k : ℕ} (hk : k₀ ≤ k) (x : M) : ∀ y ∈ (chart k x).source, ∀ v w : TangentSpace I y,
    2 * Real.pi * k * σ.eval₂ y v w =
      stdForm ι (mvfderiv I (chart k x) y v) (mvfderiv I (chart k x) y w)
  chartPushforward_zero {k : ℕ} (hk : k₀ ≤ k) (x : M) (w : StdSpace ι) :
    J.chartPushforward (chart k x).toOpenPartialHomeomorph 0 w = stdComplexStructure ι w
  contMDiffOn_frame {k : ℕ} (hk : k₀ ≤ k) (x : M) :
    ContMDiffOn I (I.prod (𝓡 1)) ∞
      (fun y ↦ ManifoldTotalSpace.homeomorph Circle P ⟨y, frame k x y⟩)
      ((chart k x).symm '' ball 0 (ρ₀ * √k))
  connectionForm_eq_model {k : ℕ} (hk : k₀ ≤ k) (x : M) :
    ∀ z ∈ ball (0 : StdSpace ι) (ρ₀ * √k), ∀ v : StdSpace ι,
      k * mpullback 𝓘(ℝ, StdSpace ι) I (chart k x).symm (mpullback I (I.prod (𝓡 1))
          (fun y ↦ ManifoldTotalSpace.homeomorph Circle P ⟨y, frame k x y⟩) α.val) z ![v] =
        -(stdForm ι).radialPrimitive.val z ![v]
  jStruct_sub_le {k : ℕ} (hk : k₀ ≤ k) (x : M) : ∀ z ∈ ball (0 : StdSpace ι) (ρ₀ * √k),
    ‖J.chartPushforward (chart k x).toOpenPartialHomeomorph z -
        LinearMap.toContinuousLinearMap (stdComplexStructure ι).toLinearMap‖ ≤
      bound 1 * (√k)⁻¹ * ‖z‖
  iteratedFDeriv_jStruct_le {k : ℕ} (hk : k₀ ≤ k) {r : ℕ} (hr : r ≠ 0) (x : M) :
    ∀ z ∈ ball (0 : StdSpace ι) (ρ₀ * √k),
      ‖iteratedFDeriv ℝ r (J.chartPushforward (chart k x).toOpenPartialHomeomorph) z‖ ≤
        bound r * (√k)⁻¹

/-- The scale `√(2π k)` as a unit, for `k ≥ 1`. -/
private theorem exists_unit_eq_sqrt (k : ℕ) : ∃ u : ℝˣ, 1 ≤ k → (u : ℝ) = √(2 * Real.pi * k) := by
  by_cases hk : 1 ≤ k
  · refine ⟨Units.mk0 _ (Real.sqrt_ne_zero'.2 (by positivity)), fun _ ↦ rfl⟩
  · exact ⟨1, fun h ↦ absurd h hk⟩

/-- **Existence of rescaled unitary charts.** On a compact boundaryless manifold `M` of dimension
`2 * card ι`, with a two-form `σ`, a smooth almost complex structure `J` compatible with `σ`,
and a connection form `α` on a principal `Circle`-bundle `P` with curvature `-2π σ`, there are
rescaled unitary charts from the power `1` on, for some radius `ρ₀ > 0`.

They are the centred Darboux charts of
`SymplecticGeometry.exists_centeredDarbouxCharts_source_subset`, with sources inside base sets of
trivializations of `P`, rescaled by `√(2π k)`; the frames are local sections of `P` rotated so that
`α` reads as the model connection form
(`SymplecticGeometry.IsCircleConnectionForm.exists_mpullback_symm_mpullback_eq_stdConnectionForm`).
`σ` need not be assumed closed: it is `-(2π)⁻¹` times the curvature, which is closed.
-/
theorem exists_rescaledUnitaryCharts [FiniteDimensional ℝ E] [CompactSpace M]
    [∀ x, Nonempty (P x)] (hE : Module.finrank ℝ E = 2 * Fintype.card ι)
    {σ : SmoothTwoForm I M} {J : SmoothAlmostComplexStructure I M} (hJ : σ.Compatible J)
    {α : SmoothForm (I.prod (𝓡 1)) (ManifoldTotalSpace Circle P) ℝ 1}
    (hα : IsCircleConnectionForm α) (hασ : hα.curvature = -(2 * Real.pi) • σ) :
    ∃ ρ₀ > 0, Nonempty (RescaledUnitaryCharts P σ J α ι 1 ρ₀) := by
  classical
  have hπ : 0 < 2 * Real.pi := by positivity
  -- `σ` is closed, as `-2π` times it is the curvature.
  have hσ : σ.IsClosed := by
    have h := (hασ ▸ hα.isClosed_curvature).smul (-(2 * Real.pi))⁻¹
    rwa [inv_smul_smul₀ (neg_ne_zero.2 hπ.ne')] at h
  -- Centred Darboux charts whose sources lie in base sets of trivializations of `P`.
  obtain ⟨D, c, hc⟩ := exists_centeredDarbouxCharts_source_subset hE hσ hJ
    (U := fun p ↦ (trivializationAt Circle P p).baseSet) fun p ↦
      (trivializationAt Circle P p).open_baseSet.mem_nhds (mem_baseSet_trivializationAt Circle P p)
  -- The frames over the balls of radius `D.radius` in the charts, rotated from the preferred
  -- local sections of `P`, which are smooth on the base sets.
  have hsec (x : M) : ContMDiffOn I (I.prod (𝓡 1)) ∞ (fun y ↦ ManifoldTotalSpace.homeomorph
      Circle P ⟨y, TauCeti.PrincipalBundle.localSection Circle P (c x) y⟩)
      ((D.chart x).symm '' ball 0 D.radius) := by
    rw [← funext (TauCeti.PrincipalBundle.manifoldLocalSection_def Circle P (c x))]
    exact (TauCeti.PrincipalBundle.contMDiffOn_manifoldLocalSection ∞ I (𝓡 1) (c x)).mono <|
      Set.image_subset_iff.2 fun z hz ↦ hc x ((D.chart x).map_target (D.ball_subset_target x hz))
  have hframe (x : M) := hα.exists_mpullback_symm_mpullback_eq_stdConnectionForm hασ (D.chart x)
    (D.eval₂_eq x) ((convex_ball (0 : StdSpace ι) D.radius).starConvex
      (mem_ball_self D.radius_pos)) isOpen_ball (D.ball_subset_target x) (hsec x)
  choose τ hτ hτα using hframe
  choose u hu using exists_unit_eq_sqrt
  set ρ₀ := √(2 * Real.pi) * D.radius
  -- The ball of radius `ρ₀ * √k` is the ball of radius `|u k| * D.radius`.
  have hball {k : ℕ} (hk : 1 ≤ k) : ρ₀ * √k = |(u k : ℝ)| * D.radius := by
    rw [hu k hk, abs_of_nonneg (Real.sqrt_nonneg _), Real.sqrt_mul hπ.le]
    ring
  have hinv {k : ℕ} (hk : 1 ≤ k) : |(u k : ℝ)|⁻¹ = (√(2 * Real.pi))⁻¹ * (√k)⁻¹ := by
    rw [hu k hk, abs_of_nonneg (Real.sqrt_nonneg _), Real.sqrt_mul hπ.le, mul_inv]
  have hsq {k : ℕ} (hk : 1 ≤ k) : (u k : ℝ) ^ 2 = 2 * Real.pi * k := by
    rw [hu k hk, Real.sq_sqrt (by positivity)]
  have hone {k : ℕ} (hk : 1 ≤ k) : 1 ≤ (u k : ℝ) := by
    rw [hu k hk, Real.one_le_sqrt]
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith [Real.two_le_pi]
  -- A point of the rescaled ball comes from the ball of radius `D.radius`.
  have hmem {k : ℕ} (hk : 1 ≤ k) {z : StdSpace ι} (hz : z ∈ ball (0 : StdSpace ι) (ρ₀ * √k)) :
      ((u k : ℝ))⁻¹ • z ∈ ball (0 : StdSpace ι) D.radius := by
    rw [hball hk] at hz
    exact (inv_smul_mem_ball_zero_iff (u k).ne_zero).2 (by rwa [Real.norm_eq_abs])
  refine ⟨ρ₀, by have := D.radius_pos; positivity, ⟨{
    chart k x := D.rescaledChart (u k) x
    frame _ x := τ x
    bound r := D.bound r * (√(2 * Real.pi))⁻¹
    mem_source _ x := D.mem_rescaledChart_source _ x
    apply_self _ x := D.rescaledChart_apply_self _ x
    ball_subset_target {k} hk x := by
      rw [hball hk]
      exact D.ball_subset_rescaledChart_target _ x
    eval₂_eq {k} hk x y hy v w := by
      rw [← D.eval₂_rescaledChart _ x y hy v w, hsq hk]
    chartPushforward_zero {k} _ x w := by
      rw [D.chartPushforward_rescaledChart _ x
        (D.ball_subset_rescaledChart_target _ x (mem_ball_self (by
          have := D.radius_pos
          have := abs_pos.2 (u k).ne_zero
          positivity))), smul_zero]
      exact D.chartPushforward_zero x w
    contMDiffOn_frame {k} hk x := (hτ x).mono <| by
      rintro _ ⟨z, hz, rfl⟩
      exact ⟨_, hmem hk hz, (D.rescaledChart_symm_apply _ x z).symm⟩
    connectionForm_eq_model {k} hk x z hz v := by
      rw [D.mpullback_rescaledChart_symm_apply _ x _ (D.ball_subset_rescaledChart_target _ x
          (by rwa [← hball hk])), mpullback_apply_congr (hτα x _ (hmem hk hz)),
        stdConnectionForm_def, SetLike.val_smul, mpullback_smul,
        mpullback_const_smul_radialPrimitive, smul_smul, Pi.smul_apply,
        ContinuousAlternatingMap.smul_apply, smul_eq_mul, inv_pow, hsq hk]
      field_simp
    jStruct_sub_le {k} hk x z hz := by
      have h := D.norm_chartPushforward_rescaledChart_sub_le (u k) x (z := z) (by rwa [← hball hk])
      rwa [hinv hk, ← mul_assoc] at h
    iteratedFDeriv_jStruct_le {k} hk r hr x z hz := by
      have h := D.norm_iteratedFDeriv_chartPushforward_rescaledChart_le_of_one_le (u k) x hr
        (hone hk) (z := z) (by
          rw [← abs_of_pos (zero_lt_one.trans_le (hone hk)), ← hball hk]
          exact hz)
      rwa [← abs_of_pos (zero_lt_one.trans_le (hone hk)), hinv hk, ← mul_assoc] at h }⟩⟩

namespace RescaledUnitaryCharts

omit [I.Boundaryless] [∀ x, MulAction Circleᵐᵒᵖ (P x)] [PrincipalBundle Circle P]

variable {σ : SmoothTwoForm I M} {J : SmoothAlmostComplexStructure I M}
  {α : SmoothForm (I.prod (𝓡 1)) (ManifoldTotalSpace Circle P) ℝ 1} {k₀ : ℕ} {ρ₀ : ℝ}
  (D : RescaledUnitaryCharts P σ J α ι k₀ ρ₀)

/-- The inverse of the chart centred at `x` sends the centre `0` to `x`. -/
theorem chart_symm_zero {k : ℕ} (hk : k₀ ≤ k) (x : M) : (D.chart k x).symm 0 = x := by
  rw [← D.apply_self hk x]
  exact (D.chart k x).left_inv (D.mem_source hk x)

/-- The centre `0` lies in the target of the chart centred at `x`. -/
theorem zero_mem_chart_target {k : ℕ} (hk : k₀ ≤ k) (x : M) :
    (0 : StdSpace ι) ∈ (D.chart k x).target := by
  rw [← D.apply_self hk x]
  exact (D.chart k x).map_source (D.mem_source hk x)

/-- The inverse of the chart centred at `x` sends a compact subset of the ball of radius
`ρ₀ * √k` to a compact subset of `M`. -/
theorem isCompact_chart_symm_image {k : ℕ} (hk : k₀ ≤ k) (x : M) {K : Set (StdSpace ι)}
    (hK : IsCompact K) (hKB : K ⊆ ball 0 (ρ₀ * √k)) : IsCompact ((D.chart k x).symm '' K) :=
  hK.image_of_continuousOn ((D.chart k x).toOpenPartialHomeomorph.continuousOn_symm.mono
    (hKB.trans (D.ball_subset_target hk x)))

/-- At a point `y` whose image `z` under the chart `D.chart k x` lies in the ball of radius
`ρ₀ * √k`, the quadratic form `2π k σ(v, J v)` of a tangent vector `v` at `y` differs from
`‖u‖ ^ 2`, for `u` the image of `v` under the derivative of the chart, by at most
`D.bound 1 * ‖z‖ / √k` times `‖u‖ ^ 2`. -/
theorem abs_eval₂_apply_sub_norm_sq_le {k : ℕ} (hk : k₀ ≤ k) (x : M) {y : M}
    (hy : y ∈ (D.chart k x).source) (hyB : D.chart k x y ∈ ball 0 (ρ₀ * √k))
    (v : TangentSpace I y) :
    |2 * Real.pi * k * σ.eval₂ y v (J y v) - ‖mvfderiv I (D.chart k x) y v‖ ^ 2| ≤
      D.bound 1 * (√k)⁻¹ * ‖D.chart k x y‖ * ‖mvfderiv I (D.chart k x) y v‖ ^ 2 := by
  set A := J.chartPushforward (D.chart k x).toOpenPartialHomeomorph (D.chart k x y) -
    LinearMap.toContinuousLinearMap (stdComplexStructure ι).toLinearMap
  have hJv : mvfderiv I (D.chart k x) y (J y v) =
      stdComplexStructure ι (mvfderiv I (D.chart k x) y v) + A (mvfderiv I (D.chart k x) y v) := by
    have h : J.chartPushforward (D.chart k x).toOpenPartialHomeomorph (D.chart k x y)
        (mfderiv I 𝓘(ℝ, StdSpace ι) (D.chart k x) y v) =
          mfderiv I 𝓘(ℝ, StdSpace ι) (D.chart k x) y (J y v) := by
      rw [J.chartPushforward_toOpenPartialHomeomorph]
      exact (D.chart k x).pushforwardEndomorphism_mfderiv_apply J hy v
    rw [mvfderiv_apply_eq_mfderiv_apply, ← h, ← mvfderiv_apply_eq_mfderiv_apply]
    simp only [A, sub_apply, LinearMap.coe_toContinuousLinearMap', add_sub_cancel]
  rw [D.eval₂_eq hk x y hy, hJv]
  set u := mvfderiv I (D.chart k x) y v
  have hsplit : stdForm ι u (stdComplexStructure ι u + A u) = ‖u‖ ^ 2 + stdForm ι u (A u) := by
    simp only [map_add, stdForm_apply_stdComplexStructure, real_inner_self_eq_norm_sq]
  rw [hsplit, add_sub_cancel_left]
  calc |stdForm ι u (A u)| ≤ ‖u‖ * ‖A u‖ := abs_stdForm_apply_le u (A u)
    _ ≤ ‖u‖ * ((D.bound 1 * (√k)⁻¹ * ‖D.chart k x y‖) * ‖u‖) := by
        gcongr
        exact (A.le_opNorm u).trans (by gcongr; exact D.jStruct_sub_le hk x _ hyB)
    _ = D.bound 1 * (√k)⁻¹ * ‖D.chart k x y‖ * ‖u‖ ^ 2 := by ring

/-- At a point `y` whose image `z` under the chart `D.chart k x` lies in the ball of radius
`ρ₀ * √k`, the square root of `σ(v, J v)` for a tangent vector `v` at `y` is at most
`(2π k)^(-1/2) (1 + C ‖z‖ / √k) ‖u‖`, for `u` the image of `v` under the derivative of the chart
and `C = max (D.bound 1) 0`. -/
theorem sqrt_eval₂_apply_le {k : ℕ} (hk : k₀ ≤ k) (x : M) {y : M}
    (hy : y ∈ (D.chart k x).source) (hyB : D.chart k x y ∈ ball 0 (ρ₀ * √k))
    (v : TangentSpace I y) :
    √(σ.eval₂ y v (J y v)) ≤ (2 * Real.pi * k) ^ (-1 / 2 : ℝ) *
      ((1 + max (D.bound 1) 0 * ‖D.chart k x y‖ / √k) * ‖mvfderiv I (D.chart k x) y v‖) := by
  set u := mvfderiv I (D.chart k x) y v
  set t := max (D.bound 1) 0 * ‖D.chart k x y‖ / √k
  set p := (2 * Real.pi * k) ^ (-1 / 2 : ℝ)
  have hkpos : (0 : ℝ) < k := by
    have h0 : 0 < ρ₀ * √k := (norm_nonneg _).trans_lt (mem_ball_zero_iff.1 hyB)
    by_contra h
    rw [Real.sqrt_eq_zero'.2 (not_lt.1 h), mul_zero] at h0
    exact lt_irrefl 0 h0
  have ht : 0 ≤ t := by positivity
  have hbt : D.bound 1 * (√k)⁻¹ * ‖D.chart k x y‖ ≤ t := by
    simp only [t, div_eq_mul_inv, mul_right_comm _ (√(k : ℝ))⁻¹]
    gcongr
    exact le_max_left _ _
  have hsq : p ^ 2 * (2 * Real.pi * k) = 1 := by
    simp only [p]
    rw [← Real.rpow_mul_natCast (by positivity : (0 : ℝ) ≤ 2 * Real.pi * k),
      ← Real.rpow_add_one (by positivity : (2 * Real.pi * k : ℝ) ≠ 0)]
    norm_num
  have hle : 2 * Real.pi * k * σ.eval₂ y v (J y v) ≤ (1 + t) ^ 2 * ‖u‖ ^ 2 := by
    have := (abs_le.1 (D.abs_eval₂_apply_sub_norm_sq_le hk x hy hyB v)).2
    have : 1 + t ≤ (1 + t) ^ 2 := by nlinarith
    have : D.bound 1 * (√k)⁻¹ * ‖D.chart k x y‖ * ‖u‖ ^ 2 ≤ t * ‖u‖ ^ 2 := by gcongr
    nlinarith [sq_nonneg ‖u‖]
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  calc σ.eval₂ y v (J y v) = p ^ 2 * (2 * Real.pi * k * σ.eval₂ y v (J y v)) := by
        rw [← mul_assoc, hsq, one_mul]
    _ ≤ p ^ 2 * ((1 + t) ^ 2 * ‖u‖ ^ 2) := by gcongr
    _ = (p * ((1 + t) * ‖u‖)) ^ 2 := by ring

/-- `D.IsComparisonRadius k x ρ₁` says that on the ball of radius `ρ₁ * √k` the quadratic form
`2π k σ(v, J v)` is comparable with the square of the norm in the chart `D.chart k x`: for every
`y` in the source of the chart whose image lies in that ball, and every tangent vector `v` at `y`,
with `u` the image of `v` under the derivative of the chart,
`‖u‖ ^ 2 / 2 ≤ 2π k σ(v, J v) ≤ 3 / 2 * ‖u‖ ^ 2`. -/
def IsComparisonRadius (k : ℕ) (x : M) (ρ₁ : ℝ) : Prop :=
  ∀ ⦃y : M⦄, y ∈ (D.chart k x).source → D.chart k x y ∈ ball 0 (ρ₁ * √k) →
    ∀ v : TangentSpace I y, 2 * Real.pi * k * σ.eval₂ y v (J y v) ∈
      Set.Icc (‖mvfderiv I (D.chart k x) y v‖ ^ 2 / 2) (3 / 2 * ‖mvfderiv I (D.chart k x) y v‖ ^ 2)

theorem isComparisonRadius_def {k : ℕ} {x : M} {ρ₁ : ℝ} :
    D.IsComparisonRadius k x ρ₁ ↔
      ∀ ⦃y : M⦄, y ∈ (D.chart k x).source → D.chart k x y ∈ ball 0 (ρ₁ * √k) →
        ∀ v : TangentSpace I y, 2 * Real.pi * k * σ.eval₂ y v (J y v) ∈
          Set.Icc (‖mvfderiv I (D.chart k x) y v‖ ^ 2 / 2)
            (3 / 2 * ‖mvfderiv I (D.chart k x) y v‖ ^ 2) :=
  Iff.rfl

variable {D} in
/-- On a comparison radius, `2π k σ(v, J v)` lies between `‖u‖ ^ 2 / 2` and `3 / 2 * ‖u‖ ^ 2`,
for `u` the image of `v` under the derivative of the chart. -/
theorem IsComparisonRadius.mem_Icc {k : ℕ} {x : M} {ρ₁ : ℝ} (h : D.IsComparisonRadius k x ρ₁)
    {y : M} (hy : y ∈ (D.chart k x).source) (hyB : D.chart k x y ∈ ball 0 (ρ₁ * √k))
    (v : TangentSpace I y) :
    2 * Real.pi * k * σ.eval₂ y v (J y v) ∈
      Set.Icc (‖mvfderiv I (D.chart k x) y v‖ ^ 2 / 2)
        (3 / 2 * ‖mvfderiv I (D.chart k x) y v‖ ^ 2) :=
  D.isComparisonRadius_def.1 h hy hyB v

variable {D} in
/-- A radius smaller than a comparison radius is a comparison radius. -/
theorem IsComparisonRadius.mono {k : ℕ} {x : M} {ρ₁ ρ₂ : ℝ} (h : D.IsComparisonRadius k x ρ₂)
    (hρ : ρ₁ ≤ ρ₂) : D.IsComparisonRadius k x ρ₁ :=
  D.isComparisonRadius_def.2 fun _ hy hyB v ↦
    h.mem_Icc hy (ball_subset_ball (by gcongr) hyB) v

/-- **The metric `g_J` read in the rescaled unitary charts.** For rescaled unitary charts with
radius `ρ₀ > 0`, there is a radius `ρ₁` with `0 < ρ₁ ≤ ρ₀` that is a comparison radius
(`IsComparisonRadius`) for every `k ≥ k₀` and every point `x`: for every `y` in the source of
`D.chart k x` whose image lies in the ball of radius `ρ₁ * √k`, and every tangent vector `v` at
`y`, with `u` the image of `v` under the derivative of the chart,
`‖u‖ ^ 2 / 2 ≤ 2π k σ(v, J v) ≤ 3 / 2 * ‖u‖ ^ 2`.
For `J` compatible with `σ`, `σ(v, J v)` is the square of the norm of `v` for the metric `g_J`. -/
theorem exists_forall_isComparisonRadius (hρ₀ : 0 < ρ₀) :
    ∃ ρ₁, 0 < ρ₁ ∧ ρ₁ ≤ ρ₀ ∧ ∀ {k : ℕ}, k₀ ≤ k → ∀ x : M, D.IsComparisonRadius k x ρ₁ := by
  set b := |D.bound 1|
  refine ⟨min ρ₀ (1 / (2 * (b + 1))), lt_min hρ₀ (by positivity), min_le_left _ _,
    fun {k} hk x ↦ D.isComparisonRadius_def.2 fun y hy hyB v ↦ ?_⟩
  set ρ₁ := min ρ₀ (1 / (2 * (b + 1)))
  have hz : ‖D.chart k x y‖ < ρ₁ * √k := mem_ball_zero_iff.1 hyB
  have hρ₁ : 0 < ρ₁ := lt_min hρ₀ (by positivity)
  have hk0 : 0 < √k := pos_of_mul_pos_right ((norm_nonneg _).trans_lt hz) hρ₁.le
  have h := D.abs_eval₂_apply_sub_norm_sq_le hk x hy
    (ball_subset_ball (by gcongr; exact min_le_left _ _) hyB) v
  have ht : (√k)⁻¹ * ‖D.chart k x y‖ ≤ ρ₁ := by
    rw [inv_mul_le_iff₀ hk0]
    linarith
  have hsmall : D.bound 1 * (√k)⁻¹ * ‖D.chart k x y‖ ≤ 1 / 2 := by
    have hb : b * ρ₁ ≤ 1 / 2 := by
      calc b * ρ₁ ≤ b * (1 / (2 * (b + 1))) := by gcongr; exact min_le_right _ _
        _ ≤ 1 / 2 := by
          rw [mul_one_div, div_le_iff₀ (by positivity)]
          linarith
    calc D.bound 1 * (√k)⁻¹ * ‖D.chart k x y‖ = D.bound 1 * ((√k)⁻¹ * ‖D.chart k x y‖) := by
          ring
      _ ≤ b * ((√k)⁻¹ * ‖D.chart k x y‖) := by gcongr; exact le_abs_self _
      _ ≤ b * ρ₁ := by gcongr
      _ ≤ 1 / 2 := hb
  have hu := sq_nonneg ‖mvfderiv I (D.chart k x) y v‖
  have h' := h.trans (mul_le_mul_of_nonneg_right hsmall hu)
  exact Set.mem_Icc.2 ⟨by nlinarith [abs_le.1 h'], by nlinarith [abs_le.1 h']⟩

section RiemannianEDist

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- **The derivative of the inverse of a rescaled unitary chart, for `g_J`.** Let `M` carry a
Riemannian metric whose inner product is `⟪u, w⟫ = σ(u, J w)`, let `k ≥ k₀`, let `x` be a point,
and let `ρ₁ ≤ ρ₀` be a comparison radius for `D.chart k x` (`IsComparisonRadius`), as
`exists_forall_isComparisonRadius` provides. For every `w` in the ball of radius `ρ₁ * √k` and
every vector `u`, the derivative of the inverse of `D.chart k x`
at `w` sends `u` to a tangent vector whose norm, multiplied by `√(2π k)`, is at most
`√(3 / 2) * ‖u‖`. -/
theorem mul_norm_mfderiv_symm_le
    (hg : ∀ (x : M) (u w : TangentSpace I x), inner ℝ u w = σ.eval₂ x u (J x w))
    {ρ₁ : ℝ} (hρ₁₀ : ρ₁ ≤ ρ₀)
    {k : ℕ} (hk : k₀ ≤ k) (x : M) (hcmp : D.IsComparisonRadius k x ρ₁)
    {w : StdSpace ι} (hw : w ∈ ball (0 : StdSpace ι) (ρ₁ * √k))
    (u : StdSpace ι) :
    √(2 * Real.pi * k) * ‖mfderiv 𝓘(ℝ, StdSpace ι) I (D.chart k x).symm w u‖ ≤
      √(3 / 2) * ‖u‖ := by
  set φ := D.chart k x with hφ
  have hwt : w ∈ φ.target :=
    (ball_subset_ball (by gcongr)).trans (D.ball_subset_target hk x) hw
  set v := mfderiv 𝓘(ℝ, StdSpace ι) I φ.symm w u
  have hu : mvfderiv I φ (φ.symm w) v = u := by
    rw [mvfderiv_apply_eq_mfderiv_apply]
    exact φ.mfderiv_apply_mfderiv_symm_apply (by simp) hwt u
  have h := (hcmp.mem_Icc (y := φ.symm w) (φ.map_target hwt)
    (by convert hw; exact φ.right_inv hwt) v).2
  rw [← hφ, hu, ← hg, real_inner_self_eq_norm_sq] at h
  refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 ?_
  rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by norm_num)]
  linarith

/-- **A rescaled unitary chart stretches `g_J`-norms by at most `√2 * √(2π k)`.** Let `M` carry a
Riemannian metric whose inner product is `⟪u, w⟫ = σ(u, J w)`, let `k` be a natural number, `x` a
point, and `ρ₁` a comparison radius for `D.chart k x` (`IsComparisonRadius`), as
`exists_forall_isComparisonRadius` provides. For every `y` in the source of `D.chart k x`
whose image lies in the ball of radius `ρ₁ * √k`, and every tangent vector `v` at `y`, the
derivative of the chart sends `v` to a vector of norm at most `√2 * √(2π k) * ‖v‖`. -/
theorem norm_mvfderiv_le_mul
    (hg : ∀ (x : M) (u w : TangentSpace I x), inner ℝ u w = σ.eval₂ x u (J x w))
    {ρ₁ : ℝ} {k : ℕ} (x : M) (hcmp : D.IsComparisonRadius k x ρ₁)
    {y : M} (hy : y ∈ (D.chart k x).source) (hyB : D.chart k x y ∈ ball 0 (ρ₁ * √k))
    (v : TangentSpace I y) :
    ‖mvfderiv I (D.chart k x) y v‖ ≤ √2 * √(2 * Real.pi * k) * ‖v‖ := by
  have h := (hcmp.mem_Icc hy hyB v).1
  rw [← hg, real_inner_self_eq_norm_sq] at h
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  rw [mul_pow, mul_pow, Real.sq_sqrt zero_le_two, Real.sq_sqrt (by positivity)]
  linarith

/-- **Distances between two points, bounded in the rescaled unitary charts.** Let `M` carry a
Riemannian metric whose inner product is `g_J(u, w) = σ(u, J w)`, let `k ≥ k₀`, let `x` be a
point, and let `ρ₁ ≤ ρ₀` be a comparison radius for `D.chart k x` (`IsComparisonRadius`), as
`exists_forall_isComparisonRadius` provides. For all `a` and `b` in the ball of radius `ρ₁ * √k`,
the Riemannian distance between the points `(D.chart k x).symm a` and `(D.chart k x).symm b`,
multiplied by `√(2π k)`, is at most `√(3 / 2) * ‖a - b‖`. -/
theorem rescaledEDist_symm_symm_le
    (hg : ∀ (x : M) (u w : TangentSpace I x), inner ℝ u w = σ.eval₂ x u (J x w))
    {ρ₁ : ℝ} (hρ₁₀ : ρ₁ ≤ ρ₀)
    {k : ℕ} (hk : k₀ ≤ k) (x : M) (hcmp : D.IsComparisonRadius k x ρ₁)
    {a b : StdSpace ι} (ha : a ∈ ball (0 : StdSpace ι) (ρ₁ * √k))
    (hb : b ∈ ball (0 : StdSpace ι) (ρ₁ * √k)) :
    rescaledEDist I k ((D.chart k x).symm a) ((D.chart k x).symm b) ≤
      ENNReal.ofReal (√(3 / 2) * ‖a - b‖) := by
  rw [rescaledEDist_def]
  set φ := D.chart k x
  have hR : 0 < ρ₁ * √k := (norm_nonneg a).trans_lt (mem_ball_zero_iff.1 ha)
  have hk0 : 0 < √k := pos_of_mul_pos_right hR (pos_of_mul_pos_left hR (Real.sqrt_nonneg _)).le
  set s := √(2 * Real.pi * k)
  have hs : 0 < s := by
    have : 0 < (k : ℝ) := Real.sqrt_pos.1 hk0
    positivity
  have hball : ball (0 : StdSpace ι) (ρ₁ * √k) ⊆ φ.target :=
    (ball_subset_ball (by gcongr)).trans (D.ball_subset_target hk x)
  -- The straight segment from `a` to `b` lies in the ball, and its image is a path.
  have hseg : segment ℝ a b ⊆ ball (0 : StdSpace ι) (ρ₁ * √k) :=
    (convex_ball _ _).segment_subset ha hb
  have hd := Manifold.riemannianEDist_le_of_norm_mfderiv_le (I := I) (f := φ.symm)
    (C := √(3 / 2) * ‖a - b‖ / s)
    (fun w hw ↦ (φ.symm.contMDiffAt (by simpa using hball (hseg hw))).of_le (by simp))
    (fun w hw ↦ by
      rw [le_div_iff₀ hs, mul_comm, ← norm_sub_rev]
      exact D.mul_norm_mfderiv_symm_le hg hρ₁₀ hk x hcmp (hseg hw) (b - a))
  calc ENNReal.ofReal s * Manifold.riemannianEDist I (φ.symm a) (φ.symm b)
      ≤ ENNReal.ofReal s * ENNReal.ofReal (√(3 / 2) * ‖a - b‖ / s) := by gcongr
    _ = ENNReal.ofReal (√(3 / 2) * ‖a - b‖) := by
        rw [← ENNReal.ofReal_mul hs.le, mul_div_cancel₀ _ hs.ne']

/-- **Distances from the centre, bounded in the rescaled unitary charts.** Let `M` carry a
Riemannian metric whose inner product is `g_J(u, w) = σ(u, J w)`, let `k ≥ k₀`, let `x` be a
point, and let `ρ₁ ≤ ρ₀` be a comparison radius for `D.chart k x` (`IsComparisonRadius`), as
`exists_forall_isComparisonRadius` provides. For every `z` in the ball of
radius `ρ₁ * √k`, the Riemannian distance from `x` to the point
`(D.chart k x).symm z`, multiplied by `√(2π k)`, is at most `√(3 / 2) * ‖z‖`. -/
theorem rescaledEDist_symm_le
    (hg : ∀ (x : M) (u w : TangentSpace I x), inner ℝ u w = σ.eval₂ x u (J x w))
    {ρ₁ : ℝ} (hρ₁₀ : ρ₁ ≤ ρ₀)
    {k : ℕ} (hk : k₀ ≤ k) (x : M) (hcmp : D.IsComparisonRadius k x ρ₁)
    {z : StdSpace ι} (hz : z ∈ ball (0 : StdSpace ι) (ρ₁ * √k)) :
    rescaledEDist I k x ((D.chart k x).symm z) ≤ ENNReal.ofReal (√(3 / 2) * ‖z‖) := by
  have h := D.rescaledEDist_symm_symm_le hg hρ₁₀ hk x hcmp
    (mem_ball_self ((norm_nonneg z).trans_lt (mem_ball_zero_iff.1 hz))) hz
  rwa [D.chart_symm_zero hk x, zero_sub, norm_neg] at h

open scoped ENNReal NNReal in
/-- A step shared by the lower bounds for `d_k` below: a bound `a ≤ C · d(x, w)`, for `d` the
Riemannian distance, that holds for every nonzero `C` with which the chart `D.chart k x` satisfies
the hypotheses of
`PartialDiffeomorph.ofReal_norm_sub_le_mul_riemannianEDist` on the ball of radius `ρ₁ * √k`
gives `a / √2 ≤ d_k(x, w)`, the chart stretching `g_J`-norms by at most `√2 * √(2π k)` there
(`norm_mvfderiv_le_mul`). -/
private theorem ofReal_inv_sqrt_two_mul_le_of_forall
    (hg : ∀ (x : M) (u w : TangentSpace I x), inner ℝ u w = σ.eval₂ x u (J x w))
    {ρ₁ : ℝ} (hρ₁₀ : ρ₁ ≤ ρ₀)
    {k : ℕ} (hk : k₀ ≤ k) (hk0 : 0 < (k : ℝ)) (x : M) (hcmp : D.IsComparisonRadius k x ρ₁)
    {a : ℝ} {w : M}
    (h : ∀ C : ℝ≥0, C ≠ 0 → ball (D.chart k x x) (ρ₁ * √k) ⊆ (D.chart k x).target →
      (∀ y ∈ (D.chart k x).source, D.chart k x y ∈ ball (D.chart k x x) (ρ₁ * √k) →
        ∀ v : TangentSpace I y, ‖mvfderiv I (D.chart k x) y v‖ ≤ C * ‖v‖) →
      ENNReal.ofReal a ≤ C * Manifold.riemannianEDist I x w) :
    ENNReal.ofReal ((√2)⁻¹ * a) ≤ rescaledEDist I k x w := by
  rw [rescaledEDist_def]
  set d := Manifold.riemannianEDist I x w
  set s := √(2 * Real.pi * k)
  have hC := h (√2 * s).toNNReal (by rw [Ne, Real.toNNReal_eq_zero, not_le]; positivity)
    (by
      rw [D.apply_self hk x]
      exact (ball_subset_ball (mul_le_mul_of_nonneg_right hρ₁₀ (Real.sqrt_nonneg _))).trans
        (D.ball_subset_target hk x))
    (fun y hy hyB v ↦ by
      rw [D.apply_self hk x] at hyB
      rw [Real.coe_toNNReal _ (by positivity)]
      exact D.norm_mvfderiv_le_mul hg x hcmp hy hyB v)
  rw [ENNReal.ofNNReal_toNNReal] at hC
  calc ENNReal.ofReal ((√2)⁻¹ * a) = ENNReal.ofReal (√2)⁻¹ * ENNReal.ofReal a :=
        ENNReal.ofReal_mul (by positivity)
    _ ≤ ENNReal.ofReal (√2)⁻¹ * (ENNReal.ofReal (√2 * s) * d) := by gcongr
    _ = ENNReal.ofReal ((√2)⁻¹ * (√2 * s)) * d := by
        rw [ENNReal.ofReal_mul (p := (√2)⁻¹) (by positivity), mul_assoc (ENNReal.ofReal _)]
    _ = ENNReal.ofReal s * d := by
        rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

/-- **Rescaled distances bound chart distances from below.** Let `M` be Hausdorff, with a Riemannian
metric whose inner product is `⟪u, w⟫ = σ(u, J w)`, such as the metric `g_J` of a compatible pair
(`TauCeti.SmoothTwoForm.Compatible.inner_eq_eval₂`), let `k ≥ k₀`, let `x` be a point, and let
`ρ₁ ≤ ρ₀` be a comparison radius for `D.chart k x` (`IsComparisonRadius`), as
`exists_forall_isComparisonRadius` provides. For every `z` in the ball of
radius `ρ₁ * √k`, the rescaled distance `d_k = √(2π k) · d_{g_J}` from `x` to the
point `(D.chart k x).symm z` is at least `‖z‖ / √2`. -/
theorem ofReal_mul_norm_le_rescaledEDist_symm [T2Space M]
    (hg : ∀ (x : M) (u w : TangentSpace I x), inner ℝ u w = σ.eval₂ x u (J x w))
    {ρ₁ : ℝ} (hρ₁₀ : ρ₁ ≤ ρ₀)
    {k : ℕ} (hk : k₀ ≤ k) (x : M) (hcmp : D.IsComparisonRadius k x ρ₁)
    {z : StdSpace ι} (hz : z ∈ ball (0 : StdSpace ι) (ρ₁ * √k)) :
    ENNReal.ofReal ((√2)⁻¹ * ‖z‖) ≤ rescaledEDist I k x ((D.chart k x).symm z) := by
  have hR : 0 < ρ₁ * √k := (norm_nonneg z).trans_lt (mem_ball_zero_iff.1 hz)
  have hk0 : 0 < (k : ℝ) := Real.sqrt_pos.1
    (pos_of_mul_pos_right hR (pos_of_mul_pos_left hR (Real.sqrt_nonneg _)).le)
  refine D.ofReal_inv_sqrt_two_mul_le_of_forall hg hρ₁₀ hk hk0 x hcmp fun C hC0 hball hC ↦ ?_
  have h := (D.chart k x).ofReal_norm_sub_le_mul_riemannianEDist (by norm_cast)
    (D.mem_source hk x) hball hC0 hC (by rwa [D.apply_self hk x])
  rwa [D.apply_self hk x, sub_zero] at h

/-- **Rescaled distances compared with chart distances.** Let `M` be Hausdorff, with a Riemannian
metric whose inner product is `⟪u, w⟫ = σ(u, J w)`, such as the metric `g_J` of a compatible pair
(`TauCeti.SmoothTwoForm.Compatible.inner_eq_eval₂`), let `k ≥ k₀`, let `x` be a point, and let
`ρ₁ ≤ ρ₀` be a comparison radius for `D.chart k x` (`IsComparisonRadius`), as
`exists_forall_isComparisonRadius` provides. For every `z` in the ball of
radius `ρ₁ * √k`, the rescaled distance `d_k = √(2π k) · d_{g_J}` from `x` to the
point `(D.chart k x).symm z` lies between `‖z‖ / √2` and `√(3 / 2) * ‖z‖`. -/
theorem rescaledEDist_symm_mem_Icc [T2Space M]
    (hg : ∀ (x : M) (u w : TangentSpace I x), inner ℝ u w = σ.eval₂ x u (J x w))
    {ρ₁ : ℝ} (hρ₁₀ : ρ₁ ≤ ρ₀)
    {k : ℕ} (hk : k₀ ≤ k) (x : M) (hcmp : D.IsComparisonRadius k x ρ₁)
    {z : StdSpace ι} (hz : z ∈ ball (0 : StdSpace ι) (ρ₁ * √k)) :
    rescaledEDist I k x ((D.chart k x).symm z) ∈
      Set.Icc (ENNReal.ofReal ((√2)⁻¹ * ‖z‖)) (ENNReal.ofReal (√(3 / 2) * ‖z‖)) :=
  ⟨D.ofReal_mul_norm_le_rescaledEDist_symm hg hρ₁₀ hk x hcmp hz,
    D.rescaledEDist_symm_le hg hρ₁₀ hk x hcmp hz⟩

/-- The lower bound of `rescaledEDist_symm_mem_Icc` as a real inequality: under the
same hypotheses, `‖z‖ ≤ √2 * d_k(x, (D.chart k x).symm z)`, where the rescaled distance
`d_k = √(2π k) · d_{g_J}` is taken as a real number. -/
theorem norm_le_sqrt_two_mul_rescaledDist_symm [T2Space M]
    (hg : ∀ (x : M) (u w : TangentSpace I x), inner ℝ u w = σ.eval₂ x u (J x w))
    {ρ₁ : ℝ} (hρ₁₀ : ρ₁ ≤ ρ₀)
    {k : ℕ} (hk : k₀ ≤ k) (x : M) (hcmp : D.IsComparisonRadius k x ρ₁)
    {z : StdSpace ι} (hz : z ∈ ball (0 : StdSpace ι) (ρ₁ * √k)) :
    ‖z‖ ≤ √2 * rescaledDist I k x ((D.chart k x).symm z) := by
  rw [rescaledDist_def]
  obtain ⟨hlo, hhi⟩ := D.rescaledEDist_symm_mem_Icc hg hρ₁₀ hk x hcmp hz
  have h := (ENNReal.ofReal_le_iff_le_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hhi)).1 hlo
  have h2 : (0 : ℝ) < √2 := by positivity
  calc ‖z‖ = √2 * ((√2)⁻¹ * ‖z‖) := by rw [← mul_assoc, mul_inv_cancel₀ h2.ne', one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left h h2.le

/-- The upper bound of `rescaledEDist_symm_mem_Icc` as a real inequality: under the hypotheses of
`rescaledEDist_symm_le`, `d_k(x, (D.chart k x).symm z) ≤ √(3 / 2) * ‖z‖`, where the rescaled
distance `d_k = √(2π k) · d_{g_J}` is taken as a real number. -/
theorem rescaledDist_symm_le
    (hg : ∀ (x : M) (u w : TangentSpace I x), inner ℝ u w = σ.eval₂ x u (J x w))
    {ρ₁ : ℝ} (hρ₁₀ : ρ₁ ≤ ρ₀)
    {k : ℕ} (hk : k₀ ≤ k) (x : M) (hcmp : D.IsComparisonRadius k x ρ₁)
    {z : StdSpace ι} (hz : z ∈ ball (0 : StdSpace ι) (ρ₁ * √k)) :
    rescaledDist I k x ((D.chart k x).symm z) ≤ √(3 / 2) * ‖z‖ := by
  rw [rescaledDist_def]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity)
    (D.rescaledEDist_symm_le hg hρ₁₀ hk x hcmp hz)

/-- **Points far from the centre in the chart are far for `d_k`.** Let `M` be Hausdorff, with a
Riemannian metric whose inner product is `⟪u, w⟫ = σ(u, J w)`, let `k ≥ k₀`, let `x` be a point,
and let `ρ₁ ≤ ρ₀` be a comparison radius for `D.chart k x` (`IsComparisonRadius`). Every point
`y` that is not `(D.chart k x).symm z` for any `z` in the ball of radius `ρ₁ * √k` is at
rescaled distance `d_k = √(2π k) · d_{g_J}` at least `ρ₁ * √k / √2` from `x`. -/
theorem ofReal_le_rescaledEDist_of_notMem [T2Space M]
    (hg : ∀ (x : M) (u w : TangentSpace I x), inner ℝ u w = σ.eval₂ x u (J x w))
    {ρ₁ : ℝ} (hρ₁₀ : ρ₁ ≤ ρ₀)
    {k : ℕ} (hk : k₀ ≤ k) (x : M) (hcmp : D.IsComparisonRadius k x ρ₁)
    {y : M} (hy : y ∉ (D.chart k x).symm '' ball 0 (ρ₁ * √k)) :
    ENNReal.ofReal ((√2)⁻¹ * (ρ₁ * √k)) ≤ rescaledEDist I k x y := by
  rcases le_or_gt (ρ₁ * √k) 0 with hR | hR
  · rw [ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (by positivity) hR)]
    exact zero_le
  have hk0 : 0 < (k : ℝ) := Real.sqrt_pos.1
    (pos_of_mul_pos_right hR (pos_of_mul_pos_left hR (Real.sqrt_nonneg _)).le)
  have hy' : y ∉ (D.chart k x).source ∩ D.chart k x ⁻¹' ball (D.chart k x x) (ρ₁ * √k) := by
    rintro ⟨hys, hyB⟩
    rw [Set.mem_preimage, D.apply_self hk x] at hyB
    exact hy ⟨D.chart k x y, hyB, (D.chart k x).left_inv hys⟩
  exact D.ofReal_inv_sqrt_two_mul_le_of_forall hg hρ₁₀ hk hk0 x hcmp fun C hC0 hball hC ↦
    (D.chart k x).ofReal_le_mul_riemannianEDist_of_notMem (by norm_cast) (D.mem_source hk x)
      hball hC0 hC hy'

/-- **Points close to the centre for `d_k` lie in the rescaled chart.** Let `M` be Hausdorff,
with a Riemannian metric whose inner product is `⟪u, w⟫ = σ(u, J w)`, let `k ≥ k₀`, let `x` be a
point, and let `ρ₁ ≤ ρ₀` be a comparison radius for `D.chart k x` (`IsComparisonRadius`). If the
rescaled distance `d_k = √(2π k) · d_{g_J}` from `x` to `y` is less than `R`, with
`R ≤ ρ₁ * √k / √2`, then `y = (D.chart k x).symm z` for some `z` with `‖z‖ < √2 * R`. -/
theorem exists_norm_lt_symm_eq_of_rescaledEDist_lt [T2Space M]
    (hg : ∀ (x : M) (u w : TangentSpace I x), inner ℝ u w = σ.eval₂ x u (J x w))
    {ρ₁ : ℝ} (hρ₁₀ : ρ₁ ≤ ρ₀)
    {k : ℕ} (hk : k₀ ≤ k) (x : M) (hcmp : D.IsComparisonRadius k x ρ₁)
    {R : ℝ} (hRρ : R ≤ (√2)⁻¹ * (ρ₁ * √k)) {y : M}
    (hy : rescaledEDist I k x y < ENNReal.ofReal R) :
    ∃ z, ‖z‖ < √2 * R ∧ (D.chart k x).symm z = y := by
  by_cases hmem : y ∈ (D.chart k x).symm '' ball 0 (ρ₁ * √k)
  · obtain ⟨z, hz, rfl⟩ := hmem
    have h := (D.ofReal_mul_norm_le_rescaledEDist_symm hg hρ₁₀ hk x hcmp hz).trans_lt hy
    have hR : 0 < R := ENNReal.ofReal_pos.1 (zero_le.trans_lt h)
    rw [ENNReal.ofReal_lt_ofReal_iff hR] at h
    refine ⟨z, ?_, rfl⟩
    have h2 : (0 : ℝ) < √2 := by positivity
    calc ‖z‖ = √2 * ((√2)⁻¹ * ‖z‖) := by rw [← mul_assoc, mul_inv_cancel₀ h2.ne', one_mul]
      _ < √2 * R := by gcongr
  · exact absurd ((D.ofReal_le_rescaledEDist_of_notMem hg hρ₁₀ hk x hcmp
      hmem).trans_lt hy) (not_lt.2 (ENNReal.ofReal_le_ofReal hRρ))

end RiemannianEDist

end RescaledUnitaryCharts

end RescaledUnitaryCharts

end SymplecticGeometry

end
