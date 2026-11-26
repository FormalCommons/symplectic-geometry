/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DeRham.GoodCover.Basic
import SymplecticGeometry.Geometry.Manifold.Immersion.TangentProjection
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Geometry.Manifold.WhitneyEmbedding
import SymplecticGeometry.Analysis.Convex.Deriv

/-!
# Finite good covers of compact manifolds

Every compact Hausdorff boundaryless smooth manifold `M`, modelled on a finite-dimensional space,
has a finite good cover
(`SymplecticGeometry.hasFiniteGoodCover_of_compactSpace`). We follow Weil's construction of convex
covers [Weil1952, §1]. Embed `M` in a Euclidean space by `e` (Mathlib's
`exists_embedding_euclidean_of_compact`), and read `M` near each point `x` in the uniform tangent
projection chart `Φₓ` of `exists_uniform_tangentProjectionChart`. For a small radius `r`, the
squared distance `u ↦ ‖e (Φₓ⁻¹ u) - e y‖ ^ 2` to a point `e y` near `e x` is strictly convex on
the ball of radius `r` of the chart
(`SymplecticGeometry.strictConvexOn_dist_sq_tangentProjectionChart`):
with `ψ = e ∘ Φₓ⁻¹`, its second derivative along `v` is
`2 ‖Dψ v‖ ^ 2 + 2 ⟪ψ u - e y, D²ψ v v⟫`. The first term is at least `2 ‖v‖ ^ 2`, since the chart
projects `e` onto its tangent space; the second is small, as `‖ψ u - e y‖` is small and the second
derivatives of `ψ` are bounded uniformly.

Cover `M` by finitely many sets `e⁻¹' B(e xᵢ, r / 2)`. A nonempty intersection of some of them lies
in the source of the chart at one of their centres, which carries it onto the intersection of
sublevel sets of convex functions on a ball, a convex set; so it is smoothly contractible, by
`SymplecticGeometry.IsSmoothlyContractible.of_starConvex_image`.

## Main results

* `SymplecticGeometry.strictConvexOn_dist_sq_tangentProjectionChart`
* `SymplecticGeometry.hasFiniteGoodCover_of_compactSpace`

## References

* [A. Weil, *Sur les théorèmes de de Rham*][Weil1952], §1, pp. 120–122
-/

public section

open Set Function Metric Filter Topology TopologicalSpace
open scoped Manifold ContDiff

namespace SymplecticGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] {e : M → F}

omit [IsManifold I ∞ M] [BoundarylessManifold I M] in
/-- The convexity estimate in one chart. Let `Φ` be a partial diffeomorphism given on its source
by `z ↦ P (e z - e x)`, whose target contains the ball of radius `r`, and on whose target the first
and second derivatives of `e ∘ Φ⁻¹` are bounded by `L` and `K`, with `(L + 1) * r * K < 1`. Then
`u ↦ ‖e (Φ⁻¹ u) - e y‖ ^ 2` is strictly convex on that ball for every `y` with
`‖e y - e x‖ < r`. -/
private theorem strictConvexOn_dist_sq_of_norm_iteratedFDeriv_le (he : ContMDiff I 𝓘(ℝ, F) ∞ e)
    {x : M} {Φ : PartialDiffeomorph I 𝓘(ℝ, (mvfderiv I e x).range) M (mvfderiv I e x).range ∞}
    (hΦ : ∀ z ∈ Φ.source, Φ z = (mvfderiv I e x).range.orthogonalProjectionOnto (e z - e x))
    (hx : x ∈ Φ.source) {r L K : ℝ} (hr : 0 < r) (htgt : ball 0 r ⊆ Φ.target) (hL : 0 ≤ L)
    (hL₁ : ∀ u ∈ Φ.target, ‖iteratedFDeriv ℝ 1 (e ∘ Φ.symm) u‖ ≤ L)
    (hK₂ : ∀ u ∈ Φ.target, ‖iteratedFDeriv ℝ 2 (e ∘ Φ.symm) u‖ ≤ K) (hrK : (L + 1) * r * K < 1)
    {y : M} (hy : dist (e y) (e x) < r) :
    StrictConvexOn ℝ (ball 0 r) fun u ↦ dist (e (Φ.symm u)) (e y) ^ 2 := by
  set ψ := e ∘ Φ.symm
  have hψ : ContDiffOn ℝ ∞ ψ Φ.target :=
    contMDiffOn_iff_contDiffOn.1 (he.comp_contMDiffOn Φ.symm.contMDiffOn)
  have hψ0 : ψ 0 = e x := by
    have h : Φ x = 0 := by rw [hΦ x hx, sub_self, map_zero]
    have h' : Φ.symm (Φ x) = x := Φ.left_inv hx
    rw [h] at h'
    simp only [ψ, comp_apply, h']
  -- On the ball, `e ∘ Φ⁻¹` stays within `(L + 1) * r` of `e y`.
  have hnear : ∀ u ∈ ball (0 : (mvfderiv I e x).range) r, ‖ψ u - e y‖ < (L + 1) * r := by
    intro u hu
    have hlip : ‖ψ u - ψ 0‖ ≤ L * ‖u - 0‖ :=
      (convex_ball 0 r).norm_image_sub_le_of_norm_fderiv_le
        (fun w hw ↦ (hψ.contDiffAt (Φ.open_target.mem_nhds (htgt hw))).differentiableAt
          (by simp))
        (fun w hw ↦ by rw [← norm_iteratedFDeriv_one]; exact hL₁ w (htgt hw))
        (mem_ball_self hr) hu
    rw [hψ0, sub_zero] at hlip
    calc ‖ψ u - e y‖ ≤ ‖ψ u - e x‖ + ‖e x - e y‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < L * r + r := by
          rw [← dist_eq_norm (e x), dist_comm]
          exact add_lt_add_of_le_of_lt
            (hlip.trans (mul_le_mul_of_nonneg_left (mem_ball_zero_iff.1 hu).le hL)) hy
      _ = (L + 1) * r := by ring
  have h₂ : ∀ u ∈ ball (0 : (mvfderiv I e x).range) r,
      ‖ψ u - e y‖ * ‖iteratedFDeriv ℝ 2 ψ u‖ < 1 := fun u hu ↦
    calc ‖ψ u - e y‖ * ‖iteratedFDeriv ℝ 2 ψ u‖ ≤ (L + 1) * r * K := by
          gcongr
          exacts [(hnear u hu).le, hK₂ u (htgt hu)]
      _ < 1 := hrK
  have h := (hψ.of_le (by simp)).mono htgt |>.strictConvexOn_norm_sub_sq (convex_ball 0 r)
    isOpen_ball (e y) (fun u hu ↦ norm_le_norm_fderiv_comp_symm_apply _ (by simp) he hΦ (htgt hu))
    h₂
  simpa only [ψ, comp_apply, dist_eq_norm] using h

/-- **Convexity of squared distances in tangent projection charts.** Let `e : M → F` be a smooth
injective map with injective differentials from a compact boundaryless manifold into a real inner
product space. There is `r > 0` such that, for every `x : M`, some partial diffeomorphism `Φ`
from `M` onto an open subset of the range `T` of the differential of `e` at `x`

* is given on its source by `z ↦ P (e z - e x)`, for `P` the orthogonal projection onto `T`, as
  `tangentProjectionChart` is;
* has a source containing every `z` with `‖e z - e x‖ < r`, and a target containing the ball of
  radius `r` around `0`;
* makes `u ↦ ‖e (Φ⁻¹ u) - e y‖ ^ 2` strictly convex on that ball, for every `y` with
  `‖e y - e x‖ < r`. -/
theorem strictConvexOn_dist_sq_tangentProjectionChart [CompactSpace M]
    (he : ContMDiff I 𝓘(ℝ, F) ∞ e) (hinj : ∀ x, Injective (mfderiv I 𝓘(ℝ, F) e x))
    (he' : Injective e) :
    ∃ r > 0, ∀ x : M,
      ∃ Φ : PartialDiffeomorph I 𝓘(ℝ, (mvfderiv I e x).range) M (mvfderiv I e x).range ∞,
        (∀ z ∈ Φ.source, Φ z = (mvfderiv I e x).range.orthogonalProjectionOnto (e z - e x)) ∧
        {z | dist (e z) (e x) < r} ⊆ Φ.source ∧ ball 0 r ⊆ Φ.target ∧
        ∀ y, dist (e y) (e x) < r →
          StrictConvexOn ℝ (ball 0 r) fun u ↦ dist (e (Φ.symm u)) (e y) ^ 2 := by
  obtain ⟨r₁, hr₁, C, hC⟩ := exists_uniform_tangentProjectionChart he hinj he'
  -- Bounds for the first and second derivatives of `e ∘ Φ⁻¹`, and the radius.
  set L := max (C 1) 0
  set K := max (C 2) 1
  set r := min r₁ (1 / (2 * (L + 1) * K))
  have hr : 0 < r := lt_min hr₁ (by positivity)
  have hrK : (L + 1) * r * K < 1 := by
    have h := (le_div_iff₀ (by positivity)).1 (min_le_right r₁ (1 / (2 * (L + 1) * K)))
    linarith
  refine ⟨r, hr, fun x ↦ ?_⟩
  obtain ⟨Φ, hΦ, hsrc, htgt, hbd⟩ := hC x
  have hsrc' : {z | dist (e z) (e x) < r} ⊆ Φ.source := fun z hz ↦
    hsrc (mem_ofPred_eq ▸ lt_of_lt_of_le hz (min_le_left _ _))
  have htgt' : ball 0 r ⊆ Φ.target := (ball_subset_ball (min_le_left _ _)).trans htgt
  exact ⟨Φ, hΦ, hsrc', htgt', fun y hy ↦
    strictConvexOn_dist_sq_of_norm_iteratedFDeriv_le he hΦ (hsrc' (by simpa using hr)) hr htgt'
      (le_max_right _ _) (fun u hu ↦ (hbd u hu 1).trans (le_max_left _ _))
      (fun u hu ↦ (hbd u hu 2).trans (le_max_left _ _)) hrK hy⟩

omit [IsManifold I ∞ M] [BoundarylessManifold I M] in
/-- The image of an intersection of balls in one chart. Let `Φ` be a partial diffeomorphism given
on its source by `z ↦ P (e z - e x)`, defined on every `z` with `‖e z - e x‖ < r` and reaching the
ball of radius `r`. If `0 ≤ ρ < r` and `x` is one of the centres `p i`, `i ∈ s`, then `Φ` carries
the set of points `z` with `‖e z - e (p i)‖ < ρ` for all `i ∈ s` onto the set of points `u` of the
ball of radius `r` with `‖e (Φ⁻¹ u) - e (p i)‖ ^ 2 < ρ ^ 2` for all `i ∈ s`. -/
private theorem image_setOfPred_forall_dist_lt {ι : Type*} {x : M}
    {Φ : PartialDiffeomorph I 𝓘(ℝ, (mvfderiv I e x).range) M (mvfderiv I e x).range ∞}
    (hΦ : ∀ z ∈ Φ.source, Φ z = (mvfderiv I e x).range.orthogonalProjectionOnto (e z - e x))
    {r ρ : ℝ} (hsrc : {z | dist (e z) (e x) < r} ⊆ Φ.source) (htgt : ball 0 r ⊆ Φ.target)
    (hρ : 0 ≤ ρ) (hρr : ρ < r) {p : ι → M} {s : Finset ι} {j : ι} (hj : j ∈ s) (hpj : p j = x) :
    Φ '' {z | ∀ i ∈ s, dist (e z) (e (p i)) < ρ} =
      ⋂ i ∈ s, {u ∈ ball 0 r | dist (e (Φ.symm u)) (e (p i)) ^ 2 < ρ ^ 2} := by
  subst hpj
  ext u
  simp only [mem_iInter₂, mem_ofPred_eq, mem_image]
  constructor
  · rintro ⟨z, hz, rfl⟩ i hi
    have hzs : z ∈ Φ.source := hsrc ((hz j hj).trans hρr)
    refine ⟨?_, ?_⟩
    · rw [mem_ball_zero_iff, hΦ z hzs]
      exact (Submodule.norm_orthogonalProjectionOnto_apply_le _ _).trans_lt
        (by rw [← dist_eq_norm]; exact (hz j hj).trans hρr)
    · rw [PartialDiffeomorph.symm_toPartialEquiv, Φ.left_inv hzs]
      exact pow_lt_pow_left₀ (hz i hi) dist_nonneg two_ne_zero
  · intro h
    refine ⟨Φ.symm u, fun i hi ↦ ?_, Φ.right_inv (htgt (h j hj).1)⟩
    exact (pow_lt_pow_iff_left₀ dist_nonneg hρ two_ne_zero).1 (h i hi).2

/-- **Finite good covers of compact manifolds.** A compact Hausdorff boundaryless smooth manifold,
modelled on a finite-dimensional real normed space, has a finite good cover. -/
theorem hasFiniteGoodCover_of_compactSpace [CompactSpace M] [T2Space M] :
    HasFiniteGoodCover I M := by
  obtain ⟨N, e, he, hemb, hinj⟩ := exists_embedding_euclidean_of_compact (I := I) (M := M)
  obtain ⟨r, hr, hΦ⟩ := strictConvexOn_dist_sq_tangentProjectionChart he hinj hemb.injective
  choose Φ hΦ hsrc htgt hconv using hΦ
  set ρ := r / 2
  have hρ : 0 < ρ := half_pos hr
  -- The cover by the preimages of the balls of radius `ρ`.
  let V : M → Opens M := fun x ↦ ⟨e ⁻¹' ball (e x) ρ, isOpen_ball.preimage he.continuous⟩
  have hV : ∀ x z, z ∈ V x ↔ dist (e z) (e x) < ρ := fun _ _ ↦ Iff.rfl
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ (V x : Set M))
    (fun x ↦ (V x).isOpen) fun z _ ↦ mem_iUnion.2 ⟨z, (hV z z).2 (by simpa using hρ)⟩
  refine IsFiniteGoodCover.hasFiniteGoodCover (ι := t) (U := fun i ↦ V i)
    ((isFiniteGoodCover_def _).2 ⟨?_, fun s hs hne ↦ ?_⟩)
  · refine eq_top_iff.2 fun z _ ↦ ?_
    obtain ⟨i, hi, hz⟩ := mem_iUnion₂.1 (ht (mem_univ z))
    exact Opens.mem_iSup.2 ⟨⟨i, hi⟩, hz⟩
  set W : Opens M := ⨅ i ∈ s, V i
  have hW : ∀ z, z ∈ W ↔ ∀ i ∈ s, dist (e z) (e (i : M)) < ρ := fun z ↦ by
    rw [← SetLike.mem_coe]
    simp_rw [W, Opens.coe_iInf, mem_iInter, SetLike.mem_coe]
    refine forall_congr' fun i ↦ ?_
    by_cases hi : i ∈ s
    · simp [hi, hV]
    · simp [hi]
  obtain ⟨j, hj⟩ := hs
  obtain ⟨z₀, hz₀⟩ := hne
  set x : M := (j : M)
  -- Every centre is within `r` of `x`, and `W` lies in the source of the chart at `x`.
  have hcentre : ∀ i ∈ s, dist (e i) (e x) < r := fun i hi ↦
    calc dist (e i) (e x) ≤ dist (e z₀) (e i) + dist (e z₀) (e x) := dist_triangle_left _ _ _
      _ < ρ + ρ := add_lt_add ((hW z₀).1 hz₀ i hi) ((hW z₀).1 hz₀ j hj)
      _ = r := add_halves r
  have hWsrc : (W : Set M) ⊆ (Φ x).source := fun z hz ↦
    hsrc x ((hW z).1 hz j hj |>.trans (half_lt_self hr))
  -- The chart carries `W` onto an intersection of sublevel sets of convex functions.
  have hconvex : Convex ℝ (Φ x '' W) := by
    rw [show (W : Set M) = {z | ∀ i ∈ s, dist (e z) (e (i : M)) < ρ} from Set.ext hW,
      image_setOfPred_forall_dist_lt (hΦ x) (hsrc x) (htgt x) hρ.le (half_lt_self hr) hj rfl]
    exact convex_iInter₂ fun i hi ↦ (hconv x i (hcentre i hi)).convexOn.convex_lt _
  have hWne : (Φ x '' W).Nonempty := ⟨_, mem_image_of_mem _ hz₀⟩
  exact IsSmoothlyContractible.of_starConvex_image ((Φ x).contMDiffOn.mono hWsrc)
    ((Φ x).symm.contMDiffOn.mono (image_subset_iff.2 fun z hz ↦ (Φ x).map_source (hWsrc hz)))
    (fun z hz ↦ (Φ x).left_inv (hWsrc hz)) (hconvex.starConvex hWne.some_mem) ⟨z₀, hz₀⟩

end SymplecticGeometry

end
