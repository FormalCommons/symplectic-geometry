/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.Chart
public import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.TransAffine
public import SymplecticGeometry.Geometry.Symplectic.Manifold.Darboux
public import SymplecticGeometry.LinearAlgebra.Symplectic.UnitaryNormalForm

/-!
# Centred Darboux charts with uniform bounds

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
`J.chartPushforwardAt φ` on the compact set `φ '' K`; and the radius and derivative bounds that
`SmoothAlmostComplexStructure.exists_forall_norm_iteratedFDeriv_chartPushforward_transAffine_le`
gives for any family of recentred charts whose linear parts are bounded with their inverses.

On a compact manifold of dimension `2 * card ι` with `σ` closed, the structure
`CenteredDarbouxCharts σ J ι` collects such charts centred at every point, with one radius and one
bound for each order of derivative. They exist: Darboux charts into `StdSpace ι` at every point
(`TauCeti.SmoothTwoForm.IsSymplectic.exists_darbouxChart_stdForm`) give compact neighbourhoods of
every point on which the recentred charts have uniform bounds, finitely many of these cover `M`,
and the smallest of their radii and the largest of their bounds work for all centres.

## Main definitions

* `SymplecticGeometry.CenteredDarbouxCharts`: centred Darboux charts at every point of `M`, with
  derivative at the centre complex linear for `J`, one radius, and uniform bounds on the
  derivatives of `J` read in them.

## Main results

* `SymplecticGeometry.exists_transAffine_darbouxCharts_of_isCompact`: the recentred charts on a
  compact subset of the source of one Darboux chart, with the uniform radius and the uniform
  bounds.
* `SymplecticGeometry.nonempty_centeredDarbouxCharts`: centred Darboux charts with uniform bounds
  exist on a compact manifold.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Sections 2.5 and 3.2.
* [S. K. Donaldson, *Symplectic submanifolds and almost-complex geometry*][Donaldson1996].
-/

public section

open scoped Manifold ContDiff
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
    (J := fun p : φ.target ↦ J.chartPushforwardAt φ p.property) finrank_stdSpace hLX
    (J.continuous_toContinuousLinearMap_chartPushforwardAt φ).continuousOn
    fun p _ ↦ J.compatible_chartPushforwardAt hJ φ hφ p.property
  have hex (x : M) : ∃ Ψ : StdSpace ι ≃L[ℝ] StdSpace ι, x ∈ K →
      IsSymplectomorphism (stdForm ι) (stdForm ι) Ψ.toLinearEquiv ∧
      (∀ w, Ψ (stdComplexStructure ι w) =
        J.chartPushforward φ.toOpenPartialHomeomorph (φ x) (Ψ w)) ∧
      ‖(Ψ : StdSpace ι →L[ℝ] StdSpace ι)‖ ≤ C₁ ∧
      ‖(Ψ.symm : StdSpace ι →L[ℝ] StdSpace ι)‖ ≤ C₁ := by
    by_cases hx : x ∈ K
    · obtain ⟨Ψ, h₁, h₂, h₃, h₄⟩ := hC₁ ⟨φ x, φ.map_source (hKφ hx)⟩ (Set.mem_image_of_mem φ hx)
      refine ⟨Ψ, fun _ ↦ ⟨h₁, fun w ↦ ?_, h₃, h₄⟩⟩
      simpa [SmoothAlmostComplexStructure.chartPushforwardAt_apply] using LinearMap.congr_fun h₂ w
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

/-- **Centred Darboux charts with uniform bounds.** On a compact boundaryless manifold `M` of
dimension `2 * card ι`, with a closed two-form `σ` and a smooth almost complex structure `J`
compatible with `σ`, there are centred Darboux charts into `StdSpace ι` with one radius and
uniform bounds on the derivatives of `J` read in them. -/
theorem nonempty_centeredDarbouxCharts [FiniteDimensional ℝ E] [CompactSpace M]
    (hE : Module.finrank ℝ E = 2 * Fintype.card ι) {σ : SmoothTwoForm I M} (hσ : σ.IsClosed)
    {J : SmoothAlmostComplexStructure I M} (hJ : σ.Compatible J) :
    Nonempty (CenteredDarbouxCharts σ J ι) := by
  classical
  have := Manifold.locallyCompact_of_finiteDimensional (M := M) I
  -- A Darboux chart `φ p` at every point `p`, and a compact neighbourhood `K p` of `p` in its
  -- source, on which the charts recentred from `φ p` have uniform bounds.
  choose φ hpφ hφ using fun p ↦
    SmoothTwoForm.IsSymplectic.exists_darbouxChart_stdForm hE ⟨hσ, hJ.isNondegenerate⟩ p
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
  exact ⟨{
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
      (hB r (Finset.mem_image_of_mem _ (hct x))) }⟩

end SymplecticGeometry

end
