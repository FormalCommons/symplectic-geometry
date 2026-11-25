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

The uniformity comes from three inputs: the uniform bound on the normal forms,
`SymplecticGeometry.exists_forall_isSymplectomorphism_stdForm_norm_le`, applied to the structures
`J.chartPushforwardAt φ` on the compact set `φ '' K`; a closed thickening of `φ '' K` that is
still compact and in the target of `φ`, on which the derivatives of `J` read in `φ` are bounded;
and the bound `norm_iteratedFDeriv_chartPushforward_transAffine_le` for the recentred charts.

## Main results

* `SymplecticGeometry.exists_centeredDarbouxCharts_of_isCompact`: the recentred charts, with the
  uniform radius and the uniform bounds.

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

/-- **Centred Darboux charts with uniform bounds.** Let `J` be a smooth almost complex structure
compatible with the two-form `σ` on a boundaryless manifold `M`, and `φ` a smooth chart of `M`
into `StdSpace ι` that pulls `stdForm ι` back to `σ`. Let `K` be a compact subset of the source of
`φ`. Then there are linear symplectomorphisms `A x` of `(StdSpace ι, stdForm ι)`, for `x : M`, with
`‖A x‖` and `‖(A x)⁻¹‖` bounded on `K`, and a radius `ρ > 0`, such that for every `x ∈ K` the
chart `ψ x := φ.transAffine (φ x) (A x)`, which is `φ` followed by `z ↦ A x (z - φ x)`,
* contains `x` in its source and sends it to `0`;
* contains the ball of radius `ρ` about `0` in its target;
* pulls `stdForm ι` back to `σ` on its source;
* reads `J` at `0` as `stdComplexStructure ι`;

and for every `r` the `r`-th iterated derivatives of `J` read in the charts `ψ x` are bounded on
that ball, uniformly in `x ∈ K`. -/
theorem exists_centeredDarbouxCharts_of_isCompact {σ : SmoothTwoForm I M}
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
  -- The compact set `φ '' K` and a closed thickening of it inside the target of `φ`.
  have hLc : IsCompact (φ '' K) := hK.image_of_continuousOn (φ.contMDiffOn.continuousOn.mono hKφ)
  have hLt : φ '' K ⊆ φ.target := Set.image_subset_iff.2 fun x hx ↦ φ.map_source (hKφ hx)
  obtain ⟨δ, hδ, hδt⟩ := hLc.exists_cthickening_subset_open φ.open_target hLt
  -- Unitary normal forms of `J` read in `φ`, with norms bounded on `φ '' K`.
  have hLX : IsCompact ((↑) ⁻¹' (φ '' K) : Set φ.target) := by
    rwa [Subtype.isCompact_iff, Subtype.image_preimage_coe, Set.inter_eq_right.2 hLt]
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
      have h := LinearMap.congr_fun (show _ = _ from h₂) w
      simpa [SmoothAlmostComplexStructure.chartPushforwardAt_apply] using h
    · exact ⟨ContinuousLinearEquiv.refl ℝ _, fun h ↦ absurd h hx⟩
  choose Ψ hΨ using hex
  set C₀ := max C₁ 1
  have hC₀ : 0 < C₀ := lt_max_of_lt_right one_pos
  have hρ : 0 < δ / C₀ := div_pos hδ hC₀
  -- The points `Ψ x z + φ x`, for `z` in the ball, lie in the thickening.
  have hmem : ∀ x ∈ K, ∀ z ∈ ball (0 : StdSpace ι) (δ / C₀),
      Ψ x z + φ x ∈ cthickening δ (φ '' K) := fun x hx z hz ↦ by
    refine closedBall_subset_cthickening (Set.mem_image_of_mem φ hx) δ ?_
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_right]
    rw [mem_ball_zero_iff] at hz
    calc ‖Ψ x z‖ ≤ ‖(Ψ x : StdSpace ι →L[ℝ] StdSpace ι)‖ * ‖z‖ :=
          (Ψ x : StdSpace ι →L[ℝ] StdSpace ι).le_opNorm z
      _ ≤ C₀ * (δ / C₀) := by
          gcongr
          · exact ((hΨ x hx).2.2.1).trans (le_max_left _ _)
      _ = δ := mul_div_cancel₀ δ hC₀.ne'
  have hball : ∀ x ∈ K, ball 0 (δ / C₀) ⊆ (φ.transAffine (φ x) (Ψ x).symm).target :=
    fun x hx z hz ↦ by
      rw [PartialDiffeomorph.mem_transAffine_target_iff, ContinuousLinearEquiv.symm_symm]
      exact hδt (hmem x hx z hz)
  refine ⟨fun x ↦ (Ψ x).symm, C₀, δ / C₀, hρ, fun x hx ↦ ?_, fun r ↦ ?_⟩
  · obtain ⟨h₁, h₂, h₃, h₄⟩ := hΨ x hx
    have hA : IsSymplectomorphism (stdForm ι) (stdForm ι) (Ψ x).symm.toLinearEquiv := by
      rw [ContinuousLinearEquiv.toLinearEquiv_symm]
      exact h₁.symm
    refine ⟨hA, h₄.trans (le_max_left _ _), ?_, by simpa using hKφ hx, by simp, hball x hx,
      fun y hy v w ↦
        SmoothTwoForm.transAffine_darbouxChart hφ (φ x) hA y (by simpa using hy) v w, fun w ↦ ?_⟩
    · rw [ContinuousLinearEquiv.symm_symm]
      exact h₃.trans (le_max_left _ _)
    · rw [J.chartPushforward_transAffine φ _ _ (hball x hx (mem_ball_self hρ))]
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
        ContinuousLinearEquiv.symm_symm, map_zero, zero_add, ← h₂,
        ContinuousLinearEquiv.symm_apply_apply]
  · -- The derivatives of `J` read in `φ` are bounded on the compact thickening.
    have hcont : ContinuousOn (iteratedFDeriv ℝ r (J.chartPushforward φ.toOpenPartialHomeomorph))
        φ.toOpenPartialHomeomorph.target :=
      ((J.contDiffOn_chartPushforward (ψ := φ.toOpenPartialHomeomorph) φ.contMDiffOn
        φ.symm.contMDiffOn).continuousOn_iteratedFDerivWithin
        (by exact_mod_cast le_top) φ.open_target.uniqueDiffOn).congr
        (iteratedFDerivWithin_of_isOpen r φ.open_target).symm
    obtain ⟨B, hB⟩ := hLc.cthickening.exists_bound_of_continuousOn (hcont.mono hδt)
    refine ⟨C₀ * C₀ ^ (r + 1) * max B 0, fun x hx z hz ↦ ?_⟩
    obtain ⟨-, -, h₃, h₄⟩ := hΨ x hx
    refine (J.norm_iteratedFDeriv_chartPushforward_transAffine_le φ _ _ r
      (hball x hx hz)).trans ?_
    rw [ContinuousLinearEquiv.symm_symm]
    gcongr
    · exact h₄.trans (le_max_left _ _)
    · exact h₃.trans (le_max_left _ _)
    · exact (hB _ (hmem x hx z hz)).trans (le_max_left _ _)

end SymplecticGeometry

end
