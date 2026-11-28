/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Morse.GradientLike
public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.Chart
public import SymplecticGeometry.Geometry.Symplectic.Liouville.VectorField
import SymplecticGeometry.Analysis.Normed.Operator.Functional
import SymplecticGeometry.Geometry.Manifold.Morse.LocalCoordinates

/-!
# Two Liouville fields read in a chart of the maximal atlas

Let `σ` be a closed nondegenerate two-form on a manifold `M` modelled on a finite-dimensional
space `E`, let `X` be a smooth Liouville field of `σ` on `M`, and let `X'` be a smooth Liouville
field, on an open set `U ∋ p`, of the restriction of `σ` to `U`. Suppose that `X` and `X'` are
both gradient-like for a function `f` near `p`; for `X'` this is said of a field `Y` on `M` that
agrees with `X'` on `U`, such as its extension by zero. Read everything in a chart `e` of the
maximal atlas whose source contains `p`: `f̃ = f ∘ e.symm`, and `X̃`, `Ỹ` the fields pushed
forward by `de`.

Near `p`, `X' - X` is the Hamiltonian field of a function `H` with `H p = 0`
(`TauCeti.IsLiouvilleVectorField.exists_eval₂_sub_eq_mvfderiv_opens`). Read in the chart, this
says `Ỹ z - X̃ z = J z (D(H ∘ e.symm)_z)`, with `J = TauCeti.SmoothTwoForm.inverseFlatInChart σ e`
(`TauCeti.SmoothTwoForm.IsNondegenerate.mvfderiv_eq_inverseFlatInChart_fderiv`). On a small ball
around `e p`, `J` is bounded, and so is its inverse
(`TauCeti.SmoothTwoForm.IsNondegenerate.exists_ball_norm_inverseFlatInChart_le`), and both fields
satisfy the gradient-like inequality of the model space
(`TauCeti.IsGradientLikeAt.exists_mul_le_fderiv_comp_symm`). That inequality gives
`c ‖X̃ z‖ ≤ ‖Df̃_z‖` and `c ‖Ỹ z‖ ≤ ‖Df̃_z‖`
(`ContinuousLinearMap.mul_norm_le_opNorm_of_mul_le_apply`), and the bound on the inverse of `J`
turns this into `‖D(H ∘ e.symm)_z‖ ≤ K ‖Df̃_z‖`.

These are the estimates that the cut-off step in the proof of Lemma 12.9 of
[CieliebakEliashberg2012] needs, in any chart; in a Morse or birth–death chart the radial
control of the normal form turns the last one into a bound on `H ∘ e.symm` itself.

## Main results

* `TauCeti.IsLiouvilleVectorField.exists_ball_mvfderiv_sub_eq_inverseFlatInChart`: the
  gradient-like inequalities, the Hamiltonian reading of `Ỹ - X̃`, the bound on `J`, and the
  bound on the derivative of the Hamiltonian, on a ball around `e p`.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Lemma 12.9
-/

public section

open Set Metric TopologicalSpace
open scoped Manifold Topology ContDiff

namespace TauCeti.IsLiouvilleVectorField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- **Two Liouville fields read in a chart.** Let `σ` be a closed nondegenerate two-form on `M`,
`X` a smooth Liouville field of `σ`, gradient-like for `f` near `p`, and `X'` a smooth Liouville
field, on an open `U ∋ p`, of the restriction of `σ` to `U`. Let `Y` be a field on `M` equal to
`X'` on `U` and gradient-like for `f` near `p`, and let `e` be a chart of the maximal atlas whose
source contains `p`. Write `f̃ = f ∘ e.symm`, `X̃ z = de (X (e.symm z))`,
`Ỹ z = de (Y (e.symm z))` and `J = SmoothTwoForm.inverseFlatInChart σ e`.

Then there are `r₀ > 0`, `c > 0`, `B`, `K` and `H : M → ℝ`, smooth on `U`, with `H p = 0`, such
that the ball of radius `r₀` around `e p` lies in the chart target, `e.symm` maps it into `U`,
and at each of its points `z`, with `H̃ = H ∘ e.symm`:
* `c (‖X̃ z‖² + ‖Df̃_z‖²) ≤ Df̃_z (X̃ z)` and `c (‖Ỹ z‖² + ‖Df̃_z‖²) ≤ Df̃_z (Ỹ z)`;
* `Ỹ z - X̃ z = J z (DH̃_z)`;
* `‖J z‖ ≤ B`;
* `H̃` is differentiable at `z`, and `‖DH̃_z‖ ≤ K ‖Df̃_z‖`. -/
theorem exists_ball_mvfderiv_sub_eq_inverseFlatInChart {σ : SmoothTwoForm 𝓘(ℝ, E) M}
    (hσ : σ.IsClosed) (hσn : σ.IsNondegenerate) {f : M → ℝ}
    {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} (hX : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞ (T% X))
    (hXσ : IsLiouvilleVectorField σ.val X) {p : M} (hXf : IsGradientLikeAt f X p) {U : Opens M}
    (hp : p ∈ U) {X' : (x : U) → TangentSpace 𝓘(ℝ, E) x}
    (hX' : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞ (T% X'))
    (hX'σ : IsLiouvilleVectorField
      (SmoothForm.mpullback (Subtype.val : U → M) contMDiff_subtypeVal σ).val X')
    {Y : (x : M) → TangentSpace 𝓘(ℝ, E) x} (hYX' : ∀ x (hx : x ∈ U), Y x = X' ⟨x, hx⟩)
    (hYf : IsGradientLikeAt f Y p) {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) (hpe : p ∈ e.source) :
    ∃ r₀ > 0, ∃ c > 0, ∃ B K : ℝ, ∃ H : M → ℝ, ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞ H U ∧ H p = 0 ∧
      ball (e p) r₀ ⊆ e.target ∧ e.symm '' ball (e p) r₀ ⊆ U ∧ ∀ z ∈ ball (e p) r₀,
        c * (‖mvfderiv 𝓘(ℝ, E) e (e.symm z) (X (e.symm z))‖ ^ 2 +
            ‖fderiv ℝ (f ∘ e.symm) z‖ ^ 2) ≤
          fderiv ℝ (f ∘ e.symm) z (mvfderiv 𝓘(ℝ, E) e (e.symm z) (X (e.symm z))) ∧
        c * (‖mvfderiv 𝓘(ℝ, E) e (e.symm z) (Y (e.symm z))‖ ^ 2 +
            ‖fderiv ℝ (f ∘ e.symm) z‖ ^ 2) ≤
          fderiv ℝ (f ∘ e.symm) z (mvfderiv 𝓘(ℝ, E) e (e.symm z) (Y (e.symm z))) ∧
        mvfderiv 𝓘(ℝ, E) e (e.symm z) (Y (e.symm z)) -
            mvfderiv 𝓘(ℝ, E) e (e.symm z) (X (e.symm z)) =
          σ.inverseFlatInChart e z (fderiv ℝ (H ∘ e.symm) z) ∧
        ‖σ.inverseFlatInChart e z‖ ≤ B ∧
        DifferentiableAt ℝ (H ∘ e.symm) z ∧
        ‖fderiv ℝ (H ∘ e.symm) z‖ ≤ K * ‖fderiv ℝ (f ∘ e.symm) z‖ := by
  obtain ⟨V, hVU, hpV, H, hH, hHp, hdH⟩ := hXσ.exists_eval₂_sub_eq_mvfderiv_opens hσ hX hX' hX'σ hp
  obtain ⟨r₁, hr₁, c₁, hc₁, -, h₁⟩ := hXf.exists_mul_le_fderiv_comp_symm he hpe
  obtain ⟨r₂, hr₂, c₂, hc₂, -, h₂⟩ := hYf.exists_mul_le_fderiv_comp_symm he hpe
  have he₁ : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 1 M :=
    IsManifold.maximalAtlas_subset_of_le (by simp) he
  obtain ⟨r₃, hr₃, B, B', hr₃t, hB⟩ := hσn.exists_ball_norm_inverseFlatInChart_le he₁ hpe
  -- The points of the chart that `e.symm` maps into `V`, where `H` is the Hamiltonian.
  have hV : e.symm ⁻¹' V ∈ 𝓝 (e p) :=
    (e.continuousAt_symm (e.map_source hpe)).preimage_mem_nhds
      (by rw [e.left_inv hpe]; exact V.isOpen.mem_nhds hpV)
  obtain ⟨r₀, hr₀, hball⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem (Filter.inter_mem
    (Filter.inter_mem (ball_mem_nhds _ hr₁) (ball_mem_nhds _ hr₂)) (ball_mem_nhds _ hr₃)) hV)
  set c := min c₁ c₂
  have hc : 0 < c := lt_min hc₁ hc₂
  refine ⟨r₀, hr₀, c, hc, B, 2 * max B' 0 / c, H, hH, hHp, fun z hz ↦ hr₃t (hball hz).1.2,
    ?_, fun z hz ↦ ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact hVU (hball hz).2
  obtain ⟨⟨⟨hz₁, hz₂⟩, hz₃⟩, hzV⟩ := hball hz
  have hzt := hr₃t hz₃
  set x := e.symm z
  have hxU : x ∈ U := hVU hzV
  -- Shrinking the constant keeps the inequalities, whose right sides are at least the left.
  have hmono {c' : ℝ} (hc' : c ≤ c') {a b : ℝ} (hab : c' * a ≤ b) (ha : 0 ≤ a) : c * a ≤ b :=
    (mul_le_mul_of_nonneg_right hc' ha).trans hab
  have i₁ := hmono (min_le_left _ _) (h₁ z hz₁) (by positivity)
  have i₂ := hmono (min_le_right _ _) (h₂ z hz₂) (by positivity)
  -- The difference of the two fields, read in the chart, is the Hamiltonian field of `H`.
  have h₃ : mvfderiv 𝓘(ℝ, E) e x (Y x) - mvfderiv 𝓘(ℝ, E) e x (X x) =
      σ.inverseFlatInChart e z (fderiv ℝ (H ∘ e.symm) z) := by
    rw [← map_sub]
    refine hσn.mvfderiv_eq_inverseFlatInChart_fderiv he₁ hzt fun w ↦ ?_
    rw [SmoothBundleForm.eval₂_sub_left, hYX' x hxU]
    exact hdH x hzV w
  have hHd : DifferentiableAt ℝ (H ∘ e.symm) z :=
    (((hH.contMDiffAt (U.isOpen.mem_nhds hxU)).mdifferentiableAt (by simp)).comp z
      (mdifferentiableAt_symm_of_mem_maximalAtlas he₁ hzt)).differentiableAt
  refine ⟨i₁, i₂, h₃, (hB z hz₃).1, hHd, ?_⟩
  -- `c ‖X̃‖ ≤ ‖Df̃‖` and `c ‖Ỹ‖ ≤ ‖Df̃‖`, and `J` is bounded below.
  have n₁ := ContinuousLinearMap.mul_norm_le_opNorm_of_mul_le_apply i₁
  have n₂ := ContinuousLinearMap.mul_norm_le_opNorm_of_mul_le_apply i₂
  set ℓ := fderiv ℝ (H ∘ e.symm) z
  calc ‖ℓ‖ ≤ max B' 0 * ‖σ.inverseFlatInChart e z ℓ‖ :=
        ((hB z hz₃).2 ℓ).trans (by gcongr; exact le_max_left _ _)
    _ ≤ max B' 0 * (‖mvfderiv 𝓘(ℝ, E) e x (Y x)‖ + ‖mvfderiv 𝓘(ℝ, E) e x (X x)‖) := by
        rw [← h₃]
        gcongr
        exact norm_sub_le _ _
    _ ≤ max B' 0 * (2 * ‖fderiv ℝ (f ∘ e.symm) z‖ / c) := by
        gcongr
        rw [le_div_iff₀ hc]
        linarith
    _ = 2 * max B' 0 / c * ‖fderiv ℝ (f ∘ e.symm) z‖ := by ring

end TauCeti.IsLiouvilleVectorField

end
