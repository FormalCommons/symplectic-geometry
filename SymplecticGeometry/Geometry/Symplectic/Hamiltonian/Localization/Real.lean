/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Equivariant.Localization
public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.Localization.LocalizingForm

/-!
# The Duistermaat–Heckman formula for real `ħ`

Let the circle act on a compact symplectic manifold `(M, σ)` with a moment map, `X` the
fundamental vector field of the period-one generator `ξ₁` and `H = ⟨μ, ξ₁⟩`. This file computes
the integrals that the Duistermaat–Heckman formula for real `ħ` is assembled from.

* `SymplecticGeometry.IsWeightChart.integralTopForm_mul_formCalculus_exp`: near a fixed point
  `p`, the form `e^{σ - ħH} = formCalculus Real.exp _ (-ħ • H) σ` contributes only the constant
  `e^{-ħ H(p)}`. If `Φ` is a weight chart at `p` of radius `r` and `γ` is an equivariantly closed
  form that vanishes outside `Φ '' closedBall 0 a` for some `a < r`, then the top components of
  `γ e^{σ - ħH}` and of `e^{-ħ H(p)} γ` have the same integral.

The proof is that of Berline, Getzler and Vergne, §7.2. In the chart, `θ₀ = weightOneForm (1/2)`
has `dθ₀ = σ` and `θ₀(X) = H - H(p)`, so `e^{σ - ħH} = e^{-ħH(p)} exp(d_ħ θ₀)` there. Since `θ₀`
lives only on the chart, it is cut off by an invariant cut-off that is `1` near the support of
`γ` (`SymplecticGeometry.exists_smul_invariant_cutoff_weightChart`,
`SymplecticGeometry.cutoffWeightOneForm`); the cut-off form is invariant, so has zero Lie
derivative along `X`, and `SymplecticGeometry.integralTopForm_mul_formCalculus_exp_of_forall_or`
removes the factor `exp(d_ħ θ₀)`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §5.6
* N. Berline, E. Getzler and M. Vergne, *Heat Kernels and Dirac Operators*, Grundlehren der
  mathematischen Wissenschaften 298, Springer, 1992, §7.2
-/

public section

noncomputable section

open Set Metric Real
open scoped Manifold ContDiff Topology DirectSum

namespace SymplecticGeometry

open TauCeti

variable {E H' M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'} [TopologicalSpace M] [ChartedSpace H' M]
  [I.Boundaryless] [IsManifold I ∞ M] [CompactSpace M] [T2Space M]
  [MulAction Circle M] [ContMDiffSMul (𝓡 1) I ∞ Circle M]

namespace IsWeightChart

/-- **The factor `e^{σ - ħH}` near a fixed point.** Let the circle act smoothly on a compact
boundaryless manifold `M`, with `X` the fundamental vector field of the period-one generator
`ξ₁ = circlePeriodOneGenerator`, and let `Φ` be a weight chart of radius `r` at `p` for a
two-form `σ` and a map `μ`, with `H = ⟨μ, ξ₁⟩`. Let `γ` be a form of mixed degree with
`d_ħ γ = 0` whose components all vanish outside `Φ '' closedBall 0 a`, for some `a < r`. Then
for every orientation `o` of `M`, the top component of `γ e^{σ - ħH}`, where
`e^{σ - ħH} = formCalculus Real.exp _ (-ħ • H) σ`, has integral `e^{-ħ H(p)}` times the
integral of the top component of `γ`. -/
theorem integralTopForm_mul_formCalculus_exp {σ : SmoothTwoForm I M}
    {μ : M → Module.Dual ℝ (GroupLieAlgebra (𝓡 1) Circle)} {p : M} {n : ℕ}
    {χ : Fin n → Circle →ₜ* Circle} {α : Fin n → StrongDual ℝ (EuclideanSpace ℝ (Fin 1))}
    {Φ : PartialDiffeomorph 𝓘(ℝ, StdSpace (Fin n)) I (StdSpace (Fin n)) M ∞} {r : ℝ}
    (hΦ : IsWeightChart σ μ p χ α Φ r) {H : C^∞⟮I, M; ℝ⟯}
    (hH : ∀ x, H x = μ x circlePeriodOneGenerator)
    {hX : ContMDiff I I.tangent ∞ fun x ↦
      (⟨x, fundamentalVectorField I circlePeriodOneGenerator x⟩ : TangentBundle I M)}
    {ħ : ℝ} {γ : ⨁ k, SmoothForm I M ℝ k}
    (hγ : cartanDiff (fundamentalVectorField I circlePeriodOneGenerator) hX ħ γ = 0) {a : ℝ}
    (har : a < r) (hγa : ∀ x ∉ Φ '' closedBall 0 a, ∀ i, (γ i).val x = 0) {m : ℕ}
    (o : Manifold.Orientation I M (Fin m)) :
    integralTopForm o ((γ * formCalculus Real.exp Real.contDiff_exp (-ħ • H) σ) m).val =
      Real.exp (-ħ * H p) * integralTopForm o (γ m).val := by
  -- An invariant cut-off `ρ` that is `1` on `Φ '' closedBall 0 a'`, for `a < a' < r`.
  set a' := (max a 0 + r) / 2
  have hr := hΦ.radius_pos
  have ha' : max a 0 < a' := by have := max_lt har hr; simp only [a']; linarith
  have ha'r : a' < r := by have := max_lt har hr; simp only [a']; linarith
  obtain ⟨ρ, hρ, -, hρinv, hρ1, hρs⟩ := exists_smul_invariant_cutoff_weightChart
    (fun j g ↦ χ j g) Φ hΦ.equivariant (a := a') (b := (a' + r) / 2) (by positivity)
    (by linarith) (by rw [hΦ.source_eq]; exact closedBall_subset_ball (by linarith))
  have hs : tsupport ρ ⊆ Φ.target := hρs.trans fun _ ⟨z, hz, hzx⟩ ↦ hzx ▸ Φ.map_source
    (by rw [hΦ.source_eq]; exact closedBall_subset_ball (by linarith) hz)
  -- The cut-off model form `θ = ρ (Φ⁻¹)^* θ_{1/2}` is invariant, so `L_X θ = 0`.
  set θ := cutoffWeightOneForm Φ hρ hs fun _ ↦ 1 / 2
  have hθ : mlieDerivForm (fundamentalVectorField I circlePeriodOneGenerator) θ.val = 0 :=
    mlieDerivForm_fundamentalVectorField_eq_zero (fun g ↦
      mpullback_smul_cutoffWeightOneForm hρ hs _ (fun j g ↦ χ j g) g (hΦ.equivariant g) _
        (hρinv g)) _
  refine integralTopForm_mul_formCalculus_exp_of_forall_or o hθ hγ _ fun x ↦ ?_
  by_cases hx : x ∈ Φ '' closedBall 0 a
  swap
  · exact .inl (hγa x hx)
  right
  obtain ⟨z, hz, rfl⟩ := hx
  have hza : z ∈ ball (0 : StdSpace (Fin n)) a' :=
    mem_ball.2 ((mem_closedBall.1 hz).trans_lt ((le_max_left a 0).trans_lt ha'))
  have hzs : z ∈ Φ.source := by rw [hΦ.source_eq]; exact ball_subset_ball ha'r.le hza
  -- Near `Φ z` the cut-off is `1`.
  have hρz : ρ =ᶠ[𝓝 (Φ z)] 1 := by
    have hopen : IsOpen (Φ '' ball 0 a') :=
      Φ.toOpenPartialHomeomorph.isOpen_image_of_subset_source isOpen_ball
        (hΦ.source_eq ▸ ball_subset_ball ha'r.le)
    filter_upwards [hopen.mem_nhds (mem_image_of_mem _ hza)] with y hy
    exact hρ1 (image_mono ball_subset_closedBall hy)
  refine ⟨?_,
    (mextDerivₗ_cutoffWeightOneForm_half_apply_of_eventuallyEq_one hρ hs hΦ.isSymplecticMapOn
      hρz).symm⟩
  -- There `θ(X) = π ∑ⱼ kⱼ |zⱼ|² = H - H(p)`.
  have hθX := cutoffWeightOneForm_apply_weightChart hρ hs (fun _ ↦ 1 / 2)
    (fun j ↦ α j circlePeriodOneGenerator) hzs (by
      simpa only [Pi.smul_def, smul_eq_mul] using
        hΦ.mfderiv_weightGenerator z hzs circlePeriodOneGenerator)
  have hsum : 2 * π * ∑ j, 1 / 2 * α j circlePeriodOneGenerator * (z.x j ^ 2 + z.y j ^ 2) =
      π * ∑ j, α j circlePeriodOneGenerator * (z.x j ^ 2 + z.y j ^ 2) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  rw [hθX, hρz.self_of_nhds, Pi.one_apply, one_mul, hsum, ContMDiffMap.coe_smul, Pi.smul_apply,
    smul_eq_mul, hH, hH, hΦ.momentMap_apply z hzs]
  ring

end IsWeightChart

end SymplecticGeometry

end
