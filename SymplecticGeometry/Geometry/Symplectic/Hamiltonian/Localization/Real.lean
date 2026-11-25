/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Equivariant.Calculus
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Equivariant.Localization
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Smooth
public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.Localization.LocalizingForm
public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.Localization.WeightOneForm
public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.Localization.Weights
public import SymplecticGeometry.Geometry.Symplectic.Manifold.LiouvilleMeasure
public import TauCeti.Geometry.Symplectic.Manifold.SymplecticMap
public import TauCeti.Geometry.Symplectic.Manifold.Volume
import SymplecticGeometry.Analysis.Calculus.IteratedDeriv.Support
import SymplecticGeometry.Geometry.Manifold.PartitionOfUnity
import SymplecticGeometry.Geometry.Manifold.ContMDiff.Indicator
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Interior
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.Basic
import SymplecticGeometry.Geometry.Symplectic.Manifold.SymplecticMap
import SymplecticGeometry.Topology.Algebra.ConstMulAction
import SymplecticGeometry.Topology.OpenPartialHomeomorph.Separation
import TauCeti.Geometry.Symplectic.Hamiltonian.SymplecticVectorField
import TauCeti.Geometry.Symplectic.Manifold.NeighborhoodGerm
import TauCeti.Topology.Algebra.Support

/-!
# The Duistermaat–Heckman formula for real `ħ`

Let the circle act on a compact symplectic manifold `(M, σ)` with a moment map, `X` the
fundamental vector field of the period-one generator `ξ₁` and `H = ⟨μ, ξ₁⟩`. This file computes
the integrals that the Duistermaat–Heckman formula for real `ħ` is assembled from, and assembles
it.

* `SymplecticGeometry.integralTopForm_exp_neg_mul_eq_finsum_of_pos`: for real `ħ > 0`, with
  isolated fixed points and weights `k p` at each fixed point `p`
  (`SymplecticGeometry.IsTangentWeights`), the top component of `e^{σ - ħH}` has integral
  `∑ᶠ p ∈ fixedPoints, e^{-ħ H(p)} / (ħⁿ ∏ⱼ k p j)` against the symplectic orientation.

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

## The cut-off level and the radii around the fixed points

To cut `F(d_ħ θ)` into pieces near the fixed points, `SymplecticGeometry.exists_cutoffLevel_radii`
chooses, for charts `Φᵢ` about finitely many distinct centres and a continuous `f ≥ 0` that
vanishes only at the centres (in the application `f = θ(X)`), a level `δ > 0` and radii
`0 < aᵢ < bᵢ` inside the charts, such that the images `Φᵢ '' ball 0 bᵢ` are pairwise disjoint,
`ħ f ≤ δ` only on the union of the images `Φᵢ '' ball 0 aᵢ`, and the model integrand of the
contribution of a fixed point vanishes for `‖z‖ ≥ aᵢ` when `F` is supported in `[-δ, δ]`. Since
the centres are distinct, `OpenPartialHomeomorph.exists_pairwise_disjoint_image_ball` gives
balls about `0` with pairwise disjoint images; and `IsCompact.exists_forall_le'` gives `f` a
positive lower bound on the compact complement of the small images.

## The pieces of `F(d_ħ θ)` near the fixed points

`SymplecticGeometry.exists_eq_sum_of_cartanDiff_eq_zero` splits an equivariantly closed form `β`
that vanishes outside the union of the images `Φᵢ '' ball 0 aᵢ` into equivariantly closed forms
`γᵢ`, each supported in `Φᵢ '' closedBall 0 cᵢ` for some `cᵢ < bᵢ` and equal to `β` on
`Φᵢ '' ball 0 bᵢ`, with `β = ∑ᵢ γᵢ`, provided the images `Φᵢ '' ball 0 bᵢ` are pairwise
disjoint. The piece `γᵢ` is `ρᵢ β` for a smooth cut-off `ρᵢ` that is `1` near
`Φᵢ '' closedBall 0 aᵢ` and supported in `Φᵢ '' closedBall 0 cᵢ`
(`IsClosed.exists_contMDiffMap_tsupport_subset_eventually_eq_one`). At each point either `β`
vanishes or every `ρⱼ` is locally constant, `1` for the one image of radius `aⱼ` that contains the
point and `0` for the others, so `d_ħ (ρᵢ β) = dρᵢ ∧ β = 0`
(`SymplecticGeometry.cartanDiff_ofFunctionRingHom_mul_eq_zero`), and the other properties hold
pointwise. `SymplecticGeometry.exists_formCalculus_eq_sum` applies this to `β = F(d_ħ θ)` for a
one-form `θ` with `L_X θ = 0` and `F` supported in `[-δ, δ]`: the components of `F(d_ħ θ)` vanish
where `ħ θ(X) > δ` (`SymplecticGeometry.tsupport_formCalculus_subset`), and `F(d_ħ θ)` is
equivariantly closed (`SymplecticGeometry.cartanDiff_formCalculus_of_mlieDerivForm_eq_zero`).

## The top component of `F(d_ħ θ)` on a weight chart

Let `Φ` be a partial diffeomorphism from `StdSpace (Fin n)` to `M` that pulls `σ` back to the
standard form `ω₀` on its source, and let `θ` be a one-form on `M` that, on the image `Φ '' B` of
a ball `B` about `0`, is the model one-form `θₖ = ∑ⱼ kⱼ (xⱼ dyⱼ - yⱼ dxⱼ)` read through `Φ`
(`SymplecticGeometry.weightOneForm`), as the localizing form of
`SymplecticGeometry.exists_localizingForm` is. Let `X` be a vector field that `Φ` relates on `B`
to the generator `∑ⱼ 2π kⱼ (xⱼ ∂_{yⱼ} - yⱼ ∂_{xⱼ})` of the circle action with weights `k`.

For a smooth `F : ℝ → ℝ` and real `ħ`, put `f = -ħ θ(X)`. The component of degree `2 n` of
`F(f + dθ) = ∑ₘ F⁽ᵐ⁾(f) (dθ)ᵐ / m!` (`SymplecticGeometry.formCalculus`) at `Φ z`, for `z ∈ B`, is
`2ⁿ ∏ⱼ kⱼ · F⁽ⁿ⁾(-2πħ ∑ⱼ kⱼ² (xⱼ² + yⱼ²)) · σⁿ / n!`
(`SymplecticGeometry.formCalculus_apply_weightChart`). The proof reads every factor through `Φ`:
`θ(X) = 2π ∑ⱼ kⱼ² (xⱼ² + yⱼ²)` by `mpullback_symm_weightOneForm_apply_weightChart`,
`dθ` is `dθₖ` read through `Φ` by `TauCeti.mextDerivₗ_apply_eq_of_eventuallyEq_mpullback`, and
`(dθₖ)ⁿ = 2ⁿ ∏ⱼ kⱼ · ω₀ⁿ` by `wedgePow_mextDerivₗ_weightOneForm_apply`, while `σ` is `ω₀` read
through `Φ` since `Φ` is symplectic.

## The contribution of a fixed point

With `Φ`, `θ` and `X` as above, nonzero weights `k`, real `ħ > 0` and a smooth `F` with
compact support, let `φ` be a top form that is the component of degree `2 n` of
`F(-ħ θ(X) + dθ)` on `Φ '' B` and vanishes off it. If the model integrand
`F⁽ⁿ⁾(-2πħ ∑ⱼ kⱼ² (xⱼ² + yⱼ²))` vanishes outside a ball of radius `a` smaller than that of `B`,
then the integral of `φ` against the symplectic orientation is `F(0) / (ħⁿ ∏ⱼ kⱼ)`
(`SymplecticGeometry.integralTopForm_formCalculus_weightChart`). By the computation above
`φ = f σⁿ / n!` for a continuous compactly supported `f`; the integral of `φ` is the integral of
`f` against the Liouville measure
(`TauCeti.SmoothTwoForm.IsNondegenerate.integralTopForm_smul_volumeForm`), which the chart turns
into a Lebesgue integral on `StdSpace (Fin n)`
(`SymplecticGeometry.integral_liouvilleMeasure_of_isSymplecticMapOn_stdForm`), equal to
`2ⁿ ∏ⱼ kⱼ · F(0) πⁿ / ∏ⱼ (2πħ kⱼ²)` by
`SymplecticGeometry.integral_stdSpace_iteratedDeriv_neg_sum_mul_sq`. That `f` is continuous with
compact support is `PartialDiffeomorph.continuous_indicator_comp_symm` and
`PartialDiffeomorph.hasCompactSupport_indicator_comp_symm` for `Φ`.
In dimension `0` all sums and products are empty and the value is `F(0)`.

## The formula

`SymplecticGeometry.integralTopForm_exp_neg_mul_eq_finsum_of_pos` puts these together, following
Berline, Getzler and Vergne, §7.2. Since `ι_X σ = -dH`, the form `e^{σ - ħH}` is equivariantly
closed (`SymplecticGeometry.cartanDiff_formCalculus`). Take the localizing one-form `θ` and the
weight charts of `SymplecticGeometry.exists_localizingForm`, a level `δ` and radii from
`SymplecticGeometry.exists_cutoffLevel_radii` for `f = θ(X)`, and a bump function `F` with
`F(0) = 1` and support in `[-δ, δ]`. By `SymplecticGeometry.integralTopForm_formCalculus_mul` the
integral of the top component of `e^{σ - ħH}` is that of `F(d_ħ θ) e^{σ - ħH}`; cut `F(d_ħ θ)`
into its pieces at the fixed points (`SymplecticGeometry.exists_formCalculus_eq_sum`). The piece
at `p` contributes `e^{-ħ H(p)}` times its own integral
(`SymplecticGeometry.IsWeightChart.integralTopForm_mul_formCalculus_exp`), which is
`1 / (ħⁿ ∏ⱼ αⱼ(ξ₁))` for the weights `αⱼ(ξ₁)` of the chart
(`SymplecticGeometry.integralTopForm_formCalculus_weightChart`), and their product is that of the
given weights (`SymplecticGeometry.IsWeightChart.prod_apply_circlePeriodOneGenerator_eq`). In
dimension `0` the same argument gives `∑ᶠ p, e^{-ħ H(p)}`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §5.6
* N. Berline, E. Getzler and M. Vergne, *Heat Kernels and Dirac Operators*, Grundlehren der
  mathematischen Wissenschaften 298, Springer, 1992, §7.2
-/

public section

noncomputable section

open Set Metric Real MeasureTheory
open scoped Manifold ContDiff Topology DirectSum

namespace SymplecticGeometry

open TauCeti

section CutoffLevel

variable {M : Type*} [TopologicalSpace M] [CompactSpace M] [T2Space M]

/-- **The cut-off level and the radii around the fixed points.** Let `M` be a compact Hausdorff
space and, for `i` in a finite type, let `Φ i` be an open partial homeomorphism from
`StdSpace (Fin (n i))` to `M` whose source contains `ball 0 (s i)`, with `s i > 0` and pairwise
distinct centres `Φ i 0`, and let `k i j` be nonzero reals. Let `f : M → ℝ` be continuous and
nonnegative, vanishing only at the centres, and let `ħ > 0`. Then there are `δ > 0` and radii
`0 < a i < b i ≤ s i` such that the sets `Φ i '' ball 0 (b i)` are pairwise disjoint, every `x`
with `ħ f(x) ≤ δ` lies in some `Φ i '' ball 0 (a i)`, and
`δ < 2πħ ∑ⱼ kᵢⱼ² (xⱼ(z)² + yⱼ(z)²)` for every `z` with `a i ≤ ‖z‖`. -/
theorem exists_cutoffLevel_radii {ι : Type*} [Finite ι] {n : ι → ℕ}
    (Φ : ∀ i, OpenPartialHomeomorph (StdSpace (Fin (n i))) M) {s : ι → ℝ} (hs0 : ∀ i, 0 < s i)
    (hs : ∀ i, ball 0 (s i) ⊆ (Φ i).source) (hinj : Function.Injective fun i ↦ Φ i 0)
    {k : ∀ i, Fin (n i) → ℝ} (hk : ∀ i j, k i j ≠ 0) {f : M → ℝ} (hf : Continuous f)
    (hf0 : ∀ x, 0 ≤ f x) (hfz : ∀ x, f x = 0 → ∃ i, x = Φ i 0) {ħ : ℝ} (hħ : 0 < ħ) :
    ∃ δ > 0, ∃ a b : ι → ℝ, (∀ i, 0 < a i ∧ a i < b i ∧ b i ≤ s i) ∧
      Pairwise (fun i j ↦ Disjoint (Φ i '' ball 0 (b i)) (Φ j '' ball 0 (b j))) ∧
      (∀ x, ħ * f x ≤ δ → ∃ i, x ∈ Φ i '' ball 0 (a i)) ∧
      ∀ i (z : StdSpace (Fin (n i))), a i ≤ ‖z‖ →
        δ < 2 * π * ħ * ∑ j, k i j ^ 2 * (z.x j ^ 2 + z.y j ^ 2) := by
  -- Balls about `0` whose images under the `Φ i` are pairwise disjoint.
  have h0 (i : ι) : (0 : StdSpace (Fin (n i))) ∈ (Φ i).source := hs i (mem_ball_self (hs0 i))
  obtain ⟨c, hc0, -, hcd⟩ := OpenPartialHomeomorph.exists_pairwise_disjoint_image_ball Φ h0 hinj
  set b : ι → ℝ := fun i ↦ min (c i) (s i)
  set a : ι → ℝ := fun i ↦ b i / 2
  have hb0 (i : ι) : 0 < b i := lt_min (hc0 i) (hs0 i)
  have ha0 (i : ι) : 0 < a i := half_pos (hb0 i)
  have hab (i : ι) : a i < b i := half_lt_self (hb0 i)
  have has (i : ι) : ball (0 : StdSpace (Fin (n i))) (a i) ⊆ (Φ i).source :=
    (ball_subset_ball ((hab i).le.trans (min_le_right _ _))).trans (hs i)
  -- Off the balls of radius `a i`, `f` is bounded below by some `m > 0`.
  set K : Set M := (⋃ i, Φ i '' ball 0 (a i))ᶜ
  have hK : IsCompact K := (isOpen_iUnion fun i ↦
    (Φ i).isOpen_image_of_subset_source isOpen_ball (has i)).isClosed_compl.isCompact
  have hfK : ∀ x ∈ K, 0 < f x := fun x hx ↦ (hf0 x).lt_of_ne fun h ↦ by
    obtain ⟨i, rfl⟩ := hfz x h.symm
    exact hx (mem_iUnion.2 ⟨i, mem_image_of_mem _ (mem_ball_self (ha0 i))⟩)
  obtain ⟨m, hm0, hm⟩ := hK.exists_forall_le' hf.continuousOn hfK
  -- A lower bound `κ i > 0` for the squares of the weights of each chart.
  have hκ (i : ι) : ∃ κ > 0, ∀ j, κ ≤ k i j ^ 2 := by
    obtain ⟨κ, hκ, hκ0⟩ := ((Filter.eventually_all.2 fun j ↦
      Ioo_mem_nhdsGT (by have := hk i j; positivity : (0 : ℝ) < k i j ^ 2)).and
      (self_mem_nhdsWithin (s := Ioi (0 : ℝ)) (a := 0))).exists
    exact ⟨κ, hκ0, fun j ↦ (hκ j).2.le⟩
  choose κ hκ0 hκ using hκ
  -- `δ` below `ħ m` and below each `2πħ κ i (a i)²`.
  have hpos (i : ι) : 0 < 2 * π * ħ * κ i * a i ^ 2 := by
    have := hκ0 i; have := ha0 i; positivity
  obtain ⟨δ, hδ, hδ0⟩ := (((Filter.eventually_all.2 fun i ↦ Ioo_mem_nhdsGT (hpos i)).and
    (Ioo_mem_nhdsGT (mul_pos hħ hm0))).and
    (self_mem_nhdsWithin (s := Ioi (0 : ℝ)) (a := 0))).exists
  refine ⟨δ, hδ0, a, b, fun i ↦ ⟨ha0 i, hab i, min_le_right _ _⟩, fun i j hij ↦ ?_,
    fun x hx ↦ ?_, fun i z hz ↦ ?_⟩
  · exact (hcd hij).mono (image_mono (ball_subset_ball (min_le_left _ _)))
      (image_mono (ball_subset_ball (min_le_left _ _)))
  · by_contra hxa
    have hxK : x ∈ K := by simpa [K] using hxa
    have := mul_le_mul_of_nonneg_left (hm x hxK) hħ.le
    linarith [hδ.2.2]
  · have hsq : a i ^ 2 ≤ ‖z‖ ^ 2 := pow_le_pow_left₀ (ha0 i).le hz 2
    have hsum : κ i * ‖z‖ ^ 2 ≤ ∑ j, k i j ^ 2 * (z.x j ^ 2 + z.y j ^ 2) := by
      rw [StdSpace.norm_sq_eq_sum, Finset.mul_sum]
      exact Finset.sum_le_sum fun j _ ↦
        mul_le_mul_of_nonneg_right (hκ i j) (by positivity)
    have h2 : 2 * π * ħ * κ i * a i ^ 2 ≤ 2 * π * ħ * ∑ j, k i j ^ 2 * (z.x j ^ 2 + z.y j ^ 2) := by
      have := mul_le_mul_of_nonneg_left hsq (hκ0 i).le
      have : (0 : ℝ) ≤ 2 * π * ħ := by positivity
      nlinarith
    exact (hδ.1 i).2.trans_le h2

end CutoffLevel

section Pieces

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  {X : (x : M) → TangentSpace I x}
  {hX : ContMDiff I I.tangent ∞ (fun x ↦ (X x : TangentBundle I M))} {ħ : ℝ}
  {ι : Type*} [Fintype ι] {n : ι → ℕ}

omit [Fintype ι] in
/-- Cut-offs for `SymplecticGeometry.exists_eq_sum_of_cartanDiff_eq_zero`: smooth functions
`ρ i` and radii `c i < b i` such that `ρ i` vanishes outside `Φ i '' closedBall 0 (c i)` and,
near each point of `Φ j '' ball 0 (a j)`, `ρ j` is `1` and every other `ρ i` is `0`. -/
private theorem exists_cutoffs_image_ball
    (Φ : ∀ i, PartialDiffeomorph 𝓘(ℝ, StdSpace (Fin (n i))) I (StdSpace (Fin (n i))) M ∞)
    {a b : ι → ℝ} (hab : ∀ i, a i < b i) (hb : ∀ i, ball 0 (b i) ⊆ (Φ i).source)
    (hd : Pairwise fun i j ↦ Disjoint (Φ i '' ball 0 (b i)) (Φ j '' ball 0 (b j))) :
    ∃ (ρ : ι → C^∞⟮I, M; 𝓘(ℝ), ℝ⟯) (c : ι → ℝ), (∀ i, c i < b i) ∧
      (∀ i, ∀ x ∉ Φ i '' closedBall 0 (c i), ρ i x = 0) ∧
      ∀ j, ∀ x ∈ Φ j '' ball 0 (a j),
        (∀ᶠ y in 𝓝 x, ρ j y = 1) ∧ ∀ i ≠ j, ∀ᶠ y in 𝓝 x, ρ i y = 0 := by
  set c : ι → ℝ := fun i ↦ (a i + b i) / 2
  have hac (i : ι) : a i < c i := by simp only [c]; linarith [hab i]
  have hcb (i : ι) : c i < b i := by simp only [c]; linarith [hab i]
  have hopen (i : ι) {r : ℝ} (hr : r ≤ b i) : IsOpen (Φ i '' ball 0 r) :=
    (Φ i).toOpenPartialHomeomorph.isOpen_image_of_subset_source isOpen_ball
      ((ball_subset_ball hr).trans (hb i))
  have hclosed (i : ι) {r : ℝ} (hr : r < b i) : IsClosed (Φ i '' closedBall 0 r) :=
    ((Φ i).isCompact_image_of_subset_source (isCompact_closedBall 0 r)
      ((closedBall_subset_ball hr).trans (hb i))).isClosed
  choose ρ hρs hρ1 _ using fun i ↦
    (hclosed i (hab i)).exists_contMDiffMap_tsupport_subset_eventually_eq_one I
      (hopen i (hcb i).le) (image_mono (closedBall_subset_ball (hac i)))
  have hρ0 (i : ι) (x : M) (hx : x ∉ Φ i '' closedBall 0 (c i)) : ρ i x = 0 :=
    image_eq_zero_of_notMem_tsupport fun h ↦ hx (image_mono ball_subset_closedBall (hρs i h))
  refine ⟨ρ, c, hcb, hρ0, fun j x hj ↦ ⟨(hρ1 j).filter_mono (nhds_le_nhdsSet
    (image_mono ball_subset_closedBall hj)), fun i hij ↦ ?_⟩⟩
  filter_upwards [(hopen j (hab j).le).mem_nhds hj] with y hy
  exact hρ0 i y fun hyi ↦ disjoint_left.1 (hd hij)
    (image_mono (closedBall_subset_ball (hcb i)) hyi) (image_mono (ball_subset_ball (hab j).le) hy)

/-- **Cutting an equivariantly closed form into pieces near the centres of charts.** Let `M` be a
Hausdorff, σ-compact manifold, and for `i` in a finite type let `Φ i` be a partial
diffeomorphism from `StdSpace (Fin (n i))` to `M` with `ball 0 (b i)` in its source, such that
the sets `Φ i '' ball 0 (b i)` are pairwise disjoint. Let `a i < b i`, and let `β` be a form of
mixed degree with `d_ħ β = 0` whose components all vanish outside the union of the sets
`Φ i '' ball 0 (a i)`. Then there are forms `γ i` of mixed degree and radii `c i < b i` such that
`d_ħ (γ i) = 0`, the components of `γ i` vanish outside `Φ i '' closedBall 0 (c i)` and agree
with those of `β` on `Φ i '' ball 0 (b i)`, and `β = ∑ i, γ i`. -/
theorem exists_eq_sum_of_cartanDiff_eq_zero
    (Φ : ∀ i, PartialDiffeomorph 𝓘(ℝ, StdSpace (Fin (n i))) I (StdSpace (Fin (n i))) M ∞)
    {a b : ι → ℝ} (hab : ∀ i, a i < b i) (hb : ∀ i, ball 0 (b i) ⊆ (Φ i).source)
    (hd : Pairwise fun i j ↦ Disjoint (Φ i '' ball 0 (b i)) (Φ j '' ball 0 (b j)))
    {β : ⨁ k, SmoothForm I M ℝ k} (hβ : cartanDiff X hX ħ β = 0)
    (hβa : ∀ x, (∀ i, x ∉ Φ i '' ball 0 (a i)) → ∀ k, (β k).val x = 0) :
    ∃ (γ : ι → ⨁ k, SmoothForm I M ℝ k) (c : ι → ℝ), (∀ i, c i < b i) ∧
      (∀ i, cartanDiff X hX ħ (γ i) = 0) ∧
      (∀ i, ∀ x ∉ Φ i '' closedBall 0 (c i), ∀ k, (γ i k).val x = 0) ∧
      (∀ i, ∀ x ∈ Φ i '' ball 0 (b i), ∀ k, (γ i k).val x = (β k).val x) ∧
      β = ∑ i, γ i := by
  classical
  obtain ⟨ρ, c, hcb, hρ0, hρ⟩ := exists_cutoffs_image_ball Φ hab hb hd
  -- At each point, either `β` vanishes or one cut-off is `1` nearby and the others are `0`.
  have hloc (x : M) : (∀ k, (β k).val x = 0) ∨ ∃ j, x ∈ Φ j '' ball 0 (a j) ∧
      (∀ᶠ y in 𝓝 x, ρ j y = 1) ∧ ∀ i ≠ j, ∀ᶠ y in 𝓝 x, ρ i y = 0 := by
    by_cases hx : ∃ j, x ∈ Φ j '' ball 0 (a j)
    · obtain ⟨j, hj⟩ := hx
      exact .inr ⟨j, hj, hρ j x hj⟩
    · exact .inl (hβa x fun i hi ↦ hx ⟨i, hi⟩)
  have hγ (i : ι) (k : ℕ) (x : M) :
      ((SmoothForm.ofFunctionRingHom (ρ i) * β) k).val x = ρ i x • (β k).val x := by
    simp
  refine ⟨fun i ↦ SmoothForm.ofFunctionRingHom (ρ i) * β, c, hcb, fun i ↦ ?_, fun i x hx k ↦ ?_,
    fun i x hx k ↦ ?_, ?_⟩
  · refine cartanDiff_ofFunctionRingHom_mul_eq_zero _ hβ fun x ↦ (hloc x).symm.imp_left ?_
    rintro ⟨j, -, h1, h0⟩
    obtain ⟨r, hr⟩ : ∃ r : ℝ, ∀ᶠ y in 𝓝 x, ρ i y = r := by
      by_cases hij : i = j
      · exact ⟨1, hij ▸ h1⟩
      · exact ⟨0, h0 i hij⟩
    exact ((hasMFDerivAt_const r x).congr_of_eventuallyEq hr).mfderiv
  · rw [hγ, hρ0 i x hx, zero_smul]
  · rw [hγ]
    rcases hloc x with h | ⟨j, hj, h1, -⟩
    · rw [h k, smul_zero]
    · obtain rfl : i = j := by
        by_contra hij
        exact disjoint_left.1 (hd hij) hx (image_mono (ball_subset_ball (hab j).le) hj)
      rw [h1.self_of_nhds, one_smul]
  · ext k : 1
    refine Subtype.ext (funext fun x ↦ ?_)
    rw [DirectSum.sum_apply, Submodule.coe_sum, Finset.sum_apply]
    simp only [hγ]
    rcases hloc x with h | ⟨j, -, h1, h0⟩
    · simp [h k]
    · rw [Finset.sum_eq_single j (fun i _ hij ↦ by rw [(h0 i hij).self_of_nhds, zero_smul])
        (by simp), h1.self_of_nhds, one_smul]

/-- **The pieces of `F(d_ħ θ)` near the centres of charts.** Let `M`, the charts `Φ i` and the
radii `a i < b i` be as in `SymplecticGeometry.exists_eq_sum_of_cartanDiff_eq_zero`, let `θ` be
a one-form with zero Lie derivative along `X`, and let `δ` be such that every `x` with
`ħ θ(X)(x) ≤ δ` lies in some `Φ i '' ball 0 (a i)`. For a smooth `F : ℝ → ℝ` supported in
`[-δ, δ]`, the form `F(d_ħ θ) = F(-ħ θ(X) + dθ)` is the sum of forms `γ i` of mixed degree with
`d_ħ (γ i) = 0`, whose components vanish outside `Φ i '' closedBall 0 (c i)` for some
`c i < b i` and agree with those of `F(d_ħ θ)` on `Φ i '' ball 0 (b i)`. -/
theorem exists_formCalculus_eq_sum
    (Φ : ∀ i, PartialDiffeomorph 𝓘(ℝ, StdSpace (Fin (n i))) I (StdSpace (Fin (n i))) M ∞)
    {a b : ι → ℝ} (hab : ∀ i, a i < b i) (hb : ∀ i, ball 0 (b i) ⊆ (Φ i).source)
    (hd : Pairwise fun i j ↦ Disjoint (Φ i '' ball 0 (b i)) (Φ j '' ball 0 (b j)))
    {θ : SmoothForm I M ℝ 1} (hθ : mlieDerivForm X θ.val = 0) {δ : ℝ}
    (hδ : ∀ x, ħ * θ.val x ![X x] ≤ δ → ∃ i, x ∈ Φ i '' ball 0 (a i))
    (F : ℝ → ℝ) (hF : ContDiff ℝ ∞ F) (hFδ : tsupport F ⊆ Icc (-δ) δ) :
    ∃ (γ : ι → ⨁ k, SmoothForm I M ℝ k) (c : ι → ℝ), (∀ i, c i < b i) ∧
      (∀ i, cartanDiff X hX ħ (γ i) = 0) ∧
      (∀ i, ∀ x ∉ Φ i '' closedBall 0 (c i), ∀ k, (γ i k).val x = 0) ∧
      (∀ i, ∀ x ∈ Φ i '' ball 0 (b i), ∀ k, (γ i k).val x = (formCalculus F hF
        (-ħ • SmoothForm.ofFunctionEquiv.symm (SmoothForm.interiorProduct ⟨X, hX⟩ θ))
        (mextDerivₗ I 1 θ) k).val x) ∧
      formCalculus F hF
        (-ħ • SmoothForm.ofFunctionEquiv.symm (SmoothForm.interiorProduct ⟨X, hX⟩ θ))
        (mextDerivₗ I 1 θ) = ∑ i, γ i := by
  refine exists_eq_sum_of_cartanDiff_eq_zero Φ hab hb hd
    (cartanDiff_formCalculus_of_mlieDerivForm_eq_zero F hF hθ) fun x hx k ↦ ?_
  -- Where a component of `F(d_ħ θ)` is nonzero, `-ħ θ(X)` lies in the support of `F`.
  by_contra hne
  have hFx : ħ * θ.val x ![X x] ≤ δ := by
    simpa using (hFδ (tsupport_formCalculus_subset F hF _ _ k (subset_tsupport _ hne))).1
  obtain ⟨i, hi⟩ := hδ x hFx
  exact hx i hi

end Pieces

section WeightChart

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {n : ℕ} {Φ : PartialDiffeomorph 𝓘(ℝ, StdSpace (Fin n)) I (StdSpace (Fin n)) M ∞}
  {k : Fin n → ℝ} {θ : SmoothForm I M ℝ 1} {s : ℝ}

/-- At `Φ z`, the function `θ(X)` takes the value `2π ∑ⱼ kⱼ² (xⱼ(z)² + yⱼ(z)²)`. -/
private theorem interiorProduct_apply_weightChart {X : (x : M) → TangentSpace I x}
    {hX : ContMDiff I I.tangent ∞ (fun x ↦ (X x : TangentBundle I M))} {z : StdSpace (Fin n)}
    (hθ : θ.val (Φ z) =
      TauCeti.mpullback I 𝓘(ℝ, StdSpace (Fin n)) Φ.symm (weightOneForm k).val (Φ z))
    (hz : z ∈ Φ.source)
    (hXz : mfderiv 𝓘(ℝ, StdSpace (Fin n)) I Φ z (EuclideanSpace.sumEquivProd.symm
        (weightGenerator ((2 * π) • k) (EuclideanSpace.sumEquivProd z))) = X (Φ z)) :
    SmoothForm.ofFunctionEquiv.symm (SmoothForm.interiorProduct ⟨X, hX⟩ θ) (Φ z) =
      2 * π * ∑ j, k j ^ 2 * (z.x j ^ 2 + z.y j ^ 2) := by
  rw [SmoothForm.ofFunctionEquiv_symm_apply, SmoothForm.interiorProduct_apply_degree_one,
    ContMDiffSection.coeFn_mk, hθ, mpullback_symm_weightOneForm_apply_weightChart k k hz hXz]
  simp only [sq]

/-- **The top component of `F(d_ħ θ)` on a weight chart.** Let `Φ` be a partial diffeomorphism
from `StdSpace (Fin n)` to `M` that pulls `σ` back to the standard form on its source, let
`ball 0 s` lie in its source, let `θ` be the model one-form `θₖ` read through `Φ` on
`Φ '' ball 0 s`, and let `Φ` relate on `ball 0 s` the generator of the rotations by the angles
`2π kⱼ` to the vector field `X`. For a smooth `F : ℝ → ℝ`, real `ħ` and `z ∈ ball 0 s`, the
component of degree `2 n` of `F(-ħ θ(X) + dθ)` at `Φ z` is
`2ⁿ ∏ⱼ kⱼ · F⁽ⁿ⁾(-2πħ ∑ⱼ kⱼ² (xⱼ(z)² + yⱼ(z)²))` times the symplectic volume form `σⁿ / n!`. -/
theorem formCalculus_apply_weightChart [FiniteDimensional ℝ E] {σ : SmoothTwoForm I M}
    (hσ : SmoothTwoForm.IsSymplecticMapOn (stdForm (Fin n)).constSmooth σ Φ Φ.source)
    (hs : ball 0 s ⊆ Φ.source)
    (hθ : ∀ x ∈ Φ '' ball 0 s,
      θ.val x = TauCeti.mpullback I 𝓘(ℝ, StdSpace (Fin n)) Φ.symm (weightOneForm k).val x)
    {X : (x : M) → TangentSpace I x}
    {hX : ContMDiff I I.tangent ∞ (fun x ↦ (X x : TangentBundle I M))}
    (hXΦ : ∀ z ∈ ball 0 s, mfderiv 𝓘(ℝ, StdSpace (Fin n)) I Φ z (EuclideanSpace.sumEquivProd.symm
        (weightGenerator ((2 * π) • k) (EuclideanSpace.sumEquivProd z))) = X (Φ z))
    (F : ℝ → ℝ) (hF : ContDiff ℝ ∞ F) (ħ : ℝ) {z : StdSpace (Fin n)} (hz : z ∈ ball 0 s) :
    (formCalculus F hF
        (-ħ • SmoothForm.ofFunctionEquiv.symm (SmoothForm.interiorProduct ⟨X, hX⟩ θ))
        (mextDerivₗ I 1 θ) (2 * n)).val (Φ z) =
      ((2 ^ n * ∏ j, k j) *
          iteratedDeriv n F (-(2 * π * ħ) * ∑ j, k j ^ 2 * (z.x j ^ 2 + z.y j ^ 2))) •
        (σ.volumeForm n).val (Φ z) := by
  have hzs : z ∈ Φ.source := hs hz
  have hxt : Φ z ∈ Φ.target := Φ.map_source hzs
  -- `σ` is the standard form read through `Φ`, since `Φ⁻¹` is symplectic on the target.
  have hσx : σ.val (Φ z) =
      ((stdForm (Fin n)).constSmooth.val (Φ.symm (Φ z))).compContinuousLinearMap
        (mfderiv I 𝓘(ℝ, StdSpace (Fin n)) Φ.symm (Φ z)) :=
    ((Φ.isSymplecticMapOn_symm hσ (by simp)).mpullback_apply hxt).symm.trans
      (mpullback_apply_eq_compContinuousLinearMap _ _ _)
  have hω₀ (v w : StdSpace (Fin n)) :
      (stdForm (Fin n)).constSmooth.val (Φ.symm (Φ z)) ![v, w] = stdForm (Fin n) v w :=
    (SmoothBundleForm.eval₂_apply _ _ _ _).symm.trans (SymplecticForm.constSmooth_apply _ _ _ _)
  have hpow :
      ((mextDerivₗ 𝓘(ℝ, StdSpace (Fin n)) 1 (weightOneForm k)).val (Φ.symm (Φ z))).wedgePow n =
      (2 ^ n * ∏ j, k j) • ((stdForm (Fin n)).constSmooth.val (Φ.symm (Φ z))).wedgePow n := by
    have h := wedgePow_mextDerivₗ_weightOneForm_apply k (Φ.symm (Φ z)) hω₀
    rw [Fintype.card_fin] at h
    -- `h` is stated on `StdSpace (Fin n)`, the goal on the tangent space at `Φ.symm (Φ z)`.
    exact h
  -- `θ` is `(Φ⁻¹)^* θₖ` on the open set `Φ '' ball 0 s`, a neighbourhood of `Φ z`.
  have hθx : ∀ᶠ y in 𝓝 (Φ z),
      θ.val y = TauCeti.mpullback I 𝓘(ℝ, StdSpace (Fin n)) Φ.symm (weightOneForm k).val y :=
    Filter.eventually_of_mem ((Φ.toOpenPartialHomeomorph.isOpen_image_of_subset_source
      isOpen_ball hs).mem_nhds (mem_image_of_mem _ hz)) hθ
  rw [formCalculus_apply_val, mextDerivₗ_apply_eq_of_eventuallyEq_mpullback
      ((Φ.symm.contMDiffOn.contMDiffAt (Φ.open_target.mem_nhds hxt)).of_le (by simp)) hθx,
    ← ContinuousAlternatingMap.wedgePow_compContinuousLinearMap, hpow,
    SmoothTwoForm.volumeForm_apply, hσx,
    ← ContinuousAlternatingMap.wedgePow_compContinuousLinearMap, ContMDiffMap.coe_smul,
    Pi.smul_apply, interiorProduct_apply_weightChart (hθ _ (mem_image_of_mem _ hz)) hzs (hXΦ z hz),
    smul_eq_mul]
  ext v
  simp only [ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, smul_eq_mul]
  rw [show -ħ * (2 * π * ∑ j, k j ^ 2 * (z.x j ^ 2 + z.y j ^ 2)) =
    -(2 * π * ħ) * ∑ j, k j ^ 2 * (z.x j ^ 2 + z.y j ^ 2) by ring]
  ring

/-- **The contribution of a fixed point.** Let `σ` be nondegenerate on a manifold modelled on a
space of dimension `2 n`, let `Φ` be a partial diffeomorphism from `StdSpace (Fin n)` to `M`
that pulls `σ` back to the standard form on its source, let `ball 0 s` lie in its source, let `θ`
be the model one-form `θₖ` read through `Φ` on `Φ '' ball 0 s`, with weights `kⱼ ≠ 0`, and let
`Φ` relate on `ball 0 s` the generator of the rotations by the angles `2π kⱼ` to `X`. Let
`F : ℝ → ℝ` be smooth with compact support, `ħ > 0` and `a < s`, such that
`F⁽ⁿ⁾(-2πħ ∑ⱼ kⱼ² (xⱼ(z)² + yⱼ(z)²))` vanishes for `‖z‖ > a`. If the top form `φ` is the
component of degree `2 n` of `F(-ħ θ(X) + dθ)` on `Φ '' ball 0 s` and vanishes outside it, then
its integral against the symplectic orientation is `F 0 / (ħ ^ n * ∏ j, k j)`. -/
theorem integralTopForm_formCalculus_weightChart [FiniteDimensional ℝ E] [T2Space M]
    [MeasurableSpace M] [BorelSpace M] [LindelofSpace M] [Fact (Module.finrank ℝ E = 2 * n)]
    {σ : SmoothTwoForm I M} (hσn : σ.IsNondegenerate)
    (hσ : SmoothTwoForm.IsSymplecticMapOn (stdForm (Fin n)).constSmooth σ Φ Φ.source)
    (hs : ball 0 s ⊆ Φ.source)
    (hθ : ∀ x ∈ Φ '' ball 0 s,
      θ.val x = TauCeti.mpullback I 𝓘(ℝ, StdSpace (Fin n)) Φ.symm (weightOneForm k).val x)
    {X : (x : M) → TangentSpace I x}
    {hX : ContMDiff I I.tangent ∞ (fun x ↦ (X x : TangentBundle I M))}
    (hXΦ : ∀ z ∈ ball 0 s, mfderiv 𝓘(ℝ, StdSpace (Fin n)) I Φ z (EuclideanSpace.sumEquivProd.symm
        (weightGenerator ((2 * π) • k) (EuclideanSpace.sumEquivProd z))) = X (Φ z))
    (hk : ∀ j, k j ≠ 0) {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (hFc : HasCompactSupport F)
    {ħ : ℝ} (hħ : 0 < ħ) {a : ℝ} (has : a < s)
    (hFa : ∀ z : StdSpace (Fin n), a < ‖z‖ →
      iteratedDeriv n F (-(2 * π * ħ) * ∑ j, k j ^ 2 * (z.x j ^ 2 + z.y j ^ 2)) = 0)
    {φ : RoughForm I M ℝ (2 * n)}
    (hφ : ∀ z ∈ ball 0 s, φ (Φ z) = (formCalculus F hF
        (-ħ • SmoothForm.ofFunctionEquiv.symm (SmoothForm.interiorProduct ⟨X, hX⟩ θ))
        (mextDerivₗ I 1 θ) (2 * n)).val (Φ z))
    (hφs : ∀ x ∉ Φ '' ball 0 s, φ x = 0) :
    integralTopForm (hσn.volumeOrientation Fact.out) φ = F 0 / (ħ ^ n * ∏ j, k j) := by
  -- The model integrand on `StdSpace (Fin n)`, with the weights `wⱼ = 2πħ kⱼ²`.
  set w : Fin n → ℝ := fun j ↦ 2 * π * ħ * k j ^ 2
  set G : StdSpace (Fin n) → ℝ :=
    fun z ↦ iteratedDeriv n F (-(2 * π * ħ) * ∑ j, k j ^ 2 * (z.x j ^ 2 + z.y j ^ 2))
  have hGw : G = fun z ↦ iteratedDeriv n F (-∑ j, w j * (z.x j ^ 2 + z.y j ^ 2)) := by
    funext z
    simp only [G, w, neg_mul, Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact congrArg _ (Finset.sum_congr rfl fun j _ ↦ by ring)
  have hG0 {z : StdSpace (Fin n)} (hz : a < ‖z‖) : G z = 0 := hFa z hz
  have hG : Continuous G :=
    Continuous.comp (g := iteratedDeriv n F) (hF.continuous_iteratedDeriv n (by simp))
      (by fun_prop)
  set c : ℝ := 2 ^ n * ∏ j, k j
  set f : M → ℝ := Φ.target.indicator fun x ↦ c * G (Φ.symm x) with hf_def
  have hfΦ {z : StdSpace (Fin n)} (hz : z ∈ Φ.source) : f (Φ z) = c * G z := by
    rw [hf_def, indicator_of_mem (Φ.map_source hz), Φ.symm_toPartialEquiv, Φ.left_inv hz]
  have hf0 {x : M} (hx : x ∉ Φ.target) : f x = 0 := by rw [hf_def, indicator_of_notMem hx]
  have hft {x : M} (hx : x ∈ Φ.target) (hxa : a < ‖Φ.symm x‖) : f x = 0 := by
    rw [hf_def, indicator_of_mem hx, hG0 hxa, mul_zero]
  have hsa : closedBall (0 : StdSpace (Fin n)) a ⊆ ball 0 s := closedBall_subset_ball has
  -- `f` is `c G` read through `Φ⁻¹`, and `c G` is supported in `closedBall 0 a`.
  have hGa : tsupport (fun z ↦ c * G z) ⊆ closedBall 0 a :=
    TauCeti.tsupport_subset_of_forall_notMem_eq_zero
      (fun z hz ↦ by rw [hG0 (by simpa using hz), mul_zero]) isClosed_closedBall
  have hGK : IsCompact (tsupport fun z ↦ c * G z) :=
    (isCompact_closedBall 0 a).of_isClosed_subset (isClosed_tsupport _) hGa
  have hGs : tsupport (fun z ↦ c * G z) ⊆ Φ.source := hGa.trans (hsa.trans hs)
  have hf : Continuous f := Φ.continuous_indicator_comp_symm (continuous_const.mul hG) hGK hGs
  -- `φ` is `f` times the symplectic volume form.
  have hφf : φ = fun x ↦ f x • (σ.volumeForm n).val x := by
    funext x
    by_cases hx : x ∈ Φ '' ball 0 s
    · obtain ⟨z, hz, rfl⟩ := hx
      rw [hφ z hz, formCalculus_apply_weightChart hσ hs hθ hXΦ F hF ħ hz, hfΦ (hs hz)]
    · rw [hφs x hx]
      by_cases hxt : x ∈ Φ.target
      · have hz : Φ.symm x ∉ ball 0 s := fun h ↦ hx ⟨_, h, Φ.right_inv hxt⟩
        rw [hft hxt (has.trans_le (by simpa using hz)), zero_smul]
      · rw [hf0 hxt, zero_smul]
  have hw : ∀ j, 0 < w j := fun j ↦ by have := hk j; positivity
  have hint := integral_stdSpace_iteratedDeriv_neg_sum_mul_sq (ι := Fin n)
    (hF.of_le (by simp)) hFc hw
  rw [Fintype.card_fin] at hint
  rw [hφf,
    hσn.integralTopForm_smul_volumeForm hf (Φ.hasCompactSupport_indicator_comp_symm hGK hGs),
    integral_liouvilleMeasure_of_isSymplecticMapOn_stdForm hσ fun x hx ↦ hf0 hx,
    setIntegral_congr_fun Φ.open_source.measurableSet fun z hz ↦ hfΦ hz,
    setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz ↦ by
      rw [hG0 (has.trans_le (by simpa using fun h ↦ hz (hs h))), mul_zero],
    integral_const_mul, hGw, hint]
  simp only [c, w, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, Finset.prod_pow]
  have : ∏ j, k j ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ ↦ hk j
  field_simp

end WeightChart

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

omit [I.Boundaryless] [ContMDiffSMul (𝓡 1) I ∞ Circle M] in
/-- The integral of one piece of `F(d_ħ θ)` at a fixed point. Let `Φ` be a weight chart at `p` of
radius `r` with nonzero weights `αⱼ(ξ₁)`, and `θ` the model one-form `weightOneForm` of these
weights read through `Φ` on `Φ '' ball 0 b`, for `b ≤ r`. Let `F` be smooth with compact support
in `[-δ, δ]` and `F 0 = 1`, and let `δ < 2πħ ∑ⱼ αⱼ(ξ₁)² (xⱼ² + yⱼ²)` for `‖z‖ ≥ a`, where
`a < b`. If `γ` vanishes outside `Φ '' closedBall 0 c`, for some `c < b`, and agrees with
`F(d_ħ θ)` on `Φ '' ball 0 b`, then the top component of `γ` has integral
`1 / (ħⁿ ∏ⱼ αⱼ(ξ₁))` against the symplectic orientation. -/
private theorem integralTopForm_piece_weightChart {n : ℕ} [Fact (Module.finrank ℝ E = 2 * n)]
    {σ : SmoothTwoForm I M} (hσ : σ.IsNondegenerate)
    {μ : M → Module.Dual ℝ (GroupLieAlgebra (𝓡 1) Circle)} {p : M} {m : ℕ}
    {χ : Fin m → Circle →ₜ* Circle} {α : Fin m → StrongDual ℝ (EuclideanSpace ℝ (Fin 1))}
    {Φ : PartialDiffeomorph 𝓘(ℝ, StdSpace (Fin m)) I (StdSpace (Fin m)) M ∞} {r : ℝ}
    (hΦ : IsWeightChart σ μ p χ α Φ r) (hα : ∀ j, α j circlePeriodOneGenerator ≠ 0)
    {θ : SmoothForm I M ℝ 1} {b : ℝ} (hbr : b ≤ r)
    (hθ : ∀ x ∈ Φ '' ball 0 b, θ.val x = TauCeti.mpullback I 𝓘(ℝ, StdSpace (Fin m)) Φ.symm
      (weightOneForm fun j ↦ α j circlePeriodOneGenerator).val x)
    {hX : ContMDiff I I.tangent ∞ fun x ↦
      (⟨x, fundamentalVectorField I circlePeriodOneGenerator x⟩ : TangentBundle I M)}
    {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (hFc : HasCompactSupport F) (hF0 : F 0 = 1)
    {ħ δ : ℝ} (hħ : 0 < ħ) (hFδ : tsupport F ⊆ Icc (-δ) δ) {a c : ℝ} (hab : a < b)
    (hcb : c < b)
    (hδ : ∀ z : StdSpace (Fin m), a ≤ ‖z‖ →
      δ < 2 * π * ħ * ∑ j, α j circlePeriodOneGenerator ^ 2 * (z.x j ^ 2 + z.y j ^ 2))
    {γ : ⨁ k, SmoothForm I M ℝ k} (hγc : ∀ x ∉ Φ '' closedBall 0 c, ∀ k, (γ k).val x = 0)
    (hγb : ∀ x ∈ Φ '' ball 0 b, ∀ k, (γ k).val x = (formCalculus F hF
      (-ħ • SmoothForm.ofFunctionEquiv.symm
        (SmoothForm.interiorProduct ⟨fundamentalVectorField I circlePeriodOneGenerator, hX⟩ θ))
      (mextDerivₗ I 1 θ) k).val x) :
    integralTopForm (hσ.volumeOrientation Fact.out) (γ (2 * n)).val =
      1 / (ħ ^ n * ∏ j, α j circlePeriodOneGenerator) := by
  obtain rfl : m = n := hΦ.eq_of_finrank_eq Fact.out
  borelize M
  have hbs : ball (0 : StdSpace (Fin m)) b ⊆ Φ.source := hΦ.source_eq ▸ ball_subset_ball hbr
  rw [← hF0]
  refine integralTopForm_formCalculus_weightChart hσ hΦ.isSymplecticMapOn hbs hθ
    (fun z hz ↦ ?_) hα hF hFc hħ hab (fun z hz ↦ ?_)
    (fun z hz ↦ hγb _ (mem_image_of_mem _ hz) _)
    (fun x hx ↦ hγc x (fun h ↦ hx (image_mono (closedBall_subset_ball hcb) h)) _)
  · simpa only [Pi.smul_def, smul_eq_mul] using
      hΦ.mfderiv_weightGenerator z (hbs hz) circlePeriodOneGenerator
  · refine Function.notMem_support.1 fun h ↦ ?_
    have h1 := (hFδ (support_iteratedDeriv_subset _ h)).1
    have h2 := hδ z hz.le
    linarith

/-- **The Duistermaat–Heckman formula for real `ħ`.** Let the circle act smoothly on a compact
boundaryless manifold `M` of dimension `2 n`, preserving a symplectic form `σ`, with a moment map
`μ` in the sign `d⟨μ, ξ⟩ = -ι_{ξ_M} σ` and isolated fixed points, and let `H` be the smooth
function `⟨μ, ξ₁⟩` for the period-one generator `ξ₁ = circlePeriodOneGenerator`. Let `k p` be
weights of the action at each fixed point `p`, as in `SymplecticGeometry.IsTangentWeights`. Then
for real `ħ > 0` the integral, against the symplectic orientation, of the top component of
`e^{σ - ħH} = formCalculus Real.exp _ (-ħ • H) σ` is
`∑ᶠ p ∈ fixedPoints, e^{-ħ H(p)} / (ħ ^ n * ∏ j, k p j)`. -/
theorem integralTopForm_exp_neg_mul_eq_finsum_of_pos {n : ℕ}
    [Fact (Module.finrank ℝ E = 2 * n)] {σ : SmoothTwoForm I M} (hσ : σ.IsSymplectic)
    (hinv : ∀ g : Circle, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := 𝓡 1) g) σ = σ)
    {μ : M → Module.Dual ℝ (GroupLieAlgebra (𝓡 1) Circle)}
    (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental (𝓡 1) Circle I M) fun x ↦ -μ x)
    (hiso : ∀ p ∈ MulAction.fixedPoints Circle M,
      ∀ᶠ x in 𝓝[≠] p, x ∉ MulAction.fixedPoints Circle M)
    (k : M → Fin n → ℤ)
    (hk : ∀ p ∈ MulAction.fixedPoints Circle M,
      ∃ L : TangentSpace I p ≃L[ℝ] (Fin n → ℂ), IsTangentWeights σ p (k p) L)
    {H : C^∞⟮I, M; ℝ⟯} (hH : ∀ x, H x = μ x circlePeriodOneGenerator) {ħ : ℝ} (hħ : 0 < ħ) :
    integralTopForm (hσ.isNondegenerate.volumeOrientation (n := n) Fact.out)
        ((formCalculus Real.exp Real.contDiff_exp (-ħ • H) σ) (2 * n)).val =
      ∑ᶠ p ∈ MulAction.fixedPoints Circle M,
        Real.exp (-ħ * H p) / (ħ ^ n * ∏ j, (k p j : ℝ)) := by
  classical
  set o := hσ.isNondegenerate.volumeOrientation (n := n) Fact.out
  set ξ := circlePeriodOneGenerator
  set X := fundamentalVectorField I ξ (M := M)
  have hX : ContMDiff I I.tangent ∞ fun x ↦ (⟨x, X x⟩ : TangentBundle I M) :=
    contMDiff_fundamentalVectorField (m := ∞) (n := ∞) (by simp) ξ
  -- `e^{σ - ħH}` is equivariantly closed, since `ι_X σ = -dH`.
  set e := formCalculus Real.exp Real.contDiff_exp (-ħ • H) σ
  have hι : σ.interiorₗ ⟨X, hX⟩ = mextDerivₗ I 0 (SmoothForm.ofFunction (-H)) :=
    SmoothTwoForm.isHamiltonianVectorField_iff_interiorₗ_eq.1 (by
      rw [SmoothForm.ofFunction_apply_zero]
      convert hμ.isHamiltonianVectorField ξ using 1
      · funext x
        simp [hH]
      · rw [ContMDiffSection.coeFn_mk, InfinitesimalAction.fundamental_apply])
  have he : cartanDiff X hX ħ e = 0 := by
    refine cartanDiff_formCalculus _ _ (Subtype.ext (by
      rw [mextDerivₗ_apply]; exact (SmoothForm.isClosed_def σ).1 hσ.isClosed)) ?_
    rw [← SmoothTwoForm.interiorₗ_eq_interiorProduct, hι, ← map_smul, neg_smul, ← smul_neg,
      ← SmoothForm.ofFunctionEquiv_apply, ← SmoothForm.ofFunctionEquiv_apply]
    exact congrArg _ (SmoothForm.ofFunctionEquiv.map_smul ħ (-H)).symm
  -- The localizing one-form `θ` and the weight charts at the finitely many fixed points.
  obtain ⟨θ, hθinv, hθ0, hθz, hloc⟩ := exists_localizingForm hμ hσ hinv hiso
  have hθL : mlieDerivForm X θ.val = 0 := mlieDerivForm_fundamentalVectorField_eq_zero hθinv ξ
  have : ContinuousConstSMul Circle M :=
    ⟨fun g ↦ (ContMDiffSMul.contMDiff_const_smul (I := 𝓡 1) (I' := I) (n := ∞) g).continuous⟩
  set S := MulAction.fixedPoints Circle M
  have : Fintype S := (finite_fixedPoints hiso).fintype
  choose m χ α Φ r s hW hα hs0 hsr hθΦ using fun p : S ↦ hloc p.val p.property
  have hsrc (p : S) : ball (0 : StdSpace (Fin (m p))) (s p) ⊆ (Φ p).source := by
    rw [(hW p).source_eq]; exact ball_subset_ball (hsr p)
  have hfc : Continuous fun x ↦ θ.val x ![X x] := by
    have := (SmoothForm.contMDiff_apply_zero (SmoothForm.interiorProduct ⟨X, hX⟩ θ)).continuous
    simpa only [SmoothForm.interiorProduct_apply_degree_one, ContMDiffSection.coeFn_mk] using this
  -- The cut-off level `δ`, the radii, and a bump function `F` supported in `[-δ, δ]`.
  obtain ⟨δ, hδ, a, b, hab, hd, hδa, hδz⟩ := exists_cutoffLevel_radii
    (fun p ↦ (Φ p).toOpenPartialHomeomorph) hs0 hsrc
    (fun p q h ↦ Subtype.ext ((hW p).apply_zero.symm.trans (h.trans (hW q).apply_zero)))
    (k := fun p j ↦ α p j ξ) (fun p j ↦ hα p j) hfc hθ0
    (fun x hx ↦ ⟨⟨x, (hθz x).1 hx⟩, (hW ⟨x, (hθz x).1 hx⟩).apply_zero.symm⟩) hħ
  let F : ContDiffBump (0 : ℝ) := ⟨δ / 2, δ, half_pos hδ, half_lt_self hδ⟩
  have hFδ : tsupport F ⊆ Icc (-δ) δ := by
    rw [F.tsupport_eq, Real.closedBall_eq_Icc]; simp [F]
  have hF0 : F 0 = 1 := F.one_of_mem_closedBall (mem_closedBall_self (half_pos hδ).le)
  -- `F(d_ħ θ)` cut into pieces `γ p` near the fixed points.
  obtain ⟨γ, c, hcb, hγ, hγc, hγb, hsum⟩ := exists_formCalculus_eq_sum (X := X) (hX := hX)
    (ħ := ħ) Φ (fun p ↦ (hab p).2.1) (fun p ↦ (ball_subset_ball (hab p).2.2).trans (hsrc p)) hd
    hθL hδa F F.contDiff hFδ
  -- The contribution of each piece.
  have hterm (p : S) : integralTopForm o ((γ p * e) (2 * n)).val =
      Real.exp (-ħ * H p) / (ħ ^ n * ∏ j, (k p j : ℝ)) := by
    have hcr : c p < r p := ((hcb p).trans_le (hab p).2.2).trans_le (hsr p)
    rw [IsWeightChart.integralTopForm_mul_formCalculus_exp (hW p) hH (hγ p) hcr (hγc p) o,
      integralTopForm_piece_weightChart hσ.isNondegenerate (hW p) (hα p)
        ((hab p).2.2.trans (hsr p))
        (fun x hx ↦ hθΦ p x (image_mono (ball_subset_ball (hab p).2.2) hx)) F.contDiff
        F.hasCompactSupport hF0 hħ hFδ (hab p).2.1 (hcb p) (hδz p) (hγc p) (hγb p),
      (hW p).prod_apply_circlePeriodOneGenerator_eq (hk p p.property).choose_spec, mul_one_div]
  -- Each piece is a smooth top form on a compact manifold, so integrable.
  have hint (p : S) : IntegrableTopForm ((γ p * e) (2 * n)).val :=
    ((γ p * e) (2 * n)).isSmoothForm.integrableTopForm
      (isClosed_tsupport _).isCompact
      (Module.finBasisOfFinrankEq ℝ E (by simpa using o.card_eq.symm))
  rw [← integralTopForm_formCalculus_mul o F F.contDiff hF0 hθL he, hsum, Finset.sum_mul,
    DirectSum.sum_apply, Submodule.coe_sum, integralTopForm_sum o _ _ fun p _ ↦ hint p,
    Finset.sum_congr rfl fun p _ ↦ hterm p, ← finsum_set_coe_eq_finsum_mem,
    finsum_eq_sum_of_fintype]

end SymplecticGeometry

end
