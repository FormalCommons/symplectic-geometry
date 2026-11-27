/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Density
import Mathlib.Geometry.Manifold.PartitionOfUnity
import TauCeti.Geometry.Manifold.ContMDiffMap.Extension

/-!
# Global bounds on Sobolev sections from bounds in single charts

Let `A` be a finite bundle atlas of a vector bundle `V` over a Hausdorff manifold `M`, and
`W^{k,p}(V)` the Sobolev space `TauCeti.SobolevSection A μ p k`, with `1 ≤ p < ∞`. This file shows
that a global bound `‖w‖ ≤ C f w`, for a continuous function `f` on `W^{k,p}(V)` such as the sum of
the norm of an operator applied to `w` and a weaker norm of `w`, follows from bounds of the
chart-`i` components of `χ w` by multiples of `f w`, for `χ` smooth with support in the domain of
chart `i`, proved only for the Sobolev sections of smooth sections. This is the global step of the
a priori estimates for elliptic operators on sections, which is independent of the operator, of
the order and of the bundle.

## Main results

* `TauCeti.SobolevSection.exists_norm_le_of_forall_component_le`: the global bound from the
  chartwise bounds on smooth sections. A smooth partition of unity `χᵢ` subordinate to the chart
  domains writes `w` as `∑ χᵢ w`. A cutoff `ψᵢ` equal to one on the support of `χᵢ` fixes `χᵢ w`,
  so the norm of `χᵢ w` is controlled by its chart-`i` part
  (`TauCeti.SobolevSection.exists_norm_contMDiffSMulL_le`), and so by `f w`. The bound is a closed
  condition, and the Sobolev sections of smooth sections are dense
  (`TauCeti.SobolevSection.dense_ofContMDiffSection_contMDiff`).

The proof of `exists_norm_le_of_forall_component_le` is the global step of the proof of Tau Ceti's
`TauCeti.IsRealCauchyRiemannOperator.exists_norm_le_norm_sobolevSuccL_add_norm_lowerOrderL`
(`TauCeti/Geometry/Manifold/VectorBundle/Sobolev/CauchyRiemann/HigherOrder/Estimate.lean`), for an
arbitrary continuous right-hand side in place of the one of a real Cauchy–Riemann operator.

## References

* [D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*][McDuffSalamon2012],
  Appendix B.
-/

public section

open Bundle MeasureTheory Set
open scoped Manifold ContDiff ENNReal

universe u

namespace TauCeti

namespace SobolevSection

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  {A : FiniteBundleAtlas E M F V} {μ : Measure E} [μ.IsAddHaarMeasure] {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {k : ℕ} [IsManifold 𝓘(ℝ, E) ∞ M] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, E)] [T2Space M]

/-- **Global bounds from bounds in single charts.** Let `1 ≤ p < ∞` and let `f` be a continuous
real function on `W^{k,p}(V)`. Suppose that for every chart `i` and every smooth `χ` whose support
has closure in the domain of chart `i` there is a constant `C` such that, for every smooth section
`s`, the chart-`i` part of `χ s` has norm at most `C f s`. Then there is a constant `C` with
`‖w‖ ≤ C f w` for every `w ∈ W^{k,p}(V)`. -/
theorem exists_norm_le_of_forall_component_le (hp : p ≠ ⊤)
    {f : SobolevSection A μ p k → ℝ} (hf : Continuous f)
    (h : ∀ (i : Fin A.n) {χ : M → ℝ} (hχ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ χ),
      tsupport χ ⊆ A.dom i → ∃ C : ℝ, ∀ s : Cₛ^k⟮𝓘(ℝ, E); F, V⟯,
        ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F)) ∞ (fun x ↦ TotalSpace.mk' F x (s x)) →
        ‖(contMDiffSMulL A μ p k hχ (ofContMDiffSection A μ p k s) :
          A.sectionChartData.SobolevData μ p k) i‖ ≤ C * f (ofContMDiffSection A μ p k s)) :
    ∃ C : ℝ, ∀ w : SobolevSection A μ p k, ‖w‖ ≤ C * f w := by
  have := A.compactSpace
  -- A partition of unity subordinate to the chart domains, and cutoffs equal to one on its
  -- supports.
  obtain ⟨χ, hχ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, E) isClosed_univ A.dom
    A.isOpen_dom (by rw [A.iUnion_dom])
  have hχ1 (x : M) : ∑ i, χ i x = 1 := by
    simpa [finsum_eq_sum_of_fintype] using χ.sum_eq_one (mem_univ x)
  choose ψ hψ _ hψi hψ1 using fun i ↦
    (isClosed_tsupport (χ i)).exists_contMDiff_tsupport_subset_eq_one_iff (I := 𝓘(ℝ, E))
      (A.isOpen_dom i) (hχ i)
  choose Cψ hCψ using fun i ↦
    exists_norm_contMDiffSMulL_le (μ := μ) (p := p) (k := k) (hψ i) (hψi i)
  choose Cc hCc using fun i ↦ h i (χ i).contMDiff (hχ i)
  set C := ∑ i, max (Cψ i) 0 * Cc i
  refine ⟨C, fun w ↦ ?_⟩
  -- The bound is a closed condition, so it suffices to prove it on the dense set of smooth
  -- sections.
  have hP : IsClosed {w : SobolevSection A μ p k | ‖w‖ ≤ C * f w} :=
    isClosed_le continuous_norm (continuous_const.mul hf)
  refine hP.closure_subset_iff.2 ?_
    ((dense_ofContMDiffSection_contMDiff A μ p k hp).closure_eq ▸ mem_univ w)
  rintro _ ⟨s, hs, rfl⟩
  rw [mem_ofPred_eq]
  set w := ofContMDiffSection A μ p k s
  calc ‖w‖ = ‖∑ i, contMDiffSMulL A μ p k (χ i).contMDiff w‖ := by
        rw [sum_contMDiffSMulL_eq_self_of_sum_eq_one _ hχ1]
    _ ≤ ∑ i, ‖contMDiffSMulL A μ p k (χ i).contMDiff w‖ := norm_sum_le _ _
    _ ≤ ∑ i, max (Cψ i) 0 * Cc i * f w := Finset.sum_le_sum fun i _ ↦ ?_
    _ = C * f w := by rw [Finset.sum_mul]
  set v := contMDiffSMulL A μ p k (χ i).contMDiff w
  calc ‖v‖ = ‖contMDiffSMulL A μ p k (hψ i) v‖ := by
        rw [contMDiffSMulL_contMDiffSMulL_of_eqOn _ (hψ i) fun _ h ↦ (hψ1 i _).1 h]
    _ ≤ Cψ i * ‖(v : A.sectionChartData.SobolevData μ p k) i‖ := hCψ i v
    _ ≤ max (Cψ i) 0 * ‖(v : A.sectionChartData.SobolevData μ p k) i‖ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
    _ ≤ max (Cψ i) 0 * (Cc i * f w) := mul_le_mul_of_nonneg_left (hCc i s hs) (le_max_right _ _)
    _ = max (Cψ i) 0 * Cc i * f w := by ring

end SobolevSection

end TauCeti

end
