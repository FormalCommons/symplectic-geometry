/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.Structures
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import TauCeti.Geometry.Manifold.Morse.Hessian

/-!
# Positive directions of the critical Hessian in charts

At a critical point `x` of a function `f` that is `C²` at `x`, Tau Ceti's critical Hessian
`TauCeti.criticalHessian I f x` is the Hessian of a coordinate expression of `f`, transported by
the chart derivative (`TauCeti.criticalHessian_apply_eq_of_mem_maximalAtlas`). Since the chart
derivative is invertible (`TauCeti.isInvertible_mvfderiv_extend`), the critical Hessian is positive
on some tangent vector exactly when the coordinate Hessian is positive on some vector, in any chart
of the `C²` maximal atlas (`TauCeti.exists_criticalHessian_pos_iff_of_mem_maximalAtlas`).

It also says how the critical Hessian meets sums and products at an interior point where the
functions are `C²`: it is additive (`TauCeti.criticalHessian_add`,
`TauCeti.criticalHessian_sum`), and at a point where `g` and its differential vanish, the
critical Hessian of `f * g` is `f x` times that of `g`
(`TauCeti.criticalHessian_mul_of_mem_criticalPoints`), by the Leibniz rule for the second
derivative of the coordinate expressions (Tau Ceti's `TauCeti.fderiv_fderiv_add` and
`TauCeti.fderiv_fderiv_mul_apply`).

For a smooth partition of unity `φ` subordinate to `U`, and functions `g i` that are `C²`, vanish
and are critical at an interior point `q` whenever `q ∈ U i`, the critical Hessian of
`∑ᶠ i, φ i • g i` at `q` is `∑ φ i q • criticalHessian I (g i) q`
(`SmoothPartitionOfUnity.criticalHessian_finsum_smul`), so it is positive on a vector on which all
these Hessians are (`SmoothPartitionOfUnity.criticalHessian_finsum_smul_pos`). This adapts Tau
Ceti's first-order `SmoothPartitionOfUnity.mvfderiv_finsum_smul_pos` to second derivatives, with
the same steps.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §2, for the Hessian at a critical point.
-/

public section

open Filter Topology
open scoped Manifold

namespace TauCeti

section Algebra

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] {f g : M → ℝ} {x : M}

/-- The critical Hessian of the zero function vanishes. -/
@[simp]
theorem criticalHessian_zero : criticalHessian I (0 : M → ℝ) x = 0 := by
  have h : (0 : M → ℝ) ∘ (extChartAt I x).symm = fun _ ↦ 0 := rfl
  rw [criticalHessian_def, h, fderiv_fun_const, Pi.zero_def, fderiv_const_apply]
  -- The two sides differ only in reading `E` as the tangent space at `x`.
  rfl

/-- At an interior point where `f` and `g` are `C²`, the critical Hessian of `f + g` is the sum
of their critical Hessians. -/
theorem criticalHessian_add (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) (hg : ContMDiffAt I 𝓘(ℝ) 2 g x)
    (hx : I.IsInteriorPoint x) :
    criticalHessian I (f + g) x = criticalHessian I f x + criticalHessian I g x := by
  rw [criticalHessian_def, criticalHessian_def, criticalHessian_def]
  exact fderiv_fderiv_add (hf.contDiffAt_comp_extChartAt_symm_of_isInteriorPoint hx)
    (hg.contDiffAt_comp_extChartAt_symm_of_isInteriorPoint hx)

/-- At an interior point where the functions `f i`, `i ∈ s`, are `C²`, the critical Hessian of
their sum is the sum of their critical Hessians. -/
theorem criticalHessian_sum {ι : Type*} (s : Finset ι) {f : ι → M → ℝ}
    (hf : ∀ i ∈ s, ContMDiffAt I 𝓘(ℝ) 2 (f i) x) (hx : I.IsInteriorPoint x) :
    criticalHessian I (∑ i ∈ s, f i) x = ∑ i ∈ s, criticalHessian I (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      criticalHessian_add (hf i (Finset.mem_insert_self i s))
        (contMDiffAt_finsetSum' fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)) hx,
      ih fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)]

/-- **The critical Hessian of a product with a function vanishing to second order.** At an
interior point `x` where `f` and `g` are `C²`, if `g x = 0` and `x` is a critical point of `g`,
then the critical Hessian of `f * g` at `x` is `f x` times that of `g`. -/
theorem criticalHessian_mul_of_mem_criticalPoints (hf : ContMDiffAt I 𝓘(ℝ) 2 f x)
    (hg : ContMDiffAt I 𝓘(ℝ) 2 g x) (hx : I.IsInteriorPoint x) (hg0 : g x = 0)
    (hgc : x ∈ criticalPoints I g) :
    criticalHessian I (f * g) x = f x • criticalHessian I g x := by
  ext v w
  rw [criticalHessian_apply_eq_fderiv_fderiv, Pi.mul_comp,
    fderiv_fderiv_mul_apply (hf.contDiffAt_comp_extChartAt_symm_of_isInteriorPoint hx)
      (hg.contDiffAt_comp_extChartAt_symm_of_isInteriorPoint hx),
    fderiv_comp_extChartAt_symm_eq_zero_of_mem_criticalPoints hgc,
    smul_apply, smul_apply,
    criticalHessian_apply_eq_fderiv_fderiv]
  simp [hg0]

end Algebra

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M]

/-- At a critical point `x` of a function `f` which is `C²` at `x`, on a boundaryless manifold,
the critical Hessian is positive on some tangent vector exactly when, in a chart `e` of the `C²`
maximal atlas whose source contains `x`, the Hessian of the coordinate expression of `f` at the
image of `x` is positive on some vector. -/
theorem exists_criticalHessian_pos_iff_of_mem_maximalAtlas {f : M → ℝ} {x : M}
    {e : OpenPartialHomeomorph M H} (he : e ∈ IsManifold.maximalAtlas I 2 M) (hx : x ∈ e.source)
    (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) (hcrit : x ∈ criticalPoints I f) :
    (∃ v, 0 < criticalHessian I f x v v) ↔
      ∃ w : E, 0 < fderiv ℝ (fderiv ℝ (f ∘ (e.extend I).symm)) (e.extend I x) w w := by
  obtain ⟨D, hD⟩ :=
    isInvertible_mvfderiv_extend (IsManifold.maximalAtlas_subset_of_le (by norm_num) he) hx
  simp only [criticalHessian_apply_eq_of_mem_maximalAtlas he hx hf (mem_criticalPoints.mp hcrit)]
  refine ⟨fun ⟨v, hv⟩ ↦ ⟨_, hv⟩, fun ⟨w, hw⟩ ↦ ⟨D.symm w, ?_⟩⟩
  rwa [← hD, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]

end TauCeti

namespace SmoothPartitionOfUnity

open TauCeti

variable {ι E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {s : Set M}
  {φ : SmoothPartitionOfUnity ι I M s} {U : ι → Set M} {q : M} {g : ι → M → ℝ}

/-- **The critical Hessian of a partition-of-unity sum at a common critical zero.** Let `φ` be a
smooth partition of unity subordinate to `U`, and `q` an interior point at which, for every `i`
with `q ∈ U i`, the function `g i` is `C²`, vanishes, and is critical. Then the critical Hessian
of `∑ᶠ i, φ i • g i` at `q` is the sum of the `φ i q • criticalHessian I (g i) q` over the
indices `i` with `q` in the topological support of `φ i`. -/
theorem criticalHessian_finsum_smul (hφ : φ.IsSubordinate U) (hqI : I.IsInteriorPoint q)
    (hg : ∀ i, q ∈ U i → ContMDiffAt I 𝓘(ℝ) 2 (g i) q) (h0 : ∀ i, q ∈ U i → g i q = 0)
    (hc : ∀ i, q ∈ U i → q ∈ criticalPoints I (g i)) :
    criticalHessian I (fun x ↦ ∑ᶠ i, φ i x • g i x) q =
      ∑ i ∈ φ.fintsupport q, φ i q • criticalHessian I (g i) q := by
  have hU {i : ι} (hi : i ∈ φ.fintsupport q) : q ∈ U i :=
    hφ i ((φ.mem_fintsupport_iff q i).mp hi)
  have hφ2 (i : ι) : ContMDiffAt I 𝓘(ℝ) 2 (φ i) q :=
    ((φ i).contMDiff.of_le (by simp)).contMDiffAt
  -- Near `q` the sum runs over the finite set of `i` with `q` in the topological support of `φ i`.
  have heq : (fun x ↦ ∑ᶠ i, φ i x • g i x) =ᶠ[𝓝 q] ∑ i ∈ φ.fintsupport q, ⇑(φ i) * g i := by
    filter_upwards [φ.eventually_fintsupport_subset q] with y hy
    simp only [Finset.sum_apply, ← smul_eq_mul]
    refine finsum_eq_sum_of_support_subset _ fun i hi ↦ hy ?_
    exact (φ.mem_fintsupport_iff y i).mpr (subset_tsupport _ (left_ne_zero_of_smul hi))
  rw [criticalHessian_congr_of_eventuallyEq heq,
    criticalHessian_sum _ (fun i hi ↦ (hφ2 i).mul (hg i (hU hi))) hqI]
  exact Finset.sum_congr rfl fun i hi ↦ criticalHessian_mul_of_mem_criticalPoints (hφ2 i)
    (hg i (hU hi)) hqI (h0 i (hU hi)) (hc i (hU hi))

/-- **The glued critical Hessian at a common critical zero.** Let `φ` be a smooth partition of
unity on a set `s` subordinate to `U`, and `q ∈ s` an interior point at which, for every `i` with
`q ∈ U i`, the function `g i` is `C²`, vanishes, and is critical. If the critical Hessian of every
such `g i` at `q` is positive on `v`, then so is that of `∑ᶠ i, φ i • g i`. -/
theorem criticalHessian_finsum_smul_pos (hφ : φ.IsSubordinate U) (hq : q ∈ s)
    (hqI : I.IsInteriorPoint q) (hg : ∀ i, q ∈ U i → ContMDiffAt I 𝓘(ℝ) 2 (g i) q)
    (h0 : ∀ i, q ∈ U i → g i q = 0) (hc : ∀ i, q ∈ U i → q ∈ criticalPoints I (g i))
    {v : TangentSpace I q} (hpos : ∀ i, q ∈ U i → 0 < criticalHessian I (g i) q v v) :
    0 < criticalHessian I (fun x ↦ ∑ᶠ i, φ i x • g i x) q v v := by
  have hU {i : ι} (hi : i ∈ φ.fintsupport q) : q ∈ U i :=
    hφ i ((φ.mem_fintsupport_iff q i).mp hi)
  rw [criticalHessian_finsum_smul hφ hqI hg h0 hc]
  simp only [FunLike.coe_sum, Finset.sum_apply, smul_apply,
    smul_eq_mul]
  obtain ⟨j, hj⟩ := φ.exists_pos_of_mem hq
  have hjF : j ∈ φ.fintsupport q := (φ.mem_fintsupport_iff q j).mpr (subset_tsupport _ hj.ne')
  exact Finset.sum_pos' (fun i hi ↦ mul_nonneg (φ.nonneg i q) (hpos i (hU hi)).le)
    ⟨j, hjF, mul_pos hj (hpos j (hU hjF))⟩

end SmoothPartitionOfUnity

end
