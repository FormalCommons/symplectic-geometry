/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Geometry.Manifold.Algebra.Structures
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import TauCeti.Analysis.InnerProductSpace.Calculus
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

For a map `φ : M → W` into a normed group and a zero `x` of `φ` that is an interior point, the
function `p ↦ ‖φ p‖²` has a minimum, hence a critical point, at `x`
(`TauCeti.mem_criticalPoints_norm_sq_of_eq_zero`). If moreover `W` is a real inner product space,
`M` is boundaryless and `φ` is `C²` at `x`, its critical Hessian there is `2 ⟪dφ u, dφ w⟫`
(`TauCeti.criticalHessian_norm_sq_apply_of_eq_zero`), by the second-order chain rule and Tau
Ceti's `TauCeti.fderiv_fderiv_norm_sq_apply`. For `φ = A ∘ ψ`, with `A` a continuous linear map
and `ψ` `C²` at a zero `x` of `A ∘ ψ`, this reads `2 ⟪A (dψ u), A (dψ w)⟫`
(`TauCeti.criticalHessian_norm_sq_continuousLinearMap_comp_apply_of_eq_zero`).

Let the functions `g i` be `C²`, vanish and be critical at an interior point `x` whenever
`x ∈ U i`, with critical Hessians there positive on a vector `v`. Then a finite sum
`∑ i ∈ s, b i * g i`, with nonnegative `C²` cut-offs `b i` supported in `U i` and some
`b i x > 0`, has critical Hessian positive on `v` at `x` (`TauCeti.criticalHessian_sum_mul_pos`):
near `x` only the terms with `x ∈ U i` remain, and each contributes `b i x` times the Hessian of
`g i`. This adapts Tau Ceti's first-order `SmoothPartitionOfUnity.mvfderiv_finsum_smul_pos` to
second derivatives, with the same steps. For a smooth partition of unity `φ` on a set containing
`x`, subordinate to `U`, the sum `∑ᶠ i, φ i • g i` agrees near `x` with such a finite sum, so its
critical Hessian is positive on `v` too (`SmoothPartitionOfUnity.criticalHessian_finsum_smul_pos`).

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

/-- **The critical Hessian of a finite sum of cut-off functions at a common critical zero.** Let
`x` be an interior point and `s` a finite set of indices. For `i ∈ s`, let `b i` be `C²` at `x`,
nonnegative at `x`, with topological support in `U i`, and let `g i` be `C²`, vanish, be critical,
and have critical Hessian positive on `v` at `x` whenever `x ∈ U i`. If `b i x > 0` for some
`i ∈ s`, then the critical Hessian of `∑ i ∈ s, b i * g i` at `x` is positive on `v`. -/
theorem criticalHessian_sum_mul_pos {ι : Type*} {s : Finset ι} {b g : ι → M → ℝ}
    {U : ι → Set M} (hx : I.IsInteriorPoint x) (hbU : ∀ i ∈ s, tsupport (b i) ⊆ U i)
    (hb : ∀ i ∈ s, ContMDiffAt I 𝓘(ℝ) 2 (b i) x) (hb0 : ∀ i ∈ s, 0 ≤ b i x)
    (hg : ∀ i ∈ s, x ∈ U i → ContMDiffAt I 𝓘(ℝ) 2 (g i) x)
    (h0 : ∀ i ∈ s, x ∈ U i → g i x = 0) (hc : ∀ i ∈ s, x ∈ U i → x ∈ criticalPoints I (g i))
    {v : TangentSpace I x} (hpos : ∀ i ∈ s, x ∈ U i → 0 < criticalHessian I (g i) x v v)
    (hj : ∃ i ∈ s, 0 < b i x) :
    0 < criticalHessian I (∑ i ∈ s, b i * g i) x v v := by
  classical
  -- Near `x`, the terms with `x ∉ U i` vanish, since then `x ∉ tsupport (b i)`.
  have heq : ∑ i ∈ s, b i * g i =ᶠ[𝓝 x] ∑ i ∈ s with x ∈ U i, b i * g i := by
    have hev : ∀ᶠ y in 𝓝 x, ∀ i ∈ s, x ∉ U i → b i y = 0 :=
      (s.eventually_all.2 fun i hi ↦ by
        by_cases hxi : x ∈ U i
        · exact Eventually.of_forall fun _ h ↦ absurd hxi h
        · filter_upwards [notMem_tsupport_iff_eventuallyEq.1 fun h ↦ hxi (hbU i hi h)]
            with y hy _
          exact hy)
    filter_upwards [hev] with y hy
    simp only [Finset.sum_apply, Pi.mul_apply, Finset.sum_filter]
    exact Finset.sum_congr rfl fun i hi ↦ by split_ifs with h <;> simp [hy i hi, h]
  rw [criticalHessian_congr_of_eventuallyEq heq, criticalHessian_sum _ (fun i hi ↦
      (Finset.mem_filter.1 hi).elim fun his hxi ↦ (hb i his).mul (hg i his hxi)) hx,
    Finset.sum_congr rfl fun i hi ↦ (Finset.mem_filter.1 hi).elim fun his hxi ↦
      criticalHessian_mul_of_mem_criticalPoints (hb i his) (hg i his hxi) hx (h0 i his hxi)
        (hc i his hxi)]
  simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
    Pi.smul_apply, smul_eq_mul]
  obtain ⟨j, hjs, hj⟩ := hj
  have hjU : x ∈ U j := hbU j hjs (subset_tsupport _ hj.ne')
  exact Finset.sum_pos' (fun i hi ↦ (Finset.mem_filter.1 hi).elim fun his hxi ↦
      mul_nonneg (hb0 i his) (hpos i his hxi).le)
    ⟨j, Finset.mem_filter.2 ⟨hjs, hjU⟩, mul_pos hj (hpos j hjs hjU)⟩

end Algebra

section NormSq

variable {E H M W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [NormedAddCommGroup W] {φ : M → W} {x : M}

/-- An interior point `x` where a map `φ` into a normed group vanishes is a critical point of
`p ↦ ‖φ p‖²`, which takes its minimum `0` there. -/
theorem mem_criticalPoints_norm_sq_of_eq_zero (hφx : φ x = 0) (hx : I.IsInteriorPoint x) :
    x ∈ criticalPoints I (fun p ↦ ‖φ p‖ ^ 2) := by
  refine IsLocalMin.mem_criticalPoints (Eventually.of_forall fun p ↦ ?_) hx
  simp only [hφx, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
  positivity

/-- **The Hessian of `‖φ‖²` at a zero of `φ`.** On a boundaryless manifold, if a map `φ` into a
real inner product space is `C²` at `x` and vanishes there, then the critical Hessian of
`p ↦ ‖φ p‖²` at `x` is `2 ⟪dφ u, dφ w⟫`. -/
theorem criticalHessian_norm_sq_apply_of_eq_zero [InnerProductSpace ℝ W] [I.Boundaryless]
    (hφ : ContMDiffAt I 𝓘(ℝ, W) 2 φ x) (hφx : φ x = 0) (u w : TangentSpace I x) :
    criticalHessian I (fun p ↦ ‖φ p‖ ^ 2) x u w =
      2 * inner ℝ (E := W) (mfderiv I 𝓘(ℝ, W) φ x u) (mfderiv I 𝓘(ℝ, W) φ x w) := by
  have hcrit : φ x ∈ criticalPoints 𝓘(ℝ, W) (fun z : W ↦ ‖z‖ ^ 2) :=
    mem_criticalPoints_norm_sq_of_eq_zero (φ := id) hφx BoundarylessManifold.isInteriorPoint
  -- The second-order chain rule at the critical point `φ x = 0` of `‖·‖²`.
  have hH := criticalHessian_comp_apply (f := fun z : W ↦ ‖z‖ ^ 2) rfl
    (contDiff_norm_sq ℝ).contMDiff.contMDiffAt hφ hcrit u w
  rw [criticalHessian_modelSpace] at hH
  exact hH.trans (fderiv_fderiv_norm_sq_apply (E := W) _ _ _)

variable [InnerProductSpace ℝ W] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {A : F →L[ℝ] W} {ψ : M → F}

/-- **The Hessian of `‖A ∘ ψ‖²` at a zero.** On a boundaryless manifold, let `ψ` be a map into a
real normed space that is `C²` at `x`, and `A` a continuous linear map into a real inner product
space with `A (ψ x) = 0`. Then the critical Hessian of `p ↦ ‖A (ψ p)‖²` at `x` is
`2 ⟪A (dψ u), A (dψ w)⟫`. -/
theorem criticalHessian_norm_sq_continuousLinearMap_comp_apply_of_eq_zero [I.Boundaryless]
    (hψ : ContMDiffAt I 𝓘(ℝ, F) 2 ψ x) (hψx : A (ψ x) = 0) (u w : TangentSpace I x) :
    criticalHessian I (fun p ↦ ‖A (ψ p)‖ ^ 2) x u w =
      2 * inner ℝ (A (mfderiv I 𝓘(ℝ, F) ψ x u)) (A (mfderiv I 𝓘(ℝ, F) ψ x w)) := by
  have hD : mfderiv I 𝓘(ℝ, W) (fun p ↦ A (ψ p)) x = A.comp (mfderiv I 𝓘(ℝ, F) ψ x) :=
    (A.hasFDerivAt.hasMFDerivAt.comp x (hψ.mdifferentiableAt two_ne_zero).hasMFDerivAt).mfderiv
  refine (criticalHessian_norm_sq_apply_of_eq_zero (φ := fun p ↦ A (ψ p))
    (A.contDiff.contMDiff.contMDiffAt.comp x hψ) hψx u w).trans ?_
  rw [hD]
  -- `(A ∘L dψ) u` is `A (dψ u)` by definition of the composite. `dψ` takes values in
  -- `TangentSpace 𝓘(ℝ, F) _`, which is `F` only by definition, so `comp_apply` cannot be
  -- rewritten with here.
  rfl

end NormSq

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

/-- **The glued critical Hessian at a common critical zero.** Let `φ` be a smooth partition of
unity on a set `s` subordinate to `U`, and `q ∈ s` an interior point at which, for every `i` with
`q ∈ U i`, the function `g i` is `C²`, vanishes, and is critical. If the critical Hessian of every
such `g i` at `q` is positive on `v`, then so is that of `∑ᶠ i, φ i • g i`. -/
theorem criticalHessian_finsum_smul_pos (hφ : φ.IsSubordinate U) (hq : q ∈ s)
    (hqI : I.IsInteriorPoint q) (hg : ∀ i, q ∈ U i → ContMDiffAt I 𝓘(ℝ) 2 (g i) q)
    (h0 : ∀ i, q ∈ U i → g i q = 0) (hc : ∀ i, q ∈ U i → q ∈ criticalPoints I (g i))
    {v : TangentSpace I q} (hpos : ∀ i, q ∈ U i → 0 < criticalHessian I (g i) q v v) :
    0 < criticalHessian I (fun x ↦ ∑ᶠ i, φ i x • g i x) q v v := by
  -- Near `q` the sum runs over the finite set of `i` with `q` in the topological support of `φ i`.
  have heq : (fun x ↦ ∑ᶠ i, φ i x • g i x) =ᶠ[𝓝 q] ∑ i ∈ φ.fintsupport q, ⇑(φ i) * g i := by
    filter_upwards [φ.eventually_fintsupport_subset q] with y hy
    simp only [Finset.sum_apply, ← smul_eq_mul]
    refine finsum_eq_sum_of_support_subset _ fun i hi ↦ hy ?_
    exact (φ.mem_fintsupport_iff y i).mpr (subset_tsupport _ (left_ne_zero_of_smul hi))
  rw [criticalHessian_congr_of_eventuallyEq heq]
  obtain ⟨j, hj⟩ := φ.exists_pos_of_mem hq
  exact criticalHessian_sum_mul_pos (U := fun i ↦ U i) hqI (fun i _ ↦ hφ i)
    (fun i _ ↦ ((φ i).contMDiff.of_le (by simp)).contMDiffAt) (fun i _ ↦ φ.nonneg i q)
    (fun i _ ↦ hg i) (fun i _ ↦ h0 i) (fun i _ ↦ hc i) (fun i _ ↦ hpos i)
    ⟨j, (φ.mem_fintsupport_iff q j).mpr (subset_tsupport _ hj.ne'), hj⟩

end SmoothPartitionOfUnity

end
