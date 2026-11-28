/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Smooth
import TauCeti.Geometry.Manifold.DifferentialForm.ExtDeriv

/-!
# Limits of smooth forms that settle on the open sets of a cover

Let `η n` be smooth `k`-forms on `M` and `V n` open sets covering `M`, such that `η m` agrees
with `η n` on `V n` whenever `n ≤ m`: near each point the sequence is eventually constant. Its
pointwise limit is then a smooth form, equal to `η n` on `V n`, and its exterior derivative is
equal to that of `η n` on `V n` (`TauCeti.SmoothForm.exists_eq_limit`). A typical cover is an
exhaustion of `M` by the interiors of compact sets.

For forms `γ n` that vanish on the sets `V n` of an increasing open cover, the partial sums
`∑ i ∈ Finset.range n, γ i` satisfy these hypotheses, so the series `∑ γ n`, a locally finite
sum, is a smooth form, equal to its `n`-th partial sum on `V n`, and its exterior derivative is
there the `n`-th partial sum of the series `∑ d γ n` (`TauCeti.SmoothForm.exists_eq_sum_range`).

Both rest on the locality of the exterior derivative: at a point of an open set on which two
smooth forms agree, their exterior derivatives agree
(`TauCeti.SmoothForm.mextDerivₗ_apply_eq_of_forall_mem`), by Tau Ceti's
`TauCeti.mextDeriv_congr_of_eventuallyEq`.

## Main results

* `TauCeti.SmoothForm.mextDerivₗ_apply_eq_of_forall_mem`: the exterior derivative is local.
* `TauCeti.SmoothForm.exists_eq_limit`: the limit of a sequence of smooth forms that settles
  on the open sets of a cover, with its exterior derivative.
* `TauCeti.SmoothForm.exists_eq_sum_range`: the sum of a series of smooth forms whose `n`-th term
  vanishes on the `n`-th set of an increasing open cover, with its exterior derivative.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 14 (locality of the exterior derivative).
-/

public section

open Filter
open scoped Manifold Topology ContDiff

namespace TauCeti.SmoothForm

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- **The exterior derivative is local.** Smooth forms that agree on an open set `U` have
exterior derivatives that agree on `U`. -/
theorem mextDerivₗ_apply_eq_of_forall_mem [IsManifold I 2 M] {φ ψ : SmoothForm I M F k}
    {U : Set M} (hU : IsOpen U) (h : ∀ y ∈ U, φ.val y = ψ.val y) {x : M} (hx : x ∈ U) :
    (mextDerivₗ I k φ).val x = (mextDerivₗ I k ψ).val x := by
  rw [mextDerivₗ_apply, mextDerivₗ_apply]
  exact mextDeriv_congr_of_eventuallyEq (Filter.mem_of_superset (hU.mem_nhds hx) h)

/-- **The limit of smooth forms that settle on the open sets of a cover.** Let `V n` be open
sets covering `M` and `η n` smooth forms such that `η m = η n` on `V n` for `n ≤ m`. Then there
is a smooth form `θ` equal to `η n` on each `V n`, whose exterior derivative is equal to that
of `η n` on each `V n`. -/
theorem exists_eq_limit [IsManifold I 2 M] {η : ℕ → SmoothForm I M F k} {V : ℕ → Set M}
    (hVo : ∀ n, IsOpen (V n)) (hV : ∀ x, ∃ n, x ∈ V n)
    (hη : ∀ n m, n ≤ m → ∀ x ∈ V n, (η m).val x = (η n).val x) :
    ∃ θ : SmoothForm I M F k, ∀ n, ∀ x ∈ V n, θ.val x = (η n).val x ∧
      (mextDerivₗ I k θ).val x = (mextDerivₗ I k (η n)).val x := by
  choose p hp using hV
  have heq : ∀ n, ∀ x ∈ V n, (η (p x)).val x = (η n).val x := fun n x hx ↦ by
    rcases le_total (p x) n with h | h
    · exact (hη _ _ h x (hp x)).symm
    · exact hη _ _ h x hx
  have hsmooth : IsSmoothForm I ∞ (fun x ↦ (η (p x)).val x) := by
    refine (isSmoothForm_def _ _).2 fun x ↦ ?_
    refine ((η (p x)).contMDiff x).congr_of_eventuallyEq ?_
    filter_upwards [(hVo (p x)).mem_nhds (hp x)] with y hy
    rw [heq (p x) y hy]
  let θ : SmoothForm I M F k := ⟨_, hsmooth.mem_smoothBundleForms⟩
  exact ⟨θ, fun n x hx ↦
    ⟨heq n x hx, mextDerivₗ_apply_eq_of_forall_mem (hVo n) (heq n) hx⟩⟩

/-- **The sum of a series of smooth forms that vanish on the sets of an increasing cover.** Let
`V n` be an increasing sequence of open sets covering `M` and `γ n` smooth forms with `γ n = 0`
on `V n`. Then there is a smooth form `σ`, equal on each `V n` to the partial sum
`∑ i ∈ Finset.range n, γ i`, whose exterior derivative is equal on each `V n` to
`∑ i ∈ Finset.range n, d γ i`. -/
theorem exists_eq_sum_range [IsManifold I 2 M] {γ : ℕ → SmoothForm I M F k} {V : ℕ → Set M}
    (hVo : ∀ n, IsOpen (V n)) (hVm : Monotone V) (hV : ∀ x, ∃ n, x ∈ V n)
    (hγ : ∀ n, ∀ x ∈ V n, (γ n).val x = 0) :
    ∃ σ : SmoothForm I M F k, ∀ n, ∀ x ∈ V n, σ.val x = (∑ i ∈ Finset.range n, γ i).val x ∧
      (mextDerivₗ I k σ).val x = (∑ i ∈ Finset.range n, mextDerivₗ I k (γ i)).val x := by
  have hS : ∀ n m, n ≤ m → ∀ x ∈ V n,
      (∑ i ∈ Finset.range m, γ i).val x = (∑ i ∈ Finset.range n, γ i).val x :=
    fun n m hnm x hx ↦ by
      rw [← Finset.sum_range_add_sum_Ico _ hnm, SmoothBundleForm.add_apply, add_eq_left,
        SmoothBundleForm.sum_apply]
      exact Finset.sum_eq_zero fun i hi ↦ hγ i x (hVm (Finset.mem_Ico.1 hi).1 hx)
  obtain ⟨σ, hσ⟩ := exists_eq_limit hVo hV hS
  exact ⟨σ, fun n x hx ↦ ⟨(hσ n x hx).1, by rw [(hσ n x hx).2, map_sum]⟩⟩

end TauCeti.SmoothForm

end
