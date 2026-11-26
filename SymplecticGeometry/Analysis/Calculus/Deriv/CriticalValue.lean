/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Critical values of functions of one real variable

The critical values of a function `f : ℝ → ℝ`, the values `f t` at points `t` where `f` has
derivative zero, form a null set for every additive Haar measure on `ℝ`. This is the
one-dimensional case of Sard's lemma, Mathlib's
`MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`; no regularity of `f` is
needed, since only the points where `f` is differentiable with derivative zero count.

So for countably many differentiable functions `f i : ℝ → ℝ`, almost every `c` is a common
regular value: at every `t` with `f i t = c` the derivative of `f i` is nonzero, and `f i` takes
the value `c` at no other point near `t`. In particular every nonempty open interval contains
such a `c`. A level chosen this way is crossed cleanly by finitely many curves at once.

## Main results

* `addHaar_image_setOf_hasDerivAt_zero`: the critical values of `f : ℝ → ℝ` form a null set.
* `ae_forall_apply_eq_imp_not_hasDerivAt_zero`: almost every `c` is a regular value of each of
  countably many functions `ℝ → ℝ`.
* `ae_forall_apply_eq_imp_deriv_ne_zero`: for countably many differentiable functions, almost
  every `c` is a common regular value, and each function avoids `c` on a punctured
  neighbourhood of each point where it takes the value `c`.
* `exists_mem_Ioo_forall_apply_eq_imp_deriv_ne_zero`: such a `c` exists in every nonempty open
  interval.

## References

* [J. Milnor, *Topology from the differentiable viewpoint*, University Press of Virginia, 1965],
  §2–3 (Sard's theorem and regular values)
-/

public section

namespace SymplecticGeometry

open Set Filter MeasureTheory Measure Topology

variable (μ : Measure ℝ) [μ.IsAddHaarMeasure]

/-- The critical values of a function `f : ℝ → ℝ`, the values `f t` at the points `t` where `f`
has derivative zero, form a null set for every additive Haar measure. -/
theorem addHaar_image_setOf_hasDerivAt_zero (f : ℝ → ℝ) :
    μ (f '' {t | HasDerivAt f 0 t}) = 0 :=
  addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ (f' := fun _ ↦ 0)
    (fun _ ht ↦ by simpa using (HasDerivAt.hasFDerivAt ht).hasFDerivWithinAt)
    fun _ _ ↦ by simp

/-- For countably many functions `f i : ℝ → ℝ`, almost every `c` is a regular value of each of
them: no `f i` has derivative zero at a point where it takes the value `c`. -/
theorem ae_forall_apply_eq_imp_not_hasDerivAt_zero {ι : Type*} [Countable ι] (f : ι → ℝ → ℝ) :
    ∀ᵐ c ∂μ, ∀ i t, f i t = c → ¬HasDerivAt (f i) 0 t := by
  refine ae_all_iff.2 fun i ↦ ?_
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 (addHaar_image_setOf_hasDerivAt_zero μ (f i))]
    with c hc t htc ht
  exact hc ⟨t, ht, htc⟩

/-- For countably many differentiable functions `f i : ℝ → ℝ`, almost every `c` is a common
regular value: at each `t` with `f i t = c` the derivative of `f i` is nonzero, and `f i` differs
from `c` at every point near `t` other than `t`. -/
theorem ae_forall_apply_eq_imp_deriv_ne_zero {ι : Type*} [Countable ι] {f : ι → ℝ → ℝ}
    (hf : ∀ i, Differentiable ℝ (f i)) :
    ∀ᵐ c ∂μ, ∀ i t, f i t = c → deriv (f i) t ≠ 0 ∧ ∀ᶠ u in 𝓝[≠] t, f i u ≠ c := by
  filter_upwards [ae_forall_apply_eq_imp_not_hasDerivAt_zero μ f] with c hc i t htc
  have hd : deriv (f i) t ≠ 0 := fun h0 ↦ hc i t htc (h0 ▸ (hf i t).hasDerivAt)
  exact ⟨hd, htc ▸ (hf i t).hasDerivAt.eventually_ne hd⟩

/-- For countably many differentiable functions `f i : ℝ → ℝ` and `a < b`, some `c ∈ (a, b)` is
a common regular value: at each `t` with `f i t = c` the derivative of `f i` is nonzero, and
`f i` differs from `c` at every point near `t` other than `t`. -/
theorem exists_mem_Ioo_forall_apply_eq_imp_deriv_ne_zero {ι : Type*} [Countable ι]
    {f : ι → ℝ → ℝ} (hf : ∀ i, Differentiable ℝ (f i)) {a b : ℝ} (hab : a < b) :
    ∃ c ∈ Ioo a b, ∀ i t, f i t = c → deriv (f i) t ≠ 0 ∧ ∀ᶠ u in 𝓝[≠] t, f i u ≠ c := by
  obtain ⟨c, hc, hcab⟩ :=
    (dense_of_ae (ae_forall_apply_eq_imp_deriv_ne_zero volume hf)).exists_between hab
  exact ⟨c, hcab, hc⟩

end SymplecticGeometry

end
