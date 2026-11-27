/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.UniformSpace.HeineCantor
import TauCeti.Analysis.Calculus.FDeriv.Prod

/-!
# Uniform estimates for a family on a compact rectangle

Let `f : ℝ → ℝ → ℝ` be a family of real functions, `(ℓ, r) ↦ f ℓ r`, smooth on an open set `U`
that contains a compact rectangle `[a, b] × K`. Compactness turns pointwise information on the
partial derivatives into estimates that hold uniformly on the rectangle:

* `IsCompact.exists_pos_mul_sub_le_sub_of_deriv_pos`: if `f` is `C¹` and `∂f/∂ℓ > 0` on the
  rectangle, then `f` increases in `ℓ` at a uniform rate: there is `m > 0` with
  `m (ℓ' - ℓ) ≤ f ℓ' r - f ℓ r` for `ℓ ≤ ℓ'` in `[a, b]` and `r ∈ K`;
* `IsCompact.exists_abs_deriv_sub_le_mul`: if `f` is `C²`, then the derivative `∂f/∂r` is
  Lipschitz in `ℓ`, with one constant for all `r ∈ K`;
* `IsCompact.exists_pos_abs_sub_lt_of_continuousOn`: a function continuous on the rectangle is
  uniformly continuous in `ℓ`, uniformly in `r ∈ K` (Heine–Cantor,
  `IsCompact.uniformContinuousOn_of_continuous`).

The first two come from the continuity of the partial derivatives `∂f/∂ℓ` and `∂²f/∂ℓ∂r` on `U`,
which attain a positive minimum, respectively a bound, on the rectangle, and from the mean value
theorem on the segment from `(ℓ, r)` to `(ℓ', r)`, which stays in the rectangle. The partial
derivatives are read off the derivative of `Function.uncurry f` with Tau Ceti's slice lemmas
`TauCeti.hasDerivAt_slice_left`, `TauCeti.hasDerivAt_slice_right` and
`TauCeti.hasDerivAt_fderiv_apply_fst`.
-/

public section

open Set

variable {f : ℝ → ℝ → ℝ} {a b : ℝ} {K : Set ℝ} {U : Set (ℝ × ℝ)}

/-- Let `f : ℝ → ℝ → ℝ` be `C¹` on an open set `U` containing the compact rectangle `[a, b] × K`,
with `∂f/∂ℓ > 0` on the rectangle. Then `f` increases in its first variable at a uniform rate:
there is `m > 0` with `m (ℓ' - ℓ) ≤ f ℓ' r - f ℓ r` whenever `r ∈ K` and `ℓ ≤ ℓ'` lie in
`[a, b]`. -/
theorem IsCompact.exists_pos_mul_sub_le_sub_of_deriv_pos (hK : IsCompact K) (hU : IsOpen U)
    (hKU : Icc a b ×ˢ K ⊆ U) (hf : ContDiffOn ℝ 1 (Function.uncurry f) U)
    (hpos : ∀ x ∈ Icc a b ×ˢ K, 0 < deriv (fun ℓ ↦ f ℓ x.2) x.1) :
    ∃ m > 0, ∀ r ∈ K, ∀ ℓ ∈ Icc a b, ∀ ℓ' ∈ Icc a b, ℓ ≤ ℓ' →
      m * (ℓ' - ℓ) ≤ f ℓ' r - f ℓ r := by
  have hd : ∀ x ∈ U, DifferentiableAt ℝ (Function.uncurry f) x := fun x hx ↦
    (hf.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hx)
  -- On the rectangle, `∂f/∂ℓ` is the derivative of `uncurry f` applied to `(1, 0)`.
  have hslice : ∀ x ∈ Icc a b ×ˢ K,
      HasDerivAt (fun ℓ ↦ f ℓ x.2) (fderiv ℝ (Function.uncurry f) x (1, 0)) x.1 :=
    fun x hx ↦ TauCeti.hasDerivAt_slice_left (s := x.1) (b := x.2) (hd x (hKU hx))
  have hcont : ContinuousOn (fun x ↦ fderiv ℝ (Function.uncurry f) x (1, 0)) (Icc a b ×ˢ K) :=
    ((hf.continuousOn_fderiv_of_isOpen hU le_rfl).mono hKU).clm_apply continuousOn_const
  obtain ⟨m, hm, hmle⟩ := (isCompact_Icc.prod hK).exists_forall_le' hcont fun x hx ↦
    (hslice x hx).deriv ▸ hpos x hx
  refine ⟨m, hm, fun r hr ↦ (convex_Icc a b).mul_sub_le_image_sub_of_le_deriv ?_ ?_ ?_⟩
  · exact fun ℓ hℓ ↦ (hslice (ℓ, r) ⟨hℓ, hr⟩).continuousAt.continuousWithinAt
  · exact fun ℓ hℓ ↦
      (hslice (ℓ, r) ⟨interior_subset hℓ, hr⟩).differentiableAt.differentiableWithinAt
  · intro ℓ hℓ
    rw [(hslice (ℓ, r) ⟨interior_subset hℓ, hr⟩).deriv]
    exact hmle (ℓ, r) ⟨interior_subset hℓ, hr⟩

/-- Let `f : ℝ → ℝ → ℝ` be `C²` on an open set `U` containing the compact rectangle `[a, b] × K`.
Then the derivative of `f ℓ` at `r` is Lipschitz in `ℓ ∈ [a, b]`, with a constant `L` that does
not depend on `r ∈ K`. -/
theorem IsCompact.exists_abs_deriv_sub_le_mul (hK : IsCompact K) (hU : IsOpen U)
    (hKU : Icc a b ×ˢ K ⊆ U) (hf : ContDiffOn ℝ 2 (Function.uncurry f) U) :
    ∃ L, ∀ r ∈ K, ∀ ℓ ∈ Icc a b, ∀ ℓ' ∈ Icc a b,
      |deriv (f ℓ') r - deriv (f ℓ) r| ≤ L * |ℓ' - ℓ| := by
  have hf' : ContDiffOn ℝ 1 (fderiv ℝ (Function.uncurry f)) U :=
    hf.fderiv_of_isOpen hU (by norm_num)
  have hd : ∀ x ∈ U, DifferentiableAt ℝ (Function.uncurry f) x := fun x hx ↦
    (hf.differentiableOn two_ne_zero).differentiableAt (hU.mem_nhds hx)
  have hd' : ∀ x ∈ U, DifferentiableAt ℝ (fderiv ℝ (Function.uncurry f)) x := fun x hx ↦
    (hf'.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hx)
  obtain ⟨L, hL⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn
    ((hf'.continuousOn_fderiv_of_isOpen hU le_rfl).mono hKU)
  refine ⟨L, fun r hr ℓ hℓ ℓ' hℓ' ↦ ?_⟩
  -- `∂f/∂r` at `(t, r)` is the derivative of `uncurry f` applied to `(0, 1)`.
  have hderiv : ∀ t ∈ Icc a b, deriv (f t) r = fderiv ℝ (Function.uncurry f) (t, r) (0, 1) :=
    fun t ht ↦ (TauCeti.hasDerivAt_slice_right (hd (t, r) (hKU ⟨ht, hr⟩))).deriv
  rw [hderiv ℓ' hℓ', hderiv ℓ hℓ, ← Real.norm_eq_abs, ← Real.norm_eq_abs]
  refine (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht ↦ (TauCeti.hasDerivAt_fderiv_apply_fst (hd' (t, r) (hKU ⟨ht, hr⟩))
      (0, 1)).hasDerivWithinAt) (fun t ht ↦ ?_) hℓ hℓ'
  refine ((fderiv ℝ (fderiv ℝ (Function.uncurry f)) (t, r)).le_opNorm₂ _ _).trans ?_
  simpa using hL (t, r) ⟨ht, hr⟩

/-- A function continuous on the compact rectangle `[a, b] × K` is uniformly continuous in its
first variable: for every `ε > 0` there is `h > 0` such that moving `ℓ ∈ [a, b]` by at most `h`
changes its value at `(ℓ, r)` by less than `ε`, for every `r ∈ K`. -/
theorem IsCompact.exists_pos_abs_sub_lt_of_continuousOn {g : ℝ × ℝ → ℝ} (hK : IsCompact K)
    (hg : ContinuousOn g (Icc a b ×ˢ K)) {ε : ℝ} (hε : 0 < ε) :
    ∃ h > 0, ∀ r ∈ K, ∀ ℓ ∈ Icc a b, ∀ ℓ' ∈ Icc a b, |ℓ' - ℓ| ≤ h →
      |g (ℓ', r) - g (ℓ, r)| < ε := by
  obtain ⟨d, hd, H⟩ := Metric.uniformContinuousOn_iff.1
    ((isCompact_Icc.prod hK).uniformContinuousOn_of_continuous hg) ε hε
  refine ⟨d / 2, half_pos hd, fun r hr ℓ hℓ ℓ' hℓ' hl ↦ ?_⟩
  have h := H (ℓ', r) ⟨hℓ', hr⟩ (ℓ, r) ⟨hℓ, hr⟩ (by
    rw [Prod.dist_eq, dist_self, Real.dist_eq, max_eq_left (abs_nonneg _)]
    linarith)
  rwa [Real.dist_eq] at h
