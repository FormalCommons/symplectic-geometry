/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.Compact
import SymplecticGeometry.Topology.UniformSpace.HeineCantor
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
* `IsCompact.exists_pos_abs_iteratedDeriv_sub_lt_of_continuousOn`: if the derivatives in `r` of
  order at most `n` of `f` are continuous on the rectangle, then they are uniformly continuous
  in `ℓ`, uniformly in `r ∈ K`, with one step in `ℓ` for all of them. It applies
  `IsCompact.exists_pos_abs_sub_lt_of_continuousOn`
  (`SymplecticGeometry/Topology/UniformSpace/HeineCantor.lean`) to each of them.

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

/-- Let `f : ℝ → ℝ → ℝ` be a family whose derivatives `∂ᵏf/∂rᵏ` of order `k ≤ n` are continuous
on the compact rectangle `[a, b] × K`. Then they are uniformly continuous in `ℓ`, with one step
for all of them: for every `ε > 0` there is `w > 0` such that moving `ℓ ∈ [a, b]` by at most `w`
changes each of them at `(ℓ, r)` by less than `ε`, for every `r ∈ K`. -/
theorem IsCompact.exists_pos_abs_iteratedDeriv_sub_lt_of_continuousOn {n : ℕ} (hK : IsCompact K)
    (hf : ∀ k ≤ n, ContinuousOn (fun x : ℝ × ℝ ↦ iteratedDeriv k (f x.1) x.2) (Icc a b ×ˢ K))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ w > 0, ∀ k ≤ n, ∀ r ∈ K, ∀ ℓ ∈ Icc a b, ∀ ℓ' ∈ Icc a b, |ℓ' - ℓ| ≤ w →
      |iteratedDeriv k (f ℓ') r - iteratedDeriv k (f ℓ) r| < ε := by
  choose! w hw hu using fun k (hk : k ≤ n) ↦ hK.exists_pos_abs_sub_lt_of_continuousOn (hf k hk) hε
  have hmem : ∀ {k}, k ≤ n → k ∈ Finset.range (n + 1) := fun hk ↦
    Finset.mem_range.2 (Nat.lt_succ_of_le hk)
  refine ⟨(Finset.range (n + 1)).inf' ⟨0, hmem n.zero_le⟩ w,
    (Finset.lt_inf'_iff _).2 fun k hk ↦ hw k (Nat.le_of_lt_succ (Finset.mem_range.1 hk)),
    fun k hk r hr ℓ hℓ ℓ' hℓ' hl ↦ hu k hk r hr ℓ hℓ ℓ' hℓ' (hl.trans (Finset.inf'_le _ (hmem hk)))⟩
