/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Topology.MetricSpace.Thickening
import SymplecticGeometry.Analysis.Calculus.IteratedDeriv.Prod

/-!
# Lemmas on iterated derivatives

* Adding or subtracting a constant on the right does not change the iterated derivatives of order
  at least one: `iteratedDeriv_add_const` and `iteratedDeriv_sub_const`, the counterparts of
  Mathlib's `iteratedDeriv_const_add`, from which they follow.
* `exists_forall_mem_of_abs_sub_lt_of_isOpen`: an open condition on the `2`-jet
  `(r, f r, f' r, f'' r)` of a family of real functions, which holds along a compact set of
  parameters and points on which the `2`-jet is continuous, holds with a uniform margin. The
  margin comes from `IsCompact.exists_thickening_subset_open`.
-/

public section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] {n : ℕ} {x : 𝕜} {f : 𝕜 → F}

/-- For `0 < n`, the `n`-th iterated derivative of `z ↦ f z + c` is that of `f`. -/
theorem iteratedDeriv_add_const (hn : 0 < n) (c : F) :
    iteratedDeriv n (fun z ↦ f z + c) x = iteratedDeriv n f x := by
  simpa only [add_comm] using iteratedDeriv_const_add (f := f) (x := x) hn c

/-- For `0 < n`, the `n`-th iterated derivative of `z ↦ f z - c` is that of `f`. -/
theorem iteratedDeriv_sub_const (hn : 0 < n) (c : F) :
    iteratedDeriv n (fun z ↦ f z - c) x = iteratedDeriv n f x := by
  simpa only [sub_eq_add_neg] using iteratedDeriv_add_const (f := f) (x := x) hn (-c)

open Metric in
/-- **Open conditions on the `2`-jet are uniform on a compact set.** Let `K ⊆ ℝ × ℝ` be compact,
with `(ℓ, r) ↦ iteratedDeriv k (χ ℓ) r` continuous on `K` for `k ≤ 2`, and let
`U ⊆ ℝ × ℝ × ℝ × ℝ` be open and contain `(r, χ ℓ r, (χ ℓ)' r, (χ ℓ)'' r)` for every
`(ℓ, r) ∈ K`. Then there is `η > 0` such that `(r, a, b, e) ∈ U` for every `(ℓ, r) ∈ K` and all
`a, b, e` within `η` of `χ ℓ r`, `(χ ℓ)' r` and `(χ ℓ)'' r`. -/
theorem exists_forall_mem_of_abs_sub_lt_of_isOpen {χ : ℝ → ℝ → ℝ} {K : Set (ℝ × ℝ)}
    (hK : IsCompact K)
    (hcont : ∀ k ≤ 2, ContinuousOn (fun x : ℝ × ℝ ↦ iteratedDeriv k (χ x.1) x.2) K)
    {U : Set (ℝ × ℝ × ℝ × ℝ)} (hU : IsOpen U)
    (hKU : ∀ x ∈ K, (x.2, χ x.1 x.2, deriv (χ x.1) x.2, iteratedDeriv 2 (χ x.1) x.2) ∈ U) :
    ∃ η > 0, ∀ x ∈ K, ∀ a b e : ℝ, |a - χ x.1 x.2| < η → |b - deriv (χ x.1) x.2| < η →
      |e - iteratedDeriv 2 (χ x.1) x.2| < η → (x.2, a, b, e) ∈ U := by
  -- The values of `(r, χ ℓ r, (χ ℓ)' r, (χ ℓ)'' r)` on `K` form a compact subset of `U`.
  set g : ℝ × ℝ → ℝ × ℝ × ℝ × ℝ :=
    fun x ↦ (x.2, χ x.1 x.2, deriv (χ x.1) x.2, iteratedDeriv 2 (χ x.1) x.2) with hg_def
  have hg : ContinuousOn g K :=
    continuousOn_snd.prodMk ((ContinuousOn.uncurry_of_iteratedDeriv hcont).prodMk
      ((ContinuousOn.deriv_of_iteratedDeriv hcont one_le_two).prodMk (hcont 2 le_rfl)))
  obtain ⟨η, hη, hsub⟩ := (hK.image_of_continuousOn hg).exists_thickening_subset_open hU
    (by rintro _ ⟨x, hx, rfl⟩; exact hKU x hx)
  refine ⟨η, hη, fun x hx a b e h₀ h₁ h₂ ↦ hsub (mem_thickening_iff.2 ⟨g x, ⟨x, hx, rfl⟩, ?_⟩)⟩
  simp only [hg_def, Prod.dist_eq, Real.dist_eq, sub_self, abs_zero]
  exact max_lt hη (max_lt h₀ (max_lt h₁ h₂))

end
