/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import TauCeti.Geometry.Manifold.RegularValue.Fibre
public import TauCeti.Geometry.Manifold.Sard.EqualDimension

/-!
# Maps with finitely many zeros off a level set

Let `M` be a compact smooth boundaryless manifold modelled on `E`, let `V` be a real vector space
with `dim V = dim E`, and let `g : M → ℝ` be continuous. A continuous map `h₀ : M → V` that does not
vanish on the level set `g⁻¹(0)` can be changed off that level set into a continuous map with
finitely many zeros, none of them on `g⁻¹(0)`
(`SymplecticGeometry.exists_eq_on_levelSet_finite_zeros`).

The proof: by compactness, `‖h₀‖ ≥ c` wherever `|g| < c`, for some `c > 0`. Take a smooth map `h₁`
within `c / 2` of `h₀` (Mathlib's `exists_contMDiffMap_forall_mem_convex_of_local_const`), and a
regular value `w` of `h₁` with `‖w‖ < c / 2` (Sard's theorem, `TauCeti.dense_isRegularValue`),
whose fibre is finite (`TauCeti.IsRegularValue.finite_preimage`). Interpolating between `h₀` on
the level set and `h₁ - w` where `|g| ≥ c`, with weight `min 1 (|g| / c)`, gives a map whose zeros
are zeros of `h₁ - w` in `{|g| ≥ c}`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Theorem 6.10 (Sard's theorem) and Theorem 6.21 (smooth approximation).
-/

public section

open Metric Module Set
open scoped Manifold ContDiff

namespace SymplecticGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [T2Space M] [CompactSpace M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- On a compact smooth boundaryless manifold modelled on `E`, let `g : M → ℝ` be continuous and
`h₀ : M → V` continuous and nonzero on the level set `g⁻¹(0)`, where `dim V = dim E`. Then some
continuous `h : M → V` agrees with `h₀` on `g⁻¹(0)` and has finitely many zeros, none of them on
`g⁻¹(0)`. -/
theorem exists_eq_on_levelSet_finite_zeros (hdim : finrank ℝ E = finrank ℝ V) {g : M → ℝ}
    (hg : Continuous g) (h₀ : C(M, V)) (hh₀ : ∀ x, g x = 0 → h₀ x ≠ 0) :
    ∃ h : C(M, V), (∀ x, g x = 0 → h x = h₀ x) ∧ {x | h x = 0}.Finite ∧
      ∀ x, h x = 0 → g x ≠ 0 := by
  -- A margin `c > 0` such that `‖h₀‖ ≥ c` wherever `|g| < c`.
  obtain ⟨c, hc, hcg⟩ : ∃ c > 0, ∀ x, |g x| < c → c ≤ ‖h₀ x‖ := by
    obtain ⟨c, hc, hmin⟩ := isCompact_univ.exists_forall_le' (a := 0)
      ((continuous_norm.comp h₀.continuous).max hg.abs).continuousOn fun x _ ↦
        lt_max_iff.2 ((eq_or_ne (g x) 0).imp (fun h ↦ norm_pos_iff.2 (hh₀ x h)) abs_pos.2)
    exact ⟨c, hc, fun x hx ↦ (le_max_iff.1 (hmin x (mem_univ x))).resolve_right hx.not_ge⟩
  -- A smooth approximation `h₁` within `c / 2` of `h₀`.
  obtain ⟨h₁, hh₁⟩ := exists_contMDiffMap_forall_mem_convex_of_local_const 𝓘(ℝ, E) (n := ⊤)
    (t := fun x ↦ ball (h₀ x) (c / 2)) (fun x ↦ convex_ball _ _) fun x ↦
      ⟨h₀ x, (h₀.continuous.tendsto x).eventually (ball_mem_nhds (h₀ x) (half_pos hc)) |>.mono
        fun y hy ↦ mem_ball_comm.1 hy⟩
  -- A regular value `w` of `h₁` of norm less than `c / 2`, by Sard's theorem.
  obtain ⟨w, hwreg, hw⟩ := (TauCeti.dense_isRegularValue (I := 𝓘(ℝ, E)) (J := 𝓘(ℝ, V)) hdim
    (h₁.contMDiff.mdifferentiable (by simp))).exists_mem_open isOpen_ball
    ⟨0, mem_ball_self (half_pos hc)⟩
  have hfin : (h₁ ⁻¹' {w}).Finite :=
    TauCeti.IsRegularValue.finite_preimage (hy := hwreg) hdim h₁.contMDiff.continuous
  -- Interpolate between `h₀` near the level set and `h₁ - w` away from it.
  let lam : M → ℝ := fun x ↦ max 0 (min 1 (|g x| / c))
  have hlam : Continuous lam :=
    continuous_const.max (continuous_const.min (hg.abs.div_const c))
  refine ⟨⟨fun x ↦ h₀ x + lam x • ((h₁ x - w) - h₀ x), h₀.continuous.add
    (hlam.smul ((h₁.contMDiff.continuous.sub continuous_const).sub h₀.continuous))⟩,
    fun x hx ↦ ?_, ?_⟩
  · simp [lam, hx]
  -- A zero lies where `|g| ≥ c`, and is a zero of `h₁ - w` there.
  have key : ∀ x, h₀ x + lam x • ((h₁ x - w) - h₀ x) = 0 → c ≤ |g x| ∧ h₁ x = w := by
    intro x h0
    by_cases hxc : c ≤ |g x|
    · have hl : lam x = 1 := by
        have : 1 ≤ |g x| / c := by rwa [le_div_iff₀ hc, one_mul]
        simp [lam, min_eq_left this]
      rw [hl, one_smul, add_sub_cancel, sub_eq_zero] at h0
      exact ⟨hxc, h0⟩
    · exfalso
      have habs : |g x| < c := not_le.1 hxc
      have hl0 : 0 ≤ lam x := le_max_left _ _
      have hl1 : lam x ≤ 1 := max_le zero_le_one (min_le_left _ _)
      have hd : ‖(h₁ x - w) - h₀ x‖ < c := by
        have h1 : ‖h₁ x - h₀ x‖ < c / 2 := by simpa [dist_eq_norm] using hh₁ x
        have h2 : ‖w‖ < c / 2 := by simpa using hw
        calc ‖(h₁ x - w) - h₀ x‖ = ‖(h₁ x - h₀ x) - w‖ := by abel_nf
          _ ≤ ‖h₁ x - h₀ x‖ + ‖w‖ := norm_sub_le _ _
          _ < c := by linarith
      have : ‖h₀ x‖ < c := by
        have := congrArg norm (eq_neg_of_add_eq_zero_left h0)
        rw [norm_neg, norm_smul, Real.norm_of_nonneg hl0] at this
        rw [this]
        calc lam x * ‖(h₁ x - w) - h₀ x‖ ≤ 1 * ‖(h₁ x - w) - h₀ x‖ :=
              mul_le_mul_of_nonneg_right hl1 (norm_nonneg _)
          _ < c := by linarith
      exact absurd (hcg x habs) (not_le.2 this)
  refine ⟨hfin.subset fun x hx ↦ (key x hx).2, fun x h0 hx ↦ ?_⟩
  have := (key x h0).1
  rw [hx, abs_zero] at this
  linarith

end SymplecticGeometry

end
