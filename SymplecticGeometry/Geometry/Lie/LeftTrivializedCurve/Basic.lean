/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Lie.LeftTrivializedDeriv
import SymplecticGeometry.Geometry.Lie.LeftTrivializedCurve.LocalExistence

/-!
# Global curves with a prescribed left-trivialized derivative

Let `G` be a real Lie group of class `C²` modelled on a complete space with a boundaryless model,
and let `ξ : ℝ → 𝔤` be a continuous curve in its Lie algebra `𝔤 = GroupLieAlgebra I G`. For
every `g₀ : G` there is exactly one curve `g : ℝ → G` with `g 0 = g₀` and left-trivialized
derivative `ξ` at every time, `g⁻¹ g' = ξ` in matrix notation. This file proves this and defines
that curve, `leftTrivializedCurve ξ g₀`.

## Main definitions

* `SymplecticGeometry.leftTrivializedCurve ξ g₀`: the curve through `g₀` at time `0` with
  left-trivialized derivative `ξ`.

## Main results

* `SymplecticGeometry.existsUnique_hasLeftTrivializedDerivOn_univ`: existence and uniqueness of
  the curve.
* `SymplecticGeometry.leftTrivializedCurve_zero`,
  `SymplecticGeometry.hasLeftTrivializedDerivOn_leftTrivializedCurve`: its value at `0` and its
  derivative.
* `SymplecticGeometry.eq_leftTrivializedCurve`: every curve with these two properties is it.
* `SymplecticGeometry.leftTrivializedCurve_mul`: the curve from `a * g₀` is the left translate by
  `a` of the curve from `g₀`.

## Implementation notes

The local existence theorem
`exists_pos_forall_mem_Icc_exists_hasMFDerivAt_mfderiv_inv_mul_eq` gives, for a compact interval
`[-T, T]`, a time `ε > 0` such that solutions through `1` starting at any time of `[-T, T]` exist
for a time `ε`. Starting from such a solution at time `0`, translated to start at `g₀`, a solution
on `(-r, r)` is extended to one on `(-r - ε/2, r + ε/2)` by gluing to it, at times `±(r - ε/2)`,
the local solutions starting there, translated on the left to agree with it
(`HasLeftTrivializedDerivOn.const_mul` and `HasLeftTrivializedDerivOn.piecewise`). Finitely many
steps reach `(-T, T)`. The solutions on `(-T, T)` agree on their common times by uniqueness, and
`t ↦ g_{|t| + 1} t` is the global solution. This adapts the proofs of Mathlib's
`exists_isMIntegralCurve_of_isMIntegralCurveOn` and
`exists_isMIntegralCurve_iff_exists_isMIntegralCurveOn_Ioo`, from an autonomous vector field with
a uniform time of existence on all of the manifold to a time-dependent one with a uniform time on
each compact interval of times.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Lemma 9.15.
-/

public section

noncomputable section

open Set
open scoped ContDiff

namespace SymplecticGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  {ξ : ℝ → GroupLieAlgebra I G}

/-- On `(-T, T)` there is a curve through `g₀` at time `0` with left-trivialized derivative
`ξ`. -/
private theorem exists_hasLeftTrivializedDerivOn_Ioo [CompleteSpace E] [I.Boundaryless]
    {n : ℕ∞ω} [LieGroup I n G] (hn : 2 ≤ n) (hξ : Continuous ξ) (g₀ : G) (T : ℝ) :
    ∃ g : ℝ → G, g 0 = g₀ ∧ HasLeftTrivializedDerivOn g ξ (Ioo (-T) T) := by
  have : LieGroup I 1 G := LieGroup.of_le (le_trans (by norm_num) hn)
  rcases lt_or_ge T 0 with hT | hT
  · exact ⟨fun _ ↦ g₀, rfl, by simp [Ioo_eq_empty (by linarith : ¬-T < T),
      hasLeftTrivializedDerivOn_def]⟩
  obtain ⟨ε, hε, hloc⟩ :=
    exists_pos_forall_mem_Icc_exists_hasMFDerivAt_mfderiv_inv_mul_eq hn hξ (-T) T
  -- a curve on an open interval `(a, b)` extends, through a time `t₀ ∈ [-T, T] ∩ (a, b)`, to
  -- `(a, b) ∪ (t₀ - ε, t₀ + ε)`
  have hext (a b : ℝ) (g : ℝ → G) (hg : HasLeftTrivializedDerivOn g ξ (Ioo a b)) (t₀ : ℝ)
      (ht₀ : t₀ ∈ Icc (-T) T) (ht₀' : t₀ ∈ Ioo a b) : ∃ g' : ℝ → G, EqOn g' g (Ioo a b) ∧
        HasLeftTrivializedDerivOn g' ξ (Ioo a b ∪ Ioo (t₀ - ε) (t₀ + ε)) := by
    classical
    obtain ⟨γ, hγ₀, hγ⟩ := hloc t₀ ht₀
    have hγ' := ((hasLeftTrivializedDerivOn_iff_of_isOpen isOpen_Ioo).2 hγ).const_mul (g t₀)
    refine ⟨(Ioo a b).piecewise g fun t ↦ g t₀ * γ t, piecewise_eqOn _ _ _,
      hg.piecewise hγ' isOpen_Ioo isOpen_Ioo ?_ ⟨ht₀', by simp [hε]⟩ (by simp [hγ₀])⟩
    rw [Ioo_inter_Ioo]
    exact isPreconnected_Ioo
  obtain ⟨δ, hδ, hεδ⟩ : ∃ δ : ℝ, 0 < δ ∧ ε = 2 * δ := ⟨ε / 2, half_pos hε, by ring⟩
  have hstep (k : ℕ) : (k : ℝ) * δ ≤ T → ∃ g : ℝ → G, g 0 = g₀ ∧
      HasLeftTrivializedDerivOn g ξ (Ioo (-((k + 1) * δ)) ((k + 1) * δ)) := by
    induction k with
    | zero =>
      intro _
      obtain ⟨γ, hγ₀, hγ⟩ := hloc 0 ⟨by linarith, hT⟩
      refine ⟨fun t ↦ g₀ * γ t, by simp [hγ₀], ?_⟩
      refine (((hasLeftTrivializedDerivOn_iff_of_isOpen isOpen_Ioo).2 hγ).const_mul g₀).mono ?_
      exact Ioo_subset_Ioo (by simp; linarith) (by simp; linarith)
    | succ k ih =>
      intro hk
      have hk0 : (0 : ℝ) ≤ k * δ := by positivity
      have hr : ((k + 1 : ℕ) : ℝ) * δ = k * δ + δ := by push_cast; ring
      rw [hr] at hk
      obtain ⟨g, hg₀, hg⟩ := ih (by linarith)
      have hr' : ((k : ℝ) + 1) * δ = k * δ + δ := by ring
      rw [hr'] at hg
      -- extend forwards through `k * δ`, then backwards through `-(k * δ)`
      obtain ⟨g₁, hg₁, hg₁'⟩ := hext _ _ g hg (k * δ) ⟨by linarith, by linarith⟩
        ⟨by linarith, by linarith⟩
      have hg₁'' : HasLeftTrivializedDerivOn g₁ ξ (Ioo (-(k * δ + δ)) (k * δ + 2 * δ)) := by
        refine hg₁'.mono fun t ht ↦ ?_
        rcases lt_or_ge t (k * δ + δ) with h | h
        · exact Or.inl ⟨ht.1, h⟩
        · exact Or.inr ⟨by linarith, by linarith [ht.2]⟩
      obtain ⟨g₂, hg₂, hg₂'⟩ := hext _ _ g₁ hg₁'' (-(k * δ)) ⟨by linarith, by linarith⟩
        ⟨by linarith, by linarith⟩
      refine ⟨g₂, ?_, hg₂'.mono ?_⟩
      · rw [hg₂ ⟨by linarith, by linarith⟩, hg₁ ⟨by linarith, by linarith⟩, hg₀]
      · rw [show (((k + 1 : ℕ) : ℝ) + 1) * δ = k * δ + 2 * δ by push_cast; ring]
        intro t ht
        rcases le_or_gt t (-(k * δ + δ)) with h | h
        · exact Or.inr ⟨by linarith [ht.1], by linarith⟩
        · exact Or.inl ⟨h, ht.2⟩
  obtain ⟨g, hg₀, hg⟩ := hstep ⌊T / δ⌋₊ ((le_div_iff₀ hδ).1 (Nat.floor_le (by positivity)))
  have hTk : T < (⌊T / δ⌋₊ + 1) * δ := (div_lt_iff₀ hδ).1 (Nat.lt_floor_add_one _)
  exact ⟨g, hg₀, hg.mono (Ioo_subset_Ioo (by linarith) hTk.le)⟩

/-- **Existence.** For a continuous curve `ξ` in the Lie algebra of a Lie group of class `C²`
modelled on a complete space with a boundaryless model, and `g₀ : G`, some curve `g : ℝ → G`
with `g 0 = g₀` has left-trivialized derivative `ξ` at every time. -/
theorem exists_hasLeftTrivializedDerivOn_univ [CompleteSpace E] [I.Boundaryless] {n : ℕ∞ω}
    [LieGroup I n G] (hn : 2 ≤ n) (hξ : Continuous ξ) (g₀ : G) :
    ∃ g : ℝ → G, g 0 = g₀ ∧ HasLeftTrivializedDerivOn g ξ univ := by
  have : LieGroup I 1 G := LieGroup.of_le (le_trans (by norm_num) hn)
  choose γ hγ₀ hγ using exists_hasLeftTrivializedDerivOn_Ioo hn hξ g₀
  -- the curve `t ↦ γ (|t| + 1) t` agrees with each `γ a` on `(-a, a)`
  have heq (a : ℝ) : EqOn (fun t ↦ γ (|t| + 1) t) (γ a) (Ioo (-a) a) := by
    intro t ht
    have hm : t ∈ Ioo (-min (|t| + 1) a) (min (|t| + 1) a) := by
      rw [mem_Ioo, ← abs_lt, lt_min_iff]
      exact ⟨lt_add_one _, abs_lt.mpr ht⟩
    have h0 : (0 : ℝ) ∈ Ioo (-min (|t| + 1) a) (min (|t| + 1) a) := by
      rw [mem_Ioo, ← abs_lt, abs_zero]
      exact (abs_nonneg t).trans_lt (abs_lt.mpr hm)
    exact ((hγ _).mono (Ioo_subset_Ioo (by simp) (min_le_left _ _))).eqOn
      ((hγ a).mono (Ioo_subset_Ioo (by simp) (min_le_right _ _))) isPreconnected_Ioo h0
      (by rw [hγ₀, hγ₀]) hm
  refine ⟨fun t ↦ γ (|t| + 1) t, hγ₀ _, hasLeftTrivializedDerivOn_univ_iff.2 fun t ↦ ?_⟩
  have ht : t ∈ Ioo (-(|t| + 1)) (|t| + 1) := by
    rw [mem_Ioo, ← abs_lt]
    exact lt_add_one _
  exact (hasLeftTrivializedDerivOn_iff_of_isOpen isOpen_Ioo).1 ((hγ _).congr (heq _)) t ht

/-- **Existence and uniqueness.** For a continuous curve `ξ` in the Lie algebra of a Lie group of
class `C²` modelled on a complete space with a boundaryless model, and `g₀ : G`, exactly one curve
`g : ℝ → G` with `g 0 = g₀` has left-trivialized derivative `ξ` at every time. -/
theorem existsUnique_hasLeftTrivializedDerivOn_univ [CompleteSpace E] [I.Boundaryless]
    {n : ℕ∞ω} [LieGroup I n G] (hn : 2 ≤ n) (hξ : Continuous ξ) (g₀ : G) :
    ∃! g : ℝ → G, g 0 = g₀ ∧ HasLeftTrivializedDerivOn g ξ univ := by
  have : LieGroup I 1 G := LieGroup.of_le (le_trans (by norm_num) hn)
  obtain ⟨g, hg₀, hg⟩ := exists_hasLeftTrivializedDerivOn_univ hn hξ g₀
  refine ⟨g, ⟨hg₀, hg⟩, fun h ⟨hh₀, hh⟩ ↦ funext fun t ↦ ?_⟩
  exact hh.eqOn hg isPreconnected_univ (mem_univ 0) (hh₀.trans hg₀.symm) (mem_univ t)

/-- The curve `g : ℝ → G` with `g 0 = g₀` and left-trivialized derivative `ξ` at every time,
`g⁻¹ g' = ξ`. It exists, and is unique, when `G` is a Lie group of class `C²` modelled on a
complete space with a boundaryless model and `ξ` is continuous
(`existsUnique_hasLeftTrivializedDerivOn_univ`); otherwise it is an arbitrary curve. -/
def leftTrivializedCurve (ξ : ℝ → GroupLieAlgebra I G) (g₀ : G) : ℝ → G :=
  Classical.epsilon fun g : ℝ → G ↦ g 0 = g₀ ∧ HasLeftTrivializedDerivOn g ξ univ

/-- The definition of `leftTrivializedCurve`. -/
theorem leftTrivializedCurve_def (g₀ : G) : leftTrivializedCurve ξ g₀ =
    Classical.epsilon fun g : ℝ → G ↦ g 0 = g₀ ∧ HasLeftTrivializedDerivOn g ξ univ :=
  (rfl)

variable [CompleteSpace E] [I.Boundaryless] {n : ℕ∞ω} [LieGroup I n G]

/-- `leftTrivializedCurve ξ g₀` takes the value `g₀` at `0` and has left-trivialized derivative
`ξ` at every time. -/
theorem leftTrivializedCurve_spec (hn : 2 ≤ n) (hξ : Continuous ξ) (g₀ : G) :
    leftTrivializedCurve ξ g₀ 0 = g₀ ∧
      HasLeftTrivializedDerivOn (leftTrivializedCurve ξ g₀) ξ univ :=
  Classical.epsilon_spec (exists_hasLeftTrivializedDerivOn_univ hn hξ g₀)

/-- `leftTrivializedCurve ξ g₀` takes the value `g₀` at time `0`. -/
theorem leftTrivializedCurve_zero (hn : 2 ≤ n) (hξ : Continuous ξ) (g₀ : G) :
    leftTrivializedCurve ξ g₀ 0 = g₀ :=
  (leftTrivializedCurve_spec hn hξ g₀).1

/-- `leftTrivializedCurve ξ g₀` has left-trivialized derivative `ξ` at every time. -/
theorem hasLeftTrivializedDerivOn_leftTrivializedCurve (hn : 2 ≤ n) (hξ : Continuous ξ)
    (g₀ : G) : HasLeftTrivializedDerivOn (leftTrivializedCurve ξ g₀) ξ univ :=
  (leftTrivializedCurve_spec hn hξ g₀).2

/-- **Uniqueness.** A curve with value `g₀` at time `0` and left-trivialized derivative `ξ` at
every time is `leftTrivializedCurve ξ g₀`. -/
theorem eq_leftTrivializedCurve (hn : 2 ≤ n) (hξ : Continuous ξ) {g : ℝ → G} {g₀ : G}
    (hg₀ : g 0 = g₀) (hg : HasLeftTrivializedDerivOn g ξ univ) :
    g = leftTrivializedCurve ξ g₀ :=
  (existsUnique_hasLeftTrivializedDerivOn_univ hn hξ g₀).unique ⟨hg₀, hg⟩
    (leftTrivializedCurve_spec hn hξ g₀)

/-- **Left translation.** The curve from `a * g₀` is the left translate by `a` of the curve from
`g₀`. -/
theorem leftTrivializedCurve_mul (hn : 2 ≤ n) (hξ : Continuous ξ) (a g₀ : G) :
    leftTrivializedCurve ξ (a * g₀) = fun t ↦ a * leftTrivializedCurve ξ g₀ t := by
  have : LieGroup I 1 G := LieGroup.of_le (le_trans (by norm_num) hn)
  exact (eq_leftTrivializedCurve hn hξ (by rw [leftTrivializedCurve_zero hn hξ])
    ((hasLeftTrivializedDerivOn_leftTrivializedCurve hn hξ g₀).const_mul a)).symm

/-- The curve from `g₀` is the left translate by `g₀` of the curve from `1`. -/
theorem leftTrivializedCurve_apply_eq_mul (hn : 2 ≤ n) (hξ : Continuous ξ) (g₀ : G) (t : ℝ) :
    leftTrivializedCurve ξ g₀ t = g₀ * leftTrivializedCurve ξ 1 t := by
  rw [← congrFun (leftTrivializedCurve_mul hn hξ g₀ 1) t, mul_one]

end SymplecticGeometry

end
