/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Diffeomorphism.Diffeotopy.Translate
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import SymplecticGeometry.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Holonomic approximation in coordinates: conventions, wiggling and the zig-zag profile

This file starts the coordinate treatment of holonomic approximation, following
[EliashbergMishachev2002], Chapter 3. The model is
`D := (Fin m → ℝ) × (Fin k → ℝ)`, with the core directions first and the transverse directions
second, and with sup norms, so that the cube `Iᵐ` is `Metric.closedBall (0 : Fin m → ℝ) 1` and
no cube needs a definition.

A formal section (a first jet over `D` with values in a normed space `F`) is a pair of maps
`f : D → F` and `G : D → D →L[ℝ] F`. It is holonomic on `s` when `∀ x ∈ s, fderiv ℝ f x = G x`.
Neither notion gets a definition: statements carry the two maps and this equation.

The file proves the one-dimensional *wiggling* lemma, the zig-zag diffeotopy that both
[EliashbergMishachev2002], §3.2, and the handle-core argument of [McDuffSalamon2017], Lemma 7.3.2,
use: a compactly supported diffeotopy that moves points by less than a given `δ`, stays in the
`δ`-neighbourhood of a compact set `K`, and on `K` itself pushes each point in a transverse
direction by `r sin (N u)`, where `u` is a core coordinate. As `N` grows the image of a segment
along that core coordinate oscillates more and more often between the heights `± r`, so its
length in the transverse direction is as large as wanted.

It also proves the existence of a *zig-zag profile* on the segment `[-1, 1]`: a smooth function
`g` with `|g| ≤ 1`, vanishing near `± 1`, that changes sign near finitely many points
`c 0 < ⋯ < c n`, as close together as wanted, with `|g| ≥ 1/2` and alternating signs on small
windows on either side of each `c i`. The curve `u ↦ (u, r g(u) eⱼ)` is the zig-zag along which
[EliashbergMishachev2002], §3.2, chains Taylor sections, one between consecutive crossings.

## Main results

* `SymplecticGeometry.exists_wiggling_diffeotopy`: the zig-zag on `D`. It is the case
  `g = sin (N uᵢ)`, `e = (0, r eⱼ)` of `SymplecticGeometry.exists_diffeotopy_apply_eq_add_smul`.
* `SymplecticGeometry.exists_zigzag_profile`: for `0 < b < 1` and a mesh `ρ > 0`, a profile `g`
  vanishing where `1 - b ≤ |t|`, with points `c i` less than `ρ` apart, the first at most
  `-1 + 2 b` and the last at least `1 - 2 b`, and a width `w` with `[c 0 - 2 w, c n + 2 w]`
  inside `(-1 + b, 1 - b)`, such that `|g| ≥ 1/2` with sign
  `± (-1) ^ i` at distance between `w` and `2 w` from `c i`.

## References

* [Y. Eliashberg and N. Mishachev, *Introduction to the h-Principle*][EliashbergMishachev2002]
* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017]
-/

public section

open Set Metric
open scoped Manifold ContDiff Real

namespace SymplecticGeometry

/-- **The wiggling lemma.** On `D = (Fin m → ℝ) × (Fin k → ℝ)` with sup norms, let `K` be compact,
`i` a core direction, `j` a transverse direction, `0 ≤ r < δ` and `N : ℝ`. There is a smooth
diffeotopy `h` of `D` that is the identity off a compact subset of the `δ`-neighbourhood of `K`,
moves every point by less than `δ`, and sends each `(u, v) ∈ K` at time `t` to
`(u, v + t r sin (N uᵢ) eⱼ)`. Taking `N` large makes the image of a segment along the `i`-th core
direction zig-zag between the transverse heights `± r` as often as wanted. -/
theorem exists_wiggling_diffeotopy {m k : ℕ} {K : Set ((Fin m → ℝ) × (Fin k → ℝ))}
    (hK : IsCompact K) (i : Fin m) (j : Fin k) {r δ : ℝ} (hr : 0 ≤ r) (hrδ : r < δ) (N : ℝ) :
    ∃ h : TauCeti.Diffeotopy 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ)) ∞ ((Fin m → ℝ) × (Fin k → ℝ)),
      (∃ C, IsCompact C ∧ C ⊆ thickening δ K ∧ ∀ t, ∀ x ∉ C, h (t, x) = x) ∧
      (∀ t x, dist (h (t, x)) x < δ) ∧
      ∀ t, ∀ x ∈ K, h (t, x) = (x.1, x.2 + Pi.single j ((t : ℝ) * r * Real.sin (N * x.1 i))) := by
  set e : (Fin m → ℝ) × (Fin k → ℝ) := (0, Pi.single j r)
  have hne : ‖e‖ = r := by
    have h2 : ‖e‖ = ‖(Pi.single j r : Fin k → ℝ)‖ := by simp [e]
    rw [h2, ← coe_nnNorm, Pi.nnNorm_single, coe_nnNorm, Real.norm_of_nonneg hr]
  have hg : ContDiff ℝ ∞ fun x : (Fin m → ℝ) × (Fin k → ℝ) ↦ Real.sin (N * x.1 i) :=
    by fun_prop
  obtain ⟨h, hsupp, hsmall, hK'⟩ := exists_diffeotopy_apply_eq_add_smul hK hg
    (fun x ↦ Real.abs_sin_le_one _) (e := e) (fun x _ s ↦ by simp [e]) (hne ▸ hrδ)
  refine ⟨h, hsupp, fun t x ↦ ?_, fun t x hx ↦ ?_⟩
  · rw [dist_eq_norm]
    calc ‖h (t, x) - x‖ ≤ (t : ℝ) * ‖e‖ := hsmall t x
      _ ≤ 1 * r := by rw [hne]; gcongr; exact t.property.2
      _ < δ := by linarith
  · rw [hK' t x hx]
    ext l
    · simp [e]
    · simp only [e, Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rcases eq_or_ne l j with rfl | hl
      · simp; ring
      · simp [hl]

/-- **A zig-zag profile on the segment.** Let `0 < b < 1` and `ρ > 0`. There is a smooth
`g : ℝ → ℝ` with `|g| ≤ 1`, vanishing where `1 - b ≤ |t|`, together with points
`c 0 < c 1 < ⋯ < c n` and a width `w > 0` such that:
* the windows `[c 0 - 2 w, c n + 2 w]` lie in the open interval `(-1 + b, 1 - b)`, the first
  point is at most `-1 + 2 b` and the last at least `1 - 2 b`;
* consecutive points are less than `ρ` apart and at least `4 w` apart;
* for `w ≤ |t - c i| ≤ 2 w`, the value `g t` has the sign `(-1) ^ i` to the right of `c i` and
  the opposite sign to its left, and `|g t| ≥ 1/2`.

So `g` changes sign, alternately upwards and downwards, near each `c i`, and stays away from
zero at distance between `w` and `2 w` from each `c i`. -/
theorem exists_zigzag_profile {b ρ : ℝ} (hb : 0 < b) (hb₁ : b < 1) (hρ : 0 < ρ) :
    ∃ (g : ℝ → ℝ) (n : ℕ) (c : Fin (n + 1) → ℝ) (w : ℝ),
      ContDiff ℝ ∞ g ∧ (∀ t, |g t| ≤ 1) ∧ (∀ t, 1 - b ≤ |t| → g t = 0) ∧
      0 < w ∧ StrictMono c ∧
      -1 + b < c 0 - 2 * w ∧ c 0 ≤ -1 + 2 * b ∧
      1 - 2 * b ≤ c (Fin.last n) ∧ c (Fin.last n) + 2 * w < 1 - b ∧
      (∀ i : Fin n, c i.succ - c i.castSucc < ρ ∧ c i.castSucc + 4 * w ≤ c i.succ) ∧
      ∀ i : Fin (n + 1), ∀ t, w ≤ |t - c i| → |t - c i| ≤ 2 * w →
        1 / 2 ≤ (-1) ^ (i : ℕ) * SignType.sign (t - c i) * g t := by
  -- The crossings fill `[-s, s]`, where `1 - 2 b ≤ s < 1 - b`, with a margin `m` up to `1 - b`.
  set s := (1 - b) * (2 - b) / 2 with hs_def
  set m := b * (1 - b) / 2 with hm_def
  have hs : 0 < s := by nlinarith
  have hm : 0 < m := by nlinarith
  have : s + m = 1 - b := by rw [hs_def, hm_def]; ring
  have hsb : 1 - 2 * b ≤ s := by nlinarith
  have hmin : 0 < min ρ (3 * m) := lt_min hρ (by positivity)
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * s / min ρ (3 * m))
  have hn0 : (0 : ℝ) < n := lt_trans (by positivity) hn
  set d := 2 * s / n with hd_def
  have hd : 0 < d := by positivity
  have hdmin : d < min ρ (3 * m) := (div_lt_comm₀ hmin hn0).1 hn
  obtain ⟨hdρ, hdm⟩ := lt_min_iff.1 hdmin
  have hnd : (n : ℝ) * d = 2 * s := by rw [hd_def]; field_simp
  let θ : ContDiffBump (0 : ℝ) := ⟨s + d / 3, 1 - b, by positivity, by linarith⟩
  refine ⟨fun t ↦ θ t * Real.sin (π * (t + s) / d), n, fun i ↦ -s + (i : ℕ) * d, d / 6,
    θ.contDiff.mul (by fun_prop), fun t ↦ ?_, fun t ht ↦ ?_, by positivity, fun i j hij ↦ ?_,
    by simp; linarith, by simp; linarith, by simp [hnd]; linarith, by simp [hnd]; linarith,
    fun i ↦ ?_, fun i t h₁ h₂ ↦ ?_⟩
  · simpa [abs_mul, abs_of_nonneg θ.nonneg] using
      mul_le_mul θ.le_one (Real.abs_sin_le_one (π * (t + s) / d)) (abs_nonneg _) zero_le_one
  · dsimp only
    rw [θ.zero_of_le_dist (by rw [Real.dist_eq, sub_zero]; exact ht), zero_mul]
  · dsimp only; gcongr; exact_mod_cast hij
  · simp only [Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one, add_mul,
      one_mul]
    constructor <;> linarith
  · -- Write `t = c i + u`, with `d / 6 ≤ |u| ≤ d / 3`.
    dsimp only at h₁ h₂ ⊢
    set u := t - (-s + (i : ℕ) * d) with hu
    have hid : ((i : ℕ) : ℝ) * d ≤ n * d := by gcongr; exact_mod_cast Nat.le_of_lt_succ i.isLt
    have hθ : θ t = 1 := by
      refine θ.one_of_mem_closedBall ?_
      rw [mem_closedBall, Real.dist_eq, sub_zero, abs_le]
      -- `θ.rIn` is the field `s + d / 3` of the structure `θ` built above.
      change -(s + d / 3) ≤ t ∧ t ≤ s + d / 3
      rw [abs_le] at h₂
      constructor <;> linarith [h₂.1, h₂.2, (by positivity : (0 : ℝ) ≤ (i : ℕ) * d)]
    have harg : π * (t + s) / d = π * u / d + (i : ℕ) * π := by
      rw [hu]; field_simp; ring
    have hsign : SignType.sign (π * u / d) = SignType.sign u := by
      rw [mul_div_right_comm, sign_mul, _root_.sign_pos (div_pos Real.pi_pos hd), one_mul]
    have habs : |π * u / d| = π * |u| / d := by
      rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hd]
    rw [hθ, one_mul, harg, ← hsign]
    apply Real.one_half_le_neg_one_pow_mul_sign_mul_sin_add_nat_mul_pi <;> rw [habs]
    · rw [le_div_iff₀ hd]; nlinarith [Real.pi_pos]
    · rw [div_le_iff₀ hd]; nlinarith [Real.pi_pos]

end SymplecticGeometry

end
