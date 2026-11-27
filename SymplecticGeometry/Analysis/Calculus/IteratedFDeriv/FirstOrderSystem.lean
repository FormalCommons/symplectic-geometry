/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic

/-!
# Derivative bounds for solutions of first-order systems

Let `h : E → F` satisfy the first-order system `fderiv 𝕜 h w = Φ (w, h w)` near a point `w₀`,
where `Φ : E × F → (E →L[𝕜] F)` is `C^r` at `(w₀, h w₀)`. Differentiating the system expresses
each derivative of `h` of order `j ≥ 1` at `w₀` through the derivatives of `Φ` of order `< j`
at `(w₀, h w₀)` and the derivatives of `h` of lower order. This file turns that into an explicit
pointwise bound: if the derivatives of `Φ` of order `< j` at `(w₀, h w₀)` have norm at most `A`,
then `‖iteratedFDeriv 𝕜 j h w₀‖ ≤ firstOrderSystemConst j * (1 + A) ^ j`, with a natural number
`firstOrderSystemConst j` that depends only on `j`. The bound is uniform in `h`, `Φ`, `w₀` and
the spaces, so it applies to families of solutions.

## Main definitions

* `SymplecticGeometry.firstOrderSystemConst`: the constants of the bound, defined by the
  recursion `K 0 = 1`, `K (n + 1) = n ! * (1 + K n) ^ n`.

## Main results

* `SymplecticGeometry.firstOrderSystemConst_mono`: the constants are nondecreasing.
* `SymplecticGeometry.norm_iteratedFDeriv_le_of_eventually_fderiv_eq`: the bound above, for
  `1 ≤ j ≤ r + 1`.

## Implementation notes

The proof is an induction on `j`. Since `‖iteratedFDeriv 𝕜 (n + 1) h w₀‖` is the norm of the
`n`-th derivative of `fderiv 𝕜 h`, which near `w₀` is `Φ ∘ (fun w ↦ (w, h w))`, Tau Ceti's
pointwise Faà di Bruno bound `TauCeti.norm_iteratedFDeriv_comp_le_of_contDiffAt` applies, with the
derivatives of `fun w ↦ (w, h w)` bounded by the induction hypothesis. Tau Ceti's
`HasUniformJetBoundsOn.succ_of_fderiv` (in `TauCeti/Analysis/Calculus/UniformJets.lean`) runs the
same bootstrap for families on sets, with constants that are not explicit.
-/

public section

open scoped Nat

namespace SymplecticGeometry

/-- The constants of the derivative bound for first-order systems
(`norm_iteratedFDeriv_le_of_eventually_fderiv_eq`): `K 0 = 1` and
`K (n + 1) = n ! * (1 + K n) ^ n`. -/
def firstOrderSystemConst : ℕ → ℕ
  | 0 => 1
  | n + 1 => n ! * (1 + firstOrderSystemConst n) ^ n

theorem firstOrderSystemConst_zero : firstOrderSystemConst 0 = 1 := (rfl)

theorem firstOrderSystemConst_succ (n : ℕ) :
    firstOrderSystemConst (n + 1) = n ! * (1 + firstOrderSystemConst n) ^ n := (rfl)

/-- The constants of the derivative bound for first-order systems are nondecreasing. -/
theorem firstOrderSystemConst_mono : Monotone firstOrderSystemConst := by
  refine monotone_nat_of_le_succ fun n ↦ ?_
  rw [firstOrderSystemConst_succ]
  rcases n with _ | n
  · simp [firstOrderSystemConst_zero]
  · calc firstOrderSystemConst (n + 1) ≤ (1 + firstOrderSystemConst (n + 1)) ^ 1 := by
          rw [pow_one]; omega
      _ ≤ (1 + firstOrderSystemConst (n + 1)) ^ (n + 1) :=
          Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ _ := Nat.le_mul_of_pos_left _ (Nat.factorial_pos _)

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Derivative bounds for first-order systems.** Let `h : E → F` be `C^r` at `w₀` and solve
`fderiv 𝕜 h w = Φ (w, h w)` for `w` near `w₀`, where `Φ` is `C^r` at `(w₀, h w₀)`. If the
derivatives of `Φ` at `(w₀, h w₀)` of order `< j` have norm at most `A`, then for `1 ≤ j ≤ r + 1`
the `j`-th derivative of `h` at `w₀` has norm at most `firstOrderSystemConst j * (1 + A) ^ j`. -/
theorem norm_iteratedFDeriv_le_of_eventually_fderiv_eq {h : E → F}
    {Φ : E × F → E →L[𝕜] F} {w₀ : E} {r j : ℕ} {A : ℝ}
    (hh : ContDiffAt 𝕜 r h w₀) (hΦ : ContDiffAt 𝕜 r Φ (w₀, h w₀))
    (heq : ∀ᶠ w in nhds w₀, fderiv 𝕜 h w = Φ (w, h w))
    (hA : ∀ i < j, ‖iteratedFDeriv 𝕜 i Φ (w₀, h w₀)‖ ≤ A) (hj₁ : 1 ≤ j) (hj : j ≤ r + 1) :
    ‖iteratedFDeriv 𝕜 j h w₀‖ ≤ firstOrderSystemConst j * (1 + A) ^ j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hj₁
  have hnr : n ≤ r := by omega
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0 (by omega))
  set M : ℝ := 1 + firstOrderSystemConst n
  have hM : 1 ≤ M := by simp [M]
  -- the `n`-th derivative of `fderiv 𝕜 h` at `w₀` is that of `Φ ∘ (fun w ↦ (w, h w))`
  have hcomp : iteratedFDeriv 𝕜 n (fderiv 𝕜 h) w₀ =
      iteratedFDeriv 𝕜 n (Φ ∘ fun w ↦ (w, h w)) w₀ :=
    (Filter.EventuallyEq.iteratedFDeriv 𝕜 (f₂ := Φ ∘ fun w ↦ (w, h w)) heq n).eq_of_nhds
  have hhn : ContDiffAt 𝕜 n h w₀ := hh.of_le (by exact_mod_cast hnr)
  -- the derivatives of `fun w ↦ (w, h w)` of positive order `i ≤ n` are at most `(M (1 + A)) ^ i`
  have hD : ∀ i, 1 ≤ i → i ≤ n →
      ‖iteratedFDeriv 𝕜 i (fun w ↦ (w, h w)) w₀‖ ≤ (M * (1 + A)) ^ i := by
    intro i hi₁ hin
    have hid := TauCeti.norm_iteratedFDeriv_id_le_one (𝕜 := 𝕜) (E := E) hi₁ w₀
    have hhi := ih i (by omega) (fun l hl ↦ hA l (by omega)) hi₁ (by omega)
    have hKi : (firstOrderSystemConst i : ℝ) ≤ firstOrderSystemConst n := by
      exact_mod_cast firstOrderSystemConst_mono hin
    have hprod : iteratedFDeriv 𝕜 i (fun w ↦ (w, h w)) w₀ =
        (iteratedFDeriv 𝕜 i id w₀).prod (iteratedFDeriv 𝕜 i h w₀) :=
      iteratedFDeriv_prodMk contDiffAt_id hhn (by exact_mod_cast hin)
    rw [hprod, ContinuousMultilinearMap.opNorm_prod, mul_pow]
    have h1A : 1 ≤ (1 + A) ^ i := one_le_pow₀ (by linarith)
    have hMi : M ≤ M ^ i := le_self_pow₀ hM (by omega)
    refine max_le ?_ ?_
    · nlinarith
    · nlinarith
  rw [← norm_iteratedFDeriv_fderiv, hcomp]
  refine (TauCeti.norm_iteratedFDeriv_comp_le_of_contDiffAt (f := fun w ↦ (w, h w))
    (hΦ.of_le (by exact_mod_cast hnr)) (contDiffAt_id.prodMk hhn) (fun i hi ↦ hA i (by omega))
    hD).trans ?_
  rw [firstOrderSystemConst_succ, mul_pow, pow_succ (1 + A)]
  push_cast
  calc (n ! : ℝ) * A * (M ^ n * (1 + A) ^ n) ≤ n ! * (1 + A) * (M ^ n * (1 + A) ^ n) := by
        gcongr; linarith
    _ = n ! * M ^ n * ((1 + A) ^ n * (1 + A)) := by ring

end SymplecticGeometry

end
