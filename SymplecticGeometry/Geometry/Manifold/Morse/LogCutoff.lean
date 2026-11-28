/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Support
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.Module
import SymplecticGeometry.Analysis.Normed.Operator.Functional
import SymplecticGeometry.Geometry.Manifold.Riemannian.Surface.LogCutoff.Ball

/-!
# A logarithmic cut-off keeps a field gradient-like

Let `E` be a finite-dimensional real normed space, `X : E → E` a field and `f H : E → ℝ`
differentiable on a ball `B` around `0`, such that on `B` the field `X` satisfies the
gradient-like inequality `c (‖X‖² + ‖Df‖²) ≤ Df(X)` for both `f` and `f + H`, and
`|H z| ≤ A ‖z‖ ‖Df(z)‖`. This file shows that for every `r > 0` there is a smooth cut-off
`β : E → [0, 1]`, equal to `1` near `0` and supported in the ball of radius `r`, such that `X`
satisfies the gradient-like inequality on `B`, with constant `c / 2`, for every function
`f + t β H` with `t ∈ [0, 1]`. The constant does not depend on `r`.

The cut-off `β` is the one of
`SymplecticGeometry.exists_contDiff_tsupport_subset_ball_norm_mul_norm_fderiv_le`, built from
Tau Ceti's logarithmic profile, with `‖z‖ ‖Dβ(z)‖` small. The differential of `f + t β H` is
`(1 - tβ) Df + tβ D(f + H) + t H Dβ`. The first two terms satisfy the gradient-like inequality
with the constant `c`, by convexity
(`ContinuousLinearMap.mul_le_one_sub_smul_add_smul_add_apply`).
The last term has norm at most `A ‖z‖ ‖Dβ(z)‖ ‖Df(z)‖`; since `c ‖Df‖ ≤ ‖X‖`, it costs only half
of the constant once `‖z‖ ‖Dβ(z)‖` is small enough. A cut-off with `‖Dβ‖` of order `1 / r` would
not do, since `A` need not be small: this is why the cut-off is logarithmic.

This is the estimate that lets one cut off `t H` near a critical point in the proof of
Proposition 9.23 of [CieliebakEliashberg2012], as in their Lemma 12.9, where `|H| ≤ A ‖z‖ ‖Df‖`
comes from the radial estimates of `Morse/RadialEstimate.lean`.

The file also proves the version in which `f` stays fixed and the field moves. Let `X` and `X'`
both satisfy the gradient-like inequality for `f` on `B`, with `X' - X = J(DH)` for a bounded
family `J` of linear maps from covectors to vectors (in the application, `J(DG)` is the
Hamiltonian field of `G`). Then the same logarithmic cut-off `β` makes every field
`X + t J(D(β H))` with `t ∈ [0, 1]` gradient-like for `f` on `B`, with constant `c / 2`. Here
`X + t J(D(β H)) = (1 - tβ) X + tβ X' + t H J(Dβ)`, and the pointwise estimate,
with the roles of vectors and covectors exchanged, is
`ContinuousLinearMap.mul_le_apply_one_sub_smul_add_smul_add`. This is the field version
of the cut-off in Lemma 12.9 of [CieliebakEliashberg2012].

Both pointwise estimates are cases of one statement about a linear functional `φ` on a
seminormed space, `ContinuousLinearMap.mul_le_apply_one_sub_smul_add_smul_add_of_le`, taking
`φ` to be evaluation at `v` in the first and the covector `a` in the second; each then only
bounds its own error term. Both cut-offs, with the constant `m` that bounds their error, come from
`SymplecticGeometry.exists_contDiff_tsupport_subset_ball_mul_norm_mul_norm_fderiv_le`.

## Main results

* `SymplecticGeometry.exists_contDiff_tsupport_subset_ball_mul_norm_mul_norm_fderiv_le`: the
  logarithmic cut-off together with a constant `m` with `2 (m + m²) ≤ c²` and
  `K ‖z‖ ‖Dβ(z)‖ ≤ m`.
* `SymplecticGeometry.exists_contDiff_tsupport_subset_ball_mul_le_fderiv_add_smul_mul_apply`:
  the cut-off `β` above.
* `SymplecticGeometry.exists_contDiff_tsupport_subset_ball_mul_le_fderiv_apply_add_smul`: the
  cut-off of a Hamiltonian correction of the field.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012]
-/

public section

open Set Metric Filter Topology
open scoped ContDiff

namespace SymplecticGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **A logarithmic cut-off with a margin for the gradient-like inequality.** Let `E` be a
finite-dimensional real normed space, `c > 0`, `K : ℝ` and `r > 0`. There are a smooth
`β : E → ℝ` with values in `[0, 1]`, equal to `1` near `0`, with topological support in
`ball 0 r`, and a constant `m` with `2 (m + m²) ≤ c²` and `K (‖z‖ ‖Dβ(z)‖) ≤ m` for every `z`. -/
theorem exists_contDiff_tsupport_subset_ball_mul_norm_mul_norm_fderiv_le {c K r : ℝ}
    (hc : 0 < c) (hr : 0 < r) :
    ∃ (β : E → ℝ) (m : ℝ), ContDiff ℝ ∞ β ∧ (∀ z, β z ∈ Icc (0 : ℝ) 1) ∧
      (∀ᶠ z in 𝓝 0, β z = 1) ∧ tsupport β ⊆ ball 0 r ∧ 2 * (m + m ^ 2) ≤ c ^ 2 ∧
      ∀ z, K * (‖z‖ * ‖fderiv ℝ β z‖) ≤ m := by
  set K' := max K 0
  set m := min (c ^ 2 / 4) 1
  have hm0 : 0 < m := lt_min (by positivity) one_pos
  obtain ⟨β, hβc, hβI, hβ1, hβs, hβD⟩ :=
    exists_contDiff_tsupport_subset_ball_norm_mul_norm_fderiv_le (E := E) hr
      (div_pos hm0 (by positivity : 0 < K' + 1))
  refine ⟨β, m, hβc, hβI, hβ1, hβs, ?_, fun z ↦ ?_⟩
  · have h1 : m ≤ c ^ 2 / 4 := min_le_left _ _
    have h2 : m ≤ 1 := min_le_right _ _
    nlinarith
  · have hKm : K' * (m / (K' + 1)) ≤ m := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith [le_max_right K 0]
    calc K * (‖z‖ * ‖fderiv ℝ β z‖) ≤ K' * (‖z‖ * ‖fderiv ℝ β z‖) := by
          gcongr; exact le_max_left _ _
      _ ≤ K' * (m / (K' + 1)) := by gcongr; exact hβD z
      _ ≤ m := hKm

/-- **A logarithmic cut-off keeps a field gradient-like.** Let `E` be a finite-dimensional real
normed space, `X : E → E`, and `f H : E → ℝ` differentiable on `ball 0 r₀`, such that for every
`z` in that ball and some `c > 0` and `A`,
* `c (‖X z‖² + ‖Df(z)‖²) ≤ Df(z) (X z)`,
* `c (‖X z‖² + ‖D(f + H)(z)‖²) ≤ D(f + H)(z) (X z)`,
* `|H z| ≤ A ‖z‖ ‖Df(z)‖`.

Then for every `r > 0` there is a smooth `β : E → ℝ` with values in `[0, 1]`, equal to `1` near
`0`, with topological support in `ball 0 r`, such that for every `t ∈ [0, 1]` and `z` in
`ball 0 r₀`, with `F = f + t • (β * H)`,
`c / 2 * (‖X z‖² + ‖DF(z)‖²) ≤ DF(z) (X z)`. -/
theorem exists_contDiff_tsupport_subset_ball_mul_le_fderiv_add_smul_mul_apply {f H : E → ℝ}
    {X : E → E} {r₀ c A : ℝ} (hc : 0 < c) (hf : DifferentiableOn ℝ f (ball 0 r₀))
    (hH : DifferentiableOn ℝ H (ball 0 r₀))
    (h₁ : ∀ z ∈ ball (0 : E) r₀, c * (‖X z‖ ^ 2 + ‖fderiv ℝ f z‖ ^ 2) ≤ fderiv ℝ f z (X z))
    (h₂ : ∀ z ∈ ball (0 : E) r₀,
      c * (‖X z‖ ^ 2 + ‖fderiv ℝ (f + H) z‖ ^ 2) ≤ fderiv ℝ (f + H) z (X z))
    (h₃ : ∀ z ∈ ball (0 : E) r₀, |H z| ≤ A * ‖z‖ * ‖fderiv ℝ f z‖) {r : ℝ} (hr : 0 < r) :
    ∃ β : E → ℝ, ContDiff ℝ ∞ β ∧ (∀ z, β z ∈ Icc (0 : ℝ) 1) ∧ (∀ᶠ z in 𝓝 0, β z = 1) ∧
      tsupport β ⊆ ball 0 r ∧ ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ ball (0 : E) r₀,
        c / 2 * (‖X z‖ ^ 2 + ‖fderiv ℝ (f + t • (β * H)) z‖ ^ 2) ≤
          fderiv ℝ (f + t • (β * H)) z (X z) := by
  -- The error `t H Dβ` will be at most `m ‖Df‖`, with `2 (m + m ^ 2) ≤ c ^ 2`.
  obtain ⟨β, m, hβc, hβI, hβ1, hβs, hm, hβD⟩ :=
    exists_contDiff_tsupport_subset_ball_mul_norm_mul_norm_fderiv_le (E := E) (K := A) hc hr
  refine ⟨β, hβc, hβI, hβ1, hβs, fun t ht z hz₀ ↦ ?_⟩
  -- The differential of `f + t • (β * H)` at `z`.
  have hfz := (hf z hz₀).differentiableAt (isOpen_ball.mem_nhds hz₀)
  have hHz := (hH z hz₀).differentiableAt (isOpen_ball.mem_nhds hz₀)
  have hβz : DifferentiableAt ℝ β z := hβc.differentiable (by simp) z
  have hDF : fderiv ℝ (f + t • (β * H)) z =
      (1 - t * β z) • fderiv ℝ f z + (t * β z) • fderiv ℝ (f + H) z +
        (t * H z) • fderiv ℝ β z := by
    rw [fderiv_add hfz ((hβz.mul hHz).const_smul t), fderiv_const_smul (hβz.mul hHz),
      fderiv_mul hβz hHz, fderiv_add hfz hHz]
    module
  rw [hDF]
  refine ContinuousLinearMap.mul_le_one_sub_smul_add_smul_add_apply hc
    (unitInterval.mul_mem ht (hβI z)) (h₁ z hz₀) (h₂ z hz₀) hm ?_
  -- The error term `t H Dβ`.
  rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg ht.1]
  calc t * |H z| * ‖fderiv ℝ β z‖ ≤ 1 * (A * ‖z‖ * ‖fderiv ℝ f z‖) * ‖fderiv ℝ β z‖ := by
        gcongr
        · exact ht.2
        · exact h₃ z hz₀
    _ = A * (‖z‖ * ‖fderiv ℝ β z‖) * ‖fderiv ℝ f z‖ := by ring
    _ ≤ m * ‖fderiv ℝ f z‖ := by gcongr; exact hβD z

/-- **A cut-off Hamiltonian correction keeps a field gradient-like.** Let `E` be a
finite-dimensional real normed space, `f H : E → ℝ` with `H` differentiable on `ball 0 r₀`,
`X X' : E → E` and `J : E → (E →L[ℝ] ℝ) →L[ℝ] E`, such that for every `z` in that ball and some
`c > 0`, `A` and `B`,
* `c (‖X z‖² + ‖Df(z)‖²) ≤ Df(z) (X z)` and the same for `X'`,
* `X' z - X z = J z (DH(z))`,
* `‖J z‖ ≤ B` and `|H z| ≤ A ‖z‖ ‖Df(z)‖`.

Then for every `r > 0` there is a smooth `β : E → ℝ` with values in `[0, 1]`, equal to `1` near
`0`, with topological support in `ball 0 r`, such that for every `t ∈ [0, 1]` and `z` in
`ball 0 r₀`, with `Y = X z + t • J z (D(β H)(z))`,
`c / 2 * (‖Y‖² + ‖Df(z)‖²) ≤ Df(z) Y`. -/
theorem exists_contDiff_tsupport_subset_ball_mul_le_fderiv_apply_add_smul {f H : E → ℝ}
    {X X' : E → E} {J : E → (E →L[ℝ] ℝ) →L[ℝ] E} {r₀ c A B : ℝ} (hc : 0 < c)
    (hH : DifferentiableOn ℝ H (ball 0 r₀))
    (h₁ : ∀ z ∈ ball (0 : E) r₀, c * (‖X z‖ ^ 2 + ‖fderiv ℝ f z‖ ^ 2) ≤ fderiv ℝ f z (X z))
    (h₂ : ∀ z ∈ ball (0 : E) r₀, c * (‖X' z‖ ^ 2 + ‖fderiv ℝ f z‖ ^ 2) ≤ fderiv ℝ f z (X' z))
    (h₃ : ∀ z ∈ ball (0 : E) r₀, X' z - X z = J z (fderiv ℝ H z))
    (h₄ : ∀ z ∈ ball (0 : E) r₀, ‖J z‖ ≤ B)
    (h₅ : ∀ z ∈ ball (0 : E) r₀, |H z| ≤ A * ‖z‖ * ‖fderiv ℝ f z‖) {r : ℝ} (hr : 0 < r) :
    ∃ β : E → ℝ, ContDiff ℝ ∞ β ∧ (∀ z, β z ∈ Icc (0 : ℝ) 1) ∧ (∀ᶠ z in 𝓝 0, β z = 1) ∧
      tsupport β ⊆ ball 0 r ∧ ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ ball (0 : E) r₀,
        c / 2 * (‖X z + t • J z (fderiv ℝ (β * H) z)‖ ^ 2 + ‖fderiv ℝ f z‖ ^ 2) ≤
          fderiv ℝ f z (X z + t • J z (fderiv ℝ (β * H) z)) := by
  -- The error `t H J(Dβ)` will be at most `m ‖Df‖`, with `2 (m + m ^ 2) ≤ c ^ 2`.
  obtain ⟨β, m, hβc, hβI, hβ1, hβs, hm, hβD⟩ :=
    exists_contDiff_tsupport_subset_ball_mul_norm_mul_norm_fderiv_le (E := E) (K := A * B) hc hr
  refine ⟨β, hβc, hβI, hβ1, hβs, fun t ht z hz₀ ↦ ?_⟩
  -- The corrected field at `z`.
  have hHz := (hH z hz₀).differentiableAt (isOpen_ball.mem_nhds hz₀)
  have hβz : DifferentiableAt ℝ β z := hβc.differentiable (by simp) z
  have hY : X z + t • J z (fderiv ℝ (β * H) z) =
      (1 - t * β z) • X z + (t * β z) • X' z + (t * H z) • J z (fderiv ℝ β z) := by
    rw [fderiv_mul hβz hHz, map_add, map_smul, map_smul, ← h₃ z hz₀]
    module
  rw [hY]
  refine ContinuousLinearMap.mul_le_apply_one_sub_smul_add_smul_add hc
    (unitInterval.mul_mem ht (hβI z)) (h₁ z hz₀) (h₂ z hz₀) hm ?_
  -- The error term `t H J(Dβ)`.
  have hA : 0 ≤ A * ‖z‖ * ‖fderiv ℝ f z‖ := (abs_nonneg _).trans (h₅ z hz₀)
  rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg ht.1]
  calc t * |H z| * ‖J z (fderiv ℝ β z)‖
      ≤ 1 * (A * ‖z‖ * ‖fderiv ℝ f z‖) * (B * ‖fderiv ℝ β z‖) := by
        gcongr
        · exact ht.2
        · exact h₅ z hz₀
        · exact (J z).le_opNorm_of_le le_rfl |>.trans (by gcongr; exact h₄ z hz₀)
    _ = A * B * (‖z‖ * ‖fderiv ℝ β z‖) * ‖fderiv ℝ f z‖ := by ring
    _ ≤ m * ‖fderiv ℝ f z‖ := by gcongr; exact hβD z

end SymplecticGeometry

end
