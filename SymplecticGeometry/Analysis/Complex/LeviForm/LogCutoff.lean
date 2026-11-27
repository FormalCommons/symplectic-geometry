/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import TauCeti.Analysis.Complex.LeviForm.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Surface.LogCutoff.Profile
import SymplecticGeometry.Analysis.Complex.LeviForm.Interpolation
import SymplecticGeometry.Geometry.Manifold.Riemannian.Surface.LogCutoff.Interpolation

/-!
# The Levi form of an interpolation with a logarithmic cutoff

Let `V` be a complex normed space, `f g ρ χ : V → ℝ`, and for `0 < 4ε ≤ δ ≤ 1` let
`β = χ (1 - logCutoffProfile ε δ ∘ ρ)` and `Λ = log (δ / ε)`. When the 1-jets of `f` and `g`
nearly agree at `p`, `|g p - f p| ≤ A ρ p` and `‖D(g - f)(p)‖ ≤ A √(ρ p)`, where `ρ` behaves like
a squared distance, `‖Dρ(p)‖ ≤ A √(ρ p)` and `‖D²ρ(p)‖ ≤ A`, and `χ`, with `|χ p| ≤ 1`, has first
and second derivatives at most `B`, the Levi form of `θ = f + β (g - f)` at `p` is close to the
convex combination of those of `f` and `g`:

* `TauCeti.exists_le_re_leviForm_add_logCutoff_mul_sub`: the real part of the Levi diagonal of
  `θ` at `p` is at least `(1 - β p) Re L f(v, v) + β p Re L g(v, v)` up to
  `K (A² + A³ + A² B + A B) (1 / Λ + √δ) ‖v‖²`, for an absolute constant `K`;
* `TauCeti.exists_mul_sq_norm_le_re_leviForm_add_logCutoff_mul_sub`: so, for `0 ≤ χ p ≤ 1`, lower
  bounds `m ‖v‖²` on the Levi diagonals of `f` and `g` give the lower bound
  `(m - K (A² + A³ + A² B + A B) (1 / Λ + √δ)) ‖v‖²` on that of `θ`.

It combines `TauCeti.le_re_leviForm_add_mul_sub_apply_self`, which bounds the Levi form of `θ` by
the error `|g p - f p| ‖D²β(p)‖ + ‖Dβ(p)‖ ‖D(g - f)(p)‖`, with the bound
`TauCeti.exists_abs_mul_norm_fderiv_fderiv_logCutoff_add_le` on that error. The bound on the
differential of `θ` is `TauCeti.norm_fderiv_add_logCutoff_mul_sub_sub_le`, over a real normed
space.

These are the estimates at a point behind the interpolation of two strictly plurisubharmonic
functions along a totally real submanifold, Proposition 3.26 of [CieliebakEliashberg2012],
following the logarithmic cutoff route of the library's design for that proposition.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012]
-/

public section

namespace TauCeti

/-- **The Levi form of an interpolation with a logarithmic cutoff.** There is an absolute
constant `K` with the following property. Let `V` be a complex normed space, `0 < 4ε ≤ δ ≤ 1`,
and let `f`, `g`, `ρ` and `χ` be real functions of class `C²` at `p`, with `|χ p| ≤ 1`,
`‖Dχ(p)‖ ≤ B`, `‖D²χ(p)‖ ≤ B`, `0 ≤ ρ p`, `‖Dρ(p)‖ ≤ A √(ρ p)`, `‖D²ρ(p)‖ ≤ A`, and
`|g p - f p| ≤ A ρ p`, `‖D(g - f)(p)‖ ≤ A √(ρ p)`. For the cutoff
`β = χ (1 - logCutoffProfile ε δ ∘ ρ)`, the real part of the Levi diagonal of
`θ = f + β (g - f)` at `p` is at least `(1 - β p) Re L f(v, v) + β p Re L g(v, v)`, up to the
error `K (A² + A³ + A² B + A B) (1 / log (δ / ε) + √δ) ‖v‖²`. -/
theorem exists_le_re_leviForm_add_logCutoff_mul_sub :
    ∃ K : ℝ, ∀ {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {f g ρ χ : V → ℝ} {p : V}
      {ε δ A B : ℝ}, 0 < ε → 4 * ε ≤ δ → δ ≤ 1 → ContDiffAt ℝ 2 f p → ContDiffAt ℝ 2 g p →
      ContDiffAt ℝ 2 ρ p → ContDiffAt ℝ 2 χ p → |χ p| ≤ 1 → ‖fderiv ℝ χ p‖ ≤ B →
      ‖fderiv ℝ (fderiv ℝ χ) p‖ ≤ B → 0 ≤ ρ p → ‖fderiv ℝ ρ p‖ ≤ A * √(ρ p) →
      ‖fderiv ℝ (fderiv ℝ ρ) p‖ ≤ A → |g p - f p| ≤ A * ρ p →
      ‖fderiv ℝ (g - f) p‖ ≤ A * √(ρ p) → ∀ v : V,
      (1 - (χ * (1 - logCutoffProfile ε δ ∘ ρ)) p) * (leviForm f p v v).re +
          (χ * (1 - logCutoffProfile ε δ ∘ ρ)) p * (leviForm g p v v).re -
          K * (A ^ 2 + A ^ 3 + A ^ 2 * B + A * B) * (1 / Real.log (δ / ε) + √δ) * ‖v‖ ^ 2 ≤
        (leviForm (f + χ * (1 - logCutoffProfile ε δ ∘ ρ) * (g - f)) p v v).re := by
  obtain ⟨K, hK⟩ := exists_abs_mul_norm_fderiv_fderiv_logCutoff_add_le
  refine ⟨K, fun {V} _ _ {f g ρ χ p ε δ A B} hε h4 hδ1 hf hg hρ hχ hχ1 hB hB' hρ0 hDρ hD2ρ hD
    hDD v ↦ ?_⟩
  have hu : ContDiffAt ℝ 2 (1 - logCutoffProfile ε δ ∘ ρ) p :=
    contDiffAt_const.sub (((contDiff_logCutoffProfile (by linarith)).contDiffAt.of_le
      (by simp)).comp p hρ)
  have hE := hK (u := g - f) hε h4 hδ1 hρ hχ hχ1 hB hB' hρ0 hDρ hD2ρ
    (by rwa [Pi.sub_apply]) hDD
  rw [Pi.sub_apply] at hE
  have := le_re_leviForm_add_mul_sub_apply_self (β := χ * (1 - logCutoffProfile ε δ ∘ ρ)) hf hg
    (hχ.mul hu) v
  have := mul_le_mul_of_nonneg_right hE (sq_nonneg ‖v‖)
  linarith

/-- **A lower bound on the Levi form of an interpolation with a logarithmic cutoff.** There is an
absolute constant `K` with the following property. Under the hypotheses of
`TauCeti.exists_le_re_leviForm_add_logCutoff_mul_sub`, with `0 ≤ χ p ≤ 1`, if
`m ‖v‖² ≤ Re L f(v, v)` and `m ‖v‖² ≤ Re L g(v, v)`, then for the cutoff
`β = χ (1 - logCutoffProfile ε δ ∘ ρ)` the real part of the Levi diagonal of
`θ = f + β (g - f)` at `p` is at least
`(m - K (A² + A³ + A² B + A B) (1 / log (δ / ε) + √δ)) ‖v‖²`. -/
theorem exists_mul_sq_norm_le_re_leviForm_add_logCutoff_mul_sub :
    ∃ K : ℝ, ∀ {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {f g ρ χ : V → ℝ} {p : V}
      {ε δ A B m : ℝ}, 0 < ε → 4 * ε ≤ δ → δ ≤ 1 → ContDiffAt ℝ 2 f p → ContDiffAt ℝ 2 g p →
      ContDiffAt ℝ 2 ρ p → ContDiffAt ℝ 2 χ p → 0 ≤ χ p → χ p ≤ 1 → ‖fderiv ℝ χ p‖ ≤ B →
      ‖fderiv ℝ (fderiv ℝ χ) p‖ ≤ B → 0 ≤ ρ p → ‖fderiv ℝ ρ p‖ ≤ A * √(ρ p) →
      ‖fderiv ℝ (fderiv ℝ ρ) p‖ ≤ A → |g p - f p| ≤ A * ρ p →
      ‖fderiv ℝ (g - f) p‖ ≤ A * √(ρ p) → ∀ v : V, m * ‖v‖ ^ 2 ≤ (leviForm f p v v).re →
      m * ‖v‖ ^ 2 ≤ (leviForm g p v v).re →
      (m - K * (A ^ 2 + A ^ 3 + A ^ 2 * B + A * B) * (1 / Real.log (δ / ε) + √δ)) * ‖v‖ ^ 2 ≤
        (leviForm (f + χ * (1 - logCutoffProfile ε δ ∘ ρ) * (g - f)) p v v).re := by
  obtain ⟨K, hK⟩ := exists_le_re_leviForm_add_logCutoff_mul_sub
  refine ⟨K, fun {V} _ _ {f g ρ χ p ε δ A B m} hε h4 hδ1 hf hg hρ hχ hχ0 hχ1 hB hB' hρ0 hDρ
    hD2ρ hD hDD v hLf hLg ↦ ?_⟩
  have hL := hK hε h4 hδ1 hf hg hρ hχ (abs_le.2 ⟨by linarith, hχ1⟩) hB hB' hρ0 hDρ hD2ρ hD hDD v
  have hεδ : 2 * ε ≤ δ := by linarith
  obtain ⟨hb0, hb1⟩ := mul_one_sub_logCutoffProfile_comp_mem_Icc (ρ := ρ) hε hεδ hχ0 hχ1
  have := mul_le_mul_of_nonneg_left hLf (sub_nonneg.2 hb1)
  have := mul_le_mul_of_nonneg_left hLg hb0
  linarith

end TauCeti

end
