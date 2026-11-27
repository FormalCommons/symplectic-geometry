/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Real.Sqrt
public import TauCeti.Analysis.Complex.LeviForm.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Surface.LogCutoff.Profile
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.Module
import SymplecticGeometry.Analysis.Calculus.FDeriv.Mul
import TauCeti.Analysis.Calculus.SecondDerivative
import SymplecticGeometry.Analysis.Complex.LeviForm.Interpolation
import SymplecticGeometry.Geometry.Manifold.Riemannian.Surface.LogCutoff.Comp

/-!
# Interpolation with a logarithmic cutoff

Let `V` be a complex normed space, `f g ρ χ : V → ℝ`, `D = g - f`, and for `0 < 4ε ≤ δ` let
`β = χ (1 - ψ ∘ ρ)` with `ψ = TauCeti.logCutoffProfile ε δ` and `Λ = log (δ / ε)`. This file
estimates, at a point `p`, how far `θ = f + β D` is from the convex combination of `f` and `g`
with weights `1 - β p` and `β p`, when the 1-jets of `f` and `g` nearly agree:
`|D p| ≤ A ρ p`, `‖DD(p)‖ ≤ A √(ρ p)`, and `ρ` behaves like a squared distance,
`‖Dρ(p)‖ ≤ A √(ρ p)`, `‖D²ρ(p)‖ ≤ A`; the factor `χ`, with `|χ p| ≤ 1`, has first and second
derivatives at most `B`.

* `TauCeti.norm_fderiv_add_logCutoff_mul_sub_sub_le`: the differential of `θ` at `p` is
  `(1 - β p) Df(p) + β p Dg(p)` up to `D p • Dβ(p)`, of norm at most
  `logCutoffConst A² √δ / Λ + A B δ`.
* `TauCeti.exists_le_re_leviForm_add_logCutoff_mul_sub`: for `δ ≤ 1`, the real part of the
  Levi diagonal of `θ` at `p` is at least `(1 - β p) Re L f(v, v) + β p Re L g(v, v)` up to
  `K (A² + A³ + A² B + A B) (1 / Λ + √δ) ‖v‖²`, for an absolute constant `K`.

Both errors tend to `0` when `δ → 0` and then `ε → 0`, uniformly in `p`. Where `ρ p > δ` the
cutoff vanishes near `p` and there is no error. Where `ρ p ≤ δ`, the Levi form estimate comes
from `TauCeti.le_re_leviForm_add_mul_sub_apply_self`, whose error
`|D p| ‖D²β(p)‖ + ‖Dβ(p)‖ ‖DD(p)‖` is bounded with the product rules
`SymplecticGeometry.norm_fderiv_mul_le` and `SymplecticGeometry.norm_fderiv_fderiv_mul_le` and
the bounds `TauCeti.sqrt_mul_norm_fderiv_logCutoffProfile_comp_le` and
`TauCeti.exists_mul_norm_fderiv_fderiv_logCutoffProfile_comp_le` on the derivatives of `ψ ∘ ρ`.
The terms with `Dχ` and `D²χ` are where `δ ≤ 1` is used: `|D p| ‖D²χ(p)‖` is only at most
`A B δ`, which is at most `A B √δ` once `δ ≤ 1`.

These are the estimates at a point behind the interpolation of two strictly plurisubharmonic
functions along a totally real submanifold, Proposition 3.26 of [CieliebakEliashberg2012]. The
argument is the logarithmic cutoff route of the library's design for that proposition; it is not
a transcription of a numbered lemma of the book's proof.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012]
-/

public section

open Filter Topology

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {f g ρ χ : V → ℝ} {p : V}
  {ε δ A B : ℝ}

omit [NormedSpace ℂ V] in
/-- Near a point where `ρ > δ`, the cutoff `χ * (1 - logCutoffProfile ε δ ∘ ρ)` vanishes. -/
private theorem notMem_tsupport_mul_one_sub_logCutoffProfile_comp (hε : 0 < ε)
    (h4 : 4 * ε ≤ δ) (hρ : ContinuousAt ρ p) (hp : δ < ρ p) :
    p ∉ tsupport (χ * (1 - logCutoffProfile ε δ ∘ ρ)) := by
  refine notMem_tsupport_iff_eventuallyEq.2 ?_
  filter_upwards [continuousAt_const.eventually_lt hρ hp] with x hx
  simp [logCutoffProfile_eq_one_of_ge hε (by linarith) hx.le]

/-- The cutoff `u = 1 - logCutoffProfile ε δ ∘ ρ` is `C²` at `p`, takes values in `[-1, 1]`, and
its first and second derivatives have the norms of those of `logCutoffProfile ε δ ∘ ρ`. -/
private theorem one_sub_logCutoffProfile_comp_props (hε : 0 < ε) (h4 : 4 * ε ≤ δ)
    (hρ : ContDiffAt ℝ 2 ρ p) :
    ContDiffAt ℝ 2 (1 - logCutoffProfile ε δ ∘ ρ) p ∧
      |(1 - logCutoffProfile ε δ ∘ ρ) p| ≤ 1 ∧
      ‖fderiv ℝ (1 - logCutoffProfile ε δ ∘ ρ) p‖ = ‖fderiv ℝ (logCutoffProfile ε δ ∘ ρ) p‖ ∧
      ‖fderiv ℝ (fderiv ℝ (1 - logCutoffProfile ε δ ∘ ρ)) p‖ =
        ‖fderiv ℝ (fderiv ℝ (logCutoffProfile ε δ ∘ ρ)) p‖ := by
  have hh : ContDiffAt ℝ 2 (logCutoffProfile ε δ ∘ ρ) p :=
    ((contDiff_logCutoffProfile (by linarith)).contDiffAt.of_le (by simp)).comp p hρ
  -- `fderiv_const_sub` is stated for `fun y ↦ 1 - h y`, which unfolds `1 - h`.
  have hD : fderiv ℝ (1 - logCutoffProfile ε δ ∘ ρ) = -fderiv ℝ (logCutoffProfile ε δ ∘ ρ) :=
    funext fun _ ↦ fderiv_const_sub (1 : ℝ)
  have h0 := logCutoffProfile_nonneg (δ := δ) hε (by linarith) (ρ p)
  have h1 := logCutoffProfile_le_one (δ := δ) hε (by linarith) (ρ p)
  refine ⟨contDiffAt_const.sub hh, abs_le.2 ⟨?_, ?_⟩, ?_, ?_⟩
  · simp only [Pi.sub_apply, Pi.one_apply, Function.comp_apply]; linarith
  · simp only [Pi.sub_apply, Pi.one_apply, Function.comp_apply]; linarith
  · rw [hD, Pi.neg_apply, norm_neg]
  · rw [hD, fderiv_neg]
    exact norm_neg (fderiv ℝ (fderiv ℝ (logCutoffProfile ε δ ∘ ρ)) p)

/-- The first derivative of the cutoff `χ * (1 - logCutoffProfile ε δ ∘ ρ)`. -/
private theorem norm_fderiv_mul_one_sub_logCutoffProfile_comp_le (hε : 0 < ε) (h4 : 4 * ε ≤ δ)
    (hρ : ContDiffAt ℝ 2 ρ p) (hχ : DifferentiableAt ℝ χ p) (hχ1 : |χ p| ≤ 1)
    (hB : ‖fderiv ℝ χ p‖ ≤ B) :
    ‖fderiv ℝ (χ * (1 - logCutoffProfile ε δ ∘ ρ)) p‖ ≤
      ‖fderiv ℝ (logCutoffProfile ε δ ∘ ρ) p‖ + B := by
  obtain ⟨hu, hu1, hDu, -⟩ := one_sub_logCutoffProfile_comp_props hε h4 hρ
  refine (SymplecticGeometry.norm_fderiv_mul_le hχ (hu.differentiableAt (by simp))).trans ?_
  rw [hDu, Real.norm_eq_abs, Real.norm_eq_abs]
  have := norm_nonneg (fderiv ℝ (logCutoffProfile ε δ ∘ ρ) p)
  have := norm_nonneg (fderiv ℝ χ p)
  calc _ ≤ 1 * ‖fderiv ℝ (logCutoffProfile ε δ ∘ ρ) p‖ + 1 * ‖fderiv ℝ χ p‖ := by
        gcongr
    _ ≤ _ := by linarith

/-- The second derivative of the cutoff `χ * (1 - logCutoffProfile ε δ ∘ ρ)`. -/
private theorem norm_fderiv_fderiv_mul_one_sub_logCutoffProfile_comp_le (hε : 0 < ε)
    (h4 : 4 * ε ≤ δ) (hρ : ContDiffAt ℝ 2 ρ p) (hχ : ContDiffAt ℝ 2 χ p) (hχ1 : |χ p| ≤ 1)
    (hB : ‖fderiv ℝ χ p‖ ≤ B) (hB' : ‖fderiv ℝ (fderiv ℝ χ) p‖ ≤ B) :
    ‖fderiv ℝ (fderiv ℝ (χ * (1 - logCutoffProfile ε δ ∘ ρ))) p‖ ≤
      ‖fderiv ℝ (fderiv ℝ (logCutoffProfile ε δ ∘ ρ)) p‖ + B +
        2 * (B * ‖fderiv ℝ (logCutoffProfile ε δ ∘ ρ) p‖) := by
  obtain ⟨hu, hu1, hDu, hD2u⟩ := one_sub_logCutoffProfile_comp_props hε h4 hρ
  refine (SymplecticGeometry.norm_fderiv_fderiv_mul_le hχ hu).trans ?_
  rw [hDu, hD2u, Real.norm_eq_abs, Real.norm_eq_abs]
  have := norm_nonneg (fderiv ℝ (logCutoffProfile ε δ ∘ ρ) p)
  have := norm_nonneg (fderiv ℝ (fderiv ℝ (logCutoffProfile ε δ ∘ ρ)) p)
  have := norm_nonneg (fderiv ℝ (fderiv ℝ χ) p)
  calc _ ≤ 1 * ‖fderiv ℝ (fderiv ℝ (logCutoffProfile ε δ ∘ ρ)) p‖ +
        1 * ‖fderiv ℝ (fderiv ℝ χ) p‖ +
          2 * (B * ‖fderiv ℝ (logCutoffProfile ε δ ∘ ρ) p‖) := by
        gcongr
    _ ≤ _ := by linarith

/-- **The differential of an interpolation with a logarithmic cutoff.** Let `0 < 4ε ≤ δ`, let
`f`, `g` and `χ` be differentiable at `p` and `ρ` of class `C²` at `p`, with `|χ p| ≤ 1`,
`‖Dχ(p)‖ ≤ B`, `0 ≤ ρ p`, `0 ≤ A`, `‖Dρ(p)‖ ≤ A √(ρ p)`, and `|g p - f p| ≤ A ρ p`. For the cutoff
`β = χ (1 - logCutoffProfile ε δ ∘ ρ)`, the differential of `θ = f + β (g - f)` at `p` differs
from the convex combination `(1 - β p) Df(p) + β p Dg(p)` by at most
`logCutoffConst A² √δ / log (δ / ε) + A B δ`. -/
theorem norm_fderiv_add_logCutoff_mul_sub_sub_le (hε : 0 < ε) (h4 : 4 * ε ≤ δ)
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) (hρ : ContDiffAt ℝ 2 ρ p)
    (hχ : DifferentiableAt ℝ χ p) (hχ1 : |χ p| ≤ 1) (hB : ‖fderiv ℝ χ p‖ ≤ B)
    (hρ0 : 0 ≤ ρ p) (hA0 : 0 ≤ A) (hDρ : ‖fderiv ℝ ρ p‖ ≤ A * √(ρ p))
    (hD : |g p - f p| ≤ A * ρ p) :
    ‖fderiv ℝ (f + χ * (1 - logCutoffProfile ε δ ∘ ρ) * (g - f)) p -
        ((1 - (χ * (1 - logCutoffProfile ε δ ∘ ρ)) p) • fderiv ℝ f p +
          (χ * (1 - logCutoffProfile ε δ ∘ ρ)) p • fderiv ℝ g p)‖ ≤
      logCutoffConst * A ^ 2 * √δ / Real.log (δ / ε) + A * B * δ := by
  set β := χ * (1 - logCutoffProfile ε δ ∘ ρ)
  have hu := (one_sub_logCutoffProfile_comp_props hε h4 hρ).1
  have hβ : DifferentiableAt ℝ β p := hχ.mul (hu.differentiableAt (by simp))
  have hΛ : 0 < Real.log (δ / ε) := Real.log_pos ((one_lt_div hε).2 (by linarith))
  have hB0 : 0 ≤ B := (norm_nonneg (fderiv ℝ χ p)).trans hB
  have heq : fderiv ℝ (f + β * (g - f)) p - ((1 - β p) • fderiv ℝ f p + β p • fderiv ℝ g p) =
      (g p - f p) • fderiv ℝ β p := by
    rw [fderiv_add hf (hβ.mul (hg.sub hf)), fderiv_mul hβ (hg.sub hf), fderiv_sub hg hf,
      Pi.sub_apply]
    module
  rw [heq, norm_smul, Real.norm_eq_abs]
  have hR : 0 ≤ logCutoffConst * A ^ 2 * √δ / Real.log (δ / ε) + A * B * δ := by
    have := logCutoffConst_pos
    have : 0 ≤ δ := by linarith
    positivity
  rcases le_or_gt (ρ p) δ with hpδ | hpδ
  · have h1 := sqrt_mul_norm_fderiv_logCutoffProfile_comp_le hε h4
      (hρ.differentiableAt (by simp)) hA0 hDρ
    have h2 := norm_fderiv_mul_one_sub_logCutoffProfile_comp_le hε h4 hρ hχ hχ1 hB
    set s := √(ρ p)
    set a := ‖fderiv ℝ (logCutoffProfile ε δ ∘ ρ) p‖
    have hρs : ρ p = s * s := (Real.mul_self_sqrt hρ0).symm
    have hsδ : s ≤ √δ := Real.sqrt_le_sqrt hpδ
    calc |g p - f p| * ‖fderiv ℝ β p‖ ≤ A * ρ p * (a + B) :=
          mul_le_mul hD h2 (norm_nonneg _) (by positivity)
      _ = A * s * (s * a) + A * B * ρ p := by rw [hρs]; ring
      _ ≤ A * √δ * (logCutoffConst * A / Real.log (δ / ε)) + A * B * δ := by
          gcongr
      _ = _ := by ring
  · rw [fderiv_of_notMem_tsupport ℝ (notMem_tsupport_mul_one_sub_logCutoffProfile_comp hε h4
      hρ.continuousAt hpδ), norm_zero, mul_zero]
    exact hR

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
  obtain ⟨c, hc⟩ := exists_mul_norm_fderiv_fderiv_logCutoffProfile_comp_le
  refine ⟨|c| + 2 * logCutoffConst + 2, fun {V} _ _ {f g ρ χ p ε δ A B} hε h4 hδ1 hf hg hρ hχ
    hχ1 hB hB' hρ0 hDρ hD2ρ hD hDD v ↦ ?_⟩
  set β := χ * (1 - logCutoffProfile ε δ ∘ ρ)
  set K := |c| + 2 * logCutoffConst + 2
  set P := A ^ 2 + A ^ 3 + A ^ 2 * B + A * B
  have hu := (one_sub_logCutoffProfile_comp_props hε h4 hρ).1
  have hβ : ContDiffAt ℝ 2 β p := hχ.mul hu
  have hΛ : 0 < Real.log (δ / ε) := Real.log_pos ((one_lt_div hε).2 (by linarith))
  have hA0 : 0 ≤ A := (norm_nonneg (fderiv ℝ (fderiv ℝ ρ) p)).trans hD2ρ
  have hB0 : 0 ≤ B := (norm_nonneg (fderiv ℝ χ p)).trans hB
  have hc₀ := logCutoffConst_pos
  have hP : 0 ≤ P := by positivity
  have hR : 0 ≤ K * P * (1 / Real.log (δ / ε) + √δ) := by positivity
  have hE : |g p - f p| * ‖fderiv ℝ (fderiv ℝ β) p‖ + ‖fderiv ℝ β p‖ * ‖fderiv ℝ (g - f) p‖ ≤
      K * P * (1 / Real.log (δ / ε) + √δ) := by
    rcases le_or_gt (ρ p) δ with hpδ | hpδ
    · have h1 := sqrt_mul_norm_fderiv_logCutoffProfile_comp_le hε h4
        (hρ.differentiableAt (by simp)) hA0 hDρ
      have h2 := hc hε h4 hρ hDρ hD2ρ
      have hDβ := norm_fderiv_mul_one_sub_logCutoffProfile_comp_le hε h4 hρ
        (hχ.differentiableAt (by simp)) hχ1 hB
      have hD2β :=
        norm_fderiv_fderiv_mul_one_sub_logCutoffProfile_comp_le hε h4 hρ hχ hχ1 hB hB'
      set s := √(ρ p)
      set a₁ := ‖fderiv ℝ (logCutoffProfile ε δ ∘ ρ) p‖
      set a₂ := ‖fderiv ℝ (fderiv ℝ (logCutoffProfile ε δ ∘ ρ)) p‖
      set Λ := Real.log (δ / ε)
      have hρs : ρ p = s * s := (Real.mul_self_sqrt hρ0).symm
      have hs0 : 0 ≤ s := Real.sqrt_nonneg _
      have hsδ : s ≤ √δ := Real.sqrt_le_sqrt hpδ
      have hδ0 : 0 ≤ δ := by linarith
      have hsqδ1 : √δ ≤ 1 := Real.sqrt_le_one.mpr hδ1
      have hs1 : s ≤ 1 := hsδ.trans hsqδ1
      have hδsq : δ ≤ √δ := by
        have := Real.mul_self_sqrt hδ0
        nlinarith [Real.sqrt_nonneg δ]
      have hρδ : ρ p ≤ √δ := hpδ.trans hδsq
      have hnum : c * (A ^ 2 + A ^ 3) + 2 * logCutoffConst * (A ^ 2 * B) +
          logCutoffConst * A ^ 2 ≤ K * P := by
        have : c * (A ^ 2 + A ^ 3) ≤ |c| * (A ^ 2 + A ^ 3) :=
          mul_le_mul_of_nonneg_right (le_abs_self c) (by positivity)
        have := mul_nonneg (abs_nonneg c) (by positivity : 0 ≤ A ^ 2 * B + A * B)
        have := mul_nonneg hc₀.le (by positivity : 0 ≤ A ^ 3 + A * B)
        have : 0 ≤ A ^ 2 + A ^ 3 + A ^ 2 * B + A * B := hP
        nlinarith
      have hAB : 2 * (A * B) ≤ K * P := by
        have := mul_nonneg (abs_nonneg c) hP
        have := mul_nonneg hc₀.le hP
        have : 0 ≤ A ^ 2 + A ^ 3 + A ^ 2 * B := by positivity
        nlinarith
      calc |g p - f p| * ‖fderiv ℝ (fderiv ℝ β) p‖ + ‖fderiv ℝ β p‖ * ‖fderiv ℝ (g - f) p‖
          ≤ A * ρ p * (a₂ + B + 2 * (B * a₁)) + (a₁ + B) * (A * s) := by
            gcongr
        _ = A * (ρ p * a₂) + A * B * ρ p + 2 * (A * B) * s * (s * a₁) + A * (s * a₁) +
            A * B * s := by rw [hρs]; ring
        _ ≤ A * (c * (A + A ^ 2) / Λ) + A * B * √δ + 2 * (A * B) * 1 * (logCutoffConst * A / Λ) +
            A * (logCutoffConst * A / Λ) + A * B * √δ := by gcongr
        _ = (c * (A ^ 2 + A ^ 3) + 2 * logCutoffConst * (A ^ 2 * B) + logCutoffConst * A ^ 2) *
            (1 / Λ) + 2 * (A * B) * √δ := by ring
        _ ≤ K * P * (1 / Λ) + K * P * √δ := by gcongr
        _ = _ := by ring
    · have hp := notMem_tsupport_mul_one_sub_logCutoffProfile_comp (χ := χ) hε h4
        hρ.continuousAt hpδ
      rw [fderiv_of_notMem_tsupport ℝ hp, fderiv_fderiv_of_notMem_tsupport hp]
      simpa [ContinuousLinearMap.opNorm_zero] using hR
  have := le_re_leviForm_add_mul_sub_apply_self hf hg hβ v
  have := mul_le_mul_of_nonneg_right hE (sq_nonneg ‖v‖)
  linarith

end TauCeti

end
