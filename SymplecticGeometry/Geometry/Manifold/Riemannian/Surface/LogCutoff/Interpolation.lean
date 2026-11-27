/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Real.Sqrt
public import TauCeti.Geometry.Manifold.Riemannian.Surface.LogCutoff.Profile
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.Module
import SymplecticGeometry.Analysis.Calculus.FDeriv.Mul
import SymplecticGeometry.Geometry.Manifold.Riemannian.Surface.LogCutoff.Comp
import TauCeti.Analysis.Calculus.SecondDerivative

/-!
# Interpolation with a logarithmic cutoff

Let `F` be a real normed space, `ρ χ : F → ℝ`, and for `0 < 4ε ≤ δ` let
`β = χ (1 - ψ ∘ ρ)` with `ψ = TauCeti.logCutoffProfile ε δ` and `Λ = log (δ / ε)`. Here `ρ`
behaves like a squared distance at `p`, `‖Dρ(p)‖ ≤ A √(ρ p)` and `‖D²ρ(p)‖ ≤ A`, and the factor
`χ`, with `|χ p| ≤ 1`, has first and second derivatives at most `B` at `p`. For two functions
`f g : F → ℝ` whose 1-jets nearly agree at `p`, `|g p - f p| ≤ A ρ p` and
`‖D(g - f)(p)‖ ≤ A √(ρ p)`, this file bounds at `p` the error terms of the interpolation
`θ = f + β (g - f)`:

* `TauCeti.mul_one_sub_logCutoffProfile_comp_mem_Icc`: for `0 ≤ χ p ≤ 1`, the value `β p` lies in
  `[0, 1]`;
* `TauCeti.norm_fderiv_mul_one_sub_logCutoffProfile_comp_le` and
  `TauCeti.norm_fderiv_fderiv_mul_one_sub_logCutoffProfile_comp_le`: the first and second
  derivatives of `β`, by the product rules `SymplecticGeometry.norm_fderiv_mul_le` and
  `SymplecticGeometry.norm_fderiv_fderiv_mul_le`;
* `TauCeti.norm_fderiv_add_logCutoff_mul_sub_sub_le`: the differential of `θ` at `p` is
  `(1 - β p) Df(p) + β p Dg(p)` up to `(g p - f p) • Dβ(p)`, of norm at most
  `logCutoffConst A² √δ / Λ + A B δ`;
* `TauCeti.sub_le_norm_fderiv_add_logCutoff_mul_sub`: so, for `0 ≤ χ p ≤ 1`, a lower bound
  `m ≤ ‖Df(p)‖` gives `m - (A √δ + logCutoffConst A² √δ / Λ + A B δ) ≤ ‖Dθ(p)‖`;
* `TauCeti.exists_abs_mul_norm_fderiv_fderiv_logCutoff_add_le`: for `δ ≤ 1`, the quantity
  `|g p - f p| ‖D²β(p)‖ + ‖Dβ(p)‖ ‖D(g - f)(p)‖`, the error of the Levi form of `θ` in
  `TauCeti.le_re_leviForm_add_mul_sub_apply_self`, is at most
  `K (A² + A³ + A² B + A B) (1 / Λ + √δ)` for an absolute constant `K`.

Where `ρ p > δ` the cutoff vanishes near `p` and there is no error
(`TauCeti.notMem_tsupport_mul_one_sub_logCutoffProfile_comp`). Where `ρ p ≤ δ`, the bounds
`TauCeti.sqrt_mul_norm_fderiv_logCutoffProfile_comp_le` and
`TauCeti.exists_mul_norm_fderiv_fderiv_logCutoffProfile_comp_le` on the derivatives of `ψ ∘ ρ`
make the factors `√(ρ p)` and `ρ p` cancel their singular parts. The terms with `Dχ` and `D²χ`
are where `δ ≤ 1` is used: `|g p - f p| ‖D²χ(p)‖` is only at most `A B δ`, which is at most
`A B √δ` once `δ ≤ 1`.

The library uses these bounds to interpolate between two strictly plurisubharmonic functions along
a totally real submanifold, for Proposition 3.26 of [CieliebakEliashberg2012], following the
logarithmic cutoff route of its design.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012]
-/

public section

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f g ρ χ : F → ℝ} {p : F}
  {ε δ A B : ℝ}

omit [NormedSpace ℝ F] in
/-- Near a point where `ρ > δ`, the cutoff `χ * (1 - logCutoffProfile ε δ ∘ ρ)` vanishes. -/
theorem notMem_tsupport_mul_one_sub_logCutoffProfile_comp (hε : 0 < ε) (hεδ : 2 * ε ≤ δ)
    (hρ : ContinuousAt ρ p) (hp : δ < ρ p) :
    p ∉ tsupport (χ * (1 - logCutoffProfile ε δ ∘ ρ)) := by
  refine notMem_tsupport_iff_eventuallyEq.2 ?_
  filter_upwards [continuousAt_const.eventually_lt hρ hp] with x hx
  simp [logCutoffProfile_eq_one_of_ge hε (by linarith) hx.le]

/-- For `0 < 2ε ≤ δ`, the defect `1 - logCutoffProfile ε δ r` lies in `[-1, 1]`. -/
theorem abs_one_sub_logCutoffProfile_le (hε : 0 < ε) (hεδ : 2 * ε ≤ δ) (r : ℝ) :
    |1 - logCutoffProfile ε δ r| ≤ 1 := by
  have h0 := logCutoffProfile_nonneg hε hεδ r
  have h1 := logCutoffProfile_le_one hε hεδ r
  exact abs_le.2 ⟨by linarith, by linarith⟩

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
/-- For `0 < 2ε ≤ δ` and `0 ≤ χ p ≤ 1`, the cutoff `χ * (1 - logCutoffProfile ε δ ∘ ρ)` takes a
value in `[0, 1]` at `p`. -/
theorem mul_one_sub_logCutoffProfile_comp_mem_Icc (hε : 0 < ε) (hεδ : 2 * ε ≤ δ) (hχ0 : 0 ≤ χ p)
    (hχ1 : χ p ≤ 1) : (χ * (1 - logCutoffProfile ε δ ∘ ρ)) p ∈ Set.Icc 0 1 := by
  have h0 := logCutoffProfile_nonneg hε hεδ (ρ p)
  have h1 := logCutoffProfile_le_one hε hεδ (ρ p)
  simp only [Pi.mul_apply, Pi.sub_apply, Pi.one_apply, Function.comp_apply, Set.mem_Icc]
  exact ⟨mul_nonneg hχ0 (by linarith), by nlinarith⟩

/-- **The first derivative of a logarithmic cutoff times a function.** For `0 < 2ε ≤ δ`, `ρ`
and `χ` differentiable at `p`, `|χ p| ≤ 1` and `‖Dχ(p)‖ ≤ B`, the derivative of
`χ * (1 - logCutoffProfile ε δ ∘ ρ)` at `p` has norm at most
`‖D(logCutoffProfile ε δ ∘ ρ)(p)‖ + B`. -/
theorem norm_fderiv_mul_one_sub_logCutoffProfile_comp_le (hε : 0 < ε) (hεδ : 2 * ε ≤ δ)
    (hρ : DifferentiableAt ℝ ρ p) (hχ : DifferentiableAt ℝ χ p) (hχ1 : |χ p| ≤ 1)
    (hB : ‖fderiv ℝ χ p‖ ≤ B) :
    ‖fderiv ℝ (χ * (1 - logCutoffProfile ε δ ∘ ρ)) p‖ ≤
      ‖fderiv ℝ (logCutoffProfile ε δ ∘ ρ) p‖ + B := by
  have hh : DifferentiableAt ℝ (logCutoffProfile ε δ ∘ ρ) p :=
    ((contDiff_logCutoffProfile (by linarith)).differentiable (by simp) _).comp p hρ
  -- `fderiv_const_sub` is stated for `fun y ↦ 1 - h y`, which unfolds `1 - h`.
  have hD : fderiv ℝ (1 - logCutoffProfile ε δ ∘ ρ) p = -fderiv ℝ (logCutoffProfile ε δ ∘ ρ) p :=
    fderiv_const_sub (1 : ℝ)
  have hu : DifferentiableAt ℝ (1 - logCutoffProfile ε δ ∘ ρ) p := (differentiableAt_const _).sub hh
  refine (SymplecticGeometry.norm_fderiv_mul_le hχ hu).trans ?_
  rw [hD, norm_neg, Real.norm_eq_abs, Real.norm_eq_abs]
  have := norm_nonneg (fderiv ℝ (logCutoffProfile ε δ ∘ ρ) p)
  have := norm_nonneg (fderiv ℝ χ p)
  have : |(1 - logCutoffProfile ε δ ∘ ρ) p| ≤ 1 := by
    simpa only [Pi.sub_apply, Pi.one_apply, Function.comp_apply] using
      abs_one_sub_logCutoffProfile_le (δ := δ) hε (by linarith) (ρ p)
  calc _ ≤ 1 * ‖fderiv ℝ (logCutoffProfile ε δ ∘ ρ) p‖ + 1 * ‖fderiv ℝ χ p‖ := by
        gcongr
    _ ≤ _ := by linarith

/-- **The second derivative of a logarithmic cutoff times a function.** For `0 < 2ε ≤ δ`, `ρ`
and `χ` of class `C²` at `p`, `|χ p| ≤ 1`, `‖Dχ(p)‖ ≤ B` and `‖D²χ(p)‖ ≤ B`, the second
derivative of `χ * (1 - logCutoffProfile ε δ ∘ ρ)` at `p` has norm at most
`‖D²(logCutoffProfile ε δ ∘ ρ)(p)‖ + B + 2 B ‖D(logCutoffProfile ε δ ∘ ρ)(p)‖`. -/
theorem norm_fderiv_fderiv_mul_one_sub_logCutoffProfile_comp_le (hε : 0 < ε)
    (hεδ : 2 * ε ≤ δ) (hρ : ContDiffAt ℝ 2 ρ p) (hχ : ContDiffAt ℝ 2 χ p) (hχ1 : |χ p| ≤ 1)
    (hB : ‖fderiv ℝ χ p‖ ≤ B) (hB' : ‖fderiv ℝ (fderiv ℝ χ) p‖ ≤ B) :
    ‖fderiv ℝ (fderiv ℝ (χ * (1 - logCutoffProfile ε δ ∘ ρ))) p‖ ≤
      ‖fderiv ℝ (fderiv ℝ (logCutoffProfile ε δ ∘ ρ)) p‖ + B +
        2 * (B * ‖fderiv ℝ (logCutoffProfile ε δ ∘ ρ) p‖) := by
  have hh : ContDiffAt ℝ 2 (logCutoffProfile ε δ ∘ ρ) p :=
    ((contDiff_logCutoffProfile (by linarith)).contDiffAt.of_le (by simp)).comp p hρ
  -- `fderiv_const_sub` is stated for `fun y ↦ 1 - h y`, which unfolds `1 - h`.
  have hD : fderiv ℝ (1 - logCutoffProfile ε δ ∘ ρ) = -fderiv ℝ (logCutoffProfile ε δ ∘ ρ) :=
    funext fun _ ↦ fderiv_const_sub (1 : ℝ)
  have hu : ContDiffAt ℝ 2 (1 - logCutoffProfile ε δ ∘ ρ) p := contDiffAt_const.sub hh
  refine (SymplecticGeometry.norm_fderiv_fderiv_mul_le hχ hu).trans ?_
  have hD2 : ‖fderiv ℝ (fderiv ℝ (1 - logCutoffProfile ε δ ∘ ρ)) p‖ =
      ‖fderiv ℝ (fderiv ℝ (logCutoffProfile ε δ ∘ ρ)) p‖ := by
    rw [hD, fderiv_neg]
    exact norm_neg (fderiv ℝ (fderiv ℝ (logCutoffProfile ε δ ∘ ρ)) p)
  rw [hD2, hD, Pi.neg_apply, norm_neg, Real.norm_eq_abs, Real.norm_eq_abs]
  have := norm_nonneg (fderiv ℝ (logCutoffProfile ε δ ∘ ρ) p)
  have := norm_nonneg (fderiv ℝ (fderiv ℝ (logCutoffProfile ε δ ∘ ρ)) p)
  have := norm_nonneg (fderiv ℝ (fderiv ℝ χ) p)
  have : |(1 - logCutoffProfile ε δ ∘ ρ) p| ≤ 1 := by
    simpa only [Pi.sub_apply, Pi.one_apply, Function.comp_apply] using
      abs_one_sub_logCutoffProfile_le (δ := δ) hε (by linarith) (ρ p)
  calc _ ≤ 1 * ‖fderiv ℝ (fderiv ℝ (logCutoffProfile ε δ ∘ ρ)) p‖ +
        1 * ‖fderiv ℝ (fderiv ℝ χ) p‖ +
          2 * (B * ‖fderiv ℝ (logCutoffProfile ε δ ∘ ρ) p‖) := by
        gcongr
    _ ≤ _ := by linarith

/-- **The differential of an interpolation with a logarithmic cutoff.** Let `0 < 4ε ≤ δ`, let
`f`, `g`, `ρ` and `χ` be differentiable at `p`, with `|χ p| ≤ 1`, `‖Dχ(p)‖ ≤ B`, `0 ≤ ρ p`,
`0 ≤ A`, `‖Dρ(p)‖ ≤ A √(ρ p)`, and `|g p - f p| ≤ A ρ p`. For the cutoff
`β = χ (1 - logCutoffProfile ε δ ∘ ρ)`, the differential of `θ = f + β (g - f)` at `p` differs
from the convex combination `(1 - β p) Df(p) + β p Dg(p)` by at most
`logCutoffConst A² √δ / log (δ / ε) + A B δ`. -/
theorem norm_fderiv_add_logCutoff_mul_sub_sub_le (hε : 0 < ε) (h4 : 4 * ε ≤ δ)
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) (hρ : DifferentiableAt ℝ ρ p)
    (hχ : DifferentiableAt ℝ χ p) (hχ1 : |χ p| ≤ 1) (hB : ‖fderiv ℝ χ p‖ ≤ B)
    (hρ0 : 0 ≤ ρ p) (hA0 : 0 ≤ A) (hDρ : ‖fderiv ℝ ρ p‖ ≤ A * √(ρ p))
    (hD : |g p - f p| ≤ A * ρ p) :
    ‖fderiv ℝ (f + χ * (1 - logCutoffProfile ε δ ∘ ρ) * (g - f)) p -
        ((1 - (χ * (1 - logCutoffProfile ε δ ∘ ρ)) p) • fderiv ℝ f p +
          (χ * (1 - logCutoffProfile ε δ ∘ ρ)) p • fderiv ℝ g p)‖ ≤
      logCutoffConst * A ^ 2 * √δ / Real.log (δ / ε) + A * B * δ := by
  set β := χ * (1 - logCutoffProfile ε δ ∘ ρ)
  have hεδ : 2 * ε ≤ δ := by linarith
  have hβ : DifferentiableAt ℝ β p := hχ.mul ((differentiableAt_const _).sub
    (((contDiff_logCutoffProfile (by linarith)).differentiable (by simp) _).comp p hρ))
  have hΛ : 0 < Real.log (δ / ε) := Real.log_pos ((one_lt_div hε).2 (by linarith))
  have hB0 : 0 ≤ B := (norm_nonneg (fderiv ℝ χ p)).trans hB
  have heq : fderiv ℝ (f + β * (g - f)) p - ((1 - β p) • fderiv ℝ f p + β p • fderiv ℝ g p) =
      (g p - f p) • fderiv ℝ β p := by
    rw [fderiv_add hf (hβ.mul (hg.sub hf)), fderiv_mul hβ (hg.sub hf), fderiv_sub hg hf,
      Pi.sub_apply]
    module
  rw [heq, norm_smul, Real.norm_eq_abs]
  rcases le_or_gt (ρ p) δ with hpδ | hpδ
  · have h1 := sqrt_mul_norm_fderiv_logCutoffProfile_comp_le hε h4 hρ hA0 hDρ
    have h2 := norm_fderiv_mul_one_sub_logCutoffProfile_comp_le hε hεδ hρ hχ hχ1 hB
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
  · rw [fderiv_of_notMem_tsupport ℝ (notMem_tsupport_mul_one_sub_logCutoffProfile_comp hε
      hεδ hρ.continuousAt hpδ), norm_zero, mul_zero]
    have := logCutoffConst_pos
    have : 0 ≤ δ := by linarith
    positivity

/-- **A lower bound on the differential of an interpolation with a logarithmic cutoff.** Under
the hypotheses of `TauCeti.norm_fderiv_add_logCutoff_mul_sub_sub_le`, with `0 ≤ χ p ≤ 1` and
`‖D(g - f)(p)‖ ≤ A √(ρ p)`, if `m ≤ ‖Df(p)‖` then the differential of `θ = f + β (g - f)` at `p`,
for `β = χ (1 - logCutoffProfile ε δ ∘ ρ)`, has norm at least
`m - (A √δ + logCutoffConst A² √δ / log (δ / ε) + A B δ)`. -/
theorem sub_le_norm_fderiv_add_logCutoff_mul_sub {m : ℝ} (hε : 0 < ε) (h4 : 4 * ε ≤ δ)
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) (hρ : DifferentiableAt ℝ ρ p)
    (hχ : DifferentiableAt ℝ χ p) (hχ0 : 0 ≤ χ p) (hχ1 : χ p ≤ 1) (hB : ‖fderiv ℝ χ p‖ ≤ B)
    (hρ0 : 0 ≤ ρ p) (hA0 : 0 ≤ A) (hDρ : ‖fderiv ℝ ρ p‖ ≤ A * √(ρ p))
    (hD : |g p - f p| ≤ A * ρ p) (hDD : ‖fderiv ℝ (g - f) p‖ ≤ A * √(ρ p))
    (hm : m ≤ ‖fderiv ℝ f p‖) :
    m - (A * √δ + (logCutoffConst * A ^ 2 * √δ / Real.log (δ / ε) + A * B * δ)) ≤
      ‖fderiv ℝ (f + χ * (1 - logCutoffProfile ε δ ∘ ρ) * (g - f)) p‖ := by
  have hεδ : 2 * ε ≤ δ := by linarith
  have hE := norm_fderiv_add_logCutoff_mul_sub_sub_le hε h4 hf hg hρ hχ (by
    rw [abs_le]; constructor <;> linarith) hB hρ0 hA0 hDρ hD
  obtain ⟨hb0, hb1⟩ := mul_one_sub_logCutoffProfile_comp_mem_Icc (ρ := ρ) hε hεδ hχ0 hχ1
  set b := (χ * (1 - logCutoffProfile ε δ ∘ ρ)) p with hb
  set Dθ := fderiv ℝ (f + χ * (1 - logCutoffProfile ε δ ∘ ρ) * (g - f)) p
  -- Where `β p ≠ 0`, `ρ p < δ`, so `β p ‖D(g - f)(p)‖ ≤ A √δ`.
  have hbD : ‖b • (fderiv ℝ g p - fderiv ℝ f p)‖ ≤ A * √δ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hb0, ← fderiv_sub hg hf]
    rcases le_or_gt δ (ρ p) with hδρ | hρδ
    · have : b = 0 := by
        simp [hb, logCutoffProfile_eq_one_of_ge hε hεδ hδρ]
      rw [this, zero_mul]
      positivity
    · calc b * ‖fderiv ℝ (g - f) p‖ ≤ 1 * (A * √(ρ p)) := by gcongr
        _ ≤ A * √δ := by rw [one_mul]; gcongr
  have hf' : ‖fderiv ℝ f p‖ ≤ ‖(1 - b) • fderiv ℝ f p + b • fderiv ℝ g p‖ +
      ‖b • (fderiv ℝ g p - fderiv ℝ f p)‖ := by
    calc ‖fderiv ℝ f p‖ = ‖(1 - b) • fderiv ℝ f p + b • fderiv ℝ g p -
          b • (fderiv ℝ g p - fderiv ℝ f p)‖ := by congr 1; module
      _ ≤ _ := norm_sub_le _ _
  have := norm_le_norm_add_norm_sub Dθ ((1 - b) • fderiv ℝ f p + b • fderiv ℝ g p)
  linarith

/-- **The error terms of an interpolation with a logarithmic cutoff.** There is an absolute
constant `K` with the following property. Let `F` be a real normed space, `0 < 4ε ≤ δ ≤ 1`, and
let `ρ` and `χ` be real functions of class `C²` at `p`, with `|χ p| ≤ 1`, `‖Dχ(p)‖ ≤ B`,
`‖D²χ(p)‖ ≤ B`, `0 ≤ ρ p`, `‖Dρ(p)‖ ≤ A √(ρ p)` and `‖D²ρ(p)‖ ≤ A`, and let `u` be a real
function with `|u p| ≤ A ρ p` and `‖Du(p)‖ ≤ A √(ρ p)`. For the cutoff
`β = χ (1 - logCutoffProfile ε δ ∘ ρ)`,
`|u p| ‖D²β(p)‖ + ‖Dβ(p)‖ ‖Du(p)‖ ≤ K (A² + A³ + A² B + A B) (1 / log (δ / ε) + √δ)`. -/
theorem exists_abs_mul_norm_fderiv_fderiv_logCutoff_add_le :
    ∃ K : ℝ, ∀ {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {u ρ χ : F → ℝ} {p : F}
      {ε δ A B : ℝ}, 0 < ε → 4 * ε ≤ δ → δ ≤ 1 → ContDiffAt ℝ 2 ρ p → ContDiffAt ℝ 2 χ p →
      |χ p| ≤ 1 → ‖fderiv ℝ χ p‖ ≤ B → ‖fderiv ℝ (fderiv ℝ χ) p‖ ≤ B → 0 ≤ ρ p →
      ‖fderiv ℝ ρ p‖ ≤ A * √(ρ p) → ‖fderiv ℝ (fderiv ℝ ρ) p‖ ≤ A → |u p| ≤ A * ρ p →
      ‖fderiv ℝ u p‖ ≤ A * √(ρ p) →
      |u p| * ‖fderiv ℝ (fderiv ℝ (χ * (1 - logCutoffProfile ε δ ∘ ρ))) p‖ +
          ‖fderiv ℝ (χ * (1 - logCutoffProfile ε δ ∘ ρ)) p‖ * ‖fderiv ℝ u p‖ ≤
        K * (A ^ 2 + A ^ 3 + A ^ 2 * B + A * B) * (1 / Real.log (δ / ε) + √δ) := by
  obtain ⟨c, hc⟩ := exists_mul_norm_fderiv_fderiv_logCutoffProfile_comp_le
  refine ⟨|c| + 2 * logCutoffConst + 2, fun {F} _ _ {u ρ χ p ε δ A B} hε h4 hδ1 hρ hχ hχ1 hB
    hB' hρ0 hDρ hD2ρ hu hDu ↦ ?_⟩
  set β := χ * (1 - logCutoffProfile ε δ ∘ ρ)
  set K := |c| + 2 * logCutoffConst + 2
  set P := A ^ 2 + A ^ 3 + A ^ 2 * B + A * B
  have hεδ : 2 * ε ≤ δ := by linarith
  set Λ := Real.log (δ / ε)
  have hΛ : 0 < Λ := Real.log_pos ((one_lt_div hε).2 (by linarith))
  have hA0 : 0 ≤ A := (norm_nonneg (fderiv ℝ (fderiv ℝ ρ) p)).trans hD2ρ
  have hB0 : 0 ≤ B := (norm_nonneg (fderiv ℝ χ p)).trans hB
  have hc₀ := logCutoffConst_pos
  have hP : 0 ≤ P := by positivity
  rcases le_or_gt (ρ p) δ with hpδ | hpδ
  swap
  · have hp := notMem_tsupport_mul_one_sub_logCutoffProfile_comp (χ := χ) hε hεδ
      hρ.continuousAt hpδ
    rw [fderiv_of_notMem_tsupport ℝ hp, fderiv_fderiv_of_notMem_tsupport hp]
    simpa [ContinuousLinearMap.opNorm_zero] using by positivity
  have h1 := sqrt_mul_norm_fderiv_logCutoffProfile_comp_le hε h4
    (hρ.differentiableAt (by simp)) hA0 hDρ
  have h2 := hc hε h4 hρ hDρ hD2ρ
  have hDβ := norm_fderiv_mul_one_sub_logCutoffProfile_comp_le hε hεδ
    (hρ.differentiableAt (by simp)) (hχ.differentiableAt (by simp)) hχ1 hB
  have hD2β := norm_fderiv_fderiv_mul_one_sub_logCutoffProfile_comp_le hε hεδ hρ hχ hχ1
    hB hB'
  set s := √(ρ p)
  set a₁ := ‖fderiv ℝ (logCutoffProfile ε δ ∘ ρ) p‖
  set a₂ := ‖fderiv ℝ (fderiv ℝ (logCutoffProfile ε δ ∘ ρ)) p‖
  have hρs : ρ p = s * s := (Real.mul_self_sqrt hρ0).symm
  have hsδ : s ≤ √δ := Real.sqrt_le_sqrt hpδ
  have hsqδ1 : √δ ≤ 1 := Real.sqrt_le_one.mpr hδ1
  have hs1 : s ≤ 1 := hsδ.trans hsqδ1
  have hρδ : ρ p ≤ √δ :=
    hpδ.trans (by nlinarith [Real.mul_self_sqrt (hρ0.trans hpδ), Real.sqrt_nonneg δ])
  -- The coefficients of `1 / Λ` and of `√δ` below are each at most `K * P`.
  have hnum : c * (A ^ 2 + A ^ 3) + 2 * logCutoffConst * (A ^ 2 * B) +
      logCutoffConst * A ^ 2 ≤ K * P := by
    have : c * (A ^ 2 + A ^ 3) ≤ |c| * (A ^ 2 + A ^ 3) :=
      mul_le_mul_of_nonneg_right (le_abs_self c) (by positivity)
    have := mul_nonneg (abs_nonneg c) (by positivity : 0 ≤ A ^ 2 * B + A * B)
    have := mul_nonneg hc₀.le (by positivity : 0 ≤ A ^ 3 + A * B)
    nlinarith
  have hAB : 2 * (A * B) ≤ K * P := by
    have := mul_nonneg (abs_nonneg c) hP
    have := mul_nonneg hc₀.le hP
    have : 0 ≤ A ^ 2 + A ^ 3 + A ^ 2 * B := by positivity
    nlinarith
  calc |u p| * ‖fderiv ℝ (fderiv ℝ β) p‖ + ‖fderiv ℝ β p‖ * ‖fderiv ℝ u p‖
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

end TauCeti

end
