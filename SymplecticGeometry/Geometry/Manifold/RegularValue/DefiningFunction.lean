/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Defs
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import SymplecticGeometry.Analysis.Calculus.DefiningFunction
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Defining functions of a hypersurface near a regular point

Let `M` be a manifold without boundary modelled on a real Banach space, and let `f : M → ℝ` be
`C^(n+1)` at `x`, with `f x = 0` and `df_x ≠ 0`, so that `{f = 0}` is a hypersurface near `x`. A
function `g`, `C^(n+1)` at `x`, that vanishes near `x` wherever `f` does is `a * f` near `x` for
a function `a` that is `C^n` at `x`, and `dg_x = a x • df_x`. Hence two defining functions of
the same hypersurface near a regular point differ by a factor that does not vanish at the point,
and that is positive there when their differentials are positively proportional, as for two
defining functions of a cooriented hypersurface.

The proof reads `f` and `g` in the extended chart at `x` and applies the normed-space statement
`ContDiffOn.exists_contDiffAt_eventuallyEq_mul_of_eq_zero`.

## Main results

* `ContMDiffAt.exists_contMDiffAt_eventuallyEq_mul_of_eq_zero`: `g = a * f` near `x`, with `a`
  of class `C^n` at `x` and `dg_x = a x • df_x`.
* `ContMDiffAt.exists_contMDiffAt_eventuallyEq_mul_ne_zero`: for two defining functions, the
  factor does not vanish at `x`.
* `ContMDiffAt.exists_contMDiffAt_eventuallyEq_mul_of_mvfderiv_eq_smul`,
  `ContMDiffAt.exists_contMDiffAt_eventuallyEq_mul_pos`: when `dg_x = c • df_x`, the factor is `c`
  at `x`, so it is positive there when `c > 0`.

## References

* [K. Cieliebak, Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Chapter 2, on defining functions of hypersurfaces and their Levi forms.
-/

public section

open Filter
open scoped Topology Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {f g : M → ℝ} {x : M} {n : ℕ}

namespace ContMDiffAt

/-- **A function vanishing on a regular zero set is a multiple of the defining function.** On a
manifold without boundary modelled on a real Banach space, let `f` and `g` be `C^(n+1)` at `x`,
with `f x = 0`, `df_x ≠ 0`, and `g = 0` near `x` wherever `f = 0`. Then there is `a`, of class
`C^n` at `x`, with `g = a * f` near `x`; its value at `x` satisfies `dg_x = a x • df_x`. -/
theorem exists_contMDiffAt_eventuallyEq_mul_of_eq_zero (hf : ContMDiffAt I 𝓘(ℝ) (n + 1) f x)
    (hg : ContMDiffAt I 𝓘(ℝ) (n + 1) g x) (hfx : f x = 0) (hf' : mvfderiv I f x ≠ 0)
    (hfg : ∀ᶠ y in 𝓝 x, f y = 0 → g y = 0) :
    ∃ a : M → ℝ, ContMDiffAt I 𝓘(ℝ) n a x ∧ g =ᶠ[𝓝 x] a * f ∧
      mvfderiv I g x = a x • mvfderiv I f x := by
  have ht : (extChartAt I x).target ∈ 𝓝 (extChartAt I x x) := extChartAt_target_mem_nhds x
  have hsymm : Tendsto (extChartAt I x).symm (𝓝 (extChartAt I x x)) (𝓝 x) := by
    have := continuousAt_extChartAt_symm (I := I) x
    rwa [ContinuousAt, extChartAt_to_inv] at this
  -- `f` and `g` in the chart at `x`.
  have hfc := TauCeti.contMDiffAt_iff_contDiffAt_comp_extChartAt_symm.1 hf
  have hgc := TauCeti.contMDiffAt_iff_contDiffAt_comp_extChartAt_symm.1 hg
  have hnat : ((n + 1 : ℕ) : WithTop ℕ∞) ≠ ∞ := by simp
  -- An open set around the image of `x` on which both are `C^(n+1)`, and `g` vanishes where `f`
  -- does.
  have hgood : ∀ᶠ z in 𝓝 (extChartAt I x x), ContDiffAt ℝ (n + 1) (f ∘ (extChartAt I x).symm) z ∧
      ContDiffAt ℝ (n + 1) (g ∘ (extChartAt I x).symm) z ∧
      ((f ∘ (extChartAt I x).symm) z = 0 → (g ∘ (extChartAt I x).symm) z = 0) := by
    exact_mod_cast (hfc.eventually hnat).and ((hgc.eventually hnat).and (hsymm.eventually hfg))
  obtain ⟨s, hsgood, hs, hxs⟩ := mem_nhds_iff.1 hgood
  have hf'c : fderiv ℝ (f ∘ (extChartAt I x).symm) (extChartAt I x x) ≠ 0 := by
    rwa [← fderivWithin_of_mem_nhds ht,
      ← TauCeti.mvfderiv_eq_fderivWithin_extChartAt_target (hf.mdifferentiableAt (by simp))]
  have hfx' : (f ∘ (extChartAt I x).symm) (extChartAt I x x) = 0 := by
    rw [Function.comp_apply, extChartAt_to_inv, hfx]
  obtain ⟨b, hb, hgb, hdb⟩ := ContDiffOn.exists_contDiffAt_eventuallyEq_mul_of_eq_zero (n := n)
    hs hxs (fun z hz ↦ (hsgood hz).1.contDiffWithinAt) (fun z hz ↦ (hsgood hz).2.1.contDiffWithinAt)
    hfx' hf'c fun z hz ↦ (hsgood hz).2.2
  refine ⟨b ∘ extChartAt I x, ?_, ?_, ?_⟩
  · refine TauCeti.contMDiffAt_iff_contDiffAt_comp_extChartAt_symm.2 (hb.congr_of_eventuallyEq ?_)
    filter_upwards [ht] with z hz
    simp only [Function.comp_apply, (extChartAt I x).right_inv hz]
  · have hc : Tendsto (extChartAt I x) (𝓝 x) (𝓝 (extChartAt I x x)) := continuousAt_extChartAt x
    filter_upwards [extChartAt_source_mem_nhds (I := I) x, hc.eventually hgb] with y hy hgy
    simpa only [Pi.mul_apply, Function.comp_apply, (extChartAt I x).left_inv hy] using hgy
  · rw [TauCeti.mvfderiv_eq_fderivWithin_extChartAt_target (hg.mdifferentiableAt (by simp)),
      TauCeti.mvfderiv_eq_fderivWithin_extChartAt_target (hf.mdifferentiableAt (by simp)),
      fderivWithin_of_mem_nhds ht, fderivWithin_of_mem_nhds ht, hdb, Function.comp_apply]
    -- The two sides differ only in reading the tangent space `TangentSpace I x` as `E`.
    rfl

/-- **Two defining functions of a hypersurface differ by a nonvanishing factor.** On a manifold
without boundary modelled on a real Banach space, let `f` and `g` be `C^(n+1)` at `x`, with
`f x = 0`, `df_x ≠ 0`, `dg_x ≠ 0`, and `g = 0` near `x` wherever `f = 0`. Then `g = a * f` near
`x` for a function `a` that is `C^n` at `x` with `a x ≠ 0`. -/
theorem exists_contMDiffAt_eventuallyEq_mul_ne_zero (hf : ContMDiffAt I 𝓘(ℝ) (n + 1) f x)
    (hg : ContMDiffAt I 𝓘(ℝ) (n + 1) g x) (hfx : f x = 0) (hf' : mvfderiv I f x ≠ 0)
    (hg' : mvfderiv I g x ≠ 0) (hfg : ∀ᶠ y in 𝓝 x, f y = 0 → g y = 0) :
    ∃ a : M → ℝ, ContMDiffAt I 𝓘(ℝ) n a x ∧ g =ᶠ[𝓝 x] a * f ∧ a x ≠ 0 := by
  obtain ⟨a, ha, hga, hd⟩ := hf.exists_contMDiffAt_eventuallyEq_mul_of_eq_zero hg hfx hf' hfg
  refine ⟨a, ha, hga, fun h ↦ hg' ?_⟩
  rw [hd, h, zero_smul]

/-- **The factor between two defining functions at a point.** On a manifold without boundary
modelled on a real Banach space, let `f` and `g` be `C^(n+1)` at `x`, with `f x = 0`,
`df_x ≠ 0`, `dg_x = c • df_x`, and `g = 0` near `x` wherever `f = 0`. Then `g = a * f` near `x`
for a function `a` that is `C^n` at `x` with `a x = c`. -/
theorem exists_contMDiffAt_eventuallyEq_mul_of_mvfderiv_eq_smul
    (hf : ContMDiffAt I 𝓘(ℝ) (n + 1) f x) (hg : ContMDiffAt I 𝓘(ℝ) (n + 1) g x) (hfx : f x = 0)
    (hf' : mvfderiv I f x ≠ 0) {c : ℝ} (hgf : mvfderiv I g x = c • mvfderiv I f x)
    (hfg : ∀ᶠ y in 𝓝 x, f y = 0 → g y = 0) :
    ∃ a : M → ℝ, ContMDiffAt I 𝓘(ℝ) n a x ∧ g =ᶠ[𝓝 x] a * f ∧ a x = c := by
  obtain ⟨a, ha, hga, hd⟩ := hf.exists_contMDiffAt_eventuallyEq_mul_of_eq_zero hg hfx hf' hfg
  refine ⟨a, ha, hga, smul_left_injective ℝ hf' ?_⟩
  simp only [← hd, hgf]

/-- **Two defining functions of a cooriented hypersurface differ by a positive factor.** On a
manifold without boundary modelled on a real Banach space, let `f` and `g` be `C^(n+1)` at `x`,
with `f x = 0`, `df_x ≠ 0`, `dg_x = c • df_x` for some `c > 0`, and `g = 0` near `x` wherever
`f = 0`. Then `g = a * f` near `x` for a function `a` that is `C^n` at `x` with `a x > 0`. -/
theorem exists_contMDiffAt_eventuallyEq_mul_pos (hf : ContMDiffAt I 𝓘(ℝ) (n + 1) f x)
    (hg : ContMDiffAt I 𝓘(ℝ) (n + 1) g x) (hfx : f x = 0) (hf' : mvfderiv I f x ≠ 0) {c : ℝ}
    (hc : 0 < c) (hgf : mvfderiv I g x = c • mvfderiv I f x)
    (hfg : ∀ᶠ y in 𝓝 x, f y = 0 → g y = 0) :
    ∃ a : M → ℝ, ContMDiffAt I 𝓘(ℝ) n a x ∧ g =ᶠ[𝓝 x] a * f ∧ 0 < a x := by
  obtain ⟨a, ha, hga, hax⟩ :=
    hf.exists_contMDiffAt_eventuallyEq_mul_of_mvfderiv_eq_smul hg hfx hf' hgf hfg
  exact ⟨a, ha, hga, hax ▸ hc⟩

end ContMDiffAt

end
