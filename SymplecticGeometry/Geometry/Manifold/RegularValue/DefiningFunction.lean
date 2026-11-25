/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Defs
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import SymplecticGeometry.Analysis.Calculus.DefiningFunction
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Defining functions of a hypersurface near a regular point

Let `M` be a manifold without boundary modelled on a real Banach space, and let `f : M → ℝ`
vanish at `x` with `df_x ≠ 0`, so that `{f = 0}` is a hypersurface near `x`. A function `g` that
vanishes near `x` wherever `f` does is `a * f` near `x`, and `dg_x = a x • df_x`. If `f` and `g`
are `C^(n+1)` on an open set around `x`, with `n : ℕ∞` (so `n = ∞` is allowed), the factor `a` is
`C^n` at `x`; the same holds for `f` and `g` that are `C^(n+1)` at `x`, with `n : ℕ`. Hence two
defining functions of the same hypersurface near a regular point differ by a factor that does not
vanish at the point, and that is positive there when their differentials are positively
proportional, as for two defining functions of a cooriented hypersurface.

The proof reads `f` and `g` in the extended chart at `x` and applies the normed-space statement
`ContDiffOn.exists_contDiffAt_eventuallyEq_mul_of_eq_zero`; both forms go through
`ContDiffOn.exists_contMDiffAt_eventuallyEq_mul_of_comp_extChartAt_symm`, the statement in that
chart.

## Main results

* `ContMDiffOn.exists_contMDiffAt_eventuallyEq_mul_of_eq_zero`: for `f` and `g` that are
  `C^(n+1)` on an open set `s ∋ x`, `g = a * f` near `x`, with `a` of class `C^n` at `x` and
  `dg_x = a x • df_x`.
* `ContMDiffOn.exists_contMDiffAt_eventuallyEq_mul_ne_zero`: for two defining functions, the
  factor does not vanish at `x`.
* `ContMDiffOn.exists_contMDiffAt_eventuallyEq_mul_of_mvfderiv_eq_smul`,
  `ContMDiffOn.exists_contMDiffAt_eventuallyEq_mul_pos`: when `dg_x = c • df_x`, the factor is `c`
  at `x`, so it is positive there when `c > 0`.
* The same four statements in the namespace `ContMDiffAt`, for `f` and `g` that are `C^(n+1)` at
  `x`, with `n : ℕ`.

## References

* [K. Cieliebak, Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Chapter 2, on defining functions of hypersurfaces and their Levi forms.
-/

public section

open Set Filter
open scoped Topology Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {f g : M → ℝ} {x : M}

/-- **The factorization read in the chart at `x`.** On a manifold without boundary modelled on a
real Banach space, let `f` and `g`, read in the extended chart at `x`, be `C^(n+1)` on an open set
`t` containing the image of `x`, with `f x = 0`, `df_x ≠ 0`, and `g = 0` at every point of `t`
where `f = 0`. Then there is `a`, of class `C^n` at `x`, with `g = a * f` near `x`; its value at
`x` satisfies `dg_x = a x • df_x`. -/
theorem ContDiffOn.exists_contMDiffAt_eventuallyEq_mul_of_comp_extChartAt_symm {n : ℕ∞}
    {t : Set E} (ht : IsOpen t) (hxt : extChartAt I x x ∈ t)
    (hf : ContDiffOn ℝ (n + 1) (f ∘ (extChartAt I x).symm) t)
    (hg : ContDiffOn ℝ (n + 1) (g ∘ (extChartAt I x).symm) t) (hfx : f x = 0)
    (hf' : mvfderiv I f x ≠ 0)
    (hfg : ∀ z ∈ t, f ((extChartAt I x).symm z) = 0 → g ((extChartAt I x).symm z) = 0) :
    ∃ a : M → ℝ, ContMDiffAt I 𝓘(ℝ) n a x ∧ g =ᶠ[𝓝 x] a * f ∧
      mvfderiv I g x = a x • mvfderiv I f x := by
  have htar : (extChartAt I x).target ∈ 𝓝 (extChartAt I x x) := extChartAt_target_mem_nhds x
  have hfd : MDifferentiableAt I 𝓘(ℝ) f x :=
    (TauCeti.contMDiffAt_iff_contDiffAt_comp_extChartAt_symm.2
      (hf.contDiffAt (ht.mem_nhds hxt))).mdifferentiableAt (by simp)
  have hgd : MDifferentiableAt I 𝓘(ℝ) g x :=
    (TauCeti.contMDiffAt_iff_contDiffAt_comp_extChartAt_symm.2
      (hg.contDiffAt (ht.mem_nhds hxt))).mdifferentiableAt (by simp)
  have hf'c : fderiv ℝ (f ∘ (extChartAt I x).symm) (extChartAt I x x) ≠ 0 := by
    rwa [← fderivWithin_of_mem_nhds htar,
      ← TauCeti.mvfderiv_eq_fderivWithin_extChartAt_target hfd]
  have hfx' : (f ∘ (extChartAt I x).symm) (extChartAt I x x) = 0 := by
    rw [Function.comp_apply, extChartAt_to_inv, hfx]
  obtain ⟨b, hb, hgb, hdb⟩ :=
    ContDiffOn.exists_contDiffAt_eventuallyEq_mul_of_eq_zero ht hxt hf hg hfx' hf'c hfg
  refine ⟨b ∘ extChartAt I x, ?_, ?_, ?_⟩
  · refine TauCeti.contMDiffAt_iff_contDiffAt_comp_extChartAt_symm.2
      (hb.congr_of_eventuallyEq ?_)
    filter_upwards [htar] with z hz
    simp only [Function.comp_apply, (extChartAt I x).right_inv hz]
  · have hc : Tendsto (extChartAt I x) (𝓝 x) (𝓝 (extChartAt I x x)) := continuousAt_extChartAt x
    filter_upwards [extChartAt_source_mem_nhds (I := I) x, hc.eventually hgb] with y hy hgy
    simpa only [Pi.mul_apply, Function.comp_apply, (extChartAt I x).left_inv hy] using hgy
  · rw [TauCeti.mvfderiv_eq_fderivWithin_extChartAt_target hgd,
      TauCeti.mvfderiv_eq_fderivWithin_extChartAt_target hfd,
      fderivWithin_of_mem_nhds htar, fderivWithin_of_mem_nhds htar, hdb, Function.comp_apply]
    -- The two sides differ only in reading the tangent space `TangentSpace I x` as `E`.
    rfl

namespace ContMDiffOn

variable {s : Set M} {n : ℕ∞} [IsManifold I (n + 1) M]

/-- **A function vanishing on a regular zero set is a multiple of the defining function.** On a
manifold without boundary modelled on a real Banach space, let `f` and `g` be `C^(n+1)` on an
open set `s` containing `x`, where `n : ℕ∞` may be `∞`, with `f x = 0`, `df_x ≠ 0`, and `g = 0`
at every point of `s` where `f = 0`. Then there is `a`, of class `C^n` at `x`, with `g = a * f`
near `x`; its value at `x` satisfies `dg_x = a x • df_x`. -/
theorem exists_contMDiffAt_eventuallyEq_mul_of_eq_zero (hs : IsOpen s) (hx : x ∈ s)
    (hf : ContMDiffOn I 𝓘(ℝ) (n + 1) f s) (hg : ContMDiffOn I 𝓘(ℝ) (n + 1) g s) (hfx : f x = 0)
    (hf' : mvfderiv I f x ≠ 0) (hfg : ∀ y ∈ s, f y = 0 → g y = 0) :
    ∃ a : M → ℝ, ContMDiffAt I 𝓘(ℝ) n a x ∧ g =ᶠ[𝓝 x] a * f ∧
      mvfderiv I g x = a x • mvfderiv I f x := by
  -- The part of the chart's target that the inverse chart maps into `s`.
  set t := (extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s
  have ht : IsOpen t :=
    (continuousOn_extChartAt_symm x).isOpen_inter_preimage (isOpen_extChartAt_target x) hs
  have hxt : extChartAt I x x ∈ t :=
    ⟨mem_extChartAt_target x, by rwa [mem_preimage, extChartAt_to_inv]⟩
  have hc {h : M → ℝ} (hh : ContMDiffOn I 𝓘(ℝ) (n + 1) h s) :
      ContDiffOn ℝ (n + 1) (h ∘ (extChartAt I x).symm) t :=
    contMDiffOn_iff_contDiffOn.1 (hh.comp' (contMDiffOn_extChartAt_symm x))
  exact (hc hf).exists_contMDiffAt_eventuallyEq_mul_of_comp_extChartAt_symm ht hxt (hc hg) hfx
    hf' fun z hz ↦ hfg _ hz.2

/-- **Two defining functions of a hypersurface differ by a nonvanishing factor.** On a manifold
without boundary modelled on a real Banach space, let `f` and `g` be `C^(n+1)` on an open set `s`
containing `x`, with `f x = 0`, `df_x ≠ 0`, `dg_x ≠ 0`, and `g = 0` at every point of `s` where
`f = 0`. Then `g = a * f` near `x` for a function `a` that is `C^n` at `x` with `a x ≠ 0`. -/
theorem exists_contMDiffAt_eventuallyEq_mul_ne_zero (hs : IsOpen s) (hx : x ∈ s)
    (hf : ContMDiffOn I 𝓘(ℝ) (n + 1) f s) (hg : ContMDiffOn I 𝓘(ℝ) (n + 1) g s) (hfx : f x = 0)
    (hf' : mvfderiv I f x ≠ 0) (hg' : mvfderiv I g x ≠ 0) (hfg : ∀ y ∈ s, f y = 0 → g y = 0) :
    ∃ a : M → ℝ, ContMDiffAt I 𝓘(ℝ) n a x ∧ g =ᶠ[𝓝 x] a * f ∧ a x ≠ 0 := by
  obtain ⟨a, ha, hga, hd⟩ := hf.exists_contMDiffAt_eventuallyEq_mul_of_eq_zero hs hx hg hfx hf' hfg
  exact ⟨a, ha, hga, fun h ↦ hg' (by rw [hd, h, zero_smul])⟩

/-- **The factor between two defining functions at a point.** On a manifold without boundary
modelled on a real Banach space, let `f` and `g` be `C^(n+1)` on an open set `s` containing `x`,
with `f x = 0`, `df_x ≠ 0`, `dg_x = c • df_x`, and `g = 0` at every point of `s` where `f = 0`.
Then `g = a * f` near `x` for a function `a` that is `C^n` at `x` with `a x = c`. -/
theorem exists_contMDiffAt_eventuallyEq_mul_of_mvfderiv_eq_smul (hs : IsOpen s) (hx : x ∈ s)
    (hf : ContMDiffOn I 𝓘(ℝ) (n + 1) f s) (hg : ContMDiffOn I 𝓘(ℝ) (n + 1) g s) (hfx : f x = 0)
    (hf' : mvfderiv I f x ≠ 0) {c : ℝ} (hgf : mvfderiv I g x = c • mvfderiv I f x)
    (hfg : ∀ y ∈ s, f y = 0 → g y = 0) :
    ∃ a : M → ℝ, ContMDiffAt I 𝓘(ℝ) n a x ∧ g =ᶠ[𝓝 x] a * f ∧ a x = c := by
  obtain ⟨a, ha, hga, hd⟩ := hf.exists_contMDiffAt_eventuallyEq_mul_of_eq_zero hs hx hg hfx hf' hfg
  exact ⟨a, ha, hga, smul_left_injective ℝ hf' (by simp only [← hd, hgf])⟩

/-- **Two defining functions of a cooriented hypersurface differ by a positive factor.** On a
manifold without boundary modelled on a real Banach space, let `f` and `g` be `C^(n+1)` on an
open set `s` containing `x`, with `f x = 0`, `df_x ≠ 0`, `dg_x = c • df_x` for some `c > 0`, and
`g = 0` at every point of `s` where `f = 0`. Then `g = a * f` near `x` for a function `a` that is
`C^n` at `x` with `a x > 0`. -/
theorem exists_contMDiffAt_eventuallyEq_mul_pos (hs : IsOpen s) (hx : x ∈ s)
    (hf : ContMDiffOn I 𝓘(ℝ) (n + 1) f s) (hg : ContMDiffOn I 𝓘(ℝ) (n + 1) g s) (hfx : f x = 0)
    (hf' : mvfderiv I f x ≠ 0) {c : ℝ} (hc : 0 < c) (hgf : mvfderiv I g x = c • mvfderiv I f x)
    (hfg : ∀ y ∈ s, f y = 0 → g y = 0) :
    ∃ a : M → ℝ, ContMDiffAt I 𝓘(ℝ) n a x ∧ g =ᶠ[𝓝 x] a * f ∧ 0 < a x := by
  obtain ⟨a, ha, hga, hax⟩ :=
    hf.exists_contMDiffAt_eventuallyEq_mul_of_mvfderiv_eq_smul hs hx hg hfx hf' hgf hfg
  exact ⟨a, ha, hga, hax ▸ hc⟩

end ContMDiffOn

namespace ContMDiffAt

variable {n : ℕ}

/-- **A function vanishing on a regular zero set is a multiple of the defining function.** On a
manifold without boundary modelled on a real Banach space, let `f` and `g` be `C^(n+1)` at `x`,
with `f x = 0`, `df_x ≠ 0`, and `g = 0` near `x` wherever `f = 0`. Then there is `a`, of class
`C^n` at `x`, with `g = a * f` near `x`; its value at `x` satisfies `dg_x = a x • df_x`. -/
theorem exists_contMDiffAt_eventuallyEq_mul_of_eq_zero (hf : ContMDiffAt I 𝓘(ℝ) (n + 1) f x)
    (hg : ContMDiffAt I 𝓘(ℝ) (n + 1) g x) (hfx : f x = 0) (hf' : mvfderiv I f x ≠ 0)
    (hfg : ∀ᶠ y in 𝓝 x, f y = 0 → g y = 0) :
    ∃ a : M → ℝ, ContMDiffAt I 𝓘(ℝ) n a x ∧ g =ᶠ[𝓝 x] a * f ∧
      mvfderiv I g x = a x • mvfderiv I f x := by
  have hsymm : Tendsto (extChartAt I x).symm (𝓝 (extChartAt I x x)) (𝓝 x) := by
    have := continuousAt_extChartAt_symm (I := I) x
    rwa [ContinuousAt, extChartAt_to_inv] at this
  have hfc := TauCeti.contMDiffAt_iff_contDiffAt_comp_extChartAt_symm.1 hf
  have hgc := TauCeti.contMDiffAt_iff_contDiffAt_comp_extChartAt_symm.1 hg
  have hnat : ((n + 1 : ℕ) : WithTop ℕ∞) ≠ ∞ := by simp
  -- An open set around the image of `x` on which `f` and `g`, read in the chart, are `C^(n+1)`,
  -- and `g` vanishes where `f` does.
  have hgood : ∀ᶠ z in 𝓝 (extChartAt I x x), ContDiffAt ℝ (n + 1) (f ∘ (extChartAt I x).symm) z ∧
      ContDiffAt ℝ (n + 1) (g ∘ (extChartAt I x).symm) z ∧
      ((f ∘ (extChartAt I x).symm) z = 0 → (g ∘ (extChartAt I x).symm) z = 0) := by
    exact_mod_cast (hfc.eventually hnat).and ((hgc.eventually hnat).and (hsymm.eventually hfg))
  obtain ⟨t, htgood, ht, hxt⟩ := mem_nhds_iff.1 hgood
  exact ContDiffOn.exists_contMDiffAt_eventuallyEq_mul_of_comp_extChartAt_symm (n := n) ht hxt
    (fun z hz ↦ (htgood hz).1.contDiffWithinAt) (fun z hz ↦ (htgood hz).2.1.contDiffWithinAt) hfx
    hf' fun z hz ↦ (htgood hz).2.2

/-- **Two defining functions of a hypersurface differ by a nonvanishing factor.** On a manifold
without boundary modelled on a real Banach space, let `f` and `g` be `C^(n+1)` at `x`, with
`f x = 0`, `df_x ≠ 0`, `dg_x ≠ 0`, and `g = 0` near `x` wherever `f = 0`. Then `g = a * f` near
`x` for a function `a` that is `C^n` at `x` with `a x ≠ 0`. -/
theorem exists_contMDiffAt_eventuallyEq_mul_ne_zero (hf : ContMDiffAt I 𝓘(ℝ) (n + 1) f x)
    (hg : ContMDiffAt I 𝓘(ℝ) (n + 1) g x) (hfx : f x = 0) (hf' : mvfderiv I f x ≠ 0)
    (hg' : mvfderiv I g x ≠ 0) (hfg : ∀ᶠ y in 𝓝 x, f y = 0 → g y = 0) :
    ∃ a : M → ℝ, ContMDiffAt I 𝓘(ℝ) n a x ∧ g =ᶠ[𝓝 x] a * f ∧ a x ≠ 0 := by
  obtain ⟨a, ha, hga, hd⟩ := hf.exists_contMDiffAt_eventuallyEq_mul_of_eq_zero hg hfx hf' hfg
  exact ⟨a, ha, hga, fun h ↦ hg' (by rw [hd, h, zero_smul])⟩

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
  exact ⟨a, ha, hga, smul_left_injective ℝ hf' (by simp only [← hd, hgf])⟩

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
