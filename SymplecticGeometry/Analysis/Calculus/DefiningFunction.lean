/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import SymplecticGeometry.Analysis.Calculus.FiberRescale
import TauCeti.Analysis.Calculus.FDeriv.Smul
import TauCeti.Analysis.Calculus.ImplicitFunctionTheorem

/-!
# Functions vanishing on a regular zero set are multiples of its defining function

Let `f : E → ℝ` be `C^(n+1)` on an open set `s` of a real Banach space, with `f x = 0` and
`df_x ≠ 0`. A function `g`, `C^(n+1)` on `s`, that vanishes wherever `f` does on `s` is, near `x`,
the product `a * f` of `f` with a function `a` that is `C^n` at `x`; and `dg_x = a x • df_x`.
So two defining functions of the same hypersurface differ near a regular point by a factor, which
does not vanish at `x` when `dg_x ≠ 0`.

The proof straightens `f`: Tau Ceti's local normal form of a submersion
(`ContDiffOn.exists_openPartialHomeomorph_eqOn_fderiv_comp`) writes `f` as `df_x ∘ Θ` near `x` for
a `C^(n+1)` chart `Θ` of `E`, and the coordinates `E ≃ ℝ × ker df_x` of
`ContinuousLinearMap.implicitCoordEquiv` make `f` the first coordinate. In these coordinates `g`
vanishes on `ker df_x × {0}` (the normal variable written last), and the factor is the rescaling
`fiberRescale` of `g` in the normal variable. It is `C^n` at the zero section by Hadamard's lemma
with parameters (`contDiffAt_fiberRescale_zero`, in
`SymplecticGeometry/Analysis/Calculus/FiberRescale.lean`). The value `a x` is read off from the
derivative of `a * f` at a zero of `f`, by Tau Ceti's `HasFDerivAt.smul_of_eq_zero`, which
needs `a` only continuous at `x`.

## Main results

* `ContDiffOn.exists_contDiffAt_eventuallyEq_mul_of_eq_zero`: the factorization `g = a * f` near
  `x`, with `a` of class `C^n` at `x` and `dg_x = a x • df_x`.

## References

* [K. Cieliebak, Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Chapter 2, where defining functions of hypersurfaces are compared.
-/

public section


open Set Filter
open scoped Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **A function vanishing on a regular zero set is a multiple of the defining function.** Let `f`
and `g` be `C^(n+1)` on an open set `s` containing `x`, with `f x = 0`, `df_x ≠ 0`, and `g = 0`
at every point of `s` where `f = 0`. Then there is `a`, of class `C^n` at `x`, with `g = a * f`
near `x`; its value at `x` satisfies `dg_x = a x • df_x`. -/
theorem ContDiffOn.exists_contDiffAt_eventuallyEq_mul_of_eq_zero {n : ℕ∞} {f g : E → ℝ}
    {s : Set E} {x : E} (hs : IsOpen s) (hx : x ∈ s) (hf : ContDiffOn ℝ (n + 1) f s)
    (hg : ContDiffOn ℝ (n + 1) g s) (hfx : f x = 0) (hf' : fderiv ℝ f x ≠ 0)
    (hfg : ∀ y ∈ s, f y = 0 → g y = 0) :
    ∃ a : E → ℝ, ContDiffAt ℝ n a x ∧ g =ᶠ[𝓝 x] a * f ∧
      fderiv ℝ g x = a x • fderiv ℝ f x := by
  set L := fderiv ℝ f x
  obtain ⟨v, hv⟩ : ∃ v, L v ≠ 0 := by
    by_contra! h
    exact hf' (ContinuousLinearMap.ext h)
  -- `t ↦ t • (L v)⁻¹ • v` is a right inverse of `L`.
  have hright : Function.RightInverse (ContinuousLinearMap.toSpanSingleton ℝ ((L v)⁻¹ • v)) L :=
    fun t ↦ by simp [hv]
  have hsurj : L.range = ⊤ := LinearMap.range_eq_top.2 hright.surjective
  have hker : L.ker.ClosedComplemented := L.closedComplemented_ker_of_rightInverse _ hright
  have h1 : (1 : WithTop ℕ∞) ≤ n + 1 := le_add_self
  obtain ⟨Θ, hxΘ, hΘs, hΘ, hΘsymm, hfΘ⟩ :=
    hf.exists_openPartialHomeomorph_eqOn_fderiv_comp hs hx h1 hsurj hker
  -- The coordinates `J : E ≃ ℝ × ker L`, whose first component is `L`.
  set J := L.implicitCoordEquiv hsurj hker
  have hJ (z : E) : (J z).1 = L z := by simp [J]
  -- `g` read in the straightening coordinates, with the normal variable last.
  set U : Set (L.ker × ℝ) := (fun q ↦ J.symm (q.2, q.1)) ⁻¹' Θ.target
  have hU : IsOpen U :=
    Θ.open_target.preimage (J.symm.continuous.comp (continuous_snd.prodMk continuous_fst))
  set G : L.ker × ℝ → ℝ := fun q ↦ g (Θ.symm (J.symm (q.2, q.1)))
  have hGU : ContDiffOn ℝ (n + 1) G U := by
    refine (hg.comp hΘsymm fun z hz ↦ hΘs (Θ.map_target hz)).comp
      (J.symm.contDiff.comp (contDiff_snd.prodMk contDiff_fst)).contDiffOn fun q hq ↦ hq
  have hG0 : ∀ p, (p, (0 : ℝ)) ∈ U → G (p, 0) = 0 := fun p hp ↦ by
    have hsrc := Θ.map_target hp
    refine hfg _ (hΘs hsrc) ?_
    rw [hfΘ hsrc, Function.comp_apply, Θ.right_inv hp, ← hJ, J.apply_symm_apply]
  -- The factor is the rescaling of `G` in the normal variable.
  set q : E → (L.ker × ℝ) × ℝ := fun y ↦ (((J (Θ y)).2, 1), (J (Θ y)).1)
  set a : E → ℝ := fun y ↦ fiberRescale G (q y)
  have hc0 : (J (Θ x)).1 = 0 := by rw [hJ, ← Function.comp_apply (f := L), ← hfΘ hxΘ, hfx]
  have hUx : ((J (Θ x)).2, (0 : ℝ)) ∈ U := by
    simp only [U, mem_preimage, ← hc0, Prod.mk.eta, J.symm_apply_apply]
    exact Θ.map_source hxΘ
  have hΘx : ContDiffAt ℝ (n + 1) Θ x := hΘ.contDiffAt (Θ.open_source.mem_nhds hxΘ)
  have ha : ContDiffAt ℝ n a x := by
    have hk : ContDiffAt ℝ n (fiberRescale G) (q x) := by
      simpa only [q, hc0] using contDiffAt_fiberRescale_zero hU hGU hG0 (p := (_, 1)) hUx
    have hJΘ : ContDiffAt ℝ n (fun y ↦ J (Θ y)) x :=
      J.contDiff.contDiffAt.comp x (hΘx.of_le le_self_add)
    exact hk.comp x ((hJΘ.snd.prodMk contDiffAt_const).prodMk hJΘ.fst)
  have hfact : g =ᶠ[𝓝 x] a * f := by
    filter_upwards [Θ.open_source.mem_nhds hxΘ] with y hy
    have hfy : f y = (J (Θ y)).1 := by rw [hfΘ hy, Function.comp_apply, hJ]
    rw [Pi.mul_apply, hfy]
    by_cases ht : (J (Θ y)).1 = 0
    · rw [ht, mul_zero]
      exact hfg y (hΘs hy) (hfy.trans ht)
    · have hgy : g y = G ((J (Θ y)).2, (J (Θ y)).1) := by
        simp only [G, Prod.mk.eta, J.symm_apply_apply, Θ.left_inv hy]
      simp only [a, q, fiberRescale_of_ne_zero G (q := (((J (Θ y)).2, 1), (J (Θ y)).1)) ht,
        smul_eq_mul, mul_one]
      rw [hgy]
      field_simp
  refine ⟨a, ha, hfact, ?_⟩
  have hfd : HasFDerivAt f L x :=
    ((hf.contDiffAt (hs.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
  rw [hfact.fderiv_eq, mul_comm]
  exact (hfd.smul_of_eq_zero ha.continuousAt hfx).fderiv.trans (by ext; simp [mul_comm])

end
