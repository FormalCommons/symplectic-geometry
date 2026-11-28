/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import SymplecticGeometry.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.ContDiff.IsOpen
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.BumpFunction.DerivativeApproximation

/-!
# Smooth approximation in `Cⁿ` that keeps a function where it is already smooth

Let `f` be `Cⁿ` on a neighbourhood of a compact set `K` of a finite-dimensional real vector
space, and smooth on a neighbourhood of a compact set `C`. For every `ε > 0` there is a smooth
`g` whose derivatives of order at most `n` are within `ε` of those of `f` on `K`, and which
equals `f` near `C` (`ContDiffOn.exists_contDiff_norm_iteratedFDeriv_sub_lt`). The version for
real functions on an interval, with `iteratedDeriv`, is
`ContDiffOn.exists_contDiff_abs_iteratedDeriv_sub_lt`;
`ContDiffOn.exists_contDiff_abs_iteratedDeriv_sub_lt_of_contDiffAt` takes instead `Cⁿ` at each
point of the interval and an open set on which `f` is smooth.

The approximation itself is Tau Ceti's
`ContDiffOn.exists_contDiff_hasCompactSupport_tendstoUniformlyOn_iteratedFDeriv` (convolution
with shrinking bumps). It is glued to a smooth extension `f₀` of `f` from near `C` by a smooth
cutoff `χ` equal to `1` near `C` and supported where `f₀` agrees with `f` locally, giving
`g = h + χ • (f₀ - h)`. Since `χ • (f₀ - f)` vanishes near each point, near `K` the error
`g - f` equals `(1 - χ) • (h - f)`, whose derivatives the Leibniz rule bounds by a constant
times those of `h - f`.

## References

* L. C. Evans, *Partial Differential Equations*, Appendix C.4 (mollifiers).
-/

public section

open Filter Set
open scoped Topology ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Let `f` be `Cⁿ` on a neighbourhood `U` of a compact set `K` and smooth on a neighbourhood
`V` of a compact set `C`. For every `ε > 0` there is a smooth `g` whose derivatives of order
`k ≤ n` are within `ε` of those of `f` at every point of `K`, and which agrees with `f` on a
neighbourhood of `C`. -/
theorem ContDiffOn.exists_contDiff_norm_iteratedFDeriv_sub_lt {f : E → F} {n : ℕ}
    {K C U V : Set E} (hK : IsCompact K) (hU : U ∈ 𝓝ˢ K) (hf : ContDiffOn ℝ n f U)
    (hC : IsCompact C) (hV : V ∈ 𝓝ˢ C) (hfV : ContDiffOn ℝ ∞ f V) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E → F, ContDiff ℝ ∞ g ∧
      (∀ k ≤ n, ∀ x ∈ K, ‖iteratedFDeriv ℝ k g x - iteratedFDeriv ℝ k f x‖ < ε) ∧
      g =ᶠ[𝓝ˢ C] f := by
  -- `C^n` and smooth extensions of `f` from near `K` and from near `C`.
  obtain ⟨f₂, hf₂, hf₂K⟩ := hf.exists_contDiff_eventuallyEq_nhdsSet hK hU
  obtain ⟨f₀, hf₀, hf₀C⟩ := hfV.exists_contDiff_eventuallyEq_nhdsSet hC hV
  replace hf₂K : ∀ x ∈ K, f₂ =ᶠ[𝓝 x] f := eventually_nhdsSet_iff_forall.1 hf₂K
  replace hf₀C : ∀ x ∈ C, f₀ =ᶠ[𝓝 x] f := eventually_nhdsSet_iff_forall.1 hf₀C
  -- A cutoff equal to `1` near `C`, supported where `f₀` agrees with `f`.
  set W : Set E := {x | f₀ =ᶠ[𝓝 x] f}
  have hWo : IsOpen W := isOpen_setOfPred_eventually_nhds
  obtain ⟨χ, hχ, -, hχ1, -, hχW⟩ := hC.exists_contDiff_cutoff_eventuallyEq_one hWo hf₀C
  set φ : E → ℝ := fun x ↦ 1 - χ x
  have hφ : ContDiff ℝ ∞ φ := contDiff_const.sub hχ
  -- A bound on the derivatives of `φ` of order at most `n` on `K`.
  obtain ⟨A, hA0, hA⟩ := ContDiffOn.exists_nonneg_bound_iteratedFDeriv_of_isOpen
    (hφ.of_le (m := n) (by simp)).contDiffOn isOpen_univ hK (subset_univ K)
  set L : ℝ := 2 ^ n * (A + 1)
  -- A smooth approximation of `f₂` within `ε / L` in `C^n` on `K`.
  obtain ⟨h, Lh, -, -, hh, hlim⟩ :=
    hf₂.contDiffOn.exists_contDiff_hasCompactSupport_tendstoUniformlyOn_iteratedFDeriv
      isOpen_univ hK (subset_univ K)
  have hev : ∀ᶠ m in atTop, ∀ j ∈ Finset.range (n + 1), ∀ x ∈ K,
      ‖iteratedFDeriv ℝ j (h m) x - iteratedFDeriv ℝ j f₂ x‖ < ε / L := by
    refine (Finset.eventually_all _).2 fun j hj ↦ ?_
    refine (Metric.tendstoUniformlyOn_iff.1
      (hlim j (by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)))
      (ε / L) (by positivity)).mono fun m hm x hx ↦ ?_
    rw [← dist_eq_norm, dist_comm]
    exact hm x hx
  obtain ⟨m, hm⟩ := hev.exists
  set e : E → F := fun x ↦ h m x - f₂ x
  have he : ContDiff ℝ n e := ((hh m).1.of_le (by simp)).sub hf₂
  set g : E → F := fun x ↦ h m x + χ x • (f₀ x - h m x)
  have hg : ContDiff ℝ ∞ g := (hh m).1.add (hχ.smul (hf₀.sub (hh m).1))
  refine ⟨g, hg, ?_, ?_⟩
  · intro k hk x hx
    -- Near `x`, `g - f₂` is `φ • e`.
    have hloc : (fun y ↦ g y - f₂ y) =ᶠ[𝓝 x] fun y ↦ φ y • e y := by
      have h0 : ∀ᶠ y in 𝓝 x, χ y • (f₀ y - f y) = 0 := by
        by_cases hxW : x ∈ W
        · simp only [W, mem_ofPred_eq] at hxW
          exact hxW.mono fun y hy ↦ by simp [hy]
        · exact (notMem_tsupport_iff_eventuallyEq.1 fun hx' ↦ hxW (hχW hx')).mono
            fun y hy ↦ by simp [hy]
      filter_upwards [h0, hf₂K x hx] with y hy hy'
      simp only [g, φ, e, sub_smul, one_smul, smul_sub] at hy ⊢
      rw [sub_eq_zero] at hy
      rw [hy', hy]
      abel
    have hfx : iteratedFDeriv ℝ k f x = iteratedFDeriv ℝ k f₂ x :=
      ((hf₂K x hx).iteratedFDeriv (𝕜 := ℝ) k).self_of_nhds.symm
    rw [hfx, ← fun_iteratedFDeriv_sub_apply (f := g)
      ((hg.of_le (by simp)).contDiffAt)
      ((hf₂.of_le (by exact_mod_cast hk)).contDiffAt),
      (hloc.iteratedFDeriv (𝕜 := ℝ) k).self_of_nhds]
    have hex : ∀ p ≤ n, ‖iteratedFDeriv ℝ p e x‖ ≤ ε / L := fun p hp ↦ by
      rw [fun_iteratedFDeriv_sub_apply (((hh m).1.of_le (by simp)).contDiffAt)
        ((hf₂.of_le (by exact_mod_cast hp)).contDiffAt)]
      exact (hm p (Finset.mem_range.2 (Nat.lt_succ_of_le hp)) x hx).le
    have hle := (ContinuousLinearMap.lsmul ℝ ℝ).norm_iteratedFDeriv_le_two_pow_mul_of_bilinear
      ContinuousLinearMap.opNorm_lsmul_le (hφ.of_le (by simp)) he (fun p hp ↦ hA p hp x hx)
      hex hk
    simp only [ContinuousLinearMap.lsmul_apply] at hle
    refine hle.trans_lt ?_
    calc (2 : ℝ) ^ k * (A * (ε / L)) ≤ 2 ^ n * (A * (ε / L)) := by
          gcongr
          · norm_num
      _ = ε * (A / (A + 1)) := by simp only [L]; field_simp
      _ < ε := mul_lt_of_lt_one_right hε ((div_lt_one (by positivity)).2 (lt_add_one A))
  · refine eventually_nhdsSet_iff_forall.2 fun x hx ↦ ?_
    filter_upwards [hχ1 x hx, hf₀C x hx] with y hy hy'
    simp [g, hy, ← hy']

/-- Let `f : ℝ → ℝ` be `Cⁿ` on a neighbourhood `U` of `[a, b]` and smooth on a neighbourhood `V`
of `[c, b]`. For every `ε > 0` there is a smooth `g` whose derivatives of order `k ≤ n` are within
`ε` of those of `f` on `[a, b]`, and which agrees with `f` on a neighbourhood of `[c, b]`. Taking
`b < c` gives the case without the second condition. -/
theorem ContDiffOn.exists_contDiff_abs_iteratedDeriv_sub_lt {f : ℝ → ℝ} {n : ℕ}
    {a b c ε : ℝ} {U V : Set ℝ} (hU : U ∈ 𝓝ˢ (Icc a b)) (hf : ContDiffOn ℝ n f U)
    (hV : V ∈ 𝓝ˢ (Icc c b)) (hfV : ContDiffOn ℝ ∞ f V) (hε : 0 < ε) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧
      (∀ k ≤ n, ∀ x ∈ Icc a b, |iteratedDeriv k g x - iteratedDeriv k f x| < ε) ∧
      g =ᶠ[𝓝ˢ (Icc c b)] f := by
  obtain ⟨g, hg, hgf, hgC⟩ :=
    hf.exists_contDiff_norm_iteratedFDeriv_sub_lt isCompact_Icc hU isCompact_Icc hV hfV hε
  refine ⟨g, hg, fun k hk x hx ↦ ?_, hgC⟩
  rw [iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_eq_iteratedFDeriv, ← Real.norm_eq_abs,
    ← sub_apply]
  refine lt_of_le_of_lt ?_ (hgf k hk x hx)
  simpa using (iteratedFDeriv ℝ k g x - iteratedFDeriv ℝ k f x).le_opNorm fun _ ↦ 1

/-- Let `f : ℝ → ℝ` be `Cⁿ` at every point of `[a, b]` and smooth on an open set `V` containing
`[c, b]`. For every `ε > 0` there is a smooth `g` whose derivatives of order `k ≤ n` are within
`ε` of those of `f` on `[a, b]`, and which agrees with `f` on a neighbourhood of `[c, b]`. -/
theorem ContDiffOn.exists_contDiff_abs_iteratedDeriv_sub_lt_of_contDiffAt {f : ℝ → ℝ} {n : ℕ}
    {a b c ε : ℝ} {V : Set ℝ} (hf : ∀ x ∈ Icc a b, ContDiffAt ℝ n f x) (hV : IsOpen V)
    (hcV : Icc c b ⊆ V) (hfV : ContDiffOn ℝ ∞ f V) (hε : 0 < ε) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧
      (∀ k ≤ n, ∀ x ∈ Icc a b, |iteratedDeriv k g x - iteratedDeriv k f x| < ε) ∧
      g =ᶠ[𝓝ˢ (Icc c b)] f :=
  let ⟨_, hU, haU, hfU⟩ := TauCeti.exists_isOpen_superset_contDiffOn (by simp) hf
  hfU.exists_contDiff_abs_iteratedDeriv_sub_lt (hU.mem_nhdsSet.2 haU) (hV.mem_nhdsSet.2 hcV) hfV hε
