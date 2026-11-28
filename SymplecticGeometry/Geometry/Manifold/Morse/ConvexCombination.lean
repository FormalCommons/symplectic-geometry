/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Morse.Linearization
public import SymplecticGeometry.Geometry.Manifold.Morse.BirthDeath.Basic
import TauCeti.Topology.Algebra.Module.BilinearForm
import SymplecticGeometry.Geometry.Manifold.Morse.BirthDeath.OfCubic
import SymplecticGeometry.Topology.Algebra.Module.BilinearForm
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic

/-!
# Critical points along a segment of functions with a common gradient-like field

Let `X` be differentiable at `p` and gradient-like near `p` (`TauCeti.IsGradientLikeAt`)
for two functions `f` and `g`, each with a metric and a constant of its own. If `p` is a
nondegenerate critical point of `f` and `g` is of class `C²` in the chart at `p`, then `p` is
a nondegenerate critical point of every function `(1 - s) • f + s • g` with `s ∈ [0, 1]`
(`TauCeti.IsManifoldNondegenerateCriticalPoint.one_sub_smul_add_smul`), and so of every function
equal to one of them near `p`, by Tau Ceti's
`TauCeti.IsManifoldNondegenerateCriticalPoint.congr_of_eventuallyEq`.

The same holds for birth–death critical points. If `X` is `C³` at `p` and gradient-like near `p`
for `f` and for a function `g` that is smooth near `p`, and `f` has a birth–death chart at `p`
(`TauCeti.BirthDeathChart`), then so does `g`
(`TauCeti.BirthDeathChart.nonempty_of_isGradientLikeAt`). Since `X` is gradient-like for every
`(1 - s) • f + s • g` with `s ∈ [0, 1]` (`TauCeti.IsGradientLikeAt.one_sub_smul_add_smul`), each
of them has a birth–death chart at `p` (`TauCeti.BirthDeathChart.nonempty_one_sub_smul_add_smul`),
and so does every function equal to one of them near `p`, by
`TauCeti.BirthDeathChart.nonempty_of_eventuallyEq`.

These are the two cases of the statement that the type of a critical point is kept along such a
segment, used for the homotopies of functions with a fixed Weinstein field.

## Implementation notes

At `p` the inequality for `f` forces `X p = 0`, and then the inequality for `g` forces the
gradient of `g` to vanish at `p`, so `p` is a critical point of `g` too. Write `A` for the
linearization of `X` at `p`, and `B`, `B'` for the second derivatives of `f`, `g` in the chart
at `p`. By `TauCeti.exists_pos_mul_norm_sq_add_norm_sq_le_fderiv_fderiv`,
`c * (‖A v‖ ^ 2 + ‖B v‖ ^ 2) ≤ B v (A v)` for some `c > 0`, and the same for `B'`. If `A v = 0`
the first inequality gives `B v = 0`, so `v = 0` since `B` is invertible: `A` is injective. The
second derivative `(1 - s) • B + s • B'` of the combination then satisfies
`(1 - s) • B v (A v) + s • B' v (A v) ≥ min c c' * ‖A v‖ ^ 2`, so it is injective, hence
invertible in finite dimension (`ContinuousLinearMap.isInvertible_of_injective`).

In the birth–death case, read `f` and `g` in the chart at `p` as `F` and `G`, with Hessians `B` and
`B'`, and `X` as `Y`, with linearization `A`. The second-order inequality gives
`ker B = ker A = ker B'` (`ContinuousLinearMap.ker_eq_ker_of_mul_norm_sq_add_norm_sq_le`), and
`ker B` is a line `ℝ ∙ e` with `D³F e e e ≠ 0` (`TauCeti.nonempty_birthDeathChart_iff`). Along the
parabolas `t ↦ t • e + t ^ 2 • w` the inequality holds at order `t ^ 4`
(`TauCeti.exists_pos_mul_norm_sq_add_sq_le_of_fderiv_fderiv_apply_eq_zero`), between
`α = B w + D³F e e / 2` and `β = A w + D²Y e e / 2`, and between `α' = B' w + D³G e e / 2` and the
same `β`. If `D³G e e e` vanished, the form `D³G e e` would vanish on `ker B'`, so
`α' = 0` for some `w` (`ContinuousLinearMap.exists_apply_eq_of_ker_eq_span_singleton`); then
`β = 0` by the inequality for `g`, so `α e = 0` by the inequality for `f`, and
`α e = D³F e e e / 2` since `B` is symmetric and `B e = 0`. The converse of the criterion,
`TauCeti.nonempty_birthDeathChart_of_ker_eq_span_singleton`, then gives the chart of `g`. The
terms of `dG` and of `Y` across `e` enter only through `w`, so no chart adapted to `f` is used.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Proposition 9.23
-/

public section

open Bundle Filter Set TauCeti.Manifold
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {f g : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

/-- **Nondegeneracy along a segment of functions.** Let `X` be differentiable at `p` and
gradient-like near `p` (`TauCeti.IsGradientLikeAt`) for `f` and for `g`. Let `p` be a
nondegenerate critical point of `f`, and let `g` be of class `C²` in the chart at `p`. Then `p` is a
nondegenerate critical point of `(1 - s) • f + s • g` for every `s ∈ [0, 1]`. -/
theorem IsManifoldNondegenerateCriticalPoint.one_sub_smul_add_smul {p : M}
    (hf : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f p)
    (hg : ContDiffAt ℝ 2 (g ∘ (extChartAt 𝓘(ℝ, E) p).symm) (extChartAt 𝓘(ℝ, E) p p))
    (hXf : IsGradientLikeAt f X p)
    (hXg : IsGradientLikeAt g X p)
    (hXp : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E).tangent
      (fun x ↦ (X x : TangentBundle 𝓘(ℝ, E) M)) p)
    {s : ℝ} (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1) :
    IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) ((1 - s) • f + s • g) p := by
  have hf' := (isManifoldNondegenerateCriticalPoint_iff _).1 hf
  set φ := extChartAt 𝓘(ℝ, E) p
  set A : E →L[ℝ] E := sectionLinearization (F := E) 𝓘(ℝ, E) id X p
  set B := fderiv ℝ (fderiv ℝ (f ∘ φ.symm)) (φ p)
  set B' := fderiv ℝ (fderiv ℝ (g ∘ φ.symm)) (φ p)
  -- At the critical point `p` of `f`, the inequality for `f` forces `X p = 0`.
  have hX₀ : X p = 0 :=
    hXf.eq_zero_iff.2 hf.mem_criticalPoints
  -- Then the inequality for `g` at `p` makes `p` a critical point of `g`.
  have hgp : p ∈ criticalPoints 𝓘(ℝ, E) g := hXg.eq_zero_iff.1 hX₀
  obtain ⟨c, hc, hcB⟩ := exists_pos_mul_norm_sq_add_norm_sq_le_fderiv_fderiv hXf
    hf.mem_criticalPoints hf'.contDiffAt hXp (A := A) rfl
  obtain ⟨c', hc', hcB'⟩ := exists_pos_mul_norm_sq_add_norm_sq_le_fderiv_fderiv hXg hgp hg hXp
    (A := A) rfl
  -- The linearization `A` is injective, since `B` is.
  have hA (v : E) (hv : A v = 0) : v = 0 := by
    have h := hcB v
    rw [hv, map_zero, norm_zero, zero_pow two_ne_zero, zero_add] at h
    have hBv : B v = 0 := norm_eq_zero.1 <| pow_eq_zero_iff (n := 2) two_ne_zero |>.1 <|
      le_antisymm (nonpos_of_mul_nonpos_right h hc) (sq_nonneg _)
    obtain ⟨L, hL⟩ := hf'.isInvertible
    exact L.injective (by rw [map_zero]; exact (congrArg (· v) hL).trans hBv)
  -- The second derivative of the combination, in the chart.
  have hcomp : ((1 - s) • f + s • g) ∘ φ.symm = (1 - s) • (f ∘ φ.symm) + s • (g ∘ φ.symm) := by
    rw [Pi.add_comp, Pi.smul_comp, Pi.smul_comp]
  have hF := hf'.contDiffAt
  have hBs : fderiv ℝ (fderiv ℝ ((1 - s) • (f ∘ φ.symm) + s • (g ∘ φ.symm))) (φ p) =
      (1 - s) • B + s • B' := by
    rw [fderiv_fderiv_add (u := (1 - s) • (f ∘ φ.symm)) (w := s • (g ∘ φ.symm))
      (by exact hF.const_smul (1 - s)) (by exact hg.const_smul s), fderiv_fderiv_const_smul,
      fderiv_fderiv_const_smul]
  have h₁ := hF.differentiableAt (by norm_num)
  have h₂ := hg.differentiableAt (by norm_num)
  rw [isManifoldNondegenerateCriticalPoint_iff, hcomp]
  refine ⟨?_, ?_, ?_⟩
  · rw [Pi.add_def, Pi.smul_def, Pi.smul_def]
    exact (hF.const_smul (1 - s)).add (hg.const_smul s)
  · rw [fderiv_add (h₁.const_smul _) (h₂.const_smul _), fderiv_const_smul h₁,
      fderiv_const_smul h₂, hf'.fderiv_eq_zero,
      fderiv_comp_extChartAt_symm_eq_zero_of_mem_criticalPoints hgp, smul_zero, smul_zero,
      add_zero]
  rw [hBs]
  refine ContinuousLinearMap.isInvertible_of_injective ((injective_iff_map_eq_zero _).2
    fun v hv ↦ hA v ?_)
  have h := congrArg (· (A v)) hv
  simp only [add_apply, smul_apply, smul_eq_mul, zero_apply] at h
  have hm : 0 < min c c' := lt_min hc hc'
  have h₁ : min c c' * ‖A v‖ ^ 2 ≤ B v (A v) := by
    nlinarith [hcB v, min_le_left c c', sq_nonneg ‖A v‖, sq_nonneg ‖B v‖]
  have h₂ : min c c' * ‖A v‖ ^ 2 ≤ B' v (A v) := by
    nlinarith [hcB' v, min_le_right c c', sq_nonneg ‖A v‖, sq_nonneg ‖B' v‖]
  have hAv : min c c' * ‖A v‖ ^ 2 ≤ 0 := by
    nlinarith [mul_le_mul_of_nonneg_left h₁ (sub_nonneg.2 hs₁), mul_le_mul_of_nonneg_left h₂ hs₀]
  exact norm_eq_zero.1 <| pow_eq_zero_iff (n := 2) two_ne_zero |>.1 <|
    le_antisymm (nonpos_of_mul_nonpos_right hAv hm) (sq_nonneg _)


/-- **The birth–death type is fixed by a gradient-like field.** Let `X` be `C³` at `p` and
gradient-like near `p` (`TauCeti.IsGradientLikeAt`) for `f` and for `g`. If `f` has a
birth–death chart at `p` and `g` is smooth near `p`, then `g` has a birth–death chart at `p`. -/
theorem BirthDeathChart.nonempty_of_isGradientLikeAt {p : M} (φ : BirthDeathChart E f p)
    (hg : ∀ᶠ y in 𝓝 p, ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) ∞ g y)
    (hXf : IsGradientLikeAt f X p) (hXg : IsGradientLikeAt g X p)
    (hX : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E).tangent 3 (fun x ↦ (X x : TangentBundle 𝓘(ℝ, E) M)) p) :
    Nonempty (BirthDeathChart E g p) := by
  have hf := φ.eventually_contMDiffAt
  obtain ⟨e, he, -, hkerF, h3F⟩ := (nonempty_birthDeathChart_iff hf).1 ⟨φ⟩
  have hfp := φ.mem_criticalPoints
  -- `p` is a critical point of `g`, since `X` vanishes there.
  have hgp : p ∈ criticalPoints 𝓘(ℝ, E) g := hXg.eq_zero_iff.1 (hXf.eq_zero_iff.2 hfp)
  have hF : ContDiffAt ℝ 4 (f ∘ (extChartAt 𝓘(ℝ, E) p).symm) (extChartAt 𝓘(ℝ, E) p p) :=
    hf.self_of_nhds.contDiffAt_comp_extChartAt_symm.of_le (by norm_num)
  have hG : ContDiffAt ℝ 4 (g ∘ (extChartAt 𝓘(ℝ, E) p).symm) (extChartAt 𝓘(ℝ, E) p p) :=
    hg.self_of_nhds.contDiffAt_comp_extChartAt_symm.of_le (by norm_num)
  have hXd := hX.mdifferentiableAt (by norm_num)
  -- Both Hessians have the kernel of the linearization of `X`, so the same kernel `ℝ ∙ e`.
  set A : E →L[ℝ] E := sectionLinearization (F := E) 𝓘(ℝ, E) id X p
  obtain ⟨c, hc, hcF⟩ := exists_pos_mul_norm_sq_add_norm_sq_le_fderiv_fderiv hXf hfp
    (hF.of_le (by norm_num)) hXd (A := A) rfl
  obtain ⟨c', hc', hcG⟩ := exists_pos_mul_norm_sq_add_norm_sq_le_fderiv_fderiv hXg hgp
    (hG.of_le (by norm_num)) hXd (A := A) rfl
  have hkerG : (fderiv ℝ (fderiv ℝ (g ∘ (extChartAt 𝓘(ℝ, E) p).symm))
      (extChartAt 𝓘(ℝ, E) p p)).ker = ℝ ∙ e := by
    rw [← hkerF, ContinuousLinearMap.ker_eq_ker_of_mul_norm_sq_add_norm_sq_le hc hcF,
      ContinuousLinearMap.ker_eq_ker_of_mul_norm_sq_add_norm_sq_le hc' hcG]
  have hmem (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : B.ker = ℝ ∙ e) : B e = 0 :=
    LinearMap.mem_ker.1 (hB ▸ Submodule.mem_span_singleton_self e)
  -- The inequality at fourth order along `e`, for `f` and for `g`.
  obtain ⟨κ, hκ, hκF⟩ :=
    exists_pos_mul_norm_sq_add_sq_le_of_fderiv_fderiv_apply_eq_zero hXf hfp hF hX (hmem _ hkerF)
  obtain ⟨κ', hκ', hκG⟩ :=
    exists_pos_mul_norm_sq_add_sq_le_of_fderiv_fderiv_apply_eq_zero hXg hgp hG hX (hmem _ hkerG)
  refine nonempty_birthDeathChart_of_ker_eq_span_singleton hg
    (fderiv_comp_extChartAt_symm_eq_zero_of_mem_criticalPoints hgp) hkerG fun h3G ↦ h3F ?_
  set BF := fderiv ℝ (fderiv ℝ (f ∘ (extChartAt 𝓘(ℝ, E) p).symm)) (extChartAt 𝓘(ℝ, E) p p)
  set BG := fderiv ℝ (fderiv ℝ (g ∘ (extChartAt 𝓘(ℝ, E) p).symm)) (extChartAt 𝓘(ℝ, E) p p)
  set TG := fderiv ℝ (fderiv ℝ (fderiv ℝ (g ∘ (extChartAt 𝓘(ℝ, E) p).symm)))
    (extChartAt 𝓘(ℝ, E) p p) e e
  -- If the cubic term of `g` vanished along `e`, some `w` would make `BG w + TG / 2` vanish.
  obtain ⟨w, hw⟩ := ContinuousLinearMap.exists_apply_eq_of_ker_eq_span_singleton
    (fun v w ↦ hG.isSymmSndFDerivAt (by simp; norm_num) v w) he hkerG
    (ℓ := -((2⁻¹ : ℝ) • TG)) (by simp [show TG e = 0 from h3G])
  have hαG : BG w + (2⁻¹ : ℝ) • TG = 0 := by rw [hw, neg_add_cancel]
  -- Then the field term `β` vanishes, by the inequality for `g` ...
  have hβ := hκG w 0 (by simp)
  rw [hαG] at hβ
  simp only [zero_apply, map_zero, zero_pow two_ne_zero, add_zero] at hβ
  set Y := VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) p).symm X
  set β := fderiv ℝ Y (extChartAt 𝓘(ℝ, E) p p) w + (2⁻¹ : ℝ) •
    fderiv ℝ (fderiv ℝ Y) (extChartAt 𝓘(ℝ, E) p p) e e
  have hβ₀ : β = 0 := norm_eq_zero.1 <| pow_eq_zero_iff two_ne_zero |>.1 <|
    le_antisymm (nonpos_of_mul_nonpos_right (by simpa using hβ) hκ') (sq_nonneg _)
  -- ... and then the inequality for `f`, against `e / ‖e‖`, kills the cubic term of `f`.
  have he' : ‖‖e‖⁻¹ • e‖ ≤ 1 := by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀
    (norm_ne_zero_iff.2 he)]
  have hα := hκF w _ he'
  simp only [β] at hβ₀
  rw [hβ₀, norm_zero, map_zero, zero_pow two_ne_zero, zero_add] at hα
  have hα₀ := pow_eq_zero_iff two_ne_zero |>.1 <| le_antisymm
    (nonpos_of_mul_nonpos_right hα hκ) (sq_nonneg _)
  have hBF : BF w e = 0 := by
    rw [hF.isSymmSndFDerivAt (by simp; norm_num) w e, hmem _ hkerF, zero_apply]
  simp only [map_smul, add_apply, smul_apply, hBF, smul_eq_mul, zero_add] at hα₀
  have hne : ‖e‖⁻¹ ≠ 0 := inv_ne_zero (norm_ne_zero_iff.2 he)
  simpa [hne] using hα₀

/-- **The birth–death type along a segment of functions.** Let `X` be `C³` at `p` and
gradient-like near `p` (`TauCeti.IsGradientLikeAt`) for `f` and for `g`, let `f` have a
birth–death chart at `p`, and let `g` be smooth near `p`. Then `(1 - s) • f + s • g` has a
birth–death chart at `p` for every `s ∈ [0, 1]`. -/
theorem BirthDeathChart.nonempty_one_sub_smul_add_smul {p : M} (φ : BirthDeathChart E f p)
    (hg : ∀ᶠ y in 𝓝 p, ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) ∞ g y)
    (hXf : IsGradientLikeAt f X p) (hXg : IsGradientLikeAt g X p)
    (hX : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E).tangent 3 (fun x ↦ (X x : TangentBundle 𝓘(ℝ, E) M)) p)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    Nonempty (BirthDeathChart E ((1 - s) • f + s • g) p) := by
  have hf := φ.eventually_contMDiffAt
  refine φ.nonempty_of_isGradientLikeAt ?_ hXf
    (hXf.one_sub_smul_add_smul hXg (hf.mono fun y hy ↦ hy.mdifferentiableAt (by simp))
      (hg.mono fun y hy ↦ hy.mdifferentiableAt (by simp)) hs) hX
  filter_upwards [hf, hg] with y hfy hgy
  exact (contMDiffAt_const.mul hfy).add (contMDiffAt_const.mul hgy)

end TauCeti

end
