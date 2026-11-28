/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Weinstein.Handle.Linearization
import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# Nondegenerate critical points along a segment of functions with a common gradient-like field

Let `X` be differentiable at `p` and satisfy the gradient-like inequality near `p` for two
functions `f` and `g` (in the local form of `TauCeti.isGradientLike_of_forall_exists_nhds`), each
with a metric and a constant of its own. If `p` is a nondegenerate critical point of `f` and a
critical point of `g`, with `g` of class `C²` in the chart at `p`, then `p` is a nondegenerate
critical point of every function `(1 - s) • f + s • g` with `s ∈ [0, 1]`
(`TauCeti.IsManifoldNondegenerateCriticalPoint.one_sub_smul_add_smul`), and so of every function
equal to one of them near `p` (`TauCeti.IsManifoldNondegenerateCriticalPoint.congr_of_eventuallyEq`).

This is the nondegenerate case of the statement that the type of a critical point is kept along
such a segment, used for the homotopies of functions with a fixed Weinstein field.

## Implementation notes

Write `A` for the linearization of `X` at `p`, and `B`, `B'` for the second derivatives of `f`,
`g` in the chart at `p`. By `TauCeti.exists_pos_mul_norm_sq_add_norm_sq_le_fderiv_fderiv`,
`c * (‖A v‖ ^ 2 + ‖B v‖ ^ 2) ≤ B v (A v)` for some `c > 0`, and the same for `B'`. If `A v = 0`
the first inequality gives `B v = 0`, so `v = 0` since `B` is invertible: `A` is injective. The
second derivative `(1 - s) • B + s • B'` of the combination then satisfies
`(1 - s) • B v (A v) + s • B' v (A v) ≥ min c c' * ‖A v‖ ^ 2`, so it is injective, hence
invertible in finite dimension (`ContinuousLinearMap.isInvertible_of_injective`).

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

/-- **Nondegeneracy along a segment of functions.** Let `X` be differentiable at `p` and satisfy
the gradient-like inequality near `p` for `f` and for `g`, in the local form of
`TauCeti.isGradientLike_of_forall_exists_nhds`, with a smooth metric and a constant `c > 0` for
each. Let `p` be a nondegenerate critical point of `f` and a critical point of `g`, with `g` of
class `C²` in the chart at `p`. Then `p` is a nondegenerate critical point of
`(1 - s) • f + s • g` for every `s ∈ [0, 1]`. -/
theorem IsManifoldNondegenerateCriticalPoint.one_sub_smul_add_smul {p : M}
    (hf : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f p)
    (hgp : p ∈ criticalPoints 𝓘(ℝ, E) g)
    (hg : ContDiffAt ℝ 2 (g ∘ (extChartAt 𝓘(ℝ, E) p).symm) (extChartAt 𝓘(ℝ, E) p p))
    (hXf : ∃ U ∈ 𝓝 p,
      ∃ G : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x),
      ∃ c : ℝ, 0 < c ∧
        letI : RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) := ⟨G.toRiemannianMetric⟩
        ∀ y ∈ U, c * (G.inner y (X y) (X y) + ‖mgradient 𝓘(ℝ, E) f y‖ ^ 2) ≤
          mvfderiv 𝓘(ℝ, E) f y (X y))
    (hXg : ∃ U ∈ 𝓝 p,
      ∃ G : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x),
      ∃ c : ℝ, 0 < c ∧
        letI : RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) := ⟨G.toRiemannianMetric⟩
        ∀ y ∈ U, c * (G.inner y (X y) (X y) + ‖mgradient 𝓘(ℝ, E) g y‖ ^ 2) ≤
          mvfderiv 𝓘(ℝ, E) g y (X y))
    (hXp : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E).tangent
      (fun x ↦ (X x : TangentBundle 𝓘(ℝ, E) M)) p)
    {s : ℝ} (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1) :
    IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) ((1 - s) • f + s • g) p := by
  have hf' := (isManifoldNondegenerateCriticalPoint_iff _).1 hf
  set φ := extChartAt 𝓘(ℝ, E) p
  set A : E →L[ℝ] E := sectionLinearization (F := E) 𝓘(ℝ, E) id X p
  set B := fderiv ℝ (fderiv ℝ (f ∘ φ.symm)) (φ p)
  set B' := fderiv ℝ (fderiv ℝ (g ∘ φ.symm)) (φ p)
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
  have hev : fderiv ℝ ((1 - s) • (f ∘ φ.symm) + s • (g ∘ φ.symm)) =ᶠ[𝓝 (φ p)]
      (1 - s) • fderiv ℝ (f ∘ φ.symm) + s • fderiv ℝ (g ∘ φ.symm) := by
    filter_upwards [hF.eventually (by simp), hg.eventually (by simp)] with u hu hu'
    have h₁ := hu.differentiableAt (by norm_num)
    have h₂ := hu'.differentiableAt (by norm_num)
    rw [fderiv_add (h₁.const_smul _) (h₂.const_smul _), fderiv_const_smul h₁,
      fderiv_const_smul h₂]
    simp only [Pi.add_apply, Pi.smul_apply]
  have hBs : HasFDerivAt (fderiv ℝ ((1 - s) • (f ∘ φ.symm) + s • (g ∘ φ.symm)))
      ((1 - s) • B + s • B') (φ p) :=
    (((hF.hasFDerivAt_fderiv le_rfl).const_smul (1 - s)).add
      ((hg.hasFDerivAt_fderiv le_rfl).const_smul s)).congr_of_eventuallyEq hev
  rw [isManifoldNondegenerateCriticalPoint_iff, hcomp]
  refine ⟨?_, ?_, ?_⟩
  · rw [Pi.add_def, Pi.smul_def, Pi.smul_def]
    exact (hF.const_smul (1 - s)).add (hg.const_smul s)
  · rw [hev.eq_of_nhds, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, hf'.fderiv_eq_zero,
      fderiv_comp_extChartAt_symm_eq_zero_of_mem_criticalPoints hgp, smul_zero, smul_zero,
      add_zero]
  rw [hBs.fderiv]
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

end TauCeti

end
