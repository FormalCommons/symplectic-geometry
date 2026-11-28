/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.PathIntegral
public import TauCeti.Geometry.Manifold.Instances.Icc.CollaredSmoothTransition
import TauCeti.Topology.Algebra.Order.Floor

/-!
# Exactness of closed `1`-forms from their periods on periodic loops

Tau Ceti's `TauCeti.mem_exactForms_one_iff_forall_pathIntegral_eq_zero` detects exactness of a
closed smooth real `1`-form by its integrals along smooth curves `γ : ℝ → M` with
`γ 0 = γ 1 = x₀`. Such a curve need not be periodic. This file shows that the integrals along
smooth `1`-periodic curves `c : ℝ → M` over `[0, 1]` detect exactness as well.

A curve `γ` with `γ 0 = γ 1` is first flattened near both ends by the collared smooth transition
`ρ = TauCeti.collaredSmoothTransition`, which is `0` up to `1 / 4` and `1` from `3 / 4` on, and
then periodized: `c t = γ (ρ (fract t))`. Since `γ ∘ ρ` is periodic just below `0`, the
periodization is smooth, as in Tau Ceti's `ContMDiff.comp_fract_snd`, whose proof (through
`TauCeti.apply_fract_snd_eventuallyEq`) is followed here for curves. On `(0, 1)` the curve `c` is
`γ ∘ ρ`, whose integral is that of `γ` by reparametrization invariance
(`TauCeti.pathIntegral_comp`).

## Main results

* `TauCeti.contMDiff_comp_collaredSmoothTransition_fract`: the periodization
  `t ↦ γ (ρ (fract t))` of a `C^n` curve `γ` with `γ 0 = γ 1` is `C^n`.
* `TauCeti.pathIntegral_comp_collaredSmoothTransition_fract`: its integral over `[0, 1]` is that
  of `γ`.
* `TauCeti.mem_exactForms_one_iff_forall_periodic_pathIntegral_eq_zero`: a closed smooth real
  `1`-form on a preconnected manifold is exact exactly when its integrals over `[0, 1]` along all
  smooth `1`-periodic curves vanish.

## References

* [R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982]
-/

public section

open Set Filter
open scoped Manifold ContDiff Topology

noncomputable section

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-- The curve `t ↦ γ (ρ (fract t))`, for any curve `γ` and the collared smooth transition `ρ`, is
`1`-periodic. -/
theorem periodic_comp_collaredSmoothTransition_fract {α : Type*} (γ : ℝ → α) :
    Function.Periodic (fun t ↦ γ (collaredSmoothTransition (Int.fract t))) 1 := fun t ↦ by
  simp

/-- The periodization `t ↦ γ (ρ (fract t))` of a `C^n` curve `γ` with `γ 0 = γ 1`, flattened near
the ends by the collared smooth transition `ρ`, is `C^n`. -/
theorem contMDiff_comp_collaredSmoothTransition_fract {n : WithTop ℕ∞} (hn : n ≤ ∞)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I n γ) (h : γ 0 = γ 1) :
    ContMDiff 𝓘(ℝ, ℝ) I n fun t ↦ γ (collaredSmoothTransition (Int.fract t)) := fun t ↦ by
  set G : Unit × ℝ → M := fun w ↦ γ (collaredSmoothTransition w.2)
  have hG : ∀ y : Unit, ∀ {s : ℝ}, -(1 / 4) < s → s < 0 → G (y, s + 1) = G (y, s) :=
    fun _ s hs₀ hs₁ ↦ by
      simp only [G, collaredSmoothTransition_eq_one_of_ge (by linarith : (3 / 4 : ℝ) ≤ s + 1),
        collaredSmoothTransition_eq_zero_of_le (by linarith : s ≤ 1 / 4), h]
  -- Near `t`, the periodization is a translate of `γ ∘ ρ`.
  have hev := (apply_fract_snd_eventuallyEq (by norm_num) hG ((), t)).comp_tendsto
    ((continuous_const.prodMk continuous_id).tendsto t)
  have hsm : ContMDiff 𝓘(ℝ, ℝ) I n fun s : ℝ ↦ γ (collaredSmoothTransition (s - ⌊t⌋)) :=
    hγ.comp ((contDiff_collaredSmoothTransition hn).comp
      (contDiff_id.sub contDiff_const)).contMDiff
  exact (hsm t).congr_of_eventuallyEq hev

/-- The integral over `[0, 1]` of a continuous `1`-form along the periodization
`t ↦ γ (ρ (fract t))` of a `C¹` curve `γ`, flattened near the ends by the collared smooth
transition `ρ`, is its integral along `γ` over `[0, 1]`. -/
theorem pathIntegral_comp_collaredSmoothTransition_fract [IsManifold I 1 M]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {φ : RoughForm I M F 1} (hφ : IsSmoothForm I 0 φ) {γ : ℝ → M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) :
    pathIntegral φ (fun t ↦ γ (collaredSmoothTransition (Int.fract t))) 0 1 =
      pathIntegral φ γ 0 1 := by
  have hρ : ContDiff ℝ 1 collaredSmoothTransition := contDiff_collaredSmoothTransition (by simp)
  have hfr : EqOn (fun t ↦ γ (collaredSmoothTransition (Int.fract t)))
      (γ ∘ collaredSmoothTransition) (uIoo 0 1) := fun t ht ↦ by
    rw [uIoo_of_le zero_le_one] at ht
    simp [Int.fract_eq_self.2 ⟨ht.1.le, ht.2⟩]
  rw [pathIntegral_congr_of_eqOn_uIoo hfr,
    pathIntegral_comp hφ hγ (σ' := deriv collaredSmoothTransition)
      (fun t _ ↦ (hρ.differentiable one_ne_zero t).hasDerivAt)
      (hρ.continuous_deriv le_rfl).continuousOn,
    collaredSmoothTransition_eq_zero_of_le (by norm_num),
    collaredSmoothTransition_eq_one_of_ge (by norm_num)]

/-- **Periodic loops detect exactness.** A closed smooth real `1`-form on a preconnected manifold
is exact exactly when its integral over `[0, 1]` along every smooth `1`-periodic curve vanishes. -/
theorem mem_exactForms_one_iff_forall_periodic_pathIntegral_eq_zero [FiniteDimensional ℝ E]
    [T2Space M] [IsManifold I ∞ M] [PreconnectedSpace M] {φ : SmoothForm I M ℝ 1}
    (hφ : φ ∈ closedForms I M 1) :
    φ ∈ exactForms I M 1 ↔ ∀ c : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I ∞ c → Function.Periodic c 1 →
      pathIntegral (φ : RoughForm I M ℝ 1) c 0 1 = 0 := by
  refine ⟨fun he c hc hcp ↦ pathIntegral_eq_zero_of_mem_exactForms he (hc.of_le (by simp))
    (by simpa using (hcp 0).symm), fun h ↦ ?_⟩
  rcases isEmpty_or_nonempty M with hM | ⟨⟨x₀⟩⟩
  · convert (exactForms I M 1).zero_mem
    exact SmoothBundleForm.ext fun x ↦ isEmptyElim x
  rw [mem_exactForms_one_iff_forall_pathIntegral_eq_zero hφ x₀]
  intro γ hγ hγ₀ hγ₁
  rw [← pathIntegral_comp_collaredSmoothTransition_fract (φ.isSmoothForm.of_le (by simp))
    (hγ.of_le (by simp))]
  exact h _ (contMDiff_comp_collaredSmoothTransition_fract le_rfl hγ (hγ₀.trans hγ₁.symm))
    (periodic_comp_collaredSmoothTransition_fract γ)

end TauCeti

end
