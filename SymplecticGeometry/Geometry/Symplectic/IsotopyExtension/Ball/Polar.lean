/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.IsotopyExtension.Ball.Basic
import SymplecticGeometry.Geometry.Manifold.ContMDiff.TimeExtension
import SymplecticGeometry.Analysis.CStarAlgebra.Matrix
import SymplecticGeometry.Analysis.Matrix.EuclideanLin
import SymplecticGeometry.Analysis.Matrix.SymplecticGroup.Polar
import TauCeti.Geometry.Manifold.ContMDiff.Subtype.Cutoff
import SymplecticGeometry.Geometry.Symplectic.Manifold.TwoForm
import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Matrix

/-!
# Polar decomposition of the linearization of a family of symplectic balls

Let `κ` be a smooth family over `[0, 1]` of symplectic embeddings of a closed ball `B(δ)`,
`0 < δ`, of `StdSpace (Fin n)` into itself, with the standard form `ω₀`. The derivatives
`Ψ_t = dκ_t(0)` preserve `ω₀`. Their polar decompositions `Ψ_t = P_t U_t` give a smooth family
`U` of linear isometries and a smooth two-parameter family `Q (t, s) = P_t ^ (s - 1)` of linear
maps, all preserving `ω₀` for `t ∈ [0, 1]`, with `Q (t, 1) = 1` and `Ψ_t ∘ U_t⁻¹ ∘ Q (t, 0) = 1`;
and `U_t = 1`, `Q (t, s) = 1` whenever `Ψ_t = 1`
(`SymplecticGeometry.IsSymplecticBallFamily.exists_polar_fderiv_zero`). This is the input that
`SymplecticGeometry.IsSymplecticBallFamily.exists_rescaling_family` takes, for the family
`κ_t ∘ U_t⁻¹`, in the proof of McDuff–Salamon, Proposition 7.1.22 (second part).

The derivatives `dκ_t(0)` are those of the extension `timeExtend κ` of `κ` to all times, which
are smooth in `t ∈ ℝ` (`SymplecticGeometry.IsSymplecticBallFamily.contDiff_fderiv_timeExtend`).
Seeley's extension does not keep them symplectic outside `[0, 1]`, but they stay invertible on
an open neighbourhood of `[0, 1]`. So after a smooth change of time that is the identity on
`[0, 1]` and maps `ℝ` into that neighbourhood
(Tau Ceti's `TopologicalSpace.Opens.exists_contMDiff_eventuallyEq_id`), the polar decomposition of a
smooth family of invertible matrices (`Matrix.exists_contDiff_polar`) applies, and its factors
are symplectic at the times in `[0, 1]`.

## Main results

* `SymplecticGeometry.IsSymplecticBallFamily.contDiff_fderiv_timeExtend`: the derivative at a
  point of `B(r)` of the time extension of a family of symplectic balls is smooth in time.
* `SymplecticGeometry.IsSymplecticBallFamily.exists_polar_fderiv_zero`: the families `U` and `Q`
  described above.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Proposition 7.1.22.
-/

public section

noncomputable section

open Set Function Metric
open scoped ContDiff Manifold Matrix.Norms.Elementwise

namespace SymplecticGeometry

open TauCeti Matrix

variable {n : ℕ}

/-- For a smooth family `κ` over `[0, 1]` of symplectic embeddings of `B(r)` into
`StdSpace (Fin n)`, and a point `z ∈ B(r)`, the derivative at `z` of the time extension
`timeExtend κ` at time `t` is smooth in `t ∈ ℝ`. -/
theorem IsSymplecticBallFamily.contDiff_fderiv_timeExtend
    {σ : SmoothTwoForm 𝓘(ℝ, StdSpace (Fin n)) (StdSpace (Fin n))} {r : ℝ}
    {κ : unitInterval × StdSpace (Fin n) → StdSpace (Fin n)}
    (hκ : IsSymplecticBallFamily σ r κ) {z : StdSpace (Fin n)} (hz : z ∈ closedBall 0 r) :
    ContDiff ℝ ∞ fun t ↦ fderiv ℝ (fun w ↦ timeExtend κ (t, w)) z := by
  obtain ⟨U, hUo, hrU, hf⟩ := hκ.exists_contDiffOn_timeExtend
  refine contDiff_iff_contDiffAt.2 fun t ↦ ?_
  exact ContDiffAt.fderiv (f := fun t w ↦ timeExtend κ (t, w)) (g := fun _ ↦ z)
    (hf.contDiffAt ((isOpen_univ.prod hUo).mem_nhds ⟨trivial, hrU hz⟩)) contDiffAt_const
    (by simp)

/-- **Polar decomposition of the linearization of a family of symplectic balls.** Let `κ` be a
smooth family over `[0, 1]` of symplectic embeddings of `B(δ)`, `0 < δ`, into `StdSpace (Fin n)`
with `ω₀`. Then there are a family `U` of linear isometries of `StdSpace (Fin n)`, smooth as a
family of continuous linear maps, and a smooth family `Q : ℝ × ℝ → (StdSpace (Fin n) →L[ℝ]
StdSpace (Fin n))`, such that for `t ∈ [0, 1]` the maps `U t` and `Q (t, s)` preserve `ω₀`,
`Q (t, 1) = 1` for all `t`, `dκ_t(0) ∘ (U t)⁻¹ ∘ Q (t, 0) = 1` for `t ∈ [0, 1]`, and `U t = 1`
and `Q (t, s) = 1` for all `s` whenever `dκ_t(0) = 1`. -/
theorem IsSymplecticBallFamily.exists_polar_fderiv_zero {δ : ℝ} (hδ : 0 < δ)
    {κ : unitInterval × StdSpace (Fin n) → StdSpace (Fin n)}
    (hκ : IsSymplecticBallFamily (stdForm (Fin n)).constSmooth δ κ) :
    ∃ (U : ℝ → (StdSpace (Fin n) ≃ₗᵢ[ℝ] StdSpace (Fin n)))
      (Q : ℝ × ℝ → StdSpace (Fin n) →L[ℝ] StdSpace (Fin n)),
      ContDiff ℝ ∞ (fun t ↦ (U t : StdSpace (Fin n) →L[ℝ] StdSpace (Fin n))) ∧
      ContDiff ℝ ∞ Q ∧
      (∀ t : unitInterval, ∀ v w, stdForm (Fin n) (U t v) (U t w) = stdForm (Fin n) v w) ∧
      (∀ (t : unitInterval) (s : ℝ) v w,
        stdForm (Fin n) (Q (t, s) v) (Q (t, s) w) = stdForm (Fin n) v w) ∧
      (∀ t, Q (t, 1) = 1) ∧
      (∀ t : unitInterval, ((fderiv ℝ (fun z ↦ κ (t, z)) 0).comp
        ((U t).symm : StdSpace (Fin n) →L[ℝ] StdSpace (Fin n))).comp (Q (t, 0)) = 1) ∧
      ∀ t : unitInterval, fderiv ℝ (fun z ↦ κ (t, z)) 0 = 1 → U t = 1 ∧ ∀ s, Q (t, s) = 1 := by
  -- The matrices `Ψ₀ t` of the derivatives at `0` of the time extension of `κ`.
  set Ψ₀ : ℝ → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
    fun t ↦ (toEuclideanCLM (n := Fin n ⊕ Fin n) (𝕜 := ℝ)).symm
      (fderiv ℝ (fun z ↦ timeExtend κ (t, z)) 0)
  have hΨ₀ : ContDiff ℝ ∞ Ψ₀ := by
    simp only [Ψ₀, ← coe_toEuclideanCLMContinuousLinearEquiv_symm]
    exact toEuclideanCLMContinuousLinearEquiv.symm.contDiff.comp
      (hκ.contDiff_fderiv_timeExtend (mem_closedBall_self hδ.le))
  have hΨ₀t (t : unitInterval) :
      toEuclideanCLM (n := Fin n ⊕ Fin n) (𝕜 := ℝ) (Ψ₀ t) = fderiv ℝ (fun z ↦ κ (t, z)) 0 := by
    simp only [Ψ₀, StarAlgEquiv.apply_symm_apply, timeExtend_apply_coe]
  have hΨ₀sp (t : unitInterval) : Ψ₀ t ∈ symplecticGroup (Fin n) ℝ := by
    refine mem_symplecticGroup_iff_forall_stdForm_toEuclideanCLM.2 fun v w ↦ ?_
    rw [hΨ₀t t]
    exact (SymplecticForm.mpullback_constSmooth_apply_eq_iff _ _).1
      ((hκ.isSymplecticBallEmbedding t).mpullback_eq (mem_ball_self hδ)) v w
  -- A smooth change of time `φ`, the identity on `[0, 1]`, along which `Ψ₀` stays invertible.
  have hO : IsOpen {t | IsUnit (Ψ₀ t)} := by
    simp_rw [isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    exact isOpen_ne_fun hΨ₀.continuous.matrix_det continuous_const
  obtain ⟨g, hg, hgt⟩ := (⟨_, hO⟩ : TopologicalSpace.Opens ℝ).exists_contMDiff_eventuallyEq_id
    (convex_Icc 0 1) isCompact_Icc (nonempty_Icc.2 zero_le_one)
    fun t ht ↦ (isUnit_iff_isUnit_det _).2 (SymplecticGroup.symplectic_det (hΨ₀sp ⟨t, ht⟩))
  set φ : ℝ → ℝ := fun t ↦ g t
  have hφ : ContDiff ℝ ∞ φ := contMDiff_iff_contDiff.1 (contMDiff_subtypeVal.comp hg)
  have hφt : EqOn φ id (Icc 0 1) := fun t ht ↦ (hgt t ht).eq_of_nhds
  have hφO (t : ℝ) : IsUnit (Ψ₀ (φ t)) := (g t).property
  -- The polar decomposition of `Ψ₀ ∘ φ`.
  obtain ⟨U', Q', hU', hQ', hU'o, hQ'0, hQ'add, hΨQU, hsp, h1⟩ :=
    exists_contDiff_polar (hΨ₀.comp hφ) hφO
  have hΨ (t : unitInterval) : Ψ₀ (φ t) = Ψ₀ t := by rw [hφt t.property, id_eq]
  have hspt (t : unitInterval) := hsp t (by rw [Function.comp_apply, hΨ t]; exact hΨ₀sp t)
  set U : ℝ → (StdSpace (Fin n) ≃ₗᵢ[ℝ] StdSpace (Fin n)) :=
    fun t ↦ UnitaryGroup.toLinearIsometryEquiv ⟨U' t, hU'o t⟩
  set Q : ℝ × ℝ → StdSpace (Fin n) →L[ℝ] StdSpace (Fin n) :=
    fun p ↦ toEuclideanCLM (n := Fin n ⊕ Fin n) (𝕜 := ℝ) (Q' (p.1, p.2 - 1))
  refine ⟨U, Q, ?_, ?_, fun t v w ↦ ?_, fun t s v w ↦ ?_, fun t ↦ by simp [Q, hQ'0], fun t ↦ ?_,
    fun t ht ↦ ?_⟩
  · simp only [U, UnitaryGroup.coe_toLinearIsometryEquiv, ← coe_toEuclideanCLMContinuousLinearEquiv]
    exact toEuclideanCLMContinuousLinearEquiv.contDiff.comp hU'
  · simp only [Q, ← coe_toEuclideanCLMContinuousLinearEquiv]
    exact toEuclideanCLMContinuousLinearEquiv.contDiff.comp
      (hQ'.comp (contDiff_fst.prodMk (contDiff_snd.sub contDiff_const)))
  · simpa [U] using mem_symplecticGroup_iff_forall_stdForm_toEuclideanCLM.1 (hspt t).1 v w
  · exact mem_symplecticGroup_iff_forall_stdForm_toEuclideanCLM.1 ((hspt t).2 (s - 1)) v w
  · have hm : Q' (t, 1) * U' t * star (U' t) * Q' (t, 0 - 1) = 1 := by
      rw [mul_assoc (Q' _), mem_unitaryGroup_iff.1 (hU'o t), mul_one, ← hQ'add]
      norm_num [hQ'0]
    rw [← hΨ₀t t, ← hΨ t, ← Function.comp_apply (f := Ψ₀), hΨQU]
    simp only [U, UnitaryGroup.coe_toLinearIsometryEquiv_symm, Q, ← ContinuousLinearMap.mul_def,
      ← map_mul, hm, map_one]
  · have hΨ1 : Ψ₀ (φ t) = 1 := by
      rw [hΨ t]
      simp only [Ψ₀, timeExtend_apply_coe, ht, map_one]
    obtain ⟨hU1, hQ1⟩ := h1 _ hΨ1
    refine ⟨LinearIsometryEquiv.ext fun x ↦ ?_, fun s ↦ ?_⟩
    · simp [U, hU1]
    · simp [Q, hQ1]

end SymplecticGeometry

end
