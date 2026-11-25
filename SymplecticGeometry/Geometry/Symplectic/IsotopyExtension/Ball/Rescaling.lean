/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.IsotopyExtension.Ball.Basic
import SymplecticGeometry.Analysis.Calculus.FiberRescale
import SymplecticGeometry.Geometry.Manifold.ContMDiff.TimeExtension
import TauCeti.Geometry.Manifold.ContMDiff.Prod

/-!
# Rescaling a family of symplectic germs to its linearization

Let `θ` be a smooth family over `[0, 1]` of symplectic embeddings of the closed ball `B(ρ)` of
`StdSpace (Fin n)` into itself, with the standard form `ω₀`, each of which fixes `0`. The
rescalings `z ↦ s⁻¹ • θ_t (s • z)`, `0 < s ≤ 1`, are again symplectic, since `ω₀` is constant, and
as `s → 0` they tend to the derivative `dθ_t(0)`, smoothly in `(t, s)`. Composing with a smooth
two-parameter family `Q (t, s)` of linear maps preserving `ω₀`, with `Q (t, 1) = 1` and
`dθ_t(0) ∘ Q (t, 0) = 1`, gives a two-parameter family `G (t, s) = s⁻¹ • θ_t (s • Q (t, s) ·)` of
symplectic embeddings of a smaller ball `B(ρ')`, with `G (t, 0) = id` and `G (t, 1) = θ_t`
(`SymplecticGeometry.IsSymplecticBallFamily.exists_rescaling_family`). This is a step of the
proof of McDuff–Salamon, Proposition 7.1.22 (second part).

The smoothness at `s = 0` is that of the library's `fiberRescale`
(`contDiffOn_fiberRescale_of_starShaped`), applied to the extension `timeExtend θ` of `θ` to
`ℝ × StdSpace (Fin n)`.

## Main results

* `fderiv_inv_smul_comp_smul`: the derivative of `x ↦ s⁻¹ • f (s • x)` at `z` is that of `f` at
  `s • z`, for `s ≠ 0`.
* `TauCeti.SymplecticForm.mpullback_constSmooth_apply_eq_iff`: a map pulls a constant symplectic
  form back to itself at a point iff its derivative there preserves the form.
* `TauCeti.SymplecticForm.mpullback_constSmooth_inv_smul_comp_smul`: a rescaling of a map that
  pulls a constant symplectic form back to itself at `s • z` does so at `z`.
* `SymplecticGeometry.IsSymplecticBallFamily.exists_rescaling_family`: the two-parameter family
  joining the identity to `θ` described above.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Proposition 7.1.22.
-/

public section

noncomputable section

open Set Function Metric
open scoped ContDiff Manifold

/-- The derivative of the rescaling `x ↦ s⁻¹ • f (s • x)` of `f` at `z` is the derivative of `f`
at `s • z`, for `s ≠ 0`. -/
theorem fderiv_inv_smul_comp_smul {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) {s : ℝ} (hs : s ≠ 0) (z : E) :
    fderiv ℝ (fun x ↦ s⁻¹ • f (s • x)) z = fderiv ℝ f (s • z) := by
  let : Invertible s⁻¹ := invertibleOfNonzero (inv_ne_zero hs)
  have h : (fun x ↦ s⁻¹ • f (s • x)) = s⁻¹ • fun x ↦ f (s • x) :=
    funext fun x ↦ (Pi.smul_apply s⁻¹ (fun x ↦ f (s • x)) x).symm
  rw [h, fderiv_const_smul_of_invertible, fderiv_comp_smul, smul_smul, inv_mul_cancel₀ hs,
    one_smul]

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- A map `f` of `V` pulls the constant form `σ.constSmooth` back to itself at `z` if and only if
its derivative at `z` preserves `σ`. -/
theorem mpullback_constSmooth_apply_eq_iff (σ : SymplecticForm V) {f : V → V} {z : V} :
    mpullback 𝓘(ℝ, V) 𝓘(ℝ, V) f σ.constSmooth.val z = σ.constSmooth.val z ↔
      ∀ v w, σ (fderiv ℝ f z v) (fderiv ℝ f z w) = σ v w := by
  have hσ (x : V) (a b : TangentSpace 𝓘(ℝ, V) x) : σ.constSmooth.val x ![a, b] =
      σ (NormedSpace.fromTangentSpace x a) (NormedSpace.fromTangentSpace x b) :=
    (SmoothBundleForm.eval₂_apply _ _ _ _).symm.trans (fromTangentSpace_constSmooth_apply σ x a b)
  have hσ' (x a b : V) : σ.constSmooth.val x ![a, b] = σ a b :=
    (SmoothBundleForm.eval₂_apply _ _ _ _).symm.trans (constSmooth_apply σ x a b)
  constructor
  · intro h v w
    have := (mpullback_apply_pair f σ.constSmooth.val z v w).symm.trans
      (congrArg (fun α ↦ α ![v, w]) h)
    rw [mfderiv_eq_fderiv, hσ, hσ' z v w] at this
    simp only [ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe,
      NormedSpace.fromTangentSpace_apply] at this
    exact this
  · intro h
    ext u
    have hu : u = ![u 0, u 1] := by
      funext i
      fin_cases i <;> rfl
    rw [hu, mpullback_apply_pair, mfderiv_eq_fderiv, hσ, hσ]
    simpa using h _ _

/-- If `f` pulls the constant form `σ.constSmooth` back to itself at `s • z`, `s ≠ 0`, then so
does its rescaling `x ↦ s⁻¹ • f (s • x)` at `z`. -/
theorem mpullback_constSmooth_inv_smul_comp_smul (σ : SymplecticForm V) {f : V → V} {s : ℝ}
    (hs : s ≠ 0) {z : V}
    (hf : mpullback 𝓘(ℝ, V) 𝓘(ℝ, V) f σ.constSmooth.val (s • z) = σ.constSmooth.val (s • z)) :
    mpullback 𝓘(ℝ, V) 𝓘(ℝ, V) (fun x ↦ s⁻¹ • f (s • x)) σ.constSmooth.val z =
      σ.constSmooth.val z := by
  rw [mpullback_constSmooth_apply_eq_iff, fderiv_inv_smul_comp_smul f hs]
  exact (mpullback_constSmooth_apply_eq_iff σ).1 hf

end TauCeti.SymplecticForm

namespace SymplecticGeometry

open TauCeti

variable {n : ℕ}

/-- A linear map that preserves `stdForm` is injective. -/
private theorem injective_of_stdForm {Q : StdSpace (Fin n) →L[ℝ] StdSpace (Fin n)}
    (hQ : ∀ v w, stdForm (Fin n) (Q v) (Q w) = stdForm (Fin n) v w) : Injective Q := by
  refine (injective_iff_map_eq_zero Q).2 fun v hv ↦ (stdForm (Fin n)).nondegenerate.1 v fun w ↦ ?_
  change stdForm (Fin n) v w = 0
  rw [← hQ, hv]
  exact LinearMap.map_zero₂ _ _

/-- **Rescaling a family of symplectic germs to its linearization.** Let `θ` be a smooth family
over `[0, 1]` of symplectic embeddings of `B(ρ)`, `0 < ρ`, into `StdSpace (Fin n)` with `ω₀`, each
fixing `0`. Let `Q` be a smooth family of linear maps preserving `ω₀` at all `(t, s) ∈ [0, 1]²`,
with `Q (t, 1) = 1` and `dθ_t(0) ∘ Q (t, 0) = 1`. Then there are `0 < ρ'` and a family
`G : [0, 1] × [0, 1] × StdSpace (Fin n) → StdSpace (Fin n)`, jointly smooth near
`[0, 1]² × B(ρ')`, such that for each `t`, `s ↦ G (t, s, ·)` is a smooth family of symplectic
embeddings of `B(ρ')`, `G (t, 0, ·)` is the identity and `G (t, 1, ·) = θ_t`; and
`G (t, s, ·)` is the identity on `B(ρ')` for all `s` whenever `θ_t` is the identity on `B(ρ)` and
`Q (t, s) = 1` for all `s`. -/
theorem IsSymplecticBallFamily.exists_rescaling_family {ρ : ℝ} (hρ : 0 < ρ)
    {θ : unitInterval × StdSpace (Fin n) → StdSpace (Fin n)}
    (hθ : IsSymplecticBallFamily (stdForm (Fin n)).constSmooth ρ θ) (hθ0 : ∀ t, θ (t, 0) = 0)
    {Q : ℝ × ℝ → StdSpace (Fin n) →L[ℝ] StdSpace (Fin n)} (hQ : ContDiff ℝ ∞ Q)
    (hQs : ∀ t s : unitInterval, ∀ v w,
      stdForm (Fin n) (Q (t, s) v) (Q (t, s) w) = stdForm (Fin n) v w)
    (hQ1 : ∀ t : unitInterval, Q (t, 1) = 1)
    (hQ0 : ∀ t : unitInterval, (fderiv ℝ (fun z ↦ θ (t, z)) 0).comp (Q (t, 0)) = 1) :
    ∃ ρ', 0 < ρ' ∧ ∃ G : unitInterval × unitInterval × StdSpace (Fin n) → StdSpace (Fin n),
      (∃ U, IsOpen U ∧ closedBall 0 ρ' ⊆ U ∧
        ContMDiffOn ((𝓡∂ 1).prod ((𝓡∂ 1).prod 𝓘(ℝ, StdSpace (Fin n)))) 𝓘(ℝ, StdSpace (Fin n)) ∞
          G (univ ×ˢ univ ×ˢ U)) ∧
      (∀ t, IsSymplecticBallFamily (stdForm (Fin n)).constSmooth ρ' fun p ↦ G (t, p.1, p.2)) ∧
      (∀ t z, G (t, 0, z) = z) ∧ (∀ t z, G (t, 1, z) = θ (t, z)) ∧
      (∀ t, (∀ z ∈ closedBall 0 ρ, θ (t, z) = z) → (∀ s : unitInterval, Q (t, s) = 1) →
        ∀ s, ∀ z ∈ closedBall 0 ρ', G (t, s, z) = z) := by
  set ω₀ := (stdForm (Fin n)).constSmooth
  -- A bound `1 ≤ C` for `‖Q (t, s)‖` on `[0, 1]²`, and the balls `B(ρ') ⊆ W = ball 0 (ρ / C)`.
  obtain ⟨C, hC1, hC⟩ : ∃ C, 1 ≤ C ∧ ∀ t s : unitInterval, ‖Q (t, s)‖ ≤ C := by
    obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
      (f := Q) hQ.continuous.continuousOn
    exact ⟨max C 1, le_max_right _ _, fun t s ↦
      (hC _ ⟨t.property, s.property⟩).trans (le_max_left _ _)⟩
  have hC0 : 0 < C := zero_lt_one.trans_le hC1
  set W : Set (StdSpace (Fin n)) := ball 0 (ρ / C)
  set ρ' := ρ / (2 * C)
  have hρ' : 0 < ρ' := by positivity
  have hρ'W : closedBall (0 : StdSpace (Fin n)) ρ' ⊆ W :=
    closedBall_subset_ball (div_lt_div_of_pos_left hρ hC0 (by linarith))
  have hρ'ρ : ρ' ≤ ρ := div_le_self hρ.le (by linarith)
  have hmem (t s : unitInterval) {z : StdSpace (Fin n)} (hz : z ∈ W) :
      (s : ℝ) • Q (t, s) z ∈ ball 0 ρ := by
    rw [mem_ball_zero_iff] at hz ⊢
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (unitInterval.nonneg s)]
    calc (s : ℝ) * ‖Q (t, s) z‖ ≤ 1 * (C * ‖z‖) :=
          mul_le_mul (unitInterval.le_one s) ((Q (t, s)).le_of_opNorm_le (hC t s) z)
            (norm_nonneg _) zero_le_one
      _ < ρ := by rw [one_mul]; exact (lt_div_iff₀' hC0).1 hz
  -- The extension of `θ` to all times, and its rescaling.
  obtain ⟨U, hUo, hρU, hθU⟩ := hθ.exists_contMDiffOn
  have hf : ContDiffOn ℝ ∞ (timeExtend θ) (univ ×ˢ ball 0 ρ) := by
    have := (hθU.timeExtend hUo).mono (prod_mono subset_rfl (ball_subset_closedBall.trans hρU))
    exact contMDiffOn_iff_contDiffOn.1 (contMDiffOn_prod_modelWithCornersSelf_iff.1 this)
  have hR := contDiffOn_fiberRescale_of_starShaped (n := ⊤) (isOpen_univ.prod isOpen_ball)
    (fun p v hv s hs ↦ ⟨trivial, (convex_ball 0 ρ).smul_mem_of_zero_mem (mem_ball_self hρ) hv.2 hs⟩)
    (by simpa using hf) (fun p _ ↦ timeExtend_eq_zero (fun s ↦ hθ0 s) p)
  set g : ℝ × ℝ × StdSpace (Fin n) → StdSpace (Fin n) :=
    fun q ↦ fiberRescale (timeExtend θ) ((q.1, Q (q.1, q.2.1) q.2.2), q.2.1)
  have hg : ContDiffOn ℝ ∞ g {q | q.2.1 • Q (q.1, q.2.1) q.2.2 ∈ ball 0 ρ} := by
    have hφ : ContDiff ℝ ∞ fun q : ℝ × ℝ × StdSpace (Fin n) ↦
        ((q.1, Q (q.1, q.2.1) q.2.2), q.2.1) :=
      (contDiff_fst.prodMk ((hQ.comp (contDiff_fst.prodMk contDiff_snd.fst)).clm_apply
        contDiff_snd.snd)).prodMk contDiff_snd.fst
    exact hR.comp hφ.contDiffOn fun q hq ↦ ⟨trivial, hq⟩
  set G : unitInterval × unitInterval × StdSpace (Fin n) → StdSpace (Fin n) :=
    fun p ↦ g (p.1, p.2.1, p.2.2)
  -- Its values.
  have hθt (t : unitInterval) : (fun w ↦ timeExtend θ ((t : ℝ), w)) = fun w ↦ θ (t, w) :=
    funext fun w ↦ timeExtend_apply_coe θ t w
  have hGne (t s : unitInterval) (hs : (s : ℝ) ≠ 0) :
      (fun z ↦ G (t, s, z)) = fun z ↦ (s : ℝ)⁻¹ • θ (t, (s : ℝ) • Q (t, s) z) := by
    funext z
    simp only [G, g]
    rw [fiberRescale_of_ne_zero _ hs]
    exact congrArg _ (timeExtend_apply_coe θ t _)
  have hG0 (t : unitInterval) (z : StdSpace (Fin n)) : G (t, 0, z) = z := by
    simp only [G, g, Set.Icc.coe_zero, fiberRescale_zero, hθt]
    rw [← ContinuousLinearMap.comp_apply, hQ0 t, one_apply_eq_self]
  have hG1 (t : unitInterval) (z : StdSpace (Fin n)) : G (t, 1, z) = θ (t, z) := by
    simp only [G, g, Set.Icc.coe_one, fiberRescale_one, hQ1 t, one_apply_eq_self,
      timeExtend_apply_coe]
  -- Smoothness.
  have hι : ContMDiff ((𝓡∂ 1).prod ((𝓡∂ 1).prod 𝓘(ℝ, StdSpace (Fin n))))
      𝓘(ℝ, ℝ × ℝ × StdSpace (Fin n)) ∞
      (fun p : unitInterval × unitInterval × StdSpace (Fin n) ↦ ((p.1 : ℝ), (p.2.1 : ℝ), p.2.2)) :=
    (contMDiff_subtypeVal_Icc.comp contMDiff_fst).prodMk_space
      ((contMDiff_subtypeVal_Icc.comp (contMDiff_fst.comp contMDiff_snd)).prodMk_space
        (contMDiff_snd.comp contMDiff_snd))
  have hGs : ContMDiffOn ((𝓡∂ 1).prod ((𝓡∂ 1).prod 𝓘(ℝ, StdSpace (Fin n))))
      𝓘(ℝ, StdSpace (Fin n)) ∞ G (univ ×ˢ univ ×ˢ W) :=
    hg.contMDiffOn.comp hι.contMDiffOn fun p hp ↦ hmem p.1 p.2.1 hp.2.2
  have hslice (t : unitInterval) : ContMDiffOn ((𝓡∂ 1).prod 𝓘(ℝ, StdSpace (Fin n)))
      𝓘(ℝ, StdSpace (Fin n)) ∞ (fun p ↦ G (t, p.1, p.2)) (univ ×ˢ W) :=
    hGs.comp (contMDiff_const.prodMk contMDiff_id).contMDiffOn fun p hp ↦ ⟨trivial, hp⟩
  -- The slices of `θ` are differentiable on `B(ρ)`.
  have hθd (t : unitInterval) {y : StdSpace (Fin n)} (hy : y ∈ closedBall 0 ρ) :
      DifferentiableAt ℝ (fun w ↦ θ (t, w)) y := by
    obtain ⟨V, hVo, hρV, hθV⟩ := (hθ.isSymplecticBallEmbedding t).exists_contMDiffOn
    exact ((contMDiffOn_iff_contDiffOn.1 hθV).differentiableOn (by simp)).differentiableAt
      (hVo.mem_nhds (hρV hy))
  -- Each slice is a symplectic embedding of `B(ρ')`.
  have hemb (t s : unitInterval) : IsSymplecticBallEmbedding ω₀ ρ' (fun z ↦ G (t, s, z)) := by
    by_cases hs : (s : ℝ) = 0
    · obtain rfl : s = 0 := Subtype.ext hs
      rw [show (fun z ↦ G (t, 0, z)) = id from funext (hG0 t)]
      exact isSymplecticBallEmbedding_id ρ'
    have hsm : ContMDiffOn 𝓘(ℝ, StdSpace (Fin n)) 𝓘(ℝ, StdSpace (Fin n)) ∞
        (fun z ↦ G (t, s, z)) W :=
      (hslice t).comp (contMDiff_const.prodMk contMDiff_id).contMDiffOn fun z hz ↦ ⟨trivial, hz⟩
    rw [hGne t s hs] at hsm ⊢
    have hcl {z : StdSpace (Fin n)} (hz : z ∈ closedBall 0 ρ') :
        (s : ℝ) • Q (t, s) z ∈ closedBall 0 ρ :=
      ball_subset_closedBall (hmem t s (hρ'W hz))
    refine (isSymplecticBallEmbedding_def _ _ _).2 ⟨⟨W, isOpen_ball, hρ'W, hsm⟩,
      fun x hx y hy h ↦ injective_of_stdForm (hQs t s) (smul_right_injective _ hs
        ((hθ.isSymplecticBallEmbedding t).injOn (hcl hx) (hcl hy)
          (smul_right_injective _ (inv_ne_zero hs) h))), fun z hz ↦ ?_⟩
    have hz' := hmem t s (hρ'W (ball_subset_closedBall hz))
    have hpull := (SymplecticForm.mpullback_constSmooth_apply_eq_iff _).1
      ((stdForm (Fin n)).mpullback_constSmooth_inv_smul_comp_smul (f := fun w ↦ θ (t, w)) hs
        ((hθ.isSymplecticBallEmbedding t).mpullback_eq hz'))
    refine (SymplecticForm.mpullback_constSmooth_apply_eq_iff _).2 fun v w ↦ ?_
    have hd : DifferentiableAt ℝ (fun y ↦ (s : ℝ)⁻¹ • θ (t, (s : ℝ) • y)) (Q (t, s) z) :=
      ((hθd t (ball_subset_closedBall hz')).comp (Q (t, s) z)
        (differentiableAt_fun_id.const_smul (s : ℝ))).const_smul ((s : ℝ)⁻¹)
    rw [fderiv_fun_comp z hd (Q (t, s)).differentiableAt, ContinuousLinearMap.fderiv,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hpull, hQs]
  refine ⟨ρ', hρ', G, ⟨W, isOpen_ball, hρ'W, hGs⟩,
    fun t ↦ (isSymplecticBallFamily_def _ _ _).2 ⟨⟨W, isOpen_ball, hρ'W, hslice t⟩, hemb t⟩,
    hG0, hG1, fun t hid hQid s z hz ↦ ?_⟩
  by_cases hs : (s : ℝ) = 0
  · obtain rfl : s = 0 := Subtype.ext hs
    exact hG0 t z
  have hsz : (s : ℝ) • z ∈ closedBall 0 ρ := by
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_nonneg (unitInterval.nonneg s)]
    exact (mul_le_of_le_one_left (norm_nonneg _) (unitInterval.le_one s)).trans
      ((mem_closedBall_zero_iff.1 hz).trans hρ'ρ)
  rw [congrFun (hGne t s hs) z, hQid s, one_apply_eq_self, hid _ hsz, smul_smul,
    inv_mul_cancel₀ hs, one_smul]

end SymplecticGeometry

end
