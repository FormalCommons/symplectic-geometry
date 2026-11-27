/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.ConnectedSum.Sphere
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
import TauCeti.Geometry.Euclidean.Inversion

/-!
# Forms on a manifold covered by two complementary balls

Let `s s' : E → N` be complementary balls (`TauCeti.IsComplementaryBall s s'`), so that `s'` is
an open embedding onto `N ∖ {s 0}` and `s' w = s (inversion 0 1 w)` for `w ≠ 0`, both smooth
local diffeomorphisms; the main example is the pair of stereographic charts of a round sphere
(`TauCeti.isComplementaryBall_sphereBall`). Let `0 < R`, `0 < R'` with `R * R' < 1`, and let `τ`,
`τ'` be forms on `E` such that the inversion pulls `τ'` back to `τ` on the shell
`R < ‖w‖ < R'⁻¹`.

Two facts about any complementary pair come first: `s w = s' (inversion 0 1 w)` for `w ≠ 0`
(`TauCeti.IsComplementaryBall.apply_eq_inversion_symm`), and `s' 0` is not in the range of `s`
(`TauCeti.IsComplementaryBall.apply_zero_notMem_range`).

The form `TauCeti.RoughForm.glue` of `τ` along `s` on `ball 0 R'⁻¹` and of `τ'` along `s'` pulls
back along `s'` to `τ'` on `ball 0 R⁻¹`
(`TauCeti.IsComplementaryBall.mpullback_glue_apply_of_mem_ball`): a point of `ball 0 R⁻¹` whose
image lies in `s '' ball 0 R'⁻¹` is a point `w ≠ 0` whose inversion lies in the shell, and there
`s' = s ∘ inversion 0 1` near `w`, so that the chain rule and the agreement on the shell give
the value. Since the two images `s '' ball 0 R'⁻¹` and `s' '' ball 0 R⁻¹` cover `N`, the glued
form is smooth (`TauCeti.RoughForm.isSmoothForm_glue`), which gives a smooth form `η` on `N` that
pulls back to `τ` along `s` on `ball 0 R'⁻¹` and to `τ'` along `s'` on `ball 0 R⁻¹`
(`TauCeti.IsComplementaryBall.exists_smoothForm_mpullback_eq`). For two-forms, `η` is
nondegenerate when `τ` and `τ'` are
(`TauCeti.IsComplementaryBall.exists_isNondegenerate_mpullback_eq`), since the differentials of
`s` and `s'` are invertible
(`TauCeti.SmoothTwoForm.nondegenerate_bilinFormAt_iff_of_isInvertible_mfderiv`).

The construction follows that of `SymplecticGeometry.GluedAlong.gluedForm`, where the two pieces
are glued along a diffeomorphism of open subsets rather than by the inversion.
-/

public section

open Set Filter EuclideanGeometry
open scoped Manifold Topology ContDiff

namespace TauCeti.IsComplementaryBall

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}
  {s s' : E → N} {R R' : ℝ}

omit [ChartedSpace H N] in
/-- For complementary balls `s` and `s'`, the first ball is the complementary one read through
the inversion away from the centre: `s w = s' (inversion 0 1 w)` for `w ≠ 0`. -/
theorem apply_eq_inversion_symm (h : IsComplementaryBall s s') {w : E} (hw : w ≠ 0) :
    s w = s' (inversion 0 1 w) := by
  rw [h.apply_eq_inversion _ fun h0 ↦ hw ((inversion_eq_center one_ne_zero).1 h0),
    inversion_inversion _ one_ne_zero]

omit [ChartedSpace H N] in
/-- For complementary balls `s` and `s'`, the centre `s' 0` of the complementary ball is not in
the range of the first ball. -/
theorem apply_zero_notMem_range (h : IsComplementaryBall s s') : s' 0 ∉ range s := by
  rintro ⟨x, hx⟩
  have hne : s' 0 ≠ s 0 := by
    have : s' 0 ∈ range s' := mem_range_self 0
    rwa [h.range_eq] at this
  rcases eq_or_ne x 0 with rfl | hx0
  · exact hne hx.symm
  · rw [h.apply_eq_inversion_symm hx0] at hx
    exact hx0 ((inversion_eq_center one_ne_zero).1 (h.isOpenEmbedding.injective hx))

omit [ChartedSpace H N] in
/-- Let `0 < R`, `0 < R'` with `R * R' < 1`. For complementary balls `s` and `s'`, a point off
`s '' ball 0 R'⁻¹` is in `s' '' ball 0 R⁻¹`, so that the two images cover `N`. -/
theorem mem_image_ball_of_notMem_image_ball (h : IsComplementaryBall s s') (hR : 0 < R)
    (hR' : 0 < R') (hRR' : R * R' < 1) {z : N} (hz : z ∉ s '' Metric.ball 0 R'⁻¹) :
    z ∈ s' '' Metric.ball 0 R⁻¹ := by
  -- The point is not `s 0`, so it is `s' y`, and `y` is `0` or its inversion lies outside
  -- `ball 0 R'⁻¹`, so that `‖y‖ ≤ R' < R⁻¹`.
  have hz0 : z ∈ range s' := by
    rw [h.range_eq]
    rintro rfl
    exact hz ⟨0, Metric.mem_ball_self (inv_pos.2 hR'), rfl⟩
  obtain ⟨y, rfl⟩ := hz0
  refine ⟨y, ?_, rfl⟩
  rw [mem_ball_zero_iff]
  rcases eq_or_ne y 0 with rfl | hy0
  · simpa using hR
  have hy : ‖y‖ ≤ R' := le_of_not_gt fun hy ↦ hz ⟨inversion 0 1 y,
    mem_ball_zero_iff.2 ((norm_inversion_lt_inv_iff hR' hy0).2 hy),
    (h.apply_eq_inversion y hy0).symm⟩
  exact hy.trans_lt (lt_of_mul_lt_mul_left (by rwa [mul_inv_cancel₀ hR.ne']) hR.le)

/-- Let `s` and `s'` be complementary balls, both smooth local diffeomorphisms, and let the
inversion pull `τ'` back to `τ` on the shell `R < ‖w‖ < R'⁻¹`. Then the form glued from `τ`
along `s` on `ball 0 R'⁻¹` and from `τ'` along `s'` pulls back along `s'` to `τ'` at each point
of `ball 0 R⁻¹`. -/
theorem mpullback_glue_apply_of_mem_ball [IsManifold I 1 N] (h : IsComplementaryBall s s')
    (hs : IsLocalDiffeomorph 𝓘(ℝ, E) I ∞ s) (hs' : IsLocalDiffeomorph 𝓘(ℝ, E) I ∞ s')
    {τ τ' : RoughForm 𝓘(ℝ, E) E F k}
    (hτ : ∀ w, R < ‖w‖ → ‖w‖ < R'⁻¹ →
      mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) (inversion 0 1) τ' w = τ w)
    {w : E} (hw : w ∈ Metric.ball 0 R⁻¹) :
    mpullback 𝓘(ℝ, E) I s' (RoughForm.glue I s (Metric.ball 0 R'⁻¹) s' τ τ') w = τ' w := by
  have hinj' : Function.Injective s' := h.isOpenEmbedding.injective
  by_cases hmem : s' w ∈ s '' Metric.ball 0 R'⁻¹
  swap
  · exact RoughForm.mpullback_glue_apply_of_notMem hinj' hmem
      ((hs' w).isInvertible_mfderiv (by simp))
  obtain ⟨x, hx, hxw⟩ := hmem
  have hw0 : w ≠ 0 := by
    rintro rfl
    exact h.apply_zero_notMem_range ⟨x, hxw⟩
  have hv0 : inversion (0 : E) 1 w ≠ 0 := fun h0 ↦ hw0 ((inversion_eq_center one_ne_zero).1 h0)
  obtain rfl : x = inversion 0 1 w := h.injective (hxw.trans (h.apply_eq_inversion w hw0))
  have hRx : R < ‖inversion (0 : E) 1 w‖ := by
    rw [norm_inversion_zero_one]
    exact lt_inv_of_lt_inv₀ (norm_pos_iff.2 hw0) (mem_ball_zero_iff.1 hw)
  have hinvd : ∀ y : E, y ≠ 0 → MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (inversion 0 1) y :=
    fun y hy ↦ mdifferentiableAt_iff_differentiableAt.2
      ((contDiffAt_inversion (n := 1) hy).differentiableAt one_ne_zero)
  have hsx : mpullback 𝓘(ℝ, E) I s (RoughForm.glue I s (Metric.ball 0 R'⁻¹) s' τ τ')
      (inversion 0 1 w) = τ (inversion 0 1 w) :=
    RoughForm.mpullback_glue_apply_of_mem h.injective.injOn hx
      ((hs _).isInvertible_mfderiv (by simp))
  -- Near `w`, the ball `s'` is the ball `s` read through the inversion.
  have hev : s' =ᶠ[𝓝 w] s ∘ inversion 0 1 :=
    eventually_of_mem (isOpen_compl_singleton.mem_nhds hw0) fun y hy ↦ h.apply_eq_inversion y hy
  rw [hev.mpullback_eq, mpullback_comp_at (hinvd w hw0) ((hs _).mdifferentiableAt (by simp)),
    mpullback_apply_congr (hsx.trans (hτ _ hRx (mem_ball_zero_iff.1 hx)).symm),
    ← mpullback_comp_at (hinvd w hw0) (hinvd _ hv0),
    (inversion_involutive (0 : E) one_ne_zero).comp_self, mpullback_id]

/-- **Two forms that agree through the inversion glue along complementary balls.** Let `s` and
`s'` be complementary balls, both smooth local diffeomorphisms, let `0 < R`, `0 < R'` with
`R * R' < 1`, and let `τ`, `τ'` be smooth forms on `E` such that the inversion pulls `τ'` back to
`τ` on the shell `R < ‖w‖ < R'⁻¹`. Then there is a smooth form on `N` that pulls back along `s`
to `τ` on `ball 0 R'⁻¹` and along `s'` to `τ'` on `ball 0 R⁻¹`. -/
theorem exists_smoothForm_mpullback_eq [IsManifold I 1 N] (h : IsComplementaryBall s s')
    (hs : IsLocalDiffeomorph 𝓘(ℝ, E) I ∞ s) (hs' : IsLocalDiffeomorph 𝓘(ℝ, E) I ∞ s')
    (hR : 0 < R) (hR' : 0 < R') (hRR' : R * R' < 1) (τ τ' : SmoothForm 𝓘(ℝ, E) E F k)
    (hτ : ∀ w, R < ‖w‖ → ‖w‖ < R'⁻¹ →
      mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) (inversion 0 1) τ'.val w = τ.val w) :
    ∃ η : SmoothForm I N F k,
      (∀ w ∈ Metric.ball 0 R'⁻¹, mpullback 𝓘(ℝ, E) I s η.val w = τ.val w) ∧
        ∀ w ∈ Metric.ball 0 R⁻¹, mpullback 𝓘(ℝ, E) I s' η.val w = τ'.val w := by
  have h₂ := fun w (hw : w ∈ Metric.ball 0 R⁻¹) ↦
    h.mpullback_glue_apply_of_mem_ball hs hs' hτ hw
  refine ⟨⟨RoughForm.glue I s (Metric.ball 0 R'⁻¹) s' τ.val τ'.val,
    IsSmoothForm.mem_smoothBundleForms <| RoughForm.isSmoothForm_glue (by simp)
      Metric.isOpen_ball h.injective.injOn (hs.isLocalDiffeomorphOn _) τ.isSmoothForm
      τ'.isSmoothForm fun z hz ↦ ?_⟩, fun w hw ↦ ?_, h₂⟩
  · obtain ⟨y, hy, rfl⟩ := h.mem_image_ball_of_notMem_image_ball hR hR' hRR' hz
    exact ⟨y, rfl, hs' y, eventually_of_mem (Metric.isOpen_ball.mem_nhds hy) h₂⟩
  · exact RoughForm.mpullback_glue_apply_of_mem h.injective.injOn hw
      ((hs w).isInvertible_mfderiv (by simp))

/-- **Nondegenerate two-forms that agree through the inversion glue along complementary balls.**
In the setting of `exists_smoothForm_mpullback_eq`, if `τ` and `τ'` are nondegenerate two-forms,
then there is a nondegenerate two-form on `N` that pulls back along `s` to `τ` on `ball 0 R'⁻¹`
and along `s'` to `τ'` on `ball 0 R⁻¹`. -/
theorem exists_isNondegenerate_mpullback_eq [IsManifold I ∞ N] (h : IsComplementaryBall s s')
    (hs : IsLocalDiffeomorph 𝓘(ℝ, E) I ∞ s) (hs' : IsLocalDiffeomorph 𝓘(ℝ, E) I ∞ s')
    (hR : 0 < R) (hR' : 0 < R') (hRR' : R * R' < 1) {τ τ' : SmoothTwoForm 𝓘(ℝ, E) E}
    (hτn : τ.IsNondegenerate) (hτn' : τ'.IsNondegenerate)
    (hτ : ∀ w, R < ‖w‖ → ‖w‖ < R'⁻¹ →
      mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) (inversion 0 1) τ'.val w = τ.val w) :
    ∃ η : SmoothTwoForm I N, η.IsNondegenerate ∧
      (∀ w ∈ Metric.ball 0 R'⁻¹, mpullback 𝓘(ℝ, E) I s η.val w = τ.val w) ∧
        ∀ w ∈ Metric.ball 0 R⁻¹, mpullback 𝓘(ℝ, E) I s' η.val w = τ'.val w := by
  obtain ⟨η, h₁, h₂⟩ := h.exists_smoothForm_mpullback_eq hs hs' hR hR' hRR' τ τ' hτ
  refine ⟨η, SmoothTwoForm.isNondegenerate_iff_forall_ker_bilinFormAt_eq_bot.2 fun z ↦
    LinearMap.separatingLeft_iff_ker_eq_bot.1 (?_ : (η.bilinFormAt z).Nondegenerate).1, h₁, h₂⟩
  by_cases hz : z ∈ s '' Metric.ball 0 R'⁻¹
  · obtain ⟨x, hx, rfl⟩ := hz
    exact (SmoothTwoForm.nondegenerate_bilinFormAt_iff_of_isInvertible_mfderiv
      ((hs x).isInvertible_mfderiv (by simp)) (h₁ x hx)).2 (hτn.nondegenerate_bilinFormAt x)
  · obtain ⟨y, hy, rfl⟩ := h.mem_image_ball_of_notMem_image_ball hR hR' hRR' hz
    exact (SmoothTwoForm.nondegenerate_bilinFormAt_iff_of_isInvertible_mfderiv
      ((hs' y).isInvertible_mfderiv (by simp)) (h₂ y hy)).2 (hτn'.nondegenerate_bilinFormAt y)

end TauCeti.IsComplementaryBall

end
