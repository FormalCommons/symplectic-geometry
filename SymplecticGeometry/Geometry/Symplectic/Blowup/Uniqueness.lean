/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Blowup.Normalized.Class

/-!
# Uniqueness of the symplectic blowup: paths between forms and equal classes

Fix a normalization `hN : IsNormalizedAt σ J p₀ δ ψ₀` and two normalized ball embeddings
`hψ₁ : IsNormalizedBallEmbedding hN ψ₁ r₁ l₁ ε₁` and
`hψ₂ : IsNormalizedBallEmbedding hN ψ₂ r₂ l₂ ε₂`.
This file shows that their forms `ω̃_{ψ₁,l₁,ε₁}` and `ω̃_{ψ₂,l₂,ε₂}` on `Blowup hN.blowupChart`
are joined by a smooth family of symplectic forms, and that their de Rham classes have the same
image in real singular cohomology when the weights agree (McDuff–Salamon, Theorem 7.1.23).

## Main results

* `SymplecticGeometry.IsNormalizedBallEmbedding.ballLiftPartialDiffeomorph_eqOn`: two normalized
  ball embeddings that agree on `B(a)` have lifts that agree on `openNbhd n a`.
* `SymplecticGeometry.IsNormalizedBallEmbedding.normalizedBlowupForm_eq_of_eqOn`: two normalized
  ball embeddings with the same weight `l` and width `ε` that agree on a ball `B(a)` with
  `l + ε < a` give the same form on the blowup.
* `SymplecticGeometry.IsNormalizedBallEmbedding.exists_path_normalizedBlowupForm`: the forms of two
  normalized ball embeddings are the ends of a smooth path of symplectic forms on the blowup.
* `SymplecticGeometry.IsNormalizedBallEmbedding.deRhamHom_normalizedBlowupForm_eq_of_weight_eq`:
  for equal weights, the classes of the two forms have the same image in real cohomology.

## Implementation notes

For the path, both embeddings equal `ψ₀` on `B(a)`, `a = min ε₁ ε₂`. Take `l' = ε' = a / 3`.
Each `ψᵢ` stays normalized for the weights and widths on the segment from `(lᵢ, εᵢ)` to
`(l', ε')` (`IsNormalizedBallEmbedding.of_width_le`), and moving linearly along that segment
gives a smooth family of forms (`isSmoothFamily_normalizedBlowupForm`), as in
`exists_path_compatible`. The family of `ψ₁` ends, and the reversed family of `ψ₂` starts, at the
same form, by `normalizedBlowupForm_eq_of_eqOn`, so the two concatenate to a smooth family
(`IsSmoothFamily.glue_collaredHalves`).

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §7.1,
  Theorem 7.1.23.
-/

public section

noncomputable section

open Set Topology Metric
open scoped ContDiff Manifold TauCeti.ComplexManifold

namespace SymplecticGeometry

open TauCeti BlowupModel

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Fin (n + 1) → ℂ) M]
  [IsManifold 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ M]
  {σ : SmoothTwoForm 𝓘(ℝ, Fin (n + 1) → ℂ) M}
  {J : SmoothAlmostComplexStructure 𝓘(ℝ, Fin (n + 1) → ℂ) M} {p₀ : M} {δ : ℝ}
  {ψ₀ : StdSpace (Fin (n + 1)) → M} {hN : IsNormalizedAt σ J p₀ δ ψ₀}
  {ψ₁ ψ₂ : StdSpace (Fin (n + 1)) → M} {r₁ r₂ l₁ l₂ ε₁ ε₂ : ℝ}

namespace IsNormalizedBallEmbedding

/-- Two normalized ball embeddings for the same normalization that agree on the ball `B(a)`,
with `a` at most both radii, have lifts that agree on `openNbhd n a`. -/
theorem ballLiftPartialDiffeomorph_eqOn (hψ₁ : IsNormalizedBallEmbedding hN ψ₁ r₁ l₁ ε₁)
    (hψ₂ : IsNormalizedBallEmbedding hN ψ₂ r₂ l₂ ε₂) {a : ℝ} (h : EqOn ψ₁ ψ₂ (ball 0 a))
    (ha₁ : a ≤ r₁) (ha₂ : a ≤ r₂) :
    EqOn hψ₁.ballLiftPartialDiffeomorph hψ₂.ballLiftPartialDiffeomorph (openNbhd n a) := by
  intro y hy
  have hy₁ : y ∈ openNbhd n r₁ := openNbhd_mono ha₁ hy
  have hy₂ : y ∈ openNbhd n r₂ := openNbhd_mono ha₂ hy
  rw [hψ₁.ballLiftPartialDiffeomorph_apply ⟨y, hy₁⟩,
    hψ₂.ballLiftPartialDiffeomorph_apply ⟨y, hy₂⟩]
  by_cases h0 : y.blowdown = 0
  · have hyD : y ∈ exceptionalDivisor n := mem_exceptionalDivisor_iff.2 h0
    rw [hψ₁.ballLift_of_mem_openNbhd _ (exceptionalDivisor_subset_openNbhd hψ₁.width_pos hyD),
      hψ₂.ballLift_of_mem_openNbhd _ (exceptionalDivisor_subset_openNbhd hψ₂.width_pos hyD)]
  · rw [hψ₁.ballLift_of_blowdown_ne_zero _ h0, hψ₂.ballLift_of_blowdown_ne_zero _ h0]
    congr 2
    exact h (mem_ball_zero_iff.2 (mem_openNbhd_iff.1 hy))

/-- A normalized ball embedding stays normalized along the segment of weights and widths from
`(l, ε)` to any admissible `(l', ε')`. -/
private theorem of_lineMap {ψ : StdSpace (Fin (n + 1)) → M} {r l ε : ℝ}
    (hψ : IsNormalizedBallEmbedding hN ψ r l ε) {l' ε' : ℝ} (hl' : 0 < l') (hε' : 0 < ε')
    (hε'ε : ε' ≤ ε) (hr : l' + ε' < r) {s : ℝ} (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1) :
    IsNormalizedBallEmbedding hN ψ r ((1 - s) * l + s * l') ((1 - s) * ε + s * ε') := by
  have hl := hψ.weight_pos
  have hε := hψ.width_pos
  have hlr := hψ.weight_add_width_lt
  have h₂ : 0 ≤ 1 - s := sub_nonneg.2 hs₁
  refine hψ.of_width_le ?_ ?_ ?_ ?_
  · rcases hs₀.eq_or_lt with rfl | hs
    · simpa using hl
    · nlinarith [mul_nonneg h₂ hl.le, mul_pos hs hl']
  · rcases hs₀.eq_or_lt with rfl | hs
    · simpa using hε
    · nlinarith [mul_nonneg h₂ hε.le, mul_pos hs hε']
  · nlinarith [mul_nonneg h₂ hε.le]
  · rcases hs₀.eq_or_lt with rfl | hs
    · simpa using hlr
    · nlinarith [mul_le_mul_of_nonneg_left hlr.le h₂, mul_lt_mul_of_pos_left hr hs]

variable [T2Space M]

/-- Two normalized ball embeddings for the same normalization, with the same weight `l` and width
`ε`, that agree on a ball `B(a)` with `l + ε < a`, give the same form `ω̃_{ψ,l,ε}` on the blowup,
for every `k`. -/
theorem normalizedBlowupForm_eq_of_eqOn {l ε : ℝ} (hψ₁ : IsNormalizedBallEmbedding hN ψ₁ r₁ l ε)
    (hψ₂ : IsNormalizedBallEmbedding hN ψ₂ r₂ l ε) {a : ℝ} (h : EqOn ψ₁ ψ₂ (ball 0 a))
    (ha : l + ε < a) (k : ℝ → ℝ) :
    hψ₁.normalizedBlowupForm k = hψ₂.normalizedBlowupForm k := by
  by_cases hk : IsBlowupProfile l ε k
  swap
  · rw [hψ₁.normalizedBlowupForm_of_not hk, hψ₂.normalizedBlowupForm_of_not hk]
  set b := min a (min r₁ r₂)
  have hb : l + ε < b := lt_min ha (lt_min hψ₁.weight_add_width_lt hψ₂.weight_add_width_lt)
  have hEq := ballLiftPartialDiffeomorph_eqOn hψ₁ hψ₂ (h.mono (ball_subset_ball (min_le_left _ _)))
    ((min_le_right _ _).trans (min_le_left _ _)) ((min_le_right _ _).trans (min_le_right _ _))
  have hK := closedNbhd_subset_openNbhd (n := n) hb
  have himage : hψ₁.ballLiftPartialDiffeomorph '' closedNbhd n (l + ε) =
      hψ₂.ballLiftPartialDiffeomorph '' closedNbhd n (l + ε) :=
    (hEq.mono hK).image_eq
  refine hψ₂.eq_normalizedBlowupForm hk (fun y hy ↦ ?_) fun x hx ↦
    hψ₁.normalizedBlowupForm_eq_on_compl x (himage ▸ hx)
  by_cases hyb : y ∈ openNbhd n b
  · -- Near `y`, the two lifts agree.
    have hev : (hψ₂.ballLiftPartialDiffeomorph : BlowupModel n → Blowup hN.blowupChart) =ᶠ[𝓝 y]
        hψ₁.ballLiftPartialDiffeomorph :=
      Filter.eventuallyEq_of_mem ((isOpen_openNbhd b).mem_nhds hyb) fun z hz ↦ (hEq hz).symm
    rw [hev.mpullback_eq]
    exact hψ₁.normalizedBlowupForm_eq_on_ballLift hk y
      (openNbhd_mono ((min_le_right _ _).trans (min_le_left _ _)) hyb)
  · -- Off `openNbhd n b`, the lift of `ψ₂` avoids the image of `L(l + ε)` under that of `ψ₁`.
    have hyK : y ∉ closedNbhd n (l + ε) := fun hyK ↦ hyb (hK hyK)
    have hx : hψ₂.ballLiftPartialDiffeomorph y ∉
        hψ₁.ballLiftPartialDiffeomorph '' closedNbhd n (l + ε) := by
      rw [himage]
      rintro ⟨z, hz, hzy⟩
      have hz₂ : z ∈ openNbhd n r₂ :=
        openNbhd_mono ((min_le_right _ _).trans (min_le_right _ _)) (hK hz)
      refine hyK ((hψ₂.ballLiftPartialDiffeomorph.injOn (by simpa using hz₂)
        (by simpa using hy) hzy) ▸ hz)
    rw [mpullback_apply_congr (hψ₁.normalizedBlowupForm_eq_on_compl _ hx),
      hψ₂.mpullback_ballLiftPartialDiffeomorph_mpullback_blowdown hy,
      profileForm_eq_on_compl n hk y hyK]

/-- Along a smooth `ρ` with values in `[0, 1]`, the forms of a normalized ball embedding whose
weight and width run linearly towards `(l', ε')` are symplectic and smooth in time; they are
its own form where `ρ = 0`, and the form of weight `l'` and width `ε'` where `ρ = 1`. -/
private theorem exists_family_normalizedBlowupForm {ψ : StdSpace (Fin (n + 1)) → M} {r l ε : ℝ}
    (hψ : IsNormalizedBallEmbedding hN ψ r l ε) (hσ : σ.IsSymplectic) {l' ε' : ℝ} (hl' : 0 < l')
    (hε' : 0 < ε') (hε'ε : ε' ≤ ε) (hr : l' + ε' < r) {ρ : unitInterval → ℝ}
    (hρ : ContMDiff (𝓡∂ 1) 𝓘(ℝ) ∞ ρ) (hρ₀ : ∀ t, 0 ≤ ρ t) (hρ₁ : ∀ t, ρ t ≤ 1) :
    ∃ τ : unitInterval → SmoothTwoForm 𝓘(ℝ, Fin (n + 1) → ℂ) (Blowup hN.blowupChart),
      IsSmoothFamily (𝓡∂ 1) τ ∧ (∀ t, (τ t).IsSymplectic) ∧
      (∀ t, ρ t = 0 → τ t = hψ.normalizedBlowupForm) ∧
      ∀ t, ρ t = 1 → τ t = (hψ.of_width_le hl' hε' hε'ε hr).normalizedBlowupForm := by
  have hψt (t : unitInterval) : IsNormalizedBallEmbedding hN (fun z ↦ ψ ((t, z) : unitInterval ×
      StdSpace (Fin (n + 1))).2) r ((1 - ρ t) * l + ρ t * l') ((1 - ρ t) * ε + ρ t * ε') :=
    hψ.of_lineMap hl' hε' hε'ε hr (hρ₀ t) (hρ₁ t)
  have hsmooth (a b : ℝ) : ContMDiff (𝓡∂ 1) 𝓘(ℝ) ∞ fun t ↦ (1 - ρ t) * a + ρ t * b :=
    ((contMDiff_const.sub hρ).mul contMDiff_const).add (hρ.mul contMDiff_const)
  -- The form depends only on the weight and the width.
  have hcongr {l₁ ε₁ l₂ ε₂ : ℝ} (h₁ : IsNormalizedBallEmbedding hN ψ r l₁ ε₁)
      (h₂ : IsNormalizedBallEmbedding hN ψ r l₂ ε₂) (hl : l₁ = l₂) (hε : ε₁ = ε₂) :
      h₁.normalizedBlowupForm = h₂.normalizedBlowupForm := by
    subst hl hε
    rfl
  refine ⟨fun t ↦ (hψt t).normalizedBlowupForm,
    isSmoothFamily_normalizedBlowupForm hψt
      (isSymplecticBallFamily_const hψ.isSymplecticBallEmbedding) (hsmooth l l') (hsmooth ε ε'),
    fun t ↦ (hψt t).isSymplectic_normalizedBlowupForm
      (isBlowupProfile_blowupProfile (hψt t).weight_pos (hψt t).width_pos) hσ,
    fun t ht ↦ hcongr _ _ (by simp [ht]) (by simp [ht]),
    fun t ht ↦ hcongr _ _ (by simp [ht]) (by simp [ht])⟩

/-- **The forms of two normalized ball embeddings are joined by a path of symplectic forms.**
Let `M` be Hausdorff, `σ` symplectic, and `ψ₁`, `ψ₂` normalized ball embeddings, for the same
normalization, of radii `rᵢ`, weights `lᵢ` and widths `εᵢ`. There is a smooth family `τ` of
symplectic two-forms on the blowup, over `t ∈ unitInterval`, with `τ 0 = ω̃_{ψ₁,l₁,ε₁}` and
`τ 1 = ω̃_{ψ₂,l₂,ε₂}`, for the profiles `blowupProfile lᵢ εᵢ`. The class of `τ t` may change with
`t`. -/
theorem exists_path_normalizedBlowupForm (hψ₁ : IsNormalizedBallEmbedding hN ψ₁ r₁ l₁ ε₁)
    (hψ₂ : IsNormalizedBallEmbedding hN ψ₂ r₂ l₂ ε₂) (hσ : σ.IsSymplectic) :
    ∃ τ : unitInterval → SmoothTwoForm 𝓘(ℝ, Fin (n + 1) → ℂ) (Blowup hN.blowupChart),
      IsSmoothFamily (𝓡∂ 1) τ ∧ (∀ t, (τ t).IsSymplectic) ∧ τ 0 = hψ₁.normalizedBlowupForm ∧
      τ 1 = hψ₂.normalizedBlowupForm := by
  -- The common small weight and width.
  set a := min ε₁ ε₂
  have ha : 0 < a := lt_min hψ₁.width_pos hψ₂.width_pos
  have hl' : 0 < a / 3 := by positivity
  have h₁ : a / 3 ≤ ε₁ := by linarith [min_le_left ε₁ ε₂]
  have h₂ : a / 3 ≤ ε₂ := by linarith [min_le_right ε₁ ε₂]
  have hr₁ : a / 3 + a / 3 < r₁ := by linarith [min_le_left ε₁ ε₂, hψ₁.width_lt_radius]
  have hr₂ : a / 3 + a / 3 < r₂ := by linarith [min_le_right ε₁ ε₂, hψ₂.width_lt_radius]
  have hid : ContMDiff (𝓡∂ 1) 𝓘(ℝ) ∞ fun t : unitInterval ↦ (t : ℝ) := contMDiff_subtypeVal_Icc
  obtain ⟨τ₁, hτ₁, hτ₁s, hτ₁0, hτ₁1⟩ := hψ₁.exists_family_normalizedBlowupForm hσ hl' hl' h₁ hr₁
    hid unitInterval.nonneg unitInterval.le_one
  obtain ⟨τ₂, hτ₂, hτ₂s, hτ₂0, hτ₂1⟩ := hψ₂.exists_family_normalizedBlowupForm hσ hl' hl' h₂ hr₂
    (contMDiff_const.sub hid) (fun t ↦ sub_nonneg.2 (unitInterval.le_one t))
    fun t ↦ by linarith [unitInterval.nonneg t]
  -- The two families meet at the weight and width `a / 3`, where both embeddings are `ψ₀`.
  have hmid : τ₁ 1 = τ₂ 0 := by
    rw [hτ₁1 1 Set.Icc.coe_one, hτ₂1 0 (by simp)]
    refine normalizedBlowupForm_eq_of_eqOn _ _ (a := a) (fun z hz ↦ ?_) (by linarith) _
    have hz := mem_ball_zero_iff.1 hz
    exact (hψ₁.eqOn (mem_closedBall_zero_iff.2 (by linarith [min_le_left ε₁ ε₂]))).trans
      (hψ₂.eqOn (mem_closedBall_zero_iff.2 (by linarith [min_le_right ε₁ ε₂]))).symm
  refine ⟨collaredConcat τ₁ τ₂, hτ₁.glue_collaredHalves hτ₂ hmid, fun t ↦ ?_,
    (collaredConcat_zero τ₁ τ₂).trans (hτ₁0 0 Set.Icc.coe_zero),
    (collaredConcat_one τ₁ τ₂).trans (hτ₂0 1 (by simp))⟩
  rcases le_or_gt (t : ℝ) (1 / 2) with h | h
  · exact collaredConcat_of_le h ▸ hτ₁s _
  · exact collaredConcat_of_lt h ▸ hτ₂s _

/-- **Equal weights give equal classes.** Let `M` be Hausdorff, second countable and σ-compact,
`σ` symplectic, and `ψ₁`, `ψ₂` normalized ball embeddings, for the same normalization, of weights
`l₁`, `l₂`, with profiles `h₁`, `h₂` of the blowup. If `l₁ = l₂`, the classes of the forms
`ω̃_{ψ₁,l₁,ε₁}` and `ω̃_{ψ₂,l₂,ε₂}` have the same image under `TauCeti.deRhamHom` in
`H²(Blowup; ℝ)`. -/
theorem deRhamHom_normalizedBlowupForm_eq_of_weight_eq [SecondCountableTopology M]
    [SigmaCompactSpace M] (hψ₁ : IsNormalizedBallEmbedding hN ψ₁ r₁ l₁ ε₁)
    (hψ₂ : IsNormalizedBallEmbedding hN ψ₂ r₂ l₂ ε₂) {h₁ h₂ : ℝ → ℝ}
    (hh₁ : IsBlowupProfile l₁ ε₁ h₁) (hh₂ : IsBlowupProfile l₂ ε₂ h₂) (hσ : σ.IsSymplectic)
    (hl : l₁ = l₂) :
    deRhamHom 𝓘(ℝ, Fin (n + 1) → ℂ) (Blowup hN.blowupChart) 2
        (deRhamCohomology.mk _ 2 ⟨hψ₁.normalizedBlowupForm h₁,
          (hψ₁.isSymplectic_normalizedBlowupForm hh₁ hσ).isClosed.mem_closedForms⟩) =
      deRhamHom 𝓘(ℝ, Fin (n + 1) → ℂ) (Blowup hN.blowupChart) 2
        (deRhamCohomology.mk _ 2 ⟨hψ₂.normalizedBlowupForm h₂,
          (hψ₂.isSymplectic_normalizedBlowupForm hh₂ hσ).isClosed.mem_closedForms⟩) := by
  rw [hψ₁.deRhamHom_normalizedBlowupForm hh₁ hσ, hψ₂.deRhamHom_normalizedBlowupForm hh₂ hσ, hl]

end IsNormalizedBallEmbedding

end SymplecticGeometry

end
