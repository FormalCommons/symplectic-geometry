/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Blowup.Normalized.Class
import SymplecticGeometry.Geometry.Symplectic.Manifold.LiouvilleMeasure
import SymplecticGeometry.Geometry.Symplectic.Manifold.Volume
import TauCeti.Geometry.Manifold.SmoothSingular.DeRham.Equiv

/-!
# Uniqueness of the symplectic blowup: paths between forms and equal classes

Fix a normalization `hN : IsNormalizedAt σ J p₀ δ ψ₀` and two normalized ball embeddings
`hψ₁ : IsNormalizedBallEmbedding hN ψ₁ r₁ l₁ ε₁` and
`hψ₂ : IsNormalizedBallEmbedding hN ψ₂ r₂ l₂ ε₂`.
This file shows that their forms `ω̃_{ψ₁,l₁,ε₁}` and `ω̃_{ψ₂,l₂,ε₂}` on `Blowup hN.blowupChart`
are joined by a smooth family of symplectic forms, and that their de Rham classes have the same
image in real singular cohomology when the weights agree, and only then when `1 ≤ n` or when
`n = 0` and `M` is compact (McDuff–Salamon, Theorem 7.1.23).

## Main results

* `SymplecticGeometry.IsNormalizedBallEmbedding.exists_path_normalizedBlowupForm`: the forms of two
  normalized ball embeddings are the ends of a smooth path of symplectic forms on the blowup.
* `SymplecticGeometry.IsNormalizedBallEmbedding.deRhamHom_normalizedBlowupForm_eq_of_weight_eq`:
  for equal weights, the classes of the two forms have the same image in real cohomology.
* `SymplecticGeometry.IsNormalizedBallEmbedding.deRhamHom_normalizedBlowupForm_eq_iff`: for
  `1 ≤ n`, the two images agree if and only if `l₁ = l₂`.
* `IsNormalizedBallEmbedding.deRhamHom_normalizedBlowupForm_eq_iff_of_compactSpace`: for `n = 0`
  and compact `M`, the two images agree if and only if `l₁ = l₂`.

## Implementation notes

For the path, both embeddings equal `ψ₀` on `B(a)`, `a = min ε₁ ε₂`. Take `l' = ε' = a / 3`.
Moving each `ψᵢ` linearly in weight and width from `(lᵢ, εᵢ)` to `(l', ε')` gives a smooth
family of symplectic forms (`IsNormalizedBallEmbedding.exists_family_normalizedBlowupForm`).
The family of `ψ₁` ends, and the reversed family of `ψ₂` starts, at the same form, by
`IsNormalizedBallEmbedding.normalizedBlowupForm_eq_of_eqOn`, so the two concatenate to a smooth
family (`IsSmoothFamily.glue_collaredHalves`).

For the converse, by `IsNormalizedBallEmbedding.deRhamHom_normalizedBlowupForm` the two images
differ by `π (l₁² - l₂²)` times the real image of `Blowup.exceptionalClass`, which is not zero for
`1 ≤ n` (`Blowup.singularCohomologyRealImageAddMonoidHom_exceptionalClass_ne_zero`); the weights
are positive, so `l₁ = l₂`.

For `n = 0` this argument does not apply, and the total area decides instead. The images agree
for the default profiles too, as they do not depend on the profile, so by the de Rham theorem
(`TauCeti.bijective_deRhamHom`) the default forms have the same de Rham class. Both forms carry
the same symplectic orientation `o`, which is constant along the path above
(`TauCeti.SmoothTwoForm.volumeOrientation_eq_of_isSmoothFamily`). On the compact blowup, two such
forms have the same total Liouville measure
(`TauCeti.SmoothTwoForm.liouvilleMeasure_univ_eq_of_mk_eq`, which integrates the class against
`o`). That measure is the area of `σ` minus the volume of `B(lᵢ)`
(`SymplecticGeometry.IsNormalizedBallEmbedding.liouvilleMeasure_normalizedBlowupForm_add`),
finite on compact `M`, and the volume `π lᵢ²` of the disc determines `lᵢ > 0`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §7.1,
  Theorem 7.1.23.
-/

public section

noncomputable section

open Set Topology Metric MeasureTheory Module
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

variable [T2Space M]

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

/-- **Normalized blowup forms have equal classes exactly for equal weights.** Let `M` be
Hausdorff, second countable and σ-compact, of complex dimension `n + 1 ≥ 2`, `σ` symplectic, and
`ψ₁`, `ψ₂` normalized ball embeddings, for the same normalization, of weights `l₁`, `l₂`, with
profiles `h₁`, `h₂` of the blowup. The classes of the forms `ω̃_{ψ₁,l₁,ε₁}` and `ω̃_{ψ₂,l₂,ε₂}`
have the same image under `TauCeti.deRhamHom` in `H²(Blowup; ℝ)` if and only if `l₁ = l₂`. -/
theorem deRhamHom_normalizedBlowupForm_eq_iff [SecondCountableTopology M]
    [SigmaCompactSpace M] (hψ₁ : IsNormalizedBallEmbedding hN ψ₁ r₁ l₁ ε₁)
    (hψ₂ : IsNormalizedBallEmbedding hN ψ₂ r₂ l₂ ε₂) {h₁ h₂ : ℝ → ℝ}
    (hh₁ : IsBlowupProfile l₁ ε₁ h₁) (hh₂ : IsBlowupProfile l₂ ε₂ h₂) (hσ : σ.IsSymplectic)
    (hn : 1 ≤ n) :
    deRhamHom 𝓘(ℝ, Fin (n + 1) → ℂ) (Blowup hN.blowupChart) 2
        (deRhamCohomology.mk _ 2 ⟨hψ₁.normalizedBlowupForm h₁,
          (hψ₁.isSymplectic_normalizedBlowupForm hh₁ hσ).isClosed.mem_closedForms⟩) =
      deRhamHom 𝓘(ℝ, Fin (n + 1) → ℂ) (Blowup hN.blowupChart) 2
        (deRhamCohomology.mk _ 2 ⟨hψ₂.normalizedBlowupForm h₂,
          (hψ₂.isSymplectic_normalizedBlowupForm hh₂ hσ).isClosed.mem_closedForms⟩) ↔
      l₁ = l₂ := by
  refine ⟨fun h ↦ ?_, hψ₁.deRhamHom_normalizedBlowupForm_eq_of_weight_eq hψ₂ hh₁ hh₂ hσ⟩
  rw [hψ₁.deRhamHom_normalizedBlowupForm hh₁ hσ, hψ₂.deRhamHom_normalizedBlowupForm hh₂ hσ,
    add_right_inj] at h
  have h' := smul_left_injective ℝ
    (Blowup.singularCohomologyRealImageAddMonoidHom_exceptionalClass_ne_zero _ hn) h
  rw [mul_right_inj' Real.pi_ne_zero] at h'
  exact (pow_left_inj₀ hψ₁.weight_pos.le hψ₂.weight_pos.le two_ne_zero).1 h'

/-- **On a compact surface, normalized blowup forms have equal classes exactly for equal
weights.** Let `M` be compact, Hausdorff and second countable, of complex dimension `n + 1 = 1`,
`σ` symplectic, and `ψ₁`, `ψ₂` normalized ball embeddings, for the same normalization, of weights
`l₁`, `l₂`, with profiles `h₁`, `h₂` of the blowup. The classes of the forms `ω̃_{ψ₁,l₁,ε₁}` and
`ω̃_{ψ₂,l₂,ε₂}` have the same image under `TauCeti.deRhamHom` in `H²(Blowup; ℝ)` if and only if
`l₁ = l₂`. -/
theorem deRhamHom_normalizedBlowupForm_eq_iff_of_compactSpace [SecondCountableTopology M]
    [CompactSpace M] (hψ₁ : IsNormalizedBallEmbedding hN ψ₁ r₁ l₁ ε₁)
    (hψ₂ : IsNormalizedBallEmbedding hN ψ₂ r₂ l₂ ε₂) {h₁ h₂ : ℝ → ℝ}
    (hh₁ : IsBlowupProfile l₁ ε₁ h₁) (hh₂ : IsBlowupProfile l₂ ε₂ h₂) (hσ : σ.IsSymplectic)
    (hn : n = 0) :
    deRhamHom 𝓘(ℝ, Fin (n + 1) → ℂ) (Blowup hN.blowupChart) 2
        (deRhamCohomology.mk _ 2 ⟨hψ₁.normalizedBlowupForm h₁,
          (hψ₁.isSymplectic_normalizedBlowupForm hh₁ hσ).isClosed.mem_closedForms⟩) =
      deRhamHom 𝓘(ℝ, Fin (n + 1) → ℂ) (Blowup hN.blowupChart) 2
        (deRhamCohomology.mk _ 2 ⟨hψ₂.normalizedBlowupForm h₂,
          (hψ₂.isSymplectic_normalizedBlowupForm hh₂ hσ).isClosed.mem_closedForms⟩) ↔
      l₁ = l₂ := by
  refine ⟨fun h ↦ ?_, hψ₁.deRhamHom_normalizedBlowupForm_eq_of_weight_eq hψ₂ hh₁ hh₂ hσ⟩
  subst hn
  have hk : finrank ℝ (Fin (0 + 1) → ℂ) = 2 * 1 := by simp [finrank_pi_fintype]
  have : Fact (finrank ℝ (Fin (0 + 1) → ℂ) = 2 * 1) := ⟨hk⟩
  borelize M (Blowup hN.blowupChart)
  -- The images do not depend on the profiles, so those of the default forms agree, and by the de
  -- Rham theorem so do the classes of the default forms.
  have hb₁ := isBlowupProfile_blowupProfile hψ₁.weight_pos hψ₁.width_pos
  have hb₂ := isBlowupProfile_blowupProfile hψ₂.weight_pos hψ₂.width_pos
  rw [hψ₁.deRhamHom_normalizedBlowupForm hh₁ hσ, hψ₂.deRhamHom_normalizedBlowupForm hh₂ hσ,
    ← hψ₁.deRhamHom_normalizedBlowupForm hb₁ hσ, ← hψ₂.deRhamHom_normalizedBlowupForm hb₂ hσ] at h
  have hmk := (bijective_deRhamHom _ _ 2).1 h
  -- The two forms have the same symplectic orientation, which is constant along the path
  -- between them.
  have hω₁ := (hψ₁.isSymplectic_normalizedBlowupForm hb₁ hσ).isNondegenerate
  have hω₂ := (hψ₂.isSymplectic_normalizedBlowupForm hb₂ hσ).isNondegenerate
  have ho : hω₁.volumeOrientation hk = hω₂.volumeOrientation hk := by
    obtain ⟨τ, hτ, hτs, hτ0, hτ1⟩ := hψ₁.exists_path_normalizedBlowupForm hψ₂ hσ
    have := SmoothTwoForm.volumeOrientation_eq_of_isSmoothFamily hτ
      (fun t ↦ (hτs t).isNondegenerate) hk 0 1
    -- The proofs of nondegeneracy depend on the forms, so generalize them before rewriting.
    revert hω₁ hω₂
    rw [← hτ0, ← hτ1]
    exact fun _ _ ↦ this
  -- On the compact blowup, the two forms therefore have the same total area.
  have hA := SmoothTwoForm.liouvilleMeasure_univ_eq_of_mk_eq hω₁ hω₂ _ _ ho hmk
  -- Each area is that of `σ` minus the volume of the ball `B(lᵢ)`, which is `lᵢ²` times that of
  -- the unit ball.
  have hV := (hψ₁.liouvilleMeasure_normalizedBlowupForm_add (m := 1) hb₁).trans
    (hψ₂.liouvilleMeasure_normalizedBlowupForm_add (m := 1) hb₂).symm
  rw [hA, ENNReal.add_right_inj (measure_ne_top _ _),
    Measure.addHaar_closedBall _ _ hψ₁.weight_pos.le,
    Measure.addHaar_closedBall _ _ hψ₂.weight_pos.le,
    ENNReal.mul_left_inj (measure_ball_pos _ _ one_pos).ne' measure_ball_lt_top.ne,
    ENNReal.ofReal_eq_ofReal_iff (pow_nonneg hψ₁.weight_pos.le _)
      (pow_nonneg hψ₂.weight_pos.le _)] at hV
  exact (pow_left_inj₀ hψ₁.weight_pos.le hψ₂.weight_pos.le (by simp)).1 hV

end IsNormalizedBallEmbedding

end SymplecticGeometry

end
