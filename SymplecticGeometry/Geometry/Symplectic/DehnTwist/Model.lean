/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.DehnTwist.Geodesic
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import SymplecticGeometry.Analysis.Calculus.ContDiff.Even

/-!
# The model Dehn twist on the cotangent bundle of the sphere

Let `μ = cotangentNorm` be the norm of a covector on the unit sphere `Sⁿ ⊆ ℝⁿ⁺¹` and `σ_t` the
normalized geodesic flow `geodesicFlow t` of `T*Sⁿ`. A *twist profile* with support radius `r₀`
is a smooth function `R : ℝ → ℝ` with `R (-t) = R t - t` that vanishes on `[r₀, ∞)`. The model
Dehn twist of such a profile is the map
`z ↦ σ_{2π R'(μ z)} z` off the zero section, extended by the antipodal map on the zero section.
Since `R'(0) = 1 / 2`, the time `2π R'(μ z)` tends to `π` at the zero section, where the flow at
time `π` is the antipodal map; and since `R' = 0` on `[r₀, ∞)`, the twist is the identity where
`μ ≥ r₀`.

## Main definitions

* `SymplecticGeometry.IsTwistProfile R r₀`: `R` is a twist profile with support radius `r₀`.
* `SymplecticGeometry.modelTwistFun R`: the model twist as a function of `T*Sⁿ`.
* `SymplecticGeometry.modelTwist hR`: the model twist of a twist profile, as a diffeomorphism.

## Main results

* `SymplecticGeometry.IsTwistProfile.deriv_zero`, `SymplecticGeometry.IsTwistProfile.pos`,
  `SymplecticGeometry.IsTwistProfile.deriv_eq_zero`: `R'(0) = 1 / 2`, so `0 < r₀`, and `R'`
  vanishes on `[r₀, ∞)`.
* `SymplecticGeometry.IsTwistProfile.lineMap`: twist profiles of the same radius form an affine
  subspace; `SymplecticGeometry.exists_isTwistProfile`: there is one for every `r₀ > 0`.
* `SymplecticGeometry.modelTwist_apply_of_le`: the model twist is the identity where `μ ≥ r₀`.
* `SymplecticGeometry.modelTwist_cotangent_orthogonal`: it commutes with the cotangent lift of
  every orthogonal transformation of `ℝⁿ⁺¹`.

## Implementation notes

Write `θ = 2π R'`. From `R (-t) = R t - t` one gets `R'(-t) = 1 - R'(t)`, so `cos ∘ θ` is even
and `sin ∘ θ` is odd. By Whitney's theorem (`Function.Even.exists_contDiff_comp_sq`,
`Function.Odd.exists_contDiff_mul_comp_sq`) they are `C (t ^ 2)` and `t * S (t ^ 2)` with `C`
and `S` smooth. By `cotangentCoord_geodesicFlow`, the twist then reads, in the coordinates
`(q, p)` of `cotangentCoord`,
`(q, p) ↦ (C ‖p‖² • q + S ‖p‖² • p, C ‖p‖² • p - (‖p‖² * S ‖p‖²) • q)`,
also on the zero section, where `C 0 = cos π = -1`. This is a smooth map of `(q, p)`, so the twist
is smooth (`contMDiff_of_contMDiff_cotangentCoord_comp`). The inverse is the same construction
with `-θ` in place of `θ`, as the flow preserves `μ`. The same coordinate formula gives the
equivariance under `O(n + 1)`, which acts on the coordinates by isometries.

## References

* [P. Seidel, *A long exact sequence for symplectic Floer cohomology*][Seidel2003], Lemma 1.8
  and equation (1.7) (arXiv version 2): the model twist on `T*Sⁿ` built from the normalized
  geodesic flow.
* [P. Seidel, *Lectures on four-dimensional Dehn twists*][Seidel2008], §1a.
* [V. I. Arnold, *Some remarks on symplectic monodromy of Milnor fibrations*][Arnold1995], one of
  the early sources on twists of `T*Sⁿ`.
* H. Whitney, *Differentiable even functions*, Duke Math. J. 10 (1943), 159–160.
-/

public section

noncomputable section

namespace SymplecticGeometry

open Bundle Metric Set TauCeti Real
open scoped Manifold ContDiff InnerProductSpace

variable {n : ℕ}

/-- The Euclidean space `ℝⁿ⁺¹` containing the unit sphere `Sⁿ`. -/
local notation "𝔼" n => EuclideanSpace ℝ (Fin (n + 1))

/-- The unit sphere `Sⁿ` of `ℝⁿ⁺¹`. -/
local notation "𝕊" n => sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

/-! ### Twist profiles -/

/-- `R` is a profile of a model Dehn twist with support radius `r₀`: a smooth function with
`R (-t) = R t - t` everywhere, vanishing on `[r₀, ∞)`. -/
def IsTwistProfile (R : ℝ → ℝ) (r₀ : ℝ) : Prop :=
  ContDiff ℝ ∞ R ∧ (∀ t, R (-t) = R t - t) ∧ ∀ t, r₀ ≤ t → R t = 0

theorem isTwistProfile_iff {R : ℝ → ℝ} {r₀ : ℝ} :
    IsTwistProfile R r₀ ↔ ContDiff ℝ ∞ R ∧ (∀ t, R (-t) = R t - t) ∧ ∀ t, r₀ ≤ t → R t = 0 :=
  Iff.rfl

namespace IsTwistProfile

variable {R R₀ R₁ : ℝ → ℝ} {r₀ : ℝ}

theorem contDiff (hR : IsTwistProfile R r₀) : ContDiff ℝ ∞ R :=
  hR.1

theorem apply_neg (hR : IsTwistProfile R r₀) (t : ℝ) : R (-t) = R t - t :=
  hR.2.1 t

theorem apply_of_le (hR : IsTwistProfile R r₀) {t : ℝ} (ht : r₀ ≤ t) : R t = 0 :=
  hR.2.2 t ht

/-- The derivative of a twist profile is smooth. -/
theorem contDiff_deriv (hR : IsTwistProfile R r₀) : ContDiff ℝ ∞ (deriv R) :=
  (contDiff_infty_iff_deriv.1 hR.contDiff).2

/-- The derivative of a twist profile satisfies `R'(-t) = 1 - R'(t)`. -/
theorem deriv_neg (hR : IsTwistProfile R r₀) (t : ℝ) : deriv R (-t) = 1 - deriv R t := by
  have hd : Differentiable ℝ R := hR.contDiff.differentiable (by simp)
  have h := congrArg (fun f ↦ deriv f t) (funext hR.apply_neg)
  simp only [deriv_comp_neg] at h
  rw [show deriv (fun x ↦ R x - x) t = deriv R t - 1 from
    ((hd t).hasDerivAt.sub (hasDerivAt_id' t)).deriv] at h
  linarith

/-- The derivative of a twist profile at `0` is `1 / 2`. -/
theorem deriv_zero (hR : IsTwistProfile R r₀) : deriv R 0 = 1 / 2 := by
  have h := hR.deriv_neg 0
  rw [neg_zero] at h
  linarith

/-- The derivative of a twist profile vanishes on `[r₀, ∞)`. -/
theorem deriv_eq_zero (hR : IsTwistProfile R r₀) {t : ℝ} (ht : r₀ ≤ t) : deriv R t = 0 := by
  have hd : Differentiable ℝ R := hR.contDiff.differentiable (by simp)
  have h₀ : HasDerivWithinAt R 0 (Ici r₀) t :=
    (hasDerivWithinAt_const t (Ici r₀) (0 : ℝ)).congr (fun s hs ↦ hR.apply_of_le hs)
      (hR.apply_of_le ht)
  exact (uniqueDiffOn_Ici r₀ t ht).eq_deriv _ (hd t).hasDerivAt.hasDerivWithinAt h₀

/-- The support radius of a twist profile is positive, since `R'(0) = 1 / 2` while `R'` vanishes
on `[r₀, ∞)`. -/
theorem pos (hR : IsTwistProfile R r₀) : 0 < r₀ := by
  by_contra h
  have h₀ := hR.deriv_eq_zero (not_lt.1 h)
  rw [hR.deriv_zero] at h₀
  norm_num at h₀

/-- Twist profiles of the same support radius form an affine subspace: the combination
`(1 - s) R₀ + s R₁` is a twist profile for every real `s`, not only for `s ∈ [0, 1]`. -/
theorem lineMap (h₀ : IsTwistProfile R₀ r₀) (h₁ : IsTwistProfile R₁ r₀) (s : ℝ) :
    IsTwistProfile (fun t ↦ (1 - s) * R₀ t + s * R₁ t) r₀ := by
  refine ⟨(contDiff_const.mul h₀.contDiff).add (contDiff_const.mul h₁.contDiff),
    fun t ↦ ?_, fun t ht ↦ ?_⟩
  · dsimp only
    rw [h₀.apply_neg, h₁.apply_neg]
    ring
  · dsimp only
    rw [h₀.apply_of_le ht, h₁.apply_of_le ht]
    ring

end IsTwistProfile

/-- For every `r₀ > 0` there is a twist profile with support radius `r₀`: with `ρ` a smooth
function that is `0` on `(-∞, 0]` and `1` on `[r₀, ∞)`, take `R t = t * (1 - ρ t + ρ (-t)) / 2`. -/
theorem exists_isTwistProfile {r₀ : ℝ} (hr : 0 < r₀) : ∃ R, IsTwistProfile R r₀ := by
  let ρ : ℝ → ℝ := fun t ↦ smoothTransition (t / r₀)
  have hρ : ContDiff ℝ ∞ ρ := smoothTransition.contDiff.comp (contDiff_id.div_const r₀)
  refine ⟨fun t ↦ t * (1 - ρ t + ρ (-t)) / 2, ?_, fun t ↦ ?_, fun t ht ↦ ?_⟩
  · exact ((contDiff_id.mul ((contDiff_const.sub hρ).add
      (hρ.comp contDiff_neg))).div_const 2)
  · simp only [neg_neg]
    ring
  · have h1 : ρ t = 1 := smoothTransition.one_of_one_le ((one_le_div hr).2 ht)
    have h0 : ρ (-t) = 0 :=
      smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hr.le)
    dsimp only
    rw [h1, h0]
    ring

/-! ### Twisting along the geodesic flow by an angle function -/

/-- The map that moves a covector `z` off the zero section along the normalized geodesic flow for
the time `θ (μ z)`, and acts by the antipodal map on the zero section. -/
private def twistOfAngle (θ : ℝ → ℝ) (z : CotangentBundle (𝓡 n) (𝕊 n)) :
    CotangentBundle (𝓡 n) (𝕊 n) :=
  if cotangentNorm z = 0 then antipodal z else geodesicFlow (θ (cotangentNorm z)) z

private theorem cotangentNorm_twistOfAngle (θ : ℝ → ℝ) (z : CotangentBundle (𝓡 n) (𝕊 n)) :
    cotangentNorm (twistOfAngle θ z) = cotangentNorm z := by
  unfold twistOfAngle
  split_ifs
  · exact cotangentNorm_antipodal z
  · exact cotangentNorm_geodesicFlow _ z

/-- Twisting by `-θ` undoes twisting by `θ`. -/
private theorem twistOfAngle_neg_twistOfAngle (θ : ℝ → ℝ) (z : CotangentBundle (𝓡 n) (𝕊 n)) :
    twistOfAngle (fun t ↦ -θ t) (twistOfAngle θ z) = z := by
  have hn := cotangentNorm_twistOfAngle θ z
  unfold twistOfAngle at hn ⊢
  by_cases hz : cotangentNorm z = 0
  · rw [ite_eq_left hz] at hn ⊢
    rw [ite_eq_left (hn.trans hz)]
    refine cotangentCoord_injective ?_
    rw [cotangentCoord_antipodal, cotangentCoord_antipodal, neg_neg]
  · rw [ite_eq_right hz] at hn ⊢
    rw [ite_eq_right (hn.trans_ne hz), hn, ← geodesicFlow_add, neg_add_cancel, geodesicFlow_zero]

/-- If `cos ∘ θ = C (t ^ 2)` and `sin ∘ θ = t * S (t ^ 2)`, and `cos (θ 0) = -1`, then twisting
by `θ` acts on the coordinates `(q, p)` by
`(C ‖p‖² • q + S ‖p‖² • p, C ‖p‖² • p - (‖p‖² * S ‖p‖²) • q)`. -/
private theorem cotangentCoord_twistOfAngle {θ C S : ℝ → ℝ} (hC : ∀ t, cos (θ t) = C (t ^ 2))
    (hS : ∀ t, sin (θ t) = t * S (t ^ 2)) (h0 : cos (θ 0) = -1)
    (z : CotangentBundle (𝓡 n) (𝕊 n)) :
    cotangentCoord (twistOfAngle θ z) =
      (C (‖(cotangentCoord z).2‖ ^ 2) • (cotangentCoord z).1 +
          S (‖(cotangentCoord z).2‖ ^ 2) • (cotangentCoord z).2,
        C (‖(cotangentCoord z).2‖ ^ 2) • (cotangentCoord z).2 -
          (‖(cotangentCoord z).2‖ ^ 2 * S (‖(cotangentCoord z).2‖ ^ 2)) •
            (cotangentCoord z).1) := by
  unfold twistOfAngle
  by_cases hz : cotangentNorm z = 0
  · have hp : (cotangentCoord z).2 = 0 := norm_eq_zero.1 ((cotangentNorm_def z).symm.trans hz)
    have hC0 : C 0 = -1 := by rw [← h0, hC, sq, mul_zero]
    rw [ite_eq_left hz, cotangentCoord_antipodal, hp, norm_zero]
    ext1 <;> simp [hC0, hp]
  · rw [ite_eq_right hz, cotangentCoord_geodesicFlow hz, cotangentNorm_def, hC, hS]
    have hN : ‖(cotangentCoord z).2‖ ≠ 0 := (cotangentNorm_def z).symm.trans_ne hz
    ext1
    · simp only
      congr 2
      field_simp
    · simp only
      congr 2
      ring

/-- If `θ` is smooth, `cos ∘ θ` is even, `sin ∘ θ` is odd and `cos (θ 0) = -1`, then by Whitney's
theorem twisting by `θ` acts on the coordinates `(q, p)` by
`(C ‖p‖² • q + S ‖p‖² • p, C ‖p‖² • p - (‖p‖² * S ‖p‖²) • q)` for smooth `C` and `S`. -/
private theorem exists_cotangentCoord_twistOfAngle {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ)
    (hc : ∀ t, cos (θ (-t)) = cos (θ t)) (hs : ∀ t, sin (θ (-t)) = -sin (θ t))
    (h0 : cos (θ 0) = -1) :
    ∃ C S : ℝ → ℝ, ContDiff ℝ ∞ C ∧ ContDiff ℝ ∞ S ∧ ∀ z : CotangentBundle (𝓡 n) (𝕊 n),
      cotangentCoord (twistOfAngle θ z) =
        (C (‖(cotangentCoord z).2‖ ^ 2) • (cotangentCoord z).1 +
            S (‖(cotangentCoord z).2‖ ^ 2) • (cotangentCoord z).2,
          C (‖(cotangentCoord z).2‖ ^ 2) • (cotangentCoord z).2 -
            (‖(cotangentCoord z).2‖ ^ 2 * S (‖(cotangentCoord z).2‖ ^ 2)) •
              (cotangentCoord z).1) := by
  obtain ⟨C, hCd, hC⟩ := Function.Even.exists_contDiff_comp_sq (f := fun t ↦ cos (θ t))
    (fun t ↦ hc t) (Real.contDiff_cos.comp hθ)
  obtain ⟨S, hSd, hS⟩ := Function.Odd.exists_contDiff_mul_comp_sq (f := fun t ↦ sin (θ t))
    (fun t ↦ hs t) (Real.contDiff_sin.comp hθ)
  exact ⟨C, S, hCd, hSd, cotangentCoord_twistOfAngle hC hS h0⟩

/-- Twisting by a smooth angle function `θ` with `cos ∘ θ` even, `sin ∘ θ` odd and
`cos (θ 0) = -1` is smooth, also across the zero section. -/
private theorem contMDiff_twistOfAngle {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ)
    (hc : ∀ t, cos (θ (-t)) = cos (θ t)) (hs : ∀ t, sin (θ (-t)) = -sin (θ t))
    (h0 : cos (θ 0) = -1) :
    ContMDiff ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) ∞
      (twistOfAngle (n := n) θ) := by
  obtain ⟨C, S, hCd, hSd, hG⟩ := exists_cotangentCoord_twistOfAngle (n := n) hθ hc hs h0
  refine contMDiff_of_contMDiff_cotangentCoord_comp ?_
  have hn : ContDiff ℝ ∞ fun x : (𝔼 n) × 𝔼 n ↦ ‖x.2‖ ^ 2 :=
    (contDiff_norm_sq ℝ).comp contDiff_snd
  have hF : ContDiff ℝ ∞ fun x : (𝔼 n) × 𝔼 n ↦
      (C (‖x.2‖ ^ 2) • x.1 + S (‖x.2‖ ^ 2) • x.2,
        C (‖x.2‖ ^ 2) • x.2 - (‖x.2‖ ^ 2 * S (‖x.2‖ ^ 2)) • x.1) :=
    (((hCd.comp hn).smul contDiff_fst).add ((hSd.comp hn).smul contDiff_snd)).prodMk
      (((hCd.comp hn).smul contDiff_snd).sub ((hn.mul (hSd.comp hn)).smul contDiff_fst))
  exact (hF.contMDiff.comp contMDiff_cotangentCoord).congr hG

/-- Twisting by `-θ` is smooth under the hypotheses of `contMDiff_twistOfAngle` on `θ`. -/
private theorem contMDiff_twistOfAngle_neg {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ)
    (hc : ∀ t, cos (θ (-t)) = cos (θ t)) (hs : ∀ t, sin (θ (-t)) = -sin (θ t))
    (h0 : cos (θ 0) = -1) :
    ContMDiff ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) ∞
      (twistOfAngle (n := n) fun t ↦ -θ t) :=
  contMDiff_twistOfAngle hθ.neg (fun t ↦ by rw [cos_neg, cos_neg, hc])
    (fun t ↦ by rw [sin_neg, sin_neg, hs]) (by rw [cos_neg, h0])

/-! ### The model twist -/

/-- The model Dehn twist of a function `R` as a map of `T*Sⁿ`: off the zero section it moves `z`
along the normalized geodesic flow for the time `2π R'(μ z)`, `μ = cotangentNorm`, and on the zero
section it is the antipodal map. -/
def modelTwistFun (R : ℝ → ℝ) (z : CotangentBundle (𝓡 n) (𝕊 n)) :
    CotangentBundle (𝓡 n) (𝕊 n) :=
  if cotangentNorm z = 0 then antipodal z
  else geodesicFlow (2 * π * deriv R (cotangentNorm z)) z

theorem modelTwistFun_def (R : ℝ → ℝ) (z : CotangentBundle (𝓡 n) (𝕊 n)) :
    modelTwistFun R z = if cotangentNorm z = 0 then antipodal z
      else geodesicFlow (2 * π * deriv R (cotangentNorm z)) z :=
  (rfl)

private theorem modelTwistFun_eq_twistOfAngle (R : ℝ → ℝ) :
    modelTwistFun (n := n) R = twistOfAngle fun t ↦ 2 * π * deriv R t :=
  (rfl)

/-- The angle function `2π R'` of a twist profile is smooth, its cosine is even, its sine is odd,
and its value at `0` is `π`. -/
private theorem angle_of_isTwistProfile {R : ℝ → ℝ} {r₀ : ℝ} (hR : IsTwistProfile R r₀) :
    ContDiff ℝ ∞ (fun t ↦ 2 * π * deriv R t) ∧
      (∀ t, cos (2 * π * deriv R (-t)) = cos (2 * π * deriv R t)) ∧
      (∀ t, sin (2 * π * deriv R (-t)) = -sin (2 * π * deriv R t)) ∧
      cos (2 * π * deriv R 0) = -1 :=
  ⟨contDiff_const.mul hR.contDiff_deriv,
    fun t ↦ by rw [hR.deriv_neg, mul_one_sub, cos_two_pi_sub],
    fun t ↦ by rw [hR.deriv_neg, mul_one_sub, sin_two_pi_sub],
    by rw [hR.deriv_zero, show 2 * π * (1 / 2) = π by ring, cos_pi]⟩

/-- The model Dehn twist of a twist profile `R`, as a diffeomorphism of `T*Sⁿ`
(`coe_modelTwist`). Its inverse moves `z` along the normalized geodesic flow for the time
`-2π R'(μ z)`. -/
def modelTwist {R : ℝ → ℝ} {r₀ : ℝ} (hR : IsTwistProfile R r₀) :
    CotangentBundle (𝓡 n) (𝕊 n) ≃ₘ⟮(𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ),
      (𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)⟯ CotangentBundle (𝓡 n) (𝕊 n) where
  toFun := modelTwistFun R
  invFun := twistOfAngle fun t ↦ -(2 * π * deriv R t)
  left_inv z := twistOfAngle_neg_twistOfAngle _ z
  right_inv z := by
    have h := twistOfAngle_neg_twistOfAngle (n := n) (fun t ↦ -(2 * π * deriv R t)) z
    exact (congrFun (modelTwistFun_eq_twistOfAngle R) _).trans (by simpa only [neg_neg] using h)
  contMDiff_toFun :=
    let ⟨hθ, hc, hs, h0⟩ := angle_of_isTwistProfile hR
    contMDiff_twistOfAngle hθ hc hs h0
  contMDiff_invFun :=
    let ⟨hθ, hc, hs, h0⟩ := angle_of_isTwistProfile hR
    contMDiff_twistOfAngle_neg hθ hc hs h0

@[simp]
theorem coe_modelTwist {R : ℝ → ℝ} {r₀ : ℝ} (hR : IsTwistProfile R r₀) :
    ⇑(modelTwist (n := n) hR) = modelTwistFun R :=
  (rfl)

/-- The model twist is the identity where `μ ≥ r₀`. -/
theorem modelTwist_apply_of_le {R : ℝ → ℝ} {r₀ : ℝ} (hR : IsTwistProfile R r₀)
    {z : CotangentBundle (𝓡 n) (𝕊 n)} (hz : r₀ ≤ cotangentNorm z) : modelTwist hR z = z := by
  rw [coe_modelTwist, modelTwistFun_def, ite_eq_right (hR.pos.trans_le hz).ne',
    hR.deriv_eq_zero hz, mul_zero, geodesicFlow_zero]

/-- The model twist commutes with the cotangent lift of every orthogonal transformation of
`ℝⁿ⁺¹`. -/
theorem modelTwist_cotangent_orthogonal {R : ℝ → ℝ} {r₀ : ℝ} (hR : IsTwistProfile R r₀)
    (A : Matrix.orthogonalGroup (Fin (n + 1)) ℝ) (z : CotangentBundle (𝓡 n) (𝕊 n)) :
    modelTwist hR ((orthogonalToDiffSphere n ∞ A).cotangent z) =
      (orthogonalToDiffSphere n ∞ A).cotangent (modelTwist hR z) := by
  obtain ⟨hθ, hc, hs, h0⟩ := angle_of_isTwistProfile hR
  obtain ⟨C, S, -, -, hG⟩ := exists_cotangentCoord_twistOfAngle (n := n) hθ hc hs h0
  refine cotangentCoord_injective ?_
  rw [coe_modelTwist, modelTwistFun_eq_twistOfAngle, hG, cotangentCoord_cotangent_orthogonal,
    cotangentCoord_cotangent_orthogonal, hG, LinearIsometryEquiv.norm_map]
  simp only [map_add, map_sub, map_smul]

end SymplecticGeometry
