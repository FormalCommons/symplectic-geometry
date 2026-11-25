/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.DehnTwist.Geodesic
public import SymplecticGeometry.Geometry.Symplectic.Flux.CompactSupport
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Geometry.Manifold.Instances.Icc
import Mathlib.Geometry.Manifold.IntegralCurve.Transform
import SymplecticGeometry.Analysis.Calculus.ContDiff.Even
import SymplecticGeometry.Geometry.Diffeomorphism.Diffeotopy.Velocity

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
* `SymplecticGeometry.geodesicTwist θ`: the map that moves `z` along the normalized geodesic flow
  for the time `θ (μ z)` off the zero section, and is the antipodal map on it.
* `SymplecticGeometry.modelTwistFun R`: the model twist as a function of `T*Sⁿ`, the geodesic
  twist of `2π R'`.
* `SymplecticGeometry.modelTwist hR`: the model twist of a twist profile, as a diffeomorphism.
* `SymplecticGeometry.twistPrimitive R`: the function `2π (R'(μ z) μ z - R (μ z))` of `T*Sⁿ`, the
  primitive of the model twist.

## Main results

* `SymplecticGeometry.IsTwistProfile.deriv_zero`, `SymplecticGeometry.IsTwistProfile.pos`,
  `SymplecticGeometry.IsTwistProfile.deriv_eq_zero`: `R'(0) = 1 / 2`, so `0 < r₀`, and `R'`
  vanishes on `[r₀, ∞)`.
* `SymplecticGeometry.IsTwistProfile.lineMap`: twist profiles of the same radius form an affine
  subspace; `SymplecticGeometry.exists_isTwistProfile`: there is one for every `r₀ > 0`.
* `SymplecticGeometry.contMDiff_geodesicTwist`: the geodesic twist of `θ` is smooth when `θ` is,
  `cos ∘ θ` is even, `sin ∘ θ` is odd and `cos (θ 0) = -1`.
* `SymplecticGeometry.coe_modelTwist_symm`: the inverse of the model twist of `R` is the model
  twist of `-R`.
* `SymplecticGeometry.modelTwist_of_cotangentNorm_ne_zero`: off the zero section the model twist
  of `z` is `σ_{2π R'(μ z)} z`.
* `SymplecticGeometry.modelTwist_apply_of_le`: the model twist is the identity where `μ ≥ r₀`.
* `SymplecticGeometry.modelTwist_cotangent_orthogonal`: it commutes with the cotangent lift of
  every orthogonal transformation of `ℝⁿ⁺¹`.
* `SymplecticGeometry.isMIntegralCurve_geodesicFlow_comp`: off the zero section, the geodesic flow
  run at the constant speed `φ'(μ z)` is an integral curve of the Hamiltonian vector field of
  `φ ∘ μ`; `SymplecticGeometry.isMIntegralCurve_geodesicFlow_twistProfile`: for a twist profile
  `R` its value at time `2π` is the model twist, which is thus the time-`2π` map of `R ∘ μ` there.
* `SymplecticGeometry.contMDiff_twistPrimitive`, `SymplecticGeometry.twistPrimitive_of_le`: the
  primitive of the model twist of a twist profile is smooth, and vanishes where `μ ≥ r₀`.
* `Function.Even.mvfderiv_comp_cotangentNorm_eq_zero`: for a smooth even `g`, the differential of
  `g ∘ μ` vanishes on the zero section.
* `SymplecticGeometry.exists_isCompactlySupportedHamiltonian_modelTwist`: two model twists of the
  same support radius `r₀` differ by the time-one map of a compactly supported Hamiltonian
  diffeotopy that fixes every point with `μ ≥ r₀`;
  `SymplecticGeometry.apply_modelTwist_eq_modelTwist_lineMap` describes its trajectories.

## Implementation notes

Write `θ = 2π R'`. From `R (-t) = R t - t` one gets `R'(-t) = 1 - R'(t)`, so `cos ∘ θ` is even
and `sin ∘ θ` is odd. By Whitney's theorem (`Function.Even.exists_contDiff_comp_sq`,
`Function.Odd.exists_contDiff_mul_comp_sq`) they are `C (t ^ 2)` and `t * S (t ^ 2)` with `C`
and `S` smooth. By `cotangentCoord_geodesicFlow`, the twist then reads, in the coordinates
`(q, p)` of `cotangentCoord`,
`(q, p) ↦ (C ‖p‖² • q + S ‖p‖² • p, C ‖p‖² • p - (‖p‖² * S ‖p‖²) • q)`,
also on the zero section, where `C 0 = cos π = -1`. This is a smooth map of `(q, p)`, so the twist
is smooth (`contMDiff_of_contMDiff_cotangentCoord_comp`). The inverse is the same construction
with `-θ` in place of `θ`, that is the model twist of `-R`, as the flow preserves `μ`. The same
coordinate formula gives the equivariance under `O(n + 1)`, which acts on the coordinates by
isometries. The function `t ↦ R'(t) t - R t` is even, so the primitive `twistPrimitive R`
is smooth by `Function.Even.contDiff_comp_norm`, applied to the second coordinate.

For two profiles `R₀` and `R₁` of radius `r₀`, the Hamiltonian `G = 2π (R₁ - R₀) ∘ μ` is smooth,
as `R₁ - R₀` is even, and vanishes where `μ ≥ r₀`, so it generates a compactly supported
diffeotopy `φ_t` (`TauCeti.Diffeotopy.exists_isCompactlySupportedHamiltonian`). The curve
`t ↦ τ_{R_t} z`, for `R_t = (1 - t) R₀ + t R₁`, solves the equation of `φ_t`: off the zero section
it is the geodesic flow from `τ_{R₀} z` at the constant speed `2π (R₁' - R₀') (μ z)`, an integral
curve of the Hamiltonian vector field of `G` (`isMIntegralCurve_geodesicFlow_comp`), and on the
zero section it is constant, where `dG = 0` because `G` is a smooth function of `‖p‖²`. Hence
`φ_t (τ_{R₀} z) = τ_{R_t} z` (`TauCeti.Diffeotopy.apply_eq_of_mfderiv_eq_velocity`). Both
`φ₁ ∘ τ_{R₀} = τ_{R₁}` and the fixing of the points with `μ ≥ r₀`, including those with
`μ = r₀`, follow from that identity, since all the twists are the identity there.

## References

* [P. Seidel, *A long exact sequence for symplectic Floer cohomology*][Seidel2003], Lemma 1.8
  and equation (1.7) (arXiv version 2): the model twist on `T*Sⁿ` built from the normalized
  geodesic flow.
* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], 3rd ed.,
  p. 270: the model twist as the time-`2π` map of a function of the norm, and its primitive.
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

/-- The derivative of the profile `(1 - s) R₀ + s R₁` is `(1 - s) R₀' + s R₁'`. -/
theorem deriv_lineMap (h₀ : IsTwistProfile R₀ r₀) (h₁ : IsTwistProfile R₁ r₀) (s t : ℝ) :
    deriv (fun t ↦ (1 - s) * R₀ t + s * R₁ t) t = (1 - s) * deriv R₀ t + s * deriv R₁ t :=
  (((h₀.contDiff.differentiable (by simp) t).hasDerivAt.const_mul _).add
    ((h₁.contDiff.differentiable (by simp) t).hasDerivAt.const_mul _)).deriv

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

/-- The geodesic twist of an angle function `θ`: it moves a covector `z` off the zero section
along the normalized geodesic flow for the time `θ (μ z)`, and acts by the antipodal map on the
zero section. -/
def geodesicTwist (θ : ℝ → ℝ) (z : CotangentBundle (𝓡 n) (𝕊 n)) :
    CotangentBundle (𝓡 n) (𝕊 n) :=
  if cotangentNorm z = 0 then antipodal z else geodesicFlow (θ (cotangentNorm z)) z

theorem geodesicTwist_def (θ : ℝ → ℝ) (z : CotangentBundle (𝓡 n) (𝕊 n)) :
    geodesicTwist θ z =
      if cotangentNorm z = 0 then antipodal z else geodesicFlow (θ (cotangentNorm z)) z :=
  (rfl)

theorem geodesicTwist_of_cotangentNorm_eq_zero (θ : ℝ → ℝ) {z : CotangentBundle (𝓡 n) (𝕊 n)}
    (hz : cotangentNorm z = 0) : geodesicTwist θ z = antipodal z := by
  rw [geodesicTwist_def, ite_eq_left hz]

theorem geodesicTwist_of_cotangentNorm_ne_zero (θ : ℝ → ℝ) {z : CotangentBundle (𝓡 n) (𝕊 n)}
    (hz : cotangentNorm z ≠ 0) : geodesicTwist θ z = geodesicFlow (θ (cotangentNorm z)) z := by
  rw [geodesicTwist_def, ite_eq_right hz]

/-- The geodesic twist preserves the norm `μ` of covectors. -/
@[simp]
theorem cotangentNorm_geodesicTwist (θ : ℝ → ℝ) (z : CotangentBundle (𝓡 n) (𝕊 n)) :
    cotangentNorm (geodesicTwist θ z) = cotangentNorm z := by
  by_cases hz : cotangentNorm z = 0
  · rw [geodesicTwist_of_cotangentNorm_eq_zero θ hz, cotangentNorm_antipodal]
  · rw [geodesicTwist_of_cotangentNorm_ne_zero θ hz, cotangentNorm_geodesicFlow]

/-- The geodesic twist of `-θ` undoes the geodesic twist of `θ`. -/
@[simp]
theorem geodesicTwist_neg_geodesicTwist (θ : ℝ → ℝ) (z : CotangentBundle (𝓡 n) (𝕊 n)) :
    geodesicTwist (fun t ↦ -θ t) (geodesicTwist θ z) = z := by
  have hn := cotangentNorm_geodesicTwist θ z
  by_cases hz : cotangentNorm z = 0
  · rw [geodesicTwist_of_cotangentNorm_eq_zero _ (hn.trans hz),
      geodesicTwist_of_cotangentNorm_eq_zero θ hz]
    refine cotangentCoord_injective ?_
    rw [cotangentCoord_antipodal, cotangentCoord_antipodal, neg_neg]
  · rw [geodesicTwist_of_cotangentNorm_ne_zero _ (hn.trans_ne hz), hn,
      geodesicTwist_of_cotangentNorm_ne_zero θ hz, ← geodesicFlow_add, neg_add_cancel,
      geodesicFlow_zero]

/-- The geodesic twist of `θ` undoes the geodesic twist of `-θ`. -/
@[simp]
theorem geodesicTwist_geodesicTwist_neg (θ : ℝ → ℝ) (z : CotangentBundle (𝓡 n) (𝕊 n)) :
    geodesicTwist θ (geodesicTwist (fun t ↦ -θ t) z) = z := by
  simpa only [neg_neg] using geodesicTwist_neg_geodesicTwist (fun t ↦ -θ t) z

/-- If `cos ∘ θ = C (t ^ 2)` and `sin ∘ θ = t * S (t ^ 2)`, and `cos (θ 0) = -1`, then the
geodesic twist of `θ` acts on the coordinates `(q, p)` by
`(C ‖p‖² • q + S ‖p‖² • p, C ‖p‖² • p - (‖p‖² * S ‖p‖²) • q)`. -/
theorem cotangentCoord_geodesicTwist {θ C S : ℝ → ℝ} (hC : ∀ t, cos (θ t) = C (t ^ 2))
    (hS : ∀ t, sin (θ t) = t * S (t ^ 2)) (h0 : cos (θ 0) = -1)
    (z : CotangentBundle (𝓡 n) (𝕊 n)) :
    cotangentCoord (geodesicTwist θ z) =
      (C (‖(cotangentCoord z).2‖ ^ 2) • (cotangentCoord z).1 +
          S (‖(cotangentCoord z).2‖ ^ 2) • (cotangentCoord z).2,
        C (‖(cotangentCoord z).2‖ ^ 2) • (cotangentCoord z).2 -
          (‖(cotangentCoord z).2‖ ^ 2 * S (‖(cotangentCoord z).2‖ ^ 2)) •
            (cotangentCoord z).1) := by
  by_cases hz : cotangentNorm z = 0
  · have hp : (cotangentCoord z).2 = 0 := norm_eq_zero.1 ((cotangentNorm_def z).symm.trans hz)
    have hC0 : C 0 = -1 := by rw [← h0, hC, sq, mul_zero]
    rw [geodesicTwist_of_cotangentNorm_eq_zero θ hz, cotangentCoord_antipodal, hp, norm_zero]
    ext1 <;> simp [hC0, hp]
  · rw [geodesicTwist_of_cotangentNorm_ne_zero θ hz, cotangentCoord_geodesicFlow hz,
      cotangentNorm_def, hC, hS]
    have hN : ‖(cotangentCoord z).2‖ ≠ 0 := (cotangentNorm_def z).symm.trans_ne hz
    ext1
    · simp only
      congr 2
      field_simp
    · simp only
      congr 2
      ring

/-- If `θ` is smooth, `cos ∘ θ` is even, `sin ∘ θ` is odd and `cos (θ 0) = -1`, then by Whitney's
theorem the geodesic twist of `θ` acts on the coordinates `(q, p)` by
`(C ‖p‖² • q + S ‖p‖² • p, C ‖p‖² • p - (‖p‖² * S ‖p‖²) • q)` for smooth `C` and `S`. -/
theorem exists_cotangentCoord_geodesicTwist {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ)
    (hc : ∀ t, cos (θ (-t)) = cos (θ t)) (hs : ∀ t, sin (θ (-t)) = -sin (θ t))
    (h0 : cos (θ 0) = -1) :
    ∃ C S : ℝ → ℝ, ContDiff ℝ ∞ C ∧ ContDiff ℝ ∞ S ∧ ∀ z : CotangentBundle (𝓡 n) (𝕊 n),
      cotangentCoord (geodesicTwist θ z) =
        (C (‖(cotangentCoord z).2‖ ^ 2) • (cotangentCoord z).1 +
            S (‖(cotangentCoord z).2‖ ^ 2) • (cotangentCoord z).2,
          C (‖(cotangentCoord z).2‖ ^ 2) • (cotangentCoord z).2 -
            (‖(cotangentCoord z).2‖ ^ 2 * S (‖(cotangentCoord z).2‖ ^ 2)) •
              (cotangentCoord z).1) := by
  obtain ⟨C, hCd, hC⟩ := Function.Even.exists_contDiff_comp_sq (f := fun t ↦ cos (θ t))
    (fun t ↦ hc t) (Real.contDiff_cos.comp hθ)
  obtain ⟨S, hSd, hS⟩ := Function.Odd.exists_contDiff_mul_comp_sq (f := fun t ↦ sin (θ t))
    (fun t ↦ hs t) (Real.contDiff_sin.comp hθ)
  exact ⟨C, S, hCd, hSd, cotangentCoord_geodesicTwist hC hS h0⟩

/-- The geodesic twist of a smooth angle function `θ` with `cos ∘ θ` even, `sin ∘ θ` odd and
`cos (θ 0) = -1` is smooth, also across the zero section. -/
theorem contMDiff_geodesicTwist {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ)
    (hc : ∀ t, cos (θ (-t)) = cos (θ t)) (hs : ∀ t, sin (θ (-t)) = -sin (θ t))
    (h0 : cos (θ 0) = -1) :
    ContMDiff ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) ∞
      (geodesicTwist (n := n) θ) := by
  obtain ⟨C, S, hCd, hSd, hG⟩ := exists_cotangentCoord_geodesicTwist (n := n) hθ hc hs h0
  refine contMDiff_of_contMDiff_cotangentCoord_comp ?_
  have hn : ContDiff ℝ ∞ fun x : (𝔼 n) × 𝔼 n ↦ ‖x.2‖ ^ 2 :=
    (contDiff_norm_sq ℝ).comp contDiff_snd
  have hF : ContDiff ℝ ∞ fun x : (𝔼 n) × 𝔼 n ↦
      (C (‖x.2‖ ^ 2) • x.1 + S (‖x.2‖ ^ 2) • x.2,
        C (‖x.2‖ ^ 2) • x.2 - (‖x.2‖ ^ 2 * S (‖x.2‖ ^ 2)) • x.1) :=
    (((hCd.comp hn).smul contDiff_fst).add ((hSd.comp hn).smul contDiff_snd)).prodMk
      (((hCd.comp hn).smul contDiff_snd).sub ((hn.mul (hSd.comp hn)).smul contDiff_fst))
  exact (hF.contMDiff.comp contMDiff_cotangentCoord).congr hG

/-! ### The angle function of a twist profile -/

namespace IsTwistProfile

variable {R : ℝ → ℝ} {r₀ : ℝ}

/-- The cosine of the angle function `2π R'` of a twist profile is even. -/
theorem cos_two_pi_mul_deriv_neg (hR : IsTwistProfile R r₀) (t : ℝ) :
    cos (2 * π * deriv R (-t)) = cos (2 * π * deriv R t) := by
  rw [hR.deriv_neg, mul_one_sub, cos_two_pi_sub]

/-- The sine of the angle function `2π R'` of a twist profile is odd. -/
theorem sin_two_pi_mul_deriv_neg (hR : IsTwistProfile R r₀) (t : ℝ) :
    sin (2 * π * deriv R (-t)) = -sin (2 * π * deriv R t) := by
  rw [hR.deriv_neg, mul_one_sub, sin_two_pi_sub]

/-- The angle function `2π R'` of a twist profile is `π` at `0`. -/
theorem two_pi_mul_deriv_zero (hR : IsTwistProfile R r₀) : 2 * π * deriv R 0 = π := by
  rw [hR.deriv_zero]
  ring

end IsTwistProfile

/-! ### The model twist -/

/-- The model Dehn twist of a function `R` as a map of `T*Sⁿ`, the geodesic twist of the angle
function `2π R'`: off the zero section it moves `z` along the normalized geodesic flow for the
time `2π R'(μ z)`, `μ = cotangentNorm`, and on the zero section it is the antipodal map
(`modelTwistFun_def`). -/
def modelTwistFun (R : ℝ → ℝ) : CotangentBundle (𝓡 n) (𝕊 n) → CotangentBundle (𝓡 n) (𝕊 n) :=
  geodesicTwist fun t ↦ 2 * π * deriv R t

theorem modelTwistFun_eq_geodesicTwist (R : ℝ → ℝ) :
    modelTwistFun (n := n) R = geodesicTwist fun t ↦ 2 * π * deriv R t :=
  (rfl)

theorem modelTwistFun_def (R : ℝ → ℝ) (z : CotangentBundle (𝓡 n) (𝕊 n)) :
    modelTwistFun R z = if cotangentNorm z = 0 then antipodal z
      else geodesicFlow (2 * π * deriv R (cotangentNorm z)) z := by
  rw [modelTwistFun_eq_geodesicTwist, geodesicTwist_def]

/-- The model twist preserves the norm `μ` of covectors. -/
@[simp]
theorem cotangentNorm_modelTwistFun (R : ℝ → ℝ) (z : CotangentBundle (𝓡 n) (𝕊 n)) :
    cotangentNorm (modelTwistFun R z) = cotangentNorm z := by
  rw [modelTwistFun_eq_geodesicTwist, cotangentNorm_geodesicTwist]

/-- The angle function of `-R` is minus that of `R`. -/
private theorem two_pi_mul_deriv_neg_fun (R : ℝ → ℝ) :
    (fun t ↦ 2 * π * deriv (fun t ↦ -R t) t) = fun t ↦ -(2 * π * deriv R t) := by
  ext t
  rw [deriv.fun_neg, mul_neg]

/-- The model twist of `-R` undoes the model twist of `R`. -/
@[simp]
theorem modelTwistFun_neg_modelTwistFun (R : ℝ → ℝ) (z : CotangentBundle (𝓡 n) (𝕊 n)) :
    modelTwistFun (fun t ↦ -R t) (modelTwistFun R z) = z := by
  rw [modelTwistFun_eq_geodesicTwist, modelTwistFun_eq_geodesicTwist, two_pi_mul_deriv_neg_fun,
    geodesicTwist_neg_geodesicTwist]

/-- The model twist of `R` undoes the model twist of `-R`. -/
@[simp]
theorem modelTwistFun_modelTwistFun_neg (R : ℝ → ℝ) (z : CotangentBundle (𝓡 n) (𝕊 n)) :
    modelTwistFun R (modelTwistFun (fun t ↦ -R t) z) = z := by
  simpa only [neg_neg] using modelTwistFun_neg_modelTwistFun (fun t ↦ -R t) z

/-- The model twist of a twist profile is smooth, also across the zero section. -/
theorem contMDiff_modelTwistFun {R : ℝ → ℝ} {r₀ : ℝ} (hR : IsTwistProfile R r₀) :
    ContMDiff ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) ∞ (modelTwistFun (n := n) R) :=
  contMDiff_geodesicTwist (contDiff_const.mul hR.contDiff_deriv) hR.cos_two_pi_mul_deriv_neg
    hR.sin_two_pi_mul_deriv_neg (by rw [hR.two_pi_mul_deriv_zero, cos_pi])

/-- The model twist of `-R`, for a twist profile `R`, is smooth, also across the zero section. -/
theorem contMDiff_modelTwistFun_neg {R : ℝ → ℝ} {r₀ : ℝ} (hR : IsTwistProfile R r₀) :
    ContMDiff ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) ∞
      (modelTwistFun (n := n) fun t ↦ -R t) := by
  rw [modelTwistFun_eq_geodesicTwist, two_pi_mul_deriv_neg_fun]
  exact contMDiff_geodesicTwist (contDiff_const.mul hR.contDiff_deriv).neg
    (fun t ↦ by rw [cos_neg, cos_neg, hR.cos_two_pi_mul_deriv_neg])
    (fun t ↦ by rw [sin_neg, sin_neg, hR.sin_two_pi_mul_deriv_neg])
    (by rw [cos_neg, hR.two_pi_mul_deriv_zero, cos_pi])

/-- The model Dehn twist of a twist profile `R`, as a diffeomorphism of `T*Sⁿ`
(`coe_modelTwist`). Its inverse is the model twist of `-R` (`coe_modelTwist_symm`): off the zero
section it moves `z` along the normalized geodesic flow for the time `-2π R'(μ z)`, and on the
zero section it is the antipodal map. -/
def modelTwist {R : ℝ → ℝ} {r₀ : ℝ} (hR : IsTwistProfile R r₀) :
    CotangentBundle (𝓡 n) (𝕊 n) ≃ₘ⟮(𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ),
      (𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)⟯ CotangentBundle (𝓡 n) (𝕊 n) where
  toFun := modelTwistFun R
  invFun := modelTwistFun fun t ↦ -R t
  left_inv := modelTwistFun_neg_modelTwistFun R
  right_inv := modelTwistFun_modelTwistFun_neg R
  contMDiff_toFun := contMDiff_modelTwistFun hR
  contMDiff_invFun := contMDiff_modelTwistFun_neg hR

@[simp]
theorem coe_modelTwist {R : ℝ → ℝ} {r₀ : ℝ} (hR : IsTwistProfile R r₀) :
    ⇑(modelTwist (n := n) hR) = modelTwistFun R :=
  (rfl)

/-- The inverse of the model twist of `R` is the model twist of `-R`. -/
@[simp]
theorem coe_modelTwist_symm {R : ℝ → ℝ} {r₀ : ℝ} (hR : IsTwistProfile R r₀) :
    ⇑(modelTwist (n := n) hR).symm = modelTwistFun fun t ↦ -R t :=
  (rfl)

/-- The model twist preserves the norm `μ` of covectors. -/
theorem cotangentNorm_modelTwist {R : ℝ → ℝ} {r₀ : ℝ} (hR : IsTwistProfile R r₀)
    (z : CotangentBundle (𝓡 n) (𝕊 n)) : cotangentNorm (modelTwist hR z) = cotangentNorm z := by
  rw [coe_modelTwist, cotangentNorm_modelTwistFun]

/-- The model twist is the identity where `μ ≥ r₀`. -/
theorem modelTwist_apply_of_le {R : ℝ → ℝ} {r₀ : ℝ} (hR : IsTwistProfile R r₀)
    {z : CotangentBundle (𝓡 n) (𝕊 n)} (hz : r₀ ≤ cotangentNorm z) : modelTwist hR z = z := by
  rw [coe_modelTwist, modelTwistFun_def, ite_eq_right (hR.pos.trans_le hz).ne',
    hR.deriv_eq_zero hz, mul_zero, geodesicFlow_zero]

/-- Off the zero section, the model twist moves `z` along the geodesic flow for the time
`2π R'(μ z)`. -/
theorem modelTwist_of_cotangentNorm_ne_zero {R : ℝ → ℝ} {r₀ : ℝ} (hR : IsTwistProfile R r₀)
    {z : CotangentBundle (𝓡 n) (𝕊 n)} (hz : cotangentNorm z ≠ 0) :
    modelTwist hR z = geodesicFlow (2 * π * deriv R (cotangentNorm z)) z := by
  rw [coe_modelTwist, modelTwistFun_def, ite_eq_right hz]

/-- The model twist commutes with the cotangent lift of every orthogonal transformation of
`ℝⁿ⁺¹`. -/
theorem modelTwist_cotangent_orthogonal {R : ℝ → ℝ} {r₀ : ℝ} (hR : IsTwistProfile R r₀)
    (A : Matrix.orthogonalGroup (Fin (n + 1)) ℝ) (z : CotangentBundle (𝓡 n) (𝕊 n)) :
    modelTwist hR ((orthogonalToDiffSphere n ∞ A).cotangent z) =
      (orthogonalToDiffSphere n ∞ A).cotangent (modelTwist hR z) := by
  obtain ⟨C, S, -, -, hG⟩ := exists_cotangentCoord_geodesicTwist (n := n)
    (contDiff_const.mul hR.contDiff_deriv) hR.cos_two_pi_mul_deriv_neg hR.sin_two_pi_mul_deriv_neg
    (by rw [hR.two_pi_mul_deriv_zero, cos_pi])
  refine cotangentCoord_injective ?_
  rw [coe_modelTwist, modelTwistFun_eq_geodesicTwist, hG, cotangentCoord_cotangent_orthogonal,
    cotangentCoord_cotangent_orthogonal, hG, LinearIsometryEquiv.norm_map]
  simp only [map_add, map_sub, map_smul]

/-! ### The model twist as a Hamiltonian flow -/

/-- **Reparametrized geodesic flows are Hamiltonian flows of functions of the norm.** Off the zero
section, for a function `φ` differentiable at `μ z`, the curve
`t ↦ geodesicFlow (t * φ'(μ z)) z` is an integral curve of the Hamiltonian vector field of
`φ ∘ μ` for the canonical symplectic form of `T*Sⁿ`, with Tau Ceti's convention `ι_X ω = dH`. -/
theorem isMIntegralCurve_geodesicFlow_comp {φ : ℝ → ℝ} {z : CotangentBundle (𝓡 n) (𝕊 n)}
    (hz : cotangentNorm z ≠ 0) (hφ : DifferentiableAt ℝ φ (cotangentNorm z)) :
    IsMIntegralCurve (fun t ↦ geodesicFlow (t * deriv φ (cotangentNorm z)) z) fun w ↦
      (CotangentBundle.symplecticForm (𝓡 n) (𝕊 n)).hamiltonianVectorField
        (φ ∘ cotangentNorm) w := by
  intro t
  have hw := cotangentNorm_geodesicFlow (t * deriv φ (cotangentNorm z)) z
  have hμ : MDifferentiableAt ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) 𝓘(ℝ)
      cotangentNorm (geodesicFlow (t * deriv φ (cotangentNorm z)) z) :=
    (contMDiffAt_cotangentNorm (by rwa [hw])).mdifferentiableAt (by simp)
  dsimp only
  rw [SmoothTwoForm.hamiltonianVectorField_comp (by rwa [hw]) hμ, hw]
  exact (isMIntegralCurve_geodesicFlow hz).comp_mul (deriv φ (cotangentNorm z)) t

/-- **Off the zero section, the model twist is the time-`2π` map of the Hamiltonian `R ∘ μ`.** For
a twist profile `R` and `z` off the zero section, `t ↦ geodesicFlow (t * R'(μ z)) z` is an
integral curve of the Hamiltonian vector field of `R ∘ μ`, and its value at `t = 2π` is the model
twist of `z`. Only the second half uses that `R` is a twist profile; the first holds for every `R`
differentiable at `μ z` (`isMIntegralCurve_geodesicFlow_comp`). -/
theorem isMIntegralCurve_geodesicFlow_twistProfile {R : ℝ → ℝ} {r₀ : ℝ}
    (hR : IsTwistProfile R r₀) {z : CotangentBundle (𝓡 n) (𝕊 n)} (hz : cotangentNorm z ≠ 0) :
    IsMIntegralCurve (fun t ↦ geodesicFlow (t * deriv R (cotangentNorm z)) z) (fun w ↦
        (CotangentBundle.symplecticForm (𝓡 n) (𝕊 n)).hamiltonianVectorField
          (R ∘ cotangentNorm) w) ∧
      geodesicFlow (2 * π * deriv R (cotangentNorm z)) z = modelTwist hR z :=
  ⟨isMIntegralCurve_geodesicFlow_comp hz (hR.contDiff.differentiable (by simp) _),
    (modelTwist_of_cotangentNorm_ne_zero hR hz).symm⟩

/-! ### The primitive of the model twist -/

/-- For a smooth even function `f : ℝ → ℝ`, the function `z ↦ f (μ z)` of `T*Sⁿ` is smooth, also
across the zero section. -/
theorem _root_.Function.Even.contMDiff_comp_cotangentNorm {f : ℝ → ℝ} (hf : f.Even)
    (hc : ContDiff ℝ ∞ f) :
    ContMDiff ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) 𝓘(ℝ) ∞
      fun z : CotangentBundle (𝓡 n) (𝕊 n) ↦ f (cotangentNorm z) := by
  simp only [cotangentNorm_def]
  exact ((hf.contDiff_comp_norm (V := 𝔼 n) hc).comp contDiff_snd).contMDiff.comp
    contMDiff_cotangentCoord

/-- For a smooth even function `g : ℝ → ℝ`, the differential of `z ↦ g (μ z)` vanishes on the
zero section of `T*Sⁿ`. -/
theorem _root_.Function.Even.mvfderiv_comp_cotangentNorm_eq_zero {g : ℝ → ℝ} (hg : g.Even)
    (hc : ContDiff ℝ ∞ g) {z : CotangentBundle (𝓡 n) (𝕊 n)} (hz : cotangentNorm z = 0) :
    mvfderiv ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))
      (fun w : CotangentBundle (𝓡 n) (𝕊 n) ↦ g (cotangentNorm w)) z = 0 := by
  -- By Whitney's theorem `g t = h (t ^ 2)`, and `p ↦ ‖p‖ ^ 2` has derivative `0` at `p = 0`.
  obtain ⟨h, hh, hgh⟩ := hg.exists_contDiff_comp_sq hc
  have hp : (cotangentCoord z).2 = 0 := norm_eq_zero.1 ((cotangentNorm_def z).symm.trans hz)
  have hsq : HasFDerivAt (fun v : 𝔼 n ↦ ‖v‖ ^ 2) (0 : (𝔼 n) →L[ℝ] ℝ) 0 := by
    simpa using (hasStrictFDerivAt_norm_sq (0 : 𝔼 n)).hasFDerivAt
  have hh₀ : HasDerivAt h (deriv h 0) 0 := (hh.differentiable (by simp) 0).hasDerivAt
  have hF : HasFDerivAt (h ∘ fun v : 𝔼 n ↦ ‖v‖ ^ 2) (deriv h 0 • (0 : (𝔼 n) →L[ℝ] ℝ)) 0 :=
    HasDerivAt.comp_hasFDerivAt (0 : 𝔼 n) (by simpa using hh₀) hsq
  rw [smul_zero, ← hp] at hF
  have hq : MDifferentiableAt ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) 𝓘(ℝ, 𝔼 n)
      (fun w : CotangentBundle (𝓡 n) (𝕊 n) ↦ (cotangentCoord w).2) z :=
    (contDiff_snd.contMDiff.comp contMDiff_cotangentCoord).mdifferentiableAt (by simp)
  have hfun : (fun w : CotangentBundle (𝓡 n) (𝕊 n) ↦ g (cotangentNorm w)) =
      (h ∘ fun v : 𝔼 n ↦ ‖v‖ ^ 2) ∘ fun w ↦ (cotangentCoord w).2 := by
    ext w
    rw [Function.comp_apply, Function.comp_apply, hgh, cotangentNorm_def]
  rw [mvfderiv_eq_zero_iff, hfun, (hF.hasMFDerivAt.comp z hq.hasMFDerivAt).mfderiv]
  exact ContinuousLinearMap.zero_comp _

/-- For a twist profile `R`, the function `t ↦ R'(t) t - R(t)` is even. -/
theorem IsTwistProfile.even_deriv_mul_sub {R : ℝ → ℝ} {r₀ : ℝ} (hR : IsTwistProfile R r₀) :
    (fun t ↦ deriv R t * t - R t).Even := fun t ↦ by
  simp only [hR.deriv_neg, hR.apply_neg]
  ring

/-- The primitive of the model twist of `R`: the function `2π (R'(μ z) μ z - R(μ z))` of `T*Sⁿ`,
`μ = cotangentNorm`. -/
def twistPrimitive (R : ℝ → ℝ) (z : CotangentBundle (𝓡 n) (𝕊 n)) : ℝ :=
  2 * π * (deriv R (cotangentNorm z) * cotangentNorm z - R (cotangentNorm z))

theorem twistPrimitive_def (R : ℝ → ℝ) (z : CotangentBundle (𝓡 n) (𝕊 n)) :
    twistPrimitive R z =
      2 * π * (deriv R (cotangentNorm z) * cotangentNorm z - R (cotangentNorm z)) :=
  (rfl)

/-- The primitive of the model twist of a twist profile is smooth, also across the zero
section. -/
theorem contMDiff_twistPrimitive {R : ℝ → ℝ} {r₀ : ℝ} (hR : IsTwistProfile R r₀) :
    ContMDiff ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) 𝓘(ℝ) ∞
      (twistPrimitive (n := n) R) := by
  have hc : ContDiff ℝ ∞ fun t ↦ deriv R t * t - R t :=
    (hR.contDiff_deriv.mul contDiff_id).sub hR.contDiff
  refine ((contMDiff_const (c := 2 * π)).mul
    (hR.even_deriv_mul_sub.contMDiff_comp_cotangentNorm (n := n) hc)).congr fun z ↦ ?_
  rw [twistPrimitive_def, Pi.mul_apply]

/-- The primitive of the model twist of a twist profile vanishes where `μ ≥ r₀`. -/
theorem twistPrimitive_of_le {R : ℝ → ℝ} {r₀ : ℝ} (hR : IsTwistProfile R r₀)
    {z : CotangentBundle (𝓡 n) (𝕊 n)} (hz : r₀ ≤ cotangentNorm z) : twistPrimitive R z = 0 := by
  rw [twistPrimitive_def, hR.deriv_eq_zero hz, hR.apply_of_le hz]
  ring

/-! ### Model twists of the same radius are Hamiltonian isotopic -/

/-- **The trajectories of the isotopy between two model twists.** Let `R₀` and `R₁` be twist
profiles of the same support radius and let `φ_t` be a diffeotopy of `T*Sⁿ` whose velocity at
every time is the Hamiltonian vector field of `G = 2π (R₁ - R₀) ∘ μ`. Then `φ_t` moves the
model twist of `R₀` along the model twists of the profiles `R_t = (1 - t) R₀ + t R₁`:
`φ_t (τ_{R₀} z) = τ_{R_t} z`. -/
theorem apply_modelTwist_eq_modelTwist_lineMap {R₀ R₁ : ℝ → ℝ} {r₀ : ℝ}
    (h₀ : IsTwistProfile R₀ r₀) (h₁ : IsTwistProfile R₁ r₀)
    {Φ : Diffeotopy ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) ∞
      (CotangentBundle (𝓡 n) (𝕊 n))}
    (hX : ∀ t, Φ.velocity t = (CotangentBundle.symplecticForm (𝓡 n) (𝕊 n)).hamiltonianVectorField
      fun y ↦ 2 * π * (R₁ (cotangentNorm y) - R₀ (cotangentNorm y)))
    (t : unitInterval) (z : CotangentBundle (𝓡 n) (𝕊 n)) :
    Φ (t, modelTwist h₀ z) = modelTwist (h₀.lineMap h₁ t) z := by
  set g : ℝ → ℝ := fun t ↦ 2 * π * (R₁ t - R₀ t) with hg
  have hgc : ContDiff ℝ ∞ g := contDiff_const.mul (h₁.contDiff.sub h₀.contDiff)
  have hσ := CotangentBundle.isSymplectic_symplecticForm (I := 𝓡 n) (M := 𝕊 n)
  -- Both curves start at `τ_{R₀} z`; it remains to see that `s ↦ τ_{R_s} z` solves the equation
  -- of `φ_t` (`TauCeti.Diffeotopy.apply_eq_of_mfderiv_eq_velocity`).
  have hγ0 : modelTwist (h₀.lineMap h₁ ((0 : unitInterval) : ℝ)) z = modelTwist h₀ z := by
    simp only [coe_modelTwist, Set.Icc.coe_zero, sub_zero, one_mul, zero_mul, add_zero]
  rw [← hγ0]
  obtain ⟨γ, hγ⟩ : ∃ γ : unitInterval → CotangentBundle (𝓡 n) (𝕊 n),
      γ = fun s : unitInterval ↦ modelTwist (h₀.lineMap h₁ s) z := ⟨_, rfl⟩
  have hγt (s : unitInterval) : modelTwist (h₀.lineMap h₁ s) z = γ s := by rw [hγ]
  rw [hγt, hγt]
  by_cases hz : cotangentNorm z = 0
  · -- On the zero section `γ` stays at `-z`, where `dG` vanishes, as `R₁ - R₀` is even.
    have hge : g.Even := fun t ↦ by
      simp only [hg, h₀.apply_neg, h₁.apply_neg]
      ring
    have hc : γ = fun _ ↦ antipodal z := by
      rw [hγ]
      funext s
      rw [coe_modelTwist, modelTwistFun_def, ite_eq_left hz]
    refine Φ.apply_eq_of_mfderiv_eq_velocity (hc ▸ mdifferentiable_const) (fun s ↦ ?_) t
    rw [hc, mfderiv_const, hX s, (hσ.isNondegenerate.hamiltonianVectorField_eq_zero_iff).2
      (hge.mvfderiv_comp_cotangentNorm_eq_zero hgc (by rwa [cotangentNorm_antipodal]))]
    -- Both sides are the zero vector, of tangent spaces that agree only up to unfolding.
    rfl
  · -- Off it `γ` is the geodesic flow from `τ_{R₀} z` at the speed `g' (μ z)`, an integral
    -- curve of the Hamiltonian vector field of `g ∘ μ`.
    have hw : cotangentNorm (modelTwist h₀ z) ≠ 0 := by rwa [cotangentNorm_modelTwist]
    have hcurve := isMIntegralCurve_geodesicFlow_comp hw (hgc.differentiable (by simp) _)
    rw [Function.comp_def] at hcurve
    have hdg : deriv g (cotangentNorm z) =
        2 * π * (deriv R₁ (cotangentNorm z) - deriv R₀ (cotangentNorm z)) :=
      (((h₁.contDiff.differentiable (by simp) _).hasDerivAt.sub
        (h₀.contDiff.differentiable (by simp) _).hasDerivAt).const_mul _).deriv
    have hc : γ = (fun s : ℝ ↦ geodesicFlow (s * deriv g (cotangentNorm (modelTwist h₀ z)))
        (modelTwist h₀ z)) ∘ Subtype.val := by
      rw [hγ]
      funext s
      rw [Function.comp_apply, cotangentNorm_modelTwist, modelTwist_of_cotangentNorm_ne_zero _ hz,
        modelTwist_of_cotangentNorm_ne_zero h₀ hz, ← geodesicFlow_add, h₀.deriv_lineMap h₁, hdg]
      congr 1
      ring
    have hval (s : unitInterval) : MDifferentiableAt (𝓡∂ 1) 𝓘(ℝ) Subtype.val s :=
      (contMDiff_subtypeVal_Icc (n := 1)).mdifferentiable one_ne_zero s
    refine Φ.apply_eq_of_mfderiv_eq_velocity
      (hc ▸ fun s ↦ (hcurve s).mdifferentiableAt.comp s (hval s)) (fun s ↦ ?_) t
    rw [hc, ((hcurve s).comp s (hval s).hasMFDerivAt).mfderiv, hX s]
    -- `(A ∘L B) 1` is `A (B 1)` by definition, but `ContinuousLinearMap.comp_apply` does not
    -- rewrite here: the tangent space of `[0, 1]` at `s` is `ℝ` only up to unfolding.
    exact (congrArg (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) _)
      (mfderiv_subtypeVal_Icc_one s)).trans (one_smul ℝ _)

/-- **Model twists of the same radius are Hamiltonian isotopic.** For twist profiles `R₀` and
`R₁` with the same support radius `r₀`, there is a compactly supported Hamiltonian diffeotopy
`φ_t` of `T*Sⁿ`, for the canonical symplectic form, that fixes every point with `μ ≥ r₀` at
every time and satisfies `φ₁ ∘ τ_{R₀} = τ_{R₁}`. It is generated by the time-independent
Hamiltonian `2π (R₁ - R₀) ∘ μ`. -/
theorem exists_isCompactlySupportedHamiltonian_modelTwist {R₀ R₁ : ℝ → ℝ} {r₀ : ℝ}
    (h₀ : IsTwistProfile R₀ r₀) (h₁ : IsTwistProfile R₁ r₀) :
    ∃ Φ : Diffeotopy ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) ∞
        (CotangentBundle (𝓡 n) (𝕊 n)),
      Φ.IsCompactlySupportedHamiltonian (CotangentBundle.symplecticForm (𝓡 n) (𝕊 n)) ∧
        (∀ t z, r₀ ≤ cotangentNorm z → Φ (t, z) = z) ∧
          ∀ z, Φ.final (modelTwist h₀ z) = modelTwist h₁ z := by
  set g : ℝ → ℝ := fun t ↦ 2 * π * (R₁ t - R₀ t) with hg
  have hge : g.Even := fun t ↦ by
    simp only [hg, h₀.apply_neg, h₁.apply_neg]
    ring
  have hσ := CotangentBundle.isSymplectic_symplecticForm (I := 𝓡 n) (M := 𝕊 n)
  have hG : ContMDiff (((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)).prod (𝓡∂ 1)) 𝓘(ℝ) ∞
      fun p : CotangentBundle (𝓡 n) (𝕊 n) × unitInterval ↦ g (cotangentNorm p.1) :=
    (hge.contMDiff_comp_cotangentNorm (contDiff_const.mul (h₁.contDiff.sub h₀.contDiff))).comp
      contMDiff_fst
  -- `g ∘ μ` vanishes off the compact set `{μ ≤ r₀}`.
  obtain ⟨Φ, hgen, hΦ, -⟩ := Diffeotopy.exists_isCompactlySupportedHamiltonian hσ hG
    (isCompact_setOf_cotangentNorm_le (n := n) r₀) fun p hp ↦ by
      have hr : r₀ ≤ cotangentNorm p.1 := (not_le.1 hp).le
      simp only [hg, h₀.apply_of_le hr, h₁.apply_of_le hr, sub_zero, mul_zero]
  have key := apply_modelTwist_eq_modelTwist_lineMap h₀ h₁ fun t ↦
    hσ.isNondegenerate.isHamiltonianVectorField_iff_eq.1 (hgen.isHamiltonianVectorField t)
  refine ⟨Φ, hΦ, fun t z hz ↦ ?_, fun z ↦ ?_⟩
  · -- The twists are the identity where `μ ≥ r₀`, so the trajectory of `z` is constant.
    have h := key t z
    rwa [modelTwist_apply_of_le h₀ hz, modelTwist_apply_of_le _ hz] at h
  · have h1 : modelTwist (h₀.lineMap h₁ ((1 : unitInterval) : ℝ)) z = modelTwist h₁ z := by
      simp only [coe_modelTwist, Set.Icc.coe_one, sub_self, zero_mul, one_mul, zero_add]
    rw [Diffeotopy.final_apply, key, h1]

end SymplecticGeometry
