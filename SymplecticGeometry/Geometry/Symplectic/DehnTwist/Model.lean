/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.DehnTwist.Geodesic
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import SymplecticGeometry.Analysis.Calculus.ContDiff.Even
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
import TauCeti.Geometry.Manifold.DifferentialForm.Squared

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
* `SymplecticGeometry.modelTwist_apply_of_le`: the model twist is the identity where `μ ≥ r₀`.
* `SymplecticGeometry.modelTwist_cotangent_orthogonal`: it commutes with the cotangent lift of
  every orthogonal transformation of `ℝⁿ⁺¹`.
* `SymplecticGeometry.contMDiff_twistPrimitive`, `SymplecticGeometry.twistPrimitive_of_le`: the
  primitive of the model twist of a twist profile is smooth, and vanishes where `μ ≥ r₀`.
* `SymplecticGeometry.mpullback_modelTwist_liouvilleForm`: the model twist pulls the Liouville
  form `λ` back to `λ + dK` with `K = twistPrimitive R`, so it is exact;
  `SymplecticGeometry.mpullback_modelTwist_symplecticForm`: it preserves `ω = -dλ`.

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

The exactness is checked in the coordinates `(q, p)` at every covector, the zero section
included, so no density argument is needed. With `s = ‖p‖²`, the twist reads
`(q, p) ↦ (C q + S p, C p - s S q)`, and the Liouville form reads `⟪p, δq⟫`
(`liouvilleForm_apply_eq_inner_cotangentCoord`). On the image of `T*Sⁿ`, where `‖q‖ = 1`,
`q ⊥ p`, `q ⊥ δq` and `⟪δq, p⟫ + ⟪q, δp⟫ = 0`, the pulled back form is
`(C² + s S²) ⟪p, δq⟫ + (2 s (C S' - S C') + C S) ⟪p, δp⟫`. Write `K = k (‖p‖²)` by Whitney's
theorem; then `dK = 2 k' ⟪p, δp⟫`. So exactness comes down to `C² + s S² = 1`, which is
`cos² + sin² = 1`, and `2 s (C S' - S C') + C S = 2 k'`
(`two_mul_mul_sub_add_mul_eq_two_mul_deriv`). The second identity follows for `s > 0` from
differentiating the relations between `C`, `S`, `k` and `R`, and at `s = 0` by continuity.
The symplecticity follows by applying `d`, since `d (dK) = 0`.

## References

* [P. Seidel, *A long exact sequence for symplectic Floer cohomology*][Seidel2003], Lemma 1.8
  and equation (1.7) (arXiv version 2): the model twist on `T*Sⁿ` built from the normalized
  geodesic flow.
* [P. Seidel, *Lectures on four-dimensional Dehn twists*][Seidel2008], §1a.
* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], third
  edition, p. 270: the primitive of the twist.
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

/-! ### The geodesic twist in coordinates -/

section twistCoord

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {C S : ℝ → ℝ}

/-- The map `(q, p) ↦ (C ‖p‖² • q + S ‖p‖² • p, C ‖p‖² • p - (‖p‖² * S ‖p‖²) • q)` of `E × E`.
When `cos (θ t) = C (t ^ 2)` and `sin (θ t) = t * S (t ^ 2)`, it is the geodesic twist of `θ` in
the coordinates `(q, p)` of `cotangentCoord` (`cotangentCoord_geodesicTwist`). -/
def twistCoord (C S : ℝ → ℝ) (y : E × E) : E × E :=
  (C (‖y.2‖ ^ 2) • y.1 + S (‖y.2‖ ^ 2) • y.2,
    C (‖y.2‖ ^ 2) • y.2 - (‖y.2‖ ^ 2 * S (‖y.2‖ ^ 2)) • y.1)

theorem twistCoord_def (C S : ℝ → ℝ) (y : E × E) :
    twistCoord C S y =
      (C (‖y.2‖ ^ 2) • y.1 + S (‖y.2‖ ^ 2) • y.2,
        C (‖y.2‖ ^ 2) • y.2 - (‖y.2‖ ^ 2 * S (‖y.2‖ ^ 2)) • y.1) :=
  (rfl)

@[simp]
theorem twistCoord_fst (C S : ℝ → ℝ) (y : E × E) :
    (twistCoord C S y).1 = C (‖y.2‖ ^ 2) • y.1 + S (‖y.2‖ ^ 2) • y.2 := by
  rw [twistCoord_def]

@[simp]
theorem twistCoord_snd (C S : ℝ → ℝ) (y : E × E) :
    (twistCoord C S y).2 = C (‖y.2‖ ^ 2) • y.2 - (‖y.2‖ ^ 2 * S (‖y.2‖ ^ 2)) • y.1 := by
  rw [twistCoord_def]

/-- The map `twistCoord C S` is `C^m` when `C` and `S` are. -/
theorem contDiff_twistCoord {m : WithTop ℕ∞} (hC : ContDiff ℝ m C) (hS : ContDiff ℝ m S) :
    ContDiff ℝ m (twistCoord (E := E) C S) := by
  have hn : ContDiff ℝ m fun y : E × E ↦ ‖y.2‖ ^ 2 := (contDiff_norm_sq ℝ).comp contDiff_snd
  rw [show twistCoord (E := E) C S = _ from funext (twistCoord_def C S)]
  exact (((hC.comp hn).smul contDiff_fst).add ((hS.comp hn).smul contDiff_snd)).prodMk
    (((hC.comp hn).smul contDiff_snd).sub ((hn.mul (hS.comp hn)).smul contDiff_fst))

/-- The map `twistCoord C S` is differentiable when `C` and `S` are `C¹`. -/
theorem differentiable_twistCoord (hC : ContDiff ℝ 1 C) (hS : ContDiff ℝ 1 S) :
    Differentiable ℝ (twistCoord (E := E) C S) :=
  (contDiff_twistCoord hC hS).differentiable one_ne_zero

/-- For `C¹` functions `C` and `S`, the derivative of `twistCoord C S` at `(q, p)` sends
`(δq, δp)`, with `s = ‖p‖²` and `δs = 2 ⟪p, δp⟫`, to
`(C δq + δs C' q + S δp + δs S' p, C δp + δs C' p - (s S δq + (δs S + s δs S') q))`. -/
theorem fderiv_twistCoord_apply (hC : ContDiff ℝ 1 C) (hS : ContDiff ℝ 1 S) (y u : E × E) :
    fderiv ℝ (twistCoord C S) y u =
      (C (‖y.2‖ ^ 2) • u.1 + (2 * ⟪y.2, u.2⟫_ℝ * deriv C (‖y.2‖ ^ 2)) • y.1 +
          (S (‖y.2‖ ^ 2) • u.2 + (2 * ⟪y.2, u.2⟫_ℝ * deriv S (‖y.2‖ ^ 2)) • y.2),
        C (‖y.2‖ ^ 2) • u.2 + (2 * ⟪y.2, u.2⟫_ℝ * deriv C (‖y.2‖ ^ 2)) • y.2 -
          ((‖y.2‖ ^ 2 * S (‖y.2‖ ^ 2)) • u.1 +
            (2 * ⟪y.2, u.2⟫_ℝ * S (‖y.2‖ ^ 2) +
              ‖y.2‖ ^ 2 * (2 * ⟪y.2, u.2⟫_ℝ * deriv S (‖y.2‖ ^ 2))) • y.1)) := by
  have hn := (hasFDerivAt_snd (p := y)).norm_sq
  have hC' := (hC.differentiable one_ne_zero _).hasDerivAt.hasFDerivAt.comp y hn
  have hS' := (hS.differentiable one_ne_zero _).hasDerivAt.hasFDerivAt.comp y hn
  have h := (((hC'.smul hasFDerivAt_fst).add (hS'.smul hasFDerivAt_snd)).prodMk
    ((hC'.smul hasFDerivAt_snd).sub ((hn.mul hS').smul hasFDerivAt_fst))).congr_of_eventuallyEq
    (f₁ := twistCoord C S) (.of_forall fun x ↦ by simp [twistCoord_def])
  rw [h.fderiv]
  ext1 <;> simp <;> ring_nf

end twistCoord

/-- If `cos ∘ θ = C (t ^ 2)` and `sin ∘ θ = t * S (t ^ 2)`, and `cos (θ 0) = -1`, then the
geodesic twist of `θ` acts on the coordinates `(q, p)` by `twistCoord C S`. -/
theorem cotangentCoord_geodesicTwist {θ C S : ℝ → ℝ} (hC : ∀ t, cos (θ t) = C (t ^ 2))
    (hS : ∀ t, sin (θ t) = t * S (t ^ 2)) (h0 : cos (θ 0) = -1)
    (z : CotangentBundle (𝓡 n) (𝕊 n)) :
    cotangentCoord (geodesicTwist θ z) = twistCoord C S (cotangentCoord z) := by
  rw [twistCoord_def]
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
theorem the geodesic twist of `θ` acts on the coordinates `(q, p)` by `twistCoord C S` for smooth
`C` and `S`. -/
theorem exists_cotangentCoord_geodesicTwist {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ)
    (hc : ∀ t, cos (θ (-t)) = cos (θ t)) (hs : ∀ t, sin (θ (-t)) = -sin (θ t))
    (h0 : cos (θ 0) = -1) :
    ∃ C S : ℝ → ℝ, ContDiff ℝ ∞ C ∧ ContDiff ℝ ∞ S ∧ ∀ z : CotangentBundle (𝓡 n) (𝕊 n),
      cotangentCoord (geodesicTwist θ z) = twistCoord C S (cotangentCoord z) := by
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
  exact contMDiff_of_contMDiff_cotangentCoord_comp
    (((contDiff_twistCoord hCd hSd).contMDiff.comp contMDiff_cotangentCoord).congr hG)

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
    cotangentCoord_cotangent_orthogonal, hG, twistCoord_def, twistCoord_def,
    LinearIsometryEquiv.norm_map]
  simp only [map_add, map_sub, map_smul]

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

/-! ### Exactness and symplecticity of the model twist -/

/-- Let `C`, `S` and `k` be `C¹` functions with `cos (θ t) = C (t ^ 2)`,
`sin (θ t) = t * S (t ^ 2)` and `f t = k (t ^ 2)`, where `f' (t) = t θ' (t)`. Then
`2 s (C S' - S C') + C S = 2 k'` at every `s ≥ 0`: at `s = t ^ 2 > 0` by differentiating the
three relations, and at `s = 0` by continuity. -/
theorem two_mul_mul_sub_add_mul_eq_two_mul_deriv {θ θ' C S f k : ℝ → ℝ}
    (hθ : ∀ t, HasDerivAt θ (θ' t) t) (hf : ∀ t, HasDerivAt f (t * θ' t) t)
    (hCd : ContDiff ℝ 1 C) (hSd : ContDiff ℝ 1 S) (hkd : ContDiff ℝ 1 k)
    (hC : ∀ t, cos (θ t) = C (t ^ 2)) (hS : ∀ t, sin (θ t) = t * S (t ^ 2))
    (hk : ∀ t, f t = k (t ^ 2)) (s : ℝ) (hs : 0 ≤ s) :
    2 * s * (C s * deriv S s - S s * deriv C s) + C s * S s = 2 * deriv k s := by
  have hC' : ∀ x, HasDerivAt C (deriv C x) x := fun x ↦
    (hCd.differentiable one_ne_zero x).hasDerivAt
  have hS' : ∀ x, HasDerivAt S (deriv S x) x := fun x ↦
    (hSd.differentiable one_ne_zero x).hasDerivAt
  have hk' : ∀ x, HasDerivAt k (deriv k x) x := fun x ↦
    (hkd.differentiable one_ne_zero x).hasDerivAt
  have key : ∀ t, 0 < t → 2 * t ^ 2 * (C (t ^ 2) * deriv S (t ^ 2) -
      S (t ^ 2) * deriv C (t ^ 2)) + C (t ^ 2) * S (t ^ 2) = 2 * deriv k (t ^ 2) := by
    intro t ht
    have hsq : HasDerivAt (fun t : ℝ ↦ t ^ 2) (2 * t) t := by
      simpa using hasDerivAt_pow 2 t
    have h1 := ((hC' _).comp t hsq).unique
      (show HasDerivAt (fun t ↦ C (t ^ 2)) (-sin (θ t) * θ' t) t by
        rw [← funext hC]; exact (hθ t).cos)
    have h2 := ((hasDerivAt_id' t).mul ((hS' _).comp t hsq)).unique
      (show HasDerivAt (fun t ↦ t * S (t ^ 2)) (cos (θ t) * θ' t) t by
        rw [← funext hS]; exact (hθ t).sin)
    have h3 := ((hk' _).comp t hsq).unique
      (show HasDerivAt (fun t ↦ k (t ^ 2)) (t * θ' t) t by rw [← funext hk]; exact hf t)
    simp only [Function.comp_apply] at h1 h2 h3
    have hcs := sin_sq_add_cos_sq (θ t)
    rw [hS t, hC t] at hcs
    rw [hC t] at h2
    rw [hS t] at h1
    have : t * (2 * t ^ 2 * (C (t ^ 2) * deriv S (t ^ 2) - S (t ^ 2) * deriv C (t ^ 2)) +
        C (t ^ 2) * S (t ^ 2) - 2 * deriv k (t ^ 2)) = 0 := by
      linear_combination (t * C (t ^ 2)) * h2 - t ^ 2 * S (t ^ 2) * h1 - h3 + θ' t * t * hcs
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h ht.ne'
    · linarith
  have hcont : Continuous fun s ↦ 2 * s * (C s * deriv S s - S s * deriv C s) + C s * S s -
      2 * deriv k s := by
    have := hCd.continuous_deriv le_rfl
    have := hSd.continuous_deriv le_rfl
    have := hkd.continuous_deriv le_rfl
    fun_prop
  have hpos : Ioi (0 : ℝ) ⊆ {s | 2 * s * (C s * deriv S s - S s * deriv C s) + C s * S s -
      2 * deriv k s = 0} := fun s hs ↦ by
    have := key (√s) (sqrt_pos.2 hs)
    rw [sq_sqrt (le_of_lt hs)] at this
    simp only [mem_ofPred_eq]
    linarith
  have := (isClosed_eq hcont continuous_const).closure_subset_iff.2 hpos
    (by rw [closure_Ioi]; exact hs)
  simp only [mem_ofPred_eq] at this
  linarith

/-- Whitney's theorem for a twist profile `R`, with angle function `θ = 2π R'`: there are smooth
`C`, `S` and `k` with `cos (θ t) = C (t ^ 2)`, `sin (θ t) = t * S (t ^ 2)` and
`2π (R'(t) t - R t) = k (t ^ 2)`. At every `s ≥ 0` they satisfy `C(s)² + s S(s)² = 1` and
`2 s (C S' - S C') + C S = 2 k'`. -/
theorem IsTwistProfile.exists_contDiff_comp_sq {R : ℝ → ℝ} {r₀ : ℝ} (hR : IsTwistProfile R r₀) :
    ∃ C S k : ℝ → ℝ, ContDiff ℝ ∞ C ∧ ContDiff ℝ ∞ S ∧ ContDiff ℝ ∞ k ∧
      (∀ t, cos (2 * π * deriv R t) = C (t ^ 2)) ∧
      (∀ t, sin (2 * π * deriv R t) = t * S (t ^ 2)) ∧
      (∀ t, 2 * π * (deriv R t * t - R t) = k (t ^ 2)) ∧
      (∀ s, 0 ≤ s → C s ^ 2 + s * S s ^ 2 = 1) ∧
      ∀ s, 0 ≤ s → 2 * s * (C s * deriv S s - S s * deriv C s) + C s * S s = 2 * deriv k s := by
  have hθ : ContDiff ℝ ∞ fun t ↦ 2 * π * deriv R t := contDiff_const.mul hR.contDiff_deriv
  obtain ⟨C, hCd, hC⟩ := Function.Even.exists_contDiff_comp_sq
    (f := fun t ↦ cos (2 * π * deriv R t)) hR.cos_two_pi_mul_deriv_neg (contDiff_cos.comp hθ)
  obtain ⟨S, hSd, hS⟩ := Function.Odd.exists_contDiff_mul_comp_sq
    (f := fun t ↦ sin (2 * π * deriv R t)) hR.sin_two_pi_mul_deriv_neg (contDiff_sin.comp hθ)
  obtain ⟨k, hkd, hk⟩ := Function.Even.exists_contDiff_comp_sq
    (f := fun t ↦ 2 * π * (deriv R t * t - R t))
    (fun t ↦ congrArg (2 * π * ·) (hR.even_deriv_mul_sub t))
    (contDiff_const.mul ((hR.contDiff_deriv.mul contDiff_id).sub hR.contDiff))
  have hR' : ∀ t, HasDerivAt R (deriv R t) t := fun t ↦
    (hR.contDiff.differentiable (by simp) t).hasDerivAt
  have hR'' : ∀ t, HasDerivAt (deriv R) (deriv (deriv R) t) t := fun t ↦
    (hR.contDiff_deriv.differentiable (by simp) t).hasDerivAt
  refine ⟨C, S, k, hCd, hSd, hkd, hC, hS, hk, fun s hs ↦ ?_,
    two_mul_mul_sub_add_mul_eq_two_mul_deriv (θ := fun t ↦ 2 * π * deriv R t)
      (θ' := fun t ↦ 2 * π * deriv (deriv R) t) (f := fun t ↦ 2 * π * (deriv R t * t - R t))
      (fun t ↦ (hR'' t).const_mul _)
      (fun t ↦ ((((hR'' t).mul (hasDerivAt_id' t)).sub (hR' t)).const_mul (2 * π)).congr_deriv
        (by ring))
      (hCd.of_le (by simp)) (hSd.of_le (by simp)) (hkd.of_le (by simp)) hC hS hk⟩
  have h := sin_sq_add_cos_sq (2 * π * deriv R √s)
  rw [hC, hS, sq_sqrt hs] at h
  linear_combination h - S s ^ 2 * sq_sqrt hs

/-- The pointwise identity behind the exactness of the model twist. Let `y = (q, p)` and
`u = (δq, δp)` satisfy `⟪q, q⟫ = 1`, `q ⊥ p`, `q ⊥ δq` and `⟪δq, p⟫ + ⟪q, δp⟫ = 0`, as the
coordinates of a covector of `T*Sⁿ` and their differentials do. If, with `s = ‖p‖²`,
`C(s)² + s S(s)² = 1` and `2 s (C S' - S C') + C S = 2 k'` at `s`, then the second component of
`twistCoord C S y`, paired with the first component of the derivative of `twistCoord C S` at `y`
applied to `u`, is `⟪p, δq⟫ + k' (2 ⟪p, δp⟫)`. -/
theorem inner_twistCoord_snd_fderiv_twistCoord_fst {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {C S : ℝ → ℝ} (hC : ContDiff ℝ 1 C) (hS : ContDiff ℝ 1 S)
    {y u : E × E} {k' : ℝ} (hqq : ⟪y.1, y.1⟫_ℝ = 1) (hqp : ⟪y.1, y.2⟫_ℝ = 0)
    (hqdq : ⟪y.1, u.1⟫_ℝ = 0) (hd : ⟪u.1, y.2⟫_ℝ + ⟪y.1, u.2⟫_ℝ = 0)
    (h1 : C (‖y.2‖ ^ 2) ^ 2 + ‖y.2‖ ^ 2 * S (‖y.2‖ ^ 2) ^ 2 = 1)
    (h2 : 2 * ‖y.2‖ ^ 2 * (C (‖y.2‖ ^ 2) * deriv S (‖y.2‖ ^ 2) -
      S (‖y.2‖ ^ 2) * deriv C (‖y.2‖ ^ 2)) + C (‖y.2‖ ^ 2) * S (‖y.2‖ ^ 2) = 2 * k') :
    ⟪(twistCoord C S y).2, (fderiv ℝ (twistCoord C S) y u).1⟫_ℝ =
      ⟪y.2, u.1⟫_ℝ + k' * (2 * ⟪y.2, u.2⟫_ℝ) := by
  have hpp : ⟪y.2, y.2⟫_ℝ = ‖y.2‖ ^ 2 := real_inner_self_eq_norm_sq y.2
  rw [twistCoord_snd, fderiv_twistCoord_apply hC hS]
  simp only [inner_add_right, inner_sub_left, real_inner_smul_left, real_inner_smul_right, hqq,
    hpp, hqdq, real_inner_comm y.1 y.2, hqp]
  rw [real_inner_comm y.2 u.1] at hd
  linear_combination (⟪y.2, u.1⟫_ℝ) * h1 + ⟪y.2, u.2⟫_ℝ * h2 -
    ‖y.2‖ ^ 2 * S (‖y.2‖ ^ 2) ^ 2 * hd

/-- The model twist of a twist profile `R` pulls the Liouville form `λ` of `T*Sⁿ` back to
`λ + dK`, where `K = twistPrimitive R` is the function `2π (R'(μ) μ - R(μ))`: the model twist is
an exact symplectomorphism. -/
theorem mpullback_modelTwist_liouvilleForm {R : ℝ → ℝ} {r₀ : ℝ} (hR : IsTwistProfile R r₀) :
    SmoothForm.mpullback (modelTwist (n := n) hR) (modelTwist hR).contMDiff
        (CotangentBundle.liouvilleForm (𝓡 n) (𝕊 n)) =
      CotangentBundle.liouvilleForm (𝓡 n) (𝕊 n) +
        mextDerivₗ ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) 0
          (SmoothForm.ofFunction ⟨twistPrimitive R, contMDiff_twistPrimitive hR⟩) := by
  obtain ⟨C, S, k, hCd, hSd, hkd, hC, hS, hk, h1, h2⟩ := hR.exists_contDiff_comp_sq
  have hC1 : ContDiff ℝ 1 C := hCd.of_le (by simp)
  have hS1 : ContDiff ℝ 1 S := hSd.of_le (by simp)
  -- The twist and its primitive in the coordinates `(q, p)`.
  have hτ : cotangentCoord ∘ modelTwist (n := n) hR = twistCoord C S ∘ cotangentCoord :=
    funext fun y ↦ by
      rw [Function.comp_apply, Function.comp_apply, coe_modelTwist,
        modelTwistFun_eq_geodesicTwist,
        cotangentCoord_geodesicTwist hC hS (by rw [hR.two_pi_mul_deriv_zero, cos_pi])]
  have hK : twistPrimitive (n := n) R = fun z ↦ k (cotangentNorm z ^ 2) :=
    funext fun z ↦ by rw [twistPrimitive_def, hk]
  apply Subtype.ext
  funext z
  ext v
  have hdq : mfderiv ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) 𝓘(ℝ, (𝔼 n) × 𝔼 n)
      (cotangentCoord ∘ modelTwist hR) z (v 0) =
      fderiv ℝ (twistCoord C S) (cotangentCoord z)
        (mfderiv ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) 𝓘(ℝ, (𝔼 n) × 𝔼 n)
          cotangentCoord z (v 0)) := by
    rw [hτ, (differentiable_twistCoord hC1 hS1 _).hasFDerivAt.mfderiv_comp_cotangentCoord_apply]
  have hdK : (mextDerivₗ ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) 0
      (SmoothForm.ofFunction ⟨twistPrimitive R, contMDiff_twistPrimitive hR⟩)).val z v =
      mvfderiv ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) (twistPrimitive R) z
        (v 0) := by
    rw [show v = ![v 0] from funext fun i ↦ by rw [Fin.fin_one_eq_zero i, Matrix.cons_val_zero],
      mextDerivₗ_zero_apply]
    exact congrArg (fun g ↦ mvfderiv _ g z (v 0)) (SmoothForm.ofFunction_apply_zero _)
  -- The constraints on the coordinates and their differentials.
  have hqq : ⟪(cotangentCoord z).1, (cotangentCoord z).1⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, cotangentCoord_fst, norm_eq_of_mem_sphere, one_pow]
  have hqp : ⟪(cotangentCoord z).1, (cotangentCoord z).2⟫_ℝ = 0 := by
    rw [cotangentCoord_fst]
    exact inner_proj_cotangentCoord_snd z
  have hqdq := inner_fst_mfderiv_cotangentCoord z (v 0)
  have hd := inner_fst_mfderiv_cotangentCoord_add_inner_snd z (v 0)
  have hτz : cotangentCoord (modelTwist hR z) = twistCoord C S (cotangentCoord z) :=
    congrFun hτ z
  rw [SmoothForm.coe_mpullback, mpullback_liouvilleForm_apply_eq_inner_cotangentCoord
    ((modelTwist hR).contMDiff.mdifferentiableAt (by simp)), AddMemClass.coe_add, Pi.add_apply,
    ContinuousAlternatingMap.add_apply, liouvilleForm_apply_eq_inner_cotangentCoord, hdK, hK,
    mvfderiv_comp_cotangentNorm_sq (hkd.of_le (by simp)), hdq, hτz, cotangentNorm_def]
  generalize (mfderiv ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) 𝓘(ℝ, (𝔼 n) × 𝔼 n)
    cotangentCoord z (v 0) : (𝔼 n) × 𝔼 n) = u at hqdq hd ⊢
  exact inner_twistCoord_snd_fderiv_twistCoord_fst hC1 hS1 hqq hqp hqdq hd (h1 _ (sq_nonneg _))
    (h2 _ (sq_nonneg _))

/-- The model twist of a twist profile preserves the canonical symplectic form `ω = -dλ` of
`T*Sⁿ`. -/
theorem mpullback_modelTwist_symplecticForm {R : ℝ → ℝ} {r₀ : ℝ} (hR : IsTwistProfile R r₀) :
    SmoothForm.mpullback (modelTwist (n := n) hR) (modelTwist hR).contMDiff
        (CotangentBundle.symplecticForm (𝓡 n) (𝕊 n)) =
      CotangentBundle.symplecticForm (𝓡 n) (𝕊 n) := by
  rw [CotangentBundle.symplecticForm_eq_neg_mextDerivₗ, map_neg,
    ← SmoothForm.mextDerivₗ_mpullback, mpullback_modelTwist_liouvilleForm hR, map_add,
    ← LinearMap.comp_apply (mextDerivₗ _ 1), mextDerivₗ_comp_mextDerivₗ, LinearMap.zero_apply,
    add_zero]

end SymplecticGeometry
