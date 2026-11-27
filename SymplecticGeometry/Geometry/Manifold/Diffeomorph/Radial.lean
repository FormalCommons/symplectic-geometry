/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Topology.Order.IntermediateValue
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic

/-!
# Radial rescalings `x ↦ τ x • x` as diffeomorphisms

Let `F` be a real normed space and `τ : F → ℝ` differentiable with `0 < τ x + dτ_x x` for every
`x`. The derivative of `s ↦ s * τ (s • u)` at `s` is `τ y + dτ_y y` for `y = s • u`, so this
function is strictly increasing on every line through `0`
(`SymplecticGeometry.strictMono_mul_apply_smul`). Hence `τ` is positive
(`SymplecticGeometry.pos_of_forall_add_fderiv_pos`), the map `σ x = τ x • x` sends each ray from
`0` into itself, and it is injective there. If `τ = 1` outside some ball, the intermediate value
theorem on each ray shows that `σ` is onto. Its differential `v ↦ τ x • v + dτ_x v • x` is
injective: a vector `v` in its kernel satisfies `dτ_x v * (τ x + dτ_x x) = 0`, so `dτ_x v = 0` and
then `v = 0`.

The differential itself is `SymplecticGeometry.hasFDerivAt_smul_self`, and
`SymplecticGeometry.mfderiv_radialSmulDiffeomorph_apply` states it for the diffeomorphism.

## Main results

* `SymplecticGeometry.injective_smul_self`, `SymplecticGeometry.surjective_smul_self`: `σ` is
  injective, and onto when `τ = 1` outside a ball.
* `SymplecticGeometry.isLocalDiffeomorph_smul_self`: for `F` finite-dimensional and `τ` of class
  `C^n` with `1 ≤ n`, `σ` is a `C^n` local diffeomorphism, by Tau Ceti's inverse function theorem
  `TauCeti.isLocalDiffeomorphAt_of_injective_mfderiv`.
* `SymplecticGeometry.radialSmulDiffeomorph`: `σ` as a `C^n` diffeomorphism of `F`, from Mathlib's
  `IsLocalDiffeomorph.diffeomorphOfBijective`, with `radialSmulDiffeomorph_apply`.
* `SymplecticGeometry.norm_smul_self_lt_iff` (and its `le` and `eq` versions): if `τ = 1` on the
  sphere of radius `r`, then `‖τ x • x‖ < r ↔ ‖x‖ < r`, so that `σ` maps the open ball, the
  closed ball and the sphere of radius `r` onto themselves
  (`SymplecticGeometry.image_radialSmulDiffeomorph_ball` and its neighbours).

This is the reparametrization of a ball along its rays in Step 2 of the proof of Theorem 8.5 of
[CieliebakEliashberg2012].

## References

* [K. Cieliebak, Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Theorem 8.5.
-/

public section

namespace SymplecticGeometry

open Set Metric
open scoped Manifold ContDiff

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {τ : F → ℝ}

/-- If `0 < τ y + dτ_y y` for every `y`, then for each `u` the function `s ↦ s * τ (s • u)` is
strictly increasing: its derivative at `s` is `τ y + dτ_y y` with `y = s • u`. -/
theorem strictMono_mul_apply_smul (hτ : Differentiable ℝ τ)
    (hd : ∀ x, 0 < τ x + fderiv ℝ τ x x) (u : F) :
    StrictMono fun s : ℝ ↦ s * τ (s • u) := by
  have hder (s : ℝ) : HasDerivAt (fun s : ℝ ↦ s * τ (s • u))
      (τ (s • u) + fderiv ℝ τ (s • u) (s • u)) s := by
    have h1 : HasDerivAt (fun s : ℝ ↦ s • u) u s := by
      simpa using (hasDerivAt_id s).smul_const u
    have h2 : HasDerivAt (fun s : ℝ ↦ τ (s • u)) (fderiv ℝ τ (s • u) u) s :=
      (hτ (s • u)).hasFDerivAt.comp_hasDerivAt s h1
    convert (hasDerivAt_id' s).mul h2 using 1
    simp [map_smul]
  exact strictMono_of_deriv_pos fun s ↦ (hder s).deriv ▸ hd _

/-- If `τ` is differentiable and `0 < τ y + dτ_y y` for every `y`, then `τ` is positive. -/
theorem pos_of_forall_add_fderiv_pos (hτ : Differentiable ℝ τ)
    (hd : ∀ x, 0 < τ x + fderiv ℝ τ x x) (x : F) : 0 < τ x := by
  simpa using strictMono_mul_apply_smul hτ hd x zero_lt_one

/-- If `τ` is differentiable and `0 < τ y + dτ_y y` for every `y`, then `x ↦ τ x • x` is
injective. -/
theorem injective_smul_self (hτ : Differentiable ℝ τ) (hd : ∀ x, 0 < τ x + fderiv ℝ τ x x) :
    Function.Injective fun x : F ↦ τ x • x := by
  intro x y hxy
  simp only at hxy
  have hpos := pos_of_forall_add_fderiv_pos hτ hd
  have hy : y = (τ x / τ y) • x := by
    rw [div_eq_inv_mul, mul_smul, hxy, inv_smul_smul₀ (hpos y).ne']
  rcases eq_or_ne x 0 with rfl | hx
  · rw [hy, smul_zero]
  set t := τ x / τ y
  have ht : t * τ (t • x) = 1 * τ ((1 : ℝ) • x) := by
    refine smul_left_injective ℝ hx ?_
    simp only [one_smul, one_mul]
    rw [hxy, hy, smul_smul, mul_comm]
  rw [hy, strictMono_mul_apply_smul hτ hd x |>.injective ht, one_smul]

/-- If `τ` is continuous and `τ = 1` outside a ball, then `x ↦ τ x • x` is onto. -/
theorem surjective_smul_self (hτ : Continuous τ) {R : ℝ} (hR : ∀ x, R ≤ ‖x‖ → τ x = 1) :
    Function.Surjective fun x : F ↦ τ x • x := by
  intro y
  rcases eq_or_ne y 0 with rfl | hy
  · exact ⟨0, by simp⟩
  set S := max 1 (R / ‖y‖)
  have hS : 1 ≤ S := le_max_left _ _
  have hSy : τ (S • y) = 1 := hR _ <| by
    rw [norm_smul, Real.norm_of_nonneg (by linarith)]
    exact (div_le_iff₀ (norm_pos_iff.2 hy)).1 (le_max_right _ _)
  have hcont : ContinuousOn (fun s : ℝ ↦ s * τ (s • y)) (Icc 0 S) := by fun_prop
  obtain ⟨s, -, hs⟩ := intermediate_value_Icc (by linarith) hcont
    (show (1 : ℝ) ∈ Icc (0 * τ ((0 : ℝ) • y)) (S * τ (S • y)) by simp [hSy, hS])
  exact ⟨s • y, by simp only [smul_smul, mul_comm, hs, one_smul]⟩

/-- If `τ` is differentiable at `x`, the differential of `y ↦ τ y • y` at `x` is
`v ↦ τ x • v + dτ_x v • x`. -/
theorem hasFDerivAt_smul_self {x : F} (hτ : DifferentiableAt ℝ τ x) :
    HasFDerivAt (fun y ↦ τ y • y)
      (τ x • ContinuousLinearMap.id ℝ F + (fderiv ℝ τ x).smulRight x) x :=
  hτ.hasFDerivAt.smul (hasFDerivAt_id x)

/-- If `τ` is differentiable at `x` with `0 < τ x + dτ_x x` and `τ x ≠ 0`, the differential
`v ↦ τ x • v + dτ_x v • x` of `x ↦ τ x • x` at `x` is injective. -/
theorem injective_fderiv_smul_self {x : F} (hτ : DifferentiableAt ℝ τ x) (hx : τ x ≠ 0)
    (hd : 0 < τ x + fderiv ℝ τ x x) : Function.Injective (fderiv ℝ (fun x ↦ τ x • x) x) := by
  rw [(hasFDerivAt_smul_self hτ).fderiv, injective_iff_map_eq_zero]
  intro v hv
  have hv' : τ x • v + fderiv ℝ τ x v • x = 0 := by simpa using hv
  have ha : fderiv ℝ τ x v = 0 := by
    have h := congrArg (fderiv ℝ τ x) hv'
    simp only [map_add, map_smul, map_zero, smul_eq_mul] at h
    have h' : fderiv ℝ τ x v * (τ x + fderiv ℝ τ x x) = 0 := by linarith
    exact (mul_eq_zero.1 h').resolve_right hd.ne'
  rw [ha, zero_smul, add_zero] at hv'
  exact (smul_eq_zero.1 hv').resolve_left hx

/-- For `F` finite-dimensional, `1 ≤ n` and `τ` of class `C^n` with `0 < τ y + dτ_y y` for every
`y`, the map `x ↦ τ x • x` is a `C^n` local diffeomorphism. -/
theorem isLocalDiffeomorph_smul_self [FiniteDimensional ℝ F] {n : WithTop ℕ∞} (hn : 1 ≤ n)
    (hτ : ContDiff ℝ n τ) (hd : ∀ x, 0 < τ x + fderiv ℝ τ x x) :
    IsLocalDiffeomorph 𝓘(ℝ, F) 𝓘(ℝ, F) n fun x : F ↦ τ x • x := fun x ↦ by
  have hτ' : Differentiable ℝ τ := hτ.differentiable (by positivity)
  refine TauCeti.isLocalDiffeomorphAt_of_injective_mfderiv (s := univ)
    (hτ.smul contDiff_id).contMDiff.contMDiffOn isOpen_univ (mem_univ x)
    BoundarylessManifold.isInteriorPoint hn ?_ rfl
  rw [mfderiv_eq_fderiv, ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_comp]
  exact (NormedSpace.fromTangentSpace _).symm.injective.comp
    ((injective_fderiv_smul_self (hτ' x) (pos_of_forall_add_fderiv_pos hτ' hd x).ne' (hd x)).comp
      (NormedSpace.fromTangentSpace x).injective)

/-- For `F` finite-dimensional, `1 ≤ n` and `τ : F → ℝ` of class `C^n` with `0 < τ y + dτ_y y`
for every `y` and `τ = 1` outside a ball, the map `x ↦ τ x • x` as a `C^n` diffeomorphism of `F`
(`radialSmulDiffeomorph_apply`). -/
noncomputable def radialSmulDiffeomorph [FiniteDimensional ℝ F] {n : WithTop ℕ∞} (hn : 1 ≤ n)
    (hτ : ContDiff ℝ n τ) (hd : ∀ x, 0 < τ x + fderiv ℝ τ x x) {R : ℝ}
    (hR : ∀ x, R ≤ ‖x‖ → τ x = 1) : F ≃ₘ^n⟮𝓘(ℝ, F), 𝓘(ℝ, F)⟯ F :=
  (isLocalDiffeomorph_smul_self hn hτ hd).diffeomorphOfBijective
    ⟨injective_smul_self (hτ.differentiable (by positivity)) hd,
      surjective_smul_self hτ.continuous hR⟩

section radialSmulDiffeomorph

variable [FiniteDimensional ℝ F] {n : WithTop ℕ∞} (hn : 1 ≤ n) (hτ : ContDiff ℝ n τ)
  (hd : ∀ x, 0 < τ x + fderiv ℝ τ x x) {R : ℝ} (hR : ∀ x, R ≤ ‖x‖ → τ x = 1)

/-- The underlying map of `radialSmulDiffeomorph` is `x ↦ τ x • x`. -/
theorem coe_radialSmulDiffeomorph :
    ⇑(radialSmulDiffeomorph hn hτ hd hR) = fun x ↦ τ x • x := by
  unfold radialSmulDiffeomorph
  exact IsLocalDiffeomorph.coe_diffeomorphOfBijective _ _

@[simp]
theorem radialSmulDiffeomorph_apply (x : F) :
    radialSmulDiffeomorph hn hτ hd hR x = τ x • x := by
  rw [coe_radialSmulDiffeomorph]

/-- The differential of `radialSmulDiffeomorph` at `x` is `v ↦ τ x • v + dτ_x v • x`. -/
theorem mfderiv_radialSmulDiffeomorph_apply (x v : F) :
    mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) (radialSmulDiffeomorph hn hτ hd hR) x v =
      τ x • v + fderiv ℝ τ x v • x := by
  rw [coe_radialSmulDiffeomorph,
    (hasFDerivAt_smul_self (hτ.differentiable (by positivity) x)).hasMFDerivAt.mfderiv]
  -- The goal applies the differential to `v` seen as a tangent vector, where `simp` does not
  -- rewrite; `e` states the same equality in `F`.
  have e : (τ x • ContinuousLinearMap.id ℝ F + (fderiv ℝ τ x).smulRight x) v =
      τ x • v + fderiv ℝ τ x v • x := by
    simp
  exact e

end radialSmulDiffeomorph

/-- If `τ = 1` on the sphere of radius `r ≥ 0`, then `‖τ x • x‖` is the value at `‖x‖` of a
strictly increasing function that fixes `r`. -/
private theorem exists_strictMono_norm_smul_self (hτ : Differentiable ℝ τ)
    (hd : ∀ x, 0 < τ x + fderiv ℝ τ x x) {r : ℝ} (hr0 : 0 ≤ r)
    (hr : ∀ x : F, ‖x‖ = r → τ x = 1) (x : F) :
    ∃ g : ℝ → ℝ, StrictMono g ∧ g ‖x‖ = ‖τ x • x‖ ∧ g r = r := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact ⟨id, strictMono_id, by simp, rfl⟩
  have hx' : 0 < ‖x‖ := norm_pos_iff.2 hx
  set u := ‖x‖⁻¹ • x
  have hu : ‖u‖ = 1 := by simp [u, norm_smul, hx'.ne']
  refine ⟨fun s ↦ s * τ (s • u), strictMono_mul_apply_smul hτ hd u, ?_, ?_⟩
  · simp only [u, smul_smul, mul_inv_cancel₀ hx'.ne', one_smul, norm_smul,
      Real.norm_of_nonneg (pos_of_forall_add_fderiv_pos hτ hd x).le, mul_comm]
  · simp [hr (r • u) (by rw [norm_smul, hu, mul_one, Real.norm_of_nonneg hr0])]

/-- If `τ = 1` on the sphere of radius `r`, then `x ↦ τ x • x` keeps the open ball of radius `r`:
`‖τ x • x‖ < r ↔ ‖x‖ < r`. -/
theorem norm_smul_self_lt_iff (hτ : Differentiable ℝ τ) (hd : ∀ x, 0 < τ x + fderiv ℝ τ x x)
    {r : ℝ} (hr : ∀ x : F, ‖x‖ = r → τ x = 1) (x : F) : ‖τ x • x‖ < r ↔ ‖x‖ < r := by
  rcases lt_or_ge r 0 with hr0 | hr0
  · exact iff_of_false (fun h ↦ ((norm_nonneg _).trans_lt h).not_ge hr0.le)
      (fun h ↦ ((norm_nonneg _).trans_lt h).not_ge hr0.le)
  obtain ⟨g, hg, hgx, hgr⟩ := exists_strictMono_norm_smul_self hτ hd hr0 hr x
  rw [← hgx]
  conv_lhs => rw [← hgr]
  exact hg.lt_iff_lt

/-- If `τ = 1` on the sphere of radius `r`, then `x ↦ τ x • x` keeps the closed ball of radius
`r`: `‖τ x • x‖ ≤ r ↔ ‖x‖ ≤ r`. -/
theorem norm_smul_self_le_iff (hτ : Differentiable ℝ τ) (hd : ∀ x, 0 < τ x + fderiv ℝ τ x x)
    {r : ℝ} (hr : ∀ x : F, ‖x‖ = r → τ x = 1) (x : F) : ‖τ x • x‖ ≤ r ↔ ‖x‖ ≤ r := by
  rcases lt_or_ge r 0 with hr0 | hr0
  · exact iff_of_false (fun h ↦ ((norm_nonneg _).trans h).not_gt hr0)
      (fun h ↦ ((norm_nonneg _).trans h).not_gt hr0)
  obtain ⟨g, hg, hgx, hgr⟩ := exists_strictMono_norm_smul_self hτ hd hr0 hr x
  rw [← hgx]
  conv_lhs => rw [← hgr]
  exact hg.le_iff_le

/-- If `τ = 1` on the sphere of radius `r`, then `x ↦ τ x • x` keeps that sphere:
`‖τ x • x‖ = r ↔ ‖x‖ = r`. -/
theorem norm_smul_self_eq_iff (hτ : Differentiable ℝ τ) (hd : ∀ x, 0 < τ x + fderiv ℝ τ x x)
    {r : ℝ} (hr : ∀ x : F, ‖x‖ = r → τ x = 1) (x : F) : ‖τ x • x‖ = r ↔ ‖x‖ = r := by
  rw [eq_iff_le_not_lt, eq_iff_le_not_lt, norm_smul_self_le_iff hτ hd hr,
    norm_smul_self_lt_iff hτ hd hr]

section radialSmulDiffeomorph

variable [FiniteDimensional ℝ F] {n : WithTop ℕ∞} (hn : 1 ≤ n) (hτ : ContDiff ℝ n τ)
  (hd : ∀ x, 0 < τ x + fderiv ℝ τ x x) {R : ℝ} (hR : ∀ x, R ≤ ‖x‖ → τ x = 1) {r : ℝ}
  (hr : ∀ x : F, ‖x‖ = r → τ x = 1)
include hr

/-- If `τ = 1` on the sphere of radius `r`, the preimage of `ball 0 r` under
`radialSmulDiffeomorph` is `ball 0 r`. -/
theorem preimage_radialSmulDiffeomorph_ball :
    radialSmulDiffeomorph hn hτ hd hR ⁻¹' ball 0 r = ball 0 r := by
  ext x
  simp [norm_smul_self_lt_iff (hτ.differentiable (by positivity)) hd hr]

/-- If `τ = 1` on the sphere of radius `r`, the preimage of `closedBall 0 r` under
`radialSmulDiffeomorph` is `closedBall 0 r`. -/
theorem preimage_radialSmulDiffeomorph_closedBall :
    radialSmulDiffeomorph hn hτ hd hR ⁻¹' closedBall 0 r = closedBall 0 r := by
  ext x
  simp [norm_smul_self_le_iff (hτ.differentiable (by positivity)) hd hr]

/-- If `τ = 1` on the sphere of radius `r`, the preimage of `sphere 0 r` under
`radialSmulDiffeomorph` is `sphere 0 r`. -/
theorem preimage_radialSmulDiffeomorph_sphere :
    radialSmulDiffeomorph hn hτ hd hR ⁻¹' sphere 0 r = sphere 0 r := by
  ext x
  simp [norm_smul_self_eq_iff (hτ.differentiable (by positivity)) hd hr]

/-- If `τ = 1` on the sphere of radius `r`, `radialSmulDiffeomorph` maps `ball 0 r` onto
itself. -/
theorem image_radialSmulDiffeomorph_ball :
    radialSmulDiffeomorph hn hτ hd hR '' ball 0 r = ball 0 r := by
  conv_lhs => rw [← preimage_radialSmulDiffeomorph_ball hn hτ hd hR hr]
  exact (radialSmulDiffeomorph hn hτ hd hR).toEquiv.surjective.image_preimage _

/-- If `τ = 1` on the sphere of radius `r`, `radialSmulDiffeomorph` maps `closedBall 0 r` onto
itself. -/
theorem image_radialSmulDiffeomorph_closedBall :
    radialSmulDiffeomorph hn hτ hd hR '' closedBall 0 r = closedBall 0 r := by
  conv_lhs => rw [← preimage_radialSmulDiffeomorph_closedBall hn hτ hd hR hr]
  exact (radialSmulDiffeomorph hn hτ hd hR).toEquiv.surjective.image_preimage _

/-- If `τ = 1` on the sphere of radius `r`, `radialSmulDiffeomorph` maps `sphere 0 r` onto
itself. -/
theorem image_radialSmulDiffeomorph_sphere :
    radialSmulDiffeomorph hn hτ hd hR '' sphere 0 r = sphere 0 r := by
  conv_lhs => rw [← preimage_radialSmulDiffeomorph_sphere hn hτ hd hR hr]
  exact (radialSmulDiffeomorph hn hτ hd hR).toEquiv.surjective.image_preimage _

end radialSmulDiffeomorph

end SymplecticGeometry

end
