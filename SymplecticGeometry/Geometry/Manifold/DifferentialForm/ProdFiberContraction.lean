/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.HomotopyOperator
public import TauCeti.Analysis.Calculus.DifferentialForm.Relative.Basic
public import Mathlib.Geometry.Manifold.VectorField.Pullback
import SymplecticGeometry.Geometry.Manifold.Instances.Icc
import TauCeti.Topology.UnitInterval

/-!
# The fibrewise contraction of a product onto its first factor

For real normed spaces `E` and `F`, the map `Φ ((u, v), s) = (u, s • v)` on `(E × F) × [0, 1]`
(`SymplecticGeometry.prodFiberContraction`) is a smooth homotopy from the projection
`g (u, v) = (u, 0)` onto the core `E × {0}` to the identity. Its derivative at `((u, v), s)`
sends `(w, r ∂ₜ)` to `(w₁, s w₂ + r v)` (`SymplecticGeometry.mfderiv_prodFiberContraction`).
The map is Tau Ceti's flat fibre scaling `TauCeti.fiberScaling` on `(E × F) × ℝ`, restricted
to times in `[0, 1]`, and its smoothness and derivative come from `TauCeti.contDiff_fiberScaling`
and `TauCeti.fderiv_fiberScaling_apply` by the chain rule.

Let `h` be the homotopy operator `TauCeti.SmoothForm.homotopyOperator`, and `τ` a smooth
`(k + 1)`-form on `E × F`. The cochain-homotopy identity
`d (h (Φ^* τ)) + h (Φ^* (d τ)) = τ - g^* τ` holds for every form, closed or not. When
`dim E ≤ k`, the map `g` factors through `E`, which carries no nonzero `(k + 1)`-forms, so
`g^* τ = 0` and `d (h (Φ^* τ)) = τ - h (Φ^* (d τ))`. For a one-dimensional `E` this holds for
two-forms: the core being one-dimensional is used only here.

The error term is controlled along the fibre segments: the time derivative of `Φ` at `((u, v), s)`
is `(0, v)`, and its spatial derivative has operator norm at most `1` for the sup norm of
`E × F`. So, by `TauCeti.norm_homotopyOperator_mpullback_apply_le`, `h (Φ^* σ)` has norm at most
`‖v‖ C` at `(u, v)` when `σ` has norm at most `C` at every point `(u, s • v)`, `s ∈ [0, 1]`; in
particular it vanishes there when `σ` vanishes along that segment.

Since `Φ` is smooth, `ω ↦ h (Φ^* ω)` takes smooth families of forms to smooth families
(`SymplecticGeometry.preservesSmoothFamilies_homotopyOperator_mpullback`, or
`SymplecticGeometry.IsSmoothFamily.homotopyOperator` after
`SymplecticGeometry.IsSmoothFamily.mpullback`).

This file carries Tau Ceti's flat relative Poincaré construction
(`TauCeti/Analysis/Calculus/DifferentialForm/Relative/Basic.lean`) over to the manifold homotopy
operator `TauCeti.SmoothForm.homotopyOperator` on the cylinder `(E × F) × [0, 1]`. The bound
`norm_mfderiv_prodFiberContraction_comp_inl_le` and the bound on `h (Φ^* σ)` adapt the steps of
`TauCeti.norm_fiberwisePoincareHomotopy_le`, and the identity for `d (h (Φ^* τ))` follows the
plan of `TauCeti.mextDeriv_vectorBundlePoincareHomotopy_add_vectorBundlePoincareHomotopy_mextDeriv`.

## Main definitions

* `SymplecticGeometry.prodFiberContraction`: the map `((u, v), s) ↦ (u, s • v)`.

## Main results

* `SymplecticGeometry.contMDiff_prodFiberContraction`: it is smooth, up to the ends of `[0, 1]`.
* `SymplecticGeometry.mextDerivₗ_homotopyOperator_mpullback_prodFiberContraction`: for
  `dim E ≤ k` and a smooth `(k + 1)`-form `τ` with values in a Banach space,
  `d (h (Φ^* τ)) = τ - h (Φ^* (d τ))`.
* `SymplecticGeometry.norm_homotopyOperator_mpullback_prodFiberContraction_apply_le`: the bound
  `‖h (Φ^* σ) (u, v)‖ ≤ ‖v‖ C` when `‖σ (u, s • v)‖ ≤ C` for all `s ∈ [0, 1]`.
* `SymplecticGeometry.homotopyOperator_mpullback_prodFiberContraction_apply_eq_zero`:
  `h (Φ^* σ)` vanishes at `(u, v)` when `σ` vanishes at every `(u, s • v)`, `s ∈ [0, 1]`.

## References

* [R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §4 (the
  homotopy operator).
* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Lemma 7.3.2 (the result whose one-dimensional case this file serves).
-/

public section

noncomputable section

open Set TauCeti
open scoped Manifold ContDiff

namespace SymplecticGeometry

variable {E F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

variable (E F) in
/-- The **fibrewise contraction** of `E × F` onto `E × {0}`: the map
`((u, v), s) ↦ (u, s • v)` on `(E × F) × [0, 1]`, the identity at `s = 1` and the projection
`(u, v) ↦ (u, 0)` at `s = 0`. It is the flat fibre scaling `TauCeti.fiberScaling` with the
time restricted to `[0, 1]`. -/
def prodFiberContraction (x : (E × F) × unitInterval) : E × F :=
  fiberScaling (x.1, (x.2 : ℝ))

theorem prodFiberContraction_def (x : (E × F) × unitInterval) :
    prodFiberContraction E F x = fiberScaling (x.1, (x.2 : ℝ)) :=
  (rfl)

variable (E F) in
/-- The fibrewise contraction is the flat fibre scaling after the inclusion of `[0, 1]` into
`ℝ`. -/
theorem prodFiberContraction_eq_comp :
    prodFiberContraction E F =
      fiberScaling ∘ Prod.map (id : E × F → E × F) (Subtype.val : unitInterval → ℝ) :=
  funext prodFiberContraction_def

/-- The fibrewise contraction sends `((u, v), s)` to `(u, s • v)`. -/
theorem prodFiberContraction_apply (x : (E × F) × unitInterval) :
    prodFiberContraction E F x = (x.1.1, (x.2 : ℝ) • x.1.2) := by
  rw [prodFiberContraction_def, fiberScaling_apply]

/-- The fibrewise contraction does not move the point of `E`. -/
@[simp]
theorem prodFiberContraction_fst (x : (E × F) × unitInterval) :
    (prodFiberContraction E F x).1 = x.1.1 := by
  rw [prodFiberContraction_apply]

/-- The fibrewise contraction scales the point of `F`. -/
@[simp]
theorem prodFiberContraction_snd (x : (E × F) × unitInterval) :
    (prodFiberContraction E F x).2 = (x.2 : ℝ) • x.1.2 := by
  rw [prodFiberContraction_apply]

/-- At time `1` the fibrewise contraction is the identity. -/
@[simp]
theorem prodFiberContraction_one (p : E × F) : prodFiberContraction E F (p, 1) = p := by
  simp [prodFiberContraction_apply]

/-- At time `0` the fibrewise contraction is the projection onto `E × {0}`. -/
@[simp]
theorem prodFiberContraction_zero (p : E × F) :
    prodFiberContraction E F (p, 0) = (p.1, 0) := by
  simp [prodFiberContraction_apply]

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]

variable (E F) in
/-- The fibrewise contraction is smooth, up to the ends of the unit interval. -/
theorem contMDiff_prodFiberContraction :
    ContMDiff (𝓘(ℝ, E × F).prod (𝓡∂ 1)) 𝓘(ℝ, E × F) ∞ (prodFiberContraction E F) := by
  rw [prodFiberContraction_eq_comp]
  exact contDiff_fiberScaling.contMDiff.comp contMDiff_prodMap_id_subtypeVal_Icc

/-- **The derivative of the fibrewise contraction.** At `((u, v), s)`, it sends `(w, r • 1)`,
where `1` is the unit tangent vector of the interval, to `(w₁, s • w₂ + r • v)`. -/
theorem mfderiv_prodFiberContraction (x : (E × F) × unitInterval) (w : E × F) (r : ℝ) :
    mfderiv (𝓘(ℝ, E × F).prod (𝓡∂ 1)) 𝓘(ℝ, E × F) (prodFiberContraction E F) x
        (w, r • (1 : TangentSpace (𝓡∂ 1) x.2)) =
      (w.1, (x.2 : ℝ) • w.2 + r • x.1.2) := by
  have hs : MDifferentiableAt 𝓘(ℝ, (E × F) × ℝ) 𝓘(ℝ, E × F) fiberScaling (x.1, (x.2 : ℝ)) :=
    ((contDiff_fiberScaling (r := 1)).differentiable one_ne_zero).differentiableAt
      |>.mdifferentiableAt
  rw [prodFiberContraction_eq_comp]
  refine (mfderiv_comp_apply x hs
    ((contMDiff_prodMap_id_subtypeVal_Icc (n := 1)).mdifferentiable one_ne_zero x) _).trans ?_
  have h := mfderiv_prodMap_id_subtypeVal_Icc (I := 𝓘(ℝ, E × F)) x w r
  -- The model `𝓘(ℝ, E × F).prod 𝓘(ℝ, ℝ)` and its charted space are those of `(E × F) × ℝ`.
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at h
  rw [h, mfderiv_eq_fderiv]
  -- The identifications `NormedSpace.fromTangentSpace` around `fderiv` are the identity.
  exact fderiv_fiberScaling_apply _ _

/-- The time derivative of the fibrewise contraction at `((u, v), s)` is `(0, v)`. -/
theorem mfderiv_prodFiberContraction_time (x : (E × F) × unitInterval) :
    mfderiv (𝓘(ℝ, E × F).prod (𝓡∂ 1)) 𝓘(ℝ, E × F) (prodFiberContraction E F) x
        ((0 : E × F), (1 : TangentSpace (𝓡∂ 1) x.2)) = (0, x.1.2) := by
  have h := mfderiv_prodFiberContraction x 0 1
  rw [one_smul] at h
  rw [h, Prod.fst_zero, Prod.snd_zero, smul_zero, zero_add, one_smul]

/-- The spatial derivative of the fibrewise contraction at `((u, v), s)`, the restriction of its
derivative to `E × F`, is `(w₁, w₂) ↦ (w₁, s • w₂)`. -/
theorem mfderiv_prodFiberContraction_comp_inl (x : (E × F) × unitInterval) :
    (mfderiv (𝓘(ℝ, E × F).prod (𝓡∂ 1)) 𝓘(ℝ, E × F) (prodFiberContraction E F) x).comp
        (.inl ℝ (E × F) (EuclideanSpace ℝ (Fin 1))) =
      (ContinuousLinearMap.fst ℝ E F).prod ((x.2 : ℝ) • ContinuousLinearMap.snd ℝ E F) := by
  refine ContinuousLinearMap.ext fun w ↦ ?_
  have h := mfderiv_prodFiberContraction x w 0
  rw [zero_smul, zero_smul, add_zero] at h
  -- The two sides are `h` read through `comp_apply`, `inl_apply` and `prod_apply`. The tangent
  -- space of the cylinder is `(E × F) × ℝ¹` only by unfolding, so `rw` cannot apply these.
  exact h

/-- The spatial derivative of the fibrewise contraction has operator norm at most `1`, for the
sup norm of `E × F`. -/
theorem norm_mfderiv_prodFiberContraction_comp_inl_le (x : (E × F) × unitInterval) :
    @norm (E × F →L[ℝ] E × F) _
      ((mfderiv (𝓘(ℝ, E × F).prod (𝓡∂ 1)) 𝓘(ℝ, E × F) (prodFiberContraction E F) x).comp
        (.inl ℝ (E × F) (EuclideanSpace ℝ (Fin 1)))) ≤ 1 := by
  rw [mfderiv_prodFiberContraction_comp_inl]
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w ↦ ?_
  rw [ContinuousLinearMap.prod_apply, smul_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', one_mul, Prod.norm_def, Prod.norm_def, norm_smul]
  exact max_le_max le_rfl
    (mul_le_of_le_one_left (norm_nonneg _) (unitInterval.abs_coe_le_one x.2))

/-- **The fibrewise contraction pulls back to a primitive up to an error term.** Let `E` have
dimension at most `k`, and `τ` be a smooth `(k + 1)`-form on `E × F` with values in a Banach
space, closed or not. Then `d (h (Φ^* τ)) = τ - h (Φ^* (d τ))`, where `Φ` is the fibrewise
contraction and `h` the homotopy operator. -/
theorem mextDerivₗ_homotopyOperator_mpullback_prodFiberContraction [FiniteDimensional ℝ E]
    [CompleteSpace G] {k : ℕ} (hE : Module.finrank ℝ E ≤ k)
    (τ : SmoothForm 𝓘(ℝ, E × F) (E × F) G (k + 1)) :
    mextDerivₗ 𝓘(ℝ, E × F) k (SmoothForm.homotopyOperator
        (SmoothForm.mpullback _ (contMDiff_prodFiberContraction E F) τ)) =
      τ - SmoothForm.homotopyOperator (SmoothForm.mpullback _
        (contMDiff_prodFiberContraction E F) (mextDerivₗ 𝓘(ℝ, E × F) (k + 1) τ)) := by
  -- The projection onto the core factors through `E`.
  have hfst : ContMDiff 𝓘(ℝ, E × F) 𝓘(ℝ, E) ∞ (Prod.fst : E × F → E) := contDiff_fst.contMDiff
  have hinl : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E × F) ∞ (fun u : E ↦ ((u, 0) : E × F)) :=
    (contDiff_id.prodMk contDiff_const).contMDiff
  have hg := hinl.comp hfst
  have hg₀ : SmoothForm.mpullback _ hg τ = 0 := by
    rw [← SmoothForm.mpullback_mpullback _ _ hfst hinl,
      SmoothForm.eq_zero_of_finrank_lt (Nat.lt_succ_of_le hE) (SmoothForm.mpullback _ hinl τ),
      map_zero]
  have key :=
    SmoothForm.mextDerivₗ_homotopyOperator_mpullback_add_homotopyOperator_mpullback_mextDerivₗ
    hg (contMDiff_prodFiberContraction E F) (fun p ↦ prodFiberContraction_zero p)
    (fun p ↦ prodFiberContraction_one p) τ
  rwa [hg₀, sub_zero, ← eq_sub_iff_add_eq] at key

/-- **A bound for the homotopy operator along the fibre segments.** Let `σ` be a
`(k + 1)`-form on `E × F` and `p = (u, v)`. If `σ` has norm at most `C` at every point
`(u, s • v)`, `s ∈ [0, 1]`, then `h (Φ^* σ)` has operator norm at most `‖v‖ * C` at `p`, where
`Φ` is the fibrewise contraction and `h` the homotopy operator. -/
theorem norm_homotopyOperator_mpullback_prodFiberContraction_apply_le {k : ℕ}
    (σ : RoughForm 𝓘(ℝ, E × F) (E × F) G (k + 1)) (p : E × F) {C : ℝ}
    (h : ∀ s : unitInterval,
      @norm ((E × F) [⋀^Fin (k + 1)]→L[ℝ] G) _ (σ (p.1, (s : ℝ) • p.2)) ≤ C) :
    @norm ((E × F) [⋀^Fin k]→L[ℝ] G) _ (homotopyOperator
      (mpullback (𝓘(ℝ, E × F).prod (𝓡∂ 1)) 𝓘(ℝ, E × F) (prodFiberContraction E F) σ) p) ≤
      ‖p.2‖ * C := by
  have hC : 0 ≤ C := (norm_nonneg _).trans (h 0)
  refine norm_homotopyOperator_mpullback_apply_le _ σ p fun t ↦ ?_
  rw [mfderiv_prodFiberContraction_time, prodFiberContraction_apply]
  have hv : @norm (E × F) _ (0, p.2) = ‖p.2‖ := by simp [Prod.norm_def]
  rw [hv]
  calc _ ≤ C * ‖p.2‖ * 1 ^ k :=
        mul_le_mul (mul_le_mul_of_nonneg_right (h t) (norm_nonneg _))
          (pow_le_pow_left₀ (norm_nonneg _) (norm_mfderiv_prodFiberContraction_comp_inl_le _) k)
          (pow_nonneg (norm_nonneg _) k) (by positivity)
    _ = ‖p.2‖ * C := by ring

/-- **The homotopy operator vanishes where the form vanishes along the fibre segment.** Let `σ`
be a `(k + 1)`-form on `E × F` and `p = (u, v)`. If `σ` vanishes at every point `(u, s • v)`,
`s ∈ [0, 1]`, then `h (Φ^* σ)` vanishes at `p`, where `Φ` is the fibrewise contraction and `h`
the homotopy operator. -/
theorem homotopyOperator_mpullback_prodFiberContraction_apply_eq_zero {k : ℕ}
    {σ : RoughForm 𝓘(ℝ, E × F) (E × F) G (k + 1)} {p : E × F}
    (h : ∀ s : unitInterval, σ (p.1, (s : ℝ) • p.2) = 0) :
    homotopyOperator
      (mpullback (𝓘(ℝ, E × F).prod (𝓡∂ 1)) 𝓘(ℝ, E × F) (prodFiberContraction E F) σ) p = 0 :=
  homotopyOperator_mpullback_apply_eq_zero_of_forall fun s ↦ by
    rw [prodFiberContraction_apply]
    exact h s

end SymplecticGeometry

end
