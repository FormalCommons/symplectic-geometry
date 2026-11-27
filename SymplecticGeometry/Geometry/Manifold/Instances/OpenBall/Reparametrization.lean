/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.Instances.OpenBall.Diffeomorph

/-!
# Balls and boxes as images of whole vector spaces

Two reparametrizations of a whole real vector space onto a bounded open set, by smooth embeddings
that send `0` to `0`:

* `SymplecticGeometry.exists_isSmoothEmbedding_range_eq_ball_of_isCompact`: if `V` and `F` are
  finite-dimensional of the same dimension, `F` with an inner product, and `K` is a compact subset
  of the open unit ball of `F`, there is a smooth embedding `ψ : V → F` onto that ball such that
  `K` lies in the image of the open unit ball of `V`. It is Tau Ceti's
  `TauCeti.unitBallDiffeomorph`, read through a linear isomorphism `V ≃ F` scaled so that the
  preimage of `K` lies in the unit ball of `V`. For `V = Fin m → ℝ` with the sup norm, the unit
  ball of `V` is the open cube, so the sup-norm sphere of `V` is sent off `K`.
* `SymplecticGeometry.exists_isSmoothEmbedding_range_eq_ball_pi`: for `δ > 0`, a smooth
  embedding of `ι → ℝ` onto its sup-norm ball of radius `δ`, the box `(-δ, δ)ᶥ`. It acts on each
  coordinate by `t ↦ δ t / √(1 + t²)` (Mathlib's `OpenPartialHomeomorph.univUnitBall` on `ℝ`).
* `SymplecticGeometry.exists_isSmoothEmbedding_prod_range_eq_ball_prod_ball`: the product of
  the two, a smooth embedding of `V × (ι → ℝ)` onto (open unit ball of `F`) × (box).

These give the coordinates on `(Fin m → ℝ) × (Fin k → ℝ)` in which the cube of a critical point
of a Morse function is read off its unstable disc.
-/

public section

open Manifold Metric OpenPartialHomeomorph Set
open scoped ContDiff

namespace SymplecticGeometry

section Ball

variable {V F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- **A compact subset of the unit ball as part of the image of a unit ball.** If `V` and the
inner product space `F` are finite-dimensional of the same dimension and `K` is a compact subset of
the open unit ball of `F`, there is a smooth embedding `ψ : V → F` with `ψ 0 = 0` whose range is
the open unit ball of `F`, such that `K` lies in the image under `ψ` of the open unit ball of
`V`. -/
theorem exists_isSmoothEmbedding_range_eq_ball_of_isCompact
    (hVF : Module.finrank ℝ V = Module.finrank ℝ F) {K : Set F} (hK : IsCompact K)
    (hKb : K ⊆ ball 0 1) :
    ∃ ψ : V → F, IsSmoothEmbedding 𝓘(ℝ, V) 𝓘(ℝ, F) ∞ ψ ∧ range ψ = ball 0 1 ∧ ψ 0 = 0 ∧
      K ⊆ ψ '' ball 0 1 := by
  let e : V ≃L[ℝ] F := ContinuousLinearEquiv.ofFinrankEq hVF
  -- The points of `V` that `e` and `univUnitBall` send to `K` form a compact set.
  have hL : IsCompact (e.symm '' (univUnitBall.symm '' K)) :=
    (hK.image_of_continuousOn (univUnitBall.continuousOn_symm.mono
      (by rwa [univUnitBall_target]))).image e.symm.continuous
  obtain ⟨R, hR, hLR⟩ := hL.isBounded.subset_ball_lt 0 0
  let s : V ≃L[ℝ] V := ContinuousLinearEquiv.smulLeft (Units.mk0 R hR.ne')
  have hs (x : V) : s x = R • x := by simp [s, Units.smul_def]
  have hg (y : F) : ((TauCeti.unitBallDiffeomorph F).symm y : F) = univUnitBall y :=
    TauCeti.coe_unitBallDiffeomorph_symm_apply y
  refine ⟨((Subtype.val ∘ (TauCeti.unitBallDiffeomorph F).symm) ∘ e) ∘ s, ?_, ?_,
    by simp [hs, hg], ?_⟩
  · exact TauCeti.isSmoothEmbedding_comp_continuousLinearEquiv s
      (TauCeti.isSmoothEmbedding_comp_continuousLinearEquiv e
        (TauCeti.isSmoothEmbedding_comp_diffeomorph _ (IsSmoothEmbedding.of_opens _)))
  · rw [EquivLike.range_comp, EquivLike.range_comp, EquivLike.range_comp, Subtype.range_coe,
      TauCeti.coe_unitBallOpens]
  · intro k hk
    have hy : e.symm (univUnitBall.symm k) ∈ ball 0 R := hLR ⟨_, mem_image_of_mem _ hk, rfl⟩
    refine ⟨R⁻¹ • e.symm (univUnitBall.symm k), ?_, ?_⟩
    · rw [mem_ball_zero_iff] at hy ⊢
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hR.le), inv_mul_lt_one₀ hR]
      exact hy
    · simp only [Function.comp_apply, hs, hg, smul_inv_smul₀ hR.ne', e.apply_symm_apply]
      exact univUnitBall.right_inv (by rw [univUnitBall_target]; exact hKb hk)

end Ball

section Box

variable {ι : Type*} [Fintype ι]

/-- The box `(-δ, δ)ᶥ`, the sup-norm ball of radius `δ` in `ι → ℝ`, as an open set. -/
private def boxOpens (δ : ℝ) : TopologicalSpace.Opens (ι → ℝ) :=
  ⟨ball 0 δ, isOpen_ball⟩

private theorem coe_boxOpens (δ : ℝ) : (boxOpens (ι := ι) δ : Set (ι → ℝ)) = ball 0 δ := rfl

private theorem mem_boxOpens {δ : ℝ} (hδ : 0 < δ) {y : ι → ℝ} :
    y ∈ boxOpens δ ↔ ∀ i, δ⁻¹ * y i ∈ ball (0 : ℝ) 1 := by
  rw [← SetLike.mem_coe, coe_boxOpens]
  simp only [mem_ball_zero_iff, Real.norm_eq_abs, pi_norm_lt_iff hδ, abs_mul,
    abs_of_pos (inv_pos.2 hδ), inv_mul_lt_one₀ hδ]

/-- The diffeomorphism of `ι → ℝ` onto the box `(-δ, δ)ᶥ` acting on each coordinate by
`t ↦ δ t / √(1 + t²)`. -/
private noncomputable def boxDiffeomorph {δ : ℝ} (hδ : 0 < δ) :
    (ι → ℝ) ≃ₘ^∞⟮𝓘(ℝ, ι → ℝ), 𝓘(ℝ, ι → ℝ)⟯ boxOpens (ι := ι) δ where
  toFun x := ⟨fun i ↦ δ * univUnitBall (x i), (mem_boxOpens hδ).2 fun i ↦ by
    rw [inv_mul_cancel_left₀ hδ.ne', ← univUnitBall_target]
    exact univUnitBall.map_source (mem_univ _)⟩
  invFun y := fun i ↦ univUnitBall.symm (δ⁻¹ * (y : ι → ℝ) i)
  left_inv x := funext fun i ↦ by
    simp only [inv_mul_cancel_left₀ hδ.ne']
    exact univUnitBall.left_inv (mem_univ _)
  right_inv y := Subtype.ext <| funext fun i ↦ by
    -- `y` is read through the components of `toFun` and `invFun` given above.
    change δ * univUnitBall (univUnitBall.symm (δ⁻¹ * (y : ι → ℝ) i)) = (y : ι → ℝ) i
    rw [univUnitBall.right_inv
        (by rw [univUnitBall_target]; exact (mem_boxOpens hδ).1 y.property i),
      mul_inv_cancel_left₀ hδ.ne']
  contMDiff_toFun := by
    refine (TauCeti.ContMDiff.subtypeVal_comp_iff (boxOpens δ) _).1 ?_
    refine ContDiff.contMDiff (contDiff_pi.2 fun i ↦ ?_)
    exact contDiff_const.mul (contDiff_univUnitBall.comp (contDiff_apply ℝ (fun _ : ι ↦ ℝ) i))
  contMDiff_invFun := by
    have h : ContDiffOn ℝ ∞ (fun y : ι → ℝ ↦ fun i ↦ univUnitBall.symm (δ⁻¹ * y i))
        (boxOpens (ι := ι) δ) := contDiffOn_pi.2 fun i ↦ contDiffOn_univUnitBall_symm.comp
      (contDiff_const.mul (contDiff_apply ℝ (fun _ : ι ↦ ℝ) i)).contDiffOn
      fun y hy ↦ (mem_boxOpens hδ).1 (SetLike.mem_coe.1 hy) i
    exact h.contMDiffOn.comp_contMDiff contMDiff_subtypeVal fun y ↦ y.property

private theorem coe_boxDiffeomorph_apply {δ : ℝ} (hδ : 0 < δ) (x : ι → ℝ) :
    (boxDiffeomorph hδ x : ι → ℝ) = fun i ↦ δ * univUnitBall (x i) := rfl

/-- **A box as the image of a whole vector space.** For `δ > 0` there is a smooth embedding
`ψ : (ι → ℝ) → (ι → ℝ)` with `ψ 0 = 0` whose range is the sup-norm ball of radius `δ`, that is,
the box `(-δ, δ)ᶥ`. -/
theorem exists_isSmoothEmbedding_range_eq_ball_pi {δ : ℝ} (hδ : 0 < δ) :
    ∃ ψ : (ι → ℝ) → (ι → ℝ), IsSmoothEmbedding 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) ∞ ψ ∧
      range ψ = ball 0 δ ∧ ψ 0 = 0 := by
  refine ⟨Subtype.val ∘ boxDiffeomorph (ι := ι) hδ,
    TauCeti.isSmoothEmbedding_comp_diffeomorph _ (IsSmoothEmbedding.of_opens _), ?_, ?_⟩
  · rw [EquivLike.range_comp, Subtype.range_coe, coe_boxOpens]
  · simp [coe_boxDiffeomorph_apply, Pi.zero_def]

end Box

/-- **A ball times a box as the image of a whole vector space.** If `V` and the inner product
space `F` are finite-dimensional of the same dimension, `K` is a compact subset of the open unit
ball of `F` and `δ > 0`, there is a smooth embedding `ψ : V × (ι → ℝ) → F × (ι → ℝ)` with
`ψ 0 = 0` onto the product of the open unit ball of `F` and the sup-norm ball of radius `δ`,
which sends `V × {0}` into `F × {0}`, and such that `K ×ˢ {0}` lies in the image of
`ball 0 1 ×ˢ {0}`. -/
theorem exists_isSmoothEmbedding_prod_range_eq_ball_prod_ball {V F ι : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [Fintype ι]
    (hVF : Module.finrank ℝ V = Module.finrank ℝ F) {K : Set F} (hK : IsCompact K)
    (hKb : K ⊆ ball 0 1) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ψ : V × (ι → ℝ) → F × (ι → ℝ),
      IsSmoothEmbedding 𝓘(ℝ, V × (ι → ℝ)) 𝓘(ℝ, F × (ι → ℝ)) ∞ ψ ∧
      range ψ = ball 0 1 ×ˢ ball 0 δ ∧ ψ 0 = 0 ∧
      (∀ x, (ψ (x, 0)).2 = 0) ∧ K ×ˢ {0} ⊆ ψ '' (ball 0 1 ×ˢ {0}) := by
  obtain ⟨ψ₁, h₁, hr₁, h0₁, hK₁⟩ := exists_isSmoothEmbedding_range_eq_ball_of_isCompact hVF hK hKb
  obtain ⟨ψ₂, h₂, hr₂, h0₂⟩ := exists_isSmoothEmbedding_range_eq_ball_pi (ι := ι) hδ
  refine ⟨Prod.map ψ₁ ψ₂, ?_, by rw [range_prodMap, hr₁, hr₂], Prod.ext h0₁ h0₂,
    fun x ↦ by simp [h0₂], ?_⟩
  · rw [modelWithCornersSelf_prod, modelWithCornersSelf_prod, ← chartedSpaceSelf_prod,
      ← chartedSpaceSelf_prod]
    exact h₁.prodMap h₂
  · rintro ⟨k, _⟩ ⟨hk, rfl⟩
    obtain ⟨x, hx, rfl⟩ := hK₁ hk
    exact ⟨(x, 0), ⟨hx, rfl⟩, by simp [h0₂]⟩

end SymplecticGeometry

end
