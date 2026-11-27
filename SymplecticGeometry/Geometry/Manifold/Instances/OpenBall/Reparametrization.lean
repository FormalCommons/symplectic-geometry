/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Analysis.InnerProductSpace.Calculus
import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.PartialDiffeomorph
import SymplecticGeometry.Logic.Equiv.PartialEquiv
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
  embedding of `ι → ℝ` onto its sup-norm ball of radius `δ`, the box `(-δ, δ)ᶥ`. It is Mathlib's
  `OpenPartialHomeomorph.univBall 0 δ` of `ℝ` on each coordinate (`OpenPartialHomeomorph.pi`),
  which is a smooth embedding onto its target, as its source is everything
  (`OpenPartialHomeomorph.isSmoothEmbedding_of_source_eq_univ` and
  `PartialEquiv.range_eq_target_of_source_eq_univ`).
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

/-- **A box as the image of a whole vector space.** For `δ > 0` there is a smooth embedding
`ψ : (ι → ℝ) → (ι → ℝ)` with `ψ 0 = 0` whose range is the sup-norm ball of radius `δ`, that is,
the box `(-δ, δ)ᶥ`. -/
theorem exists_isSmoothEmbedding_range_eq_ball_pi {δ : ℝ} (hδ : 0 < δ) :
    ∃ ψ : (ι → ℝ) → (ι → ℝ), IsSmoothEmbedding 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) ∞ ψ ∧
      range ψ = ball 0 δ ∧ ψ 0 = 0 := by
  -- Mathlib's `univBall 0 δ` of `ℝ`, on each coordinate.
  let Θ : OpenPartialHomeomorph (ι → ℝ) (ι → ℝ) := .pi fun _ ↦ univBall (0 : ℝ) δ
  have hsource : Θ.source = univ := by simp [Θ, univBall_source]
  have htarget : Θ.target = ball 0 δ := by simp [Θ, univBall_target _ hδ, ball_pi _ hδ]
  refine ⟨Θ, Θ.isSmoothEmbedding_of_source_eq_univ hsource
      (contDiff_pi.2 fun i ↦ contDiff_univBall.comp (contDiff_apply ℝ (fun _ : ι ↦ ℝ) i))
      (htarget ▸ contDiffOn_pi.2 fun i ↦ contDiffOn_univBall_symm.comp
        (contDiff_apply ℝ (fun _ : ι ↦ ℝ) i).contDiffOn fun y hy ↦
          mem_ball_zero_iff.2 ((norm_le_pi_norm y i).trans_lt (mem_ball_zero_iff.1 hy))),
    by rw [← coe_toPartialEquiv, Θ.toPartialEquiv.range_eq_target_of_source_eq_univ hsource,
      htarget], ?_⟩
  ext i
  simp [Θ, univBall_apply_zero]

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
