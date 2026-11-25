/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Geometry.Manifold.Algebra.SMul
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Fibrewise scalings of a product

For normed spaces `E` and `F` and a function `ρ : E → ℝ`, `SymplecticGeometry.prodFiberScaling ρ`
is the map `(u, v) ↦ (u, ρ u • v)` of `E × F`, which rescales each fibre `{u} × F` by `ρ u`. When
`ρ` is `C^n` and vanishes nowhere it is a `C^n` diffeomorphism
(`SymplecticGeometry.prodFiberScalingDiffeomorph`), whose inverse rescales by `(ρ u)⁻¹`. When
`|ρ| ≤ 1` it maps every closed ball around `0` of `E × F` (with the sup norm of the product) into
itself.

## Main results

* `SymplecticGeometry.prodFiberScaling`: the map `(u, v) ↦ (u, ρ u • v)`.
* `SymplecticGeometry.contMDiff_prodFiberScaling_family`: fibre scalings by `ψ (p, ·)`, for a
  smooth `ψ` on the product with a parameter manifold, are smooth jointly in `p` and the point.
* `SymplecticGeometry.prodFiberScalingDiffeomorph`: the fibre scaling as a diffeomorphism, when
  `ρ` vanishes nowhere.
* `SymplecticGeometry.mapsTo_prodFiberScaling_closedBall`: it maps closed balls around `0` into
  themselves when `|ρ| ≤ 1`.
-/

public section

open Set Metric
open scoped Manifold

namespace SymplecticGeometry

section FiberScaling

variable {E F : Type*} [AddCommGroup F] [Module ℝ F]

/-- The map `(u, v) ↦ (u, ρ u • v)` of `E × F`, which rescales the fibre `{u} × F` by `ρ u`. -/
def prodFiberScaling (ρ : E → ℝ) (x : E × F) : E × F :=
  (x.1, ρ x.1 • x.2)

variable {ρ σ : E → ℝ}

theorem prodFiberScaling_def (ρ : E → ℝ) (x : E × F) :
    prodFiberScaling ρ x = (x.1, ρ x.1 • x.2) :=
  (rfl)

@[simp]
theorem prodFiberScaling_fst (ρ : E → ℝ) (x : E × F) : (prodFiberScaling ρ x).1 = x.1 := by
  rw [prodFiberScaling_def]

@[simp]
theorem prodFiberScaling_snd (ρ : E → ℝ) (x : E × F) :
    (prodFiberScaling ρ x).2 = ρ x.1 • x.2 := by
  rw [prodFiberScaling_def]

@[simp]
theorem prodFiberScaling_mk (ρ : E → ℝ) (u : E) (v : F) :
    prodFiberScaling ρ (u, v) = (u, ρ u • v) :=
  prodFiberScaling_def ρ (u, v)

/-- The fibre scaling fixes the points of the fibres on which `ρ` is `1`. -/
theorem prodFiberScaling_of_eq_one {x : E × F} (h : ρ x.1 = 1) : prodFiberScaling ρ x = x := by
  rw [prodFiberScaling_def, h, one_smul]

/-- Scaling by `σ` and then by `ρ` is scaling by `ρ * σ`. -/
theorem prodFiberScaling_prodFiberScaling (x : E × F) :
    prodFiberScaling ρ (prodFiberScaling σ x) = prodFiberScaling (ρ * σ) x := by
  simp [prodFiberScaling_def, mul_smul]

/-- For `ρ` nowhere zero, the fibre scaling by `ρ` is inverse to the one by `u ↦ (ρ u)⁻¹`. -/
theorem prodFiberScaling_inv_prodFiberScaling (hρ : ∀ u, ρ u ≠ 0) (x : E × F) :
    prodFiberScaling (fun u ↦ (ρ u)⁻¹) (prodFiberScaling ρ x) = x := by
  simp [prodFiberScaling_def, inv_smul_smul₀ (hρ x.1)]

/-- For `ρ` nowhere zero, the fibre scaling by `u ↦ (ρ u)⁻¹` is inverse to the one by `ρ`. -/
theorem prodFiberScaling_prodFiberScaling_inv (hρ : ∀ u, ρ u ≠ 0) (x : E × F) :
    prodFiberScaling ρ (prodFiberScaling (fun u ↦ (ρ u)⁻¹) x) = x := by
  simp [prodFiberScaling_def, smul_inv_smul₀ (hρ x.1)]

end FiberScaling

section NormedFiberScaling

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {ρ : E → ℝ} {n : WithTop ℕ∞}

/-- The fibre scaling is `C^n` when `ρ` is. -/
theorem contDiff_prodFiberScaling (hρ : ContDiff ℝ n ρ) :
    ContDiff ℝ n (prodFiberScaling (F := F) ρ) :=
  contDiff_fst.prodMk ((hρ.comp contDiff_fst).smul contDiff_snd)

/-- A smooth family of fibre scalings, by `ψ (p, ·)` for a smooth `ψ : N × E → ℝ` on the product
with a parameter manifold `N`, is smooth jointly in the parameter and the point. -/
theorem contMDiff_prodFiberScaling_family {EN HN N : Type*} [NormedAddCommGroup EN]
    [NormedSpace ℝ EN] [TopologicalSpace HN] {J : ModelWithCorners ℝ EN HN} [TopologicalSpace N]
    [ChartedSpace HN N] {ψ : N × E → ℝ}
    (hψ : ContMDiff (J.prod 𝓘(ℝ, E)) 𝓘(ℝ) n ψ) :
    ContMDiff (J.prod 𝓘(ℝ, E × F)) 𝓘(ℝ, E × F) n
      fun p : N × (E × F) ↦ prodFiberScaling (fun u ↦ ψ (p.1, u)) p.2 :=
  (contDiff_fst.contMDiff.comp contMDiff_snd).prodMk_space
    (ContMDiff.smul (hψ.comp (contMDiff_fst.prodMk (contDiff_fst.contMDiff.comp contMDiff_snd)))
      (contDiff_snd.contMDiff.comp contMDiff_snd))

/-- For a `C^n` function `ρ` that vanishes nowhere, the fibre scaling `(u, v) ↦ (u, ρ u • v)` as a
`C^n` diffeomorphism of `E × F`, with inverse `(u, v) ↦ (u, (ρ u)⁻¹ • v)`. -/
noncomputable def prodFiberScalingDiffeomorph (hρ : ContDiff ℝ n ρ) (h₀ : ∀ u, ρ u ≠ 0) :
    (E × F) ≃ₘ^n⟮𝓘(ℝ, E × F), 𝓘(ℝ, E × F)⟯ (E × F) where
  toFun := prodFiberScaling ρ
  invFun := prodFiberScaling fun u ↦ (ρ u)⁻¹
  left_inv := prodFiberScaling_inv_prodFiberScaling h₀
  right_inv := prodFiberScaling_prodFiberScaling_inv h₀
  contMDiff_toFun := (contDiff_prodFiberScaling hρ).contMDiff
  contMDiff_invFun := (contDiff_prodFiberScaling (hρ.inv h₀)).contMDiff

@[simp]
theorem coe_prodFiberScalingDiffeomorph (hρ : ContDiff ℝ n ρ) (h₀ : ∀ u, ρ u ≠ 0) :
    ⇑(prodFiberScalingDiffeomorph (F := F) hρ h₀) = prodFiberScaling ρ :=
  (rfl)

@[simp]
theorem coe_prodFiberScalingDiffeomorph_symm (hρ : ContDiff ℝ n ρ) (h₀ : ∀ u, ρ u ≠ 0) :
    ⇑(prodFiberScalingDiffeomorph (F := F) hρ h₀).symm = prodFiberScaling fun u ↦ (ρ u)⁻¹ :=
  (rfl)

/-- For a `C^n` function `ρ` that vanishes nowhere, the fibre scaling is a `C^n` local
diffeomorphism. -/
theorem isLocalDiffeomorph_prodFiberScaling (hρ : ContDiff ℝ n ρ) (h₀ : ∀ u, ρ u ≠ 0) :
    IsLocalDiffeomorph 𝓘(ℝ, E × F) 𝓘(ℝ, E × F) n (prodFiberScaling (F := F) ρ) := by
  rw [← coe_prodFiberScalingDiffeomorph hρ h₀]
  exact (prodFiberScalingDiffeomorph hρ h₀).isLocalDiffeomorph

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The norm of the fibre component of a fibre scaling. -/
theorem norm_prodFiberScaling_snd (ρ : E → ℝ) (x : E × F) :
    ‖(prodFiberScaling ρ x).2‖ = |ρ x.1| * ‖x.2‖ := by
  rw [prodFiberScaling_snd, norm_smul, Real.norm_eq_abs]

omit [NormedSpace ℝ E] in
/-- Where `|ρ| ≤ 1`, the fibre scaling does not increase the sup norm of `E × F`. -/
theorem norm_prodFiberScaling_le {x : E × F} (h : |ρ x.1| ≤ 1) :
    ‖prodFiberScaling ρ x‖ ≤ ‖x‖ := by
  rw [Prod.norm_def, Prod.norm_def, prodFiberScaling_fst, norm_prodFiberScaling_snd]
  exact max_le_max le_rfl (mul_le_of_le_one_left (norm_nonneg _) h)

omit [NormedSpace ℝ E] in
/-- When `|ρ| ≤ 1`, the fibre scaling maps every closed ball around `0` into itself. -/
theorem mapsTo_prodFiberScaling_closedBall (h : ∀ u, |ρ u| ≤ 1) (r : ℝ) :
    MapsTo (prodFiberScaling ρ) (closedBall (0 : E × F) r) (closedBall 0 r) := fun x hx ↦ by
  rw [mem_closedBall_zero_iff] at hx ⊢
  exact (norm_prodFiberScaling_le (h x.1)).trans hx

end NormedFiberScaling

end SymplecticGeometry

end
