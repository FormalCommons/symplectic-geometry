/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Compressing a cube onto a thin tube around a one-dimensional core

For normed spaces `E` and `F` and a function `ρ : E → ℝ`, `SymplecticGeometry.prodFiberScaling ρ`
is the map `(u, v) ↦ (u, ρ u • v)` of `E × F`, which rescales each fibre `{u} × F` by `ρ u`. When
`ρ` is smooth and vanishes nowhere it is a diffeomorphism
(`SymplecticGeometry.prodFiberScalingDiffeomorph`), whose inverse rescales by `(ρ u)⁻¹`. When
`|ρ| ≤ 1` it maps every closed ball of `E × F` (with the sup norm of the product) into itself.

On `D = (Fin 1 → ℝ) × F`, with the cube `Q = closedBall 0 1` and the attaching faces
`A = sphere 0 1 ×ˢ closedBall 0 1`, `SymplecticGeometry.exists_cubeCompression` gives, for
`0 < ε < 1` and `0 < δ`, a smooth `ψ : ℝ × (Fin 1 → ℝ) → ℝ` with positive values at most `1`
such that the maps `c s = prodFiberScaling (ψ (s, ·))` are the identity at `s = 0` and near `A`
(where `1 - ε / 2 < ‖u‖`) for every `s`, preserve `Q`, and such that `c 1` maps `Q` into the
union of the thin tube `‖v‖ < δ` around the core `closedBall 0 1 ×ˢ {0}` and the slab
`1 - ε < ‖u‖` next to `A`. Since the sup norm of `u` is `|u 0|`, which is not smooth at `0`, `ψ`
depends on `u` through `u 0 ^ 2`.

## Forms

The handle-core lemma of McDuff–Salamon pulls two-forms back along the maps `c s`. Each `c s` is
a diffeomorphism, so the pullback of a two-form is nondegenerate at `x` exactly when the form is
nondegenerate at `c s x`, by
`TauCeti.SmoothTwoForm.nondegenerate_bilinFormAt_iff_of_isInvertible_mfderiv` and
`IsLocalDiffeomorph.isInvertible_mfderiv`. A smooth family of forms pulled back along
`(p, x) ↦ c (a p) x`, for a smooth function `a` of the parameter, is a smooth family by
`SymplecticGeometry.IsSmoothFamily.mpullback_family`, since `(s, x) ↦ c s x` is smooth
(`SymplecticGeometry.contMDiff_prodFiberScaling_family`). A form that is exact near `Q` pulls back
to a form exact near `Q`, by `TauCeti.SmoothForm.exists_mem_nhdsSet_mextDerivₗ_mpullback_eq`,
since `c s` maps `Q` into `Q`.

This compression replaces the zig-zag immersion of McDuff–Salamon's proof of Lemma 7.3.2: instead
of stretching the core so that primitives near its ends can be patched with a small error, the
cube is squeezed towards the core, where a single primitive along the fibres is close to the
given form.

## Main results

* `SymplecticGeometry.prodFiberScaling`: the map `(u, v) ↦ (u, ρ u • v)`.
* `SymplecticGeometry.prodFiberScalingDiffeomorph`: it is a diffeomorphism when `ρ` is smooth and
  vanishes nowhere.
* `SymplecticGeometry.mapsTo_prodFiberScaling_closedBall`: it preserves closed balls when
  `|ρ| ≤ 1`.
* `SymplecticGeometry.exists_cubeCompression`: the compression of the cube.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Lemma 7.3.2.
-/

public section

open Set Metric
open scoped Manifold ContDiff

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
  [NormedSpace ℝ F] {ρ : E → ℝ}

/-- The fibre scaling is smooth when `ρ` is. -/
theorem contDiff_prodFiberScaling {n : WithTop ℕ∞} (hρ : ContDiff ℝ n ρ) :
    ContDiff ℝ n (prodFiberScaling (F := F) ρ) :=
  contDiff_fst.prodMk ((hρ.comp contDiff_fst).smul contDiff_snd)

/-- A smooth family of fibre scalings, by `ψ (p, ·)` for a smooth `ψ : N × E → ℝ` on the product
with a parameter manifold `N`, is smooth jointly in the parameter and the point. -/
theorem contMDiff_prodFiberScaling_family {EN HN N : Type*} [NormedAddCommGroup EN]
    [NormedSpace ℝ EN] [TopologicalSpace HN] {J : ModelWithCorners ℝ EN HN} [TopologicalSpace N]
    [ChartedSpace HN N] {n : WithTop ℕ∞} {ψ : N × E → ℝ}
    (hψ : ContMDiff (J.prod 𝓘(ℝ, E)) 𝓘(ℝ) n ψ) :
    ContMDiff (J.prod 𝓘(ℝ, E × F)) 𝓘(ℝ, E × F) n
      fun p : N × (E × F) ↦ prodFiberScaling (fun u ↦ ψ (p.1, u)) p.2 :=
  (contDiff_fst.contMDiff.comp contMDiff_snd).prodMk_space
    (ContMDiff.smul (hψ.comp (contMDiff_fst.prodMk (contDiff_fst.contMDiff.comp contMDiff_snd)))
      (contDiff_snd.contMDiff.comp contMDiff_snd))

/-- For a smooth `ρ` that vanishes nowhere, the fibre scaling `(u, v) ↦ (u, ρ u • v)` as a
diffeomorphism of `E × F`, with inverse `(u, v) ↦ (u, (ρ u)⁻¹ • v)`. -/
noncomputable def prodFiberScalingDiffeomorph (hρ : ContDiff ℝ ∞ ρ) (h₀ : ∀ u, ρ u ≠ 0) :
    (E × F) ≃ₘ^∞⟮𝓘(ℝ, E × F), 𝓘(ℝ, E × F)⟯ (E × F) where
  toFun := prodFiberScaling ρ
  invFun := prodFiberScaling fun u ↦ (ρ u)⁻¹
  left_inv := prodFiberScaling_inv_prodFiberScaling h₀
  right_inv := prodFiberScaling_prodFiberScaling_inv h₀
  contMDiff_toFun := (contDiff_prodFiberScaling hρ).contMDiff
  contMDiff_invFun := (contDiff_prodFiberScaling (hρ.inv h₀)).contMDiff

@[simp]
theorem coe_prodFiberScalingDiffeomorph (hρ : ContDiff ℝ ∞ ρ) (h₀ : ∀ u, ρ u ≠ 0) :
    ⇑(prodFiberScalingDiffeomorph (F := F) hρ h₀) = prodFiberScaling ρ :=
  (rfl)

@[simp]
theorem coe_prodFiberScalingDiffeomorph_symm (hρ : ContDiff ℝ ∞ ρ) (h₀ : ∀ u, ρ u ≠ 0) :
    ⇑(prodFiberScalingDiffeomorph (F := F) hρ h₀).symm = prodFiberScaling fun u ↦ (ρ u)⁻¹ :=
  (rfl)

/-- For a smooth `ρ` that vanishes nowhere, the fibre scaling is a local diffeomorphism. -/
theorem isLocalDiffeomorph_prodFiberScaling (hρ : ContDiff ℝ ∞ ρ) (h₀ : ∀ u, ρ u ≠ 0) :
    IsLocalDiffeomorph 𝓘(ℝ, E × F) 𝓘(ℝ, E × F) ∞ (prodFiberScaling (F := F) ρ) := by
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

section Cube

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The sup norm of `u : Fin 1 → ℝ` is `|u 0|`. -/
private theorem norm_fin_one (u : Fin 1 → ℝ) : ‖u‖ = |u 0| := by
  simp [Pi.norm_def, Real.norm_eq_abs]

/-- The profile of the compression: a smooth `ψ` with values in `(0, 1]`,
equal to `1` at time `0` and where `1 - ε / 2 < ‖u‖`, and below `δ` at time `1` where
`‖u‖ ≤ 1 - ε`. -/
private theorem exists_cubeCompression_profile {ε δ : ℝ} (hε : 0 < ε) (hε₁ : ε < 1)
    (hδ : 0 < δ) :
    ∃ ψ : ℝ × (Fin 1 → ℝ) → ℝ, ContDiff ℝ ∞ ψ ∧ (∀ p, 0 < ψ p) ∧ (∀ p, ψ p ≤ 1) ∧
      (∀ u, ψ (0, u) = 1) ∧ (∀ s u, 1 - ε / 2 < ‖u‖ → ψ (s, u) = 1) ∧
      ∀ u, ‖u‖ ≤ 1 - ε → ψ (1, u) < δ := by
  set a := min (δ / 2) (1 / 2)
  have ha₀ : 0 < a := lt_min (half_pos hδ) one_half_pos
  have haδ : a < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  have ha₁ : a ≤ 1 / 2 := min_le_right _ _
  set b := 1 - ε / 2
  set c := 1 - ε
  have hc : 0 < c := by simp only [c]; linarith
  have hcb : c < b := by simp only [c, b]; linarith
  have hd : 0 < b ^ 2 - c ^ 2 := by nlinarith
  -- `χ u` is `1` where `‖u‖ ≤ c` and `0` where `b < ‖u‖`.
  let χ : (Fin 1 → ℝ) → ℝ := fun u ↦ Real.smoothTransition ((b ^ 2 - u 0 ^ 2) / (b ^ 2 - c ^ 2))
  let ψ : ℝ × (Fin 1 → ℝ) → ℝ := fun p ↦ 1 - Real.smoothTransition p.1 * χ p.2 * (1 - a)
  have hχ : ContDiff ℝ ∞ χ :=
    Real.smoothTransition.contDiff.comp
      ((contDiff_const.sub ((contDiff_pi.mp contDiff_id 0).pow 2)).div_const _)
  have hθχ (p : ℝ × (Fin 1 → ℝ)) :
      0 ≤ Real.smoothTransition p.1 * χ p.2 ∧ Real.smoothTransition p.1 * χ p.2 ≤ 1 :=
    ⟨mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _),
      (mul_le_of_le_one_left (Real.smoothTransition.nonneg _)
        (Real.smoothTransition.le_one _)).trans (Real.smoothTransition.le_one _)⟩
  refine ⟨ψ, contDiff_const.sub (((Real.smoothTransition.contDiff.comp contDiff_fst).mul
      (hχ.comp contDiff_snd)).mul contDiff_const), fun p ↦ ?_, fun p ↦ ?_, fun u ↦ ?_,
      fun s u hu ↦ ?_, fun u hu ↦ ?_⟩
  · obtain ⟨_, h₁⟩ := hθχ p
    simp only [ψ]
    nlinarith
  · obtain ⟨h₀, _⟩ := hθχ p
    simp only [ψ]
    nlinarith
  · simp [ψ, Real.smoothTransition.zero]
  · have hu' : b ^ 2 < u 0 ^ 2 := by
      rw [norm_fin_one] at hu
      rw [← sq_abs (u 0)]
      exact pow_lt_pow_left₀ hu (hc.le.trans hcb.le) two_ne_zero
    have : χ u = 0 := Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le)
    simp [ψ, this]
  · have hu' : u 0 ^ 2 ≤ c ^ 2 := by
      rw [norm_fin_one] at hu
      rw [← sq_abs (u 0)]
      exact pow_le_pow_left₀ (abs_nonneg _) hu 2
    have : χ u = 1 := Real.smoothTransition.one_of_one_le
      ((one_le_div hd).2 (by linarith))
    simp only [ψ, this, Real.smoothTransition.one_of_one_le le_rfl]
    linarith

/-- **Compression of the cube onto a thin tube around a one-dimensional core.** On
`D = (Fin 1 → ℝ) × F` with the sup norm, let `0 < ε < 1` and `0 < δ`. There is a smooth
`ψ : ℝ × (Fin 1 → ℝ) → ℝ` with values in `(0, 1]` whose fibre scalings
`c s = prodFiberScaling (ψ (s, ·))`, `(u, v) ↦ (u, ψ (s, u) • v)`, which are
diffeomorphisms of `D` by `prodFiberScalingDiffeomorph`, such that

* `c 0` is the identity, and every `c s` is the identity where `1 - ε / 2 < ‖u‖`, a neighbourhood
  of the attaching faces `sphere 0 1 ×ˢ closedBall 0 1`;
* every `c s` maps the cube `closedBall 0 1` into itself;
* `c 1` maps the cube into the union of the tube `‖v‖ < δ` and the slab `1 - ε < ‖u‖`. -/
theorem exists_cubeCompression {ε δ : ℝ} (hε : 0 < ε) (hε₁ : ε < 1) (hδ : 0 < δ) :
    ∃ ψ : ℝ × (Fin 1 → ℝ) → ℝ, ContDiff ℝ ∞ ψ ∧ (∀ p, 0 < ψ p ∧ ψ p ≤ 1) ∧
      (∀ x : (Fin 1 → ℝ) × F, prodFiberScaling (fun u ↦ ψ (0, u)) x = x) ∧
      (∀ s, ∀ x : (Fin 1 → ℝ) × F, 1 - ε / 2 < ‖x.1‖ →
        prodFiberScaling (fun u ↦ ψ (s, u)) x = x) ∧
      (∀ s, MapsTo (prodFiberScaling (fun u ↦ ψ (s, u)))
        (closedBall (0 : (Fin 1 → ℝ) × F) 1) (closedBall 0 1)) ∧
      MapsTo (prodFiberScaling (fun u ↦ ψ (1, u))) (closedBall (0 : (Fin 1 → ℝ) × F) 1)
        ({x | ‖x.2‖ < δ} ∪ {x | 1 - ε < ‖x.1‖}) := by
  obtain ⟨ψ, hψ, hpos, hle, h0, hA, h1⟩ := exists_cubeCompression_profile hε hε₁ hδ
  have habs (p) : |ψ p| ≤ 1 := by rw [abs_of_pos (hpos p)]; exact hle p
  refine ⟨ψ, hψ, fun p ↦ ⟨hpos p, hle p⟩, fun x ↦ prodFiberScaling_of_eq_one (h0 x.1),
    fun s x hx ↦ prodFiberScaling_of_eq_one (hA s x.1 hx),
    fun s ↦ mapsTo_prodFiberScaling_closedBall (fun u ↦ habs (s, u)) 1, fun x hx ↦ ?_⟩
  rw [mem_closedBall_zero_iff] at hx
  rcases lt_or_ge (1 - ε) ‖x.1‖ with hu | hu
  · exact Or.inr (by simpa using hu)
  · left
    rw [mem_ofPred_eq, norm_prodFiberScaling_snd, abs_of_pos (hpos _)]
    calc ψ (1, x.1) * ‖x.2‖ ≤ ψ (1, x.1) * 1 :=
          mul_le_mul_of_nonneg_left ((norm_snd_le x).trans hx) (hpos _).le
      _ < δ := by simpa using h1 x.1 hu

end Cube

end SymplecticGeometry

end
