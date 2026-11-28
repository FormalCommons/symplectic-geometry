/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import TauCeti.Analysis.Calculus.SecondOrderExpansion

/-!
# Inequalities between vanishing derivatives at second and fourth order

Let `D : E → F →L[ℝ] ℝ` (typically the derivative of a function, read on a space `F`) and
`Y : E → F` (typically a vector field) both vanish at `x₀` and be differentiable there, with
derivatives `B` and `A`. Both sides of an inequality `K * (‖Y u‖ ^ 2 + (D u e) ^ 2) ≤ D u (Y u)`,
for `u` near `x₀`, vanish to second order at `x₀`; dividing by `s ^ 2` along `u = x₀ + s • v`
and letting `s → 0` gives `K * (‖A v‖ ^ 2 + (B v e) ^ 2) ≤ B v (A v)`
(`HasFDerivAt.mul_norm_sq_add_sq_apply_le_apply_apply_of_eventually`). Both this and the fourth
order below pass to the limit along a rescaled curve in the same way
(`Filter.Tendsto.mul_norm_sq_add_sq_apply_le_apply_of_tendsto_smul`).

If moreover `D` and `Y` are `C³` at `x₀` and a vector `e₀` lies in the kernels of `B` and `A`, both
sides vanish to fourth order along the parabola `u = x₀ + s • e₀ + s ^ 2 • w`: there
`D u / s ^ 2` and `Y u / s ^ 2` tend to `α = B w + D²D(x₀) e₀ e₀ / 2` and
`β = A w + D²Y(x₀) e₀ e₀ / 2` (`ContDiffAt.tendsto_inv_sq_smul_add_smul_add_sq_smul`, from
Tau Ceti's Taylor expansion `ContDiffAt.isBigO_sub_taylor_two`), so
`K * (‖β‖ ^ 2 + (α e) ^ 2) ≤ α β`
(`ContDiffAt.mul_norm_sq_add_sq_le_of_eventually_of_fderiv_apply_eq_zero`).

This is the step by which a gradient-like inequality at a critical point passes to the
linearizations of the function and of the field there. The proof differentiates along the
lines `s ↦ x₀ + s • v` and passes to the limit in the slopes, as Tau Ceti's
`HasFDerivAt.norm_apply_le_mul_norm_apply` does for an inequality between norms.
-/

public section

open Asymptotics Filter
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- **An inequality passes to rescaled limits.** Let `γ` tend to `x₀` along a nontrivial
filter `l`, and let `r t • D (γ t)` and `r t • Y (γ t)` tend to `α` and `β` along `l`. If
`K * (‖Y u‖ ^ 2 + D u e ^ 2) ≤ D u (Y u)` for every `u` near `x₀`, then
`K * (‖β‖ ^ 2 + α e ^ 2) ≤ α β`. -/
theorem Filter.Tendsto.mul_norm_sq_add_sq_apply_le_apply_of_tendsto_smul {ι P : Type*}
    [TopologicalSpace P] {l : Filter ι} [l.NeBot] {γ : ι → P} {x₀ : P} (hγ : Tendsto γ l (𝓝 x₀))
    {r : ι → ℝ} {D : P → F →L[ℝ] ℝ} {Y : P → F} {α : F →L[ℝ] ℝ} {β : F}
    (hD : Tendsto (fun t ↦ r t • D (γ t)) l (𝓝 α)) (hY : Tendsto (fun t ↦ r t • Y (γ t)) l (𝓝 β))
    {K : ℝ} {e : F} (h : ∀ᶠ u in 𝓝 x₀, K * (‖Y u‖ ^ 2 + D u e ^ 2) ≤ D u (Y u)) :
    K * (‖β‖ ^ 2 + α e ^ 2) ≤ α β := by
  have hlim₁ := ((hY.norm.pow 2).add
    ((((ContinuousLinearMap.apply ℝ ℝ e).continuous.tendsto _).comp hD).pow 2)).const_mul K
  have hlim₂ := (isBoundedBilinearMap_apply.continuous.tendsto _).comp (hD.prodMk_nhds hY)
  refine le_of_tendsto_of_tendsto hlim₁ hlim₂ ?_
  filter_upwards [hγ.eventually h] with t ht
  simp only [Function.comp_apply, ContinuousLinearMap.apply_apply, smul_apply, smul_eq_mul,
    map_smul, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  nlinarith [mul_le_mul_of_nonneg_left ht (sq_nonneg (r t))]

/-- **An inequality between vanishing derivatives, at second order.** Let `D : E → F →L[ℝ] ℝ` and
`Y : E → F` vanish at `x₀`, with derivatives `B` and `A` there. If
`K * (‖Y u‖ ^ 2 + D u e ^ 2) ≤ D u (Y u)` for every `u` near `x₀`, then
`K * (‖A v‖ ^ 2 + B v e ^ 2) ≤ B v (A v)` for every `v`. -/
theorem HasFDerivAt.mul_norm_sq_add_sq_apply_le_apply_apply_of_eventually {D : E → F →L[ℝ] ℝ}
    {Y : E → F} {x₀ : E} {B : E →L[ℝ] F →L[ℝ] ℝ} {A : E →L[ℝ] F} (hD : HasFDerivAt D B x₀)
    (hD₀ : D x₀ = 0) (hY : HasFDerivAt Y A x₀) (hY₀ : Y x₀ = 0) {K : ℝ} {e : F}
    (h : ∀ᶠ u in 𝓝 x₀, K * (‖Y u‖ ^ 2 + D u e ^ 2) ≤ D u (Y u)) (v : E) :
    K * (‖A v‖ ^ 2 + B v e ^ 2) ≤ B v (A v) := by
  have hℓ : HasDerivAt (fun s : ℝ ↦ x₀ + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x₀
  have hℓ₀ : x₀ + (0 : ℝ) • v = x₀ := by simp
  -- The slopes `s⁻¹ • D (x₀ + s • v)` and `s⁻¹ • Y (x₀ + s • v)` tend to `B v` and `A v`.
  have hDℓ := (hD.comp_hasDerivAt_of_eq 0 hℓ hℓ₀.symm).tendsto_slope_zero
  have hYℓ := (hY.comp_hasDerivAt_of_eq 0 hℓ hℓ₀.symm).tendsto_slope_zero
  simp only [Function.comp_apply, zero_add, hℓ₀, hD₀, hY₀, sub_zero] at hDℓ hYℓ
  have hℓt : Tendsto (fun s : ℝ ↦ x₀ + s • v) (𝓝[≠] 0) (𝓝 x₀) := by
    have := hℓ.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
    rwa [hℓ₀] at this
  exact hℓt.mul_norm_sq_add_sq_apply_le_apply_of_tendsto_smul hDℓ hYℓ h


/-! ### Fourth order, along a kernel direction -/

/-- **The quadratic rate along a parabola tangent to a kernel direction.** Let `G` be `C³` at `x`,
vanish there, and let `DG(x) e = 0`. Then along `t ↦ x + t • e + t ^ 2 • w`,
`G (x + t • e + t ^ 2 • w) / t ^ 2` tends to `DG(x) w + D²G(x) e e / 2` as `t → 0`. -/
theorem ContDiffAt.tendsto_inv_sq_smul_add_smul_add_sq_smul {G : E → F} {x e : E}
    (hG : ContDiffAt ℝ 3 G x) (hG₀ : G x = 0) (he : fderiv ℝ G x e = 0) (w : E) :
    Tendsto (fun t : ℝ ↦ (t ^ 2)⁻¹ • G (x + t • e + t ^ 2 • w)) (𝓝[≠] 0)
      (𝓝 (fderiv ℝ G x w + (2⁻¹ : ℝ) • fderiv ℝ (fderiv ℝ G) x e e)) := by
  set L := fderiv ℝ G x
  set Q := fderiv ℝ (fderiv ℝ G) x
  set R : E → F := fun x' ↦ G x' - G x - L (x' - x) - (2⁻¹ : ℝ) • Q (x' - x) (x' - x)
  have hR : R =O[𝓝 x] fun x' ↦ ‖x' - x‖ ^ 3 := hG.isBigO_sub_taylor_two
  set z : ℝ → E := fun t ↦ e + t • w
  have hz : Continuous z := by fun_prop
  have hγ : Tendsto (fun t : ℝ ↦ x + t • e + t ^ 2 • w) (𝓝 0) (𝓝 x) := by
    have : Continuous fun t : ℝ ↦ x + t • e + t ^ 2 • w := by fun_prop
    simpa using this.tendsto 0
  have hγx (t : ℝ) : x + t • e + t ^ 2 • w - x = t • z t := by
    simp only [z, smul_add, smul_smul]; abel_nf; simp [sq]
  -- The remainder is `O(t ^ 3)`, hence `o(t ^ 2)`.
  have hRt : (fun t : ℝ ↦ R (x + t • e + t ^ 2 • w)) =o[𝓝 0] fun t ↦ t ^ 2 := by
    have h₁ := hR.comp_tendsto hγ
    have h₂ : (fun t : ℝ ↦ ‖x + t • e + t ^ 2 • w - x‖ ^ 3) =O[𝓝 0] fun t ↦ ‖t‖ ^ 3 := by
      have hb : (fun t ↦ ‖z t‖ ^ 3) =O[𝓝 0] fun _ ↦ (1 : ℝ) :=
        ((hz.norm.pow 3).continuousAt (x := 0)).isBigO_one ℝ
      refine (IsBigO.mul (isBigO_refl (fun t : ℝ ↦ ‖t‖ ^ 3) _) hb).congr' ?_ (by simp)
      filter_upwards with t
      simp [hγx, norm_smul, mul_pow]
    refine (h₁.trans h₂).trans_isLittleO ?_
    simpa [norm_pow] using (isLittleO_pow_pow (𝕜 := ℝ) (by norm_num : 2 < 3)).norm_left
  have hmain : ∀ t : ℝ, t ≠ 0 → (t ^ 2)⁻¹ • G (x + t • e + t ^ 2 • w) =
      L w + (2⁻¹ : ℝ) • Q (z t) (z t) + (t ^ 2)⁻¹ • R (x + t • e + t ^ 2 • w) := by
    intro t ht
    have hL : L (t • z t) = t ^ 2 • L w := by
      simp [z, he, smul_smul, sq]
    simp only [R, hγx, hG₀, sub_zero, hL, map_smul, smul_apply, smul_sub,
      smul_smul]
    field_simp
    module
  have hlim : Tendsto (fun t : ℝ ↦ L w + (2⁻¹ : ℝ) • Q (z t) (z t) +
      (t ^ 2)⁻¹ • R (x + t • e + t ^ 2 • w)) (𝓝[≠] 0)
      (𝓝 (L w + (2⁻¹ : ℝ) • Q e e + 0)) := by
    refine Tendsto.add (Tendsto.const_add _ (Tendsto.const_smul ?_ _))
      ((hRt.mono nhdsWithin_le_nhds).tendsto_inv_smul_nhds_zero)
    have : Continuous fun t ↦ Q (z t) (z t) := by fun_prop
    simpa [z] using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  rw [add_zero] at hlim
  exact hlim.congr' (eventually_nhdsWithin_of_forall fun t ht ↦ (hmain t ht).symm)


/-- **An inequality between vanishing derivatives, at fourth order.** Let `D : E → F →L[ℝ] ℝ` and
`Y : E → F` be `C³` at `x₀` and vanish there, and let `e` lie in the kernels of their derivatives
there. If `K * (‖Y u‖ ^ 2 + D u e' ^ 2) ≤ D u (Y u)` for every `u` near `x₀`, then for every `w`,
with `α = DD(x₀) w + D²D(x₀) e e / 2` and `β = DY(x₀) w + D²Y(x₀) e e / 2`,
`K * (‖β‖ ^ 2 + α e' ^ 2) ≤ α β`. -/
theorem ContDiffAt.mul_norm_sq_add_sq_le_of_eventually_of_fderiv_apply_eq_zero
    {D : E → F →L[ℝ] ℝ} {Y : E → F} {x₀ e : E} (hD : ContDiffAt ℝ 3 D x₀) (hD₀ : D x₀ = 0)
    (hDe : fderiv ℝ D x₀ e = 0) (hY : ContDiffAt ℝ 3 Y x₀) (hY₀ : Y x₀ = 0)
    (hYe : fderiv ℝ Y x₀ e = 0) {K : ℝ} {e' : F}
    (h : ∀ᶠ u in 𝓝 x₀, K * (‖Y u‖ ^ 2 + D u e' ^ 2) ≤ D u (Y u)) (w : E) :
    K * (‖fderiv ℝ Y x₀ w + (2⁻¹ : ℝ) • fderiv ℝ (fderiv ℝ Y) x₀ e e‖ ^ 2 +
      (fderiv ℝ D x₀ w + (2⁻¹ : ℝ) • fderiv ℝ (fderiv ℝ D) x₀ e e) e' ^ 2) ≤
      (fderiv ℝ D x₀ w + (2⁻¹ : ℝ) • fderiv ℝ (fderiv ℝ D) x₀ e e)
        (fderiv ℝ Y x₀ w + (2⁻¹ : ℝ) • fderiv ℝ (fderiv ℝ Y) x₀ e e) := by
  have hγ : Tendsto (fun t : ℝ ↦ x₀ + t • e + t ^ 2 • w) (𝓝[≠] 0) (𝓝 x₀) := by
    have : Continuous fun t : ℝ ↦ x₀ + t • e + t ^ 2 • w := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  exact hγ.mul_norm_sq_add_sq_apply_le_apply_of_tendsto_smul
    (hD.tendsto_inv_sq_smul_add_smul_add_sq_smul hD₀ hDe w)
    (hY.tendsto_inv_sq_smul_add_smul_add_sq_smul hY₀ hYe w) h

end
