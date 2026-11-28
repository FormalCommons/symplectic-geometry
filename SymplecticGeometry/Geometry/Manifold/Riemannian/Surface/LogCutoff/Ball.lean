/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Support
import TauCeti.Geometry.Manifold.Riemannian.Surface.LogCutoff.Profile
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import SymplecticGeometry.Geometry.Manifold.Riemannian.Surface.LogCutoff.Comp
import SymplecticGeometry.Geometry.Manifold.Riemannian.Surface.LogCutoff.Interpolation

/-!
# Cut-offs near a point with `‖z‖ ‖Dβ(z)‖` small

In a finite-dimensional real normed space `E`, for every `r > 0` and `η > 0` this file builds a
smooth `β : E → [0, 1]`, equal to `1` near `0`, with topological support in `ball 0 r`, and with
`‖z‖ ‖Dβ(z)‖ ≤ η` everywhere. A cut-off whose differential is of order `1 / r` cannot do this
for small `η`; the logarithmic profile can.

The cut-off is `β = 1 - ψ ∘ ρ`, with `ρ z = ‖toEuclidean z‖²` and `ψ` Tau Ceti's logarithmic
profile `TauCeti.logCutoffProfile ε δ`, with `δ` of order `r²` and `Λ = log (δ / ε)` large. The
bound on `‖z‖ ‖Dβ(z)‖`, of order `1 / Λ`, comes from
`TauCeti.sqrt_mul_norm_fderiv_logCutoffProfile_comp_le`.

Such cut-offs are used to cut off a perturbation near a critical point in the proof of
Proposition 9.23 of [CieliebakEliashberg2012], as in their Lemma 12.9.

## Main results

* `SymplecticGeometry.exists_contDiff_tsupport_subset_ball_norm_mul_norm_fderiv_le`: the
  cut-off `β` above.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012]
-/

public section

open Set Metric Filter Topology TauCeti
open scoped ContDiff

namespace SymplecticGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- In a finite-dimensional real normed space, for every `r > 0` and `η > 0` there is a smooth
`β : E → ℝ` with values in `[0, 1]`, equal to `1` near `0`, with topological support in
`ball 0 r`, and with `‖z‖ ‖Dβ(z)‖ ≤ η` for every `z`. -/
theorem exists_contDiff_tsupport_subset_ball_norm_mul_norm_fderiv_le {r η : ℝ} (hr : 0 < r)
    (hη : 0 < η) :
    ∃ β : E → ℝ, ContDiff ℝ ∞ β ∧ (∀ z, β z ∈ Icc (0 : ℝ) 1) ∧ (∀ᶠ z in 𝓝 0, β z = 1) ∧
      tsupport β ⊆ ball 0 r ∧ ∀ z, ‖z‖ * ‖fderiv ℝ β z‖ ≤ η := by
  -- The squared Euclidean norm `ρ` and its comparison with the norm of `E`.
  set T := toEuclidean (E := E)
  set ρ : E → ℝ := fun z ↦ ‖T z‖ ^ 2
  set a₁ := ‖(T.symm : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →L[ℝ] E)‖
  set a₂ := ‖(T : E →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))‖
  have hz (z : E) : ‖z‖ ≤ a₁ * ‖T z‖ := by
    simpa using (T.symm : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →L[ℝ] E).le_opNorm (T z)
  have hsqrt (z : E) : √(ρ z) = ‖T z‖ := Real.sqrt_sq (norm_nonneg _)
  have hρd (z : E) : HasFDerivAt ρ (2 • (innerSL ℝ (T z)).comp
      (T : E →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) z :=
    (T : E →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E))).hasFDerivAt.norm_sq
  have hρD (z : E) : ‖fderiv ℝ ρ z‖ ≤ (2 * a₂) * √(ρ z) := by
    rw [(hρd z).fderiv, hsqrt]
    refine (norm_nsmul_le).trans ?_
    push_cast
    calc 2 * ‖(innerSL ℝ (T z)).comp
          (T : E →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))‖
        ≤ 2 * (‖innerSL ℝ (T z)‖ * a₂) := by gcongr; exact ContinuousLinearMap.opNorm_comp_le _ _
      _ = 2 * a₂ * ‖T z‖ := by rw [innerSL_apply_norm]; ring
  have hρc : ContDiff ℝ ∞ ρ := (contDiff_norm_sq ℝ).comp T.contDiff
  -- The parameters: `δ` of order `r ^ 2` and `log (δ / ε) = L` large.
  set κ := a₁ * (logCutoffConst * (2 * a₂))
  have hκ : 0 ≤ κ := by have := logCutoffConst_pos; positivity
  set L := 3 + κ / η
  have hL : 3 ≤ L := le_add_of_nonneg_right (by positivity)
  set δ := (r / (a₁ + 1)) ^ 2
  have hδ : 0 < δ := by positivity
  set ε := δ / Real.exp L
  have hε : 0 < ε := by positivity
  have hΛ : Real.log (δ / ε) = L := by
    rw [show δ / ε = Real.exp L by simp only [ε]; field_simp, Real.log_exp]
  have h4 : 4 * ε ≤ δ := by
    have : 4 ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
    simp only [ε]
    rw [mul_div_assoc', div_le_iff₀ (Real.exp_pos L)]
    nlinarith
  have h2 : 2 * ε ≤ δ := by linarith
  set β : E → ℝ := fun z ↦ 1 - logCutoffProfile ε δ (ρ z)
  refine ⟨β, contDiff_const.sub ((contDiff_logCutoffProfile hδ.ne').comp hρc), fun z ↦ ?_, ?_,
    ?_, fun z ↦ ?_⟩
  · simpa [β] using mul_one_sub_logCutoffProfile_comp_mem_Icc (χ := 1) (ρ := ρ) (p := z) hε h2
      zero_le_one le_rfl
  · have : ∀ᶠ z in 𝓝 (0 : E), ρ z < ε := by
      refine hρc.continuous.continuousAt.eventually_lt continuousAt_const ?_
      simpa [ρ] using hε
    filter_upwards [this] with z hz
    simp [β, logCutoffProfile_eq_zero_of_le h2 hz.le]
  · -- The support lies where `ρ ≤ δ`, that is, in the Euclidean ball of radius `r / (a₁ + 1)`.
    have hsub : tsupport β ⊆ {z | ρ z ≤ δ} := fun z hz ↦ not_lt.1 fun h ↦
      notMem_tsupport_mul_one_sub_logCutoffProfile_comp (χ := 1) hε h2
        hρc.continuous.continuousAt h (by rwa [one_mul])
    intro z hzs
    have hTz : ‖T z‖ ≤ r / (a₁ + 1) := by
      rw [← hsqrt, ← Real.sqrt_sq (by positivity : 0 ≤ r / (a₁ + 1))]
      exact Real.sqrt_le_sqrt (hsub hzs)
    rw [mem_ball_zero_iff]
    calc ‖z‖ ≤ a₁ * ‖T z‖ := hz z
      _ ≤ a₁ * (r / (a₁ + 1)) := by gcongr
      _ < r := by rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith
  · -- `‖z‖ ‖Dβ(z)‖ ≤ κ / L ≤ η`.
    have h := sqrt_mul_norm_fderiv_logCutoffProfile_comp_le hε h4 (hρd z).differentiableAt
      (by positivity) (hρD z)
    rw [hΛ] at h
    have hD : fderiv ℝ β z = -fderiv ℝ (logCutoffProfile ε δ ∘ ρ) z := fderiv_const_sub _
    rw [hD, norm_neg]
    calc ‖z‖ * ‖fderiv ℝ (logCutoffProfile ε δ ∘ ρ) z‖
        ≤ a₁ * ‖T z‖ * ‖fderiv ℝ (logCutoffProfile ε δ ∘ ρ) z‖ := by gcongr; exact hz z
      _ = a₁ * (√(ρ z) * ‖fderiv ℝ (logCutoffProfile ε δ ∘ ρ) z‖) := by rw [hsqrt]; ring
      _ ≤ a₁ * (logCutoffConst * (2 * a₂) / L) := by gcongr
      _ = κ / L := by simp only [κ]; ring
      _ ≤ η := by
        rw [div_le_iff₀ (by linarith)]
        have : κ = η * (κ / η) := by field_simp
        nlinarith

end SymplecticGeometry

end
