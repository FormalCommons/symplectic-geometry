/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.Tempered
public import TauCeti.Analysis.Sobolev.BesselPotential.Schwartz
import SymplecticGeometry.Analysis.Sobolev.BesselPotential.Duality.FromTauCeti
import SymplecticGeometry.Analysis.Sobolev.BesselPotential.Schwartz
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Sobolev.BesselPotential.Multiplication

/-!
# A local criterion for `H^{-1}` regularity of distributions

Let `T` be a complex distribution on an open set `Ω` of a finite-dimensional real inner product
space `E`, and `x ∈ Ω`. If, on real test functions `φ` supported in a neighbourhood `V` of `x`,

`‖T φ‖ ≤ C (‖φ‖_{L²} + ∑ᵢ ‖∂_{vᵢ} φ‖_{L²})`

for some finite family of vectors `vᵢ`, then `T` is `H^{-1}` near `x`
(`Distribution.isLocallySobolevAt_neg_one_of_norm_le`).

The proof cuts `T` off by a test function `χ` supported in `V` with `χ x = 1`. For a Schwartz
function `ψ`, the cut-off distribution `χ T` takes at `ψ` the value of `T` at `χ ψ`
(`Distribution.cutoffTempered_def`), which splits into `T` at the real and imaginary parts of
`χ ψ`. Their `L²` norms and those of their derivatives are at most those of `χ ψ`, which are bounded
by `‖χ ψ‖_{H¹}` (Tau Ceti's `BesselPotentialSpace.norm_inclusionLp_apply_le`, and
`SchwartzMap.norm_toBesselPotentialSpaceCLM_lineDerivOp_le`). Multiplication by the Schwartz
function `χ` is bounded on `H¹` (Tau Ceti's
`SchwartzMap.norm_toLp_fourierMultiplierCLM_smulLeftCLM_le`), so `χ T` is a bounded functional on
`H¹`, hence in `H^{-1}` (`TemperedDistribution.memSobolev_neg_of_norm_le`), and
`Distribution.isLocallySobolevAt_iff_exists_memSobolev_cutoffTempered` concludes.

## Main results

* `Distribution.exists_norm_cutoffTempered_le_of_norm_le`: under the bound, every cut-off `χ T`
  with `χ` supported in `V` is bounded by a multiple of the `H¹` norm on Schwartz functions.
* `Distribution.isLocallySobolevAt_neg_one_of_norm_le`: the criterion.

## References

* G. B. Folland, *Real Analysis: Modern Techniques and Their Applications*, 2nd ed., Wiley, 1999,
  §9.3 (the dual of `H_s` is `H_{-s}`, and `H_1` is the space of `L²` functions with first
  derivatives in `L²`).
-/

public section

open Filter MeasureTheory Set TestFunction TopologicalSpace FourierTransform
open scoped Distributions Topology SchwartzMap LineDeriv Real

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω : Opens E}

/-- If `T` is bounded on real test functions supported in `V` by the bracket
`‖φ‖_{L²} + ∑ᵢ ‖∂_{vᵢ} φ‖_{L²}`, then for every complex test function `χ` supported in `V`, the
cut-off distribution `χ T` is bounded by a multiple of the `H¹` norm on Schwartz functions. -/
theorem exists_norm_cutoffTempered_le_of_norm_le {T : 𝓓'(Ω, ℂ)} {ι : Type*} [Fintype ι]
    (v : ι → E) {V : Set E} {C : ℝ}
    (hT : ∀ φ : 𝓓(Ω, ℝ), tsupport φ ⊆ V →
      ‖T φ‖ ≤ C * ((eLpNorm (φ : E → ℝ) 2 volume).toReal +
        ∑ i, (eLpNorm ((∂_{v i} φ : 𝓓(Ω, ℝ)) : E → ℝ) 2 volume).toReal))
    {χ : 𝓓(Ω, ℂ)} (hχ : tsupport χ ⊆ V) :
    ∃ K, ∀ ψ : 𝓢(E, ℂ),
      ‖T.cutoffTempered χ ψ‖ ≤ K * ‖SchwartzMap.toBesselPotentialSpaceCLM 1 2 ψ‖ := by
  -- The bound with a nonnegative constant `C'`.
  set C' := max C 0
  have hC' : 0 ≤ C' := le_max_right C 0
  have hT' (φ : 𝓓(Ω, ℝ)) (hφ : tsupport φ ⊆ V) :
      ‖T φ‖ ≤ C' * ((eLpNorm (φ : E → ℝ) 2 volume).toReal +
        ∑ i, (eLpNorm ((∂_{v i} φ : 𝓓(Ω, ℝ)) : E → ℝ) 2 volume).toReal) :=
    (hT φ hφ).trans (mul_le_mul_of_nonneg_right (le_max_left C 0) (by positivity))
  set χs : 𝓢(E, ℂ) := toSchwartzMapCLM ℂ χ
  set M := 2 ^ (|(1 : ℝ)| / 2) * ∫ ζ, (1 + ‖ζ‖ ^ 2) ^ (|(1 : ℝ)| / 2) * ‖𝓕 χs ζ‖
  set A := 1 + ∑ i, 2 * π * ‖v i‖
  have hA : 0 ≤ A := by positivity
  refine ⟨2 * C' * (A * M), fun ψ ↦ ?_⟩
  -- The product `χ ψ`, as a test function `g` and as a Schwartz function `f`.
  set g : 𝓓(Ω, ℂ) := bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) (ψ.smooth ⊤) χ
  set f : 𝓢(E, ℂ) := SchwartzMap.smulLeftCLM ℂ (χs : E → ℂ) ψ
  have hgf : toSchwartzMapCLM ℂ g = f := by
    ext y
    rw [SchwartzMap.smulLeftCLM_apply_apply χs.hasTemperateGrowth]
    simp [g, χs]
  have hgV : tsupport g ⊆ V := by
    have : tsupport g ⊆ tsupport χ := by
      simpa [g] using tsupport_mul_subset_left (f := (χ : E → ℂ)) (g := ψ)
    exact this.trans hχ
  -- `T` at a real part of `g`: its bracket is at most that of `f`, which `‖f‖_{H¹}` bounds.
  have hpart {L : ℂ →L[ℝ] ℝ} (hL : ∀ z, ‖L z‖ ≤ ‖z‖) :
      ‖T (postcompCLM (𝕜 := ℝ) L g)‖ ≤
        C' * (A * ‖SchwartzMap.toBesselPotentialSpaceCLM 1 2 f‖) := by
    have hle (h : 𝓓(Ω, ℂ)) : (eLpNorm (postcompCLM (𝕜 := ℝ) L h : E → ℝ) 2 volume).toReal ≤
        (eLpNorm (toSchwartzMapCLM ℂ h : E → ℂ) 2 volume).toReal :=
      ENNReal.toReal_mono ((toSchwartzMapCLM ℂ h).memLp 2 volume).eLpNorm_ne_top
        (eLpNorm_mono (postcompCLM (𝕜 := ℝ) L h).continuous.aestronglyMeasurable
          fun y ↦ by simpa using hL (h y))
    refine (hT' _ ((tsupport_comp_subset (map_zero L) g).trans hgV)).trans
      (mul_le_mul_of_nonneg_left ?_ hC')
    rw [add_mul, one_mul, Finset.sum_mul]
    refine add_le_add ((hle g).trans ?_) (Finset.sum_le_sum fun i _ ↦ ?_)
    · rw [hgf, ← SchwartzMap.norm_toLp,
        ← BesselPotentialSpace.inclusionLp_toBesselPotentialSpaceCLM zero_le_one]
      exact BesselPotentialSpace.norm_inclusionLp_apply_le zero_le_one _
    · rw [TestFunction.lineDerivOp_eq_lineDerivCLM ℝ, lineDerivCLM_postcompCLM,
        ← TestFunction.lineDerivOp_eq_lineDerivCLM ℝ]
      refine (hle _).trans ?_
      rw [toSchwartzMapCLM_lineDerivOp, hgf]
      have h := SchwartzMap.norm_toBesselPotentialSpaceCLM_lineDerivOp_le 0 (v i) f
      rwa [zero_add, SchwartzMap.norm_toBesselPotentialSpaceCLM_zero] at h
  -- Multiplication by `χ` is bounded on `H¹`.
  have hf : ‖SchwartzMap.toBesselPotentialSpaceCLM 1 2 f‖ ≤
      M * ‖SchwartzMap.toBesselPotentialSpaceCLM 1 2 ψ‖ := by
    simpa [← BesselPotentialSpace.norm_toLp_eq, M] using
      SchwartzMap.norm_toLp_fourierMultiplierCLM_smulLeftCLM_le 1 χs ψ
  calc ‖T.cutoffTempered χ ψ‖
      = ‖T (postcompCLM (𝕜 := ℝ) Complex.reCLM g) +
          Complex.I * T (postcompCLM (𝕜 := ℝ) Complex.imCLM g)‖ := by
        rw [cutoffTempered_def, complexPairing_apply]
    _ ≤ C' * (A * ‖SchwartzMap.toBesselPotentialSpaceCLM 1 2 f‖) +
          C' * (A * ‖SchwartzMap.toBesselPotentialSpaceCLM 1 2 f‖) := by
        refine (norm_add_le _ _).trans (add_le_add (hpart fun z ↦ ?_) ?_)
        · simpa using Complex.abs_re_le_norm z
        · rw [norm_mul, Complex.norm_I, one_mul]
          exact hpart fun z ↦ by simpa using Complex.abs_im_le_norm z
    _ ≤ 2 * C' * (A * M) * ‖SchwartzMap.toBesselPotentialSpaceCLM 1 2 ψ‖ := by
        have := mul_le_mul_of_nonneg_left hf (mul_nonneg hC' hA)
        nlinarith [this]

/-- **A local criterion for `H^{-1}`.** Let `T` be a complex distribution on `Ω` and `x ∈ Ω`. If
for some neighbourhood `V` of `x`, finite family of vectors `v`, and constant `C`, every real test
function `φ` supported in `V` satisfies `‖T φ‖ ≤ C (‖φ‖_{L²} + ∑ᵢ ‖∂_{vᵢ} φ‖_{L²})`, then `T` is
`H^{-1}` near `x`. -/
theorem isLocallySobolevAt_neg_one_of_norm_le {T : 𝓓'(Ω, ℂ)} {x : E} (hx : x ∈ Ω)
    {ι : Type*} [Fintype ι] (v : ι → E) {V : Set E} (hV : V ∈ 𝓝 x) {C : ℝ}
    (hT : ∀ φ : 𝓓(Ω, ℝ), tsupport φ ⊆ V →
      ‖T φ‖ ≤ C * ((eLpNorm (φ : E → ℝ) 2 volume).toReal +
        ∑ i, (eLpNorm ((∂_{v i} φ : 𝓓(Ω, ℝ)) : E → ℝ) 2 volume).toReal)) :
    T.IsLocallySobolevAt (-1) x := by
  -- A cutoff `χ` supported in `V` with `χ x = 1`.
  obtain ⟨χ, hχV, hχx⟩ := exists_tsupport_subset_apply_eq (n := ⊤)
    (inter_mem hV (Ω.isOpen.mem_nhds hx)) inter_subset_right (1 : ℂ)
  obtain ⟨K, hK⟩ := exists_norm_cutoffTempered_le_of_norm_le v hT (hχV.trans inter_subset_left)
  exact isLocallySobolevAt_iff_exists_memSobolev_cutoffTempered.2
    ⟨χ, by simp [hχx], TemperedDistribution.memSobolev_neg_of_norm_le hK⟩

end Distribution

end
