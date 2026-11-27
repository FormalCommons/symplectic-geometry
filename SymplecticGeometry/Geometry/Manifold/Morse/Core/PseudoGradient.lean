/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.PseudoGradient.Existence
import TauCeti.Geometry.Manifold.PartitionOfUnity.Compact
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# A compactly supported pseudo-gradient near a compact set

Let `g` be a smooth function on a boundaryless Hausdorff sigma-compact manifold `M` modelled on a
finite-dimensional real normed space `E`, and let `K ⊆ M` be a compact set on which every critical
point of `g` is nondegenerate. Tau Ceti's `IsCompact.exists_contMDiff_pseudoGradientOn_nhds` gives
a smooth field `X₀` along which `g` strictly decreases at the regular points of a neighbourhood `U`
of `K`, and which is the linear field of a Morse chart near each critical point of `K`; outside `U`
nothing is known about it.

## Main results

* `IsCompact.exists_contMDiff_pseudoGradient_eq_zero_off`: there is a smooth vector field `X`
  vanishing outside a compact set, with `dg(X) ≤ 0` everywhere, `dg(X) < 0` at the regular points
  of `K`, and equal near each critical point of `K` to the linear field
  `TauCeti.MorseChart.field` on the whole source of a Morse chart.

Such a field is complete (`TauCeti.isCompleteVectorField_of_isCompact_of_eq_zero_off`), and it has
the form that `TauCeti.MorseChart.exists_cubeChart_unstableSet` (`Morse/Core/Cube.lean`) asks for.

## Construction

`X = χ • X₀`, for a smooth cutoff `0 ≤ χ ≤ 1` (Tau Ceti's
`IsCompact.exists_contMDiff_one_nhds_tsupport_subset`) equal to `1` near `K`, with compact support
inside `U`. Then `dg(X) = χ · dg(X₀)`, which is `≤ 0` since
`dg(X₀) < 0` at the regular points of `U` and `dg(X₀) = 0` at critical points. The Morse charts of
`X₀` are shrunk with `TauCeti.MorseChart.restr` to the open set where `χ = 1`.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Proposition 2.2.3 and its proof.
-/

public section

open Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [SigmaCompactSpace M] {g : M → ℝ}

/-- **A compactly supported pseudo-gradient near a compact set.** Let `K` be a compact subset of a
Hausdorff sigma-compact manifold modelled on a finite-dimensional real normed space, and let `g`
be smooth with only nondegenerate critical points in `K`. Then there is a smooth vector field `X`
on `M`, vanishing outside a compact set, such that `g` never increases along `X`, strictly
decreases along `X` at every regular point of `K`, and such that around each critical point
`x ∈ K` the field `X` agrees with the linear field of some Morse chart at `x` on its whole
source. -/
theorem _root_.IsCompact.exists_contMDiff_pseudoGradient_eq_zero_off {K : Set M}
    (hK : IsCompact K) (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ g)
    (hnd : ∀ x ∈ K, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) g x = 0 →
      IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) g x) :
    ∃ X : (x : M) → TangentSpace 𝓘(ℝ, E) x,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞ (fun x ↦ (⟨x, X x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
      (∃ C, IsCompact C ∧ ∀ x ∉ C, X x = 0) ∧
      (∀ x, mvfderiv 𝓘(ℝ, E) g x (X x) ≤ 0) ∧
      (∀ x ∈ K, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) g x ≠ 0 → mvfderiv 𝓘(ℝ, E) g x (X x) < 0) ∧
      ∀ x ∈ K, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) g x = 0 →
        ∃ φ : MorseChart E g x, ∀ y ∈ φ.toChart.source, X y = φ.field y := by
  obtain ⟨U, hU, hUo, X₀, hX₀, hdesc, hchart⟩ := hK.exists_contMDiff_pseudoGradientOn_nhds hg hnd
  -- A cutoff `χ`, equal to `1` on an open neighbourhood `V` of `K`, with compact support in `U`.
  obtain ⟨χ, hχ, hχ1, hχc, hχU, hχI⟩ :=
    hK.exists_contMDiff_one_nhds_tsupport_subset 𝓘(ℝ, E) hUo (subset_of_mem_nhdsSet hU)
  have hχ0 (x : M) (hx : x ∉ tsupport χ) : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
  obtain ⟨V, ⟨hVo, hKV⟩, hχV⟩ := (hasBasis_nhdsSet K).eventually_iff.1 hχ1
  have hdX (x : M) : mvfderiv 𝓘(ℝ, E) g x (χ x • X₀ x) =
      χ x * mvfderiv 𝓘(ℝ, E) g x (X₀ x) := by
    rw [map_smul, smul_eq_mul]
  refine ⟨fun x ↦ χ x • X₀ x, ContMDiff.smul_section hχ hX₀,
    ⟨tsupport χ, hχc, fun x hx ↦ by simp [hχ0 x hx]⟩, fun x ↦ ?_, fun x hx hx0 ↦ ?_,
    fun x hx hx0 ↦ ?_⟩
  · rw [hdX]
    by_cases hxL : x ∈ tsupport χ
    · refine mul_nonpos_of_nonneg_of_nonpos (hχI x).1 ?_
      by_cases hx0 : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) g x = 0
      · simp [mvfderiv_eq_zero_iff.2 hx0]
      · exact (hdesc x (hχU hxL) hx0).le
    · rw [hχ0 x hxL, zero_mul]
  · rw [hdX, hχV (hKV hx), one_mul]
    exact hdesc x (hχU (subset_tsupport χ (by simp [hχV (hKV hx)]))) hx0
  · obtain ⟨φ, -, hφ⟩ := hchart x hx hx0
    refine ⟨φ.restr hVo (hKV hx), fun y hy ↦ ?_⟩
    rw [MorseChart.restr_source] at hy
    rw [MorseChart.restr_field, ← hφ y hy.1]
    simp [hχV hy.2]

end TauCeti

end
