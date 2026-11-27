/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.ContMDiffSection
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.ZeroOneForm.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Density

/-!
# Smooth one-forms and Sobolev `(0,1)`-forms

Let `A` be a finite bundle atlas of a complex vector bundle `V` over a complex curve `M`, and let
`TauCeti.zeroOnePartSobolevL` be the `(0,1)`-projection of the Sobolev space `W^{k,p}` of
`V`-valued one-forms onto the subspace `TauCeti.zeroOneSobolevSections A μ p k` of
`(0,1)`-forms. This file relates it to smooth one-forms.

## Main results

* `TauCeti.coe_zeroOnePartSobolevL_ofContMDiffSection`: the `(0,1)`-projection of the Sobolev
  form of a `Cᵏ` one-form `s` is the Sobolev form of the pointwise `(0,1)`-part of `s`.
* `TauCeti.dense_zeroOnePartSobolevL_ofContMDiffSection`: for `p < ∞`, the `(0,1)`-projections
  of the Sobolev forms of smooth one-forms are dense in the Sobolev `(0,1)`-forms.

## Proof

The first result compares chart data, by Tau Ceti's
`TauCeti.chartValueL_zeroOnePartSobolevL_ae_coord`. The second pushes Tau Ceti's density of
smooth sections, `TauCeti.SobolevSection.dense_ofContMDiffSection_contMDiff`, forward along the
continuous surjection `TauCeti.zeroOnePartSobolevL`.

## References

* [D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*][McDuffSalamon2012],
  Appendix C.1.
-/

public section

open Bundle MeasureTheory Set
open scoped Manifold ContDiff ENNReal

noncomputable section

namespace TauCeti

open SmoothAlmostComplexStructure

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℂ F V]

local instance instVectorBundleRealZeroOneFormSmooth : VectorBundle ℝ F V :=
  VectorBundle.restrictScalars ℝ ℂ F V

variable (A : FiniteBundleAtlas ℂ M F V) (μ : Measure ℂ) [μ.IsAddHaarMeasure] (p : ℝ≥0∞)
  [Fact (1 ≤ p)] (k : ℕ) [IsManifold 𝓘(ℝ, ℂ) ∞ M] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)]

variable {A μ p k} in
/-- **The `(0,1)`-projection of a smooth one-form.** If the `Cᵏ` one-form `t` is the pointwise
`(0,1)`-part of the `Cᵏ` one-form `s`, the `(0,1)`-projection of the Sobolev form of `s` is the
Sobolev form of `t`. -/
theorem coe_zeroOnePartSobolevL_ofContMDiffSection [∀ x, ContinuousSMul ℂ (V x)]
    {s t : Cₛ^k⟮𝓘(ℝ, ℂ); ℂ →L[ℝ] F, fun x ↦ TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x⟯}
    (hst : ∀ x, t x = (ofComplexManifold ℂ M).zeroOnePart (s x)) :
    (zeroOnePartSobolevL A μ p k (SobolevSection.ofContMDiffSection A.tangentHom μ p k s) :
        SobolevSection A.tangentHom μ p k) =
      SobolevSection.ofContMDiffSection A.tangentHom μ p k t := by
  refine SectionChartData.eq_of_chartValueL_ae_eq fun i ↦ ?_
  have hs := chartValueL_zeroOnePartSobolevL_ae_coord
    (SobolevSection.chartValueL_ofContMDiffSection_ae A.tangentHom μ p k s i)
  rw [show (fun x ↦ (ofComplexManifold ℂ M).zeroOnePart (s x)) = ⇑t from (funext hst).symm]
    at hs
  exact hs.trans (SobolevSection.chartValueL_ofContMDiffSection_ae A.tangentHom μ p k t i).symm

variable [T2Space M]

/-- **Density of smooth `(0,1)`-forms.** For `1 ≤ p < ∞`, the `(0,1)`-projections of the Sobolev
forms of the smooth `V`-valued one-forms are dense in the Sobolev `(0,1)`-forms
`zeroOneSobolevSections A μ p k`. -/
theorem dense_zeroOnePartSobolevL_ofContMDiffSection (hp : p ≠ ⊤) :
    Dense {w : zeroOneSobolevSections A μ p k |
      ∃ s : Cₛ^k⟮𝓘(ℝ, ℂ); ℂ →L[ℝ] F, fun x ↦ TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x⟯,
        ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ →L[ℝ] F)) ∞
          (fun x ↦ TotalSpace.mk' (ℂ →L[ℝ] F)
            (E := fun x ↦ TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x) x (s x)) ∧
        zeroOnePartSobolevL A μ p k (SobolevSection.ofContMDiffSection A.tangentHom μ p k s) =
          w} := by
  have h := (zeroOnePartSobolevL_surjective (A := A) (μ := μ) (p := p) (k := k)).denseRange
    |>.dense_image (zeroOnePartSobolevL A μ p k).continuous
      (SobolevSection.dense_ofContMDiffSection_contMDiff A.tangentHom μ p k hp)
  convert h using 1
  ext w
  simp only [mem_ofPred_eq, mem_image]
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨_, ⟨s, hs, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨s, hs, rfl⟩

end TauCeti

end
