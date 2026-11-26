/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Analysis.Sobolev.Wkp.Hilbert
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.ZeroOneForm.Basic
import TauCeti.Geometry.Manifold.Complex.Analytic

/-!
# Sobolev sections of exponent two are Hilbert spaces up to isomorphism

At exponent `p = 2`, the norm of `TauCeti.SobolevSection A μ 2 k` is the maximum of the norms of
its chart components, so it does not come from an inner product. The space is nevertheless
continuously linearly equivalent to a real Hilbert space, and so is its subspace of
`(0,1)`-forms; this is what the Fredholm theory along a connected family of operators,
`ContinuousOn.isFredholm_of_isPreconnected`, needs of its target.

* The chart data `C.SobolevData μ 2 k` is a finite product of scalar spaces `W^{k,2}`, each
  equivalent to a Hilbert space by `TauCeti.Wkp.exists_continuousLinearEquiv_innerProductSpace`,
  hence equivalent to a `PiLp 2` of Hilbert spaces.
* `TauCeti.SobolevSection A μ 2 k` is a closed subspace of it, and
  `TauCeti.zeroOneSobolevSections A μ 2 k` a closed subspace of that; a closed subspace of a space
  equivalent to a Hilbert space is one too
  (`Submodule.exists_continuousLinearEquiv_innerProductSpace_of_isClosed`).

## Main results

* `TauCeti.SectionChartData.SobolevData.exists_continuousLinearEquiv_innerProductSpace`: the chart
  data of order `k` and exponent two is equivalent to a Hilbert space.
* `TauCeti.SobolevSection.exists_continuousLinearEquiv_innerProductSpace`: so is the space
  `W^{k,2}(V)` of Sobolev sections of a vector bundle.
* `TauCeti.exists_continuousLinearEquiv_innerProductSpace_zeroOneSobolevSections`: so is its
  subspace of `(0,1)`-forms.

The file also names the normed group and real normed space structures of
`TauCeti.zeroOneSobolevSections A μ p k` as instances
(`TauCeti.zeroOneSobolevSections.instNormedAddCommGroup`,
`TauCeti.zeroOneSobolevSections.instNormedSpace`): instance search finds them for a concrete
atlas only within a larger budget than it has when nested in another search, such as that for the
operator norm on maps into these spaces.

## References

* [D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*][McDuffSalamon2012],
  Appendix B.
-/

public section

noncomputable section

open MeasureTheory Module
open scoped Manifold ContDiff ENNReal

universe u

namespace TauCeti

section SobolevSection

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {S : Type*} [AddCommGroup S] [Module ℝ S]

/-- The tuples of scalar Sobolev functions of order `k` and exponent two, one for each chart and
each basis vector of the model fibre, form a space continuously linearly equivalent to a real
Hilbert space. -/
theorem SectionChartData.SobolevData.exists_continuousLinearEquiv_innerProductSpace
    (C : SectionChartData E F S) (μ : Measure E) [μ.IsAddHaarMeasure] (k : ℕ) :
    ∃ (K : Type u) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℝ K) (_ : CompleteSpace K),
      Nonempty (C.SobolevData μ 2 k ≃L[ℝ] K) := by
  choose H _ _ _ e using fun i : Fin C.n ↦ Wkp.exists_continuousLinearEquiv_innerProductSpace μ
    (C.image i) k
  exact ⟨PiLp 2 fun i : Fin C.n ↦ PiLp 2 fun _ : Fin (finrank ℝ F) ↦ H i, _, _, inferInstance,
    ⟨(ContinuousLinearEquiv.piCongrRight fun i ↦ (ContinuousLinearEquiv.piCongrRight
      fun _ ↦ (e i).some).trans (PiLp.continuousLinearEquiv 2 ℝ _).symm).trans
      (PiLp.continuousLinearEquiv 2 ℝ _).symm⟩⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]
  {V : M → Type*} [TopologicalSpace (Bundle.TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [FiniteDimensional ℝ F]

/-- **`W^{k,2}(V)` is a Hilbert space up to isomorphism.** For a finite bundle atlas `A` of a
vector bundle `V` over a manifold without boundary, a Haar measure `μ` and every order `k`, the
Sobolev space `W^{k,2}(V)` of sections is continuously linearly equivalent to a real Hilbert
space. -/
theorem SobolevSection.exists_continuousLinearEquiv_innerProductSpace
    (A : FiniteBundleAtlas E M F V) (μ : Measure E) [μ.IsAddHaarMeasure] (k : ℕ) :
    ∃ (K : Type u) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℝ K) (_ : CompleteSpace K),
      Nonempty (SobolevSection A μ 2 k ≃L[ℝ] K) := by
  obtain ⟨H, _, _, _, ⟨e⟩⟩ :=
    SectionChartData.SobolevData.exists_continuousLinearEquiv_innerProductSpace
      A.sectionChartData μ k
  exact Submodule.exists_continuousLinearEquiv_innerProductSpace_of_isClosed
    (SectionChartData.isClosed_sobolevSections (A.aeTransition_sectionChartData μ)) e
end SobolevSection

section ZeroOne

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (Bundle.TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℂ F V]

/-- The real vector bundle underlying the complex vector bundle `V`, as in
`TauCeti.zeroOneSobolevSections`. -/
local instance instVectorBundleRealHilbert : VectorBundle ℝ F V :=
  VectorBundle.restrictScalars ℝ ℂ F V

/-- The normed group structure of the Sobolev `(0,1)`-forms, that of a subspace of
`TauCeti.SobolevSection A.tangentHom μ p k`. -/
instance zeroOneSobolevSections.instNormedAddCommGroup (A : FiniteBundleAtlas ℂ M F V)
    (μ : Measure ℂ) [μ.IsAddHaarMeasure] (p : ℝ≥0∞) [Fact (1 ≤ p)] (k : ℕ) :
    NormedAddCommGroup (zeroOneSobolevSections A μ p k) :=
  inferInstance

/-- The real normed space structure of the Sobolev `(0,1)`-forms, that of a subspace of
`TauCeti.SobolevSection A.tangentHom μ p k`. -/
instance zeroOneSobolevSections.instNormedSpace (A : FiniteBundleAtlas ℂ M F V)
    (μ : Measure ℂ) [μ.IsAddHaarMeasure] (p : ℝ≥0∞) [Fact (1 ≤ p)] (k : ℕ) :
    NormedSpace ℝ (zeroOneSobolevSections A μ p k) :=
  inferInstance

/-- **The Sobolev `(0,1)`-forms at exponent two are a Hilbert space up to isomorphism.** For a
finite bundle atlas `A` of a complex vector bundle `V` over a complex curve, a Haar measure `μ` on
`ℂ` and every order `k`, the space `W^{k,2}(Λ^{0,1} ⊗_ℂ V)` of `(0,1)`-forms is continuously
linearly equivalent to a real Hilbert space. -/
theorem exists_continuousLinearEquiv_innerProductSpace_zeroOneSobolevSections
    (A : FiniteBundleAtlas ℂ M F V) (μ : Measure ℂ) [μ.IsAddHaarMeasure] (k : ℕ) :
    ∃ (K : Type) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℝ K) (_ : CompleteSpace K),
      Nonempty (zeroOneSobolevSections A μ 2 k ≃L[ℝ] K) := by
  have : IsManifold 𝓘(ℝ, ℂ) 1 M :=
    IsManifold.restrictScalars_of_ne_zero 1 (m := ∞) (by simp) inferInstance
  obtain ⟨H, _, _, _, ⟨e⟩⟩ :=
    SobolevSection.exists_continuousLinearEquiv_innerProductSpace A.tangentHom μ k
  exact Submodule.exists_continuousLinearEquiv_innerProductSpace_of_isClosed
    isClosed_zeroOneSobolevSections e

end ZeroOne


end TauCeti

end
