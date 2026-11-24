/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.MeasureTheory.Function.L2Space
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.ZeroOneForm
import TauCeti.Geometry.Manifold.Complex.Analytic
import TauCeti.MeasureTheory.Function.Lp.Basic

/-!
# Sobolev spaces of exponent two are Hilbert spaces up to isomorphism

At exponent `p = 2` the Sobolev spaces built in Tau Ceti carry norms that are not themselves
given by inner products: the norm of `TauCeti.SobolevSection A μ 2 k` is the maximum of the norms
of its chart components, and the iterated weak derivatives take values in iterated spaces of
continuous linear maps with their operator norms. They are nevertheless continuously linearly
equivalent to real Hilbert spaces, which is what the Fredholm theory along a connected family of
operators, `ContinuousOn.isFredholm_of_isPreconnected`, needs of its target.

The argument embeds each space by a continuous injective linear map with closed range into a
space already known to be equivalent to a Hilbert space; the open mapping theorem, through
`ContinuousLinearMap.equivRange`, identifies the domain with the range, a closed subspace of a
Hilbert space.

* `Lp G 2 μ` for a finite-dimensional `G` is carried onto `L²` with values in a Euclidean space by
  a linear isomorphism `G ≃L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ G))`.
* `TauCeti.Wkp μ Ω 2 (k + 1)` embeds into the product of `TauCeti.Wkp μ Ω 2 k` and the `L²`
  space of its highest weak derivatives, by `TauCeti.Wkp.lowerOrderL` and
  `TauCeti.Wkp.iteratedGradientL`; by induction on `k` all these spaces are equivalent to Hilbert
  spaces.
* `TauCeti.SobolevSection A μ 2 k` is a closed subspace of a finite product of scalar Sobolev
  spaces, and `TauCeti.zeroOneSobolevSections A μ 2 k` a closed subspace of it.

## Main results

* `ContinuousLinearMap.exists_continuousLinearEquiv_innerProductSpace`: the domain of an injective
  continuous linear map with closed range from a Banach space into a Hilbert space is equivalent to
  a Hilbert space.
* `MeasureTheory.Lp.exists_continuousLinearEquiv_innerProductSpace`: `L²` with values in a
  finite-dimensional normed space is equivalent to a Hilbert space.
* `TauCeti.Wkp.exists_continuousLinearEquiv_innerProductSpace`: so is `W^{k,2}(Ω)`.
* `TauCeti.SobolevSection.exists_continuousLinearEquiv_innerProductSpace`: so is the space
  `W^{k,2}(V)` of Sobolev sections of a vector bundle.
* `TauCeti.exists_continuousLinearEquiv_innerProductSpace_zeroOneSobolevSections`: so is its
  subspace of `(0,1)`-forms.

## References

* [D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*][McDuffSalamon2012],
  Appendix B.
-/

public section

noncomputable section

open MeasureTheory Module
open scoped Manifold ContDiff

universe u v w

namespace ContinuousLinearMap

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A Banach space that a continuous linear map embeds injectively, with closed range, into a
real Hilbert space is continuously linearly equivalent to a real Hilbert space, namely the
range. -/
theorem exists_continuousLinearEquiv_innerProductSpace (f : X →L[ℝ] H)
    (hinj : Function.Injective f) (hclo : IsClosed (Set.range f)) :
    ∃ (K : Type w) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℝ K) (_ : CompleteSpace K),
      Nonempty (X ≃L[ℝ] K) :=
  have : CompleteSpace (LinearMap.range (f : X →ₗ[ℝ] H)) := hclo.completeSpace_coe
  ⟨LinearMap.range (f : X →ₗ[ℝ] H), _, _, this, ⟨f.equivRange hinj hclo⟩⟩

/-- A Banach space that a continuous linear map embeds injectively, with closed range, into a
space continuously linearly equivalent to a real Hilbert space is itself continuously linearly
equivalent to a real Hilbert space. -/
theorem exists_continuousLinearEquiv_innerProductSpace_of_continuousLinearEquiv
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] (f : X →L[ℝ] Y) (e : Y ≃L[ℝ] H)
    (hinj : Function.Injective f) (hclo : IsClosed (Set.range f)) :
    ∃ (K : Type w) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℝ K) (_ : CompleteSpace K),
      Nonempty (X ≃L[ℝ] K) := by
  refine exists_continuousLinearEquiv_innerProductSpace ((e : Y →L[ℝ] H).comp f)
    (e.injective.comp hinj) ?_
  rw [coe_comp, Set.range_comp]
  exact e.toHomeomorph.isClosedMap _ hclo

end ContinuousLinearMap

namespace Submodule

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A closed subspace of a Banach space that is continuously linearly equivalent to a real Hilbert
space is itself continuously linearly equivalent to a real Hilbert space. -/
theorem exists_continuousLinearEquiv_innerProductSpace_of_isClosed {p : Submodule ℝ X}
    (hp : IsClosed (p : Set X)) (e : X ≃L[ℝ] H) :
    ∃ (K : Type w) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℝ K) (_ : CompleteSpace K),
      Nonempty (p ≃L[ℝ] K) :=
  have : CompleteSpace p := hp.completeSpace_coe
  ContinuousLinearMap.exists_continuousLinearEquiv_innerProductSpace_of_continuousLinearEquiv
    p.subtypeL e Subtype.val_injective (by
      rwa [coe_subtypeL, coe_subtype, Subtype.range_coe])

end Submodule

namespace MeasureTheory.Lp

variable {α : Type u} [MeasurableSpace α] (μ : Measure α)
  (G : Type v) [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]

/-- `L²` with values in a finite-dimensional real normed space is continuously linearly
equivalent to a real Hilbert space. -/
theorem exists_continuousLinearEquiv_innerProductSpace :
    ∃ (K : Type u) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℝ K) (_ : CompleteSpace K),
      Nonempty (Lp G 2 μ ≃L[ℝ] K) := by
  let e : G ≃L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ G)) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  let f := (e : G →L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ G))).compLpL 2 μ
  let g := (e.symm : EuclideanSpace ℝ (Fin (finrank ℝ G)) →L[ℝ] G).compLpL 2 μ
  have hgf : ∀ u, g (f u) = u := fun u ↦ by
    rw [ContinuousLinearMap.compLpL_compLpL, ContinuousLinearEquiv.coe_symm_comp_coe,
      ContinuousLinearMap.compLpL_apply, ContinuousLinearMap.id_compLp]
  have hfg : ∀ y, f (g y) = y := fun y ↦ by
    rw [ContinuousLinearMap.compLpL_compLpL, ContinuousLinearEquiv.coe_comp_coe_symm,
      ContinuousLinearMap.compLpL_apply, ContinuousLinearMap.id_compLp]
  refine ContinuousLinearMap.exists_continuousLinearEquiv_innerProductSpace f
    (Function.LeftInverse.injective hgf) ?_
  rw [(Function.RightInverse.surjective hfg).range_eq]
  exact isClosed_univ

end MeasureTheory.Lp

namespace TauCeti

namespace Wkp

variable {E : Type u} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
  (Ω : TopologicalSpace.Opens E)

/-- **`W^{k,2}` is a Hilbert space up to isomorphism.** For every order `k`, the Sobolev space
`W^{k,2}(Ω)` is continuously linearly equivalent to a real Hilbert space. -/
theorem exists_continuousLinearEquiv_innerProductSpace (k : ℕ) :
    ∃ (K : Type u) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℝ K) (_ : CompleteSpace K),
      Nonempty (Wkp μ Ω 2 k ≃L[ℝ] K) := by
  induction k with
  | zero => exact ⟨_, _, _, inferInstance, ⟨ContinuousLinearEquiv.refl ℝ (Lp ℝ 2 (μ.restrict Ω))⟩⟩
  | succ k ih =>
    obtain ⟨H₁, _, _, _, ⟨e₁⟩⟩ := ih
    obtain ⟨H₂, _, _, _, ⟨e₂⟩⟩ :=
      Lp.exists_continuousLinearEquiv_innerProductSpace (μ.restrict Ω) (IteratedGradient E k)
    let f := (lowerOrderL (mu := μ) (Omega := Ω) (p := 2) k).prod (iteratedGradientL k)
    have hbound : ∀ u, ‖u‖ ≤ ((2 : NNReal) : ℝ) * ‖f u‖ := fun u ↦ by
      have h := norm_le_norm_lowerOrder_add_norm_iteratedGradient k u
      have h₁ : ‖lowerOrder k u‖ ≤ ‖f u‖ := by
        rw [← lowerOrderL_apply]; exact norm_fst_le (f u)
      have h₂ : ‖iteratedGradient k u‖ ≤ ‖f u‖ := by
        rw [← iteratedGradientL_apply]; exact norm_snd_le (f u)
      push_cast
      linarith
    have hanti := f.antilipschitz_of_bound hbound
    refine
      ContinuousLinearMap.exists_continuousLinearEquiv_innerProductSpace_of_continuousLinearEquiv f
        ((e₁.prodCongr e₂).trans (WithLp.prodContinuousLinearEquiv 2 ℝ H₁ H₂).symm)
        hanti.injective (hanti.isClosed_range f.uniformContinuous)

end Wkp

section SobolevSection

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {S : Type*} [AddCommGroup S] [Module ℝ S]

/-- The tuples of scalar Sobolev functions of order `k` and exponent two, one for each chart and
each basis vector of the model fibre, form a space continuously linearly equivalent to a real
Hilbert space. -/
theorem SectionChartData.exists_continuousLinearEquiv_innerProductSpace_sobolevData
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
    A.sectionChartData.exists_continuousLinearEquiv_innerProductSpace_sobolevData μ k
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
