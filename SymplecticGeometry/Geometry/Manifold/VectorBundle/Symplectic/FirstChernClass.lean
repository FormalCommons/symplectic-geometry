/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Symplectic.Classification
public import SymplecticGeometry.Topology.VectorBundle.Complex.FirstChernClass
public import SymplecticGeometry.Topology.VectorBundle.Complex.Structure

/-!
# First Chern classes of complex structures on vector bundles

A complex structure `J` on a real vector bundle `V` makes `V` a complex vector bundle
`J.toContinuousComplexStructure.Fiber`, which has a first Chern class
`SymplecticGeometry.Bundle.firstChernClass` (the Euler class of its determinant line). This file
relates these classes to the operations on complex structures and to tameness:

* `ContMDiffComplexStructure.firstChernClass_pullback`: the class of the pull-back
  `J.pullback f hf` along a `Cⁿ` map `f` is the pull-back of the class of `J`;
* `ContMDiffComplexStructure.firstChernClass_pushforward`: transport along an isomorphism of
  vector bundles does not change the class;
* `ContMDiffComplexStructure.firstChernClass_neg`: the complex bundle of `-J` has the opposite
  class, since it is the conjugate of the bundle of `J`;
* `ContMDiffTwoForm.Tames.firstChernClass_eq`: two complex structures tamed by the same two-form,
  of any regularities, have the same class, since they give isomorphic complex bundles
  (`ContMDiffTwoForm.Tames.exists_complex_bundleEquiv`).

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.6
  (Proposition 2.6.4) and §2.7.
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §14.
-/

public section

open _root_.Bundle Module TauCeti.Bundle.ContinuousComplexStructure
open scoped Manifold

namespace SymplecticGeometry.Bundle

variable {EB HB : Type*} {M : Type} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [TopologicalSpace HB] {I : ModelWithCorners ℝ EB HB}
  [TopologicalSpace M] [ChartedSpace HB M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  (G : Type*) [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  [Fact (finrank ℝ F = 2 * finrank ℂ G)] {n m : ℕ∞}

namespace ContMDiffComplexStructure

/-- **Naturality of the first Chern class of a complex structure.** The complex bundle of the
pull-back `J.pullback f hf` along a `Cⁿ` map `f : N → M`, of any type `K` with
`[ContinuousMapClass K N M]`, has the pull-back along `f` of the first Chern class of the complex
bundle of `J`. -/
theorem firstChernClass_pullback {EN HN : Type*} {N : Type} [NormedAddCommGroup EN]
    [NormedSpace ℝ EN] [TopologicalSpace HN] {I' : ModelWithCorners ℝ EN HN} [TopologicalSpace N]
    [ChartedSpace HN N] {K : Type*} [FunLike K N M] [ContinuousMapClass K N M]
    (J : ContMDiffComplexStructure I n F V) (f : K) (hf : ContMDiff I' I n f) :
    firstChernClass G (J.pullback f hf).toContinuousComplexStructure.Fiber =
      TopCat.singularCohomologyMap (TopCat.ofHom (f : C(N, M))) 2
        (firstChernClass G J.toContinuousComplexStructure.Fiber) := by
  rw [← SymplecticGeometry.Bundle.firstChernClass_pullback]
  exact firstChernClass_congr (J.pullbackFiberEquiv f hf)
    (continuous_pullbackFiberEquiv G J f hf)

/-- **Transport does not change the first Chern class.** The transport `Φ ∘ J ∘ Φ⁻¹` of a complex
structure `J` along an isomorphism `Φ : V ≃ V₂` of vector bundles, whose map of total spaces is
`Cⁿ`, gives a complex bundle with the same first Chern class as `J`. -/
theorem firstChernClass_pushforward
    {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
    {V₂ : M → Type}
    [∀ x, AddCommGroup (V₂ x)] [∀ x, Module ℝ (V₂ x)] [∀ x, TopologicalSpace (V₂ x)]
    [∀ x, IsTopologicalAddGroup (V₂ x)] [∀ x, ContinuousSMul ℝ (V₂ x)]
    [TopologicalSpace (TotalSpace F₂ V₂)] [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂]
    (G₂ : Type*) [NormedAddCommGroup G₂] [NormedSpace ℂ G₂] [FiniteDimensional ℂ G₂]
    [Fact (finrank ℝ F₂ = 2 * finrank ℂ G₂)] (Φ : ∀ x, V x ≃L[ℝ] V₂ x)
    (hΦ : ContMDiff (I.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F₂)) n
      (fun p : TotalSpace F V ↦ TotalSpace.mk' F₂ p.proj (Φ p.proj p.snd)))
    (J : ContMDiffComplexStructure I n F V) :
    firstChernClass G₂ (J.pushforward Φ hΦ).toContinuousComplexStructure.Fiber =
      firstChernClass G J.toContinuousComplexStructure.Fiber := by
  have hc : ∀ x v, Φ x (J.toContinuousComplexStructure x v) =
      (J.pushforward Φ hΦ).toContinuousComplexStructure x (Φ x v) := fun x v ↦ by
    simp [pushforward_apply]
  exact (firstChernClass_congr (fiberEquivOfCommute _ _ Φ hc)
    (continuous_fiberEquivOfCommute _ _ Φ hc hΦ.continuous)).symm

/-- **Negating a complex structure negates the first Chern class.** The complex bundle of `-J`
has the opposite of the first Chern class of the complex bundle of `J`: through the identity of
`V`, it is the conjugate of that bundle. -/
@[simp]
theorem firstChernClass_neg (J : ContMDiffComplexStructure I n F V) :
    firstChernClass G (-J).toContinuousComplexStructure.Fiber =
      -firstChernClass G J.toContinuousComplexStructure.Fiber := by
  -- The identity of `V` intertwines `-J` with `-J`.
  have hc : ∀ x v, ContinuousLinearEquiv.refl ℝ (V x) ((-J).toContinuousComplexStructure x v) =
      -J.toContinuousComplexStructure x (ContinuousLinearEquiv.refl ℝ (V x) v) := fun x v ↦ by
    rw [ContinuousLinearEquiv.refl_apply, ContinuousLinearEquiv.refl_apply,
      toContinuousComplexStructure_apply, toContinuousComplexStructure_apply, neg_apply,
      _root_.neg_apply]
  rw [← firstChernClass_conj (G := G) (E := J.toContinuousComplexStructure.Fiber)]
  exact firstChernClass_congr (fiberEquivConjOfAnticommute _ _ _ hc)
    (continuous_fiberEquivConjOfAnticommute _ _ _ hc (continuous_id.congr fun _ ↦ rfl))

end ContMDiffComplexStructure

namespace ContMDiffTwoForm

/-- **Complex structures tamed by one form have the same first Chern class.** If a two-form `ω`
tames complex structures `J` and `J'`, of any regularities, then the complex bundles `(V, J)` and
`(V, J')` have the same first Chern class. -/
theorem Tames.firstChernClass_eq {m' : ℕ∞} {ω : ContMDiffTwoForm I n F V}
    {J : ContMDiffComplexStructure I m F V} {J' : ContMDiffComplexStructure I m' F V}
    (h : ω.Tames J) (h' : ω.Tames J') :
    firstChernClass G J'.toContinuousComplexStructure.Fiber =
      firstChernClass G J.toContinuousComplexStructure.Fiber := by
  -- At regularity `0`, a fibrewise equivalence, continuous on total spaces, intertwines them.
  rw [← J.toContinuousComplexStructure_ofLE zero_le,
    ← J'.toContinuousComplexStructure_ofLE zero_le]
  -- `ContMDiffComplexStructure` counts regularity in `ℕ∞`, bundles in `WithTop ℕ∞`.
  have : ContMDiffVectorBundle ((0 : ℕ∞) : WithTop ℕ∞) F V I :=
    WithTop.coe_zero (α := ℕ∞) ▸ inferInstance
  obtain ⟨Ψ, hΨ, hJ⟩ := ((ContMDiffTwoForm.tames_ofLE_iff zero_le).2 h).exists_complex_bundleEquiv
    ((ContMDiffTwoForm.tames_ofLE_iff zero_le).2 h')
  have hc : ∀ x v, Ψ x ((J.ofLE zero_le).toContinuousComplexStructure x v) =
      (J'.ofLE zero_le).toContinuousComplexStructure x (Ψ x v) := fun x v ↦ by
    simpa only [ContMDiffComplexStructure.toContinuousComplexStructure_apply] using hJ x v
  exact (firstChernClass_congr (fiberEquivOfCommute _ _ Ψ hc)
    (continuous_fiberEquivOfCommute _ _ Ψ hc hΨ.continuous)).symm

end ContMDiffTwoForm

end SymplecticGeometry.Bundle
