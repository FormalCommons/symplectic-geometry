/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Topology.Algebra.Module.ComplexSmulI
public import TauCeti.Topology.VectorBundle.Complex.Structure
public import TauCeti.Topology.VectorBundle.Conjugate

/-!
# Maps of real bundles that intertwine complex structures

Let `J₁` and `J₂` be continuous complex structures on real vector bundles `V₁` and `V₂` over the
same base, and `Φ x : V₁ x ≃ V₂ x` real-linear equivalences of the fibres.

* If `Φ` intertwines `J₁` with `J₂`, it is a complex-linear equivalence of the complex bundles
  `J₁.Fiber` and `J₂.Fiber` (`TauCeti.Bundle.ContinuousComplexStructure.fiberEquivOfCommute`).
* If `Φ` intertwines `J₁` with `-J₂`, it is a complex-linear equivalence of `J₁.Fiber` with the
  conjugate bundle of `J₂.Fiber`
  (`TauCeti.Bundle.ContinuousComplexStructure.fiberEquivConjOfAnticommute`).

When `Φ` is continuous on total spaces, so are these equivalences, for any complex models of the
two complex bundles.

## References

* J. W. Milnor and J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §14 (complex vector bundles as real bundles with a complex structure).
-/

public section

noncomputable section

open Bundle Module TauCeti.Conjugate

namespace TauCeti.Bundle.ContinuousComplexStructure

variable {B : Type*} [TopologicalSpace B]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  {V₁ : B → Type*} [∀ b, AddCommGroup (V₁ b)] [∀ b, Module ℝ (V₁ b)]
  [∀ b, TopologicalSpace (V₁ b)] [∀ b, IsTopologicalAddGroup (V₁ b)]
  [∀ b, ContinuousSMul ℝ (V₁ b)] [TopologicalSpace (TotalSpace F₁ V₁)]
  [FiberBundle F₁ V₁] [VectorBundle ℝ F₁ V₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  {V₂ : B → Type*} [∀ b, AddCommGroup (V₂ b)] [∀ b, Module ℝ (V₂ b)]
  [∀ b, TopologicalSpace (V₂ b)] [∀ b, IsTopologicalAddGroup (V₂ b)]
  [∀ b, ContinuousSMul ℝ (V₂ b)] [TopologicalSpace (TotalSpace F₂ V₂)]
  [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂]
  (J₁ : ContinuousComplexStructure F₁ V₁) (J₂ : ContinuousComplexStructure F₂ V₂)
  (Φ : ∀ b, V₁ b ≃L[ℝ] V₂ b)

/-! ### Complex-linear maps -/

section Commute

variable (hΦ : ∀ b v, Φ b (J₁ b v) = J₂ b (Φ b v))

/-- A family of real-linear equivalences `Φ` that intertwines `J₁` with `J₂`, as complex-linear
equivalences `J₁.Fiber b ≃ J₂.Fiber b`. -/
def fiberEquivOfCommute (b : B) : J₁.Fiber b ≃L[ℂ] J₂.Fiber b :=
  ((J₁.fiberEquiv b).trans ((Φ b).trans (J₂.fiberEquiv b).symm)).complexOfMapISmul fun v ↦
    (J₂.fiberEquiv b).injective <| by simp [hΦ]

theorem fiberEquivOfCommute_apply (b : B) (v : J₁.Fiber b) :
    J₁.fiberEquivOfCommute J₂ Φ hΦ b v = (J₂.fiberEquiv b).symm (Φ b (J₁.fiberEquiv b v)) := by
  simp [fiberEquivOfCommute]

@[simp]
theorem fiberEquiv_fiberEquivOfCommute (b : B) (v : J₁.Fiber b) :
    J₂.fiberEquiv b (J₁.fiberEquivOfCommute J₂ Φ hΦ b v) = Φ b (J₁.fiberEquiv b v) := by
  rw [fiberEquivOfCommute_apply, ContinuousLinearEquiv.apply_symm_apply]

variable {G₁ : Type*} [NormedAddCommGroup G₁] [NormedSpace ℂ G₁] [FiniteDimensional ℂ G₁]
  [FiniteDimensional ℝ F₁] [Fact (finrank ℝ F₁ = 2 * finrank ℂ G₁)]
  {G₂ : Type*} [NormedAddCommGroup G₂] [NormedSpace ℂ G₂] [FiniteDimensional ℂ G₂]
  [FiniteDimensional ℝ F₂] [Fact (finrank ℝ F₂ = 2 * finrank ℂ G₂)]

/-- If `Φ` is continuous on total spaces, so is `fiberEquivOfCommute`. -/
theorem continuous_fiberEquivOfCommute
    (hc : Continuous fun p : TotalSpace F₁ V₁ ↦ TotalSpace.mk' F₂ (E := V₂) p.proj
      (Φ p.proj p.snd)) :
    Continuous fun p : TotalSpace G₁ J₁.Fiber ↦ TotalSpace.mk' G₂ (E := J₂.Fiber) p.proj
      (J₁.fiberEquivOfCommute J₂ Φ hΦ p.proj p.snd) := by
  refine ((J₂.totalSpaceHomeomorph G₂).symm.continuous.comp
    (hc.comp (J₁.totalSpaceHomeomorph G₁).continuous)).congr fun p ↦ ?_
  rw [Function.comp_apply, Function.comp_apply, totalSpaceHomeomorph_apply,
    totalSpaceHomeomorph_symm_apply, fiberEquivOfCommute_apply]

end Commute

/-! ### Maps to the conjugate bundle -/

section Anticommute

variable (hΦ : ∀ b v, Φ b (J₁ b v) = -J₂ b (Φ b v))

/-- A family of real-linear equivalences `Φ` that intertwines `J₁` with `-J₂`, as complex-linear
equivalences from `J₁.Fiber b` to the conjugate of `J₂.Fiber b`. -/
def fiberEquivConjOfAnticommute (b : B) : J₁.Fiber b ≃L[ℂ] ConjugateBundle J₂.Fiber b :=
  ((J₁.fiberEquiv b).trans ((Φ b).trans ((J₂.fiberEquiv b).symm.trans toConjL'))).complexOfMapISmul
    fun v ↦ ofConj.injective <| (J₂.fiberEquiv b).injective <| by
      simp [hΦ, Complex.conj_I, neg_smul]

theorem fiberEquivConjOfAnticommute_apply (b : B) (v : J₁.Fiber b) :
    J₁.fiberEquivConjOfAnticommute J₂ Φ hΦ b v =
      toConj ((J₂.fiberEquiv b).symm (Φ b (J₁.fiberEquiv b v))) := by
  simp [fiberEquivConjOfAnticommute]

@[simp]
theorem fiberEquiv_ofConj_fiberEquivConjOfAnticommute (b : B) (v : J₁.Fiber b) :
    J₂.fiberEquiv b (ofConj (J₁.fiberEquivConjOfAnticommute J₂ Φ hΦ b v)) =
      Φ b (J₁.fiberEquiv b v) := by
  rw [fiberEquivConjOfAnticommute_apply, ofConj_toConj, ContinuousLinearEquiv.apply_symm_apply]

variable {G₁ : Type*} [NormedAddCommGroup G₁] [NormedSpace ℂ G₁] [FiniteDimensional ℂ G₁]
  [FiniteDimensional ℝ F₁] [Fact (finrank ℝ F₁ = 2 * finrank ℂ G₁)]
  {G₂ : Type*} [NormedAddCommGroup G₂] [NormedSpace ℂ G₂] [FiniteDimensional ℂ G₂]
  [FiniteDimensional ℝ F₂] [Fact (finrank ℝ F₂ = 2 * finrank ℂ G₂)]

/-- If `Φ` is continuous on total spaces, so is `fiberEquivConjOfAnticommute`. -/
theorem continuous_fiberEquivConjOfAnticommute
    (hc : Continuous fun p : TotalSpace F₁ V₁ ↦ TotalSpace.mk' F₂ (E := V₂) p.proj
      (Φ p.proj p.snd)) :
    Continuous fun p : TotalSpace G₁ J₁.Fiber ↦
      TotalSpace.mk' (Conjugate G₂) (E := ConjugateBundle J₂.Fiber) p.proj
        (J₁.fiberEquivConjOfAnticommute J₂ Φ hΦ p.proj p.snd) := by
  refine ((ConjugateBundle.toConjHomeomorph G₂ J₂.Fiber).continuous.comp
    ((J₂.totalSpaceHomeomorph G₂).symm.continuous.comp
    (hc.comp (J₁.totalSpaceHomeomorph G₁).continuous))).congr fun p ↦ ?_
  rw [Function.comp_apply, Function.comp_apply, Function.comp_apply, totalSpaceHomeomorph_apply,
    totalSpaceHomeomorph_symm_apply,
    ConjugateBundle.toConjHomeomorph_apply, fiberEquivConjOfAnticommute_apply]

end Anticommute

end TauCeti.Bundle.ContinuousComplexStructure
