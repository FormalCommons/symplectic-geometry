/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.Algebra.Module.ComplexSmulI
public import TauCeti.Topology.VectorBundle.Complex.Structure
public import TauCeti.Topology.VectorBundle.Conjugate
import TauCeti.Topology.FiberBundle.Pullback

/-!
# Maps of real bundles that intertwine complex structures

Let `K₁` and `K₂` be continuous complex structures on real vector bundles `U₁` over `B₁` and
`U₂` over `B₂`, `g : B₁ → B₂` a map of bases, and `Ψ b : U₁ b ≃ U₂ (g b)` real-linear
equivalences of the fibres. If `Ψ` intertwines `K₁` with `K₂`, it is a complex-linear
equivalence `K₁.Fiber b ≃ K₂.Fiber (g b)`
(`TauCeti.Bundle.ContinuousComplexStructure.fiberEquivOfCommuteAlong`). At each `b` this is the
pointwise statement: one real-linear equivalence `U₁ b₁ ≃ U₂ b₂` that intertwines `K₁ b₁` with
`K₂ b₂` is complex linear (`TauCeti.Bundle.ContinuousComplexStructure.fiberEquivOfCommuteAt`),
which also serves where such an equivalence is given only at some points. Such pointwise
equivalences `U₁ (f x) ≃ U₂ (g x)` along a continuous map `f : X → B₁` are continuous from the
total space of `f *ᵖ K₁.Fiber` when they are from that of `f *ᵖ U₁`
(`TauCeti.Bundle.ContinuousComplexStructure.continuous_fiberEquivOfCommuteAt_pullback`).

Now let `J₁` and `J₂` be continuous complex structures on real vector bundles `V₁` and `V₂` over
the same base, and `Φ x : V₁ x ≃ V₂ x` real-linear equivalences of the fibres.

* If `Φ` intertwines `J₁` with `J₂`, it is a complex-linear equivalence of the complex bundles
  `J₁.Fiber` and `J₂.Fiber` (`TauCeti.Bundle.ContinuousComplexStructure.fiberEquivOfCommute`),
  the case of `fiberEquivOfCommuteAlong` over the identity of the base.
* If `Φ` intertwines `J₁` with `-J₂`, it is a complex-linear equivalence of `J₁.Fiber` with the
  conjugate bundle of `J₂.Fiber`
  (`TauCeti.Bundle.ContinuousComplexStructure.fiberEquivConjOfAnticommute`).

When `Φ` is continuous on total spaces, so are these equivalences, for any complex models of the
two complex bundles.

In the same way, a frame of `V` along a map `f : X → B` by real-linear equivalences
`Ψ x : E ≃ V (f x)` from a complex normed space, that carries multiplication by `I` to `J`, is a
frame of the complex bundle `J.Fiber` (`TauCeti.Bundle.ContinuousComplexStructure.frameOfCommute`),
continuous when `Ψ` is. In the other direction, real-linear equivalences `e b : V b ≃ W b`
onto a family of complex vector spaces, that carry `J` to multiplication by `I`, are
complex-linear equivalences `J.Fiber b ≃ W b`
(`TauCeti.Bundle.ContinuousComplexStructure.fiberEquivOfCommuteI`), continuous when `e` is.

The trivialization of `J.Fiber` at `b₀` is read in that of `V` at `b₀`
(`TauCeti.Bundle.ContinuousComplexStructure.trivializationAt_fiberEquiv_symm_apply_snd`): over
`J.unitSet b₀`, a coordinate in `V` is sent to the inverse of `J.complexLinearPart b₀ b` applied to
it, followed by `J.modelEquiv G b₀`. For a section of `V` along a map `b : X → B` continuous at
`x`, this holds near `x` (`eventuallyEq_trivializationAt_fiberEquiv_symm_apply_snd`),
with a family of linear maps continuous at `x`
(`continuousAt_modelEquiv_symm_comp_inverse_complexLinearPart`).

## References

* J. W. Milnor and J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §14 (complex vector bundles as real bundles with a complex structure).
-/

public section

noncomputable section

open Bundle Module TauCeti.Conjugate
open scoped Topology

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

/-! ### Complex-linear maps over a map of bases -/

section CommuteAlong

variable {B₁ : Type*} [TopologicalSpace B₁] {B₂ : Type*} [TopologicalSpace B₂]
  {U₁ : B₁ → Type*} [∀ b, AddCommGroup (U₁ b)] [∀ b, Module ℝ (U₁ b)]
  [∀ b, TopologicalSpace (U₁ b)] [∀ b, IsTopologicalAddGroup (U₁ b)]
  [∀ b, ContinuousSMul ℝ (U₁ b)] [TopologicalSpace (TotalSpace F₁ U₁)]
  [FiberBundle F₁ U₁] [VectorBundle ℝ F₁ U₁]
  {U₂ : B₂ → Type*} [∀ b, AddCommGroup (U₂ b)] [∀ b, Module ℝ (U₂ b)]
  [∀ b, TopologicalSpace (U₂ b)] [∀ b, IsTopologicalAddGroup (U₂ b)]
  [∀ b, ContinuousSMul ℝ (U₂ b)] [TopologicalSpace (TotalSpace F₂ U₂)]
  [FiberBundle F₂ U₂] [VectorBundle ℝ F₂ U₂]
  (K₁ : ContinuousComplexStructure F₁ U₁) (K₂ : ContinuousComplexStructure F₂ U₂)

section At

variable {b₁ : B₁} {b₂ : B₂} (e : U₁ b₁ ≃L[ℝ] U₂ b₂) (he : ∀ v, e (K₁ b₁ v) = K₂ b₂ (e v))

/-- A real-linear equivalence `e : U₁ b₁ ≃ U₂ b₂` of two fibres that intertwines `K₁ b₁` with
`K₂ b₂`, as a complex-linear equivalence `K₁.Fiber b₁ ≃ K₂.Fiber b₂`. -/
def fiberEquivOfCommuteAt : K₁.Fiber b₁ ≃L[ℂ] K₂.Fiber b₂ :=
  ((K₁.fiberEquiv b₁).trans (e.trans (K₂.fiberEquiv b₂).symm)).complexOfMapISmul fun v ↦
    (K₂.fiberEquiv b₂).injective <| by simp [he]

theorem fiberEquivOfCommuteAt_apply (v : K₁.Fiber b₁) :
    K₁.fiberEquivOfCommuteAt K₂ e he v = (K₂.fiberEquiv b₂).symm (e (K₁.fiberEquiv b₁ v)) := by
  simp [fiberEquivOfCommuteAt]

@[simp]
theorem fiberEquiv_fiberEquivOfCommuteAt (v : K₁.Fiber b₁) :
    K₂.fiberEquiv b₂ (K₁.fiberEquivOfCommuteAt K₂ e he v) = e (K₁.fiberEquiv b₁ v) := by
  rw [fiberEquivOfCommuteAt_apply, ContinuousLinearEquiv.apply_symm_apply]

end At

variable (g : B₁ → B₂) (Ψ : ∀ b, U₁ b ≃L[ℝ] U₂ (g b)) (hΨ : ∀ b v, Ψ b (K₁ b v) = K₂ (g b) (Ψ b v))

/-- A family of real-linear equivalences `Ψ b : U₁ b ≃ U₂ (g b)` over a map `g` of bases that
intertwines `K₁` with `K₂`, as complex-linear equivalences `K₁.Fiber b ≃ K₂.Fiber (g b)`: at each
`b`, this is `fiberEquivOfCommuteAt`. Over the identity of the base this is
`fiberEquivOfCommute`. -/
def fiberEquivOfCommuteAlong (b : B₁) : K₁.Fiber b ≃L[ℂ] K₂.Fiber (g b) :=
  K₁.fiberEquivOfCommuteAt K₂ (Ψ b) (hΨ b)

theorem fiberEquivOfCommuteAlong_eq_fiberEquivOfCommuteAt (b : B₁) :
    K₁.fiberEquivOfCommuteAlong K₂ g Ψ hΨ b = K₁.fiberEquivOfCommuteAt K₂ (Ψ b) (hΨ b) :=
  (rfl)

theorem fiberEquivOfCommuteAlong_apply (b : B₁) (v : K₁.Fiber b) :
    K₁.fiberEquivOfCommuteAlong K₂ g Ψ hΨ b v =
      (K₂.fiberEquiv (g b)).symm (Ψ b (K₁.fiberEquiv b v)) := by
  rw [fiberEquivOfCommuteAlong_eq_fiberEquivOfCommuteAt, fiberEquivOfCommuteAt_apply]

@[simp]
theorem fiberEquiv_fiberEquivOfCommuteAlong (b : B₁) (v : K₁.Fiber b) :
    K₂.fiberEquiv (g b) (K₁.fiberEquivOfCommuteAlong K₂ g Ψ hΨ b v) =
      Ψ b (K₁.fiberEquiv b v) := by
  rw [fiberEquivOfCommuteAlong_eq_fiberEquivOfCommuteAt, fiberEquiv_fiberEquivOfCommuteAt]

variable {G₁ : Type*} [NormedAddCommGroup G₁] [NormedSpace ℂ G₁] [FiniteDimensional ℂ G₁]
  [FiniteDimensional ℝ F₁] [Fact (finrank ℝ F₁ = 2 * finrank ℂ G₁)]
  {G₂ : Type*} [NormedAddCommGroup G₂] [NormedSpace ℂ G₂] [FiniteDimensional ℂ G₂]
  [FiniteDimensional ℝ F₂] [Fact (finrank ℝ F₂ = 2 * finrank ℂ G₂)]

/-- If `Ψ` is continuous on total spaces, so is `fiberEquivOfCommuteAlong`. -/
theorem continuous_fiberEquivOfCommuteAlong
    (hc : Continuous fun p : TotalSpace F₁ U₁ ↦ TotalSpace.mk' F₂ (E := U₂) (g p.proj)
      (Ψ p.proj p.snd)) :
    Continuous fun p : TotalSpace G₁ K₁.Fiber ↦ TotalSpace.mk' G₂ (E := K₂.Fiber) (g p.proj)
      (K₁.fiberEquivOfCommuteAlong K₂ g Ψ hΨ p.proj p.snd) := by
  refine ((K₂.totalSpaceHomeomorph G₂).symm.continuous.comp
    (hc.comp (K₁.totalSpaceHomeomorph G₁).continuous)).congr fun p ↦ ?_
  rw [Function.comp_apply, Function.comp_apply, totalSpaceHomeomorph_apply,
    totalSpaceHomeomorph_symm_apply, fiberEquivOfCommuteAlong_apply]

/-- A family of real-linear equivalences `Ψ x : U₁ (f x) ≃ U₂ (g x)`, over a continuous map
`f : X → B₁` and a map `g : X → B₂`, that intertwines `K₁` with `K₂` and is continuous from the
total space of the pull-back `f *ᵖ U₁`: then the complex-linear equivalences
`fiberEquivOfCommuteAt` that it gives are continuous from the total space of `f *ᵖ K₁.Fiber`. -/
theorem continuous_fiberEquivOfCommuteAt_pullback {X : Type*} [TopologicalSpace X]
    {Y : Type*} [FunLike Y X B₁] [ContinuousMapClass Y X B₁] (f : Y) (g : X → B₂)
    (Ψ : ∀ x, U₁ (f x) ≃L[ℝ] U₂ (g x)) (hΨ : ∀ x v, Ψ x (K₁ (f x) v) = K₂ (g x) (Ψ x v))
    (hc : Continuous fun p : TotalSpace F₁ ((f : X → B₁) *ᵖ U₁) ↦
      TotalSpace.mk' F₂ (E := U₂) (g p.proj) (Ψ p.proj p.snd)) :
    Continuous fun p : TotalSpace G₁ ((f : X → B₁) *ᵖ K₁.Fiber) ↦
      TotalSpace.mk' G₂ (E := K₂.Fiber) (g p.proj)
        (K₁.fiberEquivOfCommuteAt K₂ (Ψ p.proj) (hΨ p.proj) p.snd) := by
  refine ((K₂.totalSpaceHomeomorph G₂).symm.continuous.comp (hc.comp
    (Pullback.continuous_fiberwise (Φ := fun b ↦ K₁.fiberEquiv b)
      ((K₁.totalSpaceHomeomorph G₁).continuous.congr (K₁.totalSpaceHomeomorph_apply G₁))
      f))).congr fun p ↦ ?_
  rw [Function.comp_apply, Function.comp_apply, totalSpaceHomeomorph_symm_apply]
  exact congrArg (TotalSpace.mk' G₂ (g p.proj))
    (K₁.fiberEquivOfCommuteAt_apply K₂ (Ψ p.proj) (hΨ p.proj) p.snd).symm

end CommuteAlong

/-! ### Complex-linear maps -/

section Commute

variable (hΦ : ∀ b v, Φ b (J₁ b v) = J₂ b (Φ b v))

/-- A family of real-linear equivalences `Φ` that intertwines `J₁` with `J₂`, as complex-linear
equivalences `J₁.Fiber b ≃ J₂.Fiber b`: `fiberEquivOfCommuteAlong` over the identity of `B`. -/
def fiberEquivOfCommute (b : B) : J₁.Fiber b ≃L[ℂ] J₂.Fiber b :=
  J₁.fiberEquivOfCommuteAlong J₂ id Φ hΦ b

theorem fiberEquivOfCommute_eq_fiberEquivOfCommuteAlong (b : B) :
    J₁.fiberEquivOfCommute J₂ Φ hΦ b = J₁.fiberEquivOfCommuteAlong J₂ id Φ hΦ b :=
  (rfl)

theorem fiberEquivOfCommute_apply (b : B) (v : J₁.Fiber b) :
    J₁.fiberEquivOfCommute J₂ Φ hΦ b v = (J₂.fiberEquiv b).symm (Φ b (J₁.fiberEquiv b v)) := by
  rw [fiberEquivOfCommute_eq_fiberEquivOfCommuteAlong, fiberEquivOfCommuteAlong_apply]
  -- The base point `id b` reduces to `b`.
  rfl

@[simp]
theorem fiberEquiv_fiberEquivOfCommute (b : B) (v : J₁.Fiber b) :
    J₂.fiberEquiv b (J₁.fiberEquivOfCommute J₂ Φ hΦ b v) = Φ b (J₁.fiberEquiv b v) := by
  rw [fiberEquivOfCommute_eq_fiberEquivOfCommuteAlong]
  exact J₁.fiberEquiv_fiberEquivOfCommuteAlong J₂ id Φ hΦ b v

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
  simp_rw [fiberEquivOfCommute_eq_fiberEquivOfCommuteAlong]
  exact J₁.continuous_fiberEquivOfCommuteAlong J₂ id Φ hΦ hc

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

/-! ### Complex frames from real frames -/

section Frame

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [∀ b, AddCommGroup (V b)] [∀ b, Module ℝ (V b)] [∀ b, TopologicalSpace (V b)]
  [∀ b, IsTopologicalAddGroup (V b)] [∀ b, ContinuousSMul ℝ (V b)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  (J : ContinuousComplexStructure F V)
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {X : Type*} {f : X → B}
  (Ψ : ∀ x, E ≃L[ℝ] V (f x)) (hΨ : ∀ x v, Ψ x (Complex.I • v) = J (f x) (Ψ x v))

/-- A frame of `V` along `f : X → B` by real-linear equivalences `Ψ x : E ≃ V (f x)` from a
complex normed space, that carries multiplication by `I` to `J`, as a frame of the complex bundle
`J.Fiber` by complex-linear equivalences `E ≃ J.Fiber (f x)`. -/
def frameOfCommute (x : X) : E ≃L[ℂ] J.Fiber (f x) :=
  ((Ψ x).trans (J.fiberEquiv (f x)).symm).complexOfMapISmul fun v ↦
    (J.fiberEquiv (f x)).injective <| by simp [hΨ]

theorem frameOfCommute_apply (x : X) (v : E) :
    J.frameOfCommute Ψ hΨ x v = (J.fiberEquiv (f x)).symm (Ψ x v) := by
  simp [frameOfCommute]

@[simp]
theorem fiberEquiv_frameOfCommute (x : X) (v : E) :
    J.fiberEquiv (f x) (J.frameOfCommute Ψ hΨ x v) = Ψ x v := by
  rw [frameOfCommute_apply, ContinuousLinearEquiv.apply_symm_apply]

variable (G : Type*) [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  [FiniteDimensional ℝ F] [Fact (finrank ℝ F = 2 * finrank ℂ G)]

/-- If the real frame `Ψ` is continuous as a map to the total space of `V`, the complex frame
`J.frameOfCommute Ψ hΨ` is continuous as a map to the total space of `J.Fiber`, for any complex
model `G` of `J.Fiber`. -/
theorem continuous_frameOfCommute [TopologicalSpace X]
    (hc : Continuous fun q : X × E ↦ TotalSpace.mk' F (f q.1) (Ψ q.1 q.2)) :
    Continuous fun q : X × E ↦ TotalSpace.mk' G (E := J.Fiber) (f q.1)
      (J.frameOfCommute Ψ hΨ q.1 q.2) := by
  refine ((J.totalSpaceHomeomorph G).symm.continuous.comp hc).congr fun q ↦ ?_
  rw [Function.comp_apply, totalSpaceHomeomorph_symm_apply, frameOfCommute_apply]

end Frame

/-! ### Complex-linear maps into bundles of complex vector spaces -/

section ToComplex

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [∀ b, AddCommGroup (V b)] [∀ b, Module ℝ (V b)] [∀ b, TopologicalSpace (V b)]
  [∀ b, IsTopologicalAddGroup (V b)] [∀ b, ContinuousSMul ℝ (V b)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  (J : ContinuousComplexStructure F V)
  {W : B → Type*} [∀ b, AddCommGroup (W b)] [∀ b, Module ℝ (W b)] [∀ b, Module ℂ (W b)]
  [∀ b, IsScalarTower ℝ ℂ (W b)] [∀ b, TopologicalSpace (W b)]
  (e : ∀ b, V b ≃L[ℝ] W b) (he : ∀ b v, e b (J b v) = Complex.I • e b v)

/-- Real-linear equivalences `e b : V b ≃ W b` onto the fibres of a family of complex vector
spaces, that carry `J` to multiplication by `I`, as complex-linear equivalences
`J.Fiber b ≃ W b`. -/
def fiberEquivOfCommuteI (b : B) : J.Fiber b ≃L[ℂ] W b :=
  ((J.fiberEquiv b).trans (e b)).complexOfMapISmul fun v ↦ by
    rw [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.trans_apply, fiberEquiv_I_smul,
      he]

@[simp]
theorem fiberEquivOfCommuteI_apply (b : B) (v : J.Fiber b) :
    J.fiberEquivOfCommuteI e he b v = e b (J.fiberEquiv b v) := by
  simp [fiberEquivOfCommuteI]

variable (G : Type*) [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  [FiniteDimensional ℝ F] [Fact (finrank ℝ F = 2 * finrank ℂ G)]
  {F' : Type*} [TopologicalSpace (TotalSpace F' W)]

/-- If `e` is continuous on total spaces, so is `fiberEquivOfCommuteI`, for any complex model `G`
of `J.Fiber`. -/
theorem continuous_fiberEquivOfCommuteI
    (hc : Continuous fun p : TotalSpace F V ↦ TotalSpace.mk' F' p.proj (e p.proj p.snd)) :
    Continuous fun p : TotalSpace G J.Fiber ↦
      TotalSpace.mk' F' p.proj (J.fiberEquivOfCommuteI e he p.proj p.snd) := by
  refine (hc.comp (J.totalSpaceHomeomorph G).continuous).congr fun p ↦ ?_
  rw [Function.comp_apply, totalSpaceHomeomorph_apply, fiberEquivOfCommuteI_apply]

end ToComplex

/-! ### The trivializations of `J.Fiber` -/

section Trivialization

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [∀ b, AddCommGroup (V b)] [∀ b, Module ℝ (V b)] [∀ b, TopologicalSpace (V b)]
  [∀ b, IsTopologicalAddGroup (V b)] [∀ b, ContinuousSMul ℝ (V b)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  (J : ContinuousComplexStructure F V)
  (G : Type*) [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  [FiniteDimensional ℝ F] [Fact (finrank ℝ F = 2 * finrank ℂ G)]

/-- **The trivialization of `J.Fiber` at `b₀`, in the trivialization of `V`.** Over the open set
`J.unitSet b₀`, the coordinate of a vector in the trivialization of `J.Fiber` at `b₀` is obtained
from its coordinate in the trivialization of `V` at `b₀` by the inverse of
`J.complexLinearPart b₀ b`, followed by the identification `J.modelEquiv G b₀` of `F` with `G`. -/
theorem trivializationAt_fiberEquiv_symm_apply_snd {b₀ b : B} (hb : b ∈ J.unitSet b₀)
    (v : V b) :
    (trivializationAt G J.Fiber b₀ ⟨b, (J.fiberEquiv b).symm v⟩).2 =
      (J.modelEquiv G b₀).symm (Ring.inverse (J.complexLinearPart b₀ b)
        (trivializationAt F V b₀ ⟨b, v⟩).2) := by
  have hb' : b ∈ (trivializationAt F V b₀).baseSet := J.unitSet_subset b₀ hb
  have hbe : b ∈ (trivializationAt G J.Fiber b₀).baseSet := by
    rwa [baseSet_trivializationAt]
  set w := (trivializationAt G J.Fiber b₀ ⟨b, (J.fiberEquiv b).symm v⟩).2
  have h₁ : (trivializationAt G J.Fiber b₀).symm b w = (J.fiberEquiv b).symm v :=
    (trivializationAt G J.Fiber b₀).symm_apply_apply_mk hbe _
  have h₂ := J.trivializationAt_symm_apply G hb w
  rw [h₁, ContinuousLinearEquiv.apply_symm_apply] at h₂
  rw [h₂, (trivializationAt F V b₀).apply_mk_symm hb',
    J.inverse_complexLinearPart_complexLinearPart_apply hb, ContinuousLinearEquiv.symm_apply_apply]

variable {X : Type*} [TopologicalSpace X] {b : X → B} {s : ∀ y, V (b y)} {x : X}

/-- Over `J.unitSet (b x)`, hence near `x` when `b` is continuous at `x`, the section
`y ↦ (J.fiberEquiv (b y)).symm (s y)` of `J.Fiber` read in the trivialization of `J.Fiber` at
`b x` is the reading of `s` in the trivialization of `V` at `b x` followed by the inverse of
`J.complexLinearPart (b x) (b y)` and by `(J.modelEquiv G (b x)).symm`. -/
theorem eventuallyEq_trivializationAt_fiberEquiv_symm_apply_snd (hb : ContinuousAt b x) :
    (fun y ↦ (((J.modelEquiv G (b x)).symm : F →L[ℝ] G).comp
        (Ring.inverse (J.complexLinearPart (b x) (b y)))) (trivializationAt F V (b x) ⟨b y, s y⟩).2)
      =ᶠ[𝓝 x]
        fun y ↦ (trivializationAt G J.Fiber (b x) ⟨b y, (J.fiberEquiv (b y)).symm (s y)⟩).2 := by
  have := FiniteDimensional.completeSpace ℝ F
  filter_upwards [hb.preimage_mem_nhds
    ((J.isOpen_unitSet (b x)).mem_nhds (J.mem_unitSet_self _))] with y hy
  exact (J.trivializationAt_fiberEquiv_symm_apply_snd G hy (s y)).symm

/-- If `b` is continuous at `x`, the family of linear maps
`y ↦ (J.modelEquiv G (b x)).symm ∘ (J.complexLinearPart (b x) (b y))⁻¹`, that of
`eventuallyEq_trivializationAt_fiberEquiv_symm_apply_snd`, is continuous at `x`. -/
theorem continuousAt_modelEquiv_symm_comp_inverse_complexLinearPart
    (hb : ContinuousAt b x) :
    ContinuousAt (fun y ↦ ((J.modelEquiv G (b x)).symm : F →L[ℝ] G).comp
      (Ring.inverse (J.complexLinearPart (b x) (b y)))) x := by
  have := FiniteDimensional.completeSpace ℝ F
  exact continuousAt_const.clm_comp (((J.continuousOn_inverse_complexLinearPart (b x)).continuousAt
    ((J.isOpen_unitSet (b x)).mem_nhds (J.mem_unitSet_self _))).comp hb)

end Trivialization

end TauCeti.Bundle.ContinuousComplexStructure
