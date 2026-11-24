/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.FiberBundle.Basic

/-!
# Changing the model fibre of a fibre bundle

A fibre bundle `E` with model fibre `F` is also a fibre bundle with model fibre `F'`, for any
homeomorphism `e : F ≃ₜ F'`: its trivializations are those of `E` followed by `e` on the fibre
coordinate. The total spaces `TotalSpace F E` and `TotalSpace F' E` have the same points. The
topology on the second is an instance argument, with the hypothesis that the identification
`Bundle.TotalSpace.modelFiberEquiv F F' E` is inducing, which holds by `⟨rfl⟩` for the induced
topology. Since `e` is data, the resulting fibre-bundle structure is a definition, not an
instance.

## Main definitions and results

* `Bundle.TotalSpace.modelFiberEquiv`, `Bundle.TotalSpace.modelFiberHomeomorph`: the total space
  of `E` read with model fibre `F'` is the total space with model fibre `F`.
* `Bundle.Trivialization.changeModelFiber`: a trivialization with fibre `F`, read with fibre `F'`
  through a homeomorphism `F ≃ₜ F'`.
* `Bundle.Trivialization.transFiberHomeomorph_baseSet`, `_source`, `_target`, `_symm_apply`: the
  base set, source, target and inverse of Mathlib's `Bundle.Trivialization.transFiberHomeomorph`,
  which composes a trivialization with a homeomorphism of the model fibre.
* `Bundle.Trivialization.compHomeomorph_apply`, `_baseSet`, `_source`, `_target`, `_symm_apply`:
  the map, base set, source, target and inverse of Mathlib's
  `Bundle.Trivialization.compHomeomorph`, which precomposes a trivialization with a homeomorphism
  of the total space.
* `FiberBundle.changeModelFiber`: a fibre bundle with fibre `F` is a fibre bundle with fibre `F'`,
  its atlas being the image of the atlas with fibre `F`.

## References

* D. Husemoller, *Fibre Bundles*, 3rd ed., Graduate Texts in Mathematics 20, Springer, 1994,
  Chapter 4 (principal bundles and morphisms between them).
* S. Kobayashi, K. Nomizu, *Foundations of Differential Geometry I*, Interscience, 1963,
  Chapter I, §5 (homomorphisms of principal bundles and reduction of the structure group).
-/

public section

open Bundle Topology

/-! ### The total space with another model fibre -/

namespace Bundle.TotalSpace

variable {B : Type*} (F F' : Type*) (E : B → Type*)

/-- The total space of `E` with model fibre `F'` is the total space of `E` with model fibre `F`:
both consist of a point of the base and a point of its fibre. -/
def modelFiberEquiv : TotalSpace F' E ≃ TotalSpace F E where
  toFun p := ⟨p.proj, p.snd⟩
  invFun p := ⟨p.proj, p.snd⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable {F F' E}

@[simp]
theorem modelFiberEquiv_apply (p : TotalSpace F' E) :
    modelFiberEquiv F F' E p = ⟨p.proj, p.snd⟩ :=
  (rfl)

@[simp]
theorem modelFiberEquiv_symm_apply (p : TotalSpace F E) :
    (modelFiberEquiv F F' E).symm p = ⟨p.proj, p.snd⟩ :=
  (rfl)

variable [TopologicalSpace (TotalSpace F E)] [TopologicalSpace (TotalSpace F' E)]

/-- `Bundle.TotalSpace.modelFiberEquiv` as a homeomorphism, when the topology on the total space
with model fibre `F'` is induced from the one with model fibre `F`. -/
def modelFiberHomeomorph (h : IsInducing (modelFiberEquiv F F' E)) :
    TotalSpace F' E ≃ₜ TotalSpace F E :=
  (modelFiberEquiv F F' E).toHomeomorphOfIsInducing h

@[simp]
theorem coe_modelFiberHomeomorph (h : IsInducing (modelFiberEquiv F F' E)) :
    ⇑(modelFiberHomeomorph h) = modelFiberEquiv F F' E :=
  (rfl)

@[simp]
theorem coe_modelFiberHomeomorph_symm (h : IsInducing (modelFiberEquiv F F' E)) :
    ⇑(modelFiberHomeomorph h).symm = (modelFiberEquiv F F' E).symm :=
  (rfl)

end Bundle.TotalSpace

/-! ### Trivializations with another model fibre -/

namespace Bundle.Trivialization

section transFiberHomeomorph

variable {B F F' Z : Type*} [TopologicalSpace B] [TopologicalSpace F] [TopologicalSpace F']
  [TopologicalSpace Z] {proj : Z → B} (e : Trivialization F proj) (h : F ≃ₜ F')

@[simp]
theorem transFiberHomeomorph_baseSet : (e.transFiberHomeomorph h).baseSet = e.baseSet :=
  (rfl)

@[simp]
theorem transFiberHomeomorph_source : (e.transFiberHomeomorph h).source = e.source :=
  (rfl)

@[simp]
theorem transFiberHomeomorph_target :
    (e.transFiberHomeomorph h).target = e.baseSet ×ˢ Set.univ := by
  rw [target_eq, transFiberHomeomorph_baseSet]

/-- The inverse of `e.transFiberHomeomorph h` sends `q` to the image of `(q.1, h.symm q.2)`
under the inverse of `e`. -/
@[simp]
theorem transFiberHomeomorph_symm_apply (q : B × F') :
    (e.transFiberHomeomorph h).toOpenPartialHomeomorph.symm q =
      e.toOpenPartialHomeomorph.symm (q.1, h.symm q.2) :=
  (rfl)

end transFiberHomeomorph

section compHomeomorph

variable {B F Z Z' : Type*} [TopologicalSpace B] [TopologicalSpace F] [TopologicalSpace Z]
  [TopologicalSpace Z'] {proj : Z → B} (e : Trivialization F proj) (h : Z' ≃ₜ Z)

@[simp]
theorem compHomeomorph_apply (x : Z') : e.compHomeomorph h x = e (h x) :=
  (rfl)

@[simp]
theorem compHomeomorph_baseSet : (e.compHomeomorph h).baseSet = e.baseSet :=
  (rfl)

@[simp]
theorem compHomeomorph_source : (e.compHomeomorph h).source = h ⁻¹' e.source :=
  (rfl)

@[simp]
theorem compHomeomorph_target : (e.compHomeomorph h).target = e.target :=
  (rfl)

/-- The inverse of `e.compHomeomorph h` sends `x` to the image under `h.symm` of the image of `x`
under the inverse of `e`. -/
@[simp]
theorem compHomeomorph_symm_apply (x : B × F) :
    (e.compHomeomorph h).toOpenPartialHomeomorph.symm x =
      h.symm (e.toOpenPartialHomeomorph.symm x) :=
  (rfl)

end compHomeomorph

variable {B F F' : Type*} [TopologicalSpace B] [TopologicalSpace F] [TopologicalSpace F']
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [TopologicalSpace (TotalSpace F' E)]

/-- A trivialization of `E` with model fibre `F`, read with model fibre `F'` through a
homeomorphism `e : F ≃ₜ F'`: it sends `p` to `(b, e v)` where `(b, v)` is its image under `t`. -/
def changeModelFiber (t : Trivialization F (π F E)) (e : F ≃ₜ F')
    (h : IsInducing (TotalSpace.modelFiberEquiv F F' E)) : Trivialization F' (π F' E) :=
  (t.compHomeomorph (TotalSpace.modelFiberHomeomorph h)).transFiberHomeomorph e

variable (t : Trivialization F (π F E)) (e : F ≃ₜ F')
  (h : IsInducing (TotalSpace.modelFiberEquiv F F' E))

@[simp]
theorem changeModelFiber_apply (p : TotalSpace F' E) :
    t.changeModelFiber e h p = ((t ⟨p.proj, p.snd⟩).1, e (t ⟨p.proj, p.snd⟩).2) :=
  (rfl)

@[simp]
theorem changeModelFiber_symm_apply (q : B × F') :
    (t.changeModelFiber e h).toOpenPartialHomeomorph.symm q =
      (TotalSpace.modelFiberEquiv F F' E).symm
        (t.toOpenPartialHomeomorph.symm (q.1, e.symm q.2)) := by
  rw [changeModelFiber, transFiberHomeomorph_symm_apply, compHomeomorph_symm_apply,
    TotalSpace.coe_modelFiberHomeomorph_symm]

@[simp]
theorem baseSet_changeModelFiber : (t.changeModelFiber e h).baseSet = t.baseSet := by
  rw [changeModelFiber, transFiberHomeomorph_baseSet, compHomeomorph_baseSet]

end Bundle.Trivialization

/-! ### Fibre bundles with another model fibre -/

namespace FiberBundle

variable {B F F' : Type*} [TopologicalSpace B] [TopologicalSpace F] [TopologicalSpace F']
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [TopologicalSpace (TotalSpace F' E)]
  [∀ b, TopologicalSpace (E b)] [FiberBundle F E] (e : F ≃ₜ F')
  (h : IsInducing (TotalSpace.modelFiberEquiv F F' E))

/-- A fibre bundle with model fibre `F` is a fibre bundle with model fibre `F'`, for a
homeomorphism `e : F ≃ₜ F'` and the topology on the total space induced from the one with model
fibre `F`. Its atlas consists of the trivializations of the atlas of `E` read through `e`
(`Bundle.Trivialization.changeModelFiber`). This is a definition, not an instance, since `e` is
data. -/
@[implicit_reducible]
def changeModelFiber : FiberBundle F' E where
  totalSpaceMk_isInducing' b := by
    have hb := (TotalSpace.modelFiberHomeomorph h).symm.isInducing.comp
      (totalSpaceMk_isInducing F E b)
    rwa [TotalSpace.coe_modelFiberHomeomorph_symm] at hb
  trivializationAtlas' :=
    {t' | ∃ (t : Trivialization F (π F E)) (_ : MemTrivializationAtlas t),
      t' = t.changeModelFiber e h}
  trivializationAt' b := (trivializationAt F E b).changeModelFiber e h
  mem_baseSet_trivializationAt' b := by
    rw [Trivialization.baseSet_changeModelFiber]
    exact mem_baseSet_trivializationAt F E b
  trivialization_mem_atlas' b := ⟨_, inferInstance, rfl⟩

/-- The trivialization at `b` of `FiberBundle.changeModelFiber e h` is the trivialization at `b`
of `E` read through `e`. -/
@[simp]
theorem trivializationAt_changeModelFiber (b : B) :
    letI := changeModelFiber e h
    trivializationAt F' E b = (trivializationAt F E b).changeModelFiber e h :=
  (rfl)

/-- The trivializations of the atlas of `E`, read through `e`, are in the atlas of
`FiberBundle.changeModelFiber e h`. -/
theorem memTrivializationAtlas_changeModelFiber (t : Trivialization F (π F E))
    [MemTrivializationAtlas t] :
    letI := changeModelFiber e h
    MemTrivializationAtlas (t.changeModelFiber e h) :=
  letI := changeModelFiber e h
  ⟨⟨t, inferInstance, rfl⟩⟩

/-- Every trivialization of the atlas of `FiberBundle.changeModelFiber e h` is a trivialization of
the atlas of `E` read through `e`. -/
theorem exists_eq_changeModelFiber_of_memTrivializationAtlas
    (t' : Trivialization F' (π F' E))
    (ht' : letI := changeModelFiber e h; MemTrivializationAtlas t') :
    ∃ (t : Trivialization F (π F E)) (_ : MemTrivializationAtlas t),
      t' = t.changeModelFiber e h :=
  ht'.out

end FiberBundle

end
