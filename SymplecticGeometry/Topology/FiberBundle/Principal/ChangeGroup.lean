/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import TauCeti.Topology.FiberBundle.Principal.Basic

/-!
# Change of structure group of a principal bundle

Let `P` be a principal `G`-bundle in the sense of `TauCeti.PrincipalBundle`, and let
`e : G ≃ₜ* H` be an isomorphism of topological groups. Then the same fibres `P b` form a
principal `H`-bundle, `H` acting on the right through `e.symm` and the trivializations being those
of `P` followed by `e` on the fibre coordinate.

Since `e` is data, neither the right action of `Hᵐᵒᵖ` on the fibres nor the topology on
`TotalSpace H P` can be global instances. They are taken as instance arguments, with hypotheses
saying how they are related to the `G`-structure:

* the topology on `TotalSpace H P` makes the identification
  `Bundle.TotalSpace.modelFiberEquiv G H P : TotalSpace H P ≃ TotalSpace G P`,
  `p ↦ ⟨p.proj, p.snd⟩`, an inducing map; this holds by `⟨rfl⟩` for the induced topology;
* the action satisfies `op h • p = op (e.symm h) • p`; this holds by `rfl` for the action
  `MulAction.compHom` along `e.symm`.

The construction of the trivializations and of the fibre bundle uses only the homeomorphism of
model fibres, so it is stated for any homeomorphism `e : F ≃ₜ F'`; equivariance and the
principal-bundle structure then need a group isomorphism.

## Main definitions

* `Bundle.TotalSpace.modelFiberEquiv`, `Bundle.TotalSpace.modelFiberHomeomorph`: the total space
  of `E` read with model fibre `F'` is the total space with model fibre `F`.
* `Bundle.Trivialization.changeModelFiber`: a trivialization with fibre `F`, read with fibre `F'`
  through a homeomorphism `F ≃ₜ F'`.
* `FiberBundle.changeModelFiber`: a fibre bundle with fibre `F` is a fibre bundle with fibre `F'`,
  its atlas being the image of the atlas with fibre `F`.

## Main results

* `Bundle.Trivialization.isEquivariant_changeModelFiber`: an equivariant trivialization stays
  equivariant after changing the group.
* `TauCeti.PrincipalBundle.changeGroup`: the change of structure group of a principal bundle along
  an isomorphism of topological groups.

## References

* D. Husemoller, *Fibre Bundles*, 3rd ed., Graduate Texts in Mathematics 20, Springer, 1994,
  Chapter 4 (principal bundles and morphisms between them).
* S. Kobayashi, K. Nomizu, *Foundations of Differential Geometry I*, Interscience, 1963,
  Chapter I, §5 (homomorphisms of principal bundles and reduction of the structure group).
-/

public section

open Bundle MulOpposite Topology

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

@[simp]
theorem proj_modelFiberEquiv (p : TotalSpace F' E) : (modelFiberEquiv F F' E p).proj = p.proj :=
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
      (TotalSpace.modelFiberEquiv F F' E).symm (t.toOpenPartialHomeomorph.symm (q.1, e.symm q.2)) :=
  (rfl)

@[simp]
theorem baseSet_changeModelFiber : (t.changeModelFiber e h).baseSet = t.baseSet :=
  (rfl)

/-- Changing the group along an isomorphism `e : G ≃ₜ* H` keeps a trivialization equivariant,
when `H` acts on the fibres through `e.symm`. -/
theorem isEquivariant_changeModelFiber {G H : Type*} [Group G] [TopologicalSpace G] [Group H]
    [TopologicalSpace H] {P : B → Type*} [TopologicalSpace (TotalSpace G P)]
    [TopologicalSpace (TotalSpace H P)] [∀ b, MulAction Gᵐᵒᵖ (P b)] [∀ b, MulAction Hᵐᵒᵖ (P b)]
    (t : Trivialization G (π G P)) [t.IsEquivariant] (e : G ≃ₜ* H)
    (h : IsInducing (TotalSpace.modelFiberEquiv G H P))
    (hact : ∀ b (p : P b) (g : H), op g • p = op (e.symm g) • p) :
    (t.changeModelFiber e.toHomeomorph h).IsEquivariant :=
  ⟨fun b hb p g ↦ by
    simp only [changeModelFiber_apply]
    change e _ = e _ * g
    rw [hact, t.snd_apply_smul hb, map_mul, ContinuousMulEquiv.apply_symm_apply]⟩

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
@[expose, implicit_reducible]
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

theorem trivializationAt_changeModelFiber (b : B) :
    letI := changeModelFiber e h
    trivializationAt F' E b = (trivializationAt F E b).changeModelFiber e h :=
  rfl

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

/-! ### Principal bundles with another structure group -/

namespace TauCeti.PrincipalBundle

variable {B G H : Type*} [TopologicalSpace B] [Group G] [TopologicalSpace G] [Group H]
  [TopologicalSpace H] {P : B → Type*} [TopologicalSpace (TotalSpace G P)]
  [TopologicalSpace (TotalSpace H P)] [∀ b, TopologicalSpace (P b)] [FiberBundle G P]
  [∀ b, MulAction Gᵐᵒᵖ (P b)] [∀ b, MulAction Hᵐᵒᵖ (P b)]

/-- **Change of structure group.** A principal `G`-bundle `P` is a principal `H`-bundle for an
isomorphism of topological groups `e : G ≃ₜ* H`, when `H` acts on the fibres through `e.symm` and
the total space with model fibre `H` carries the topology induced from the one with model
fibre `G`. Its fibre-bundle structure is `FiberBundle.changeModelFiber e.toHomeomorph h`. -/
theorem changeGroup [PrincipalBundle G P] (e : G ≃ₜ* H)
    (h : IsInducing (TotalSpace.modelFiberEquiv G H P))
    (hact : ∀ b (p : P b) (g : H), op g • p = op (e.symm g) • p) :
    letI := FiberBundle.changeModelFiber e.toHomeomorph h
    PrincipalBundle H P :=
  letI := FiberBundle.changeModelFiber e.toHomeomorph h
  ⟨fun t' ht' ↦ by
    obtain ⟨t, _, rfl⟩ :=
      FiberBundle.exists_eq_changeModelFiber_of_memTrivializationAtlas e.toHomeomorph h t' ht'
    exact t.isEquivariant_changeModelFiber e h hact⟩

end TauCeti.PrincipalBundle

/-! ### Example: the induced topology and the action through `e.symm` -/

section Example

variable {B G H : Type*} [TopologicalSpace B] [Group G] [TopologicalSpace G] [Group H]
  [TopologicalSpace H] {P : B → Type*} [TopologicalSpace (TotalSpace G P)]
  [∀ b, TopologicalSpace (P b)] [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)]
  [TauCeti.PrincipalBundle G P]

/-- The hypotheses of `TauCeti.PrincipalBundle.changeGroup` hold, by `rfl`, for the topology
induced along `Bundle.TotalSpace.modelFiberEquiv` and the action through `e.symm`. -/
example (e : G ≃ₜ* H) :
    letI : TopologicalSpace (TotalSpace H P) :=
      .induced (TotalSpace.modelFiberEquiv G H P) inferInstance
    letI (b : B) : MulAction Hᵐᵒᵖ (P b) :=
      MulAction.compHom _ (MulEquiv.op e.symm.toMulEquiv).toMonoidHom
    letI := FiberBundle.changeModelFiber (E := P) e.toHomeomorph ⟨rfl⟩
    TauCeti.PrincipalBundle H P :=
  letI : TopologicalSpace (TotalSpace H P) :=
    .induced (TotalSpace.modelFiberEquiv G H P) inferInstance
  letI (b : B) : MulAction Hᵐᵒᵖ (P b) :=
    MulAction.compHom _ (MulEquiv.op e.symm.toMulEquiv).toMonoidHom
  TauCeti.PrincipalBundle.changeGroup e ⟨rfl⟩ fun _ _ _ ↦ rfl

end Example
