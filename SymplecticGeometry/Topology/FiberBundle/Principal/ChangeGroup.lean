/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import SymplecticGeometry.Topology.FiberBundle.ChangeModelFiber
public import TauCeti.Topology.FiberBundle.Principal.Basic

/-!
# Change of structure group of a principal bundle

Let `P` be a principal `G`-bundle in the sense of `TauCeti.PrincipalBundle`, and let
`e : G ≃ₜ* H` be an isomorphism of topological groups. Then the same fibres `P b` form a
principal `H`-bundle, `H` acting on the right through `e.symm` and the trivializations being those
of `P` followed by `e` on the fibre coordinate (`FiberBundle.changeModelFiber`).

Since `e` is data, neither the right action of `Hᵐᵒᵖ` on the fibres nor the topology on
`TotalSpace H P` can be global instances. They are taken as instance arguments, with hypotheses
saying how they are related to the `G`-structure:

* the topology on `TotalSpace H P` makes the identification
  `Bundle.TotalSpace.modelFiberEquiv G H P : TotalSpace H P ≃ TotalSpace G P`,
  `p ↦ ⟨p.proj, p.snd⟩`, an inducing map; this holds by `⟨rfl⟩` for the induced topology;
* the action satisfies `op h • p = op (e.symm h) • p`; this holds by `rfl` for the action
  `MulAction.compHom` along `e.symm`.

## Main results

* `Bundle.Trivialization.isEquivariant_changeModelFiber`: an equivariant trivialization stays
  equivariant after changing the group.
* `TauCeti.PrincipalBundle.changeGroup`: the change of structure group of a principal bundle along
  an isomorphism of topological groups.
* `TauCeti.PrincipalBundle.division_changeGroup`: the division map of the new bundle is the image
  under `e` of the division map of `P`.

## References

* D. Husemoller, *Fibre Bundles*, 3rd ed., Graduate Texts in Mathematics 20, Springer, 1994,
  Chapter 4 (principal bundles and morphisms between them).
* S. Kobayashi, K. Nomizu, *Foundations of Differential Geometry I*, Interscience, 1963,
  Chapter I, §5 (homomorphisms of principal bundles and reduction of the structure group).
-/

public section

open Bundle MulOpposite Topology

namespace Bundle.Trivialization

variable {B G H : Type*} [TopologicalSpace B] [Group G] [TopologicalSpace G] [Group H]
  [TopologicalSpace H] {P : B → Type*} [TopologicalSpace (TotalSpace G P)]
  [TopologicalSpace (TotalSpace H P)] [∀ b, MulAction Gᵐᵒᵖ (P b)] [∀ b, MulAction Hᵐᵒᵖ (P b)]

/-- Changing the group along an isomorphism `e : G ≃ₜ* H` keeps a trivialization equivariant,
when `H` acts on the fibres through `e.symm`. -/
theorem isEquivariant_changeModelFiber (t : Trivialization G (π G P)) [t.IsEquivariant]
    (e : G ≃ₜ* H) (h : IsInducing (TotalSpace.modelFiberEquiv G H P))
    (hact : ∀ b (p : P b) (g : H), op g • p = op (e.symm g) • p) :
    (t.changeModelFiber (e : G ≃ₜ H) h).IsEquivariant :=
  ⟨fun b hb p g ↦ by
    rw [baseSet_changeModelFiber] at hb
    simp [hact, t.snd_apply_smul hb]⟩

end Bundle.Trivialization

namespace TauCeti.PrincipalBundle

variable {B G H : Type*} [TopologicalSpace B] [Group G] [TopologicalSpace G] [Group H]
  [TopologicalSpace H] {P : B → Type*} [TopologicalSpace (TotalSpace G P)]
  [TopologicalSpace (TotalSpace H P)] [∀ b, TopologicalSpace (P b)] [FiberBundle G P]
  [∀ b, MulAction Gᵐᵒᵖ (P b)] [∀ b, MulAction Hᵐᵒᵖ (P b)]

/-- **Change of structure group.** A principal `G`-bundle `P` is a principal `H`-bundle for an
isomorphism of topological groups `e : G ≃ₜ* H`, when `H` acts on the fibres through `e.symm` and
the total space with model fibre `H` carries the topology induced from the one with model
fibre `G`. Its fibre-bundle structure is `FiberBundle.changeModelFiber (e : G ≃ₜ H) h`. -/
theorem changeGroup [PrincipalBundle G P] (e : G ≃ₜ* H)
    (h : IsInducing (TotalSpace.modelFiberEquiv G H P))
    (hact : ∀ b (p : P b) (g : H), op g • p = op (e.symm g) • p) :
    letI := FiberBundle.changeModelFiber (e : G ≃ₜ H) h
    PrincipalBundle H P :=
  letI := FiberBundle.changeModelFiber (e : G ≃ₜ H) h
  ⟨fun t' ht' ↦ by
    obtain ⟨t, _, rfl⟩ :=
      FiberBundle.exists_eq_changeModelFiber_of_memTrivializationAtlas (e : G ≃ₜ H) h t' ht'
    exact t.isEquivariant_changeModelFiber e h hact⟩

/-- The division map of the principal `H`-bundle `TauCeti.PrincipalBundle.changeGroup e h hact`
is the image under `e` of the division map of `P`. -/
theorem division_changeGroup [PrincipalBundle G P] (e : G ≃ₜ* H)
    (h : IsInducing (TotalSpace.modelFiberEquiv G H P))
    (hact : ∀ b (p : P b) (g : H), op g • p = op (e.symm g) • p) {b : B} (p q : P b) :
    letI := FiberBundle.changeModelFiber (e : G ≃ₜ H) h
    haveI := changeGroup e h hact
    division H p q = e (division G p q) :=
  letI := FiberBundle.changeModelFiber (e : G ≃ₜ H) h
  haveI := changeGroup e h hact
  division_eq_iff.2 (by rw [hact, ContinuousMulEquiv.symm_apply_apply, smul_division])

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
    letI := FiberBundle.changeModelFiber (E := P) (e : G ≃ₜ H) ⟨rfl⟩
    TauCeti.PrincipalBundle H P :=
  letI : TopologicalSpace (TotalSpace H P) :=
    .induced (TotalSpace.modelFiberEquiv G H P) inferInstance
  letI (b : B) : MulAction Hᵐᵒᵖ (P b) :=
    MulAction.compHom _ (MulEquiv.op e.symm.toMulEquiv).toMonoidHom
  TauCeti.PrincipalBundle.changeGroup e ⟨rfl⟩ fun _ _ _ ↦ rfl

end Example

end
