/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Algebra.Constructions
public import TauCeti.Topology.Algebra.GroupAction.OrbitTrivialization
public import TauCeti.Topology.FiberBundle.Principal.Basic
public import SymplecticGeometry.Topology.Algebra.ProperAction.Free

/-!
# The principal bundle of a free proper action

Let a group `H` act on a space `X`. The orbit projection `X → X ⧸ H` is a family of types over the
orbit space, `orbitFiber H X`, whose fibre over an orbit `q` is the subtype of the points of `q`.
This file gives that family the structure the topological principal bundle needs, before any
manifold structure enters:

* each fibre carries the action of `H` and the subspace topology;
* the total space `TotalSpace F (orbitFiber H X)`, for any model fibre `F`, carries the topology
  that makes `p ↦ p.snd.val` a homeomorphism onto `X`
  (`SymplecticGeometry.orbitFiber.totalSpaceHomeomorph`), equivariant for the fibrewise action of
  Tau Ceti's `Bundle.TotalSpace.instMulAction`;
* a map `s` from the orbit space to `X` picks out, for each `x`, the element
  `SymplecticGeometry.orbitSectionCoord s x` of `H` carrying `s ⟦x⟧` to `x`. For a free proper
  continuous action and a section `s` of the orbit projection continuous on an open set `U`, it is
  continuous over `U` (`SymplecticGeometry.continuousOn_orbitSectionCoord`), by
  `ProperSMul.continuousOn_of_smul_eq`, and equivariant.

Principal bundles in Tau Ceti act on the right, through an action of `Gᵐᵒᵖ`, and Tau Ceti's
`TauCeti.orbitTrivialization` is stated for a left action, with an equivariant map
`u (g • x) = g * u x`. For `H = Gᵐᵒᵖ` the map `orbitSectionCoord s` is such a `u`, and
`SymplecticGeometry.orbitFiber.trivializationOfSection` reads the resulting trivialization with
fibre `G` through `MulOpposite.opHomeomorph` and moves it to the total space of `orbitFiber`. Left
multiplication by `g : Gᵐᵒᵖ` on `Gᵐᵒᵖ` is right multiplication by `unop g` on `G`, so this
trivialization is equivariant in Tau Ceti's sense (`Bundle.Trivialization.IsEquivariant`), which
is the instance `SymplecticGeometry.orbitFiber.isEquivariant_trivializationOfSection`.

The acting group is an explicit argument of `orbitFiber`: in `TotalSpace G (orbitFiber Gᵐᵒᵖ X)`
nothing else determines it.

## Main definitions and results

* `SymplecticGeometry.orbitFiber`: the fibres of the orbit projection.
* `SymplecticGeometry.orbitFiber.totalSpaceHomeomorph`: their total space is homeomorphic to `X`.
* `SymplecticGeometry.orbitSectionCoord`: the element carrying the value of a section to a point.
* `SymplecticGeometry.orbitFiber.trivializationOfSection`: the trivialization with fibre `G` over
  the domain of a continuous local section of the orbit projection of a free proper action of
  `Gᵐᵒᵖ`, with `trivializationOfSection_apply` and `trivializationOfSection_symm_apply`.
* `SymplecticGeometry.orbitFiber.isEquivariant_trivializationOfSection`: it is equivariant.

## References

* D. Husemoller, *Fibre Bundles*, 3rd ed., Graduate Texts in Mathematics 20, Springer, 1994,
  Chapter 4 (principal bundles; the orbit projection of a free action with local cross sections).
* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §5.1
  (minimal coupling, which uses the principal bundle of a free circle action).
-/

public section

open Bundle MulAction MulOpposite Set Topology

namespace SymplecticGeometry

/-! ### The fibres of the orbit projection -/

section Fibres

variable (H X : Type*) [Group H] [MulAction H X]

/-- The fibres of the orbit projection `X → X ⧸ H`: the fibre over an orbit `q` is the type of the
points of `X` in `q`. -/
abbrev orbitFiber (q : orbitRel.Quotient H X) : Type _ :=
  {x : X // Quotient.mk (orbitRel H X) x = q}

variable {H X}

namespace orbitFiber

/-- A point of the fibre over `q` lies in the orbit `q`. -/
@[simp]
theorem mk_val {q : orbitRel.Quotient H X} (x : orbitFiber H X q) :
    Quotient.mk (orbitRel H X) x.val = q :=
  x.property

/-- The action of `H` on each fibre of the orbit projection, restricted from `X`. -/
instance instMulAction (q : orbitRel.Quotient H X) : MulAction H (orbitFiber H X q) where
  smul h x := ⟨h • x.val, by rw [orbitRel.Quotient.quotient_smul_eq, x.property]⟩
  one_smul x := Subtype.ext (one_smul H x.val)
  mul_smul g h x := Subtype.ext (mul_smul g h x.val)

/-- The action on a fibre of the orbit projection is the action on `X`. -/
@[simp]
theorem val_smul {q : orbitRel.Quotient H X} (h : H) (x : orbitFiber H X q) :
    (h • x).val = h • x.val :=
  rfl

end orbitFiber

end Fibres

/-! ### The total space -/

section TotalSpace

variable (H X F : Type*) [Group H] [MulAction H X]

/-- The total space of the fibres of the orbit projection is `X`: a point `⟨q, x⟩` goes to `x`,
and `x` comes from `⟨⟦x⟧, x⟩`. -/
def orbitFiber.totalSpaceEquiv : TotalSpace F (orbitFiber H X) ≃ X where
  toFun p := p.snd.val
  invFun x := ⟨Quotient.mk (orbitRel H X) x, x, rfl⟩
  left_inv := by rintro ⟨_, x, rfl⟩; rfl
  right_inv _ := rfl

variable {H X F} in
@[simp]
theorem orbitFiber.totalSpaceEquiv_apply (p : TotalSpace F (orbitFiber H X)) :
    orbitFiber.totalSpaceEquiv H X F p = p.snd.val :=
  (rfl)

variable {H X F} in
@[simp]
theorem orbitFiber.totalSpaceEquiv_symm_apply (x : X) :
    (orbitFiber.totalSpaceEquiv H X F).symm x = ⟨Quotient.mk (orbitRel H X) x, x, rfl⟩ :=
  (rfl)

variable [TopologicalSpace X]

/-- The topology on the total space of the fibres of the orbit projection induced from `X`
through `orbitFiber.totalSpaceEquiv`. -/
instance orbitFiber.instTopologicalSpaceTotalSpace :
    TopologicalSpace (TotalSpace F (orbitFiber H X)) :=
  .induced (orbitFiber.totalSpaceEquiv H X F) ‹_›

namespace orbitFiber

/-- The total space of the fibres of the orbit projection is homeomorphic to `X`, by
`p ↦ p.snd.val`. -/
def totalSpaceHomeomorph : TotalSpace F (orbitFiber H X) ≃ₜ X :=
  (totalSpaceEquiv H X F).toHomeomorphOfIsInducing ⟨rfl⟩

variable {H X F}

@[simp]
theorem totalSpaceHomeomorph_apply (p : TotalSpace F (orbitFiber H X)) :
    totalSpaceHomeomorph H X F p = p.snd.val :=
  (rfl)

@[simp]
theorem totalSpaceHomeomorph_symm_apply (x : X) :
    (totalSpaceHomeomorph H X F).symm x = ⟨Quotient.mk (orbitRel H X) x, x, rfl⟩ :=
  (rfl)

/-- The homeomorphism of the total space with `X` is equivariant for the fibrewise action. -/
theorem totalSpaceHomeomorph_smul (h : H) (p : TotalSpace F (orbitFiber H X)) :
    totalSpaceHomeomorph H X F (h • p) = h • totalSpaceHomeomorph H X F p := by
  simp

variable (F) in
/-- The projection of the total space to the orbit space is continuous. -/
theorem continuous_proj : Continuous (π F (orbitFiber H X)) :=
  (continuous_quot_mk.comp (totalSpaceHomeomorph H X F).continuous).congr fun p ↦
    p.snd.property

variable (F) in
/-- The inclusion of a fibre into the total space is inducing, for the subspace topology on the
fibre. -/
theorem isInducing_totalSpaceMk (q : orbitRel.Quotient H X) :
    IsInducing (TotalSpace.mk (F := F) (E := orbitFiber H X) q) := by
  have h : totalSpaceHomeomorph H X F ∘ TotalSpace.mk q = Subtype.val :=
    funext fun _ ↦ by simp
  exact (totalSpaceHomeomorph H X F).isInducing.of_comp_iff.1
    (h ▸ IsEmbedding.subtypeVal.isInducing)

end orbitFiber

end TotalSpace

/-! ### The element carrying a section to a point -/

section SectionCoord

variable {H X : Type*} [Group H] [MulAction H X]

/-- For a map `s` from the orbit space to `X`, an element of `H` carrying `s ⟦x⟧` to `x`.
Such an element exists when `s ⟦x⟧` lies in the orbit of `x` (`orbitSectionCoord_smul_apply`),
and is unique when the action is free (`orbitSectionCoord_eq_iff`); otherwise the value is
arbitrary. -/
noncomputable def orbitSectionCoord (s : orbitRel.Quotient H X → X) (x : X) : H :=
  Classical.epsilon fun g : H ↦ g • s (Quotient.mk (orbitRel H X) x) = x

variable {s : orbitRel.Quotient H X → X} {x : X}

/-- `orbitSectionCoord s x` carries `s ⟦x⟧` to `x` when `s ⟦x⟧` lies in the orbit of `x`. -/
theorem orbitSectionCoord_smul_apply
    (hx : Quotient.mk (orbitRel H X) (s (Quotient.mk (orbitRel H X) x)) =
      Quotient.mk (orbitRel H X) x) :
    orbitSectionCoord s x • s (Quotient.mk (orbitRel H X) x) = x :=
  Classical.epsilon_spec (Quotient.exact hx.symm)

variable [IsCancelSMul H X]

/-- For a free action, `orbitSectionCoord s x` is the element carrying `s ⟦x⟧` to `x`. -/
theorem orbitSectionCoord_eq_iff
    (hx : Quotient.mk (orbitRel H X) (s (Quotient.mk (orbitRel H X) x)) =
      Quotient.mk (orbitRel H X) x) {g : H} :
    orbitSectionCoord s x = g ↔ g • s (Quotient.mk (orbitRel H X) x) = x :=
  ⟨fun h ↦ h ▸ orbitSectionCoord_smul_apply hx, fun h ↦
    IsCancelSMul.right_cancel _ _ _ ((orbitSectionCoord_smul_apply hx).trans h.symm)⟩

/-- For a free action, `orbitSectionCoord s` is equivariant: `u (g • x) = g * u x`. -/
theorem orbitSectionCoord_smul
    (hx : Quotient.mk (orbitRel H X) (s (Quotient.mk (orbitRel H X) x)) =
      Quotient.mk (orbitRel H X) x) (g : H) :
    orbitSectionCoord s (g • x) = g * orbitSectionCoord s x := by
  rw [orbitSectionCoord_eq_iff (by simpa using hx), orbitRel.Quotient.quotient_smul_eq, mul_smul,
    orbitSectionCoord_smul_apply hx]

/-- For a free action and a section `s` of the orbit projection, `orbitSectionCoord s` is one
at the points of the image of `s`. -/
theorem orbitSectionCoord_apply_self {q : orbitRel.Quotient H X}
    (hq : Quotient.mk (orbitRel H X) (s q) = q) : orbitSectionCoord s (s q) = 1 :=
  (orbitSectionCoord_eq_iff (by rw [hq]; exact hq)).2 (by rw [hq, one_smul])

variable [TopologicalSpace H] [TopologicalSpace X] [ProperSMul H X]

/-- For a free proper action and a section `s` of the orbit projection over `U`, continuous on
`U`, the map `orbitSectionCoord s` is continuous on the points over `U`. -/
theorem continuousOn_orbitSectionCoord {U : Set (orbitRel.Quotient H X)} (hs : ContinuousOn s U)
    (hsec : ∀ q ∈ U, Quotient.mk (orbitRel H X) (s q) = q) :
    ContinuousOn (orbitSectionCoord s) (Quotient.mk (orbitRel H X) ⁻¹' U) :=
  ProperSMul.continuousOn_of_smul_eq (hs.comp continuous_quot_mk.continuousOn (mapsTo_preimage _ _))
    continuousOn_id fun _ hx ↦ orbitSectionCoord_smul_apply (hsec _ hx)

end SectionCoord

/-! ### Trivializations from local sections -/

section Trivialization

variable {G X : Type*} [Group G] [TopologicalSpace G] [ContinuousInv G] [TopologicalSpace X]
  [MulAction Gᵐᵒᵖ X] [ProperSMul Gᵐᵒᵖ X] [IsCancelSMul Gᵐᵒᵖ X]
  {U : Set (orbitRel.Quotient Gᵐᵒᵖ X)} {s : orbitRel.Quotient Gᵐᵒᵖ X → X}

namespace orbitFiber

/-- Tau Ceti's trivialization of the orbit projection over `U` determined by the equivariant map
`orbitSectionCoord s`, with fibre `Gᵐᵒᵖ`. -/
private noncomputable def orbitTrivializationOfSection (U : Set (orbitRel.Quotient Gᵐᵒᵖ X))
    (hU : IsOpen U) (s : orbitRel.Quotient Gᵐᵒᵖ X → X) (hs : ContinuousOn s U)
    (hsec : ∀ q ∈ U, Quotient.mk (orbitRel Gᵐᵒᵖ X) (s q) = q) :
    Bundle.Trivialization Gᵐᵒᵖ (Quotient.mk (orbitRel Gᵐᵒᵖ X)) :=
  TauCeti.orbitTrivialization U hU (orbitSectionCoord s) (continuousOn_orbitSectionCoord hs hsec)
    fun g _ hx ↦ orbitSectionCoord_smul (hsec _ hx) g

private theorem orbitTrivializationOfSection_baseSet {hU : IsOpen U} {hs : ContinuousOn s U}
    {hsec : ∀ q ∈ U, Quotient.mk (orbitRel Gᵐᵒᵖ X) (s q) = q} :
    (orbitTrivializationOfSection U hU s hs hsec).baseSet = U :=
  TauCeti.orbitTrivialization_baseSet

private theorem orbitTrivializationOfSection_apply {hU : IsOpen U} {hs : ContinuousOn s U}
    {hsec : ∀ q ∈ U, Quotient.mk (orbitRel Gᵐᵒᵖ X) (s q) = q} (x : X) :
    orbitTrivializationOfSection U hU s hs hsec x =
      (Quotient.mk (orbitRel Gᵐᵒᵖ X) x, orbitSectionCoord s x) :=
  TauCeti.orbitTrivialization_apply x

/-- The trivialization of the fibres of the orbit projection of a free proper action of `Gᵐᵒᵖ`
over an open set `U` of orbits, with fibre `G`, determined by a section `s` of the orbit projection
over `U` that is continuous on `U`. It sends a point `x` over `q ∈ U` to
`(q, unop (orbitSectionCoord s x))`, where `orbitSectionCoord s x • s q = x`. It is Tau Ceti's
`TauCeti.orbitTrivialization` for the equivariant map `orbitSectionCoord s`, read with fibre `G`
and moved to the total space through `orbitFiber.totalSpaceHomeomorph`. -/
noncomputable def trivializationOfSection (U : Set (orbitRel.Quotient Gᵐᵒᵖ X)) (hU : IsOpen U)
    (s : orbitRel.Quotient Gᵐᵒᵖ X → X) (hs : ContinuousOn s U)
    (hsec : ∀ q ∈ U, Quotient.mk (orbitRel Gᵐᵒᵖ X) (s q) = q) :
    Bundle.Trivialization G (π G (orbitFiber Gᵐᵒᵖ X)) where
  toOpenPartialHomeomorph :=
    (((orbitTrivializationOfSection U hU s hs hsec).transFiberHomeomorph
      (opHomeomorph (M := G)).symm).compHomeomorph
        (totalSpaceHomeomorph Gᵐᵒᵖ X G)).toOpenPartialHomeomorph
  baseSet := U
  open_baseSet := hU
  source_eq := by
    rw [Bundle.Trivialization.source_eq]
    ext ⟨_, x, rfl⟩
    -- the base set of the composite is that of Tau Ceti's trivialization, by definition
    change Quotient.mk _ x ∈ (orbitTrivializationOfSection U hU s hs hsec).baseSet ↔ _
    rw [orbitTrivializationOfSection_baseSet]
    rfl
  target_eq := (Bundle.Trivialization.target_eq _).trans
    (congrArg (· ×ˢ univ) orbitTrivializationOfSection_baseSet)
  proj_toFun p hp := (Bundle.Trivialization.proj_toFun _ p hp).trans p.snd.property

variable {hU : IsOpen U} {hs : ContinuousOn s U}
  {hsec : ∀ q ∈ U, Quotient.mk (orbitRel Gᵐᵒᵖ X) (s q) = q}

@[simp]
theorem trivializationOfSection_baseSet :
    (trivializationOfSection U hU s hs hsec).baseSet = U :=
  (rfl)

/-- `trivializationOfSection` sends a point `x` over `q` to `(q, unop (orbitSectionCoord s x))`. -/
@[simp]
theorem trivializationOfSection_apply (p : TotalSpace G (orbitFiber Gᵐᵒᵖ X)) :
    trivializationOfSection U hU s hs hsec p = (p.proj, unop (orbitSectionCoord s p.snd.val)) := by
  -- the composite applies Tau Ceti's chart to `p.snd.val` and `unop` to its second component
  change ((orbitTrivializationOfSection U hU s hs hsec p.snd.val).1,
    unop (orbitTrivializationOfSection U hU s hs hsec p.snd.val).2) = _
  rw [orbitTrivializationOfSection_apply]
  exact Prod.ext p.snd.property rfl

/-- Over a point `q` of `U`, the inverse of `trivializationOfSection` sends `(q, g)` to the
point `s q` moved by `g` on the right, `op g • s q`. -/
theorem trivializationOfSection_symm_apply {q : orbitRel.Quotient Gᵐᵒᵖ X} (hq : q ∈ U) (g : G) :
    (trivializationOfSection U hU s hs hsec).toOpenPartialHomeomorph.symm (q, g) =
      ⟨q, op g • ⟨s q, hsec q hq⟩⟩ := by
  set e := trivializationOfSection U hU s hs hsec
  have hq' : q ∈ e.baseSet := hq
  refine ((e.toOpenPartialHomeomorph.eq_symm_apply (e.mem_source.2 hq')
    (e.mem_target.2 hq')).2 ?_).symm
  rw [e.coe_coe, trivializationOfSection_apply, orbitFiber.val_smul,
    orbitSectionCoord_smul (by rw [hsec q hq, hsec q hq]),
    orbitSectionCoord_apply_self (hsec q hq), mul_one, unop_op]

/-- **The trivialization from a local section is equivariant.** Left multiplication by
`g : Gᵐᵒᵖ` on the fibre `Gᵐᵒᵖ` of Tau Ceti's `TauCeti.orbitTrivialization` is right
multiplication by `unop g` on `G`, so `trivializationOfSection` intertwines the right action of
`G` on the fibres with right multiplication on `G`. -/
instance isEquivariant_trivializationOfSection :
    (trivializationOfSection U hU s hs hsec).IsEquivariant :=
  ⟨fun b hb p g ↦ by
    simp only [trivializationOfSection_apply, val_smul]
    rw [orbitSectionCoord_smul (by rw [p.property, hsec b hb]), unop_mul, unop_op]⟩

end orbitFiber

end Trivialization

end SymplecticGeometry

end
