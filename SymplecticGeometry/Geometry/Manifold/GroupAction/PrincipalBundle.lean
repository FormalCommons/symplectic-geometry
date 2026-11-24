/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.FiberBundle.MapFiber
public import SymplecticGeometry.Topology.Algebra.ProperAction.Free

/-!
# The principal bundle of a free proper action

Let a group `H` act on a space `X`. The orbit projection `X → X ⧸ H` is a family of types over the
orbit space, `orbitFiber H X`, whose fibre over an orbit `q` is the subtype of the points of `q`:
it is Tau Ceti's `TauCeti.MapFiber` of the orbit projection. This file gives that family the
structure the topological principal bundle needs, before any manifold structure enters:

* each fibre carries the action of `H`, restricted from `X` by Tau Ceti's
  `TauCeti.MapFiber.mulAction`, and the subspace topology;
* the total space `TotalSpace F (orbitFiber H X)`, for any model fibre `F`, carries the topology
  of `X` through Tau Ceti's homeomorphism `TauCeti.MapFiber.totalSpaceHomeomorph`, which is
  equivariant for the fibrewise action of Tau Ceti's `Bundle.TotalSpace.instMulAction`
  (`SymplecticGeometry.orbitFiber.totalSpaceHomeomorph_smul`);
* for a free proper action of `Gᵐᵒᵖ` and a section `s` of the orbit projection continuous on an
  open set `U`, the trivialization `SymplecticGeometry.orbitTrivializationOfSection` of the orbit
  projection, read with fibre `G` through `MulOpposite.opHomeomorph` and passed to the fibres by
  `Bundle.Trivialization.toMapFiber`, is a trivialization of `orbitFiber Gᵐᵒᵖ X` over `U`
  (`SymplecticGeometry.orbitFiber.trivializationOfSection`).

Principal bundles in Tau Ceti act on the right, through an action of `Gᵐᵒᵖ`, and Tau Ceti's
`TauCeti.orbitTrivialization` is stated for a left action. Left multiplication by `g : Gᵐᵒᵖ` on
`Gᵐᵒᵖ` is right multiplication by `unop g` on `G`, so the trivialization with fibre `G` is
equivariant in Tau Ceti's sense (`Bundle.Trivialization.IsEquivariant`), which is the instance
`SymplecticGeometry.orbitFiber.isEquivariant_trivializationOfSection`.

The acting group is an explicit argument of `orbitFiber`: in `TotalSpace G (orbitFiber Gᵐᵒᵖ X)`
nothing else determines it.

## Main definitions and results

* `SymplecticGeometry.orbitFiber`: the fibres of the orbit projection.
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

open Bundle MulAction MulOpposite Set Topology TauCeti

namespace SymplecticGeometry

/-! ### The fibres of the orbit projection -/

section Fibres

variable (H X : Type*) [Group H] [MulAction H X]

/-- The fibres of the orbit projection `X → X ⧸ H`: the fibre over an orbit `q` is the type of the
points of `X` in `q`. -/
abbrev orbitFiber : orbitRel.Quotient H X → Type _ :=
  MapFiber (Quotient.mk (orbitRel H X))

variable {H X}

namespace orbitFiber

/-- A point of the fibre over `q` lies in the orbit `q`. -/
@[simp]
theorem mk_val {q : orbitRel.Quotient H X} (x : orbitFiber H X q) :
    Quotient.mk (orbitRel H X) x.val = q :=
  x.property

/-- The action of `H` on each fibre of the orbit projection, restricted from `X`. -/
instance instMulAction (q : orbitRel.Quotient H X) : MulAction H (orbitFiber H X q) :=
  MapFiber.mulAction (fun _ _ ↦ orbitRel.Quotient.quotient_smul_eq) q

variable [TopologicalSpace X] (F : Type*)

/-- The homeomorphism of the total space of the fibres with `X` is equivariant for the fibrewise
action. -/
theorem totalSpaceHomeomorph_smul (h : H) (p : TotalSpace F (orbitFiber H X)) :
    MapFiber.totalSpaceHomeomorph F (Quotient.mk (orbitRel H X)) (h • p) =
      h • MapFiber.totalSpaceHomeomorph F (Quotient.mk (orbitRel H X)) p := by
  simp

/-- The projection of the total space to the orbit space is continuous. -/
theorem continuous_proj : Continuous (π F (orbitFiber H X)) :=
  (continuous_quot_mk.comp (MapFiber.totalSpaceHomeomorph F _).continuous).congr
    MapFiber.proj_totalSpaceHomeomorph

end orbitFiber

end Fibres

/-! ### Trivializations from local sections -/

section Trivialization

variable {G X : Type*} [Group G] [TopologicalSpace G] [ContinuousInv G] [TopologicalSpace X]
  [MulAction Gᵐᵒᵖ X] [ProperSMul Gᵐᵒᵖ X] [IsCancelSMul Gᵐᵒᵖ X]
  {U : Set (orbitRel.Quotient Gᵐᵒᵖ X)} {s : orbitRel.Quotient Gᵐᵒᵖ X → X}

namespace orbitFiber

/-- The trivialization of the fibres of the orbit projection of a free proper action of `Gᵐᵒᵖ`
over an open set `U` of orbits, with fibre `G`, determined by a section `s` of the orbit projection
over `U` that is continuous on `U`. It sends a point `x` over `q ∈ U` to
`(q, unop (orbitSectionCoord s x))`, where `orbitSectionCoord s x • s q = x`. It is
`orbitTrivializationOfSection` read with fibre `G` and passed to the fibres. -/
noncomputable def trivializationOfSection (U : Set (orbitRel.Quotient Gᵐᵒᵖ X)) (hU : IsOpen U)
    (s : orbitRel.Quotient Gᵐᵒᵖ X → X) (hs : ContinuousOn s U)
    (hsec : ∀ q ∈ U, Quotient.mk (orbitRel Gᵐᵒᵖ X) (s q) = q) :
    Bundle.Trivialization G (π G (orbitFiber Gᵐᵒᵖ X)) :=
  ((orbitTrivializationOfSection U hU s hs hsec).transFiberHomeomorph
    (opHomeomorph (M := G)).symm).toMapFiber

variable {hU : IsOpen U} {hs : ContinuousOn s U}
  {hsec : ∀ q ∈ U, Quotient.mk (orbitRel Gᵐᵒᵖ X) (s q) = q}

@[simp]
theorem trivializationOfSection_baseSet :
    (trivializationOfSection U hU s hs hsec).baseSet = U := by
  rw [trivializationOfSection, Trivialization.toMapFiber_baseSet]
  -- `transFiberHomeomorph` keeps the base set by definition; Mathlib states no lemma for it
  exact orbitTrivializationOfSection_baseSet

/-- `trivializationOfSection` sends a point `x` over `q` to `(q, unop (orbitSectionCoord s x))`. -/
@[simp]
theorem trivializationOfSection_apply (p : TotalSpace G (orbitFiber Gᵐᵒᵖ X)) :
    trivializationOfSection U hU s hs hsec p = (p.proj, unop (orbitSectionCoord s p.snd.val)) := by
  simp [trivializationOfSection, Trivialization.transFiberHomeomorph_apply]

/-- Over a point `q` of `U`, the inverse of `trivializationOfSection` sends `(q, g)` to the
point `s q` moved by `g` on the right, `op g • s q`. -/
@[simp]
theorem trivializationOfSection_symm_apply {q : orbitRel.Quotient Gᵐᵒᵖ X} (hq : q ∈ U) (g : G) :
    (trivializationOfSection U hU s hs hsec).toOpenPartialHomeomorph.symm (q, g) =
      ⟨q, op g • ⟨s q, hsec q hq⟩⟩ := by
  rw [trivializationOfSection, Trivialization.toMapFiber_symm_apply, Homeomorph.symm_apply_eq,
    MapFiber.totalSpaceHomeomorph_apply, MapFiber.coe_smul]
  -- Mathlib states no lemma for the inverse of `transFiberHomeomorph`, so its definition is
  -- unfolded to reach `OpenPartialHomeomorph.transHomeomorph_symm_apply`
  simp [Trivialization.transFiberHomeomorph, orbitTrivializationOfSection_symm_apply hq]

/-- **The trivialization from a local section is equivariant.** Left multiplication by
`g : Gᵐᵒᵖ` on the fibre `Gᵐᵒᵖ` of `orbitTrivializationOfSection` is right multiplication by
`unop g` on `G`, so `trivializationOfSection` intertwines the right action of `G` on the fibres
with right multiplication on `G`. -/
instance isEquivariant_trivializationOfSection :
    (trivializationOfSection U hU s hs hsec).IsEquivariant :=
  ⟨fun b hb p g ↦ by
    rw [trivializationOfSection_baseSet] at hb
    simp only [trivializationOfSection_apply, MapFiber.coe_smul]
    rw [orbitSectionCoord_smul (by rw [p.property, hsec b hb]), unop_mul, unop_op]⟩

end orbitFiber

end Trivialization

end SymplecticGeometry

end
