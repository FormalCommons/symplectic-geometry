/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Algebra.ProperAction.Basic
public import TauCeti.Topology.Algebra.GroupAction.OrbitTrivialization

/-!
# Free proper actions

For a proper action of a topological group `G` on `X` that is free (`IsCancelSMul G X`), the map
`(g, x) ↦ (g • x, x)` is proper and injective, hence a closed embedding. Consequently the element
of `G` carrying one point to another depends continuously on the two points: if `a` and `b` are
continuous on a set `s` and `f y • a y = b y` on `s`, then `f` is continuous on `s`.

The first statement adapts the proof of `isClosedEmbedding_smul_const` (Tau Ceti,
`Topology/Algebra/ProperAction/Orbit.lean`) from a single orbit map to the whole action.

A map `s` from the orbit space to `X` determines, at each point `x`, an element
`SymplecticGeometry.orbitSectionCoord s x` of `G` carrying `s ⟦x⟧` to `x`. When the action is
free and proper and `s` is a section of the orbit projection over an open set `U` of orbits,
continuous on `U`, this element is continuous and equivariant over `U`. Tau Ceti's
`TauCeti.orbitTrivialization` then turns it into a trivialization of the orbit projection over `U`
with fibre `G`, `SymplecticGeometry.orbitTrivializationOfSection`.

## Main results

* `ProperSMul.isClosedEmbedding_smul_pair`: for a free proper action, `(g, x) ↦ (g • x, x)` is a
  closed embedding.
* `ProperSMul.continuousOn_of_smul_eq`: the acting element between two continuous families of
  points is continuous.
* `SymplecticGeometry.orbitSectionCoord`: the element carrying the value of a section to a point,
  with `SymplecticGeometry.continuousOn_orbitSectionCoord`.
* `SymplecticGeometry.orbitTrivializationOfSection`: the trivialization of the orbit projection
  over the domain of a continuous local section.

## References

* N. Bourbaki, *General Topology*, Chapters 1–4, Springer, 1989, Chapter III, §4 (proper
  actions).
* D. Husemoller, *Fibre Bundles*, 3rd ed., Graduate Texts in Mathematics 20, Springer, 1994,
  Chapter 4 (the orbit projection of a free action with local cross sections).
-/

public section

open Function MulAction Set Topology

section ProperSMul

variable {G X : Type*} [Group G] [MulAction G X] [TopologicalSpace G] [TopologicalSpace X]
  [ProperSMul G X] [IsCancelSMul G X]

/-- For a free proper action, the map `(g, x) ↦ (g • x, x)` is a closed embedding. -/
@[to_additive /-- For a free proper additive action, the map `(g, x) ↦ (g +ᵥ x, x)` is a closed
embedding. -/]
theorem ProperSMul.isClosedEmbedding_smul_pair :
    IsClosedEmbedding fun gx : G × X ↦ (gx.1 • gx.2, gx.2) :=
  .of_continuous_injective_isClosedMap ProperSMul.isProperMap_smul_pair.continuous
    (fun ⟨g, x⟩ ⟨g', x'⟩ h ↦ by
      obtain ⟨h₁, rfl : x = x'⟩ := Prod.mk.inj h
      rw [IsCancelSMul.right_cancel g g' x h₁])
    ProperSMul.isProperMap_smul_pair.isClosedMap

/-- For a free proper action, the element of `G` carrying `a y` to `b y` is continuous where `a`
and `b` are: if `f y • a y = b y` for `y ∈ s`, and `a` and `b` are continuous on `s`, then so
is `f`. -/
@[to_additive /-- For a free proper additive action, the element of `G` carrying `a y` to `b y` is
continuous where `a` and `b` are: if `f y +ᵥ a y = b y` for `y ∈ s`, and `a` and `b` are
continuous on `s`, then so is `f`. -/]
theorem ProperSMul.continuousOn_of_smul_eq {Y : Type*} [TopologicalSpace Y] {s : Set Y}
    {f : Y → G} {a b : Y → X} (ha : ContinuousOn a s) (hb : ContinuousOn b s)
    (h : ∀ y ∈ s, f y • a y = b y) : ContinuousOn f s := by
  have hpair : ContinuousOn (fun y ↦ (f y, a y)) s :=
    ProperSMul.isClosedEmbedding_smul_pair.isInducing.continuousOn_iff.2 <|
      (hb.prodMk ha).congr fun y hy ↦ by simp [h y hy]
  exact continuous_fst.comp_continuousOn hpair

end ProperSMul

namespace SymplecticGeometry

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

variable {H X : Type*} [Group H] [TopologicalSpace H] [ContinuousInv H] [TopologicalSpace X]
  [MulAction H X] [ProperSMul H X] [IsCancelSMul H X]

/-- The trivialization, with fibre `H`, of the orbit projection of a free proper action over an
open set `U` of orbits, determined by a section `s` of the orbit projection over `U` that is
continuous on `U`. It sends `x` to `(⟦x⟧, orbitSectionCoord s x)`, where
`orbitSectionCoord s x • s ⟦x⟧ = x`. It is Tau Ceti's `TauCeti.orbitTrivialization` for the
equivariant map `orbitSectionCoord s`. -/
noncomputable def orbitTrivializationOfSection (U : Set (orbitRel.Quotient H X)) (hU : IsOpen U)
    (s : orbitRel.Quotient H X → X) (hs : ContinuousOn s U)
    (hsec : ∀ q ∈ U, Quotient.mk (orbitRel H X) (s q) = q) :
    Bundle.Trivialization H (Quotient.mk (orbitRel H X)) :=
  TauCeti.orbitTrivialization U hU (orbitSectionCoord s) (continuousOn_orbitSectionCoord hs hsec)
    fun g _ hx ↦ orbitSectionCoord_smul (hsec _ hx) g

variable {U : Set (orbitRel.Quotient H X)} {hU : IsOpen U} {s : orbitRel.Quotient H X → X}
  {hs : ContinuousOn s U} {hsec : ∀ q ∈ U, Quotient.mk (orbitRel H X) (s q) = q}

/-- The base of `orbitTrivializationOfSection` is the domain of the section. -/
@[simp]
theorem orbitTrivializationOfSection_baseSet :
    (orbitTrivializationOfSection U hU s hs hsec).baseSet = U :=
  TauCeti.orbitTrivialization_baseSet

/-- `orbitTrivializationOfSection` sends `x` to its orbit together with `orbitSectionCoord s x`. -/
@[simp]
theorem orbitTrivializationOfSection_apply (x : X) :
    orbitTrivializationOfSection U hU s hs hsec x =
      (Quotient.mk (orbitRel H X) x, orbitSectionCoord s x) :=
  TauCeti.orbitTrivialization_apply x

end Trivialization

end SymplecticGeometry

end
