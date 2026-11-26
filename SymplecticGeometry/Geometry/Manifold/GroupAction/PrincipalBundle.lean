/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberBundle.MapFiber
public import TauCeti.Geometry.Manifold.GroupAction.Quotient
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective
public import SymplecticGeometry.Geometry.Manifold.Algebra.MulOpposite
public import SymplecticGeometry.Topology.Algebra.ProperAction.Free
public import SymplecticGeometry.Topology.FiberBundle.ChangeModelFiber

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
  projection, read with fibre `G` through `MulOpposite.opHomeomorph`
  (`SymplecticGeometry.orbitTrivializationOfSectionUnop`) and passed to the fibres by
  `Bundle.Trivialization.toMapFiber`, is a trivialization of `orbitFiber Gᵐᵒᵖ X` over `U`
  (`SymplecticGeometry.orbitFiber.trivializationOfSection`).

Principal bundles in Tau Ceti act on the right, through an action of `Gᵐᵒᵖ`, and Tau Ceti's
`TauCeti.orbitTrivialization` is stated for a left action. Left multiplication by `g : Gᵐᵒᵖ` on
`Gᵐᵒᵖ` is right multiplication by `unop g` on `G`, so the trivialization with fibre `G` is
equivariant in Tau Ceti's sense (`Bundle.Trivialization.IsEquivariant`), which is the instance
`SymplecticGeometry.orbitFiber.isEquivariant_trivializationOfSection`.

The acting group is an explicit argument of `orbitFiber`: in `TotalSpace G (orbitFiber Gᵐᵒᵖ X)`
nothing else determines it.

For a free proper smooth right action of a Lie group `G` on a boundaryless finite-dimensional
manifold `X`, Tau Ceti's quotient manifold theorem gives a smooth local section of the orbit
projection through every orbit. The trivializations from these sections form a
`TauCeti.MapFiber.Atlas` (`SymplecticGeometry.orbitFiber.atlas`), and Tau Ceti's
`TauCeti.MapFiber.Atlas.fiberBundle` makes `orbitFiber Gᵐᵒᵖ X` a fibre bundle with fibre `G`. It
is a principal `G`-bundle because every trivialization of the atlas is equivariant
(`SymplecticGeometry.orbitFiber.isEquivariant_trivializationOfSection`). A compact Lie group
acts properly (`TauCeti.properSMul_of_compactSpace`), so this covers free smooth actions of
compact Lie groups.

**Smoothness.** The trivialization of a smooth local section `s` over `U` has inverse
`(q, g) ↦ op g • s q`. This is the map `(k, q) ↦ k • s q` after the diffeomorphism
`(q, g) ↦ (op g, q)` built from `MulOpposite.opDiffeomorph`. For the slice charts of the
orbit space, that map is a local diffeomorphism on `Gᵐᵒᵖ × U`
(`ProperSMul.isLocalDiffeomorphAt_smul_section`), and so is the inverse on `U × G`. The
trivialization, its inverse on its image, is then smooth
(`IsLocalDiffeomorphOn.contMDiffOn_invFunOn`). So the atlas is smooth
(`SymplecticGeometry.orbitFiber.isContMDiff_atlas`): Tau Ceti's
`TauCeti.MapFiber.Atlas.contMDiffFiberBundle` makes `orbitFiber Gᵐᵒᵖ X` a smooth fibre bundle,
and `TauCeti.MapFiber.Atlas.totalSpaceDiffeomorph` is a diffeomorphism of its total space with
`X` over the orbit space (`TauCeti.MapFiber.Atlas.proj_totalSpaceDiffeomorph`), equivariant for
the right action of `G` (`TauCeti.MapFiber.Atlas.totalSpaceDiffeomorph_smul`). The file adds no
names for these: statements take them from the atlas and `isContMDiff_atlas`.

**Local instances.** The statements about this bundle use two charted spaces that are not global
instances, and later files should use the same ones:
* on `Gᵐᵒᵖ`, the charts of `G` (`MulOpposite.chartedSpace`), a local instance of the section, in
  which the smoothness of the action is `ContMDiffSMul IG IX ∞ Gᵐᵒᵖ X`;
* on the orbit space, Tau Ceti's slice charts
  `ProperSMul.orbitRelQuotientChartedSpace IG Gᵐᵒᵖ IX X`, introduced by `letI` in the statements
  that need them.

The atlas, and so the bundle structure, depends on the models `IG` and `IX`, which the type
`orbitFiber Gᵐᵒᵖ X` does not determine, so instance search could not find it. The file adds no
bundle structure of its own: statements put Tau Ceti's in place by
`letI := (SymplecticGeometry.orbitFiber.atlas IG G IX X).fiberBundle`, and principality is the
theorem `SymplecticGeometry.orbitFiber.principalBundle IG G IX X`, to be used by `haveI`, and so
is the smooth structure, `(atlas IG G IX X).contMDiffFiberBundle (isContMDiff_atlas IG G IX X)`.

## Main definitions and results

* `SymplecticGeometry.orbitFiber`: the fibres of the orbit projection.
* `SymplecticGeometry.orbitTrivializationOfSectionUnop`: the trivialization with fibre `G` of the
  orbit projection over the domain of a continuous local section, for a free proper action of
  `Gᵐᵒᵖ`.
* `SymplecticGeometry.orbitFiber.trivializationOfSection`: the trivialization with fibre `G` over
  the domain of a continuous local section of the orbit projection of a free proper action of
  `Gᵐᵒᵖ`, with `trivializationOfSection_apply` and `trivializationOfSection_symm_apply`.
* `SymplecticGeometry.orbitFiber.isEquivariant_trivializationOfSection`: it is equivariant.
* `SymplecticGeometry.orbitFiber.atlas`: the atlas of the orbit projection of a free proper
  smooth action, whose trivializations come from smooth local sections
  (`SymplecticGeometry.orbitFiber.exists_atlas_trivAt_eq`).
* `SymplecticGeometry.orbitFiber.principalBundle`: its fibre bundle is a principal `G`-bundle.
* `SymplecticGeometry.orbitFiber.isContMDiff_atlas`: the atlas is smooth.

## References

* D. Husemoller, *Fibre Bundles*, 3rd ed., Graduate Texts in Mathematics 20, Springer, 1994,
  Chapter 4 (principal bundles; the orbit projection of a free action with local cross sections).
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Theorem 21.10 and its proof (the quotient manifold theorem: local sections of
  the orbit projection give the local trivializations of the orbit bundle).
* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §5.1
  (minimal coupling, which uses the principal bundle of a free circle action).
-/

public section

open Bundle MulAction MulOpposite Set Topology TauCeti
open scoped ContDiff Manifold

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

/-- The trivialization, with fibre `G`, of the orbit projection of a free proper action of `Gᵐᵒᵖ`
over an open set `U` of orbits, determined by a section `s` of the orbit projection over `U` that
is continuous on `U`: `orbitTrivializationOfSection` read with fibre `G` through
`MulOpposite.opHomeomorph`. It sends `x` to `(⟦x⟧, unop (orbitSectionCoord s x))`. -/
noncomputable def orbitTrivializationOfSectionUnop (U : Set (orbitRel.Quotient Gᵐᵒᵖ X))
    (hU : IsOpen U) (s : orbitRel.Quotient Gᵐᵒᵖ X → X) (hs : ContinuousOn s U)
    (hsec : ∀ q ∈ U, Quotient.mk (orbitRel Gᵐᵒᵖ X) (s q) = q) :
    Bundle.Trivialization G (Quotient.mk (orbitRel Gᵐᵒᵖ X)) :=
  (orbitTrivializationOfSection U hU s hs hsec).transFiberHomeomorph (opHomeomorph (M := G)).symm

variable {hU : IsOpen U} {hs : ContinuousOn s U}
  {hsec : ∀ q ∈ U, Quotient.mk (orbitRel Gᵐᵒᵖ X) (s q) = q}

theorem orbitTrivializationOfSectionUnop_def :
    orbitTrivializationOfSectionUnop U hU s hs hsec =
      (orbitTrivializationOfSection U hU s hs hsec).transFiberHomeomorph
        (opHomeomorph (M := G)).symm :=
  (rfl)

/-- The base of `orbitTrivializationOfSectionUnop` is the domain of the section. -/
@[simp]
theorem orbitTrivializationOfSectionUnop_baseSet :
    (orbitTrivializationOfSectionUnop U hU s hs hsec).baseSet = U := by
  rw [orbitTrivializationOfSectionUnop_def, Trivialization.transFiberHomeomorph_baseSet,
    orbitTrivializationOfSection_baseSet]

/-- `orbitTrivializationOfSectionUnop` sends `x` to its orbit together with
`unop (orbitSectionCoord s x)`. -/
@[simp]
theorem orbitTrivializationOfSectionUnop_apply (x : X) :
    orbitTrivializationOfSectionUnop U hU s hs hsec x =
      (Quotient.mk (orbitRel Gᵐᵒᵖ X) x, unop (orbitSectionCoord s x)) := by
  simp [orbitTrivializationOfSectionUnop_def, Trivialization.transFiberHomeomorph_apply]

/-- Over a point `q` of `U`, the inverse of `orbitTrivializationOfSectionUnop` sends `(q, g)` to
`s q` moved by `g` on the right, `op g • s q`. -/
@[simp]
theorem orbitTrivializationOfSectionUnop_symm_apply {q : orbitRel.Quotient Gᵐᵒᵖ X} (hq : q ∈ U)
    (g : G) :
    (orbitTrivializationOfSectionUnop U hU s hs hsec).toOpenPartialHomeomorph.symm (q, g) =
      op g • s q := by
  simp [orbitTrivializationOfSectionUnop_def, orbitTrivializationOfSection_symm_apply hq]

namespace orbitFiber

/-- The trivialization of the fibres of the orbit projection of a free proper action of `Gᵐᵒᵖ`
over an open set `U` of orbits, with fibre `G`, determined by a section `s` of the orbit projection
over `U` that is continuous on `U`. It sends a point `x` over `q ∈ U` to
`(q, unop (orbitSectionCoord s x))`, where `orbitSectionCoord s x • s q = x`. It is
`orbitTrivializationOfSectionUnop` passed to the fibres. -/
noncomputable def trivializationOfSection (U : Set (orbitRel.Quotient Gᵐᵒᵖ X)) (hU : IsOpen U)
    (s : orbitRel.Quotient Gᵐᵒᵖ X → X) (hs : ContinuousOn s U)
    (hsec : ∀ q ∈ U, Quotient.mk (orbitRel Gᵐᵒᵖ X) (s q) = q) :
    Bundle.Trivialization G (π G (orbitFiber Gᵐᵒᵖ X)) :=
  (orbitTrivializationOfSectionUnop U hU s hs hsec).toMapFiber

theorem trivializationOfSection_def :
    trivializationOfSection U hU s hs hsec =
      (orbitTrivializationOfSectionUnop U hU s hs hsec).toMapFiber :=
  (rfl)

@[simp]
theorem trivializationOfSection_baseSet :
    (trivializationOfSection U hU s hs hsec).baseSet = U := by
  rw [trivializationOfSection_def, Trivialization.toMapFiber_baseSet,
    orbitTrivializationOfSectionUnop_baseSet]

/-- `trivializationOfSection` sends a point `x` over `q` to `(q, unop (orbitSectionCoord s x))`. -/
@[simp]
theorem trivializationOfSection_apply (p : TotalSpace G (orbitFiber Gᵐᵒᵖ X)) :
    trivializationOfSection U hU s hs hsec p = (p.proj, unop (orbitSectionCoord s p.snd.val)) := by
  simp [trivializationOfSection_def]

/-- Over a point `q` of `U`, the inverse of `trivializationOfSection` sends `(q, g)` to the
point `s q` moved by `g` on the right, `op g • s q`. -/
@[simp]
theorem trivializationOfSection_symm_apply {q : orbitRel.Quotient Gᵐᵒᵖ X} (hq : q ∈ U) (g : G) :
    (trivializationOfSection U hU s hs hsec).toOpenPartialHomeomorph.symm (q, g) =
      ⟨q, op g • ⟨s q, hsec q hq⟩⟩ := by
  rw [trivializationOfSection_def, Trivialization.toMapFiber_symm_apply, Homeomorph.symm_apply_eq,
    MapFiber.totalSpaceHomeomorph_apply, MapFiber.coe_smul]
  rw [orbitTrivializationOfSectionUnop_symm_apply hq]

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

/-! ### Smoothness of the atlas -/

section Smooth

attribute [local instance] MulOpposite.chartedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {IG : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup IG ∞ G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {IX : ModelWithCorners ℝ E' H'} [IX.Boundaryless]
  {X : Type*} [TopologicalSpace X] [ChartedSpace H' X] [IsManifold IX ∞ X]
  [MulAction Gᵐᵒᵖ X] [ContMDiffSMul IG IX ∞ Gᵐᵒᵖ X] [ProperSMul Gᵐᵒᵖ X] [IsCancelSMul Gᵐᵒᵖ X]
  {U : Set (orbitRel.Quotient Gᵐᵒᵖ X)} {s : orbitRel.Quotient Gᵐᵒᵖ X → X}

namespace orbitFiber

/-- For the slice charts of the orbit space, `(q, g) ↦ op g • s q` is a local diffeomorphism on
`U × G`: it is the map `(k, q) ↦ k • s q` of Tau Ceti's
`ProperSMul.isLocalDiffeomorphAt_smul_section` after the diffeomorphism `(q, g) ↦ (op g, q)`. -/
private theorem isLocalDiffeomorphOn_op_smul_section (hU : IsOpen U)
    (hs : letI := ProperSMul.orbitRelQuotientChartedSpace IG Gᵐᵒᵖ IX X
      ContMDiffOn 𝓘(ℝ, ProperSMul.QuotientModelSpace E E') IX ∞ s U)
    (hsec : ∀ q ∈ U, Quotient.mk (orbitRel Gᵐᵒᵖ X) (s q) = q) :
    letI := ProperSMul.orbitRelQuotientChartedSpace IG Gᵐᵒᵖ IX X
    IsLocalDiffeomorphOn (𝓘(ℝ, ProperSMul.QuotientModelSpace E E').prod IG) IX ∞
      (fun p : orbitRel.Quotient Gᵐᵒᵖ X × G ↦ op p.2 • s p.1) (U ×ˢ univ) := fun p ↦ by
  let := ProperSMul.orbitRelQuotientChartedSpace IG Gᵐᵒᵖ IX X
  set IB := 𝓘(ℝ, ProperSMul.QuotientModelSpace E E')
  let T : (orbitRel.Quotient Gᵐᵒᵖ X × G) ≃ₘ⟮IB.prod IG, IG.prod IB⟯
      (Gᵐᵒᵖ × orbitRel.Quotient Gᵐᵒᵖ X) :=
    (Diffeomorph.prodComm IB IG _ G ∞).trans
      ((opDiffeomorph IG ∞ G).prodCongr (Diffeomorph.refl IB _ ∞))
  have hT : (fun p : Gᵐᵒᵖ × orbitRel.Quotient Gᵐᵒᵖ X ↦ p.1 • s p.2) ∘ T =
      fun p : orbitRel.Quotient Gᵐᵒᵖ X × G ↦ op p.2 • s p.1 :=
    funext fun p ↦ by simp [T]
  rw [← hT]
  exact IsLocalDiffeomorphAt.comp (hf := T.isLocalDiffeomorph p)
    (hg := ProperSMul.isLocalDiffeomorphAt_smul_section (I := IG) hU hs hsec p.property.1 _)

/-- The trivialization `orbitTrivializationOfSectionUnop` of a local section, smooth for the slice
charts of the orbit space, is smooth on its source, and so is its inverse on its target: the
inverse is `(q, g) ↦ op g • s q`, and the trivialization is the inverse of this injective local
diffeomorphism. -/
private theorem contMDiffOn_orbitTrivializationOfSectionUnop [ContinuousInv G] (hU : IsOpen U)
    (hs : letI := ProperSMul.orbitRelQuotientChartedSpace IG Gᵐᵒᵖ IX X
      ContMDiffOn 𝓘(ℝ, ProperSMul.QuotientModelSpace E E') IX ∞ s U)
    (hsec : ∀ q ∈ U, Quotient.mk (orbitRel Gᵐᵒᵖ X) (s q) = q) :
    letI := ProperSMul.orbitRelQuotientChartedSpace IG Gᵐᵒᵖ IX X
    ContMDiffOn IX (𝓘(ℝ, ProperSMul.QuotientModelSpace E E').prod IG) ∞
        (orbitTrivializationOfSectionUnop U hU s hs.continuousOn hsec)
        (orbitTrivializationOfSectionUnop U hU s hs.continuousOn hsec).source ∧
      ContMDiffOn (𝓘(ℝ, ProperSMul.QuotientModelSpace E E').prod IG) IX ∞
        (orbitTrivializationOfSectionUnop U hU s hs.continuousOn hsec).toOpenPartialHomeomorph.symm
        (orbitTrivializationOfSectionUnop U hU s hs.continuousOn hsec).target := by
  let := ProperSMul.orbitRelQuotientChartedSpace IG Gᵐᵒᵖ IX X
  set e := orbitTrivializationOfSectionUnop (G := G) U hU s hs.continuousOn hsec
  set Φ := fun p : orbitRel.Quotient Gᵐᵒᵖ X × G ↦ op p.2 • s p.1
  have htarget : e.target = U ×ˢ univ := by
    rw [e.target_eq, orbitTrivializationOfSectionUnop_baseSet]
  have hsymm : EqOn e.toOpenPartialHomeomorph.symm Φ (U ×ˢ univ) := fun p hp ↦
    orbitTrivializationOfSectionUnop_symm_apply hp.1 p.2
  have hloc := isLocalDiffeomorphOn_op_smul_section (IG := IG) hU hs hsec
  refine ⟨fun x hx ↦ ?_, htarget ▸ hloc.contMDiffOn.congr hsymm⟩
  have : Nonempty (orbitRel.Quotient Gᵐᵒᵖ X × G) := ⟨e x⟩
  have hinjOn : InjOn Φ (U ×ˢ univ) :=
    (htarget ▸ e.toPartialEquiv.symm_source ▸ e.toPartialEquiv.symm.injOn).congr hsymm
  have himage : Φ '' (U ×ˢ univ) = e.source := by
    rw [← hsymm.image_eq, ← htarget]
    exact e.toPartialEquiv.symm_image_target_eq_source
  have hinv : ∀ y ∈ e.source, Function.invFunOn Φ (U ×ˢ univ) y = e y := fun y hy ↦ by
    have hm : e y ∈ U ×ˢ univ := htarget ▸ e.map_source hy
    calc Function.invFunOn Φ (U ×ˢ univ) y = Function.invFunOn Φ (U ×ˢ univ) (Φ (e y)) := by
          rw [← hsymm hm]
          exact congrArg _ (e.left_inv hy).symm
      _ = e y := hinjOn.leftInvOn_invFunOn hm
  have key := hloc.contMDiffOn_invFunOn (hU.prod isOpen_univ) hinjOn
  rw [himage] at key
  exact (key.congr fun y hy ↦ (hinv y hy).symm) x hx

end orbitFiber

end Smooth

/-! ### The principal bundle of a free proper smooth action -/

section Bundle

attribute [local instance] MulOpposite.chartedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (IG : ModelWithCorners ℝ E H)
  (G : Type*) [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup IG ∞ G]
  [ContinuousInv G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] (IX : ModelWithCorners ℝ E' H') [IX.Boundaryless]
  (X : Type*) [TopologicalSpace X] [ChartedSpace H' X] [IsManifold IX ∞ X]
  [MulAction Gᵐᵒᵖ X] [ContMDiffSMul IG IX ∞ Gᵐᵒᵖ X] [ProperSMul Gᵐᵒᵖ X] [IsCancelSMul Gᵐᵒᵖ X]

namespace orbitFiber

omit [ContinuousInv G] in
/-- Through every orbit passes a smooth local section of the orbit projection, for the slice
charts of the orbit space. -/
private theorem exists_section (q : orbitRel.Quotient Gᵐᵒᵖ X) :
    letI := ProperSMul.orbitRelQuotientChartedSpace IG Gᵐᵒᵖ IX X
    ∃ Us : Set (orbitRel.Quotient Gᵐᵒᵖ X) × (orbitRel.Quotient Gᵐᵒᵖ X → X),
      IsOpen Us.1 ∧ q ∈ Us.1 ∧
      ContMDiffOn 𝓘(ℝ, ProperSMul.QuotientModelSpace E E') IX ∞ Us.2 Us.1 ∧
      ∀ q' ∈ Us.1, Quotient.mk (orbitRel Gᵐᵒᵖ X) (Us.2 q') = q' := by
  obtain ⟨U, hU, hqU, s, -, hs, hsec⟩ :=
    ProperSMul.exists_contMDiffOn_section_quotientMk (I := IG) (G := Gᵐᵒᵖ) (I' := IX) q.out
  rw [Quotient.out_eq] at hqU
  exact ⟨(U, s), hU, hqU, hs, hsec⟩

/-- The atlas of the orbit projection of a free proper smooth action of `Gᵐᵒᵖ`, with model fibre
`G`: at each orbit `q`, the trivialization from a smooth local section of the orbit projection over
a neighbourhood of `q`, for the slice charts `ProperSMul.orbitRelQuotientChartedSpace` of the orbit
space. -/
noncomputable def atlas : MapFiber.Atlas G (Quotient.mk (orbitRel Gᵐᵒᵖ X)) :=
  letI := ProperSMul.orbitRelQuotientChartedSpace IG Gᵐᵒᵖ IX X
  { trivAt q :=
      orbitTrivializationOfSectionUnop _ (exists_section IG G IX X q).choose_spec.1 _
        (exists_section IG G IX X q).choose_spec.2.2.1.continuousOn
        (exists_section IG G IX X q).choose_spec.2.2.2
    mem_baseSet_trivAt q := by
      rw [orbitTrivializationOfSectionUnop_baseSet]
      exact (exists_section IG G IX X q).choose_spec.2.1 }

/-- The trivialization of `orbitFiber.atlas` at an orbit `q` is the trivialization
`orbitTrivializationOfSectionUnop` of a section of the orbit projection over an open
neighbourhood of `q` that is smooth for the slice charts of the orbit space. -/
theorem exists_atlas_trivAt_eq (q : orbitRel.Quotient Gᵐᵒᵖ X) :
    letI := ProperSMul.orbitRelQuotientChartedSpace IG Gᵐᵒᵖ IX X
    ∃ (U : Set (orbitRel.Quotient Gᵐᵒᵖ X)) (hU : IsOpen U) (s : orbitRel.Quotient Gᵐᵒᵖ X → X)
      (hs : ContMDiffOn 𝓘(ℝ, ProperSMul.QuotientModelSpace E E') IX ∞ s U)
      (hsec : ∀ q' ∈ U, Quotient.mk (orbitRel Gᵐᵒᵖ X) (s q') = q'),
      q ∈ U ∧ (atlas IG G IX X).trivAt q =
        orbitTrivializationOfSectionUnop U hU s hs.continuousOn hsec := by
  obtain ⟨hU, hq, hs, hsec⟩ := (exists_section IG G IX X q).choose_spec
  exact ⟨_, hU, _, hs, hsec, hq, rfl⟩

/-- **The orbit bundle of a free proper smooth action is principal.** For a free proper smooth
right action of a Lie group `G` on a boundaryless manifold `X`, the orbits, with the fibre bundle
structure of `orbitFiber.atlas` and the right action of `G` on each orbit, form a principal
`G`-bundle over the orbit space. -/
theorem principalBundle :
    letI := (atlas IG G IX X).fiberBundle
    PrincipalBundle G (orbitFiber Gᵐᵒᵖ X) := by
  let := (atlas IG G IX X).fiberBundle
  refine ⟨fun e he ↦ ?_⟩
  obtain ⟨q, rfl⟩ := ((atlas IG G IX X).mem_trivializationAtlas_iff e).1 he.out
  obtain ⟨U, hU, s, hs, hsec, -, h⟩ := exists_atlas_trivAt_eq IG G IX X q
  rw [h, ← trivializationOfSection_def]
  infer_instance

/-- **The atlas of the orbit projection is smooth.** For a free proper smooth right action of a Lie
group `G` on a boundaryless manifold `X`, each trivialization of `orbitFiber.atlas` is a smooth
diffeomorphism from its source, an open set of `X`, onto its target in the product of the orbit
space, with its slice charts, and `G`. So `TauCeti.MapFiber.Atlas.contMDiffFiberBundle` makes the
fibres of the orbit projection a smooth fibre bundle, and
`TauCeti.MapFiber.Atlas.totalSpaceDiffeomorph` identifies its total space with `X`. -/
theorem isContMDiff_atlas :
    letI := ProperSMul.orbitRelQuotientChartedSpace IG Gᵐᵒᵖ IX X
    (atlas IG G IX X).IsContMDiff ∞ 𝓘(ℝ, ProperSMul.QuotientModelSpace E E') IG IX := by
  let := ProperSMul.orbitRelQuotientChartedSpace IG Gᵐᵒᵖ IX X
  have key (q : orbitRel.Quotient Gᵐᵒᵖ X) :
      ContMDiffOn IX (𝓘(ℝ, ProperSMul.QuotientModelSpace E E').prod IG) ∞
          ((atlas IG G IX X).trivAt q) ((atlas IG G IX X).trivAt q).source ∧
        ContMDiffOn (𝓘(ℝ, ProperSMul.QuotientModelSpace E E').prod IG) IX ∞
          ((atlas IG G IX X).trivAt q).toOpenPartialHomeomorph.symm
          ((atlas IG G IX X).trivAt q).target := by
    obtain ⟨U, hU, s, hs, hsec, -, h⟩ := exists_atlas_trivAt_eq IG G IX X q
    rw [h]
    exact contMDiffOn_orbitTrivializationOfSectionUnop hU hs hsec
  exact ⟨fun q ↦ (key q).1, fun q ↦ (key q).2⟩

end orbitFiber

end Bundle

end SymplecticGeometry

end
