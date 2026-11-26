/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SMul
public import SymplecticGeometry.Geometry.Manifold.FiberBundle.MapFiber
public import TauCeti.Geometry.Diffeomorphism.Group
public import TauCeti.Topology.FiberBundle.Associated.Basic
import SymplecticGeometry.Topology.FiberBundle.ChangeModelFiber

/-!
# Structure groups of atlases of a map

Let `A` and `A'` be atlases of a map `proj : M → B` with model fibre a manifold `F`
(`TauCeti.MapFiber.Atlas`), and let `H` be a subgroup of the group of `C^n` diffeomorphisms of
`F`. The two atlases are *compatible through `H`* when every coordinate change from a chart of `A`
to a chart of `A'`, over a point of both base sets, is (the underlying map of) an element of `H`.
An atlas *has structure group `H`* when it is compatible with itself through `H`.

Compatibility through `H` is symmetric and transitive, so it is an equivalence relation on the
atlases with structure group `H`. Any two `C^n` atlases are compatible through the whole group.
The atlas of the charted total space of an associated bundle `P ×_G F` has structure group `H` as
soon as `H` contains the action of every element of `G`, since its coordinate changes act on `F`
by elements of `G`.

A reduction of the structure group of `A` from `H` to a subgroup `K` is an atlas `A'` with
`A'.HasStructureGroup K` and `A.CoordChangeMem A' H`.

## Main definitions

* `TauCeti.MapFiber.Atlas.CoordChangeMem A A' H`: the coordinate changes from `A` to `A'` lie
  in `H`.
* `TauCeti.MapFiber.Atlas.HasStructureGroup A H`: the atlas `A` has structure group `H`.

## Main results

* `TauCeti.MapFiber.Atlas.coordChangeMem_top`: two `C^n` atlases are compatible through the group
  of all `C^n` diffeomorphisms.
* `TauCeti.MapFiber.Atlas.CoordChangeMem.symm` and `TauCeti.MapFiber.Atlas.CoordChangeMem.trans`:
  compatibility through `H` is symmetric and transitive.
* `TauCeti.AssociatedBundle.hasStructureGroup_mapFiberAtlas`: the atlas of an associated bundle
  has structure group any subgroup containing the action of its structure group.

## Implementation notes

Transitivity goes through the chart of the middle atlas at the point itself, with Mathlib's
`Bundle.Trivialization.coordChange_coordChange`. The coordinate changes of an associated bundle are
Tau Ceti's `TauCeti.AssociatedBundle.coordChange_trivializationAt`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §6.1.
* N. Steenrod, *The Topology of Fibre Bundles*, Princeton University Press, 1951, §2 (coordinate
  bundles with a structure group, and their equivalence).
-/

public section

open Bundle Function Set
open scoped Manifold ContDiff

namespace TauCeti.MapFiber.Atlas

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ∞ω}
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace 𝕜 EF] {HF : Type*} [TopologicalSpace HF]
  {IF : ModelWithCorners 𝕜 EF HF} {F : Type*} [TopologicalSpace F] [ChartedSpace HF F]
  {B : Type*} [TopologicalSpace B] {M : Type*} [TopologicalSpace M] {proj : M → B}
  {A A' A'' : Atlas F proj} {H K : Subgroup (F ≃ₘ^n⟮IF, IF⟯ F)}

/-! ### Compatibility through a subgroup -/

/-- Two atlases `A` and `A'` of `proj` are *compatible through* a subgroup `H` of the `C^n`
diffeomorphisms of the fibre when, for all charts `A.trivAt b` and `A'.trivAt b'` and every point
`x` of both base sets, the coordinate change from the first to the second over `x` is an element
of `H`. -/
def CoordChangeMem (A A' : Atlas F proj) (H : Subgroup (F ≃ₘ^n⟮IF, IF⟯ F)) : Prop :=
  ∀ b b' x, x ∈ (A.trivAt b).baseSet → x ∈ (A'.trivAt b').baseSet →
    ∃ φ ∈ H, ⇑φ = (A.trivAt b).coordChange (A'.trivAt b') x

theorem coordChangeMem_iff :
    A.CoordChangeMem A' H ↔ ∀ b b' x, x ∈ (A.trivAt b).baseSet → x ∈ (A'.trivAt b').baseSet →
      ∃ φ ∈ H, ⇑φ = (A.trivAt b).coordChange (A'.trivAt b') x :=
  Iff.rfl

/-- An atlas `A` *has structure group* `H` when its coordinate changes are elements of `H`. -/
def HasStructureGroup (A : Atlas F proj) (H : Subgroup (F ≃ₘ^n⟮IF, IF⟯ F)) : Prop :=
  A.CoordChangeMem A H

theorem hasStructureGroup_iff :
    A.HasStructureGroup H ↔ ∀ b b' x, x ∈ (A.trivAt b).baseSet → x ∈ (A.trivAt b').baseSet →
      ∃ φ ∈ H, ⇑φ = (A.trivAt b).coordChange (A.trivAt b') x :=
  Iff.rfl

theorem hasStructureGroup_iff_coordChangeMem : A.HasStructureGroup H ↔ A.CoordChangeMem A H :=
  Iff.rfl

/-- Compatibility through `H` passes to a larger subgroup. -/
theorem CoordChangeMem.mono (h : A.CoordChangeMem A' H) (hHK : H ≤ K) : A.CoordChangeMem A' K :=
  fun b b' x hb hb' ↦ (h b b' x hb hb').imp fun _ hφ ↦ ⟨hHK hφ.1, hφ.2⟩

/-- An atlas with structure group `H` has every larger structure group. -/
theorem HasStructureGroup.mono (h : A.HasStructureGroup H) (hHK : H ≤ K) :
    A.HasStructureGroup K :=
  hasStructureGroup_iff_coordChangeMem.2 (hasStructureGroup_iff_coordChangeMem.1 h |>.mono hHK)

/-- Compatibility through `H` is symmetric: the coordinate changes from `A'` to `A` are the
inverses of those from `A` to `A'`. -/
theorem CoordChangeMem.symm (h : A.CoordChangeMem A' H) : A'.CoordChangeMem A H := by
  intro b' b x hb' hb
  obtain ⟨φ, hφH, hφ⟩ := h b b' x hb hb'
  refine ⟨φ⁻¹, inv_mem hφH, funext fun v ↦ ?_⟩
  rw [Diffeomorph.coe_inv, ← φ.symm_apply_apply ((A'.trivAt b').coordChange (A.trivAt b) x v), hφ,
    Trivialization.coordChange_coordChange _ _ _ hb' hb,
    Trivialization.coordChange_same_apply _ hb']

/-- Compatibility through `H` is transitive: a coordinate change from `A` to `A''` over `x` is the
composite of those through the chart of `A'` at `x`. -/
theorem CoordChangeMem.trans (h : A.CoordChangeMem A' H) (h' : A'.CoordChangeMem A'' H) :
    A.CoordChangeMem A'' H := by
  intro b b'' x hb hb''
  obtain ⟨φ, hφH, hφ⟩ := h b x x hb (A'.mem_baseSet_trivAt x)
  obtain ⟨ψ, hψH, hψ⟩ := h' x b'' x (A'.mem_baseSet_trivAt x) hb''
  refine ⟨ψ * φ, mul_mem hψH hφH, funext fun v ↦ ?_⟩
  rw [Diffeomorph.coe_mul, comp_apply, hφ, hψ,
    Trivialization.coordChange_coordChange _ _ _ hb (A'.mem_baseSet_trivAt x)]

/-! ### Smooth atlases -/

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*}
  [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB} [ChartedSpace HB B]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM} [ChartedSpace HM M]

/-- **Smooth atlases are compatible through the whole group.** The coordinate changes between two
`C^n` atlases are `C^n` diffeomorphisms of the fibre. -/
theorem coordChangeMem_top (hA : A.IsContMDiff n IB IF IM) (hA' : A'.IsContMDiff n IB IF IM) :
    A.CoordChangeMem A' (⊤ : Subgroup (F ≃ₘ^n⟮IF, IF⟯ F)) := fun b b' _ hb hb' ↦
  ⟨(A.trivAt b).coordChangeDiffeomorph (A'.trivAt b') (hA.contMDiffOn_trivAt b)
      (hA.contMDiffOn_trivAt_symm b) (hA'.contMDiffOn_trivAt b') (hA'.contMDiffOn_trivAt_symm b')
      hb hb', Subgroup.mem_top _, Trivialization.coe_coordChangeDiffeomorph ..⟩

/-- A `C^n` atlas has the group of all `C^n` diffeomorphisms of the fibre as structure group. -/
theorem IsContMDiff.hasStructureGroup_top (hA : A.IsContMDiff n IB IF IM) :
    A.HasStructureGroup (⊤ : Subgroup (F ≃ₘ^n⟮IF, IF⟯ F)) :=
  hasStructureGroup_iff_coordChangeMem.2 (coordChangeMem_top hA hA)

end TauCeti.MapFiber.Atlas

/-! ### Associated bundles -/

namespace TauCeti.AssociatedBundle

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ∞ω} {B : Type*} [TopologicalSpace B]
  {EG : Type*} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG] {HG : Type*} [TopologicalSpace HG]
  (IG : ModelWithCorners 𝕜 EG HG) {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace HG G]
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace 𝕜 EF] {HF : Type*} [TopologicalSpace HF]
  {IF : ModelWithCorners 𝕜 EF HF} {F : Type*} [TopologicalSpace F] [ChartedSpace HF F]
  [MulAction G F] [ContinuousSMul G F] [ContMDiffSMul IG IF n G F]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]

/-- **The structure group of an associated bundle.** If a subgroup `H` of the `C^n`
diffeomorphisms of `F` contains the action of every element of `G`, then the atlas of the charted
total space of the associated bundle `P ×_G F` has structure group `H`: its coordinate changes act
by the transition functions of `P`. -/
theorem hasStructureGroup_mapFiberAtlas {H : Subgroup (F ≃ₘ^n⟮IF, IF⟯ F)}
    (hH : ∀ g : G, Diffeomorph.smul IG IF n g ∈ H) :
    (ManifoldTotalSpace.mapFiberAtlas F (AssociatedBundle G P F)).HasStructureGroup H := by
  rw [MapFiber.Atlas.hasStructureGroup_iff]
  intro b b' x hb hb'
  rw [ManifoldTotalSpace.trivAt_mapFiberAtlas, Trivialization.compHomeomorph_baseSet,
    baseSet_trivializationAt] at hb hb'
  refine ⟨Diffeomorph.smul IG IF n
    ((trivializationAt G P b).coordChange (trivializationAt G P b') x 1), hH _, funext fun v ↦ ?_⟩
  rw [ManifoldTotalSpace.coordChange_mapFiberAtlas, coordChange_trivializationAt hb hb',
    Diffeomorph.smul_apply]

end TauCeti.AssociatedBundle

end
