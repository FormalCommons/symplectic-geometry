/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.FiberBundle.StructureGroup
public import TauCeti.Topology.FiberBundle.Trivialization

/-!
# The product atlas

For topological spaces `B` and `F`, the first projection `Prod.fst : B × F → B` is trivialized
over all of `B` by the identity of `B × F`. The atlas `TauCeti.MapFiber.Atlas.productAtlas B F`
takes this trivialization as its chart at every point of `B`. It is the atlas of the trivial
bundle with fibre `F` over `B`, against which the other bundles over `B` are compared: a bundle
is trivial when it is isomorphic to `Prod.fst` with this atlas.

For manifolds `B` and `F` the atlas is `C^n` for every `n`, and since every coordinate change is
the identity of `F`, it has structure group `H` for every subgroup `H` of the `C^n`
diffeomorphisms of `F`.

## Main definitions

* `TauCeti.MapFiber.Atlas.productAtlas B F`: the atlas of `Prod.fst : B × F → B` whose every chart
  is the identity of `B × F`.

## Main results

* `TauCeti.MapFiber.Atlas.isContMDiff_productAtlas`: the product atlas is `C^n`.
* `TauCeti.MapFiber.Atlas.hasStructureGroup_productAtlas`: the product atlas has structure group
  `H` for every subgroup `H`.

## Implementation notes

The chart is Tau Ceti's `Homeomorph.toTrivialization` of `Homeomorph.refl (B × F)`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §6.2.
-/

public section

open Bundle Set
open scoped Manifold ContDiff

namespace TauCeti.MapFiber.Atlas

variable (B F : Type*) [TopologicalSpace B] [TopologicalSpace F]

/-- The *product atlas* of the first projection `Prod.fst : B × F → B`: its chart at every point
of `B` is the identity of `B × F`, a trivialization over all of `B`. -/
def productAtlas : Atlas F (Prod.fst : B × F → B) where
  trivAt _ := (Homeomorph.refl (B × F)).toTrivialization (proj := Prod.fst) fun _ ↦ rfl
  mem_baseSet_trivAt _ := (Set.ext_iff.1 (Homeomorph.toTrivialization_baseSet _ _) _).2 (mem_univ _)

theorem trivAt_productAtlas (b : B) :
    (productAtlas B F).trivAt b =
      (Homeomorph.refl (B × F)).toTrivialization (proj := Prod.fst) fun _ ↦ rfl :=
  (rfl)

variable {B F}

/-- Every chart of the product atlas is the identity of `B × F`. -/
@[simp]
theorem coe_trivAt_productAtlas (b : B) : ⇑((productAtlas B F).trivAt b) = id := by
  rw [trivAt_productAtlas]
  exact (Homeomorph.coe_toTrivialization _ _).trans (Homeomorph.refl_apply _)

/-- The inverse of every chart of the product atlas is the identity of `B × F`. -/
@[simp]
theorem coe_trivAt_productAtlas_symm (b : B) :
    ⇑((productAtlas B F).trivAt b).toOpenPartialHomeomorph.symm = id := by
  rw [trivAt_productAtlas]
  exact (Homeomorph.coe_toTrivialization_symm _ _).trans (by
    rw [Homeomorph.refl_symm, Homeomorph.refl_apply])

/-- Every chart of the product atlas trivializes `Prod.fst` over all of `B`. -/
@[simp]
theorem baseSet_trivAt_productAtlas (b : B) : ((productAtlas B F).trivAt b).baseSet = univ := by
  rw [trivAt_productAtlas]
  exact Homeomorph.toTrivialization_baseSet _ _

/-- Every coordinate change of the product atlas is the identity of `F`. -/
@[simp]
theorem coordChange_trivAt_productAtlas (b b' x : B) :
    ((productAtlas B F).trivAt b).coordChange ((productAtlas B F).trivAt b') x = id := by
  rw [trivAt_productAtlas B F b', ← trivAt_productAtlas B F b]
  exact Trivialization.coordChange_same _ (by rw [baseSet_trivAt_productAtlas]; exact mem_univ x)

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ∞ω}
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [ChartedSpace HB B]
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace 𝕜 EF] {HF : Type*} [TopologicalSpace HF]
  {IF : ModelWithCorners 𝕜 EF HF} [ChartedSpace HF F]

/-- The product atlas of `Prod.fst : B × F → B` is `C^n` for the product manifold structure on
`B × F`: its charts and their inverses are the identity. -/
theorem isContMDiff_productAtlas :
    (productAtlas B F).IsContMDiff n IB IF (IB.prod IF) where
  contMDiffOn_trivAt b := by
    rw [coe_trivAt_productAtlas]
    exact contMDiffOn_id
  contMDiffOn_trivAt_symm b := by
    rw [coe_trivAt_productAtlas_symm]
    exact contMDiffOn_id

/-- The product atlas has structure group `H` for every subgroup `H` of the `C^n` diffeomorphisms
of `F`, since each of its coordinate changes is the identity element. -/
theorem hasStructureGroup_productAtlas (H : Subgroup (F ≃ₘ^n⟮IF, IF⟯ F)) :
    (productAtlas B F).HasStructureGroup H := by
  rw [hasStructureGroup_iff]
  intro b b' x _ _
  exact ⟨1, one_mem H, by rw [coordChange_trivAt_productAtlas, Diffeomorph.coe_one]⟩

end TauCeti.MapFiber.Atlas

end
