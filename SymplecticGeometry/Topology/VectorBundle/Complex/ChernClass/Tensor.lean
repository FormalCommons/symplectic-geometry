/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Topology.VectorBundle.Complex.ChernClass.Basic
public import TauCeti.Topology.VectorBundle.TensorProduct.Basic
import SymplecticGeometry.Topology.VectorBundle.Orientation.Complex.Tensor
import SymplecticGeometry.Analysis.Normed.Module.TensorProduct.ProjectiveSeminorm

/-!
# The first Chern class of a tensor product of complex line bundles

For complex line bundles `L` and `L'` over a compact normal base, such as a compact Hausdorff one,
the first Chern class of Tau Ceti's tensor product bundle `L ⊗ L'` is `c₁(L) + c₁(L')`
(`SymplecticGeometry.Bundle.chernClass_one_tensorProduct`). This is the additivity of the Euler
class, `TauCeti.complexEulerClass_tensorProduct`, read through
`SymplecticGeometry.Bundle.chernClass_one_eq_complexEulerClass`.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press (1974), §14.
* [R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §20 (the first
  Chern class of a line bundle as its Euler class).
-/

public section

open Bundle Module TauCeti
open scoped TensorProduct TauCeti.ModuleTopology

namespace SymplecticGeometry.Bundle

variable {B : Type} [TopologicalSpace B] [CompactSpace B] [NormalSpace B]
  {G : Type} [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  {L : B → Type} [TopologicalSpace (TotalSpace G L)] [∀ b, AddCommGroup (L b)]
  [∀ b, Module ℝ (L b)] [∀ b, Module ℂ (L b)] [∀ b, IsScalarTower ℝ ℂ (L b)]
  [∀ b, TopologicalSpace (L b)] [FiberBundle G L] [VectorBundle ℂ G L]
  {G' : Type} [NormedAddCommGroup G'] [NormedSpace ℂ G'] [FiniteDimensional ℂ G']
  {L' : B → Type} [TopologicalSpace (TotalSpace G' L')] [∀ b, AddCommGroup (L' b)]
  [∀ b, Module ℝ (L' b)] [∀ b, Module ℂ (L' b)] [∀ b, IsScalarTower ℝ ℂ (L' b)]
  [∀ b, TopologicalSpace (L' b)] [FiberBundle G' L'] [VectorBundle ℂ G' L']

/-- **The first Chern class of a tensor product of complex line bundles.** For complex line
bundles `L` and `L'` over a compact normal base, the first Chern class of Tau Ceti's tensor
product bundle `L ⊗ L'` is `c₁(L) + c₁(L')`. -/
theorem chernClass_one_tensorProduct (hG : finrank ℂ G = 1) (hG' : finrank ℂ G' = 1) :
    chernClass (ProjectiveTensor ℂ G G') (fun b ↦ L b ⊗[ℂ] L' b) 1 =
      chernClass G L 1 + chernClass G' L' 1 := by
  rw [chernClass_one_eq_complexEulerClass _ _ hG, chernClass_one_eq_complexEulerClass _ _ hG',
    chernClass_one_eq_complexEulerClass _ _ (by simp [hG, hG']), ← map_add,
    complexEulerClass_tensorProduct hG hG' .of_compactSpace .of_compactSpace]

end SymplecticGeometry.Bundle

end
