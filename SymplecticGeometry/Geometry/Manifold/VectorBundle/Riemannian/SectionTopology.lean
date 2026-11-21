/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Homotopy.Contractible
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.SectionTopology
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Existence

/-!
# Contractibility of the space of bundle metrics

Over a Hausdorff σ-compact base modelled on a finite-dimensional space, the `Cⁿ` metrics on a
real vector bundle of finite rank form a contractible space for Tau Ceti's frame topology
(`Bundle.ContMDiffRiemannianMetric.contractibleSpace_frameTopology`): the space is nonempty by
Tau Ceti's `TauCeti.nonempty_contMDiffRiemannianMetric`, and the straight line
`(t, g) ↦ (1 - t) g + t g₀` to a fixed metric `g₀` is a homotopy from the identity to a constant
map, continuous by Tau Ceti's `continuous_convexCombination_frameTopology`.

## Main results

* `Bundle.ContMDiffRiemannianMetric.contractibleSpace_frameTopology`

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.6
-/

public section

open Bundle TopologicalSpace TauCeti
open scoped Manifold ContDiff

namespace Bundle.ContMDiffRiemannianMetric

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : ℕ∞}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B] [T2Space B] [SigmaCompactSpace B]
  [IsManifold IB ∞ B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, ContinuousConstSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle n F V IB]
  {ι : Type*}
  (e : ι → Trivialization (symmetricBilinearMaps ℝ F ℝ)
    (π (symmetricBilinearMaps ℝ F ℝ) (fun x ↦ symmetricBilinearMaps ℝ (V x) ℝ)))
  [∀ i, MemTrivializationAtlas (e i)]
  (U : ι → Opens B) (hU : ∀ i, (U i : Set B) ⊆ (e i).baseSet)

/-- Over a Hausdorff σ-compact base modelled on a finite-dimensional space, the `Cⁿ` metrics on a
vector bundle of finite rank form a contractible space for the frame topology, in any frames. In
particular such metrics exist. -/
theorem contractibleSpace_frameTopology :
    letI := frameTopology IB n e U hU
    ContractibleSpace (ContMDiffRiemannianMetric IB n F V) := by
  let _ := frameTopology IB n e U hU
  obtain ⟨g₀⟩ := TauCeti.nonempty_contMDiffRiemannianMetric (IB := IB) (n := n) (F := F) (E := V)
  refine (contractible_iff_id_nullhomotopic _).2 ⟨g₀, ⟨{
    toFun := fun p ↦ p.2.convexCombination g₀ p.1
    continuous_toFun := (continuous_convexCombination_frameTopology e U hU).comp
      ((continuous_snd.prodMk continuous_const).prodMk continuous_fst)
    map_zero_left := fun g ↦ convexCombination_zero g g₀
    map_one_left := fun g ↦ convexCombination_one g g₀ }⟩⟩

end Bundle.ContMDiffRiemannianMetric

end
