/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Algebra.Module.LocallyConvex
public import Mathlib.Topology.Metrizable.Basic
public import TauCeti.Topology.CWComplex.Classical.CWType
import Mathlib.Topology.Homotopy.Affine
import SymplecticGeometry.AlgebraicTopology.Homotopy.Domination
import SymplecticGeometry.AlgebraicTopology.SimplicialComplex.Realization.Convex
import SymplecticGeometry.AlgebraicTopology.SimplicialComplex.Realization.PartitionOfUnity
import SymplecticGeometry.Topology.MetricSpace.PartitionOfUnity
import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.CWComplex.Basic
import TauCeti.Topology.MetricSpace.ContinuousRadius

/-!
# Open subsets of convex sets have CW type

In a metrizable locally convex real topological vector space `E`, the intersection `C ∩ U` of a
convex set `C` with an open set `U` has the homotopy type of a CW complex
(`Convex.cwType_inter`).

The proof is the nerve argument of Milnor and Dugundji. Put `O := C ∩ U` and choose a metric on
it. Every point `y` of `O` has a relatively open neighbourhood `C ∩ V y`, with `V y` open and
convex, that is a convex subset of `O`. Tau Ceti's continuous radius
`Topology.IsInducing.exists_continuous_radius_subordinate` gives a positive continuous `r` on `O`
such that the ball of radius `2 * r x` about each `x` lies in one of these convex sets. Let `ρ` be
a partition of unity on `O`, indexed by `O`, subordinate to the balls `B(x, r x)`. If the functions
`ρ x₀, …, ρ xₖ` are all nonzero at `z`, pick `xⱼ` with the largest radius: the triangle inequality
puts `z` and every `xᵢ` in the ball `B(xⱼ, 2 * r xⱼ)`, hence in one convex subset of `O`
(`PartitionOfUnity.IsSubordinate.exists_mem_forall_mem_of_ne_zero`). So the map `ψ` from the
realization of the nerve of `ρ` to `O`, the linear extension of the inclusion of the vertices, is
well defined (`AbstractSimplicialComplex.linearExtension_mem_of_convex`), and the segment from
`ψ (ρ.toNerve x)` to `x`, the affine homotopy `ContinuousMap.Homotopy.affine`, lies in
`O`. Thus `O` is dominated by the realization, a CW complex, and has CW type by
`TauCeti.CWType.of_comp_homotopic_id`.

## Main results

* `Convex.cwType_inter`: in a metrizable locally convex real topological vector space, the
  intersection of a convex set with an open set has CW type.

## References

* J. Milnor, *On spaces having the homotopy type of a CW-complex*, Trans. Amer. Math. Soc. 90
  (1959), 272–280.
* J. Dugundji, *An extension of Tietze's theorem*, Pacific J. Math. 1 (1951), 353–367.
-/

public section

open Set Metric TopologicalSpace AbstractSimplicialComplex

universe u

namespace Convex

/-- **Open subsets of convex sets have CW type.** In a metrizable locally convex real topological
vector space, the intersection of a convex set `C` with an open set `U` has the homotopy type of a
CW complex. -/
theorem cwType_inter {E : Type u} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [LocallyConvexSpace ℝ E] [MetrizableSpace E] {C U : Set E}
    (hC : Convex ℝ C) (hU : IsOpen U) : TauCeti.CWType ↥(C ∩ U) := by
  -- Every point of `O = C ∩ U` has an open convex neighbourhood `V y` inside `U`.
  have hloc (y : ↥(C ∩ U)) : ∃ V : Set E, IsOpen V ∧ Convex ℝ V ∧ (y : E) ∈ V ∧ V ⊆ U := by
    obtain ⟨N, ⟨hN, hNc⟩, hNU⟩ :=
      (LocallyConvexSpace.convex_basis (𝕜 := ℝ) (y : E)).mem_iff.1 (hU.mem_nhds y.property.2)
    exact ⟨interior N, isOpen_interior, hNc.interior, mem_interior_iff_mem_nhds.2 hN,
      interior_subset.trans hNU⟩
  choose V hVo hVc hyV hVU using hloc
  let := pseudoMetrizableSpacePseudoMetric ↥(C ∩ U)
  obtain ⟨r, hr0, hr⟩ := Topology.IsInducing.id.exists_continuous_radius_subordinate
    (fun y : ↥(C ∩ U) => {x : ↥(C ∩ U) | (x : E) ∈ V y})
    (fun y => (hVo y).preimage continuous_subtypeVal) (fun x => ⟨x, hyV x⟩)
    (fun _ => (1 : ℝ)) fun _ => one_pos
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ
    (fun x : ↥(C ∩ U) => ball x (r x)) (fun _ => isOpen_ball)
    fun x _ => mem_iUnion.2 ⟨x, mem_ball_self (hr0 x)⟩
  -- The ball of radius `2 * r x` about each `x` lies in one of the convex sets `C ∩ V y`.
  have hS (x : ↥(C ∩ U)) : ∃ y, ball x (2 * r x) ⊆ {x : ↥(C ∩ U) | (x : E) ∈ V y} := by
    obtain ⟨y, -, -, hy⟩ := hr x
    exact ⟨y, fun z hz => hy z (by rw [dist_comm]; exact hz)⟩
  -- If the functions `ρ i`, `i ∈ t`, are nonzero at `z`, then `z` and the points of `t` lie in
  -- one convex subset of `O`.
  have key (z : ↥(C ∩ U)) (t : Finset ↥(C ∩ U)) (ht : t.Nonempty) (hz : ∀ i ∈ t, ρ i z ≠ 0) :
      ∃ S : Set E, Convex ℝ S ∧ S ⊆ C ∩ U ∧ (z : E) ∈ S ∧ ∀ i ∈ t, (i : E) ∈ S := by
    obtain ⟨y, hzy, hty⟩ := hρ.exists_mem_forall_mem_of_ne_zero hS ht hz
    exact ⟨C ∩ V y, hC.inter (hVc y), inter_subset_inter_right _ (hVU y),
      ⟨z.property.1, hzy⟩, fun i hi => ⟨i.property.1, hty i hi⟩⟩
  -- Hence the points of every face of the nerve lie in one convex subset of `O`.
  have hface (t : Finset ↥(C ∩ U)) (ht : t ∈ ρ.nerve) :
      ∃ S : Set E, Convex ℝ S ∧ S ⊆ C ∩ U ∧ ∀ i ∈ t, (i : E) ∈ S := by
    rcases ρ.mem_nerve_iff.1 ht with ⟨ht, z, hz⟩ | ⟨i, rfl⟩
    · obtain ⟨S, hS, hSO, -, htS⟩ := key z t ht hz
      exact ⟨S, hS, hSO, htS⟩
    · exact ⟨{(i : E)}, convex_singleton _, singleton_subset_iff.2 i.property, by simp⟩
  -- The map from the realization of the nerve, affine on each simplex.
  have hmem (p : ρ.nerve.Realization) : ρ.nerve.linearExtension Subtype.val p ∈ C ∩ U := by
    obtain ⟨S, hS, hSO, htS⟩ := hface _ (support_mem _ p)
    exact hSO (linearExtension_mem_of_convex hS _ p htS)
  let ψ : C(ρ.nerve.Realization, ↥(C ∩ U)) :=
    ⟨fun p => ⟨_, hmem p⟩, (continuous_linearExtension _).subtype_mk hmem⟩
  -- The straight-line homotopy from `ψ ∘ ρ.toNerve` to the identity stays in `O`.
  let F : C(↥(C ∩ U), E) := ⟨_, continuous_subtypeVal⟩
  let G := ContinuousMap.Homotopy.affine (F.comp (ψ.comp ρ.toNerve)) F
  have hseg (p : unitInterval × ↥(C ∩ U)) : G p ∈ C ∩ U := by
    obtain ⟨i, hi⟩ := ρ.exists_pos (mem_univ p.2)
    obtain ⟨S, hS, hSO, hxS, htS⟩ := key p.2 (ρ.finsupport p.2)
      ⟨i, (ρ.mem_finsupport p.2).2 hi.ne'⟩ fun j hj => (ρ.mem_finsupport p.2).1 hj
    refine hSO (hS.lineMap_mem ?_ hxS p.1.property)
    exact linearExtension_mem_of_convex hS _ _ (by simpa using htS)
  let H : (ψ.comp ρ.toNerve).Homotopy (ContinuousMap.id _) :=
    { toFun := fun p => ⟨G p, hseg p⟩
      continuous_toFun := G.continuous.subtype_mk hseg
      map_zero_left := fun x => Subtype.ext (by simp [G, F])
      map_one_left := fun x => Subtype.ext (by simp [G, F]) }
  -- The realization of the nerve is a CW complex, for any linear order on the vertices.
  let : LinearOrder ↥(C ∩ U) := IsWellOrder.linearOrder WellOrderingRel
  let := realizationCWComplex ρ.nerve
  exact TauCeti.CWType.of_comp_homotopic_id ⟨H⟩

end Convex

end
