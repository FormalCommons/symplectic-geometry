/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Algebra.Module.LocallyConvex
public import Mathlib.Topology.Metrizable.Basic
public import TauCeti.Topology.CWComplex.Classical.CWType
import Mathlib.Analysis.Convex.Combination
import SymplecticGeometry.AlgebraicTopology.Homotopy.Domination
import SymplecticGeometry.AlgebraicTopology.SimplicialComplex.Realization.LinearCombination
import SymplecticGeometry.AlgebraicTopology.SimplicialComplex.Realization.PartitionOfUnity
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
puts `z` and every `xᵢ` in the ball `B(xⱼ, 2 * r xⱼ)`, hence in one convex subset of `O`. So the
map `ψ` from the realization of the nerve of `ρ` to `O`, which sends the vertex `x` to `x` and is
affine on each simplex, is well defined, and the segment from `x` to `ψ (ρ.toNerve x)` lies in
`O`. Thus `O` is dominated by the realization, a CW complex, and has CW type by
`TauCeti.CWType.of_homotopic_comp`.

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
  -- If the functions `ρ i`, `i ∈ t`, are nonzero at `z`, then `z` and the points of `t` lie in
  -- one convex subset of `O`.
  have key (z : ↥(C ∩ U)) (t : Finset ↥(C ∩ U)) (ht : t.Nonempty) (hz : ∀ i ∈ t, ρ i z ≠ 0) :
      ∃ S : Set E, Convex ℝ S ∧ S ⊆ C ∩ U ∧ (z : E) ∈ S ∧ ∀ i ∈ t, (i : E) ∈ S := by
    have hd (i) (hi : i ∈ t) : dist i z < r i := by
      rw [dist_comm, ← mem_ball]
      exact hρ i (subset_tsupport _ (hz i hi))
    obtain ⟨j, hj, hjmax⟩ := t.exists_max_image r ht
    obtain ⟨y, -, -, hy⟩ := hr j
    refine ⟨C ∩ V y, hC.inter (hVc y), inter_subset_inter_right _ (hVU y),
      ⟨z.property.1, hy z (by simp only [id]; linarith [hd j hj, hr0 j])⟩,
      fun i hi => ⟨i.property.1, hy i ?_⟩⟩
    calc dist j i ≤ dist j z + dist z i := dist_triangle _ _ _
      _ < r j + r i := by rw [dist_comm z i]; linarith [hd j hj, hd i hi]
      _ ≤ 2 * r j := by linarith [hjmax i hi]
  -- Hence the points of every face of the nerve lie in one convex subset of `O`.
  have hface (t : Finset ↥(C ∩ U)) (ht : t ∈ ρ.nerve) :
      ∃ S : Set E, Convex ℝ S ∧ S ⊆ C ∩ U ∧ ∀ i ∈ t, (i : E) ∈ S := by
    rcases ρ.mem_nerve_iff.1 ht with ⟨ht, z, hz⟩ | ⟨i, rfl⟩
    · obtain ⟨S, hS, hSO, -, htS⟩ := key z t ht hz
      exact ⟨S, hS, hSO, htS⟩
    · exact ⟨{(i : E)}, convex_singleton _, singleton_subset_iff.2 i.property, by simp⟩
  -- The map from the realization of the nerve, affine on each simplex.
  have hmem (p : ρ.nerve.Realization) :
      Finsupp.linearCombination ℝ (fun i : ↥(C ∩ U) => (i : E)) p.val ∈ C ∩ U := by
    obtain ⟨S, hS, hSO, htS⟩ := hface _ (support_mem _ p)
    exact hSO (linearCombination_mem_of_convex hS _ p htS)
  let ψ : C(ρ.nerve.Realization, ↥(C ∩ U)) :=
    ⟨fun p => ⟨_, hmem p⟩, (continuous_linearCombination _).subtype_mk hmem⟩
  have hψ (x : ↥(C ∩ U)) : ((ψ (ρ.toNerve x) : ↥(C ∩ U)) : E) =
      Finsupp.linearCombination ℝ (fun i : ↥(C ∩ U) => (i : E)) (ρ.toNerve x).val := by
    simp only [ψ, ContinuousMap.coe_mk]
  -- The straight-line homotopy from `ψ ∘ ρ.toNerve` to the identity stays in `O`.
  have hseg (s : unitInterval) (x : ↥(C ∩ U)) :
      (1 - (s : ℝ)) • ((ψ (ρ.toNerve x) : ↥(C ∩ U)) : E) + (s : ℝ) • (x : E) ∈ C ∩ U := by
    obtain ⟨i, hi⟩ := ρ.exists_pos (mem_univ x)
    obtain ⟨S, hS, hSO, hxS, htS⟩ := key x (ρ.finsupport x) ⟨i, (ρ.mem_finsupport x).2 hi.ne'⟩
      fun j hj => (ρ.mem_finsupport x).1 hj
    refine hSO (hS ?_ hxS (sub_nonneg.2 s.property.2) s.property.1 (sub_add_cancel _ _))
    rw [hψ]
    exact linearCombination_mem_of_convex hS _ _ (by simpa using htS)
  let H : (ψ.comp ρ.toNerve).Homotopy (ContinuousMap.id _) :=
    { toFun := fun p => ⟨_, hseg p.1 p.2⟩
      continuous_toFun := by
        refine Continuous.subtype_mk ?_ fun p : unitInterval × ↥(C ∩ U) => hseg p.1 p.2
        exact ((continuous_const.sub (continuous_subtypeVal.comp continuous_fst)).smul
          (continuous_subtypeVal.comp ((ψ.comp ρ.toNerve).continuous.comp continuous_snd))).add
          ((continuous_subtypeVal.comp continuous_fst).smul
            (continuous_subtypeVal.comp continuous_snd))
      map_zero_left := fun x => Subtype.ext (by simp)
      map_one_left := fun x => Subtype.ext (by simp) }
  -- The realization of the nerve is a CW complex, for any linear order on the vertices.
  let : LinearOrder ↥(C ∩ U) := IsWellOrder.linearOrder WellOrderingRel
  let := realizationCWComplex ρ.nerve
  exact TauCeti.CWType.of_homotopic_comp ⟨H⟩

end Convex

end
