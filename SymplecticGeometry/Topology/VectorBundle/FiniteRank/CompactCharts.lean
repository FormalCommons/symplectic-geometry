/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Data.Fintype.Order
public import Mathlib.Topology.PartitionOfUnity
public import Mathlib.Topology.UrysohnsLemma
public import TauCeti.Topology.VectorBundle.FiniteRank.Basic
public import TauCeti.Topology.VectorBundle.Hom

/-!
# Charts of finite-rank cores over compact sets

Estimates in finitely many charts of a vector-bundle core, of the kind used to patch local
constructions together over a compact base.

## Main results

* `TauCeti.FiniteRankBundleCore.exists_partitionOfUnity_isSubordinate_baseSet`: over a compact
  Hausdorff base, a finite-rank core has finitely many charts with a partition of unity `ρ`
  subordinate to them, and cutoffs `σ k` supported in the chart `k` and equal to `1` on the
  closed support of `ρ k`;
* `VectorBundleCore.exists_norm_coordChange_le`: over a Hausdorff base, the transitions between
  finitely many charts are bounded on the overlaps of compact subsets of their domains;
* `TauCeti.FiniteRankBundleCore.exists_norm_inChartCoordinates_le`: the fibre maps of a morphism,
  read in finitely many pairs of charts, are bounded on compact subsets of their domains.

## References

* [A. Hatcher, *Vector Bundles and K-Theory*][Hatcher2017], §2.1 (finitely many charts over a
  compact base).
-/

public section

open Set

namespace VectorBundleCore

variable {𝕜 B F ι κ : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] (Z : VectorBundleCore 𝕜 B F ι)

/-- Let `K k`, for `k` in a finite type, be compact subsets of the domains of charts `p k` of a
core over a Hausdorff base. Then the transitions from the chart `p k` to the chart `p j` are
bounded, uniformly in `j` and `k`, on `K j ∩ K k`. -/
theorem exists_norm_coordChange_le [T2Space B] [Finite κ] (p : κ → ι) {K : κ → Set B}
    (hK : ∀ k, IsCompact (K k)) (hKs : ∀ k, K k ⊆ Z.baseSet (p k)) :
    ∃ C, ∀ j k, ∀ x ∈ K j ∩ K k, ‖Z.coordChange (p k) (p j) x‖ ≤ C := by
  have h (j k : κ) : ∃ C, ∀ x ∈ K j ∩ K k, ‖Z.coordChange (p k) (p j) x‖ ≤ C :=
    ((hK j).inter_right (hK k).isClosed).exists_bound_of_continuousOn
      ((Z.continuousOn_coordChange (p k) (p j)).mono fun x hx ↦ ⟨hKs k hx.2, hKs j hx.1⟩)
  choose C hC using h
  obtain ⟨M, hM⟩ := Finite.exists_le fun q : κ × κ ↦ C q.1 q.2
  exact ⟨M, fun j k x hx ↦ (hC j k x hx).trans (hM (j, k))⟩

end VectorBundleCore

namespace TauCeti.FiniteRankBundleCore

open CategoryTheory

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace X]

/-- Over a compact Hausdorff base, a finite-rank core `E` has finitely many charts `t` with a
partition of unity `ρ` subordinate to them, and for each chart `k` a cutoff `σ k` whose closed
support lies in the chart and which is `1` on the closed support of `ρ k`. -/
theorem exists_partitionOfUnity_isSubordinate_baseSet [CompactSpace X] [T2Space X]
    (E : FiniteRankBundleCore 𝕜 X) :
    ∃ (t : Finset X) (ρ : PartitionOfUnity t X) (σ : t → C(X, ℝ)),
      ρ.IsSubordinate (fun k ↦ E.core.baseSet k) ∧ (∀ k, tsupport (σ k) ⊆ E.core.baseSet k) ∧
      ∀ k, EqOn (σ k) 1 (tsupport (ρ k)) := by
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : X ↦ E.core.baseSet x)
    (fun x ↦ E.core.isOpen_baseSet x) fun x _ ↦ mem_iUnion.2 ⟨x, E.mem_baseSet_self x⟩
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ
    (fun k : t ↦ E.core.baseSet k) (fun k ↦ E.core.isOpen_baseSet k) fun x _ ↦ by
      obtain ⟨k, hk, hx⟩ := mem_iUnion₂.1 (ht (mem_univ x))
      exact mem_iUnion.2 ⟨⟨k, hk⟩, hx⟩
  choose σ hσs hσ1 _ using fun k : t ↦ exists_tsupport_one_of_isOpen_isClosed
    (E.core.isOpen_baseSet k) isClosed_closure.isCompact (isClosed_tsupport (ρ k)) (hρ k)
  exact ⟨t, ρ, σ, hρ, hσs, hσ1⟩

/-- Let `K k`, for `k` in a finite type, be compact sets, each in the domains of a chart `p k` of
`A` and a chart `q k` of `D`. The fibre maps of a morphism `h : A ⟶ D`, read from the chart `p k`
to the chart `q k`, are bounded on `K k`, uniformly in `k`. -/
theorem exists_norm_inChartCoordinates_le {A D : FiniteRankBundleCore 𝕜 X} (h : A ⟶ D)
    {κ : Type*} [Finite κ] (p q : κ → X) {K : κ → Set X} (hK : ∀ k, IsCompact (K k))
    (hKs : ∀ k, K k ⊆ A.core.baseSet (p k) ∩ D.core.baseSet (q k)) :
    ∃ C, ∀ k, ∀ x ∈ K k,
      ‖A.core.inChartCoordinates D.core (p k) (q k) x (h.fiberMap x)‖ ≤ C := by
  have hb (k : κ) : ∃ C, ∀ x ∈ K k,
      ‖A.core.inChartCoordinates D.core (p k) (q k) x (h.fiberMap x)‖ ≤ C :=
    (hK k).exists_bound_of_continuousOn
      ((VectorBundleCore.continuousOn_inChartCoordinates
        (VectorBundleCore.CoordinateHom.continuous_fiberMap h).continuousOn).mono (hKs k))
  choose C hC using hb
  obtain ⟨M, hM⟩ := Finite.exists_le C
  exact ⟨M, fun k x hx ↦ (hC k x hx).trans (hM k)⟩

end TauCeti.FiniteRankBundleCore

end
