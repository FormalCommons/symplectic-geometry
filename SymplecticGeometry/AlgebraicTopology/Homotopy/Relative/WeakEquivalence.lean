/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Relative.Basic
public import TauCeti.Topology.Homotopy.HomotopyGroup.WeakHomotopyEquivalence
import TauCeti.AlgebraicTopology.Homotopy.Relative.Deformation
import TauCeti.AlgebraicTopology.Homotopy.Relative.Exact
import TauCeti.Topology.Homotopy.HomotopyGroup.LoopSpace
import TauCeti.Topology.Homotopy.HomotopyGroup.Map

/-!
# Trivial relative homotopy sets and weak homotopy equivalences

For a based pair `(X, A, a₀)`, the long exact homotopy sequence of the pair (Hatcher,
Theorem 4.3) shows:

* if `π_{n+1}(X, A, a₀)` is trivial, then `π_{n+1}(A, a₀) → π_{n+1}(X, a₀)` is surjective
  (`TauCeti.RelHomotopyGroup.surjective_homotopyGroupMap_of_subsingleton`);
* if `π_{n+1}(X, A, a₀)` is trivial and `n ≥ 1`, then `π_n(A, a₀) → π_n(X, a₀)` is injective
  (`TauCeti.RelHomotopyGroup.injective_homotopyGroupMap_of_subsingleton`);
* if `π_1(X, A, a₀)` is trivial, then every point of `A` joined to `a₀` by a path in `X` is
  joined to it by a path in `A` (`TauCeti.RelHomotopyGroup.joined_of_subsingleton`).

Here `π_{n+1}(X, A, a₀)` is Tau Ceti's `TauCeti.RelHomotopyGroup N` with `n = Nat.card N`.
Together they give the converse of
`TauCeti.RelHomotopyGroup.subsingleton_of_isWeakHomotopyEquivalence` for all degrees at once: the
embedding `A → X` of a topological pair is a weak homotopy equivalence if and only if every path
component of `X` meets the image of `A` and all relative homotopy sets `π_{n+1}(X, A, a)`,
`a ∈ A`, are trivial (`TauCeti.TopPair.isWeakHomotopyEquivalence_map_iff`). For the inclusion
of a subset this is `ContinuousMap.isWeakHomotopyEquivalence_subtypeVal_iff`. For subsets `S ⊆ W`
of `X`, `ContinuousMap.isWeakHomotopyEquivalence_inclusion_iff_subtypeVal` reduces the inclusion
`S → W` to the inclusion of the preimage of `S` in `W`, to which that criterion applies.

The proofs follow those of `TauCeti.surjective_homotopyGroupMap_skeletonLT` and
`TauCeti.injective_homotopyGroupMap_skeletonLT`, which make the same deductions for the skeleta
of a CW complex. The proof of
`ContinuousMap.isWeakHomotopyEquivalence_inclusion_iff_subtypeVal` adapts that of Tau Ceti's
`ContinuousMap.isWeakHomotopyEquivalence_inclusion_preimage_val_iff`, which compares inclusions
of subsets with those of their preimages by the same homeomorphisms.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.1, Theorem 4.3.
-/

public section

open Topology

namespace TauCeti.RelHomotopyGroup

variable {N : Type*} {X : BasedTopPair}

/-- If the relative homotopy set `π_{n+1}(X, A, a₀)` is trivial, then the inclusion of `A`
induces a surjection `π_{n+1}(A, a₀) → π_{n+1}(X, a₀)`, where `n = Nat.card N`. -/
theorem surjective_homotopyGroupMap_of_subsingleton [Subsingleton (RelHomotopyGroup N X)] :
    Function.Surjective
      (HomotopyGroup.map (N := Option N) (x := X.basepoint) X.pair.map.hom rfl) :=
  fun _ ↦ mem_range_homotopyGroupMap_iff.2 (Subsingleton.elim _ _)

/-- If the relative homotopy set `π_{n+1}(X, A, a₀)` is trivial, where `n = Nat.card N ≥ 1`, then
the inclusion of `A` induces an injection `π_n(A, a₀) → π_n(X, a₀)`. -/
theorem injective_homotopyGroupMap_of_subsingleton [Nonempty N]
    [Subsingleton (RelHomotopyGroup N X)] :
    Function.Injective (HomotopyGroup.map (N := N) (x := X.basepoint) X.pair.map.hom rfl) := by
  classical
  refine (injective_iff_map_eq_one
    (HomotopyGroup.mapHom (N := N) (x := X.basepoint) X.pair.map.hom rfl)).2 fun c hc ↦ ?_
  rw [HomotopyGroup.mapHom_apply, ← HomotopyGroup.mk_const_eq_one] at hc
  obtain ⟨r, hr⟩ := mem_range_boundary_iff.2 hc
  rw [← hr, Subsingleton.elim r default, boundary_default, HomotopyGroup.mk_const_eq_one]

/-- If the relative homotopy set `π_1(X, A, a₀)` is trivial, a point of `A` that is joined to the
basepoint `a₀` by a path in `X` is joined to it by a path in `A`. Here `N` is empty, so that
`RelHomotopyGroup N X` is `π_1(X, A, a₀)`. -/
theorem joined_of_subsingleton [IsEmpty N] [Subsingleton (RelHomotopyGroup N X)]
    {c : X.pair.snd} (h : Joined (X.pair.map c) (X.pair.map X.basepoint)) :
    Joined c X.basepoint := by
  have hmap : HomotopyGroup.map X.pair.map.hom rfl
      (⟦(genLoopHomeoOfIsEmpty N X.basepoint).symm c⟧ :
        HomotopyGroup N X.pair.snd X.basepoint) =
      (⟦GenLoop.const⟧ : HomotopyGroup N X.pair.fst (X.pair.map X.basepoint)) := by
    rw [HomotopyGroup.map_mk]
    refine HomotopyGroup.mk_eq_mk_iff_joined.2 ?_
    rwa [GenLoop.map_apply, genLoopHomeoOfIsEmpty_symm_apply, GenLoop.const_apply]
  obtain ⟨r, hr⟩ := mem_range_boundary_iff.2 hmap
  rw [Subsingleton.elim r default, boundary_default] at hr
  exact (HomotopyGroup.mk_eq_mk_iff_joined.1 hr).symm

end TauCeti.RelHomotopyGroup

namespace TauCeti.TopPair

/-- **Trivial relative homotopy sets characterize weak equivalences.** The embedding `A → X` of a
topological pair `(X, A)` is a weak homotopy equivalence if and only if every point of `X` is
joined by a path to a point of the image of `A`, and the relative homotopy set `π_{n+1}(X, A, a)`
is trivial for every `n` and every `a ∈ A`. -/
theorem isWeakHomotopyEquivalence_map_iff (P : TopPair) :
    P.map.hom.IsWeakHomotopyEquivalence ↔
      (∀ x : P.fst, ∃ a : P.snd, Joined (P.map a) x) ∧
        ∀ (n : ℕ) (a : P.snd), Subsingleton (RelHomotopyGroup (Fin n) ⟨P, a⟩) := by
  refine ⟨fun hf ↦ ⟨hf.exists_joined, fun n a ↦
      RelHomotopyGroup.subsingleton_of_isWeakHomotopyEquivalence (X := ⟨P, a⟩) hf⟩,
    fun ⟨hjoined, hrel⟩ ↦ ⟨hjoined, fun n a ↦ ⟨?_, ?_⟩⟩⟩
  · rcases n with _ | n
    · refine HomotopyGroup.map_injective_of_isEmpty_of_joined _ rfl fun b c hbc ↦ ?_
      have := hrel 0 c
      exact RelHomotopyGroup.joined_of_subsingleton (X := ⟨P, c⟩) (N := Fin 0) hbc
    · have := hrel (n + 1) a
      exact RelHomotopyGroup.injective_homotopyGroupMap_of_subsingleton (X := ⟨P, a⟩)
  · rcases n with _ | n
    · exact HomotopyGroup.map_surjective_of_isEmpty_of_exists_joined _ rfl hjoined
    · have := hrel n a
      rw [HomotopyGroup.map_eq_congrEquiv_symm_comp _ rfl (finSuccEquiv n), Equiv.comp_surjective,
        Equiv.surjective_comp]
      exact RelHomotopyGroup.surjective_homotopyGroupMap_of_subsingleton (X := ⟨P, a⟩)

end TauCeti.TopPair

namespace ContinuousMap

open TauCeti

variable {X : Type*} [TopologicalSpace X] {A : Set X}

/-- The inclusion of a subset `A ⊆ X` is a weak homotopy equivalence if and only if every point of
`X` is joined by a path to a point of `A`, and the relative homotopy set `π_{n+1}(X, A, a)` is
trivial for every `n` and every `a ∈ A`. -/
theorem isWeakHomotopyEquivalence_subtypeVal_iff :
    (ContinuousMap.subtypeVal A).IsWeakHomotopyEquivalence ↔
      (∀ x : X, ∃ a : A, Joined (a : X) x) ∧
        ∀ (n : ℕ) (a : A),
          Subsingleton (RelHomotopyGroup (Fin n) ⟨TopPair.ofSubset (X := TopCat.of X) A, a⟩) :=
  (TopPair.ofSubset (X := TopCat.of X) A).isWeakHomotopyEquivalence_map_iff

/-- For subsets `S ⊆ W` of `X`, the inclusion `S → W` is a weak homotopy equivalence if and only if
the inclusion into `W` of the preimage of `S` in `W` is: the two are identified by the
homeomorphism between that preimage and `S`. -/
theorem isWeakHomotopyEquivalence_inclusion_iff_subtypeVal {S W : Set X} (h : S ⊆ W) :
    (inclusion h).IsWeakHomotopyEquivalence ↔
      (subtypeVal (Subtype.val ⁻¹' S : Set W)).IsWeakHomotopyEquivalence := by
  let φ := Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange
    (h.trans (Subtype.range_coe (s := W)).ge)
  have heq : inclusion h = (subtypeVal (Subtype.val ⁻¹' S : Set W)).comp (φ.symm : C(S, _)) := by
    refine ContinuousMap.ext fun x ↦ Subtype.ext ?_
    have := congrArg Subtype.val (φ.apply_symm_apply x)
    rw [Topology.IsEmbedding.homeomorphOfSubsetRange_apply_coe] at this
    exact this.symm
  rw [heq]
  exact ⟨fun hS ↦ .of_precomp φ.symm.isWeakHomotopyEquivalence hS,
    fun hA ↦ hA.comp φ.symm.isWeakHomotopyEquivalence⟩

end ContinuousMap
