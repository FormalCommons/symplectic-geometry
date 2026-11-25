/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.VectorBundle.Countable
public import TauCeti.Topology.VectorBundle.TrivialEmbedding
public import TauCeti.Topology.VectorBundle.Transfer

/-!
# Finite trivializing covers of vector bundles

A vector bundle `E` over `B` with model fibre `F` has a *finite trivializing cover* if finitely
many linear trivializations of `E` have base sets covering `B`. Over a normal base such a cover
gives a continuous fibrewise injective linear map of `E` into a trivial bundle `B × 𝕜ᴺ`, which is
what a classifying map to a finite-dimensional projective space needs.

## Main definitions and results

* `SymplecticGeometry.Bundle.HasFiniteTrivializingCover R F E`: some finite set of `R`-linear
  trivializations of `E` has base sets covering `B`.
* `SymplecticGeometry.Bundle.HasFiniteTrivializingCover.of_finite`: a finite indexed family of
  linear trivializations whose base sets cover `B` gives one.
* `SymplecticGeometry.Bundle.HasFiniteTrivializingCover.of_compactSpace`: every vector bundle
  over a compact base has one.
* `SymplecticGeometry.Bundle.HasFiniteTrivializingCover.of_card_finsupport_le`: a partition of
  unity subordinate to the base sets of linear trivializations, in which every point lies in the
  support of at most `N` of its functions, gives one, made of the gap trivializations
  `PartitionOfUnity.gapTrivialization` of Tau Ceti of sizes `0, …, N`. This is the argument of
  Milnor–Stasheff, Lemma 5.9, where the bound `N` makes the countable family of gap
  trivializations finite.
* `SymplecticGeometry.Bundle.HasFiniteTrivializingCover.of_continuousLinearEquiv`: a finite
  trivializing cover passes along a fibrewise continuous linear equivalence of bundles over the
  same base that is a homeomorphism of total spaces, through Tau Ceti's
  `Bundle.Trivialization.compContinuousLinearEquiv`, which keeps each base set.
* `SymplecticGeometry.Bundle.HasFiniteTrivializingCover.exists_continuous_injective_fin`: over a
  normal base, a bundle with a finite trivializing cover and finite-dimensional model fibre has a
  continuous fibrewise injective linear map into a trivial bundle `B × (Fin N → 𝕜)`.

The last proof follows that of Tau Ceti's `TauCeti.exists_continuous_injective_fin_of_compactSpace`,
with the finite trivializing cover in place of the finite subcover given by compactness.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press, 1974, Lemma 5.9.
-/

public section

open Bundle Set Function

namespace SymplecticGeometry.Bundle

section Definition

variable (R : Type*) {B : Type*} (F : Type*) (E : B → Type*) [Semiring R] [TopologicalSpace B]
  [TopologicalSpace F] [AddCommMonoid F] [Module R F] [TopologicalSpace (TotalSpace F E)]
  [∀ x, AddCommMonoid (E x)] [∀ x, Module R (E x)]

/-- A bundle `E` over `B` with model fibre `F` has a finite trivializing cover over `R` if some
finite set of `R`-linear trivializations of `E` has base sets covering `B`. -/
def HasFiniteTrivializingCover : Prop :=
  ∃ s : Finset (Trivialization F (π F E)), (∀ e ∈ s, e.IsLinear R) ∧ ⋃ e ∈ s, e.baseSet = univ

theorem hasFiniteTrivializingCover_def :
    HasFiniteTrivializingCover R F E ↔
      ∃ s : Finset (Trivialization F (π F E)), (∀ e ∈ s, e.IsLinear R) ∧
        ⋃ e ∈ s, e.baseSet = univ :=
  Iff.rfl

variable {R F E}

/-- A finite family of linear trivializations whose base sets cover `B` is a finite trivializing
cover. -/
theorem HasFiniteTrivializingCover.of_finite {ι : Type*} [Finite ι]
    (e : ι → Trivialization F (π F E)) [∀ i, (e i).IsLinear R]
    (h : ⋃ i, (e i).baseSet = univ) : HasFiniteTrivializingCover R F E := by
  classical
  have := Fintype.ofFinite ι
  refine ⟨Finset.univ.image e, ?_, ?_⟩
  · simp only [Finset.mem_image]
    rintro _ ⟨i, -, rfl⟩
    infer_instance
  · simpa [Set.iUnion_exists, Set.biUnion_and'] using h

/-- A partition of unity of `B` subordinate to the base sets of linear trivializations `e i`, in
which every point lies in the support of at most `N` of its functions, gives a finite
trivializing cover: Tau Ceti's gap trivializations of sizes `0, …, N` cover `B`. -/
theorem HasFiniteTrivializingCover.of_card_finsupport_le {κ : Type*}
    (ρ : PartitionOfUnity κ B univ) (e : κ → Trivialization F (π F E)) [∀ i, (e i).IsLinear R]
    (he : ρ.IsSubordinate fun i ↦ (e i).baseSet) {N : ℕ}
    (hN : ∀ x, (ρ.finsupport x).card ≤ N) : HasFiniteTrivializingCover R F E := by
  refine .of_finite (fun n : Fin (N + 1) ↦ ρ.gapTrivialization e he n)
    (eq_univ_of_forall fun x ↦ ?_)
  obtain ⟨n, hn⟩ := mem_iUnion.1 (ρ.subset_iUnion_gapTrivialization_baseSet e he (mem_univ x))
  have hpos : 0 < ρ.gapPartition n x := by simpa using hn
  obtain ⟨S, rfl, hS⟩ := ρ.exists_gap_pos_of_gapPartition_pos hpos
  have hle : S.card ≤ N := (Finset.card_le_card (ρ.subset_finsupport_of_gap_pos hS)).trans (hN x)
  exact mem_iUnion.2 ⟨⟨S.card, Nat.lt_succ_of_le hle⟩, hn⟩

/-- A finite trivializing cover passes along a fibrewise isomorphism of bundles over the same
base: if `Φ x : E x ≃L[R] E' x` is continuous on total spaces, with continuous inverse, and `E`
has a finite trivializing cover with model `F`, then so does `E'`. -/
theorem HasFiniteTrivializingCover.of_continuousLinearEquiv [∀ x, TopologicalSpace (E x)]
    {E' : B → Type*} [TopologicalSpace (TotalSpace F E')] [∀ x, AddCommMonoid (E' x)]
    [∀ x, Module R (E' x)] [∀ x, TopologicalSpace (E' x)]
    (h : HasFiniteTrivializingCover R F E) (Φ : ∀ x, E x ≃L[R] E' x)
    (hΦ : Continuous fun p : TotalSpace F E ↦ TotalSpace.mk' F p.proj (Φ p.proj p.snd))
    (hΦ' : Continuous fun p : TotalSpace F E' ↦ TotalSpace.mk' F p.proj ((Φ p.proj).symm p.snd)) :
    HasFiniteTrivializingCover R F E' := by
  obtain ⟨s, hlin, hcover⟩ := h
  have hind := (Topology.IsEmbedding.of_leftInverse (fun p ↦ by simp) hΦ hΦ').isInducing
  have := fun e : s ↦ hlin e e.property
  refine .of_finite (fun e : s ↦ (e : Trivialization F (π F E)).compContinuousLinearEquiv
    (fun x ↦ (Φ x).symm) hind) ?_
  simpa [iUnion_subtype] using hcover

end Definition

variable {𝕜 B F : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)] [∀ x, TopologicalSpace (E x)]
  [FiberBundle F E]

/-- Every vector bundle over a compact base has a finite trivializing cover, made of finitely
many of the trivializations `trivializationAt`. -/
theorem HasFiniteTrivializingCover.of_compactSpace [CompactSpace B] [VectorBundle 𝕜 F E] :
    HasFiniteTrivializingCover 𝕜 F E := by
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x : B ↦ (trivializationAt F E x).baseSet)
    (fun x ↦ (trivializationAt F E x).open_baseSet)
    fun x _ ↦ mem_iUnion.2 ⟨x, mem_baseSet_trivializationAt F E x⟩
  refine .of_finite (fun y : t ↦ trivializationAt F E (y : B))
    (eq_univ_of_forall fun x ↦ ?_)
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 (ht (mem_univ x))
  exact mem_iUnion.2 ⟨⟨y, hy⟩, hxy⟩

/-- Over a normal base, a bundle with a finite trivializing cover and finite-dimensional model
fibre admits a continuous fibrewise injective linear map into the trivial bundle
`B × (Fin N → 𝕜)` for some `N`. -/
theorem HasFiniteTrivializingCover.exists_continuous_injective_fin [NormalSpace B]
    [NormedAlgebra ℝ 𝕜] [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]
    (h : HasFiniteTrivializingCover 𝕜 F E) :
    ∃ (N : ℕ) (j : ∀ x, E x →L[𝕜] (Fin N → 𝕜)),
      Continuous (fun p : TotalSpace F E ↦ j p.proj p.snd) ∧ ∀ x, Injective (j x) := by
  obtain ⟨s, hlin, hcover⟩ := h
  have : ∀ e : s, (e : Trivialization F (π F E)).IsLinear 𝕜 := fun e ↦ hlin e e.property
  obtain ⟨j, hj, hinj⟩ := TauCeti.exists_continuous_injective_pi_of_iUnion_baseSet (𝕜 := 𝕜)
    (fun e : s ↦ (e : Trivialization F (π F E))) (by rwa [iUnion_subtype])
  let L : (s → F) ≃L[𝕜] (Fin (Module.finrank 𝕜 (s → F)) → 𝕜) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  exact ⟨Module.finrank 𝕜 (s → F), fun x ↦ L.toContinuousLinearMap.comp (j x),
    L.continuous.comp hj, fun x ↦ L.injective.comp (hinj x)⟩

end SymplecticGeometry.Bundle

end
