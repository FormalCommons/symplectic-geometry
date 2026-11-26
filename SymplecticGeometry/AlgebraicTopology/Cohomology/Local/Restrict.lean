/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Singular.PairMap
public import TauCeti.AlgebraicTopology.Cohomology.Excision

/-!
# Local cohomology only depends on a neighbourhood of the point

Let `Y` be a `T1` space, `B ⊆ Y` and `y ∈ B`. The relative singular cohomology of the pair
`(B, B ∖ {y})` is determined by any open neighbourhood of `y` in `B`: for an open `O ⊆ B`
containing `y`, the inclusion `(O, O ∖ {y}) ⟶ (B, B ∖ {y})` is an isomorphism on cohomology, in
every degree and for all coefficients
(`TopPair.isIso_singularCohomologyMap_ofSubsetMap_inclusion`). As `{y}` is closed, this is
excision of `B ∖ O` from `(B, B ∖ {y})`, composed with the homeomorphism between `O` and the
preimage of `O` in `B`.

## Main results

* `TopPair.isIso_singularCohomologyMap_ofSubsetMap_inclusion`: in a `T1` space, restriction
  from `(B, B ∖ {y})` to `(O, O ∖ {y})`, for an open `O ⊆ B` containing `y`, is an isomorphism
  on relative cohomology.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2 (local homology groups) and Section 3.1 (excision in cohomology).
-/

public section

noncomputable section

open CategoryTheory Limits Set

universe w v u

namespace TopPair

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
  (k : Type*) [Ring k] [Linear k C] (M : C)

/-- **Restriction to a smaller open neighbourhood is an isomorphism on local cohomology.** In a
`T1` space `Y`, let `O ⊆ B` with `O` open and `y ∈ O`. The inclusion of pairs
`(O, O ∖ {y}) ⟶ (B, B ∖ {y})` induces isomorphisms `Hⁿ(B, B ∖ {y}) ⟶ Hⁿ(O, O ∖ {y})`: it is
excision of `B ∖ O` from `(B, B ∖ {y})`, read on `O`. -/
theorem isIso_singularCohomologyMap_ofSubsetMap_inclusion {Y : Type w} [TopologicalSpace Y]
    [T1Space Y] {O B : Set Y} (hO : IsOpen O) (hOB : O ⊆ B) {y : Y} (hy : y ∈ O) (n : ℕ) :
    IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M)
      (ofSubsetMap (X := TopCat.of O) (Y := TopCat.of B)
        (TopCat.ofHom ⟨Set.inclusion hOB, continuous_inclusion hOB⟩)
        (B := {⟨y, hy⟩}ᶜ) (B' := {⟨y, hOB hy⟩}ᶜ)
        fun _ hw h ↦ hw (Set.inclusion_injective hOB h)) n) := by
  set S : Set (TopCat.of B) := {⟨y, hOB hy⟩}
  set A : Set (TopCat.of B) := Subtype.val ⁻¹' O
  -- `O`, as the subspace `A` of `B`, is homeomorphic to `O`.
  let σ : O ≃ₜ A :=
    { toFun w := ⟨Set.inclusion hOB w, w.property⟩
      invFun a := ⟨a.val, a.property⟩
      left_inv _ := rfl
      right_inv _ := rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let τ := ofSubsetIso (X := TopCat.of O) (Y := TopCat.of A) (B := {⟨y, hy⟩}ᶜ)
    (B' := Subtype.val ⁻¹' Sᶜ) σ fun w ↦ by simp [σ, S, Subtype.ext_iff]
  have hfac : τ.hom ≫ excisionMap A Sᶜ = ofSubsetMap (X := TopCat.of O) (Y := TopCat.of B)
      (TopCat.ofHom ⟨Set.inclusion hOB, continuous_inclusion hOB⟩)
      (B := {⟨y, hy⟩}ᶜ) (B' := {⟨y, hOB hy⟩}ᶜ)
      fun _ hw h ↦ hw (Set.inclusion_injective hOB h) := by
    rw [ofSubsetIso_hom, excisionMap_eq_ofSubsetMap]
    exact ofSubsetMap_comp_ofSubsetMap_of_comp_eq _ _ _ rfl
  have : IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M) τ.hom n) :=
    singularCohomologyMapIso_hom (R := R) (k := k) (M := M) τ n ▸
      (singularCohomologyMapIso R k M τ n).isIso_hom
  have := isIso_singularCohomologyMap_excisionMap_of_isClosed_subset R k M (U := A) (K := S)
    (hO.preimage continuous_subtypeVal) isClosed_singleton (singleton_subset_iff.2 hy) n
  rw [← hfac, singularCohomologyMap_comp]
  infer_instance

end TopPair

end
