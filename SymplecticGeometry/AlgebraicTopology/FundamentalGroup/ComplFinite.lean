/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.FundamentalGroup.ComplSingleton
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Geometry.Manifold.HasGroupoid
import TauCeti.AlgebraicTopology.FundamentalGroup.Basic
import TauCeti.AlgebraicTopology.FundamentalGroup.Homeomorph
import TauCeti.Geometry.Manifold.Connected

/-!
# Deleting finitely many points from a manifold of dimension at least three

Let `X` be a topological space charted on a real normed space `E` with `2 < Module.rank ℝ E`,
and let `S` be a finite subset of `X`. This file extends Tau Ceti's results on the complement of
one point (`TauCeti.fundamentalGroup_map_subtypeVal_compl_singleton_bijective` and
`TauCeti.simplyConnectedSpace_compl_singleton_iff`) to `X \ S`.

Both proofs go by induction on `S`. If `S = insert a s` with `a ∉ s`, the set `X \ s` is open,
so Mathlib charts it on `E` as an open subset, and removing the point `a` from it gives a space
homeomorphic to `X \ S`. The one-point results for `X \ s`, which is connected by Tau Ceti's
`isPathConnected_compl_of_finite_of_one_lt_rank`, then pass from `s` to `S`.

## Main results

* `SymplecticGeometry.fundamentalGroup_map_subtypeVal_compl_bijective_of_finite`: if `X` is
  connected, the inclusion `X \ S → X` induces a bijection of fundamental groups at every point
  of `X \ S`.
* `SymplecticGeometry.simplyConnectedSpace_compl_iff_of_finite`: `X \ S` is simply connected if
  and only if `X` is.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press (2002), §1.2: the van Kampen
  theorem 1.20 and Proposition 1.26.
-/

public section

open Set Topology TopologicalSpace

namespace SymplecticGeometry

variable {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E] [ChartedSpace E X]

/-- The complement of a finite set, as an open subset of a charted space `X`. -/
private def complOpens {s : Set X} (hs : s.Finite) : Opens X :=
  have := ChartedSpace.t1Space E X
  ⟨sᶜ, hs.isClosed.isOpen_compl⟩

/-- Removing the point `a` from the open set `X \ s` gives `X \ insert a s`. -/
private noncomputable def complInsertHomeomorph {a : X} {s : Set X} (ha : a ∉ s)
    (hs : s.Finite) :
    ({⟨a, ha⟩}ᶜ : Set (complOpens (E := E) hs)) ≃ₜ ((insert a s)ᶜ : Set X) :=
  (Homeomorph.setCongr (by
    ext ⟨y, hy⟩
    -- Membership in `complOpens hs` is membership in `sᶜ` by definition.
    have hy' : y ∉ s := hy
    simp [Subtype.ext_iff, hy'])).trans
    (IsEmbedding.subtypeVal.homeomorphOfSubsetRange (s := (insert a s)ᶜ) fun y hy ↦
      ⟨⟨y, fun h ↦ hy (mem_insert_of_mem a h)⟩, rfl⟩)

variable [NormedSpace ℝ E]

/-- **Deleting finitely many points from a manifold of dimension at least three does not change
its fundamental group.** If `X` is a connected space charted on a real normed space of dimension
greater than two and `S ⊆ X` is finite, the inclusion `X \ S → X` induces a bijection of
fundamental groups at every point of `X \ S`. -/
theorem fundamentalGroup_map_subtypeVal_compl_bijective_of_finite [ConnectedSpace X]
    (h : 2 < Module.rank ℝ E) {S : Set X} (hS : S.Finite) (x : (Sᶜ : Set X)) :
    Function.Bijective (FundamentalGroup.map (ContinuousMap.subtypeVal (Sᶜ : Set X)) x) := by
  -- A homeomorphism induces a bijection of fundamental groups.
  have key {A B : Type _} [TopologicalSpace A] [TopologicalSpace B] (φ : A ≃ₜ B) (y : A) :
      Function.Bijective (FundamentalGroup.map (φ : C(A, B)) y) := by
    convert (FundamentalGroup.homeomorphMulEquiv φ y).bijective using 1
    ext p
    simp
  induction S, hS using Set.Finite.induction_on with
  | empty =>
    exact key ((Homeomorph.setCongr (compl_empty : (∅ : Set X)ᶜ = univ)).trans
      (Homeomorph.Set.univ X)) x
  | @insert a s ha hs ih =>
    let U := complOpens (E := E) hs
    let e := complInsertHomeomorph (E := E) ha hs
    have : ConnectedSpace U := by
      -- The subspace `U` is `X \ s`, by the definition of `complOpens`.
      have : PathConnectedSpace U := isPathConnected_iff_pathConnectedSpace.1 <|
        TauCeti.isPathConnected_compl_of_finite_of_one_lt_rank (Cardinal.one_lt_two.trans h) hs
      infer_instance
    -- The inclusion of `X \ insert a s` factors through `e⁻¹`, then the inclusions of
    -- `U \ {a}` into `U = X \ s` and of `U` into `X`.
    have hfac : ContinuousMap.subtypeVal ((insert a s)ᶜ : Set X) =
        ContinuousMap.comp (β := U) (ContinuousMap.subtypeVal (U : Set X))
          ((ContinuousMap.subtypeVal ({⟨a, ha⟩}ᶜ : Set U)).comp (e.symm : C(_, _))) := by
      ext y
      exact (congrArg Subtype.val (e.apply_symm_apply y)).symm
    rw [hfac, FundamentalGroup.map_comp, FundamentalGroup.map_comp, MonoidHom.coe_comp,
      MonoidHom.coe_comp]
    exact (ih _).comp
      ((TauCeti.fundamentalGroup_map_subtypeVal_compl_singleton_bijective h _ _).comp
        (key e.symm x))

/-- **A manifold of dimension at least three is simply connected if and only if the complement
of a finite set is.** If `X` is charted on a real normed space of dimension greater than two and
`S ⊆ X` is finite, then `X \ S` is simply connected if and only if `X` is. -/
theorem simplyConnectedSpace_compl_iff_of_finite (h : 2 < Module.rank ℝ E) {S : Set X}
    (hS : S.Finite) : SimplyConnectedSpace (Sᶜ : Set X) ↔ SimplyConnectedSpace X := by
  induction S, hS using Set.Finite.induction_on with
  | empty =>
    exact ((Homeomorph.setCongr (compl_empty : (∅ : Set X)ᶜ = univ)).trans
      (Homeomorph.Set.univ X)).toHomotopyEquiv.simplyConnectedSpace_iff
  | @insert a s ha hs ih =>
    rw [← ih, ← (complInsertHomeomorph (E := E) ha hs).toHomotopyEquiv.simplyConnectedSpace_iff]
    exact TauCeti.simplyConnectedSpace_compl_singleton_iff h _

end SymplecticGeometry

end
