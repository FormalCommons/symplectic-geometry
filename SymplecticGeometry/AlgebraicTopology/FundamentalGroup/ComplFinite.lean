/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.FundamentalGroup.ComplSingleton
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Geometry.Manifold.HasGroupoid
import SymplecticGeometry.Topology.Homeomorph.SubtypeCompl
import TauCeti.AlgebraicTopology.FundamentalGroup.Basic
import TauCeti.AlgebraicTopology.FundamentalGroup.HomotopyEquiv
import TauCeti.Geometry.Manifold.Connected
import TauCeti.Topology.Homeomorph.SetCongr

/-!
# Deleting finitely many points from a manifold of dimension at least three

Let `X` be a topological space charted on a real normed space `E` with `2 < Module.rank ℝ E`,
and let `S` be a finite subset of `X`. This file extends Tau Ceti's results on the complement of
one point (`TauCeti.fundamentalGroup_map_subtypeVal_compl_singleton_bijective` and
`TauCeti.simplyConnectedSpace_compl_singleton_iff`) to `X \ S`.

Both proofs go by induction on `S`. If `S = insert a s` with `a ∉ s`, the set `X \ s` is open,
so Mathlib charts it on `E` as an open subset, and removing the point `a` from it gives a space
homeomorphic to `X \ S` (`Homeomorph.Set.subtypeCompl`). The one-point results for `X \ s`,
which is connected by Tau Ceti's `isPathConnected_compl_of_finite_of_one_lt_rank`, then pass
from `s` to `S`.

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
  [NormedSpace ℝ E]

/-- **Deleting finitely many points from a manifold of dimension at least three does not change
its fundamental group.** If `X` is a connected space charted on a real normed space of dimension
greater than two and `S ⊆ X` is finite, the inclusion `X \ S → X` induces a bijection of
fundamental groups at every point of `X \ S`. -/
theorem fundamentalGroup_map_subtypeVal_compl_bijective_of_finite [ConnectedSpace X]
    (h : 2 < Module.rank ℝ E) {S : Set X} (hS : S.Finite) (x : (Sᶜ : Set X)) :
    Function.Bijective (FundamentalGroup.map (ContinuousMap.subtypeVal (Sᶜ : Set X)) x) := by
  induction S, hS using Set.Finite.induction_on with
  | empty =>
    exact ((Homeomorph.setCongr (compl_empty : (∅ : Set X)ᶜ = univ)).trans
      (Homeomorph.Set.univ X)).toHomotopyEquiv.fundamentalGroup_map_bijective x
  | @insert a s ha hs ih =>
    -- The open set `U = X \ s` is a connected space charted on `E`, and removing `a` from it
    -- gives a space homeomorphic to `X \ insert a s`.
    have := ChartedSpace.t1Space E X
    let U : Opens X := ⟨sᶜ, hs.isClosed.isOpen_compl⟩
    let a' : U := ⟨a, Opens.mem_mk.2 ha⟩
    have : ConnectedSpace U := by
      have hU : IsPathConnected (U : Set X) := by
        simpa [U] using TauCeti.isPathConnected_compl_of_finite_of_one_lt_rank
          (Cardinal.one_lt_two.trans h) hs
      have : PathConnectedSpace U := isPathConnected_iff_pathConnectedSpace.1 hU
      infer_instance
    let e : ({a'}ᶜ : Set U) ≃ₜ ((insert a s)ᶜ : Set X) :=
      (Homeomorph.Set.subtypeCompl (t := (U : Set X)) {a'}).trans
        (Homeomorph.setCongr (by ext; simp [U, a', and_comm]))
    -- The inclusion of `X \ insert a s` factors through `e⁻¹`, then the inclusions of
    -- `U \ {a}` into `U` and of `U` into `X`.
    have hfac : ContinuousMap.subtypeVal ((insert a s)ᶜ : Set X) =
        (ContinuousMap.subtypeVal (U : Set X)).comp
          ((ContinuousMap.subtypeVal ({a'}ᶜ : Set U)).comp (e.symm : C(_, _))) := by
      ext y
      simp only [e, ContinuousMap.comp_apply, ContinuousMap.coe_ofClass,
        Homeomorph.symm_trans_apply, Homeomorph.setCongr_symm_apply, ContinuousMap.subtypeVal_apply]
      rw [Homeomorph.Set.coe_coe_subtypeCompl_symm_apply (t := (U : Set X))]
    rw [hfac, FundamentalGroup.map_comp, FundamentalGroup.map_comp, MonoidHom.coe_comp,
      MonoidHom.coe_comp]
    exact (ih _).comp
      ((TauCeti.fundamentalGroup_map_subtypeVal_compl_singleton_bijective (X := U) h a' _).comp
        (e.symm.toHomotopyEquiv.fundamentalGroup_map_bijective x))

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
    -- Removing `a` from the open set `U = X \ s` gives a space homeomorphic to
    -- `X \ insert a s`.
    have := ChartedSpace.t1Space E X
    let U : Opens X := ⟨sᶜ, hs.isClosed.isOpen_compl⟩
    let a' : U := ⟨a, Opens.mem_mk.2 ha⟩
    let e : ({a'}ᶜ : Set U) ≃ₜ ((insert a s)ᶜ : Set X) :=
      (Homeomorph.Set.subtypeCompl (t := (U : Set X)) {a'}).trans
        (Homeomorph.setCongr (by ext; simp [U, a', and_comm]))
    rw [← ih, ← e.toHomotopyEquiv.simplyConnectedSpace_iff]
    exact TauCeti.simplyConnectedSpace_compl_singleton_iff h a'

end SymplecticGeometry

end
