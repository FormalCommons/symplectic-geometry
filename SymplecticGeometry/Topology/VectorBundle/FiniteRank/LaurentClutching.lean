/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Complex.Circle
public import TauCeti.Topology.VectorBundle.FiniteRank.Pullback
public import SymplecticGeometry.Topology.VectorBundle.FiniteRank.SMul

/-!
# Laurent families of bundle morphisms

Let `A` and `D` be finite-rank complex cores over `X`, and let `a i : A ⟶ D` be morphisms indexed
by `i : ℤ`. For `N : ℕ`, the Laurent family `∑_{|i| ≤ N} a_i(x) u^i` is a morphism between the
pullbacks of `A` and `D` to `X × Circle`, whose fibre map at `(x, u)` is
`∑ i ∈ Finset.Icc (-N) N, u ^ i • a_i(x)`. Taking `A = D = E`, these are the Laurent clutching
functions of [Hatcher2017, §2.1], to which every clutching function over `X × S²` can be brought.

It is built from Tau Ceti's pullback of morphisms (`TauCeti.FiniteRankBundleCore.pullbackMap`),
the multiplication of morphisms by continuous scalar functions on the base
(`TauCeti.FiniteRankBundleCore.fiberMap_smul`), and Tau Ceti's sums of morphisms
(`TauCeti.FiniteRankBundleCore.fiberMap_sum`), so no continuity argument is needed beyond that of
`(x, u) ↦ u ^ i`.

## Main definitions and results

* `TauCeti.FiniteRankBundleCore.laurentHom N a`: the Laurent family `∑_{|i| ≤ N} a_i(x) u^i`;
* `TauCeti.FiniteRankBundleCore.fiberMap_laurentHom`: its fibre map at `(x, u)`.

## References

* [A. Hatcher, *Vector Bundles and K-Theory*][Hatcher2017], §2.1 (Laurent clutching functions).
-/

public section

noncomputable section

open CategoryTheory

namespace TauCeti.FiniteRankBundleCore

variable {X : Type*} [TopologicalSpace X] {A D : FiniteRankBundleCore ℂ X}

/-- The Laurent family `∑_{|i| ≤ N} a_i(x) u^i` of morphisms `a i : A ⟶ D`: the morphism between
the pullbacks of `A` and `D` to `X × Circle` whose fibre map at `(x, u)` is
`∑ i ∈ Finset.Icc (-N) N, u ^ i • (a i).fiberMap x`. -/
def laurentHom (N : ℕ) (a : ℤ → (A ⟶ D)) :
    A.pullback (ContinuousMap.fst : C(X × Circle, X)) ⟶
      D.pullback (ContinuousMap.fst : C(X × Circle, X)) :=
  ∑ i ∈ Finset.Icc (-(N : ℤ)) N,
    (⟨fun w ↦ ((w.2 ^ i : Circle) : ℂ), by fun_prop⟩ : C(X × Circle, ℂ)) •
      pullbackMap (a i) ContinuousMap.fst

theorem laurentHom_def (N : ℕ) (a : ℤ → (A ⟶ D)) :
    laurentHom N a = ∑ i ∈ Finset.Icc (-(N : ℤ)) N,
      (⟨fun w ↦ ((w.2 ^ i : Circle) : ℂ), by fun_prop⟩ : C(X × Circle, ℂ)) •
        pullbackMap (a i) ContinuousMap.fst :=
  (rfl)

@[simp]
theorem fiberMap_laurentHom (N : ℕ) (a : ℤ → (A ⟶ D)) (w : X × Circle) :
    (laurentHom N a).fiberMap w =
      ∑ i ∈ Finset.Icc (-(N : ℤ)) N, (w.2 : ℂ) ^ i • (a i).fiberMap w.1 := by
  simp only [laurentHom_def, fiberMap_sum, fiberMap_smul, ContinuousMap.coe_mk,
    fiberMap_pullbackMap, ContinuousMap.fst_apply, Circle.coe_zpow]

end TauCeti.FiniteRankBundleCore

end
