/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Basic

/-!
# Bundle morphisms multiplied by scalar functions

A coordinate morphism `a` between two vector bundle cores over `B`, in Tau Ceti's sense
(`VectorBundleCore.CoordinateHom`), can be multiplied by a continuous function `c : C(B, 𝕜)`: the
chart operators of `c • a` are those of `a` multiplied at each point by the value of `c`, and its
fibre map at `x` is `c x • a x` (`VectorBundleCore.CoordinateHom.fiberMap_smul`). The same holds
for the morphisms of Tau Ceti's finite-rank cores (`TauCeti.FiniteRankBundleCore.fiberMap_smul`),
which are coordinate morphisms.

With the addition of morphisms, this gives convex combinations of morphisms with coefficients
depending on the point of the base, such as the segment between two clutching functions.

## References

* [A. Hatcher, *Vector Bundles and K-Theory*][Hatcher2017], §1.1 (bundle maps).
-/

public section

open CategoryTheory

namespace VectorBundleCore.CoordinateHom

variable {𝕜 B F G ι κ : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {Z : VectorBundleCore 𝕜 B F ι} {W : VectorBundleCore 𝕜 B G κ}

/-- A coordinate morphism multiplied by a continuous scalar function on the base: its chart
operators are those of the morphism, multiplied at each point by the value of the function. -/
instance instSMulContinuousMap : SMul C(B, 𝕜) (CoordinateHom Z W) where
  smul c a :=
    { operator i j := ⟨fun x ↦ c x.val • a.operator i j x,
        (c.continuous.comp continuous_subtypeVal).smul (a.operator i j).continuous⟩
      compatible i i' j j' x hi hi' hj hj' v := by
        simp only [ContinuousMap.coe_mk, smul_apply, map_smul,
          a.compatible i i' j j' x hi hi' hj hj' v] }

theorem operator_smul (c : C(B, 𝕜)) (a : CoordinateHom Z W) (i : ι) (j : κ)
    (x : ↥(Z.baseSet i ∩ W.baseSet j)) :
    (c • a).operator i j x = c x.val • a.operator i j x :=
  (rfl)

@[simp]
theorem fiberMap_smul (c : C(B, 𝕜)) (a : CoordinateHom Z W) (x : B) :
    (c • a).fiberMap x = c x • a.fiberMap x := by
  rw [fiberMap_def, operator_smul, fiberMap_def]

end VectorBundleCore.CoordinateHom

namespace TauCeti.FiniteRankBundleCore

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]
  {A D : FiniteRankBundleCore 𝕜 B}

/-- A morphism of finite-rank cores multiplied by a continuous scalar function on the base, as a
coordinate morphism. -/
instance instSMulContinuousMapHom : SMul C(B, 𝕜) (A ⟶ D) :=
  inferInstanceAs (SMul C(B, 𝕜) (VectorBundleCore.CoordinateHom A.core D.core))

@[simp]
theorem fiberMap_smul (c : C(B, 𝕜)) (a : A ⟶ D) (x : B) :
    (c • a).fiberMap x = c x • a.fiberMap x :=
  VectorBundleCore.CoordinateHom.fiberMap_smul c a x

end TauCeti.FiniteRankBundleCore

end
