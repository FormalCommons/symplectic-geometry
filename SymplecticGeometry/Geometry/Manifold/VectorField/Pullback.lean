/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.VectorField.Pullback
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset

/-!
# Pulling back vector fields along local diffeomorphisms

Mathlib's `VectorField.mpullback I J f V` is the vector field `x ↦ (df_x)⁻¹ (V (f x))`, which is
meaningful when the differential of `f` is invertible. This file gives its two basic properties
when `f` is a local diffeomorphism, and specializes them to the inclusion `Subtype.val : U → M`
of an open subset, where the pullback is the restriction of a vector field to `U`.

* `IsLocalDiffeomorphAt.mfderiv_apply_mpullback`: at a point where `f` is a local diffeomorphism,
  the differential of `f` sends the pulled-back field to `V (f x)`; that is, the pullback is
  `f`-related to `V` there.
* `IsLocalDiffeomorph.contMDiffOn_mpullback`: if `f` is a `C^n` local diffeomorphism and `V` is
  `C^m` on a set `t`, with `m + 1 ≤ n`, then the pullback is `C^m` on `f ⁻¹' t`.
* `VectorField.mfderiv_subtypeVal_mpullback_subtypeVal` and
  `VectorField.contMDiff_mpullback_subtypeVal`: for an open subset `U`, the restriction of `V`
  to `U` is related to `V` by the inclusion, and is a `C^m` vector field on `U` when `V` is
  `C^m` on `U`.

The first item has the proof of Tau Ceti's `Diffeomorph.mfderiv_apply_mpullback` and
`TauCeti.IsLocalRiemannianIsometry.mfderiv_apply_mpullback`, which state it for a global
diffeomorphism and for a local Riemannian isometry. The second follows Mathlib's
`ContMDiffOn.mpullback_vectorField_preimage`, with the invertibility of the differential given by
`IsLocalDiffeomorph.isInvertible_mfderiv`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2013, Chapter 8.
-/

public section

open Set TopologicalSpace
open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E H M : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H']
  {J : ModelWithCorners 𝕜 E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  {f : M → N} {m n : ℕ∞ω}

/-- At a point `x` where `f` is a local diffeomorphism, the differential of `f` sends the pullback
of a vector field `V` to the value of `V` at `f x`. -/
theorem IsLocalDiffeomorphAt.mfderiv_apply_mpullback {x : M} (hf : IsLocalDiffeomorphAt I J n f x)
    (hn : n ≠ 0) (V : Π y : N, TangentSpace J y) :
    mfderiv I J f x (VectorField.mpullback I J f V x) = V (f x) :=
  (hf.isInvertible_mfderiv hn).self_apply_inverse _

/-- The pullback of a vector field that is `C^m` on a set `t` along a `C^n` local diffeomorphism
`f`, with `m + 1 ≤ n`, is `C^m` on `f ⁻¹' t`. -/
theorem IsLocalDiffeomorph.contMDiffOn_mpullback [CompleteSpace E] [IsManifold I 1 M]
    [IsManifold J 1 N] (hf : IsLocalDiffeomorph I J n f) {V : Π y : N, TangentSpace J y}
    {t : Set N} (hV : ContMDiffOn J J.tangent m (T% V) t) (hmn : m + 1 ≤ n) :
    ContMDiffOn I I.tangent m (T% (VectorField.mpullback I J f V)) (f ⁻¹' t) :=
  hV.mpullback_vectorField_preimage hf.contMDiff
    (fun x _ ↦ hf.isInvertible_mfderiv (ne_bot_of_le_ne_bot (by simp) hmn) x) hmn

namespace VectorField

/-- The restriction `VectorField.mpullback I I Subtype.val V` of a vector field `V` to an open
set `U` is related to `V` by the inclusion of `U`. -/
theorem mfderiv_subtypeVal_mpullback_subtypeVal {U : Opens M} (V : Π x : M, TangentSpace I x)
    (x : U) :
    mfderiv I I (Subtype.val : U → M) x (VectorField.mpullback I I Subtype.val V x) = V x :=
  (TauCeti.isLocalDiffeomorph_subtype_val (n := 1) x).mfderiv_apply_mpullback one_ne_zero V

/-- On an open set `U`, the restriction `VectorField.mpullback I I Subtype.val V` of a vector field
`V` that is `C^m` on `U` is a `C^m` vector field on `U`. -/
theorem contMDiff_mpullback_subtypeVal [CompleteSpace E] [IsManifold I 1 M] {U : Opens M}
    {V : Π x : M, TangentSpace I x} (hV : ContMDiffOn I I.tangent m (T% V) U) :
    ContMDiff I I.tangent m (T% (VectorField.mpullback I I (Subtype.val : U → M) V)) := by
  have := (TauCeti.isLocalDiffeomorph_subtype_val (I := I) (n := ω) (U := U)).contMDiffOn_mpullback
    hV le_top
  rwa [show (Subtype.val : U → M) ⁻¹' U = univ from eq_univ_of_forall fun y ↦ y.property,
    contMDiffOn_univ] at this

end VectorField

end
