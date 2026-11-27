/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.IntegralCurve.Basic
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.VectorField.Pullback
import TauCeti.Geometry.Manifold.Flow.Covering
import TauCeti.Geometry.Manifold.ContMDiff.MFDeriv
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Opens

/-!
# Pulling back vector fields along local diffeomorphisms

Mathlib's `VectorField.mpullback I J f V` is the vector field `x ↦ (df_x)⁻¹ (V (f x))`, which is
meaningful when the differential of `f` is invertible. This file gives its basic properties
when that differential is invertible at a point and when `f` is a local diffeomorphism, and
specializes them to the inclusion `Subtype.val : U → M` of an open subset, where the
pullback is the restriction of a vector field to `U`.

* `VectorField.mfderiv_apply_mpullback`: at a point where the differential of `f` is
  invertible, it sends the pulled-back field to `V (f x)`; that is, the pullback is
  `f`-related to `V` there. This covers maps that are not local diffeomorphisms, such as the
  inclusion of a regular sublevel at its boundary. `IsLocalDiffeomorphAt.mfderiv_apply_mpullback`
  is the case of a local diffeomorphism.
* `VectorField.mvfderiv_comp_apply_mpullback`: by the chain rule, the derivative of `g ∘ f`
  along the pulled-back field is the derivative of `g` along `V`.
* `IsLocalDiffeomorph.contMDiffOn_mpullback`: if `f` is a `C^n` local diffeomorphism and `V` is
  `C^m` on a set `t`, with `m + 1 ≤ n`, then the pullback is `C^m` on `f ⁻¹' t`.
* `IsLocalDiffeomorphAt.contMDiffAt_of_eventually_mfderiv_apply_eq`: conversely, a vector field
  that is, near `x`, the image under the differential of a local diffeomorphism `f` of a field
  that is `C^m` at `x`, is `C^m` at `f x`; near `f x` it is the pullback of that field along a
  local inverse of `f`.
* `VectorField.mfderiv_subtypeVal_mpullback_subtypeVal` and
  `VectorField.contMDiff_mpullback_subtypeVal`: for an open subset `U`, the restriction of `V`
  to `U` is related to `V` by the inclusion, and is a `C^m` vector field on `U` when `V` is
  `C^m` on `U`.
* `VectorField.isMIntegralCurveOn_mpullback_subtypeVal_iff`: a curve in `U` is an integral curve
  of the restriction of `V` exactly when, read in `M`, it is an integral curve of `V`.

The first item has the proof of Tau Ceti's `Diffeomorph.mfderiv_apply_mpullback` and
`TauCeti.IsLocalRiemannianIsometry.mfderiv_apply_mpullback`, which state it for a global
diffeomorphism and for a local Riemannian isometry. `IsLocalDiffeomorph.contMDiffOn_mpullback`
follows Mathlib's `ContMDiffOn.mpullback_vectorField_preimage`, with the invertibility of the
differential given by `IsLocalDiffeomorph.isInvertible_mfderiv`. The last is Mathlib's
`IsMIntegralCurveOn.map_of_mfderiv_eq` in one direction and Tau Ceti's
`IsLocalDiffeomorph.isMIntegralCurveOn_of_comp` in the other.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2013, Chapter 8.
-/

public section

open Set TopologicalSpace Filter
open scoped Manifold ContDiff Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E H M : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H']
  {J : ModelWithCorners 𝕜 E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  {f : M → N} {m n : ℕ∞ω}

namespace VectorField

/-- At a point `x` where the differential of `f` is invertible, the differential of `f` sends the
pullback of a vector field `V` to the value of `V` at `f x`; that is, the pullback is `f`-related
to `V` at `x`. -/
theorem mfderiv_apply_mpullback {x : M} (hf : (mfderiv I J f x).IsInvertible)
    (V : Π y : N, TangentSpace J y) :
    mfderiv I J f x (VectorField.mpullback I J f V x) = V (f x) :=
  hf.self_apply_inverse _

/-- **Chain rule along a pulled-back field.** If the differential of `f` at `x` is invertible
and `g` is differentiable at `f x`, then the derivative of `g ∘ f` at `x` along the
pullback of a vector field `V` is the derivative of `g` at `f x` along `V (f x)`. -/
theorem mvfderiv_comp_apply_mpullback {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {g : N → F} {x : M} (hg : MDifferentiableAt J 𝓘(𝕜, F) g (f x))
    (hf : (mfderiv I J f x).IsInvertible) (V : Π y : N, TangentSpace J y) :
    mvfderiv I (g ∘ f) x (VectorField.mpullback I J f V x) = mvfderiv J g (f x) (V (f x)) := by
  rw [mvfderiv_comp_apply x hg (mdifferentiableAt_of_isInvertible_mfderiv hf),
    mfderiv_apply_mpullback hf]

end VectorField

/-- At a point `x` where `f` is a local diffeomorphism, the differential of `f` sends the pullback
of a vector field `V` to the value of `V` at `f x`. -/
theorem IsLocalDiffeomorphAt.mfderiv_apply_mpullback {x : M} (hf : IsLocalDiffeomorphAt I J n f x)
    (hn : n ≠ 0) (V : Π y : N, TangentSpace J y) :
    mfderiv I J f x (VectorField.mpullback I J f V x) = V (f x) :=
  VectorField.mfderiv_apply_mpullback (hf.isInvertible_mfderiv hn) V

/-- The pullback of a vector field that is `C^m` on a set `t` along a `C^n` local diffeomorphism
`f`, with `m + 1 ≤ n`, is `C^m` on `f ⁻¹' t`. -/
theorem IsLocalDiffeomorph.contMDiffOn_mpullback [CompleteSpace E] [IsManifold I 1 M]
    [IsManifold J 1 N] (hf : IsLocalDiffeomorph I J n f) {V : Π y : N, TangentSpace J y}
    {t : Set N} (hV : ContMDiffOn J J.tangent m (T% V) t) (hmn : m + 1 ≤ n) :
    ContMDiffOn I I.tangent m (T% (VectorField.mpullback I J f V)) (f ⁻¹' t) :=
  hV.mpullback_vectorField_preimage hf.contMDiff
    (fun x _ ↦ hf.isInvertible_mfderiv (ne_bot_of_le_ne_bot (by simp) hmn) x) hmn

/-- **Smoothness of a vector field through a local diffeomorphism.** Let `f` be a `C^n` local
diffeomorphism at `x` and `m + 1 ≤ n`. If a vector field `V` on `N` is, near `x`, the image under
the differential of `f` of a vector field `X` on `M` that is `C^m` at `x`, then `V` is `C^m` at
`f x`: near `f x` it is the pullback of `X` along a local inverse of `f`. -/
theorem IsLocalDiffeomorphAt.contMDiffAt_of_eventually_mfderiv_apply_eq
    [IsManifold I 1 M] [IsManifold J 1 N] {x : M} (hf : IsLocalDiffeomorphAt I J n f x)
    (hmn : m + 1 ≤ n) {X : Π y : M, TangentSpace I y} {V : Π y : N, TangentSpace J y}
    (hX : ContMDiffAt I I.tangent m (T% X) x)
    (hXV : ∀ᶠ y in 𝓝 x, mfderiv I J f y (X y) = V (f y)) :
    ContMDiffAt J J.tangent m (T% V) (f x) := by
  refine (hf.contMDiffAt_comp_iff (le_trans le_self_add hmn)).1 ?_
  refine (hf.contMDiffAt.mfderiv_apply_sectionAlong (b := id) hX hmn).congr_of_eventuallyEq ?_
  filter_upwards [hXV] with y hy
  simp [hy]

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

section Real

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

namespace VectorField

/-- A curve `γ` in an open set `U` is an integral curve on `s` of the restriction
`VectorField.mpullback I I Subtype.val V` of `V` to `U` exactly when, read in `M`, it is an
integral curve of `V` on `s`. -/
theorem isMIntegralCurveOn_mpullback_subtypeVal_iff {U : Opens M}
    {V : Π x : M, TangentSpace I x} {γ : ℝ → U} {s : Set ℝ} :
    IsMIntegralCurveOn γ (VectorField.mpullback I I Subtype.val V) s ↔
      IsMIntegralCurveOn (Subtype.val ∘ γ) V s := by
  refine ⟨fun h ↦ h.map_of_mfderiv_eq (fun _ _ ↦ mdifferentiableAt_subtypeVal)
    (fun t _ ↦ mfderiv_subtypeVal_mpullback_subtypeVal V (γ t)), fun h ↦ ?_⟩
  exact (TauCeti.isLocalDiffeomorph_subtype_val (n := 1)).isMIntegralCurveOn_of_comp one_ne_zero
    (fun t _ ↦ mfderiv_subtypeVal_mpullback_subtypeVal V (γ t))
    (Topology.IsInducing.subtypeVal.continuousOn_iff.2 h.continuousOn) h

end VectorField

end Real

end
