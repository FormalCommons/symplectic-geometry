/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Map
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Topology
public import TauCeti.Topology.VectorBundle.Thom.FiberwiseEquiv

/-!
# The map of Thom pairs of normal bundles of a commuting triangle

Let `f' : Z → X'` and `f : Z → X` be embeddings of the same manifold `Z`, and `v : X' → X` a `C¹`
map with `v ∘ f' = f` whose derivative is invertible at every point `f' x`. Then the derivative of
`v` identifies the normal space of `f'` at `x` with that of `f`
(`normalSpaceEquivOfComp`): this is Tau Ceti's `normalSpaceEquiv` for the square
`v ∘ f' = f ∘ id`. By Tau Ceti's `continuous_normalBundleMap`, the resulting map of total
spaces is continuous, so Tau Ceti's `thomPairMapOfFiberwise` turns it into a map of Thom pairs
`(ν_{f'}, ν_{f'} ∖ 0) ⟶ (ν_f, ν_f ∖ 0)` over the identity of `Z` (`thomPairMapOfComp`). On the
fibre over `x` it is the isomorphism of fibre pairs of the equivalence at `x`
(`fiberThomPairMap_comp_thomPairMapOfComp`).

The two ambient manifolds may have different models and the embeddings different orders of
smoothness. The main examples are a diffeomorphism `φ : X' ≃ X` with `f' = φ⁻¹ ∘ f`, and the
inclusion of an open set `X' ⊆ X` that contains the range of `f`.

## Main definitions

* `TauCeti.SmoothEmbedding.normalSpaceEquivOfComp`: the isomorphism `ν_{f'} x ≃ ν_f x` given by
  the derivative of `v`.
* `TauCeti.SmoothEmbedding.thomPairMapOfComp`: the map of Thom pairs of normal bundles that it
  induces.

## Main results

* `TauCeti.SmoothEmbedding.normalSpaceEquivOfComp_normalClass`: on the normal class of a tangent
  vector `w`, the isomorphism is the normal class of `dv w`.
* `TauCeti.SmoothEmbedding.continuous_normalSpaceEquivOfComp`: its total-space map is continuous.
* `TauCeti.SmoothEmbedding.fiberThomPairMap_comp_thomPairMapOfComp`: on the fibre over `x`, the
  map of Thom pairs is the fibre-pair isomorphism of the derivative.
-/

public section

noncomputable section

open Bundle CategoryTheory
open scoped Manifold ContDiff

universe w

namespace TauCeti.SmoothEmbedding

variable {E H G G' : Type*} {V V' Z : Type w} {X X' : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup V'] [NormedSpace ℝ V']
  [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace G'] {I : ModelWithCorners ℝ E H}
  {J : ModelWithCorners ℝ V G} {J' : ModelWithCorners ℝ V' G'}
  [TopologicalSpace Z] [ChartedSpace H Z] [TopologicalSpace X] [ChartedSpace G X]
  [TopologicalSpace X'] [ChartedSpace G' X'] {n m : ℕ∞ω} {v : X' → X}

/-- **The normal spaces of a commuting triangle of embeddings.** For embeddings `f' : Z → X'` and
`f : Z → X` and a map `v : X' → X` with `v ∘ f' = f` whose derivative is invertible at each point
`f' x`, the isomorphism from the normal space of `f'` at `x` to that of `f` induced by the
derivative of `v`: Tau Ceti's `normalSpaceEquiv` for the square `v ∘ f' = f ∘ id`. -/
def normalSpaceEquivOfComp (f' : SmoothEmbedding I J' n Z X') (f : SmoothEmbedding I J m Z X)
    (hn : n ≠ 0) (hm : m ≠ 0) (hv : ∀ x, (mfderiv J' J v (f' x)).IsInvertible) (h : v ∘ f' = f)
    (x : Z) : f'.isImmersion.NormalSpace x hn ≃L[ℝ] f.isImmersion.NormalSpace x hm :=
  f'.normalSpaceEquiv f hn hm (u := _root_.id) (hv x)
    (by rw [mfderiv_id]; exact Function.surjective_id) (.of_eq h)

/-- `normalSpaceEquivOfComp` is Tau Ceti's normal-space equivalence of the square
`v ∘ f' = f ∘ id`. -/
theorem normalSpaceEquivOfComp_def (f' : SmoothEmbedding I J' n Z X')
    (f : SmoothEmbedding I J m Z X) (hn : n ≠ 0) (hm : m ≠ 0)
    (hv : ∀ x, (mfderiv J' J v (f' x)).IsInvertible) (h : v ∘ f' = f) (x : Z) :
    f'.normalSpaceEquivOfComp f hn hm hv h x =
      f'.normalSpaceEquiv f hn hm (u := _root_.id) (hv x)
        (by rw [mfderiv_id]; exact Function.surjective_id) (.of_eq h) :=
  (rfl)

/-- On the normal class of a tangent vector `w` of `X'` at `f' x`, `normalSpaceEquivOfComp` is
the normal class of its image `dv w`. -/
@[simp]
theorem normalSpaceEquivOfComp_normalClass (f' : SmoothEmbedding I J' n Z X')
    (f : SmoothEmbedding I J m Z X) (hn : n ≠ 0) (hm : m ≠ 0)
    (hv : ∀ x, (mfderiv J' J v (f' x)).IsInvertible) (h : v ∘ f' = f) (x : Z)
    (w : TangentSpace J' (f' x)) :
    f'.normalSpaceEquivOfComp f hn hm hv h x (f'.isImmersion.normalClass x hn w) =
      f.isImmersion.normalClass x hm (tangentSpaceCast J (v (f' x)) (f x)
          (mfderiv J' J v (f' x) w)) :=
  normalSpaceEquiv_normalClass _ _ _ _ _ _ _ w

variable [IsManifold J' 1 X'] [IsManifold J 1 X] {K K' : Type*}

/-- For `v` of class `C¹`, the total-space map `w ↦ (w.proj, dv w)` of `normalSpaceEquivOfComp`,
from the normal bundle of `f'` to that of `f`, is continuous for their quotient topologies. -/
theorem continuous_normalSpaceEquivOfComp (f' : SmoothEmbedding I J' n Z X')
    (f : SmoothEmbedding I J m Z X) (hn : n ≠ 0) (hm : m ≠ 0) (hv₁ : ContMDiff J' J 1 v)
    (hv : ∀ x, (mfderiv J' J v (f' x)).IsInvertible) (h : v ∘ f' = f) :
    Continuous fun w : TotalSpace K (fun x ↦ f'.isImmersion.NormalSpace x hn) ↦
      TotalSpace.mk' K' (E := fun x ↦ f.isImmersion.NormalSpace x hm) w.proj
        (f'.normalSpaceEquivOfComp f hn hm hv h w.proj w.snd) := by
  convert f'.continuous_normalBundleMap (K := K) (K' := K') f hn hm (u := _root_.id) hv₁ h
    using 1
  funext w
  rw [normalBundleMap_apply, normalSpaceEquivOfComp_def,
    ← normalSpaceEquiv_toContinuousLinearMap]
  -- The base points are `w.proj` and `_root_.id w.proj`, and the coercion of the equivalence to
  -- a continuous linear map applies it: both sides agree up to unfolding `id` and that coercion.
  rfl

/-- **The map of Thom pairs of normal bundles of a commuting triangle.** For a `C¹` map `v : X' → X`
with `v ∘ f' = f` and invertible derivative at each point `f' x`, the map
`(ν', ν' ∖ 0) ⟶ (ν, ν ∖ 0)` from the Thom pair of the normal bundle of `f'` to that of `f`, over
the identity of `Z`, which is the derivative of `v` on each fibre (`normalSpaceEquivOfComp`). -/
def thomPairMapOfComp (f' : SmoothEmbedding I J' n Z X') (f : SmoothEmbedding I J m Z X)
    (hn : n ≠ 0) (hm : m ≠ 0) (hv₁ : ContMDiff J' J 1 v)
    (hv : ∀ x, (mfderiv J' J v (f' x)).IsInvertible) (h : v ∘ f' = f) :
    thomPair K (fun x ↦ f'.isImmersion.NormalSpace x hn) ⟶ thomPair K'
        (fun x ↦ f.isImmersion.NormalSpace x hm) :=
  thomPairMapOfFiberwise (g := ContinuousMap.id Z)
    (f'.continuous_normalSpaceEquivOfComp f hn hm hv₁ hv h)

/-- `thomPairMapOfComp` is Tau Ceti's map of Thom pairs of the fibrewise isomorphism
`normalSpaceEquivOfComp`. -/
theorem thomPairMapOfComp_def (f' : SmoothEmbedding I J' n Z X') (f : SmoothEmbedding I J m Z X)
    (hn : n ≠ 0) (hm : m ≠ 0) (hv₁ : ContMDiff J' J 1 v)
    (hv : ∀ x, (mfderiv J' J v (f' x)).IsInvertible) (h : v ∘ f' = f) :
    f'.thomPairMapOfComp (K := K) (K' := K') f hn hm hv₁ hv h =
      thomPairMapOfFiberwise (g := ContinuousMap.id Z)
        (f'.continuous_normalSpaceEquivOfComp f hn hm hv₁ hv h) :=
  (rfl)

/-- On total spaces, `thomPairMapOfComp` keeps the base point and applies
`normalSpaceEquivOfComp` in the fibre. -/
@[simp]
theorem thomPairMapOfComp_fst_apply (f' : SmoothEmbedding I J' n Z X')
    (f : SmoothEmbedding I J m Z X) (hn : n ≠ 0) (hm : m ≠ 0) (hv₁ : ContMDiff J' J 1 v)
    (hv : ∀ x, (mfderiv J' J v (f' x)).IsInvertible) (h : v ∘ f' = f)
    (w : TotalSpace K (fun x ↦ f'.isImmersion.NormalSpace x hn)) :
    TopPair.Hom.fst (f'.thomPairMapOfComp (K' := K') f hn hm hv₁ hv h) w =
      TotalSpace.mk' K' (E := fun x ↦ f.isImmersion.NormalSpace x hm) w.proj
        (f'.normalSpaceEquivOfComp f hn hm hv h w.proj w.snd) :=
  thomPairMapOfFiberwise_fst_apply _ w

/-- On the fibre over `x`, `thomPairMapOfComp` is the isomorphism of fibre pairs induced by
`normalSpaceEquivOfComp` at `x`. -/
theorem fiberThomPairMap_comp_thomPairMapOfComp [TopologicalSpace K] [TopologicalSpace K']
    (f' : SmoothEmbedding I J' n Z X') (f : SmoothEmbedding I J m Z X) (hn : n ≠ 0) (hm : m ≠ 0)
    [FiberBundle K (fun x ↦ f'.isImmersion.NormalSpace x hn)]
        [FiberBundle K' (fun x ↦ f.isImmersion.NormalSpace x hm)]
    (hv₁ : ContMDiff J' J 1 v) (hv : ∀ x, (mfderiv J' J v (f' x)).IsInvertible)
    (h : v ∘ f' = f) (x : Z) :
    fiberThomPairMap K (fun x ↦ f'.isImmersion.NormalSpace x hn) x ≫ f'.thomPairMapOfComp f hn hm
        hv₁ hv h =
      (f'.normalSpaceEquivOfComp f hn hm hv h x).complZeroPairIso.hom ≫
        fiberThomPairMap K' (fun x ↦ f.isImmersion.NormalSpace x hm) x :=
  fiberThomPairMap_comp_thomPairMapOfFiberwise (g := ContinuousMap.id Z) _ x

end TauCeti.SmoothEmbedding

end
