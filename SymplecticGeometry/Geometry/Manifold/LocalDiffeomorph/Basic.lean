/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.Algebra.SMul
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Diffeomorph
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
public import SymplecticGeometry.Topology.OpenPartialHomeomorph.Compact

/-!
# Local diffeomorphisms at a point and their local inverses

A map `f` is a `C^n` local diffeomorphism at `x` when it agrees, on the source of some `C^n`
partial diffeomorphism containing `x`, with that partial diffeomorphism. Mathlib's
`IsLocalDiffeomorphAt` is defined this way, but its body is not exposed to other modules, which
only see the chosen local inverse `Λ = IsLocalDiffeomorphAt.localInverse`. Tau Ceti's
`IsLocalDiffeomorphAt.eqOn_localInverse_symm` says that `f` agrees with `Λ.symm` on the target of
`Λ`. So `Λ.symm` is a partial diffeomorphism that `f` agrees with (the converse is Tau Ceti's
`TauCeti.isLocalDiffeomorphAt_of_eqOn`), and `f` is a local diffeomorphism at every point of the
target of `Λ`, not only at `x`.

## Main results

* `IsLocalDiffeomorphAt.isLocalDiffeomorphOn_localInverse_target`: a local diffeomorphism `f` at
  `x` is a local diffeomorphism on the target of `hf.localInverse`.
* `IsLocalDiffeomorphAt.comp_iff_left`: composing on the left with a local diffeomorphism at the
  image point, a map continuous at `x` is a local diffeomorphism at `x` exactly when the composite
  is. It is the left-hand partner of Tau Ceti's `IsLocalDiffeomorphAt.comp_iff_right`, and
  combines Tau Ceti's `IsLocalDiffeomorphAt.of_comp_left` with Mathlib's
  `IsLocalDiffeomorphAt.comp`.
* `MDifferentiableAt.of_comp_isLocalDiffeomorph`: a map continuous at a point is differentiable
  there when its composite with a local diffeomorphism at the image point is. It is the
  differentiable counterpart of Tau Ceti's `ContMDiffWithinAt.of_comp_isLocalDiffeomorph`.
* `IsLocalDiffeomorphAt.exists_contMDiffAt_transition`: two maps that agree wherever two local
  diffeomorphisms into a common manifold do are related, near a point, by a map smooth there, as
  the transition maps of a gluing must be.
* `isLocalDiffeomorph_id`: the identity of a manifold is a local diffeomorphism.
* `isOpen_setOfPred_isLocalDiffeomorphAt`: the points at which a map is a local diffeomorphism
  form an open set, by Tau Ceti's `IsLocalDiffeomorphAt.eventually`.
* `isLocalDiffeomorphAt_smul_iff`: a map that commutes with actions of a group by `C^n` maps is a
  local diffeomorphism at `g • x` exactly when it is one at `x`. It composes with Tau Ceti's
  diffeomorphisms `Diffeomorph.constSmul` and applies Tau Ceti's
  `Diffeomorph.isLocalDiffeomorphAt_comp_diffeomorph_iff` and
  `Diffeomorph.isLocalDiffeomorphAt_diffeomorph_comp_iff`.
* `ContinuousLinearEquiv.isLocalDiffeomorph`: a continuous linear equivalence of normed spaces
  is a local diffeomorphism, for every `n`; `isLocalDiffeomorph_neg` is the case of negation.
* `PartialDiffeomorph.isLocalDiffeomorphAt_symm_comp_comp_model`: a partial diffeomorphism of
  model vector spaces that preserves the ranges of two models with corners is a local
  diffeomorphism between their model spaces.
* `ModelWithCorners.isLocalDiffeomorphAt_coe`: a model with corners is a local diffeomorphism at
  every point that it sends into the interior of its range.
* `PartialDiffeomorph.contMDiffAt`: a partial diffeomorphism is `C^n` at each point of its
  source.
* `PartialDiffeomorph.isCompact_image_of_subset_source`: a partial diffeomorphism sends compact
  subsets of its source to compact sets; it is
  `OpenPartialHomeomorph.isCompact_image_of_subset_source` applied to `Φ.toOpenPartialHomeomorph`.
-/

public section

open Set Function
open scoped Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {J : ModelWithCorners 𝕜 E' H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {n : WithTop ℕ∞} {f : M → N} {x : M}

namespace IsLocalDiffeomorphAt

/-- A local diffeomorphism `f` at `x` is a local diffeomorphism at every point of the target of
its local inverse. -/
theorem isLocalDiffeomorphOn_localInverse_target (hf : IsLocalDiffeomorphAt I J n f x) :
    IsLocalDiffeomorphOn I J n f hf.localInverse.target := fun z ↦
  TauCeti.isLocalDiffeomorphAt_of_eqOn (Φ := hf.localInverse.symm) (by simp)
    (by simpa using hf.eqOn_localInverse_symm)

/-- **Composing with a local diffeomorphism on the left.** If `g` is a `C^n` local diffeomorphism
at `f x` and `f` is continuous at `x`, then `g ∘ f` is a `C^n` local diffeomorphism at `x` exactly
when `f` is one at `x`. -/
theorem comp_iff_left {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] {G' : Type*}
    [TopologicalSpace G'] {K : ModelWithCorners 𝕜 F' G'} {P : Type*} [TopologicalSpace P]
    [ChartedSpace G' P] {g : N → P} (hg : IsLocalDiffeomorphAt J K n g (f x))
    (hf : ContinuousAt f x) :
    IsLocalDiffeomorphAt I K n (g ∘ f) x ↔ IsLocalDiffeomorphAt I J n f x :=
  ⟨fun h ↦ h.of_comp_left hg hf, fun h ↦ h.comp (hg := hg)⟩

/-- Let `f` be a `C^n` local diffeomorphism at `g y`, with `n ≠ 0`, and let `g` be continuous at
`y`. If `f ∘ g` is differentiable at `y`, so is `g`: near `y` it is the local inverse of `f`
composed with `f ∘ g`. -/
theorem _root_.MDifferentiableAt.of_comp_isLocalDiffeomorph {F' : Type*}
    [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] {G' : Type*} [TopologicalSpace G']
    {K : ModelWithCorners 𝕜 F' G'} {P : Type*} [TopologicalSpace P] [ChartedSpace G' P]
    {g : P → M} {y : P} (hf : IsLocalDiffeomorphAt I J n f (g y)) (hn : n ≠ 0)
    (hg : ContinuousAt g y) (hfg : MDifferentiableAt K J (f ∘ g) y) :
    MDifferentiableAt K I g y :=
  ((hf.mdifferentiableAt_localInverse hn).comp y hfg).congr_of_eventuallyEq
    (hf.localInverse_eventuallyEq_left.comp_tendsto hg).symm

open Topology in
/-- **Transition maps through local diffeomorphisms.** Let `f : M → N` and `g : M' → N` be `C^n`
local diffeomorphisms at `x` and `y`, with `f x = g y`, and let `φ : M → X` and `ψ : M' → X` be
maps with `φ u = ψ v` whenever `f u = g v`. Then some map `T : M → M'`, `C^n` at `x`, has
`ψ ∘ T = φ` near `x`: the local inverse of `g` at `y` composed with `f`. -/
theorem exists_contMDiffAt_transition (hf : IsLocalDiffeomorphAt I J n f x) {M' : Type*}
    [TopologicalSpace M'] [ChartedSpace H M'] {g : M' → N} {y : M'}
    (hg : IsLocalDiffeomorphAt I J n g y) (hxy : f x = g y) {X : Type*} {φ : M → X}
    {ψ : M' → X} (h : ∀ u v, f u = g v → φ u = ψ v) :
    ∃ T : M → M', ContMDiffAt I I n T x ∧ ψ ∘ T =ᶠ[𝓝 x] φ := by
  refine ⟨hg.localInverse ∘ f, ?_, ?_⟩
  · have h₁ := hg.contMDiffAt_localInverse
    rw [← hxy] at h₁
    exact h₁.comp x hf.contMDiffAt
  · have h₂ := hg.localInverse_eventuallyEq_right
    rw [← hxy] at h₂
    filter_upwards [hf.contMDiffAt.continuousAt.eventually h₂] with u hu
    exact (h u _ hu.symm).symm

end IsLocalDiffeomorphAt

namespace SymplecticGeometry

/-- The identity of a manifold is a `C^n` local diffeomorphism. -/
theorem isLocalDiffeomorph_id : IsLocalDiffeomorph I I n (id : M → M) := by
  rw [← Diffeomorph.coe_refl I M n]
  exact Diffeomorph.isLocalDiffeomorph _

variable (I J n f) in
/-- The set of points at which a map is a `C^n` local diffeomorphism is open. -/
theorem isOpen_setOfPred_isLocalDiffeomorphAt : IsOpen {x | IsLocalDiffeomorphAt I J n f x} :=
  isOpen_iff_mem_nhds.2 fun _ h ↦ h.eventually

/-- **Local diffeomorphy of an equivariant map is invariant under the group.** If `f` commutes
with actions of a group `G` on `M` and on `N` by `C^n` maps, then `f` is a `C^n` local
diffeomorphism at `g • x` exactly when it is one at `x`: the actions of `g` are diffeomorphisms. -/
theorem isLocalDiffeomorphAt_smul_iff {G : Type*} [Group G] [MulAction G M] [MulAction G N]
    [ContMDiffConstSMul I n G M] [ContMDiffConstSMul J n G N]
    (hf : ∀ (g : G) y, f (g • y) = g • f y) (g : G) :
    IsLocalDiffeomorphAt I J n f (g • x) ↔ IsLocalDiffeomorphAt I J n f x := by
  have hT : f ∘ Diffeomorph.constSmul I n g = Diffeomorph.constSmul J n g ∘ f :=
    funext fun y ↦ by simp only [comp_apply, Diffeomorph.constSmul_apply, hf]
  have h := (Diffeomorph.constSmul I n g).isLocalDiffeomorphAt_comp_diffeomorph_iff (K := J)
    (f := f) (x := x) le_rfl
  rw [hT, (Diffeomorph.constSmul J n g).isLocalDiffeomorphAt_diffeomorph_comp_iff le_rfl] at h
  rwa [Diffeomorph.constSmul_apply, Iff.comm] at h

end SymplecticGeometry

/-- A continuous linear equivalence of normed spaces is a `C^n` local diffeomorphism, for every
`n`. -/
theorem ContinuousLinearEquiv.isLocalDiffeomorph (A : E ≃L[𝕜] E') :
    IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E') n A :=
  fun _ ↦ TauCeti.isLocalDiffeomorphAt_of_eqOn (Φ := A.toPartialDiffeomorph) (by simp)
    fun _ _ ↦ by simp

namespace SymplecticGeometry

/-- Negation of a normed space is a `C^n` local diffeomorphism. -/
theorem isLocalDiffeomorph_neg : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) n (Neg.neg : E → E) :=
  (ContinuousLinearEquiv.neg 𝕜 (M := E)).isLocalDiffeomorph

end SymplecticGeometry

/-- A partial diffeomorphism `Θ` between the model vector spaces of `I` and `J` which, on its
source, sends exactly the points of `range I` into `range J` restricts to a local diffeomorphism
`J.symm ∘ Θ ∘ I` between the model spaces of `I` and `J`, at every point that `I` sends into the
source of `Θ`. -/
theorem PartialDiffeomorph.isLocalDiffeomorphAt_symm_comp_comp_model
    (I : ModelWithCorners 𝕜 E H) (J : ModelWithCorners 𝕜 E' H')
    (Θ : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E') E E' n)
    (hΘ : ∀ y ∈ Θ.source, Θ y ∈ range J ↔ y ∈ range I) {x : H} (hx : I x ∈ Θ.source) :
    IsLocalDiffeomorphAt I J n (J.symm ∘ Θ ∘ I) x := by
  have hsrc (y : H) (hy : I y ∈ Θ.source) : Θ (I y) ∈ range J :=
    (hΘ _ hy).2 (mem_range_self y)
  -- `PartialDiffeomorph` coerces to functions through its `PartialEquiv`, whose inverse laws are
  -- stated for that coercion, hence the `show`s below.
  have htgt (z : H') (hz : J z ∈ Θ.target) : Θ.toPartialEquiv.symm (J z) ∈ range I := by
    have h := Θ.map_target hz
    refine (hΘ _ h).1 ?_
    rw [show Θ (Θ.toPartialEquiv.symm (J z)) = J z from Θ.right_inv hz]
    exact mem_range_self z
  let Ψ : PartialDiffeomorph I J H H' n :=
    { toFun := J.symm ∘ Θ ∘ I
      invFun := I.symm ∘ Θ.toPartialEquiv.symm ∘ J
      source := I ⁻¹' Θ.source
      target := J ⁻¹' Θ.target
      map_source' := fun y hy ↦ by
        simp only [mem_preimage, comp_apply, J.right_inv (hsrc y hy)]
        exact Θ.map_source hy
      map_target' := fun z hz ↦ by
        simp only [mem_preimage, comp_apply, I.right_inv (htgt z hz)]
        exact Θ.map_target hz
      left_inv' := fun y hy ↦ by
        simp only [comp_apply, J.right_inv (hsrc y hy)]
        rw [show Θ.toPartialEquiv.symm (Θ (I y)) = I y from Θ.left_inv hy, I.left_inv]
      right_inv' := fun z hz ↦ by
        simp only [comp_apply, I.right_inv (htgt z hz)]
        rw [show Θ (Θ.toPartialEquiv.symm (J z)) = J z from Θ.right_inv hz, J.left_inv]
      open_source := Θ.open_source.preimage I.continuous
      open_target := Θ.open_target.preimage J.continuous
      contMDiffOn_toFun := J.contMDiffOn_symm.comp
        (Θ.contMDiffOn.comp I.contMDiff.contMDiffOn fun _ hy ↦ hy) fun y hy ↦ hsrc y hy
      contMDiffOn_invFun := I.contMDiffOn_symm.comp
        (Θ.symm.contMDiffOn.comp J.contMDiff.contMDiffOn fun _ hz ↦ hz) fun z hz ↦
          htgt z hz }
  exact Ψ.isLocalDiffeomorphAt _ _ _ hx

/-- A model with corners `I` is a `C^n` local diffeomorphism from its model space to the model
vector space at every point that it sends into the interior of its range. -/
theorem ModelWithCorners.isLocalDiffeomorphAt_coe {x : H} (hx : I x ∈ interior (range I)) :
    IsLocalDiffeomorphAt I 𝓘(𝕜, E) n I x := by
  have h := TauCeti.isLocalDiffeomorphAt_extChartAt (I := I) (n := n) (mem_extChartAt_source x)
    (by simpa [extChartAt_self_eq] using hx)
  simpa [extChartAt_self_eq] using h

/-- A `C^n` partial diffeomorphism is `C^n` at each point of its source. It is the `C^n`
counterpart of Mathlib's `PartialDiffeomorph.mdifferentiableAt`. -/
protected theorem PartialDiffeomorph.contMDiffAt (Φ : PartialDiffeomorph I J M N n) {x : M}
    (hx : x ∈ Φ.source) : ContMDiffAt I J n Φ x :=
  Φ.contMDiffOn.contMDiffAt (Φ.open_source.mem_nhds hx)

/-- The image of a compact subset of the source of a partial diffeomorphism is compact. -/
theorem PartialDiffeomorph.isCompact_image_of_subset_source (Φ : PartialDiffeomorph I J M N n)
    {K : Set M} (hK : IsCompact K) (hKs : K ⊆ Φ.source) : IsCompact (Φ '' K) := by
  simpa using Φ.toOpenPartialHomeomorph.isCompact_image_of_subset_source hK (by simpa using hKs)

end
