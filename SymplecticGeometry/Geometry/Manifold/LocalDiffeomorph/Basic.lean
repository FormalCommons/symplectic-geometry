/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.Geometry.Manifold.Instances.Real
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
* `IsLocalDiffeomorphAt.exists_contMDiffAt_transition`: two maps that agree wherever two local
  diffeomorphisms into a common manifold do are related, near a point, by a map smooth there, as
  the transition maps of a gluing must be.
* `isLocalDiffeomorph_id`: the identity of a manifold is a local diffeomorphism.
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
* `TauCeti.EuclideanHalfSpace.isLocalDiffeomorph_of_val_eq_smul`: multiplication by a positive
  constant is a local diffeomorphism of the half-space.
* `ModelWithCorners.isLocalDiffeomorphAt_coe`: a model with corners is a local diffeomorphism at
  every point that it sends into the interior of its range.
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
  exact TauCeti.isLocalDiffeomorphAt_of_eqOn (Φ := Ψ) hx fun _ _ ↦ rfl

/-- A map of the half-space `EuclideanHalfSpace m` to itself that multiplies every point by a
fixed `ε > 0` is a `C^k` local diffeomorphism, for every `k`. -/
theorem TauCeti.EuclideanHalfSpace.isLocalDiffeomorph_of_val_eq_smul {m : ℕ} [NeZero m]
    {k : WithTop ℕ∞} {ε : ℝ} (hε : 0 < ε) {f : EuclideanHalfSpace m → EuclideanHalfSpace m}
    (hf : ∀ t, (f t).val = ε • t.val) : IsLocalDiffeomorph (𝓡∂ m) (𝓡∂ m) k f := by
  intro t
  let Θ := ((LinearEquiv.smulOfNeZero ℝ (EuclideanSpace ℝ (Fin m)) ε
    hε.ne').toContinuousLinearEquiv).toPartialDiffeomorph (n := k)
  have hΘ : ∀ y : EuclideanSpace ℝ (Fin m), Θ y = ε • y := fun y ↦ by simp [Θ]
  have h := Θ.isLocalDiffeomorphAt_symm_comp_comp_model (𝓡∂ m) (𝓡∂ m) (x := t)
    (fun y _ ↦ by
      simp only [hΘ, range_modelWithCornersEuclideanHalfSpace, mem_ofPred_eq, PiLp.smul_apply,
        smul_eq_mul]
      exact ⟨fun hy ↦ nonneg_of_mul_nonneg_right hy hε, fun hy ↦ mul_nonneg hε.le hy⟩)
    (by simp [Θ])
  convert h using 1
  funext s
  simp only [comp_apply, hΘ]
  rw [← (𝓡∂ m).left_inv (f s)]
  congr 1
  rw [modelWithCornersEuclideanHalfSpace_apply, modelWithCornersEuclideanHalfSpace_apply, hf]

/-- A model with corners `I` is a `C^n` local diffeomorphism from its model space to the model
vector space at every point that it sends into the interior of its range. -/
theorem ModelWithCorners.isLocalDiffeomorphAt_coe {x : H} (hx : I x ∈ interior (range I)) :
    IsLocalDiffeomorphAt I 𝓘(𝕜, E) n I x := by
  have h := TauCeti.isLocalDiffeomorphAt_extChartAt (I := I) (n := n) (mem_extChartAt_source x)
    (by simpa [extChartAt_self_eq] using hx)
  simpa [extChartAt_self_eq] using h

/-- The image of a compact subset of the source of a partial diffeomorphism is compact. -/
theorem PartialDiffeomorph.isCompact_image_of_subset_source (Φ : PartialDiffeomorph I J M N n)
    {K : Set M} (hK : IsCompact K) (hKs : K ⊆ Φ.source) : IsCompact (Φ '' K) := by
  simpa using Φ.toOpenPartialHomeomorph.isCompact_image_of_subset_source hK (by simpa using hKs)

end
