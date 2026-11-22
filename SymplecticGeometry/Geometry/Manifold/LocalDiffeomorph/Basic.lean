/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Real
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset

/-!
# Local diffeomorphisms at a point and their local inverses

A map `f` is a `C^n` local diffeomorphism at `x` when it agrees, on the source of some `C^n`
partial diffeomorphism containing `x`, with that partial diffeomorphism. Mathlib's
`IsLocalDiffeomorphAt` is defined this way, but its body is not exposed to other modules, which
only see the chosen local inverse `Λ = IsLocalDiffeomorphAt.localInverse`. This file shows that
`f` agrees with `Λ.symm` on the target of `Λ`, since `f ∘ Λ` is the identity on the source of
`Λ`. So `Λ.symm` is a partial diffeomorphism that `f` agrees with (the converse is Tau Ceti's
`TauCeti.isLocalDiffeomorphAt_of_eqOn`), and `f` is a local diffeomorphism at every point of the
target of `Λ`, not only at `x`.

## Main results

* `IsLocalDiffeomorphAt.eqOn_localInverse_symm`: `f` agrees with the inverse of its local inverse
  on the target of the local inverse.
* `IsLocalDiffeomorphAt.exists_partialDiffeomorph`: a local diffeomorphism at `x` agrees with a
  partial diffeomorphism on a source that contains `x`.
* `IsLocalDiffeomorphAt.isLocalDiffeomorphOn_localInverse_target`: a local diffeomorphism `f` at
  `x` is a local diffeomorphism on the target of `hf.localInverse`.
* `IsLocalDiffeomorphAt.comp_iff_left`: composing on the left with a local diffeomorphism at the
  image point, a map continuous at `x` is a local diffeomorphism at `x` exactly when the composite
  is. It is the left-hand partner of Tau Ceti's `IsLocalDiffeomorphAt.comp_iff_right`, and
  combines Tau Ceti's `IsLocalDiffeomorphAt.of_comp_left` with Mathlib's
  `IsLocalDiffeomorphAt.comp`.
* `isLocalDiffeomorph_id`: the identity of a manifold is a local diffeomorphism.
* `IsLocalDiffeomorphAt.congr_of_eventuallyEq`: being a local diffeomorphism at `x` depends only
  on the germ of the map at `x`.
* `PartialDiffeomorph.isLocalDiffeomorphAt_symm_comp_comp_model`: a partial diffeomorphism of
  model vector spaces that preserves the ranges of two models with corners is a local
  diffeomorphism between their model spaces.
* `TauCeti.EuclideanHalfSpace.isLocalDiffeomorph_of_val_eq_smul`: multiplication by a positive
  constant is a local diffeomorphism of the half-space.
* `ModelWithCorners.isLocalDiffeomorphAt_coe`: a model with corners is a local diffeomorphism at
  every point that it sends into the interior of its range.
* `TauCeti.EuclideanHalfSpace.isLocalDiffeomorphAt_val_zero`: the coordinate of the half-line is a
  local diffeomorphism to `ℝ` where it is positive.
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

/-- A local diffeomorphism `f` at `x` agrees with the inverse of its local inverse
`hf.localInverse` on the target of `hf.localInverse`. -/
theorem eqOn_localInverse_symm (hf : IsLocalDiffeomorphAt I J n f x) :
    EqOn f hf.localInverse.symm hf.localInverse.target :=
  eqOn_of_leftInvOn_of_rightInvOn hf.localInverse_eqOn_right
    hf.localInverse.toPartialEquiv.rightInvOn hf.localInverse.toPartialEquiv.mapsTo_symm

/-- A `C^n` local diffeomorphism `f` at `x` agrees with some `C^n` partial diffeomorphism on
its source, and that source contains `x`. It is the inverse of
`IsLocalDiffeomorphAt.localInverse`. -/
theorem exists_partialDiffeomorph (hf : IsLocalDiffeomorphAt I J n f x) :
    ∃ Φ : PartialDiffeomorph I J M N n, x ∈ Φ.source ∧ EqOn f Φ Φ.source :=
  ⟨hf.localInverse.symm, by simpa using hf.localInverse_mem_target, by
    simpa using hf.eqOn_localInverse_symm⟩

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

end IsLocalDiffeomorphAt

/-- The identity of a manifold is a `C^n` local diffeomorphism. -/
theorem isLocalDiffeomorph_id : IsLocalDiffeomorph I I n (id : M → M) := by
  rw [← Diffeomorph.coe_refl I M n]
  exact Diffeomorph.isLocalDiffeomorph _

/-- A map that agrees near `x` with a local diffeomorphism at `x` is a local diffeomorphism at
`x`. -/
theorem IsLocalDiffeomorphAt.congr_of_eventuallyEq {g : M → N}
    (hf : IsLocalDiffeomorphAt I J n f x) (hfg : f =ᶠ[nhds x] g) :
    IsLocalDiffeomorphAt I J n g x := by
  obtain ⟨Φ, hxΦ, hfΦ⟩ := hf.exists_partialDiffeomorph
  obtain ⟨t, hft, ht, hxt⟩ := mem_nhds_iff.1 hfg
  refine TauCeti.isLocalDiffeomorphAt_of_eqOn (Φ := Φ.restrOpen t ht)
    (by rw [PartialDiffeomorph.restrOpen_source]; exact ⟨hxΦ, hxt⟩) fun y hy ↦ ?_
  rw [PartialDiffeomorph.restrOpen_source] at hy
  rw [PartialDiffeomorph.coe_restrOpen, ← hft hy.2]
  exact hfΦ hy.1

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

/-- The coordinate `t ↦ t 0` of the half-line `EuclideanHalfSpace 1` is a `C^n` local
diffeomorphism to `ℝ` at every point where it is positive. -/
theorem TauCeti.EuclideanHalfSpace.isLocalDiffeomorphAt_val_zero {t : EuclideanHalfSpace 1}
    (ht : 0 < t.val 0) :
    IsLocalDiffeomorphAt (𝓡∂ 1) 𝓘(ℝ) n (fun s : EuclideanHalfSpace 1 ↦ s.val 0) t := by
  let e : EuclideanSpace ℝ (Fin 1) ≃L[ℝ] ℝ :=
    (EuclideanSpace.equiv (Fin 1) ℝ).trans (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ)
  have he : IsLocalDiffeomorphAt (𝓡 1) 𝓘(ℝ) n e ((𝓡∂ 1) t) :=
    TauCeti.isLocalDiffeomorphAt_of_eqOn (Φ := e.toPartialDiffeomorph) (by simp)
      fun _ _ ↦ by simp
  have h := ((𝓡∂ 1).isLocalDiffeomorphAt_coe (n := n) (x := t) (by
    rwa [interior_range_modelWithCornersEuclideanHalfSpace])).comp (hg := he)
  convert h using 1
  funext s
  simp [e]

end
