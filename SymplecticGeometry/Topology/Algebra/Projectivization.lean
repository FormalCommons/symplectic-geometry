/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Projectivization
public import SymplecticGeometry.LinearAlgebra.Projectivization.Basic
public import TauCeti.Topology.Algebra.Projectivization

/-!
# Topology of projective space: normalized representatives and induced maps

The representative `Projectivization.normalizedRep φ x` of a point `x` of `ℙ K V` on which a
continuous linear form `φ` takes the value `1` depends continuously on `x`, on the open set
`Projectivization.linearProjectionDomain φ` where `φ` does not vanish
(`Projectivization.continuousOn_normalizedRep`).

For a continuous semilinear equivalence `e`, the line `e.mapProjectivization ℓ` is the image of
`ℓ` under `e` (`ContinuousLinearEquiv.submodule_mapProjectivization`), the continuous counterpart
of Tau Ceti's `LinearEquiv.submodule_mapProjectivization`.

An injective linear map `f` out of a finite-dimensional space over a complete nontrivially normed
field is continuous, so `Projectivization.map f hf` is continuous; it is bundled as
`Projectivization.mapContinuousMap f hf`, after Tau Ceti's `infiniteGrassmannian.mapContinuousMap`.
-/

public section

open scoped LinearAlgebra.Projectivization

namespace Projectivization

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [TopologicalSpace K]
  [IsTopologicalDivisionRing K] [TopologicalSpace V] [ContinuousSMul K V]

/-- The normalized representative depends continuously on the point, where `φ` does not vanish. -/
theorem continuousOn_normalizedRep {φ : V →ₗ[K] K} (hφ : Continuous φ) :
    ContinuousOn (normalizedRep φ) (linearProjectionDomain φ) := by
  intro x hx
  refine ContinuousAt.continuousWithinAt ?_
  obtain ⟨v, rfl⟩ := isOpenQuotientMap_mk'.surjective x
  rw [← isOpenQuotientMap_mk'.continuousAt_comp_iff]
  have hv : φ v ≠ 0 := by simpa [mk'_eq_mk] using hx
  have h : normalizedRep φ ∘ mk' K = fun w : {w : V // w ≠ 0} ↦ (φ w)⁻¹ • (w : V) := by
    ext w
    simp [mk'_eq_mk]
  rw [h]
  exact ((hφ.comp continuous_subtypeVal).continuousAt.inv₀ hv).smul
    continuous_subtypeVal.continuousAt

section mapContinuousMap

variable {𝕜 V W U : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousSMul 𝕜 V] [T2Space V] [FiniteDimensional 𝕜 V]
  [AddCommGroup W] [Module 𝕜 W] [TopologicalSpace W] [IsTopologicalAddGroup W]
  [ContinuousSMul 𝕜 W]

/-- The continuous map `ℙ 𝕜 V → ℙ 𝕜 W` induced by an injective linear map `f : V →ₗ[𝕜] W`
on a finite-dimensional space `V`.

It is exposed so that `mapContinuousMap f hf x` and `map f hf x` agree by definition, as fibres
`E (mapContinuousMap f hf x)` of a bundle over `ℙ 𝕜 W` require. -/
@[expose] noncomputable def mapContinuousMap (f : V →ₗ[𝕜] W) (hf : Function.Injective f) :
    C(ℙ 𝕜 V, ℙ 𝕜 W) :=
  ⟨map f hf, continuous_map hf (LinearMap.continuous_of_finiteDimensional f)⟩

/-- The underlying function of `mapContinuousMap f hf` is `Projectivization.map f hf`. -/
@[simp]
theorem coe_mapContinuousMap (f : V →ₗ[𝕜] W) (hf : Function.Injective f) :
    ⇑(mapContinuousMap f hf) = map f hf :=
  (rfl)

theorem mapContinuousMap_apply (f : V →ₗ[𝕜] W) (hf : Function.Injective f) (x : ℙ 𝕜 V) :
    mapContinuousMap f hf x = map f hf x :=
  (rfl)

@[simp]
theorem mapContinuousMap_id :
    mapContinuousMap (LinearMap.id : V →ₗ[𝕜] V) (LinearEquiv.refl 𝕜 V).injective =
      ContinuousMap.id (ℙ 𝕜 V) :=
  ContinuousMap.ext fun x ↦ congrFun map_id x

@[simp]
theorem mapContinuousMap_comp [AddCommGroup U] [Module 𝕜 U] [TopologicalSpace U]
    [IsTopologicalAddGroup U] [ContinuousSMul 𝕜 U] [T2Space W] [FiniteDimensional 𝕜 W]
    (f : V →ₗ[𝕜] W) (hf : Function.Injective f) (g : W →ₗ[𝕜] U) (hg : Function.Injective g) :
    mapContinuousMap (g ∘ₗ f) (hg.comp hf) =
      (mapContinuousMap g hg).comp (mapContinuousMap f hf) :=
  ContinuousMap.ext fun x ↦ congrFun (map_comp f hf g hg) x

end mapContinuousMap

end Projectivization

namespace ContinuousLinearEquiv

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] [TopologicalSpace V]
  {L W : Type*} [DivisionRing L] [AddCommGroup W] [Module L W] [TopologicalSpace W]
  {σ : K →+* L} {σ' : L →+* K} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]

/-- The line `e.mapProjectivization ℓ` is the image of the line `ℓ` under `e`. -/
@[simp]
theorem submodule_mapProjectivization (e : V ≃SL[σ] W) (ℓ : ℙ K V) :
    (e.mapProjectivization ℓ).submodule = ℓ.submodule.map (e : V →ₛₗ[σ] W) := by
  rw [coe_mapProjectivization, Projectivization.submodule_map]

end ContinuousLinearEquiv

end
