/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.LinearAlgebra.Symplectic.CompatibleTangent.Basic
public import TauCeti.Geometry.Symplectic.Cayley.Smooth
public import TauCeti.Geometry.Symplectic.ExistsCompatible
public import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# Cayley coordinates on the compatible complex structures

Let `ω` be a symplectic form on a finite-dimensional real normed space `V`, and `J₀` an
`ω`-compatible complex structure. Tau Ceti's compatible Cayley transform
(`TauCeti.SymplecticForm.Compatible.compatibleCayleyEquiv`) is a bijection from the
`ω`-compatible complex structures onto the compatible Cayley ball of `J₀`, with inverse
`C ↦ J₀ (1 + C) (1 - C)⁻¹`. This file reads it in the continuous endomorphisms, as a map into
the compatible tangent space at `J₀`, and shows that it is an open embedding. It also fixes the
base point and the model space of the global Cayley chart on the compatible structures.

## Main definitions and results

* `TauCeti.SymplecticForm.compatibleTangentSpaceCLM`: Tau Ceti's compatible tangent space at `J`,
  read in the continuous endomorphisms `V →L[ℝ] V`.
* `TauCeti.SymplecticForm.isOpen_setOf_strictContraction`: the continuous endomorphisms that
  strictly contract `v ↦ ω(v, J₀ v)` form an open set.
* `TauCeti.SymplecticForm.Compatible.cayleyCoord`: the Cayley coordinates `J ↦ J₀.cayley J`, a map
  from the compatible structures to `ω.compatibleTangentSpaceCLM J₀`, with
  `Compatible.range_cayleyCoord` (the strict contractions of that space),
  `Compatible.toContinuousLinearMap_eq_of_cayleyCoord_eq` (the inverse formula) and
  `Compatible.isOpenEmbedding_cayleyCoord`.
* `TauCeti.SymplecticForm.compatibleBase` and `TauCeti.SymplecticForm.compatibleModel`: a chosen
  compatible structure, and the compatible tangent space there, the model of the global chart.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third
  edition][McDuffSalamon2017], Proposition 2.5.13 (the Cayley transform proof of Sévennec).
-/

public section

open scoped Manifold

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ω : SymplecticForm V} {J₀ : AlmostComplexStructure V}

variable (ω) in
/-- The compatible tangent space `ω.compatibleTangentSpace J` read in the continuous
endomorphisms: the continuous `C` that anticommute with `J` and are skew-adjoint for `ω`. -/
def compatibleTangentSpaceCLM (J : AlmostComplexStructure V) : Submodule ℝ (V →L[ℝ] V) :=
  (ω.compatibleTangentSpace J).comap (ContinuousLinearMap.coeLM ℝ)

/-- A continuous endomorphism lies in `ω.compatibleTangentSpaceCLM J` exactly when its underlying
linear map lies in `ω.compatibleTangentSpace J`. -/
@[simp]
theorem mem_compatibleTangentSpaceCLM {J : AlmostComplexStructure V} {C : V →L[ℝ] V} :
    C ∈ ω.compatibleTangentSpaceCLM J ↔ C.toLinearMap ∈ ω.compatibleTangentSpace J :=
  Iff.rfl

variable (ω J₀) in
/-- The continuous endomorphisms that strictly contract the quadratic form `v ↦ ω(v, J₀ v)` form
an open set: they are those for which the bilinear form `ω(v, J₀ w) - ω(C v, J₀ (C w))` is
positive on the diagonal, an open condition. -/
theorem isOpen_setOf_strictContraction [FiniteDimensional ℝ V] :
    IsOpen {C : V →L[ℝ] V | ∀ v, v ≠ 0 → ω (C v) (J₀ (C v)) < ω v (J₀ v)} := by
  let g := (ω.associatedBilinForm J₀).toContinuousBilinearMap
  have hB : Continuous fun C : V →L[ℝ] V =>
      g - (ContinuousLinearMap.compL ℝ V V ℝ).flip C ∘L (g ∘L C) :=
    continuous_const.sub (((ContinuousLinearMap.compL ℝ V V ℝ).flip.continuous).clm_comp
      (continuous_const.clm_comp continuous_id))
  convert isOpen_setOf_forall_bilinear_apply_self_pos.preimage hB using 1
  ext C
  simp [g, associatedBilinForm_apply]

variable [FiniteDimensional ℝ V]

variable (ω) in
/-- In finite dimension, reading the compatible tangent space in the continuous endomorphisms does
not change its dimension. -/
theorem finrank_compatibleTangentSpaceCLM (J : AlmostComplexStructure V) :
    Module.finrank ℝ (ω.compatibleTangentSpaceCLM J) =
      Module.finrank ℝ (ω.compatibleTangentSpace J) := by
  have h : ContinuousLinearMap.coeLM (R := ℝ) ℝ (M := V) (N₃ := V) =
      (LinearMap.toContinuousLinearMap : (V →ₗ[ℝ] V) ≃ₗ[ℝ] V →L[ℝ] V).symm.toLinearMap := rfl
  rw [compatibleTangentSpaceCLM, h, Submodule.comap_equiv_eq_map_symm, LinearEquiv.symm_symm,
    LinearEquiv.finrank_map_eq]

local notation "𝒥" => {J : AlmostComplexStructure V // ω.Compatible J}

/-- The **Cayley coordinates** at an `ω`-compatible `J₀`: the Cayley transform
`J ↦ J₀.cayley J = -(1 + J₀ J)(1 - J₀ J)⁻¹` of the `ω`-compatible complex structures, read as a
continuous endomorphism in the compatible tangent space at `J₀`. -/
noncomputable def Compatible.cayleyCoord (h₀ : ω.Compatible J₀) (J : 𝒥) :
    ω.compatibleTangentSpaceCLM J₀ :=
  ⟨LinearMap.toContinuousLinearMap (J₀.cayley J.val), by
    rw [mem_compatibleTangentSpaceCLM, LinearMap.coe_toContinuousLinearMap]
    exact (mem_compatibleCayleyBall_iff_mem_compatibleTangentSpace.1
      ((h₀.cayley_mem_compatibleCayleyBall_iff J.property.tames).2 J.property)).1⟩

/-- The Cayley coordinate of `J` is its Cayley transform. -/
@[simp]
theorem Compatible.coe_cayleyCoord (h₀ : ω.Compatible J₀) (J : 𝒥) :
    (h₀.cayleyCoord J : V →L[ℝ] V) = LinearMap.toContinuousLinearMap (J₀.cayley J.val) :=
  (rfl)

/-- The Cayley coordinate of `J`, as an endomorphism, lies in the compatible Cayley ball. -/
theorem Compatible.cayleyCoord_mem_compatibleCayleyBall (h₀ : ω.Compatible J₀) (J : 𝒥) :
    (h₀.cayleyCoord J : V →L[ℝ] V).toLinearMap ∈ ω.compatibleCayleyBall J₀ := by
  rw [coe_cayleyCoord, LinearMap.coe_toContinuousLinearMap]
  exact (h₀.cayley_mem_compatibleCayleyBall_iff J.property.tames).2 J.property

/-- The Cayley coordinates send `J₀` to `0`. -/
@[simp]
theorem Compatible.cayleyCoord_self (h₀ : ω.Compatible J₀) : h₀.cayleyCoord ⟨J₀, h₀⟩ = 0 := by
  ext1
  simp

/-- The Cayley coordinates are injective. -/
theorem Compatible.cayleyCoord_injective (h₀ : ω.Compatible J₀) :
    Function.Injective h₀.cayleyCoord := fun J J' h => Subtype.ext <|
  h₀.eq_of_cayley_eq J.property.tames J'.property.tames <|
    LinearMap.toContinuousLinearMap.injective <| by
    simpa using congrArg Subtype.val h

/-- **Inverse formula.** A compatible structure with Cayley coordinate `C` is
`J₀ (1 + C) (1 - C)⁻¹`, in the continuous endomorphisms. -/
theorem Compatible.toContinuousLinearMap_eq_of_cayleyCoord_eq (h₀ : ω.Compatible J₀) {J : 𝒥}
    {C : V →L[ℝ] V} (h : (h₀.cayleyCoord J : V →L[ℝ] V) = C) :
    LinearMap.toContinuousLinearMap J.val.toLinearMap =
      LinearMap.toContinuousLinearMap J₀.toLinearMap * (1 + C) * Ring.inverse (1 - C) := by
  have hball : C.toLinearMap ∈ ω.compatibleCayleyBall J₀ :=
    h ▸ h₀.cayleyCoord_mem_compatibleCayleyBall J
  have hJ : J = h₀.compatibleCayleyEquiv.symm ⟨C.toLinearMap, hball⟩ := by
    refine h₀.compatibleCayleyEquiv.eq_symm_apply.2 (Subtype.ext ?_)
    have h' := congrArg ContinuousLinearMap.toLinearMap h
    rwa [coe_cayleyCoord, LinearMap.coe_toContinuousLinearMap, ← compatibleCayleyEquiv_apply_coe]
      at h'
  rw [hJ, h₀.compatibleCayleyEquiv_symm_apply_toContinuousLinearMap C hball]

/-- The range of the Cayley coordinates is the set of elements of the compatible tangent space
at `J₀` that strictly contract `v ↦ ω(v, J₀ v)`. -/
theorem Compatible.range_cayleyCoord (h₀ : ω.Compatible J₀) :
    Set.range h₀.cayleyCoord = (↑) ⁻¹'
      {C : V →L[ℝ] V | ∀ v, v ≠ 0 → ω (C v) (J₀ (C v)) < ω v (J₀ v)} := by
  ext C
  constructor
  · rintro ⟨J, rfl⟩
    exact (mem_compatibleCayleyBall_iff_mem_compatibleTangentSpace.1
      (h₀.cayleyCoord_mem_compatibleCayleyBall J)).2
  · intro hC
    have hball : (C : V →L[ℝ] V).toLinearMap ∈ ω.compatibleCayleyBall J₀ :=
      mem_compatibleCayleyBall_iff_mem_compatibleTangentSpace.2 ⟨C.property, hC⟩
    refine ⟨h₀.compatibleCayleyEquiv.symm ⟨_, hball⟩, Subtype.ext <|
      ContinuousLinearMap.coe_injective ?_⟩
    have := congrArg Subtype.val (h₀.compatibleCayleyEquiv.apply_symm_apply ⟨_, hball⟩)
    rw [compatibleCayleyEquiv_apply_coe] at this
    rw [coe_cayleyCoord, LinearMap.coe_toContinuousLinearMap, this]

/-- The range of the Cayley coordinates is open. -/
theorem Compatible.isOpen_range_cayleyCoord (h₀ : ω.Compatible J₀) :
    IsOpen (Set.range h₀.cayleyCoord) := by
  rw [h₀.range_cayleyCoord]
  exact (isOpen_setOf_strictContraction ω J₀).preimage continuous_subtypeVal

/-- The Cayley coordinates are continuous. -/
theorem Compatible.continuous_cayleyCoord (h₀ : ω.Compatible J₀) :
    Continuous h₀.cayleyCoord := by
  set A := LinearMap.toContinuousLinearMap J₀.toLinearMap
  set B : 𝒥 → V →L[ℝ] V := fun J => LinearMap.toContinuousLinearMap J.val.toLinearMap
  have hB : Continuous B :=
    AlmostComplexStructure.continuous_iff.1 continuous_subtypeVal
  have hf : ∀ J, (h₀.cayleyCoord J : V →L[ℝ] V) = cayleyFormula A (B J) := fun J => by
    rw [coe_cayleyCoord, AlmostComplexStructure.toContinuousLinearMap_cayley J₀ J.val
      (LinearMap.coe_toContinuousLinearMap _) (LinearMap.coe_toContinuousLinearMap _)]
  rw [Topology.IsInducing.subtypeVal.continuous_iff]
  refine Continuous.congr (f := fun J => cayleyFormula A (B J))
    (continuous_iff_continuousAt.2 fun J => ?_) fun J => (hf J).symm
  have hu : IsUnit (1 - A * B J) :=
    h₀.tames.isUnit_one_sub_mul_of_toLinearMap J.property.tames
      (LinearMap.coe_toContinuousLinearMap _) (LinearMap.coe_toContinuousLinearMap _)
  exact (contMDiffAt_cayleyFormula_of_isUnit (I := 𝓘(ℝ, V →L[ℝ] V)) (n := 0)
    contMDiffAt_const contMDiffAt_id hu).continuousAt.comp (f := B) hB.continuousAt

/-- The Cayley coordinates at an `ω`-compatible `J₀` are an open embedding of the
`ω`-compatible complex structures into the compatible tangent space at `J₀`. -/
theorem Compatible.isOpenEmbedding_cayleyCoord (h₀ : ω.Compatible J₀) :
    Topology.IsOpenEmbedding h₀.cayleyCoord := by
  set A := LinearMap.toContinuousLinearMap J₀.toLinearMap
  set F : (V →L[ℝ] V) → V →L[ℝ] V := fun C => A * (1 + C) * Ring.inverse (1 - C)
  -- `F` inverts the coordinates and is continuous on their range, so they are inducing.
  have hF : Continuous fun C : Set.range h₀.cayleyCoord => F C.val.val := by
    refine continuous_iff_continuousAt.2 fun ⟨C, J, hJ⟩ => ?_
    have hu : IsUnit (1 - C.val) := isUnit_one_sub_of_toLinearMap_mem_cayleyBall
      (compatibleCayleyBall_subset_cayleyBall (hJ ▸ h₀.cayleyCoord_mem_compatibleCayleyBall J))
    exact (contMDiffAt_mul_one_add_ringInverse (I := 𝓘(ℝ, V →L[ℝ] V)) (n := 0)
      (contMDiffAt_const (c := A)) contMDiffAt_id hu).continuousAt.comp
        (f := fun C : Set.range h₀.cayleyCoord => C.val.val) (x := ⟨C, J, hJ⟩)
        (continuous_subtypeVal.comp continuous_subtypeVal).continuousAt
  have hcomp : (fun C : Set.range h₀.cayleyCoord => F C.val.val) ∘
      Set.rangeFactorization h₀.cayleyCoord =
        (fun J => LinearMap.toContinuousLinearMap J.toLinearMap) ∘ (Subtype.val : 𝒥 → _) :=
    funext fun J => (h₀.toContinuousLinearMap_eq_of_cayleyCoord_eq rfl).symm
  have hind : Topology.IsInducing (Set.rangeFactorization h₀.cayleyCoord) :=
    Topology.IsInducing.of_comp (h₀.continuous_cayleyCoord.subtype_mk _) hF <| hcomp ▸
      (AlmostComplexStructure.isEmbedding_toContinuousLinearMap.comp
        Topology.IsEmbedding.subtypeVal).isInducing
  exact ⟨⟨Topology.IsInducing.subtypeVal.comp hind, h₀.cayleyCoord_injective⟩,
    h₀.isOpen_range_cayleyCoord⟩

variable (ω) in
/-- The base point of the global Cayley chart: an `ω`-compatible complex structure, chosen from
`TauCeti.SymplecticForm.exists_compatible`. -/
noncomputable def compatibleBase : 𝒥 :=
  ⟨ω.exists_compatible.choose, ω.exists_compatible.choose_spec⟩

/-- The base point is the structure chosen from `exists_compatible`. -/
theorem compatibleBase_def :
    ω.compatibleBase = ⟨ω.exists_compatible.choose, ω.exists_compatible.choose_spec⟩ :=
  (rfl)

variable (ω) in
/-- The model space of the global Cayley chart: the compatible tangent space at the base point
`ω.compatibleBase`, read in the continuous endomorphisms. -/
noncomputable def compatibleModel : Submodule ℝ (V →L[ℝ] V) :=
  ω.compatibleTangentSpaceCLM ω.compatibleBase.val

/-- The model space is the compatible tangent space at the base point. -/
theorem compatibleModel_def :
    ω.compatibleModel = ω.compatibleTangentSpaceCLM ω.compatibleBase.val :=
  (rfl)

variable (ω) in
/-- The norm of the model, Mathlib's `Submodule.normedAddCommGroup` stated for the model by name.
With it, instance search finds the structures of the fibres of the tangent bundle of a manifold
modelled on `ω.compatibleModel` uniformly in the point, such as
`∀ J, TopologicalSpace (TangentSpace 𝓘(ℝ, ω.compatibleModel) J)`, which it does not find through
the general instance. -/
noncomputable instance instNormedAddCommGroupCompatibleModel :
    NormedAddCommGroup ω.compatibleModel :=
  Submodule.normedAddCommGroup _

end TauCeti.SymplecticForm

end
