/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Topology.Compactness.Paracompact
public import Mathlib.Topology.Homotopy.Contractible
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure

import SymplecticGeometry.Topology.VectorBundle.Complement
import SymplecticGeometry.Topology.VectorBundle.Frame
import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.ComplexTangentBundle
import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.ContMDiff
import TauCeti.Topology.Algebra.Module.ComplexSmulI

/-!
# Complex frames along a disc

Let `M` be a complex manifold modelled on a finite-dimensional complex space `E`, and let
`f : Y → M` be a continuous map from a contractible paracompact R₁ space, such as a disc. This file
completes a continuous family of injective complex-linear maps `L y : G₁ → T_(f y) M` to a
continuous family of complex-linear isomorphisms `G₁ × G₂ → T_(f y) M`, for `G₂` of the
complementary dimension (`SymplecticGeometry.exists_continuous_isInvertible_coprod_tangentSpace`).

The tangent spaces of the underlying real manifold are those of the complex manifold, and
multiplication by `i` on them is the almost complex structure
`TauCeti.SmoothAlmostComplexStructure.ofComplexManifold`. Tau Ceti's
`TauCeti.ContMDiffAlmostComplexStructure.exists_continuous_frame` gives a continuous
complex-linear frame `φ y : E ≃ T_(f y) M` along `f`. The maps `(φ y)⁻¹ ∘ L y : G₁ → E` are then
a continuous family of injective complex-linear maps into the fixed space `E`
(`SymplecticGeometry.Bundle.continuous_frame_symm_comp`), and a continuous complement of their
ranges (`Continuous.exists_continuous_isInvertible_coprod`), carried back by `φ y`, gives the
second factor.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012]
-/

public section

open Bundle Function Module TauCeti.SmoothAlmostComplexStructure
open scoped Manifold ContDiff

namespace SymplecticGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
  {Y : Type*} [TopologicalSpace Y] [R1Space Y] [ParacompactSpace Y] [ContractibleSpace Y]
  {G₁ G₂ : Type*} [NormedAddCommGroup G₁] [NormedSpace ℂ G₁] [FiniteDimensional ℂ G₁]
  [NormedAddCommGroup G₂] [NormedSpace ℂ G₂] [FiniteDimensional ℂ G₂]

/-- The underlying real manifold of the complex manifold `M`. -/
private local instance : IsManifold 𝓘(ℝ, E) ∞ M :=
  IsManifold.restrictScalars ℝ (inferInstance : IsManifold 𝓘(ℂ, E) ∞ M)

/-- **A continuous complex complement along a map from a contractible space.** Let `M` be a
complex manifold modelled on a finite-dimensional space `E`, `Y` a contractible paracompact R₁
space and `L y : G₁ → T_(f y) M` injective complex-linear maps, continuous as a map
`Y × G₁ → TM`. If `dim G₁ + dim G₂ = dim E`, there are complex-linear maps
`K y : G₂ → T_(f y) M`, continuous as a map `Y × G₂ → TM`, such that each
`(L y, K y) : G₁ × G₂ → T_(f y) M` is an isomorphism.

Complex linearity is stated with `ofComplexManifold E M`, which is multiplication by `i` on each
tangent space (`ofComplexManifold_apply`). The real manifold structure `IsManifold 𝓘(ℝ, E) 1 M`,
which the complex one implies, gives `TM` its topology. -/
theorem exists_continuous_isInvertible_coprod_tangentSpace [IsManifold 𝓘(ℝ, E) 1 M]
    (hdim : finrank ℂ E = finrank ℂ G₁ + finrank ℂ G₂) {f : Y → M}
    {L : ∀ y, G₁ →L[ℝ] TangentSpace 𝓘(ℝ, E) (f y)}
    (hL : Continuous fun q : Y × G₁ ↦ (⟨f q.1, L q.1 q.2⟩ : TangentBundle 𝓘(ℝ, E) M))
    (hLI : ∀ y v, L y (Complex.I • v) = ofComplexManifold E M (f y) (L y v))
    (hinj : ∀ y, Injective (L y)) :
    ∃ K : ∀ y, G₂ →L[ℝ] TangentSpace 𝓘(ℝ, E) (f y),
      Continuous (fun q : Y × G₂ ↦ (⟨f q.1, K q.1 q.2⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
      (∀ y v, K y (Complex.I • v) = ofComplexManifold E M (f y) (K y v)) ∧
      ∀ y, ((L y).coprod (K y)).IsInvertible := by
  have hf : Continuous f := (FiberBundle.continuous_proj E _).comp (hL.comp
    (Continuous.prodMk_left 0))
  have : Fact (finrank ℝ E = 2 * finrank ℂ E) := ⟨finrank_real_of_complex E⟩
  -- A continuous frame of `TM` along `f` carrying multiplication by `i` to itself.
  obtain ⟨φ, hφ, hφI⟩ := ((TauCeti.SmoothAlmostComplexStructure.ofComplexManifold E M).toContMDiff
    ⊤).exists_continuous_frame (G := E) hf
  simp only [toContMDiff_toEndomorphism_apply] at hφI
  -- In the frame, `L` becomes a continuous family of injective complex-linear maps `G₁ → E`.
  have hjI (y : Y) (v : G₁) : (φ y).symm (L y (Complex.I • v)) =
      Complex.I • (φ y).symm (L y v) := by
    rw [hLI]
    beta_reduce
    rw [ContinuousLinearEquiv.symm_apply_eq, hφI, ContinuousLinearEquiv.apply_symm_apply]
  let j : Y → G₁ →L[ℂ] E := fun y ↦
    ((φ y).symm.toContinuousLinearMap.comp (L y)).complexOfMapISmul (hjI y)
  have hjv (y : Y) : ⇑(j y) = (φ y).symm ∘ L y :=
    ContinuousLinearMap.coe_complexOfMapISmul _ (hjI y)
  have hjR := Bundle.continuous_frame_symm_comp hφ hL
  have hj : Continuous j := continuous_clm_apply.2 fun v ↦
    (hjR.clm_apply (continuous_const (y := v))).congr fun y ↦ by simp [hjv]
  have hjinj (y : Y) : Injective (j y) := by
    rw [hjv]
    exact (φ y).symm.injective.comp (hinj y)
  obtain ⟨k, hk, hkj⟩ := hj.exists_continuous_isInvertible_coprod hdim.symm hjinj
  refine ⟨fun y ↦ (φ y).toContinuousLinearMap.comp ((k y).restrictScalars ℝ),
    (hφ.comp (continuous_fst.prodMk ((hk.comp continuous_fst).clm_apply continuous_snd))).congr
      fun q ↦ rfl, fun y v ↦ ?_, fun y ↦ ?_⟩
  · simp [hφI]
  · obtain ⟨e, he⟩ := hkj y
    refine ⟨(e.restrictScalars' ℝ).trans (φ y), ?_⟩
    have he' (p : G₁ × G₂) : e p = (j y).coprod (k y) p := congrArg (· p) he
    ext v <;> simp [he', hjv]

end SymplecticGeometry

end
