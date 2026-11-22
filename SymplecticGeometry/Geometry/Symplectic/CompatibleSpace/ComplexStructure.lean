/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.Integrable
public import SymplecticGeometry.Geometry.Manifold.Instances.CompatibleComplexStructures
public import TauCeti.Geometry.Symplectic.Manifold.JHolomorphic
import Mathlib.Tactic.NoncommRing
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Singleton
import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.Chart

/-!
# The complex structure of the space of compatible complex structures

Let `ω` be a symplectic form on a finite-dimensional real normed space `V`, and `𝒥 ω` the
manifold of `ω`-compatible complex structures, modelled on `ω.compatibleModel` through the
global Cayley chart at the base point `J₀ = ω.compatibleBase`. This file gives `𝒥 ω` its
almost complex structure, whose value at `J` on a tangent vector with ambient reading `Ĵ` is
`-J Ĵ` (McDuff–Salamon, Example 4.3.6), and shows that it is integrable.

The structure is defined as the constant structure `C ↦ -J₀ C` of the model, read in the global
chart. Since the chart is the only one, the changes of coordinates of the tangent bundle are the
identity (`tangentCoordChange_of_chartAt_eq`), so this constant section is smooth
(`SmoothAlmostComplexStructure.ofTangentCoordChange`).
In Cayley coordinates `J = J₀ (1 + C) (1 - C)⁻¹` the differential of the inclusion
into `V →L[ℝ] V` is `Ċ ↦ 2 J₀ (1 - C)⁻¹ Ċ (1 - C)⁻¹`, and because `C` anticommutes with `J₀`
it carries `-J₀ Ċ` to `-J` times the image of `Ċ`: this is
`mvfderiv_compatibleCLM_compatibleSpaceComplexStructure`. The global chart is then a chart in
which the structure is constant, so the structure is integrable in the sense of
`TauCeti.SmoothAlmostComplexStructure.IsIntegrable`, and its Nijenhuis tensor vanishes. The
diffeomorphisms `J ↦ Ψ J Ψ⁻¹` of linear symplectomorphisms `Ψ` are pseudoholomorphic.

## Main definitions and results

* `TauCeti.SymplecticForm.compatibleModelComplexStructure`: the linear complex structure
  `C ↦ -J₀ C` of the model.
* `TauCeti.SymplecticForm.compatibleSpaceComplexStructure`: the smooth almost complex structure
  of `𝒥 ω`, the constant structure of the model in the global chart.
* `TauCeti.SymplecticForm.mvfderiv_compatibleCLM_compatibleSpaceComplexStructure`: read in
  `V →L[ℝ] V`, the structure at `J` is `Ĵ ↦ -J Ĵ`.
* `TauCeti.SymplecticForm.chartPushforward_compatibleSpaceComplexStructure`: in the global chart
  the structure is constant.
* `TauCeti.SymplecticForm.isIntegrable_compatibleSpaceComplexStructure` and
  `TauCeti.SymplecticForm.nijenhuis_compatibleSpaceComplexStructure`: the structure is
  integrable and its Nijenhuis tensor vanishes.
* `TauCeti.SymplecticForm.isPseudoholomorphic_compatibleTransport`: the transport by a linear
  symplectomorphism is pseudoholomorphic.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third
  edition][McDuffSalamon2017], §2.5 (the Cayley transform) and Example 4.3.6.
-/

public section

open scoped Manifold


namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V}

local notation "𝒥" => {J : AlmostComplexStructure V // ω.Compatible J}

/-! ### The complex structure of the model -/

variable (ω) in
/-- The linear complex structure `C ↦ -J₀ C` of the model `ω.compatibleModel`, `J₀` being the base
point `ω.compatibleBase`. -/
noncomputable def compatibleModelComplexStructure :
    AlmostComplexStructure ω.compatibleModel where
  toLinearMap :=
    -- Composing with the base point on the left preserves the compatible tangent space there,
    -- which is the model.
    have hmem (C : ω.compatibleModel) :
        ω.compatibleCLM ω.compatibleBase * (C : V →L[ℝ] V) ∈ ω.compatibleModel := by
      obtain ⟨D, hD⟩ := C
      rw [Subtype.coe_mk, compatibleModel_def, mem_compatibleTangentSpaceCLM]
      rw [compatibleModel_def, mem_compatibleTangentSpaceCLM] at hD
      rw [compatibleCLM_def, ContinuousLinearMap.toLinearMap_mul,
        LinearMap.coe_toContinuousLinearMap]
      exact ω.compatibleBase.property.invariant.mul_mem_compatibleTangentSpace hD
    { toFun C := ⟨-(ω.compatibleCLM ω.compatibleBase * C), neg_mem (hmem C)⟩
      map_add' C D := Subtype.ext <| by simp [mul_add, add_comm]
      map_smul' c C := Subtype.ext <| by simp }
  square_neg := LinearMap.ext fun C => Subtype.ext <| by
    simp [← mul_assoc]

@[simp]
theorem coe_compatibleModelComplexStructure_apply (C : ω.compatibleModel) :
    (ω.compatibleModelComplexStructure C : V →L[ℝ] V) =
      -(ω.compatibleCLM ω.compatibleBase * C) :=
  (rfl)

/-! ### The almost complex structure of the manifold -/

variable (ω) in
/-- The almost complex structure of the manifold of `ω`-compatible complex structures: the
constant structure `compatibleModelComplexStructure` of the model, read in the global chart. Its
value at `J` on a tangent vector with ambient reading `Ĵ` has ambient reading `-J Ĵ`
(`mvfderiv_compatibleCLM_compatibleSpaceComplexStructure`). -/
noncomputable def compatibleSpaceComplexStructure :
    SmoothAlmostComplexStructure 𝓘(ℝ, ω.compatibleModel) 𝒥 :=
  -- The continuous linear map is built against the expected type, so that the topology of the
  -- model is that of its norm.
  SmoothAlmostComplexStructure.ofTangentCoordChange 𝓘(ℝ, ω.compatibleModel)
    { toLinearMap := ω.compatibleModelComplexStructure.toLinearMap
      cont := ω.compatibleModelComplexStructure.toLinearMap.continuous_of_finiteDimensional }
    ω.compatibleModelComplexStructure.apply_apply fun {x y _} hz _ => by
      simp only [tangentCoordChange_of_chartAt_eq (x := x) (y := y) rfl hz.1,
        ContinuousLinearMap.id_apply]

theorem compatibleSpaceComplexStructure_def :
    ω.compatibleSpaceComplexStructure =
      SmoothAlmostComplexStructure.ofTangentCoordChange 𝓘(ℝ, ω.compatibleModel)
        { toLinearMap := ω.compatibleModelComplexStructure.toLinearMap
          cont := ω.compatibleModelComplexStructure.toLinearMap.continuous_of_finiteDimensional }
        ω.compatibleModelComplexStructure.apply_apply fun {x y _} hz _ => by
          simp only [tangentCoordChange_of_chartAt_eq (x := x) (y := y) rfl hz.1,
            ContinuousLinearMap.id_apply] :=
  (rfl)

/-- The almost complex structure at every point is the complex structure `C ↦ -J₀ C` of the
model. -/
theorem compatibleSpaceComplexStructure_apply (J : 𝒥)
    (a : TangentSpace 𝓘(ℝ, ω.compatibleModel) J) :
    ω.compatibleSpaceComplexStructure J a = ω.compatibleModelComplexStructure a := by
  -- `ofTangentCoordChange_apply` does not find the hypotheses of the constructor by unification.
  rw [compatibleSpaceComplexStructure_def]
  exact SmoothAlmostComplexStructure.ofTangentCoordChange_apply J a

/-- **The complex structure in ambient readings.** At `J`, the almost complex structure sends a
tangent vector with ambient reading `Ĵ` to the tangent vector with ambient reading `-J Ĵ`. -/
theorem mvfderiv_compatibleCLM_compatibleSpaceComplexStructure (J : 𝒥)
    (a : TangentSpace 𝓘(ℝ, ω.compatibleModel) J) :
    mvfderiv 𝓘(ℝ, ω.compatibleModel) ω.compatibleCLM J (ω.compatibleSpaceComplexStructure J a) =
      -(ω.compatibleCLM J * mvfderiv 𝓘(ℝ, ω.compatibleModel) ω.compatibleCLM J a) := by
  rw [mvfderiv_apply_eq_mfderiv_apply, mvfderiv_apply_eq_mfderiv_apply]
  -- The tangent space at `J` is the model space; the computation reads `a` in the model.
  revert a
  intro (a : ω.compatibleModel)
  -- Name the ambient reading of `a`, an element of `V →L[ℝ] V`.
  obtain ⟨d, hd⟩ : ∃ d : V →L[ℝ] V,
      mfderiv 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V) ω.compatibleCLM J a = d := ⟨_, rfl⟩
  rw [hd]
  have hd' : d = (2 : ℝ) • (ω.compatibleCLM ω.compatibleBase *
      Ring.inverse (1 - (ω.cayleyChart J : V →L[ℝ] V)) * (a : V →L[ℝ] V) *
        Ring.inverse (1 - (ω.cayleyChart J : V →L[ℝ] V))) :=
    hd.symm.trans (mfderiv_compatibleCLM_apply J a)
  refine (congrArg (mfderiv 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V) ω.compatibleCLM J)
    (compatibleSpaceComplexStructure_apply J a)).trans ((mfderiv_compatibleCLM_apply J _).trans ?_)
  rw [hd', coe_compatibleModelComplexStructure_apply, compatibleCLM_eq_cayleyChart]
  set C : V →L[ℝ] V := ↑(ω.cayleyChart J)
  set J₀ := ω.compatibleCLM ω.compatibleBase
  -- `C` anticommutes with `J₀`, and `1 - C` is invertible, with inverse `R`.
  have hC : C * J₀ = -(J₀ * C) := by
    have h : C ∈ ω.compatibleTangentSpaceCLM ω.compatibleBase.val := by
      rw [← compatibleModel_def]
      exact (ω.cayleyChart J).property
    rw [mem_compatibleTangentSpaceCLM] at h
    ext v
    simpa [J₀, C] using (mem_compatibleTangentSpace.1 h).1 v
  obtain ⟨u, hu⟩ := isUnit_one_sub_of_mem_chartAt_target (cayleyChart_mem_chartAt_target J J)
  rw [← hu, Ring.inverse_unit]
  -- The identity `R J₀ = (1 + C) R J₀ R`, from `(1 + C) J₀ = J₀ (1 - C)`.
  have hc : (1 + C) * (↑u⁻¹ : V →L[ℝ] V) = ↑u⁻¹ * (1 + C) :=
    (Commute.units_inv_right (by rw [hu, commute_iff_eq]; noncomm_ring)).eq
  have hJ : (1 + C) * J₀ = J₀ * (u : V →L[ℝ] V) := by
    rw [hu, add_mul, mul_sub, one_mul, mul_one, hC, sub_eq_add_neg]
  have hR : (↑u⁻¹ : V →L[ℝ] V) * J₀ = (1 + C) * ↑u⁻¹ * J₀ * ↑u⁻¹ := by
    rw [hc, mul_assoc (↑u⁻¹ : V →L[ℝ] V) (1 + C) J₀, hJ, mul_assoc, mul_assoc, Units.mul_inv,
      mul_one]
  calc (2 : ℝ) • (J₀ * ↑u⁻¹ * -(J₀ * (a : V →L[ℝ] V)) * ↑u⁻¹)
      = -((2 : ℝ) • (J₀ * (↑u⁻¹ * J₀) * (a : V →L[ℝ] V) * ↑u⁻¹)) := by
        simp only [mul_neg, neg_mul, smul_neg, mul_assoc]
    _ = _ := by rw [hR, mul_smul_comm]; simp only [mul_assoc]

/-! ### Integrability -/

/-- **The structure is constant in the global chart.** On the target of the chart, the structure
pushed forward along the chart is the complex structure `C ↦ -J₀ C` of the model. -/
theorem chartPushforward_compatibleSpaceComplexStructure {J : 𝒥} {p : ω.compatibleModel}
    (hp : p ∈ (chartAt ω.compatibleModel J).target) (w : ω.compatibleModel) :
    ω.compatibleSpaceComplexStructure.chartPushforward (chartAt ω.compatibleModel J) p w =
      ω.compatibleModelComplexStructure w := by
  rw [SmoothAlmostComplexStructure.chartPushforward_apply]
  -- The differentials of the chart and of its inverse are the identity. The tangent spaces are
  -- the model, but `rw` does not rewrite under them, so the equalities of maps are applied.
  have h₁ := mfderiv_chartAt_of_chartAt_eq (I := 𝓘(ℝ, ω.compatibleModel))
    (x := (chartAt ω.compatibleModel J).symm p) (y := J) rfl
  have h₂ := mfderiv_chartAt_symm_of_chartAt_eq (I := 𝓘(ℝ, ω.compatibleModel)) hp rfl
  exact (DFunLike.congr_fun h₁ _).trans ((compatibleSpaceComplexStructure_apply _ _).trans
    (congrArg ω.compatibleModelComplexStructure (DFunLike.congr_fun h₂ w)))

/-- **The structure is integrable**: the global chart is a chart in which it is constant. -/
theorem isIntegrable_compatibleSpaceComplexStructure :
    ω.compatibleSpaceComplexStructure.IsIntegrable := by
  rw [compatibleSpaceComplexStructure_def]
  exact SmoothAlmostComplexStructure.isIntegrable_ofTangentCoordChange _ _

/-- The Nijenhuis tensor of the almost complex structure vanishes. -/
theorem nijenhuis_compatibleSpaceComplexStructure :
    ω.compatibleSpaceComplexStructure.nijenhuis = 0 :=
  isIntegrable_compatibleSpaceComplexStructure.nijenhuis_eq_zero

/-! ### The transport maps are pseudoholomorphic -/

/-- **The transport maps are pseudoholomorphic.** For a linear symplectomorphism `Ψ`, the
diffeomorphism `J ↦ Ψ J Ψ⁻¹` is pseudoholomorphic for the almost complex structure. -/
theorem isPseudoholomorphic_compatibleTransport {Ψ : V ≃L[ℝ] V}
    (hΨ : ω.IsSymplectomorphism ω Ψ.toLinearEquiv) :
    IsPseudoholomorphic ω.compatibleSpaceComplexStructure ω.compatibleSpaceComplexStructure
      (ω.compatibleTransport hΨ) := by
  rw [isPseudoholomorphic_iff]
  intro J
  refine isPseudoholomorphicAt_iff_mfderiv.2
    ⟨(ω.compatibleTransport hΨ).mdifferentiable (by simp) J, fun a => ?_⟩
  apply injective_mfderiv_compatibleCLM
  rw [mfderiv_compatibleCLM_compatibleTransport,
    ← mvfderiv_apply_eq_mfderiv_apply ω.compatibleCLM J,
    ← mvfderiv_apply_eq_mfderiv_apply ω.compatibleCLM (ω.compatibleTransport hΨ J),
    mvfderiv_compatibleCLM_compatibleSpaceComplexStructure,
    mvfderiv_compatibleCLM_compatibleSpaceComplexStructure, mvfderiv_apply_eq_mfderiv_apply,
    mvfderiv_apply_eq_mfderiv_apply, mfderiv_compatibleCLM_compatibleTransport,
    compatibleCLM_compatibleTransport]
  -- Name the ambient reading of `a`, an element of `V →L[ℝ] V`.
  obtain ⟨d, hd⟩ : ∃ d : V →L[ℝ] V,
      mfderiv 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V) ω.compatibleCLM J a = d := ⟨_, rfl⟩
  rw [hd]
  refine ContinuousLinearMap.ext fun v => ?_
  simp

end TauCeti.SymplecticForm

end
