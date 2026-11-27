/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.VectorBundle.Determinant
import TauCeti.Topology.VectorBundle.Contractible

/-!
# The determinant section of a frame

Let `E → B` be a vector bundle over a nontrivially normed field `𝕜`, with finite-dimensional
model fibre `G`. Fix the basis `b = Module.finBasis 𝕜 G` of the model fibre, the one by which Tau
Ceti's determinant line `TauCeti.DetBundle 𝕜 G E` reads its charts. A **frame** of the fibre over
`x` is a linear equivalence `φ : G ≃ₗ[𝕜] E x`, and its **determinant**,
`TauCeti.DetBundle.ofFrame φ`, is the top wedge `φ b₀ ∧ ⋯ ∧ φ bᵣ₋₁`, an element of the fibre of
the determinant line over `x`:

* it is not zero (`TauCeti.DetBundle.ofFrame_ne_zero`);
* changing the frame from `φ` to `ψ` multiplies it by the determinant of the automorphism
  `φ⁻¹ ∘ ψ` of `G` (`TauCeti.DetBundle.ofFrame_eq_det_smul`);
* in the chart induced by a linear trivialization `e` of `E`, it reads as the determinant of the
  frame read in `e` (`TauCeti.DetBundle.chartCoord_ofFrame`).

A frame `Φ y : G ≃L[𝕜] E (f y)` of `E` along a map `f : X → B` thus gives a nowhere vanishing
section `y ↦ ofFrame (Φ y)` of the determinant line along `f`. Over a complete field, when the
frame is continuous as a map `X × G → TotalSpace G E`, the map `y ↦ (f y, ofFrame (Φ y))` into the
total space of the determinant line is continuous
(`TauCeti.DetBundle.continuous_totalSpaceMk_ofFrame`), by Tau Ceti's
`TauCeti.DetBundle.continuous_totalSpaceMk_ιMulti`: the determinant of the frame is the wedge of
the values of the frame on the basis vectors, each continuous along `f`.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §3 and §14 (frames and the determinant line of a vector bundle).
-/

public section

open Bundle Module

namespace TauCeti.DetBundle

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {B : Type*}
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [FiniteDimensional 𝕜 G]
  {E : B → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)] {x : B}

/-- The **determinant of a frame**: for a frame `φ : G ≃ₗ[𝕜] E x` of the fibre of `E` over `x`,
the element of the determinant line of `E` over `x` that is the top wedge of the images under `φ`
of the basis `Module.finBasis 𝕜 G` of the model fibre. -/
noncomputable def ofFrame (φ : G ≃ₗ[𝕜] E x) : DetBundle 𝕜 G E x :=
  (linearEquiv 𝕜 G E x).symm (exteriorPower.ιMulti 𝕜 _ fun i ↦ φ (Module.finBasis 𝕜 G i))

theorem ofFrame_def (φ : G ≃ₗ[𝕜] E x) :
    ofFrame φ =
      (linearEquiv 𝕜 G E x).symm (exteriorPower.ιMulti 𝕜 _ fun i ↦ φ (Module.finBasis 𝕜 G i)) :=
  (rfl)

/-- The determinant of a frame is not zero. -/
theorem ofFrame_ne_zero (φ : G ≃ₗ[𝕜] E x) : ofFrame φ ≠ 0 := by
  -- The images under `φ` of a basis are linearly independent, so their wedge is not zero.
  rw [ofFrame_def, Ne, LinearEquiv.map_eq_zero_iff, ← Ne, exteriorPower.ιMulti_ne_zero_iff]
  simpa [Function.comp_def] using (Module.finBasis 𝕜 G).linearIndependent.map' _ φ.ker

/-- **Change of frame.** For two frames `φ` and `ψ` of the fibre of `E` over `x`, the determinant
of `ψ` is that of `φ` times the determinant of the automorphism `φ⁻¹ ∘ ψ` of `G`. -/
theorem ofFrame_eq_det_smul (φ ψ : G ≃ₗ[𝕜] E x) :
    ofFrame ψ = LinearMap.det (ψ.trans φ.symm : G →ₗ[𝕜] G) • ofFrame φ := by
  have hψ : (fun i ↦ ψ (Module.finBasis 𝕜 G i)) =
      (φ : G →ₗ[𝕜] E x) ∘ ((ψ.trans φ.symm : G →ₗ[𝕜] G) ∘ Module.finBasis 𝕜 G) := by
    ext i
    simp
  rw [ofFrame_def, ofFrame_def, hψ, ← exteriorPower.map_apply_ιMulti,
    ← exteriorPower.map_apply_ιMulti, LinearMap.map_exteriorPower_finrank_eq_det_smul,
    LinearMap.smul_apply, LinearMap.id_apply, map_smul, map_smul, exteriorPower.map_apply_ιMulti]
  simp [Function.comp_def]

section Chart

variable [TopologicalSpace B] [TopologicalSpace (TotalSpace G E)]

/-- **The determinant of a frame in a chart.** Read in the chart coordinate induced by a linear
trivialization `e` of `E`, the determinant of a frame `φ` of the fibre over `x` is the
determinant of the frame read in `e`, the endomorphism `e ∘ φ` of `G`. -/
theorem chartCoord_ofFrame (e : Trivialization G (π G E)) [e.IsLinear 𝕜] (hx : x ∈ e.baseSet)
    (φ : G ≃ₗ[𝕜] E x) :
    chartCoord e hx (ofFrame φ) = LinearMap.det (e.linearMapAt 𝕜 x ∘ₗ (φ : G →ₗ[𝕜] E x)) := by
  rw [ofFrame_def, chartCoord_ιMulti]
  have h : (fun i ↦ (e ⟨x, φ (Module.finBasis 𝕜 G i)⟩).2) =
      (e.linearMapAt 𝕜 x ∘ₗ (φ : G →ₗ[𝕜] E x)) ∘ Module.finBasis 𝕜 G := by
    ext i
    simp [Trivialization.coe_linearMapAt_of_mem e hx]
  rw [h, Module.Basis.det_comp, Module.Basis.det_self, mul_one]

variable [CompleteSpace 𝕜] [∀ x, TopologicalSpace (E x)] [FiberBundle G E] [VectorBundle 𝕜 G E]
  {X : Type*} [TopologicalSpace X] {f : X → B}

/-- **Continuity of the determinant of a frame.** For a frame `Φ` of `E` along `f`, continuous as
a map `X × G → TotalSpace G E`, the map `y ↦ (f y, ofFrame (Φ y))` into the total space of the
determinant line of `E` is continuous. -/
theorem continuous_totalSpaceMk_ofFrame {Φ : ∀ y, G ≃L[𝕜] E (f y)}
    (hΦ : Continuous fun q : X × G ↦ TotalSpace.mk' G (f q.1) (Φ q.1 q.2)) :
    Continuous fun y ↦
      TotalSpace.mk' 𝕜 (E := DetBundle 𝕜 G E) (f y) (ofFrame (Φ y : G ≃ₗ[𝕜] E (f y))) := by
  -- The determinant of the frame is the wedge of its values on the basis of `G`.
  simp only [ofFrame_def]
  exact continuous_totalSpaceMk_ιMulti (continuous_of_continuous_frame hΦ) fun i ↦
    hΦ.comp (continuous_id.prodMk continuous_const)

end Chart

end TauCeti.DetBundle

end
