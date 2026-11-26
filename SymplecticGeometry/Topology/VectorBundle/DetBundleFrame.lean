/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.VectorBundle.Contractible
public import TauCeti.Topology.VectorBundle.Determinant

/-!
# The determinant section of a frame

Let `E → B` be a vector bundle over a nontrivially normed field `𝕜`, with finite-dimensional
model fibre `G`, and let `Φ y : G ≃L[𝕜] E (f y)` be a frame of `E` along a map `f : X → B`. Fix
the basis `b = Module.finBasis 𝕜 G` of the model fibre, the one by which Tau Ceti's determinant
line `TauCeti.DetBundle 𝕜 G E` reads its charts. The **determinant section** of `Φ`,
`TauCeti.DetBundle.frameSection Φ y`, is the top wedge `Φ y b₀ ∧ ⋯ ∧ Φ y bᵣ₋₁`, an element of the
fibre of the determinant line over `f y`. It is a section of the determinant line along `f`:

* it vanishes nowhere (`TauCeti.DetBundle.frameSection_ne_zero`);
* changing the frame from `Φ` to `Ψ` multiplies it by the determinant of the automorphism
  `(Φ y)⁻¹ ∘ Ψ y` of `G` (`TauCeti.DetBundle.frameSection_eq_det_smul`);
* it is natural under reparametrization of the frame (`TauCeti.DetBundle.frameSection_comp`);
* over a complete field, when the frame is continuous as a map `X × G → TotalSpace G E`, the map
  `y ↦ (f y, frameSection Φ y)` into the total space of the determinant line is continuous
  (`TauCeti.DetBundle.continuous_totalSpaceMk_frameSection`). In the chart induced by a
  trivialization `e` of `E`, the section reads as the determinant of the frame read in `e`
  (`TauCeti.DetBundle.chartCoord_frameSection`), which is continuous by Tau Ceti's
  `TauCeti.continuousOn_continuousLinearMapAt_comp`.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §3 and §14 (frames and the determinant line of a vector bundle).
-/

public section

open Bundle Module Topology

namespace TauCeti.DetBundle

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {B X : Type*}
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [FiniteDimensional 𝕜 G]
  {E : B → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)] [∀ x, TopologicalSpace (E x)]
  {f : X → B}

/-- The **determinant section of a frame**: for a frame `Φ y : G ≃L[𝕜] E (f y)` of `E` along
`f`, the element of the determinant line of `E` over `f y` that is the top wedge of the images
under `Φ y` of the basis `Module.finBasis 𝕜 G` of the model fibre. -/
noncomputable def frameSection (Φ : ∀ y, G ≃L[𝕜] E (f y)) (y : X) : DetBundle 𝕜 G E (f y) :=
  (linearEquiv 𝕜 G E (f y)).symm
    (exteriorPower.ιMulti 𝕜 _ fun i ↦ Φ y (Module.finBasis 𝕜 G i))

theorem frameSection_def (Φ : ∀ y, G ≃L[𝕜] E (f y)) (y : X) :
    frameSection Φ y = (linearEquiv 𝕜 G E (f y)).symm
      (exteriorPower.ιMulti 𝕜 _ fun i ↦ Φ y (Module.finBasis 𝕜 G i)) :=
  (rfl)

/-- **Naturality of the determinant section of a frame.** Reparametrizing a frame `Φ` along `f`
by a map `g : Y → X` reparametrizes its determinant section by `g`. -/
theorem frameSection_comp {Y : Type*} (Φ : ∀ y, G ≃L[𝕜] E (f y)) (g : Y → X) (y : Y) :
    frameSection (f := f ∘ g) (fun y ↦ Φ (g y)) y = frameSection Φ (g y) :=
  (rfl)

/-- The determinant section of a frame vanishes nowhere. -/
theorem frameSection_ne_zero (Φ : ∀ y, G ≃L[𝕜] E (f y)) (y : X) : frameSection Φ y ≠ 0 := by
  -- The images under `Φ y` of a basis are linearly independent, so their wedge is not zero.
  rw [frameSection_def, Ne, LinearEquiv.map_eq_zero_iff, ← Ne, exteriorPower.ιMulti_ne_zero_iff]
  simpa [Function.comp_def] using
    (Module.finBasis 𝕜 G).linearIndependent.map' _ (Φ y).toLinearEquiv.ker

/-- **Change of frame.** For two frames `Φ` and `Ψ` of `E` along `f`, the determinant section of
`Ψ` is that of `Φ` times the determinant of the automorphism `(Φ y)⁻¹ ∘ Ψ y` of `G`. -/
theorem frameSection_eq_det_smul (Φ Ψ : ∀ y, G ≃L[𝕜] E (f y)) (y : X) :
    frameSection Ψ y = LinearMap.det ((Ψ y).trans (Φ y).symm : G →ₗ[𝕜] G) • frameSection Φ y := by
  set A : G →ₗ[𝕜] G := ((Ψ y).trans (Φ y).symm : G →ₗ[𝕜] G)
  have hΨ : (fun i ↦ Ψ y (Module.finBasis 𝕜 G i)) =
      (Φ y : G →ₗ[𝕜] E (f y)) ∘ (A ∘ Module.finBasis 𝕜 G) := by
    ext i
    simp [A]
  rw [frameSection_def, frameSection_def, hΨ, ← exteriorPower.map_apply_ιMulti,
    (Module.finBasis 𝕜 G).exteriorPower_ιMulti_eq_det_smul, Module.Basis.det_comp,
    Module.Basis.det_self, mul_one, map_smul, map_smul, exteriorPower.map_apply_ιMulti]
  simp [Function.comp_def]

section Chart

variable [TopologicalSpace B] [TopologicalSpace (TotalSpace G E)] [FiberBundle G E]

/-- **The determinant section in a chart.** Read in the chart coordinate induced by a linear
trivialization `e` of `E`, the determinant section of a frame `Φ` at `y` is the determinant of
the frame read in `e`, the endomorphism `e ∘ Φ y` of `G`. -/
theorem chartCoord_frameSection (e : Trivialization G (π G E)) [e.IsLinear 𝕜]
    (Φ : ∀ y, G ≃L[𝕜] E (f y)) {y : X} (hy : f y ∈ e.baseSet) :
    chartCoord e hy (frameSection Φ y) =
      LinearMap.det ((e.continuousLinearMapAt 𝕜 (f y)).comp (Φ y : G →L[𝕜] E (f y)) :
        G →ₗ[𝕜] G) := by
  rw [frameSection_def, chartCoord_ιMulti]
  have h : (fun i ↦ (e ⟨f y, Φ y (Module.finBasis 𝕜 G i)⟩).2) =
      ((e.continuousLinearMapAt 𝕜 (f y)).comp (Φ y : G →L[𝕜] E (f y)) : G →ₗ[𝕜] G) ∘
        Module.finBasis 𝕜 G := by
    ext i
    simp [Trivialization.coe_linearMapAt_of_mem e hy]
  rw [h, Module.Basis.det_comp, Module.Basis.det_self, mul_one]

variable [CompleteSpace 𝕜] [TopologicalSpace X] [VectorBundle 𝕜 G E]

/-- **Continuity of the determinant section of a frame.** For a frame `Φ` of `E` along `f`,
continuous as a map `X × G → TotalSpace G E`, the map `y ↦ (f y, frameSection Φ y)` into the
total space of the determinant line of `E` is continuous. -/
theorem continuous_totalSpaceMk_frameSection {Φ : ∀ y, G ≃L[𝕜] E (f y)}
    (hΦ : Continuous fun q : X × G ↦ TotalSpace.mk' G (f q.1) (Φ q.1 q.2)) :
    Continuous fun y ↦ TotalSpace.mk' 𝕜 (E := DetBundle 𝕜 G E) (f y) (frameSection Φ y) := by
  have hf : Continuous f :=
    (FiberBundle.continuous_proj G E).comp (hΦ.comp (Continuous.prodMk_left 0))
  refine continuous_iff_continuousAt.2 fun y₀ ↦ (FiberBundle.continuousAt_totalSpace 𝕜 _).2
    ⟨hf.continuousAt, ?_⟩
  set e := trivializationAt G E (f y₀)
  have hU : f ⁻¹' e.baseSet ∈ 𝓝 y₀ :=
    hf.continuousAt.preimage_mem_nhds
      (e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' (f y₀)))
  have hdet : ContinuousAt (fun y ↦ ((e.continuousLinearMapAt 𝕜 (f y)).comp
      (Φ y : G →L[𝕜] E (f y))).det) y₀ :=
    ContinuousLinearMap.continuous_det.continuousAt.comp
      ((continuousOn_continuousLinearMapAt_comp hΦ e).continuousAt hU)
  refine hdet.congr (Filter.eventuallyEq_of_mem hU fun y (hy : f y ∈ e.baseSet) ↦ ?_)
  rw [trivializationAt_eq, trivialization_apply_mk _ hy, chartCoord_frameSection _ Φ hy]

end Chart

end TauCeti.DetBundle

end
