/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Topology.VectorBundle.DetBundle.Frame

/-!
# The determinant transport between different models, on frames and in charts

Tau Ceti's `TauCeti.DetBundle.congrModelEquiv e x` transports the fibre over `x` of the
determinant line `TauCeti.DetBundle 𝕜 F E` to that of `TauCeti.DetBundle 𝕜 F' E'`, for a family
of continuous linear equivalences `e x : E x ≃L[𝕜] E' x` between vector bundles whose models `F`
and `F'` may differ. Tau Ceti has the isomorphisms of total spaces for one model
(`TauCeti.DetBundle.congrHomeomorph`) and for two (`TauCeti.DetBundle.congrModelHomeomorph`).
This file computes the transport on frames and in charts, and compares the two homeomorphisms:

* `TauCeti.DetBundle.congrModelEquiv_ofFrame`: the transport sends the determinant of a frame
  `φ : F ≃ E x` to the determinant of the frame `e x ∘ φ ∘ L` of `E' x`, where `L : F' ≃ F`
  sends the basis `Module.finBasis 𝕜 F'` to `Module.finBasis 𝕜 F`;
* `TauCeti.DetBundle.chartCoord_congrModelEquiv`: in charts induced by linear trivializations
  `t` of `E` and `t'` of `E'`, the transport is multiplication by the determinant of the
  endomorphism `t' ∘ e ∘ t⁻¹ ∘ L` of `F'`;
* `TauCeti.DetBundle.congrModelHomeomorph_eq_congrHomeomorph`: for one model, Tau Ceti's
  `TauCeti.DetBundle.congrModelHomeomorph` is `TauCeti.DetBundle.congrHomeomorph`.

The chart coordinate of the transport is computed through the determinant sections of frames of
`SymplecticGeometry/Topology/VectorBundle/DetBundle/Frame.lean`.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press, 1974, §3.
-/

public section

open Bundle Module

namespace TauCeti.DetBundle

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {E : B → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)]
  [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] [FiniteDimensional 𝕜 F']
  {E' : B → Type*} [∀ x, AddCommGroup (E' x)] [∀ x, Module 𝕜 (E' x)]
  [∀ x, TopologicalSpace (E' x)] [TopologicalSpace (TotalSpace F' E')]
  [FiberBundle F' E'] [VectorBundle 𝕜 F' E']

/-- **The transport of the determinant of a frame.** For `h : finrank 𝕜 F' = finrank 𝕜 F`, let
`L : F' ≃ F` send `Module.finBasis 𝕜 F'` to `Module.finBasis 𝕜 F` along `finCongr h`. Then the
transport `congrModelEquiv e x` sends the determinant of a frame `φ : F ≃ E x` to that of the
frame `e x ∘ φ ∘ L : F' ≃ E' x`. -/
theorem congrModelEquiv_ofFrame (e : ∀ x, E x ≃L[𝕜] E' x) (x : B)
    (h : finrank 𝕜 F' = finrank 𝕜 F) (φ : F ≃ₗ[𝕜] E x) :
    congrModelEquiv (F₁ := F) (F' := F') e x (ofFrame φ) =
      ofFrame (((finBasis 𝕜 F').equiv (finBasis 𝕜 F) (finCongr h)).trans
        (φ.trans (e x).toLinearEquiv)) := by
  rw [ofFrame_def, ofFrame_def, congrModelEquiv_ιMulti e x h.symm]
  congr 2
  ext i
  simp [Module.Basis.equiv_apply]

/-- **The transport in charts.** Read in the chart coordinates induced by linear trivializations
`t` of `E` and `t'` of `E'`, the transport `congrModelEquiv e x` is multiplication by the
determinant of the endomorphism `t' ∘ e x ∘ t⁻¹ ∘ L` of `F'`, where `L : F' ≃ F` sends
`Module.finBasis 𝕜 F'` to `Module.finBasis 𝕜 F` along `finCongr h`. -/
theorem chartCoord_congrModelEquiv (e : ∀ x, E x ≃L[𝕜] E' x) (h : finrank 𝕜 F' = finrank 𝕜 F)
    (t : Trivialization F (π F E)) [t.IsLinear 𝕜] (t' : Trivialization F' (π F' E'))
    [t'.IsLinear 𝕜] {x : B} (hx : x ∈ t.baseSet) (hx' : x ∈ t'.baseSet)
    (v : DetBundle 𝕜 F E x) :
    chartCoord t' hx' (congrModelEquiv (F₁ := F) (F' := F') e x v) =
      LinearMap.det ((t'.continuousLinearMapAt 𝕜 x).comp
          (((e x : E x →L[𝕜] E' x)).comp (t.symmL 𝕜 x)) ∘ₗ
        (((finBasis 𝕜 F').equiv (finBasis 𝕜 F) (finCongr h) : F' ≃ₗ[𝕜] F) : F' →ₗ[𝕜] F)) *
        chartCoord t hx v := by
  -- The inverse of the chart is a frame whose determinant has chart coordinate `1`.
  set φ : F ≃ₗ[𝕜] E x := (t.linearEquivAt 𝕜 x hx).symm
  have hφ : chartCoord t hx (ofFrame φ) = 1 := by
    have hid : t.linearMapAt 𝕜 x ∘ₗ (φ : F →ₗ[𝕜] E x) = LinearMap.id := by
      ext v
      simp [φ, Trivialization.coe_linearMapAt_of_mem t hx, t.apply_mk_symm hx]
    rw [chartCoord_ofFrame, hid, LinearMap.det_id]
  have hv : v = chartCoord t hx v • ofFrame φ :=
    (chartCoord t hx).injective (by rw [map_smul, hφ, smul_eq_mul, mul_one])
  rw [hv, map_smul, map_smul, congrModelEquiv_ofFrame e x h, chartCoord_ofFrame, smul_eq_mul,
    map_smul, hφ, smul_eq_mul, mul_one, mul_comm]
  congr 2
  ext w
  simp [φ, Trivialization.symmL_apply t hx, Trivialization.coe_linearMapAt_of_mem t' hx']

variable [CompleteSpace 𝕜]

section SameModel

variable {E₂ : B → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [∀ x, TopologicalSpace (E₂ x)] [TopologicalSpace (TotalSpace F E₂)]
  [FiberBundle F E₂] [VectorBundle 𝕜 F E₂]

/-- For bundles with the same model, Tau Ceti's homeomorphism `congrModelHomeomorph` is
`TauCeti.DetBundle.congrHomeomorph`. -/
@[simp]
theorem congrModelHomeomorph_eq_congrHomeomorph (e : ∀ x, E x ≃L[𝕜] E₂ x)
    (he : Continuous (fun p : TotalSpace F E ↦ TotalSpace.mk' F p.proj (e p.proj p.snd))) :
    congrModelHomeomorph e he = congrHomeomorph e he := by
  refine Homeomorph.ext fun p ↦ ?_
  rw [congrModelHomeomorph_apply, congrHomeomorph_apply, congrModelEquiv_eq_congrEquiv]

end SameModel

end TauCeti.DetBundle

end
