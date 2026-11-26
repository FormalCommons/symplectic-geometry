/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Topology.VectorBundle.DetBundle.Frame
public import TauCeti.LinearAlgebra.ExteriorPower.Basic
import SymplecticGeometry.Topology.VectorBundle.ModelEquiv

/-!
# Continuity of the determinant transport between different models

Tau Ceti's `TauCeti.DetBundle.congrModelEquiv e x` transports the fibre over `x` of the
determinant line `TauCeti.DetBundle 𝕜 F E` to that of `TauCeti.DetBundle 𝕜 F' E'`, for a family
of continuous linear equivalences `e x : E x ≃L[𝕜] E' x` between vector bundles whose models `F`
and `F'` may differ. Tau Ceti states no continuity in the base for it; it has the isomorphism of
total spaces only for one model (`TauCeti.DetBundle.congrHomeomorph`). This file gives it for two:

* `TauCeti.DetBundle.congrModelEquiv_ofFrame`: the transport sends the determinant of a frame
  `φ : F ≃ E x` to the determinant of the frame `e x ∘ φ ∘ L` of `E' x`, where `L : F' ≃ F`
  sends the basis `Module.finBasis 𝕜 F'` to `Module.finBasis 𝕜 F`;
* `TauCeti.DetBundle.chartCoord_congrModelEquiv`: in charts induced by linear trivializations
  `t` of `E` and `t'` of `E'`, the transport is multiplication by the determinant of the
  endomorphism `t' ∘ e ∘ t⁻¹ ∘ L` of `F'`;
* `TauCeti.DetBundle.congrModelHomeomorph`: when `e` is continuous on total spaces, the
  homeomorphism of the total spaces of the determinant lines that is `congrModelEquiv e x` on
  each fibre, which for one model is `TauCeti.DetBundle.congrHomeomorph`
  (`TauCeti.DetBundle.congrModelHomeomorph_eq_congrHomeomorph`).

The proof of continuity follows that of Tau Ceti's `TauCeti.DetBundle.congrHomeomorph`
(through `FiberBundle.continuous_of_forall_trivialization`), with the chart coordinate of the
transport computed through the determinant sections of frames of
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
  apply (linearEquiv 𝕜 F' E' x).injective
  apply Subtype.ext
  rw [coe_congrModelEquiv, ofFrame_def, ofFrame_def, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply, exteriorPower.ιMulti_apply_coe,
    exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.map_apply_ιMulti,
    ← TauCeti.ExteriorAlgebra.ιMulti_comp_cast h]
  congr 1
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

/-- Read in the charts at `a` of the determinant lines, the transport `congrModelEquiv e` is
multiplication by a function of the base point that is continuous at `a`. -/
private theorem continuousAt_chartCoord_congrModelEquiv (e : ∀ x, E x ≃L[𝕜] E' x)
    (he : Continuous (fun p : TotalSpace F E ↦ TotalSpace.mk' F' p.proj (e p.proj p.snd)))
    (a : B) :
    ∃ s : B → 𝕜, ContinuousAt s a ∧ ∀ x (hx : x ∈ (trivializationAt F E a).baseSet)
      (hx' : x ∈ (trivializationAt F' E' a).baseSet) (v : DetBundle 𝕜 F E x),
      chartCoord (trivializationAt F' E' a) hx' (congrModelEquiv (F₁ := F) (F' := F') e x v) =
        s x * chartCoord (trivializationAt F E a) hx v := by
  set t := trivializationAt F E a
  set t' := trivializationAt F' E' a
  have h : finrank 𝕜 F' = finrank 𝕜 F :=
    (VectorBundle.modelEquiv F F' a (e a)).toLinearEquiv.finrank_eq.symm
  set L : F' →L[𝕜] F :=
    ((finBasis 𝕜 F').equiv (finBasis 𝕜 F) (finCongr h) : F' ≃ₗ[𝕜] F).toContinuousLinearMap
  -- The coordinate expression of `e` is a continuous family of linear maps `F → F'`.
  have hT : ContinuousOn (fun x ↦ (t'.continuousLinearMapAt 𝕜 x).comp
      (((e x : E x →L[𝕜] E' x)).comp (t.symmL 𝕜 x))) (t.baseSet ∩ t'.baseSet) :=
    continuousOn_continuousLinearMapAt_comp_symmL (g := id)
      (φ := fun x ↦ (e x : E x →L[𝕜] E' x)) he t' t
  have hTL : ContinuousAt (fun x ↦ ((t'.continuousLinearMapAt 𝕜 x).comp
      (((e x : E x →L[𝕜] E' x)).comp (t.symmL 𝕜 x))).comp L) a :=
    (hT.continuousAt ((t.open_baseSet.inter t'.open_baseSet).mem_nhds
      ⟨mem_baseSet_trivializationAt F E a, mem_baseSet_trivializationAt F' E' a⟩)).clm_comp
      continuousAt_const
  refine ⟨fun x ↦ (((t'.continuousLinearMapAt 𝕜 x).comp
      (((e x : E x →L[𝕜] E' x)).comp (t.symmL 𝕜 x))).comp L).det,
    ContinuousLinearMap.continuous_det.continuousAt.comp hTL,
    fun x hx hx' v ↦ chartCoord_congrModelEquiv e h t t' hx hx' v⟩

/-- **Continuity of the determinant transport between different models.** A fibrewise
continuous linear isomorphism `e` between vector bundles with finite-dimensional models `F` and
`F'`, continuous as a map of total spaces, induces a homeomorphism of the total spaces of their
determinant lines, which is `TauCeti.DetBundle.congrModelEquiv e x` on the fibre over `x`. -/
noncomputable def congrModelHomeomorph (e : ∀ x, E x ≃L[𝕜] E' x)
    (he : Continuous (fun p : TotalSpace F E ↦ TotalSpace.mk' F' p.proj (e p.proj p.snd))) :
    TotalSpace 𝕜 (DetBundle 𝕜 F E) ≃ₜ TotalSpace 𝕜 (DetBundle 𝕜 F' E') :=
  bundleHomeomorph (congrModelEquiv (F₁ := F) (F' := F') e) <| by
    refine FiberBundle.continuous_of_forall_trivialization _ (fun _ ↦ rfl) fun p ↦ ?_
    obtain ⟨s, hs, hs'⟩ := continuousAt_chartCoord_congrModelEquiv e he p.proj
    refine ⟨trivializationAt 𝕜 (DetBundle 𝕜 F E) p.proj,
      trivializationAt 𝕜 (DetBundle 𝕜 F' E') p.proj, fun x c ↦ s x * c,
      mem_baseSet_trivializationAt 𝕜 _ p.proj, mem_baseSet_trivializationAt 𝕜 _ p.proj,
      (hs.comp (FiberBundle.continuous_proj 𝕜 _).continuousAt).mul
        ((trivializationAt 𝕜 (DetBundle 𝕜 F E) p.proj).continuousOn.continuousAt
          ((trivializationAt 𝕜 (DetBundle 𝕜 F E) p.proj).open_source.mem_nhds
            (FiberBundle.mem_trivializationAt_proj_source))).snd, ?_⟩
    rintro ⟨x, v⟩ hx hx'
    simp only [trivializationAt_eq, trivialization_baseSet] at hx hx' ⊢
    rw [trivialization_apply_mk _ hx', trivialization_apply_mk _ hx, hs' x hx hx' v]

@[simp]
theorem congrModelHomeomorph_apply (e : ∀ x, E x ≃L[𝕜] E' x)
    (he : Continuous (fun p : TotalSpace F E ↦ TotalSpace.mk' F' p.proj (e p.proj p.snd)))
    (p : TotalSpace 𝕜 (DetBundle 𝕜 F E)) :
    congrModelHomeomorph e he p = ⟨p.proj, congrModelEquiv (F₁ := F) (F' := F') e p.proj p.snd⟩ :=
  bundleHomeomorph_apply _ _ p

@[simp]
theorem congrModelHomeomorph_symm_apply (e : ∀ x, E x ≃L[𝕜] E' x)
    (he : Continuous (fun p : TotalSpace F E ↦ TotalSpace.mk' F' p.proj (e p.proj p.snd)))
    (p : TotalSpace 𝕜 (DetBundle 𝕜 F' E')) :
    (congrModelHomeomorph e he).symm p =
      ⟨p.proj, (congrModelEquiv (F₁ := F) (F' := F') e p.proj).symm p.snd⟩ :=
  bundleHomeomorph_symm_apply _ _ p

section SameModel

variable {E₂ : B → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [∀ x, TopologicalSpace (E₂ x)] [TopologicalSpace (TotalSpace F E₂)]
  [FiberBundle F E₂] [VectorBundle 𝕜 F E₂]

/-- For bundles with the same model, the homeomorphism `congrModelHomeomorph` is Tau Ceti's
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
