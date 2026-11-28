/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.MFDeriv
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Chart
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
public import TauCeti.Geometry.Symplectic.Transport
import TauCeti.Geometry.Symplectic.SymplecticTransport

/-!
# The chart pushforward of a smooth almost complex structure

Tau Ceti's `SmoothAlmostComplexStructure.chartPushforward` pushes a smooth almost complex
structure `J` on `M` forward along a chart `ψ : M → G` into a normed space: at `p` it is
`dψ ∘ J ∘ dψ⁻¹`, taken at `ψ⁻¹ p`. This file gives its evaluation lemma, the counterpart of Tau
Ceti's `ContMDiffAlmostComplexStructure.chartPushforward_apply`, and, for a smooth chart
`ψ : PartialDiffeomorph I 𝓘(ℝ, G) M G ∞`, the facts that the derivatives of `ψ` and of its
inverse intertwine `J` with its pushforward, that the pushforward squares to `-1` on the target
of `ψ`, and that the derivative of the transition between two smooth charts intertwines the
pushforwards along them. At each point of the target the pushforward is then an almost complex
structure on `G`, which depends continuously on the point on a boundaryless manifold; if `ψ`
pulls a symplectic form `σ₀` on `G` back to a two-form compatible with `J`, then `σ₀` is
compatible with it.

## Main declarations

* `TauCeti.SmoothAlmostComplexStructure.chartPushforward_apply`: the value of the pushforward.
* `TauCeti.SmoothAlmostComplexStructure.mfderiv_apply_eq_chartPushforward_apply` and
  `TauCeti.SmoothAlmostComplexStructure.mfderiv_symm_apply_chartPushforward_apply`: the
  derivative of a smooth chart, and that of its inverse, intertwine `J` with its pushforward.
* `TauCeti.SmoothAlmostComplexStructure.chartPushforward_apply_chartPushforward_apply`: the
  pushforward squares to `-1` on the target.
* `TauCeti.SmoothAlmostComplexStructure.chartPushforward_symm_trans_comp_fderiv`: the derivative
  of the transition between two smooth charts intertwines the pushforwards along them.
* `TauCeti.SmoothAlmostComplexStructure.forall_chartPushforward_apply_eq_iff`: a chart pushes `J`
  forward to a fixed map exactly when its derivative intertwines `J` with that map.
* `TauCeti.SmoothAlmostComplexStructure.contDiffOn_chartPushforward_toOpenPartialHomeomorph` and
  `TauCeti.SmoothAlmostComplexStructure.contDiffAt_chartPushforward`: on a boundaryless manifold,
  the pushforward along a smooth chart is smooth on its target, and at each point of it; Tau
  Ceti's `TauCeti.SmoothAlmostComplexStructure.contDiffOn_chartPushforward` applied to the
  smoothness of the chart and of its inverse.
* `TauCeti.SmoothAlmostComplexStructure.chartPushforwardAt`: the pushforward at a point of the
  target, as an almost complex structure, and
  `TauCeti.SmoothAlmostComplexStructure.continuous_toContinuousLinearMap_chartPushforwardAt`: its
  continuity in the operator norm.
* `TauCeti.SmoothAlmostComplexStructure.compatible_chartPushforwardAt`: a chart that pulls a
  symplectic form `σ₀` back to a form compatible with `J` makes `σ₀` compatible with the
  pushforward of `J` at every point of its target.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Section 4.2.
-/

public section

open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothAlmostComplexStructure

variable {E H M G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup G] [NormedSpace ℝ G] (J : SmoothAlmostComplexStructure I M)

/-- The value of the pushforward of `J` along `ψ` at `p` on `w` is `dψ (J (dψ⁻¹ w))`, with the
derivatives of `ψ` at `ψ⁻¹ p` and of `ψ⁻¹` at `p`. -/
theorem chartPushforward_apply (ψ : OpenPartialHomeomorph M G) (p w : G) :
    J.chartPushforward ψ p w =
      mfderiv I 𝓘(ℝ, G) ψ (ψ.symm p) (J (ψ.symm p) (mfderiv 𝓘(ℝ, G) I ψ.symm p w)) := by
  -- Tau Ceti does not expose `chartPushforward`; its finite-regularity version has this lemma.
  rw [← toContMDiff_chartPushforward J ⊤, ContMDiffAlmostComplexStructure.chartPushforward_apply,
    toContMDiff_apply]

/-- The derivative of a smooth chart `ψ` into a normed space intertwines `J` with its pushforward
along `ψ`: `dψ_y (J v) = (ψ_* J)_{ψ y} (dψ_y v)` at every point `y` of the source of `ψ`. -/
theorem mfderiv_apply_eq_chartPushforward_apply (ψ : PartialDiffeomorph I 𝓘(ℝ, G) M G ∞) {y : M}
    (hy : y ∈ ψ.source) (v : TangentSpace I y) :
    mfderiv I 𝓘(ℝ, G) ψ y (J y v) =
      J.chartPushforward ψ.toOpenPartialHomeomorph (ψ y) (mfderiv I 𝓘(ℝ, G) ψ y v) := by
  have h := DFunLike.congr_fun ((J.toContMDiff ⊤).mfderiv_comp_toEndomorphism
    ψ.toOpenPartialHomeomorph hy (ψ.mdifferentiableAt (by simp) hy)
    (ψ.symm.mdifferentiableAt (by simp) (ψ.map_source hy))) v
  simp only [toContMDiff_chartPushforward, toContMDiff_toEndomorphism_apply,
    ψ.toFun'_toOpenPartialHomeomorph] at h
  exact h

/-- The derivative of the inverse of a smooth chart `ψ` into a normed space intertwines the
pushforward of `J` along `ψ` with `J`: `dψ⁻¹_p ((ψ_* J)_p w) = J (dψ⁻¹_p w)` at every point `p`
of the target of `ψ`. -/
theorem mfderiv_symm_apply_chartPushforward_apply (ψ : PartialDiffeomorph I 𝓘(ℝ, G) M G ∞)
    {p : G} (hp : p ∈ ψ.target) (w : G) :
    mfderiv 𝓘(ℝ, G) I ψ.symm p (J.chartPushforward ψ.toOpenPartialHomeomorph p w) =
      J (ψ.symm p) (mfderiv 𝓘(ℝ, G) I ψ.symm p w) := by
  rw [chartPushforward_apply, ψ.coe_toOpenPartialHomeomorph_symm, ψ.toFun'_toOpenPartialHomeomorph]
  exact ψ.mfderiv_symm_apply_mfderiv_apply_of_mem_target (by simp) hp _

/-- The pushforward of `J` along a smooth chart `ψ` into a normed space squares to `-1` at every
point of the target of `ψ`. -/
theorem chartPushforward_apply_chartPushforward_apply (ψ : PartialDiffeomorph I 𝓘(ℝ, G) M G ∞)
    {p : G} (hp : p ∈ ψ.target) (w : G) :
    J.chartPushforward ψ.toOpenPartialHomeomorph p
      (J.chartPushforward ψ.toOpenPartialHomeomorph p w) = -w := by
  have h := (J.toContMDiff ⊤).chartPushforward_apply_chartPushforward_apply
    ψ.toOpenPartialHomeomorph hp (ψ.mdifferentiableAt (by simp) (ψ.map_target hp))
    (ψ.symm.mdifferentiableAt (by simp) hp) w
  rwa [toContMDiff_chartPushforward] at h

/-- **Transitions intertwine the pushforwards.** For smooth charts `Φ : M → G` and `Ψ : M → G'`
into normed spaces and `w` in the source of the transition `τ = Ψ ∘ Φ⁻¹`, the derivative of `τ`
at `w` carries the pushforward of `J` along `Φ` at `w` to its pushforward along `Ψ` at `τ w`. -/
theorem chartPushforward_symm_trans_comp_fderiv {G' : Type*} [NormedAddCommGroup G']
    [NormedSpace ℝ G'] (Φ : PartialDiffeomorph I 𝓘(ℝ, G) M G ∞)
    (Ψ : PartialDiffeomorph I 𝓘(ℝ, G') M G' ∞) {w : G}
    (hw : w ∈ (Φ.toOpenPartialHomeomorph.symm ≫ₕ Ψ.toOpenPartialHomeomorph).source) :
    (J.chartPushforward Ψ.toOpenPartialHomeomorph
          ((Φ.toOpenPartialHomeomorph.symm ≫ₕ Ψ.toOpenPartialHomeomorph) w)).comp
        (fderiv ℝ (Φ.toOpenPartialHomeomorph.symm ≫ₕ Ψ.toOpenPartialHomeomorph) w) =
      (fderiv ℝ (Φ.toOpenPartialHomeomorph.symm ≫ₕ Ψ.toOpenPartialHomeomorph) w).comp
        (J.chartPushforward Φ.toOpenPartialHomeomorph w) := by
  have hw' : w ∈ Φ.target ∧ Φ.symm w ∈ Ψ.source := by simpa using hw
  have h := (J.toContMDiff ⊤).chartPushforward_symm_trans_comp_fderiv hw
    (Φ.mdifferentiableAt (by simp) (Φ.map_target hw'.1))
    (by
      rw [PartialDiffeomorph.coe_toOpenPartialHomeomorph_symm]
      exact Ψ.symm.mdifferentiableAt (by simp) (Ψ.map_source hw'.2))
    (Φ.differentiableAt_symm_trans Ψ (by simp) hw)
  rwa [toContMDiff_chartPushforward, toContMDiff_chartPushforward] at h

/-- A smooth chart `ψ` into a normed space carries `J` to a fixed map `J₀` on its target exactly
when its derivative intertwines `J` with `J₀` at every point of its source. -/
theorem forall_chartPushforward_apply_eq_iff (ψ : PartialDiffeomorph I 𝓘(ℝ, G) M G ∞)
    (J₀ : G → G) :
    (∀ p ∈ ψ.target, ∀ w : G, J.chartPushforward ψ.toOpenPartialHomeomorph p w = J₀ w) ↔
      ∀ y ∈ ψ.source, ∀ v : TangentSpace I y,
        mfderiv I 𝓘(ℝ, G) ψ y (J y v) = J₀ (mfderiv I 𝓘(ℝ, G) ψ y v) := by
  refine ⟨fun h y hy v ↦ ?_, fun h p hp w ↦ ?_⟩
  · exact (J.mfderiv_apply_eq_chartPushforward_apply ψ hy v).trans (h _ (ψ.map_source hy) _)
  · rw [chartPushforward_apply]
    exact (h _ (ψ.map_target hp) _).trans
      (congrArg J₀ (ψ.mfderiv_apply_mfderiv_symm_apply (by simp) hp w))

/-- On a boundaryless manifold, the pushforward of `J` along a smooth chart `ψ` into a normed
space is smooth on the target of `ψ`. -/
theorem contDiffOn_chartPushforward_toOpenPartialHomeomorph [I.Boundaryless]
    (ψ : PartialDiffeomorph I 𝓘(ℝ, G) M G ∞) :
    ContDiffOn ℝ ∞ (J.chartPushforward ψ.toOpenPartialHomeomorph) ψ.target :=
  J.contDiffOn_chartPushforward ψ.contMDiffOn ψ.symm.contMDiffOn

/-- On a boundaryless manifold, the pushforward of `J` along a smooth chart `ψ` into a normed
space is smooth at every point of the target of `ψ`. -/
theorem contDiffAt_chartPushforward [I.Boundaryless] (ψ : PartialDiffeomorph I 𝓘(ℝ, G) M G ∞)
    {p : G} (hp : p ∈ ψ.target) :
    ContDiffAt ℝ ∞ (J.chartPushforward ψ.toOpenPartialHomeomorph) p :=
  (J.contDiffOn_chartPushforward_toOpenPartialHomeomorph ψ).contDiffAt
    (ψ.open_target.mem_nhds hp)

/-! ### The pushforward at a point as an almost complex structure -/

/-- At a point `p` of the target of a smooth chart `ψ` into a normed space, the pushforward of `J`
along `ψ` at `p`, as an almost complex structure on `G`: the transport of `J` at `ψ⁻¹ p` along the
derivative of `ψ` there. -/
noncomputable def chartPushforwardAt (ψ : PartialDiffeomorph I 𝓘(ℝ, G) M G ∞) {p : G}
    (hp : p ∈ ψ.target) : AlmostComplexStructure G :=
  (J.almostComplexStructureAt (ψ.symm p)).transport
    (ψ.mfderivSymmEquiv (by simp) hp).symm.toLinearEquiv

/-- `J.chartPushforwardAt ψ hp` is the transport of `J` at `ψ⁻¹ p` along the derivative of `ψ`
there. -/
theorem chartPushforwardAt_def (ψ : PartialDiffeomorph I 𝓘(ℝ, G) M G ∞) {p : G}
    (hp : p ∈ ψ.target) :
    J.chartPushforwardAt ψ hp = (J.almostComplexStructureAt (ψ.symm p)).transport
      (ψ.mfderivSymmEquiv (by simp) hp).symm.toLinearEquiv :=
  (rfl)

/-- The almost complex structure `J.chartPushforwardAt ψ hp` acts as the pushforward of `J`
along `ψ` at `p`. -/
theorem chartPushforwardAt_apply (ψ : PartialDiffeomorph I 𝓘(ℝ, G) M G ∞) {p : G}
    (hp : p ∈ ψ.target) (w : G) :
    J.chartPushforwardAt ψ hp w = J.chartPushforward ψ.toOpenPartialHomeomorph p w := by
  have h₁ (v : TangentSpace I (ψ.symm p)) :
      (ψ.mfderivSymmEquiv (by simp) hp).symm.toLinearEquiv v =
        mfderiv I 𝓘(ℝ, G) ψ (ψ.symm p) v := by
    rw [ContinuousLinearEquiv.coe_toLinearEquiv, ψ.coe_mfderivSymmEquiv_symm]
  have h₂ : (ψ.mfderivSymmEquiv (by simp) hp).symm.toLinearEquiv.symm w =
      mfderiv 𝓘(ℝ, G) I ψ.symm p w := by
    rw [ContinuousLinearEquiv.coe_symm_toLinearEquiv, ContinuousLinearEquiv.symm_symm,
      ψ.coe_mfderivSymmEquiv]
  rw [chartPushforwardAt_def, chartPushforward_apply]
  -- `refine` and `exact` match `TangentSpace 𝓘(ℝ, G) p` with `G`, which `rw` does not.
  refine (AlmostComplexStructure.transport_apply _ _ w).trans ((h₁ _).trans ?_)
  exact congrArg _ ((congrArg _ h₂).trans (J.almostComplexStructureAt_apply _ _))

/-- The linear map of `J.chartPushforwardAt ψ hp` is the pushforward of `J` along `ψ` at `p`. -/
@[simp]
theorem toLinearMap_chartPushforwardAt (ψ : PartialDiffeomorph I 𝓘(ℝ, G) M G ∞) {p : G}
    (hp : p ∈ ψ.target) :
    (J.chartPushforwardAt ψ hp).toLinearMap =
      (J.chartPushforward ψ.toOpenPartialHomeomorph p).toLinearMap :=
  LinearMap.ext (J.chartPushforwardAt_apply ψ hp)

/-- In finite dimension, the continuous linear map of the almost complex structure
`J.chartPushforwardAt ψ hp` is the pushforward of `J` along `ψ` at `p`. -/
theorem toContinuousLinearMap_chartPushforwardAt [FiniteDimensional ℝ G]
    (ψ : PartialDiffeomorph I 𝓘(ℝ, G) M G ∞) {p : G} (hp : p ∈ ψ.target) :
    LinearMap.toContinuousLinearMap (J.chartPushforwardAt ψ hp).toLinearMap =
      J.chartPushforward ψ.toOpenPartialHomeomorph p := by
  ext w
  simp

/-- On a boundaryless manifold, the almost complex structures `J.chartPushforwardAt ψ hp` depend
continuously, in the operator norm, on the point `p` of the target of a smooth chart `ψ` into a
finite-dimensional normed space. -/
theorem continuous_toContinuousLinearMap_chartPushforwardAt [I.Boundaryless]
    [FiniteDimensional ℝ G] (ψ : PartialDiffeomorph I 𝓘(ℝ, G) M G ∞) :
    Continuous fun p : ψ.target ↦
      LinearMap.toContinuousLinearMap (J.chartPushforwardAt ψ p.property).toLinearMap := by
  simp only [toContinuousLinearMap_chartPushforwardAt]
  exact continuousOn_iff_continuous_domRestrict.1
    (J.contDiffOn_chartPushforward_toOpenPartialHomeomorph ψ).continuousOn

/-- Let `ψ` be a smooth chart into a normed space `G` that pulls a symplectic form `σ₀` on `G`
back to the two-form `σ` on its source. If `σ` is compatible with `J`, then at every point `p` of
the target of `ψ`, `σ₀` is compatible with the pushforward of `J` along `ψ` at `p`. -/
theorem compatible_chartPushforwardAt {σ : SmoothTwoForm I M} (hσ : σ.Compatible J)
    {σ₀ : SymplecticForm G} (ψ : PartialDiffeomorph I 𝓘(ℝ, G) M G ∞)
    (hψ : ∀ x ∈ ψ.source, ∀ v w : TangentSpace I x,
      σ.eval₂ x v w = σ₀ (mvfderiv I ψ x v) (mvfderiv I ψ x w))
    {p : G} (hp : p ∈ ψ.target) :
    σ₀.Compatible (J.chartPushforwardAt ψ hp) := by
  have hd (v : TangentSpace I (ψ.symm p)) :
      (ψ.mfderivSymmEquiv (by simp) hp).symm.toLinearEquiv v = mvfderiv I ψ (ψ.symm p) v := by
    rw [mvfderiv_apply_eq_mfderiv_apply, ContinuousLinearEquiv.coe_toLinearEquiv,
      ψ.coe_mfderivSymmEquiv_symm]
  have he : SymplecticForm.IsSymplectomorphism (hσ.isNondegenerate.symplecticFormAt (ψ.symm p)) σ₀
      (ψ.mfderivSymmEquiv (by simp) hp).symm.toLinearEquiv :=
    SymplecticForm.isSymplectomorphism_iff.2 fun v w ↦ by
      rw [hσ.isNondegenerate.symplecticFormAt_apply]
      exact (congrArg₂ (fun a b ↦ σ₀ a b) (hd v) (hd w)).trans (hψ _ (ψ.map_target hp) v w).symm
  rw [← SymplecticForm.isSymplectomorphism_iff_transport_eq.1 he, chartPushforwardAt_def]
  exact (hσ.compatibleAt _).transport _

end SmoothAlmostComplexStructure

end TauCeti

end
