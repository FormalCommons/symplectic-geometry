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
import TauCeti.Geometry.Manifold.VectorBundle.Hom.Basic
import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Extension
import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Polar
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
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

In the other direction, a smooth almost complex structure `K` on `G` pulls back along `ψ` to
the field `dψ⁻¹ ∘ K ∘ dψ` on the source of `ψ`, which is a smooth section of the endomorphism
bundle of `TM` there. Its proof adapts Tau Ceti's private
`TauCeti.SmoothAlmostComplexStructure.contMDiff_localPullbackEndomorphism`, which does this for
a local diffeomorphism defined on all of `M`, to a chart defined on an open subset.

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
* `TauCeti.SmoothAlmostComplexStructure.chartPushforwardAt`: the pushforward at a point of the
  target, as an almost complex structure, and
  `TauCeti.SmoothAlmostComplexStructure.continuous_toContinuousLinearMap_chartPushforwardAt`: its
  continuity in the operator norm.
* `TauCeti.SmoothAlmostComplexStructure.compatible_chartPushforwardAt`: a chart that pulls a
  symplectic form `σ₀` back to a form compatible with `J` makes `σ₀` compatible with the
  pushforward of `J` at every point of its target.
* `TauCeti.SmoothAlmostComplexStructure.contMDiffOn_mfderiv_symm_comp_comp_mfderiv`: the pullback
  `dψ⁻¹ ∘ K ∘ dψ` of a smooth almost complex structure `K` on `G` is smooth on the source of `ψ`.
* `TauCeti.SmoothTwoForm.IsNondegenerate.exists_compatible_mfderiv_apply_eq`: if `ψ` pulls a
  symplectic form `form₀` on `G` back to `σ`, then for every structure `J₀` compatible with
  `form₀` and every closed set `A` in the source of `ψ`, some structure on `M` compatible with `σ`
  is carried to `J₀` by the derivative of `ψ` along `A`. It extends the pullback of `J₀` with Tau
  Ceti's `TauCeti.SmoothTwoForm.Compatible.exists_compatible_eqOn`.

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
    (J.contDiffOn_chartPushforward ψ.contMDiffOn ψ.symm.contMDiffOn).continuousOn

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

/-- Let `ψ` be a smooth chart of `M` into a normed space `G`, and `K` a smooth almost complex
structure on `G`. The endomorphisms `dψ⁻¹_{ψ x} ∘ K_{ψ x} ∘ dψ_x` of the tangent spaces of `M`
form a smooth section of the endomorphism bundle of `TM` over the source of `ψ`. -/
theorem contMDiffOn_mfderiv_symm_comp_comp_mfderiv [FiniteDimensional ℝ E]
    (ψ : PartialDiffeomorph I 𝓘(ℝ, G) M G ∞) (K : SmoothAlmostComplexStructure 𝓘(ℝ, G) G) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x ↦ Bundle.TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) x
        (mfderiv 𝓘(ℝ, G) I ψ.symm (ψ x) ∘L K.toEndomorphism (ψ x) ∘L
          mfderiv I 𝓘(ℝ, G) ψ x)) ψ.source := by
  intro x₀ hx₀
  refine ContMDiffAt.contMDiffWithinAt ((TauCeti.contMDiffAt_hom_bundle_iff _ x₀).2 fun v₀ ↦ ?_)
  -- Near `(x₀, v₀)` the map on tangent vectors is `Tψ⁻¹ ∘ K ∘ Tψ`.
  have hTψ : ContMDiffAt I.tangent 𝓘(ℝ, G).tangent ∞ (tangentMap I 𝓘(ℝ, G) ψ) ⟨x₀, v₀⟩ :=
    ContMDiffAt.contMDiffAt_tangentMap (X := ⟨x₀, v₀⟩)
      ((ψ.contMDiffOn x₀ hx₀).contMDiffAt (ψ.open_source.mem_nhds hx₀)) (by simp)
  have hK : ContMDiff 𝓘(ℝ, G).tangent 𝓘(ℝ, G).tangent ∞
      (fun w : TangentBundle 𝓘(ℝ, G) G ↦ Bundle.TotalSpace.mk' G w.proj (K w.proj w.snd)) :=
    (K.toEndomorphism.contMDiff.comp
      (Bundle.contMDiff_proj (TangentSpace 𝓘(ℝ, G)))).clm_bundle_apply contMDiff_id
  have hTψs : ContMDiffAt 𝓘(ℝ, G).tangent I.tangent ∞ (tangentMap 𝓘(ℝ, G) I ψ.symm)
      (Bundle.TotalSpace.mk' G (ψ x₀) (K (ψ x₀) (mfderiv I 𝓘(ℝ, G) ψ x₀ v₀))) :=
    ContMDiffAt.contMDiffAt_tangentMap ((ψ.symm.contMDiffOn _ (ψ.map_source hx₀)).contMDiffAt
      (ψ.open_target.mem_nhds (ψ.map_source hx₀))) (by simp)
  refine (hTψs.comp (⟨x₀, v₀⟩ : TangentBundle I M) ((hK _).comp _ hTψ)).congr_of_eventuallyEq ?_
  -- Over the source of `ψ`, `ψ⁻¹ ∘ ψ` is the identity, so the base points agree; the fibres over
  -- both are the model space `E`, so the second components agree as they stand.
  filter_upwards [(FiberBundle.continuous_proj E (TangentSpace I)).continuousAt.preimage_mem_nhds
    (ψ.open_source.mem_nhds hx₀)] with ⟨x, v⟩ hx
  exact Bundle.TotalSpace.ext (ψ.left_inv hx).symm HEq.rfl

end SmoothAlmostComplexStructure

namespace SmoothTwoForm.IsNondegenerate

variable {E H M G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Let `σ` be a fiberwise nondegenerate two-form on a Hausdorff σ-compact manifold `M`, and `ψ`
a smooth chart of `M` into `G` that pulls a symplectic form `form₀` on `G` back to `σ` on its
source. For every almost complex structure `J₀` on `G` compatible with `form₀` and every closed
set `A` inside the source of `ψ`, there is a smooth almost complex structure on `M`, compatible
with `σ`, that the derivative of `ψ` intertwines with `J₀` at every point of `A`. -/
theorem exists_compatible_mfderiv_apply_eq [FiniteDimensional ℝ E] [FiniteDimensional ℝ G]
    [T2Space M] [SigmaCompactSpace M] {σ : SmoothTwoForm I M} (hσ : σ.IsNondegenerate)
    {form₀ : SymplecticForm G} {ψ : PartialDiffeomorph I 𝓘(ℝ, G) M G ∞}
    (hψ : ∀ x ∈ ψ.source, ∀ v w : TangentSpace I x,
      σ.eval₂ x v w = form₀ (mvfderiv I ψ x v) (mvfderiv I ψ x w))
    {J₀ : AlmostComplexStructure G} (hJ₀ : form₀.Compatible J₀) {A : Set M} (hA : IsClosed A)
    (hAψ : A ⊆ ψ.source) :
    ∃ J' : SmoothAlmostComplexStructure I M, σ.Compatible J' ∧
      ∀ x ∈ A, ∀ v, mfderiv I 𝓘(ℝ, G) ψ x (J' x v) = J₀ (mfderiv I 𝓘(ℝ, G) ψ x v) := by
  classical
  obtain ⟨J₁, hJ₁⟩ := hσ.exists_compatible
  -- On the source of `ψ`, the structure `J₀` carried back by the derivative of `ψ`.
  let e (x : M) (hx : x ∈ ψ.source) : E ≃L[ℝ] G :=
    (ψ.isLocalDiffeomorphAt _ _ _ hx).mfderivToContinuousLinearEquiv (by simp)
  let K : M → AlmostComplexStructure E := fun x ↦
    if hx : x ∈ ψ.source then J₀.transport (e x hx).symm.toLinearEquiv
    else J₁.almostComplexStructureAt x
  have hKe (x : M) (hx : x ∈ ψ.source) : K x = J₀.transport (e x hx).symm.toLinearEquiv :=
    dite_eq_left_of_eq_true (eq_true hx)
  have hK (x : M) (hx : x ∈ ψ.source) (v : E) :
      K x v = mfderiv 𝓘(ℝ, G) I ψ.symm (ψ x) (J₀ (mfderiv I 𝓘(ℝ, G) ψ x v)) := by
    rw [hKe x hx]
    exact (AlmostComplexStructure.transport_apply _ _ v).trans
      (IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv_symm_apply _ _ (Set.eqOn_refl _ _) hx _)
  have hKc (x : M) (hx : x ∈ ψ.source) : (hσ.symplecticFormAt x).Compatible (K x) := by
    have he : SymplecticForm.IsSymplectomorphism form₀ (hσ.symplecticFormAt x)
        (e x hx).symm.toLinearEquiv :=
      SymplecticForm.isSymplectomorphism_iff.2 fun v w ↦ by
        rw [hσ.symplecticFormAt_apply, hψ x hx, mvfderiv_apply_eq_mfderiv_apply,
          mvfderiv_apply_eq_mfderiv_apply]
        exact congrArg₂ (fun a b ↦ form₀ a b)
          (IsLocalDiffeomorphAt.mfderiv_mfderivToContinuousLinearEquiv_symm_apply _ _ v)
          (IsLocalDiffeomorphAt.mfderiv_mfderivToContinuousLinearEquiv_symm_apply _ _ w)
    rw [← SymplecticForm.isSymplectomorphism_iff_transport_eq.1 he, hKe x hx]
    exact hJ₀.transport _
  have hKs : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x ↦ Bundle.TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) x
        (LinearMap.toContinuousLinearMap (K x).toLinearMap)) ψ.source := by
    refine (SmoothAlmostComplexStructure.contMDiffOn_mfderiv_symm_comp_comp_mfderiv ψ
      J₀.constSmooth).congr fun x hx ↦ ?_
    refine congrArg (Bundle.TotalSpace.mk' _ x) (ContinuousLinearMap.ext fun v ↦ ?_)
    -- Turning `(K x).toLinearMap` into a continuous linear map keeps its values.
    exact (hK x hx v).trans (congrArg _ (J₀.constSmooth_apply (ψ x) _).symm)
  obtain ⟨J', hJ', hJ'A, -, -⟩ := hJ₁.exists_compatible_eqOn K hKc ψ.open_source hA hAψ hKs
  refine ⟨J', hJ', fun x hx v ↦ ?_⟩
  have hJx : J' x v = K x v := (J'.almostComplexStructureAt_apply x v).symm.trans
    (congrArg (fun L : AlmostComplexStructure E ↦ L v) (hJ'A x hx))
  rw [hJx, hKe x (hAψ hx)]
  exact (congrArg _ (AlmostComplexStructure.transport_apply _ _ v)).trans
    (IsLocalDiffeomorphAt.mfderiv_mfderivToContinuousLinearEquiv_symm_apply _ _ _)

end SmoothTwoForm.IsNondegenerate

end TauCeti

end
