/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.MFDeriv
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Chart
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Pushforward
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm

/-!
# The chart pushforward of a smooth almost complex structure

Tau Ceti's `SmoothAlmostComplexStructure.chartPushforward` pushes a smooth almost complex
structure `J` on `M` forward along a chart `ψ : M → G` into a normed space: at `p` it is
`dψ ∘ J ∘ dψ⁻¹`, taken at `ψ⁻¹ p`. This file gives its evaluation lemma, the counterpart of Tau
Ceti's `ContMDiffAlmostComplexStructure.chartPushforward_apply`. For a smooth chart
`ψ : PartialDiffeomorph I 𝓘(ℝ, G) M G ∞` it identifies the chart pushforward with Tau Ceti's
`PartialDiffeomorph.pushforwardEndomorphism`, whose lemmas then apply to it, and adds the facts
that the derivative of the inverse of `ψ` intertwines the pushforward with `J`, that the
derivative of the transition between two smooth charts intertwines the pushforwards along them,
and that the pushforward is smooth on the target of `ψ` when `M` has no boundary. Tau Ceti's
`PartialDiffeomorph.pushforwardAt`, the pushforward at a point of the target as an almost complex
structure on `G`, then depends continuously on the point in the operator norm; and if `ψ` pulls a
symplectic form `σ₀` on `G` back to a two-form compatible with `J`, then `σ₀` is compatible with
it.

## Main declarations

* `TauCeti.SmoothAlmostComplexStructure.chartPushforward_apply`: the value of the pushforward.
* `TauCeti.SmoothAlmostComplexStructure.chartPushforward_toOpenPartialHomeomorph`: along a smooth
  chart, the pushforward is `PartialDiffeomorph.pushforwardEndomorphism`.
* `TauCeti.SmoothAlmostComplexStructure.mfderiv_symm_apply_chartPushforward_apply`: the
  derivative of the inverse of a smooth chart intertwines the pushforward with `J`.
* `TauCeti.SmoothAlmostComplexStructure.chartPushforward_symm_trans_comp_fderiv`: the derivative
  of the transition between two smooth charts intertwines the pushforwards along them.
* `TauCeti.SmoothAlmostComplexStructure.forall_chartPushforward_apply_eq_iff`: a chart pushes `J`
  forward to a fixed map exactly when its derivative intertwines `J` with that map.
* `TauCeti.SmoothAlmostComplexStructure.contDiffOn_chartPushforward_toOpenPartialHomeomorph` and
  `TauCeti.SmoothAlmostComplexStructure.contDiffAt_chartPushforward`: on a boundaryless manifold,
  the pushforward along a smooth chart is smooth on its target, and at each point of it; Tau
  Ceti's `TauCeti.SmoothAlmostComplexStructure.contDiffOn_chartPushforward` applied to the
  smoothness of the chart and of its inverse.
* `PartialDiffeomorph.continuous_toContinuousLinearMap_pushforwardAt`: the continuity of
  `PartialDiffeomorph.pushforwardAt` in the operator norm.
* `TauCeti.SmoothTwoForm.Compatible.compatible_pushforwardAt`: a chart that pulls a symplectic
  form `σ₀` back to a form compatible with `J` makes `σ₀` compatible with the pushforward of `J`
  at every point of its target. Its proof follows that of Tau Ceti's
  `PartialDiffeomorph.compatible_pushforwardAt`, for a constant form on `G` given through the
  pullback identity on the source of the chart.

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

/-- Along a smooth chart `ψ` into a normed space, the pushforward of `J` is Tau Ceti's pushforward
endomorphism field `ψ.pushforwardEndomorphism J` of `J` along the partial diffeomorphism `ψ`. -/
theorem chartPushforward_toOpenPartialHomeomorph (ψ : PartialDiffeomorph I 𝓘(ℝ, G) M G ∞) :
    J.chartPushforward ψ.toOpenPartialHomeomorph = ψ.pushforwardEndomorphism J := by
  funext p
  ext w
  rw [chartPushforward_apply, ψ.coe_toOpenPartialHomeomorph_symm, ψ.toFun'_toOpenPartialHomeomorph]
  exact (ψ.pushforwardEndomorphism_apply J p w).symm

/-- The derivative of the inverse of a smooth chart `ψ` into a normed space intertwines the
pushforward of `J` along `ψ` with `J`: `dψ⁻¹_p ((ψ_* J)_p w) = J (dψ⁻¹_p w)` at every point `p`
of the target of `ψ`. -/
theorem mfderiv_symm_apply_chartPushforward_apply (ψ : PartialDiffeomorph I 𝓘(ℝ, G) M G ∞)
    {p : G} (hp : p ∈ ψ.target) (w : G) :
    mfderiv 𝓘(ℝ, G) I ψ.symm p (J.chartPushforward ψ.toOpenPartialHomeomorph p w) =
      J (ψ.symm p) (mfderiv 𝓘(ℝ, G) I ψ.symm p w) := by
  rw [chartPushforward_apply, ψ.coe_toOpenPartialHomeomorph_symm, ψ.toFun'_toOpenPartialHomeomorph]
  exact ψ.mfderiv_symm_apply_mfderiv_apply_of_mem_target (by simp) hp _

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
  · have h' := h _ (ψ.map_source hy) (mfderiv I 𝓘(ℝ, G) ψ y v)
    rw [chartPushforward_toOpenPartialHomeomorph] at h'
    exact (ψ.pushforwardEndomorphism_mfderiv_apply J hy v).symm.trans h'
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

end SmoothAlmostComplexStructure

/-! ### Compatibility of the pushforward at a point -/

namespace SmoothTwoForm.Compatible

variable {E H M G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Let `ψ` be a smooth chart into a normed space `G` that pulls a symplectic form `σ₀` on `G`
back to the two-form `σ` on its source. If `σ` is compatible with `J`, then at every point `p` of
the target of `ψ`, `σ₀` is compatible with the pushforward of `J` along `ψ` at `p`. -/
theorem compatible_pushforwardAt {σ : SmoothTwoForm I M} {J : SmoothAlmostComplexStructure I M}
    (hσ : σ.Compatible J) {σ₀ : SymplecticForm G} (ψ : PartialDiffeomorph I 𝓘(ℝ, G) M G ∞)
    (hψ : ∀ x ∈ ψ.source, ∀ v w : TangentSpace I x,
      σ.eval₂ x v w = σ₀ (mvfderiv I ψ x v) (mvfderiv I ψ x w))
    {p : G} (hp : p ∈ ψ.target) :
    σ₀.Compatible (ψ.pushforwardAt J hp) := by
  obtain ⟨x, hx, rfl⟩ : ∃ x ∈ ψ.source, ψ x = p :=
    ⟨ψ.symm p, ψ.map_target hp, ψ.right_inv hp⟩
  have hsurj := (ψ.isInvertible_mfderiv (by simp) hx).surjective
  have hψ' (v w : TangentSpace I x) :
      σ₀ (mfderiv I 𝓘(ℝ, G) ψ x v) (mfderiv I 𝓘(ℝ, G) ψ x w) = σ.eval₂ x v w := by
    rw [hψ x hx, mvfderiv_apply_eq_mfderiv_apply, mvfderiv_apply_eq_mfderiv_apply]
  -- `ψ.pushforwardAt J hp` acts on `TangentSpace 𝓘(ℝ, G) (ψ x)`, which `rw` does not match with
  -- `G`; the steps below are terms, checked up to that identification.
  have hP (v : TangentSpace I x) :
      ψ.pushforwardAt J hp (mfderiv I 𝓘(ℝ, G) ψ x v) = mfderiv I 𝓘(ℝ, G) ψ x (J x v) :=
    (ψ.pushforwardAt_apply J hp _).trans (ψ.pushforwardEndomorphism_mfderiv_apply J hx v)
  have hJ := hσ.compatibleAt x
  refine SymplecticForm.Compatible.of_tames ((SymplecticForm.invariant_iff _ _).2 fun a b ↦ ?_)
    fun a ha ↦ ?_
  · obtain ⟨a, rfl⟩ := hsurj a
    obtain ⟨b, rfl⟩ := hsurj b
    refine (congrArg₂ (fun u w : G ↦ σ₀ u w) (hP a) (hP b)).trans ?_
    refine ((hψ' _ _).trans ?_).trans (hψ' a b).symm
    simpa only [SmoothTwoForm.IsNondegenerate.symplecticFormAt_apply,
      SmoothAlmostComplexStructure.almostComplexStructureAt_apply] using
      (SymplecticForm.invariant_iff _ _).1 hJ.invariant a b
  · obtain ⟨a, rfl⟩ := hsurj a
    have ha' : a ≠ 0 := by
      rintro rfl
      exact ha (map_zero _)
    refine lt_of_lt_of_eq ?_ ((congrArg (fun u : G ↦ σ₀ (mfderiv I 𝓘(ℝ, G) ψ x a) u)
      (hP a)).trans (hψ' _ _)).symm
    simpa only [SmoothTwoForm.IsNondegenerate.symplecticFormAt_apply,
      SmoothAlmostComplexStructure.almostComplexStructureAt_apply] using hJ.tames a ha'

end SmoothTwoForm.Compatible

end TauCeti

/-! ### The pushforward at a point in the operator norm -/

namespace PartialDiffeomorph

open TauCeti

variable {E H M G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  (ψ : PartialDiffeomorph I 𝓘(ℝ, G) M G ∞) (J : SmoothAlmostComplexStructure I M)

/-- The almost complex structure `ψ.pushforwardAt J hp` on `G` acts as the pushforward of `J` along
the chart `ψ` at `p`. -/
theorem pushforwardAt_apply_eq_chartPushforward_apply {p : G} (hp : p ∈ ψ.target) (w : G) :
    ψ.pushforwardAt J hp w = J.chartPushforward ψ.toOpenPartialHomeomorph p w := by
  rw [SmoothAlmostComplexStructure.chartPushforward_toOpenPartialHomeomorph]
  exact ψ.pushforwardAt_apply J hp w

/-- In finite dimension, the continuous linear map of the almost complex structure
`ψ.pushforwardAt J hp` on `G` is the pushforward of `J` along the chart `ψ` at `p`. -/
theorem toContinuousLinearMap_pushforwardAt [FiniteDimensional ℝ G] {p : G} (hp : p ∈ ψ.target) :
    LinearMap.toContinuousLinearMap (ψ.pushforwardAt J hp).toLinearMap =
      J.chartPushforward ψ.toOpenPartialHomeomorph p := by
  ext w
  exact ψ.pushforwardAt_apply_eq_chartPushforward_apply J hp w

/-- On a boundaryless manifold, the almost complex structures `ψ.pushforwardAt J hp` on a
finite-dimensional normed space `G` depend continuously, in the operator norm, on the point `p`
of the target of the smooth chart `ψ`. -/
theorem continuous_toContinuousLinearMap_pushforwardAt [I.Boundaryless] [FiniteDimensional ℝ G] :
    Continuous fun p : ψ.target ↦
      (LinearMap.toContinuousLinearMap (ψ.pushforwardAt J p.property).toLinearMap :
        G →L[ℝ] G) :=
  (continuousOn_iff_continuous_domRestrict.1
    (J.contDiffOn_chartPushforward_toOpenPartialHomeomorph ψ).continuousOn).congr fun p ↦
      (toContinuousLinearMap_pushforwardAt ψ J p.property).symm

end PartialDiffeomorph

end
