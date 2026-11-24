/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Foliation.Leaf
import SymplecticGeometry.Geometry.Manifold.Distribution.FlatChart
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Analysis.Calculus.MeanValue
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

/-!
# Transport along the leaves of a foliation

Let `𝓕` be a smooth foliation of rank `k` of a boundaryless finite-dimensional manifold `M`
modelled on `E`. This file studies how points move along the leaves of `𝓕`.

Its first result is the existence of foliated charts
(`TauCeti.Foliation.exists_foliatedChart`): for normed spaces `F₁`, `F₂` of dimensions `k` and
`dim E - k`, every point `x` has an open neighbourhood `U` with a diffeomorphism `Ψ` onto the
product `ball 0 1 ×ˢ ball 0 1` of the open unit balls of `F₁` and `F₂`, with `Ψ x = 0`, whose
derivative carries the tangent spaces of `𝓕` onto the vectors with second component `0`, and such
that two points of `U` with the same second coordinate lie on the same leaf. The sets of `U` on
which the second coordinate is constant are the plaques of the chart.

The chart is the flat partial diffeomorphism of
`TauCeti.IsInvolutiveDistribution.exists_flatPartialDiffeomorph` (a form of the Frobenius theorem),
restricted to the preimage of the product of balls by
`PartialDiffeomorph.exists_diffeomorph_ball_prod_ball`, as in the proof of
`TauCeti.SmoothForm.exists_isCharacteristicSubmersion`. Two points of a plaque are joined by the
preimage of the segment between their images, a curve tangent to `𝓕` (the segment argument of
Tau Ceti's `TauCeti.Foliation.sameLeaf_ofSubmodule_iff`, read through the chart), so
`TauCeti.Foliation.sameLeaf_of_contMDiffOn_of_tangent` puts them on one leaf
(`TauCeti.Foliation.sameLeaf_symm_of_segment_subset`).

The file then shows that leaves can be followed smoothly
(`TauCeti.Foliation.SameLeaf.exists_transport`): if `x` and `y` lie on one leaf, a map `φ`,
smooth near `x`, sends `x` to `y` and every nearby point `z` to a point of the leaf of `z`. In a
flat chart, translating the image by a vector with second component `0` moves two points of the
same plaque into each other. Along a curve tangent to `𝓕`, the second coordinate in a flat chart
has derivative `0`, so by the mean value inequality it is constant on a piece of the curve near
each parameter; composing such translations and using that `[0, 1]` is connected
(`IsPreconnected.induction₂'`) handles one curve, and Tau Ceti's `TauCeti.Foliation.sameLeaf_le`
handles chains of curves. It follows that the union of the leaves through an open set is open
(`TauCeti.Foliation.isOpen_saturation`): a point of the union is carried back into the open set by
such a map, and so are the points near it.

## Main results

* `TauCeti.Foliation.exists_foliatedChart`: a foliated chart of `𝓕` around any point, onto the
  product of the unit balls of `F₁` and `F₂`.
* `TauCeti.Foliation.sameLeaf_symm_of_segment_subset`: in a flat partial diffeomorphism, the
  preimages of the ends of a segment in its target with constant second component lie on one
  leaf.
* `TauCeti.Foliation.SameLeaf.exists_transport`: smooth local transport along a leaf.
* `TauCeti.Foliation.isOpen_saturation`: the saturation of an open set is open.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 19
  (foliations and flat charts)
* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §5.4
-/

public section

noncomputable section

open Set Function Manifold Module TopologicalSpace TauCeti.Manifold
open scoped Manifold ContDiff Topology

namespace TauCeti

namespace Foliation

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I (∞ + 1) M] [BoundarylessManifold I M] {k : ℕ}
  {F₁ F₂ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]

omit [FiniteDimensional ℝ E] [BoundarylessManifold I M] [FiniteDimensional ℝ F₁]
  [FiniteDimensional ℝ F₂] in
/-- Let `Φ` be a partial diffeomorphism into `F₁ × F₂` whose derivative sends no tangent vector
outside the tangent spaces of `𝓕` to a vector with second component `0`. If the segment between
two points `p`, `q` with the same second component lies in the target of `Φ`, then `Φ.symm p` and
`Φ.symm q` lie on the same leaf of `𝓕`: the preimage of the segment is a curve tangent to `𝓕`. -/
theorem sameLeaf_symm_of_segment_subset {𝓕 : Foliation I ∞ M k}
    {Φ : PartialDiffeomorph I 𝓘(ℝ, F₁ × F₂) M (F₁ × F₂) ∞}
    (hflat : ∀ y ∈ Φ.source, ∀ v : TangentSpace I y,
      (mfderiv I 𝓘(ℝ, F₁ × F₂) Φ y v).2 = 0 → v ∈ 𝓕.distribution y)
    {p q : F₁ × F₂} (hpq : segment ℝ p q ⊆ Φ.target) (h : p.2 = q.2) :
    𝓕.SameLeaf (Φ.symm p) (Φ.symm q) := by
  have hpq' : (q - p).2 = 0 := by simp [h]
  let ℓ : ℝ → F₁ × F₂ := fun t ↦ p + t • (q - p)
  have hℓ : MapsTo ℓ (Icc 0 1) Φ.target := fun t ht ↦
    hpq (segment_eq_image' ℝ p q ▸ mem_image_of_mem ℓ ht)
  let γ : ℝ → M := Φ.symm ∘ ℓ
  have hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc 0 1) :=
    (Φ.symm.contMDiffOn.comp
      (contDiff_const.add (contDiff_id.smul contDiff_const)).contMDiff.contMDiffOn hℓ).of_le
      (by simp)
  have htan (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      curveVelocityWithin I γ (Icc 0 1) t ∈ 𝓕.distribution (γ t) := by
    have hγt : γ t ∈ Φ.source := Φ.map_target (hℓ ht)
    have hU' : UniqueDiffWithinAt ℝ (Icc (0 : ℝ) 1) t := uniqueDiffOn_Icc zero_lt_one t ht
    refine hflat _ hγt _ ?_
    rw [← curveVelocityWithin_map (Φ.mdifferentiableAt (by simp) hγt) hU'
      ((hγ t ht).mdifferentiableWithinAt one_ne_zero), curveVelocityWithin_eq_derivWithin,
      derivWithin_congr (f₁ := Φ ∘ γ) (f := ℓ) (fun s hs ↦ Φ.right_inv (hℓ hs))
        (Φ.right_inv (hℓ ht))]
    have hd : HasDerivWithinAt ℓ (q - p) (Icc 0 1) t := by
      simpa only [id, one_smul] using
        (((hasDerivAt_id t).smul_const (q - p)).const_add p).hasDerivWithinAt
    rw [hd.derivWithin hU']
    exact hpq'
  have h01 := sameLeaf_of_contMDiffOn_of_tangent hγ htan (left_mem_Icc.2 zero_le_one)
    (right_mem_Icc.2 zero_le_one)
  simpa [γ, ℓ] using h01

/-- **Foliated charts.** Let `𝓕` be a smooth foliation of rank `k` of a boundaryless manifold
modelled on `E`, and let `F₁`, `F₂` be normed spaces with `dim F₁ = k` and `dim E = k + dim F₂`.
Every point `x` has an open neighbourhood `U` with a diffeomorphism `Ψ` from `U` onto the product
of the open unit balls of `F₁` and `F₂`, such that
* `Ψ x = 0`;
* at every `u ∈ U`, a tangent vector `v` lies in the tangent space of `𝓕` exactly when the second
  component of `dΨ_u v` is `0`;
* two points of `U` whose images under `Ψ` have the same second component lie on the same leaf
  of `𝓕`. -/
theorem exists_foliatedChart (𝓕 : Foliation I ∞ M k) (h₁ : finrank ℝ F₁ = k)
    (h₂ : finrank ℝ E = k + finrank ℝ F₂) (x : M) :
    ∃ (U : Opens M) (hxU : x ∈ U) (Ψ : U ≃ₘ^∞⟮I, 𝓘(ℝ, F₁ × F₂)⟯
        (⟨Metric.ball 0 1 ×ˢ Metric.ball 0 1, Metric.isOpen_ball.prod Metric.isOpen_ball⟩ :
          Opens (F₁ × F₂))),
      (Ψ ⟨x, hxU⟩ : F₁ × F₂) = 0 ∧
      (∀ (u : U) (v : TangentSpace I u),
        (mfderiv I 𝓘(ℝ, F₁ × F₂) (fun u ↦ (Ψ u : F₁ × F₂)) u v).2 = 0 ↔
          v ∈ 𝓕.distribution u) ∧
      ∀ u u' : U, (Ψ u : F₁ × F₂).2 = (Ψ u' : F₁ × F₂).2 → 𝓕.SameLeaf u u' := by
  have : IsManifold I ∞ M := .of_le (n := ∞ + 1) le_self_add
  obtain ⟨Φ, hx, h0, hball, hflat⟩ :=
    𝓕.isInvolutiveDistribution.exists_flatPartialDiffeomorph 𝓕.isContMDiffDistribution h₁ h₂ x
  obtain ⟨U, hxU, Ψ, hΨ0, hUΨ⟩ := Φ.exists_diffeomorph_ball_prod_ball hx h0 hball
  have hΨ (u : U) : (Ψ u : F₁ × F₂) = Φ u := (hUΨ u).2
  have huΦ (u : U) : (u : M) ∈ Φ.source ∧ Φ u ∈ Metric.ball 0 1 ×ˢ Metric.ball 0 1 :=
    ⟨(hUΨ u).1, hΨ u ▸ (Ψ u).property⟩
  have hVt : Metric.ball (0 : F₁) 1 ×ˢ Metric.ball (0 : F₂) 1 ⊆ Φ.target :=
    (ball_prod_same (0 : F₁) (0 : F₂) 1).symm ▸ hball
  refine ⟨U, hxU, Ψ, hΨ0, fun u v ↦ ?_, fun u u' huu' ↦ ?_⟩
  · -- `Ψ` is `Φ` on `U`, read in the tangent spaces of `F₁ × F₂`.
    have hcomp : ∀ g : U → F₁ × F₂, g = Φ ∘ Subtype.val →
        (mfderiv I 𝓘(ℝ, F₁ × F₂) g u v : F₁ × F₂) = mfderiv I 𝓘(ℝ, F₁ × F₂) Φ u v := by
      rintro g rfl
      exact mfderiv_comp_subtype_val_apply v
    rw [hcomp _ (funext hΨ)]
    exact hflat u (huΦ u).1 v
  -- The segment from `Φ u` to `Φ u'` lies in the product of balls, and is flat.
  have hseg : segment ℝ (Φ u) (Φ u') ⊆ Φ.target :=
    (((convex_ball (0 : F₁) 1).prod (convex_ball (0 : F₂) 1)).segment_subset (huΦ u).2
      (huΦ u').2).trans hVt
  have h := sameLeaf_symm_of_segment_subset (fun y hy v ↦ (hflat y hy v).1) hseg
    (by simp only [← hΨ, huu'])
  simpa [Φ.left_inv (huΦ u).1, Φ.left_inv (huΦ u').1] using h

omit [FiniteDimensional ℝ E] [BoundarylessManifold I M] [FiniteDimensional ℝ F₁]
  [FiniteDimensional ℝ F₂] in
/-- The point `x` can be carried to `y` along the leaves of `𝓕` by a map that is smooth near `x`:
a map `φ`, smooth on a neighbourhood `V` of `x`, with `φ x = y` and each `z ∈ V` on the leaf of
`φ z`. -/
private def Transportable (𝓕 : Foliation I ∞ M k) (x y : M) : Prop :=
  ∃ V ∈ 𝓝 x, ∃ φ : M → M, ContMDiffOn I I ∞ φ V ∧ φ x = y ∧ ∀ z ∈ V, 𝓕.SameLeaf z (φ z)

variable {𝓕 : Foliation I ∞ M k}

omit [FiniteDimensional ℝ E] [BoundarylessManifold I M] [FiniteDimensional ℝ F₁]
  [FiniteDimensional ℝ F₂] in
private theorem transportable_refl (x : M) : Transportable 𝓕 x x :=
  ⟨univ, Filter.univ_mem, id, contMDiffOn_id, rfl, fun z _ ↦ SameLeaf.refl 𝓕 z⟩

omit [FiniteDimensional ℝ E] [BoundarylessManifold I M] [FiniteDimensional ℝ F₁]
  [FiniteDimensional ℝ F₂] in
private theorem Transportable.trans {x y z : M} (hxy : Transportable 𝓕 x y)
    (hyz : Transportable 𝓕 y z) : Transportable 𝓕 x z := by
  obtain ⟨V₁, hV₁, φ₁, hφ₁, rfl, hl₁⟩ := hxy
  obtain ⟨V₂, hV₂, φ₂, hφ₂, rfl, hl₂⟩ := hyz
  have hc : ContinuousAt φ₁ x := (hφ₁.contMDiffAt hV₁).continuousAt
  exact ⟨V₁ ∩ φ₁ ⁻¹' V₂, Filter.inter_mem hV₁ (hc.preimage_mem_nhds hV₂), φ₂ ∘ φ₁,
    hφ₂.comp (hφ₁.mono inter_subset_left) fun _ hz ↦ hz.2, rfl,
    fun z hz ↦ (hl₁ z hz.1).trans (hl₂ _ hz.2)⟩

omit [FiniteDimensional ℝ E] [BoundarylessManifold I M] [FiniteDimensional ℝ F₁]
  [FiniteDimensional ℝ F₂] in
/-- In a flat partial diffeomorphism whose target contains the unit ball, two points of the
preimage of the ball with the same second coordinate can be carried to each other: near `a`,
translate the image by `Φ b - Φ a`. -/
private theorem transportable_of_snd_eq {Φ : PartialDiffeomorph I 𝓘(ℝ, F₁ × F₂) M (F₁ × F₂) ∞}
    (hball : Metric.ball 0 1 ⊆ Φ.target)
    (hflat : ∀ y ∈ Φ.source, ∀ v : TangentSpace I y,
      (mfderiv I 𝓘(ℝ, F₁ × F₂) Φ y v).2 = 0 → v ∈ 𝓕.distribution y)
    {a b : M} (ha : a ∈ Φ.source) (hb : b ∈ Φ.source) (ha' : Φ a ∈ Metric.ball 0 1)
    (hb' : Φ b ∈ Metric.ball 0 1) (h : (Φ a).2 = (Φ b).2) : Transportable 𝓕 a b := by
  set d := Φ b - Φ a
  have hd : d.2 = 0 := by simp [d, h]
  let W : Set (F₁ × F₂) := Metric.ball 0 1 ∩ (· + d) ⁻¹' Metric.ball 0 1
  have hW : IsOpen W :=
    Metric.isOpen_ball.inter (Metric.isOpen_ball.preimage (continuous_id.add continuous_const))
  have hV : IsOpen (Φ.source ∩ Φ ⁻¹' W) :=
    Φ.contMDiffOn.continuousOn.isOpen_inter_preimage Φ.open_source hW
  refine ⟨Φ.source ∩ Φ ⁻¹' W, hV.mem_nhds ⟨ha, ha', by simpa [d] using hb'⟩,
    fun z ↦ Φ.symm (Φ z + d), ?_, by simp [d, Φ.left_inv hb], fun z hz ↦ ?_⟩
  · exact Φ.symm.contMDiffOn.comp ((contDiff_id.add contDiff_const).contMDiff.comp_contMDiffOn
      (Φ.contMDiffOn.mono inter_subset_left)) fun z hz ↦ hball hz.2.2
  · have hseg : segment ℝ (Φ z) (Φ z + d) ⊆ Φ.target :=
      ((convex_ball (0 : F₁ × F₂) 1).segment_subset hz.2.1 hz.2.2).trans hball
    have h := sameLeaf_symm_of_segment_subset hflat hseg (by simp [hd])
    simpa [Φ.left_inv hz.1] using h

/-- Along a curve tangent to `𝓕`, each point can be carried to each nearby point of the curve and
back: in a flat chart around it, the second coordinate is constant along the curve. -/
private theorem eventually_transportable_curve (h₁ : finrank ℝ F₁ = k)
    (h₂ : finrank ℝ E = k + finrank ℝ F₂) {γ : ℝ → M}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc 0 1))
    (htan : ∀ t ∈ Icc (0 : ℝ) 1, curveVelocityWithin I γ (Icc 0 1) t ∈ 𝓕.distribution (γ t))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∀ᶠ s in 𝓝[Icc 0 1] t, Transportable 𝓕 (γ t) (γ s) ∧ Transportable 𝓕 (γ s) (γ t) := by
  have : IsManifold I ∞ M := .of_le (n := ∞ + 1) le_self_add
  obtain ⟨Φ, hx, h0, hball, hflat⟩ :=
    𝓕.isInvolutiveDistribution.exists_flatPartialDiffeomorph 𝓕.isContMDiffDistribution h₁ h₂ (γ t)
  have hO : IsOpen (Φ.source ∩ Φ ⁻¹' Metric.ball 0 1) :=
    Φ.contMDiffOn.continuousOn.isOpen_inter_preimage Φ.open_source Metric.isOpen_ball
  have hγO : γ ⁻¹' (Φ.source ∩ Φ ⁻¹' Metric.ball 0 1) ∈ 𝓝[Icc 0 1] t :=
    (hγ t ht).continuousWithinAt.preimage_mem_nhdsWithin (hO.mem_nhds ⟨hx, by simp [h0]⟩)
  obtain ⟨δ, hδ, hδO⟩ := Metric.mem_nhdsWithin_iff.mp hγO
  set S := Metric.ball t δ ∩ Icc 0 1
  -- On the convex set `S`, the second coordinate of `Φ ∘ γ` has derivative `0`.
  have hderiv (r : ℝ) (hr : r ∈ S) :
      HasDerivWithinAt (fun s ↦ (Φ (γ s)).2) 0 S r := by
    have hγr : γ r ∈ Φ.source := (hδO hr).1
    have hΦ := Φ.mdifferentiableAt (by simp) hγr
    have hγr' := (hγ r hr.2).mdifferentiableWithinAt one_ne_zero
    have hg : DifferentiableWithinAt ℝ (Φ ∘ γ) (Icc 0 1) r :=
      mdifferentiableWithinAt_iff_differentiableWithinAt.mp
        (hΦ.comp_mdifferentiableWithinAt r hγr')
    have hv : (derivWithin (Φ ∘ γ) (Icc 0 1) r).2 = 0 := by
      rw [← curveVelocityWithin_eq_derivWithin,
        curveVelocityWithin_map hΦ (uniqueDiffOn_Icc zero_lt_one r hr.2) hγr']
      exact (hflat _ hγr _).2 (htan r hr.2)
    have := ((ContinuousLinearMap.snd ℝ F₁ F₂).hasFDerivAt.comp_hasDerivWithinAt r
      hg.hasDerivWithinAt).mono (inter_subset_right : S ⊆ Icc 0 1)
    convert this using 1
    · simp [Function.comp_def]
    · simp [hv]
  have hconst (s : ℝ) (hs : s ∈ S) : (Φ (γ s)).2 = (Φ (γ t)).2 := by
    exact ((convex_ball t δ).inter (convex_Icc 0 1)).isPreconnected.eq_of_hasDerivWithinAt_zero
      hderiv hs ⟨Metric.mem_ball_self hδ, ht⟩
  filter_upwards [inter_mem_nhdsWithin _ (Metric.ball_mem_nhds t hδ)] with s hs
  have hs' : s ∈ S := ⟨hs.2, hs.1⟩
  have hst := hconst s hs'
  have h0' : Φ (γ t) ∈ Metric.ball 0 1 := by simp [h0]
  have hflat' := fun y hy v ↦ (hflat y hy v).1
  exact ⟨transportable_of_snd_eq hball hflat' hx (hδO hs').1 h0' (hδO hs').2 hst.symm,
    transportable_of_snd_eq hball hflat' (hδO hs').1 hx (hδO hs').2 h0' hst⟩

/-- The ends of a curve tangent to `𝓕` can be carried to each other, by connectedness of
`[0, 1]`. -/
private theorem JoinedByTangentCurve.transportable (h₁ : finrank ℝ F₁ = k)
    (h₂ : finrank ℝ E = k + finrank ℝ F₂) {x y : M} (h : 𝓕.JoinedByTangentCurve x y) :
    Transportable 𝓕 x y ∧ Transportable 𝓕 y x := by
  obtain ⟨γ, hγ, htan, rfl, rfl⟩ := joinedByTangentCurve_iff.mp h
  have key {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
      Transportable 𝓕 (γ s) (γ t) :=
    isPreconnected_Icc.induction₂' (fun s t ↦ Transportable 𝓕 (γ s) (γ t))
      (fun _ hr ↦ eventually_transportable_curve h₁ h₂ hγ htan hr)
      (fun _ _ _ _ _ _ h h' ↦ h.trans h') hs ht
  exact ⟨key (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one),
    key (right_mem_Icc.2 zero_le_one) (left_mem_Icc.2 zero_le_one)⟩

/-- **Transport along a leaf.** If `x` and `y` lie on the same leaf of a smooth foliation `𝓕` of a
boundaryless manifold, there are a neighbourhood `V` of `x` and a map `φ : M → M`, smooth on `V`,
with `φ x = y` and such that every `z ∈ V` lies on the same leaf as `φ z`. -/
theorem SameLeaf.exists_transport {x y : M} (h : 𝓕.SameLeaf x y) :
    ∃ V ∈ 𝓝 x, ∃ φ : M → M, ContMDiffOn I I ∞ φ V ∧ φ x = y ∧ ∀ z ∈ V, 𝓕.SameLeaf z (φ z) := by
  have hk : k ≤ finrank ℝ E := 𝓕.finrank_distribution x ▸ Submodule.finrank_le _
  refine (sameLeaf_le (r := fun a b ↦ Transportable 𝓕 a b ∧ Transportable 𝓕 b a)
    ⟨fun a ↦ ⟨transportable_refl a, transportable_refl a⟩, fun h ↦ h.symm,
      fun h h' ↦ ⟨h.1.trans h'.1, h'.2.trans h.2⟩⟩
    (fun a b hab ↦ hab.transportable (F₁ := Fin k → ℝ) (F₂ := Fin (finrank ℝ E - k) → ℝ)
      (Module.finrank_fin_fun ℝ) (by rw [Module.finrank_fin_fun]; omega)) x y h).1

variable (𝓕) in
/-- **Saturations of open sets are open.** The union of the leaves of a smooth foliation of a
boundaryless manifold through the points of an open set is open. -/
theorem isOpen_saturation {s : Set M} (hs : IsOpen s) : IsOpen (⋃ x ∈ s, 𝓕.leaf x) := by
  refine isOpen_iff_mem_nhds.2 fun y hy ↦ ?_
  obtain ⟨x, hx, hxy⟩ := mem_iUnion₂.1 hy
  obtain ⟨V, hV, φ, hφ, rfl, hl⟩ := (mem_leaf.1 hxy).symm.exists_transport
  filter_upwards [hV, (hφ.contMDiffAt hV).continuousAt.preimage_mem_nhds (hs.mem_nhds hx)]
    with z hz hz'
  exact mem_iUnion₂.2 ⟨φ z, hz', mem_leaf.2 (hl z hz).symm⟩

end Foliation

end TauCeti

end
