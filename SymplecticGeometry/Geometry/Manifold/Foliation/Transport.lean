/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Foliation.Leaf
import SymplecticGeometry.Geometry.Manifold.Distribution.FlatChart
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.OpenSubset
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
`TauCeti.Foliation.sameLeaf_of_contMDiffOn_of_tangent` puts them on one leaf.

## Main results

* `TauCeti.Foliation.exists_foliatedChart`: a foliated chart of `𝓕` around any point, onto the
  product of the unit balls of `F₁` and `F₂`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 19
  (foliations and flat charts)
* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §5.4
-/

public section

noncomputable section

open Set Function Manifold Module TopologicalSpace TauCeti.Manifold
open scoped Manifold ContDiff

namespace TauCeti

namespace Foliation

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I (∞ + 1) M] [BoundarylessManifold I M] {k : ℕ}
  {F₁ F₂ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]

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
  -- The preimage `γ` of the segment from `Φ u` to `Φ u'` is a curve tangent to `𝓕`.
  set p := Φ u
  set q := Φ u'
  have hpq : (q - p).2 = 0 := by
    simp only [Prod.snd_sub, p, q, ← hΨ, huu', sub_self]
  let ℓ : ℝ → F₁ × F₂ := fun t ↦ p + t • (q - p)
  have hℓ : MapsTo ℓ (Icc 0 1) Φ.target := fun t ht ↦
    hVt (((convex_ball (0 : F₁) 1).prod (convex_ball (0 : F₂) 1)).add_smul_sub_mem
      (huΦ u).2 (huΦ u').2 ht)
  let γ : ℝ → M := Φ.symm ∘ ℓ
  have hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc 0 1) :=
    (Φ.symm.contMDiffOn.comp
      (contDiff_const.add (contDiff_id.smul contDiff_const)).contMDiff.contMDiffOn hℓ).of_le
      (by simp)
  have htan (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      curveVelocityWithin I γ (Icc 0 1) t ∈ 𝓕.distribution (γ t) := by
    have hγt : γ t ∈ Φ.source := Φ.map_target (hℓ ht)
    have hU' : UniqueDiffWithinAt ℝ (Icc (0 : ℝ) 1) t := uniqueDiffOn_Icc zero_lt_one t ht
    rw [← hflat _ hγt, ← curveVelocityWithin_map (Φ.mdifferentiableAt (by simp) hγt) hU'
      ((hγ t ht).mdifferentiableWithinAt one_ne_zero), curveVelocityWithin_eq_derivWithin,
      derivWithin_congr (f₁ := Φ ∘ γ) (f := ℓ) (fun s hs ↦ Φ.right_inv (hℓ hs))
        (Φ.right_inv (hℓ ht))]
    have hd : HasDerivWithinAt ℓ (q - p) (Icc 0 1) t := by
      simpa only [id, one_smul] using
        (((hasDerivAt_id t).smul_const (q - p)).const_add p).hasDerivWithinAt
    rw [hd.derivWithin hU']
    exact hpq
  have h01 := sameLeaf_of_contMDiffOn_of_tangent hγ htan (left_mem_Icc.2 zero_le_one)
    (right_mem_Icc.2 zero_le_one)
  simpa [γ, ℓ, p, q, Φ.left_inv (huΦ u).1, Φ.left_inv (huΦ u').1] using h01

end Foliation

end TauCeti

end
