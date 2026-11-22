/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.TubularNeighborhood.MFDeriv
public import SymplecticGeometry.Geometry.Symplectic.Moser.Relative
public import TauCeti.Geometry.Symplectic.SymplecticTransport
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Opens
import SymplecticGeometry.Geometry.Symplectic.Manifold.TwoForm
import TauCeti.Geometry.Manifold.DifferentialForm.Opens
import TauCeti.Geometry.Manifold.SmoothEmbedding.LocalDiffeomorph
import TauCeti.Geometry.Symplectic.Manifold.Opens

/-!
# Symplectomorphisms of neighbourhoods with a prescribed derivative

Let `f₀ : Q → M₀` and `f₁ : Q → M₁` be smooth embeddings of the same manifold into symplectic
manifolds `(M₀, ω₀)` and `(M₁, ω₁)`, and let `A q : T_{f₀ q} M₀ ≃ T_{f₁ q} M₁` be a smooth family
of linear symplectomorphisms with `A q ∘ df₀ q = df₁ q`. Then
`TauCeti.SmoothEmbedding.exists_symplectomorphism_opens_mfderiv_eq` gives open neighbourhoods
`U₀` of `f₀ (Q)` and `U₁` of `f₁ (Q)` and a diffeomorphism `ψ : U₀ ≃ U₁` with `ψ ∘ f₀ = f₁`,
`dψ (f₀ q) = A q` and `ψ^* ω₁ = ω₀`. Neither compactness of `Q` nor closedness of the images is
assumed.

This is the common step of the neighbourhood theorems of McDuff–Salamon, §3.4
([McDuffSalamon2017], proofs of Theorems 3.4.10 and 3.4.13), with the conclusion on the first
derivative that the errata [McDuffSalamon2019Errata] add to the relative Moser lemma.

## Proof

`TauCeti.SmoothEmbedding.exists_diffeomorph_opens_mfderiv_eq` gives a diffeomorphism
`ψ' : U₀ ≃ U₁` with `ψ' ∘ f₀ = f₁` and derivative `A q` at `f₀ q`. Since each `A q` is
symplectic, `ψ'^* ω₁` and `ω₀` agree on the whole tangent space of `U₀` at each point `f₀ q`
(`TauCeti.SmoothTwoForm.coe_mpullback_apply_eq_of_mfderiv_eq`).
The relative Moser theorem `TauCeti.SmoothEmbedding.exists_diffeomorph_opens_of_eq_along`,
applied on `U₀` along `f₀` with image restricted to `U₀`, gives a diffeomorphism `χ` between
open subsets of `U₀` that pulls `ψ'^* ω₁` back to `ω₀`, fixes `f₀ (Q)` and has derivative the
identity there. Then `ψ = ψ' ∘ χ`, read as a diffeomorphism between open subsets of `M₀` and
`M₁`, and `PartialDiffeomorph.mpullback_toDiffeomorphSourceTarget_liftOpens` turns the
equality of forms on the source of `ψ' ∘ χ` into the equality of restricted forms for `ψ`.

## Main results

* `TauCeti.SmoothEmbedding.exists_symplectomorphism_opens_mfderiv_eq`: the symplectomorphism of
  open neighbourhoods with prescribed derivative along the embedded manifold.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §3.4.
* [D. McDuff and D. Salamon, *Errata*][McDuffSalamon2019Errata]
-/

public section

open Bundle Manifold TopologicalSpace
open scoped ContDiff Manifold Bundle

namespace TauCeti.SmoothEmbedding

variable {EQ E₀ E₁ HQ H₀ H₁ Q M₀ M₁ : Type*}
  [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] [FiniteDimensional ℝ EQ]
  [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  [TopologicalSpace HQ] [TopologicalSpace H₀] [TopologicalSpace H₁]
  {J : ModelWithCorners ℝ EQ HQ} {I₀ : ModelWithCorners ℝ E₀ H₀}
  {I₁ : ModelWithCorners ℝ E₁ H₁}
  [J.Boundaryless] [I₀.Boundaryless] [I₁.Boundaryless]
  [TopologicalSpace Q] [ChartedSpace HQ Q] [IsManifold J ∞ Q]
  [TopologicalSpace M₀] [ChartedSpace H₀ M₀] [IsManifold I₀ ∞ M₀] [T2Space M₀]
  [TopologicalSpace M₁] [ChartedSpace H₁ M₁] [IsManifold I₁ ∞ M₁] [T2Space M₁]

/-- **Symplectomorphisms of neighbourhoods with a prescribed derivative.** Let `f₀ : Q → M₀` and
`f₁ : Q → M₁` be smooth embeddings into second countable Hausdorff manifolds without boundary,
with symplectic forms `ω₀` and `ω₁`, and let `A q : T_{f₀ q} M₀ ≃L[ℝ] T_{f₁ q} M₁` be linear
symplectomorphisms forming a smooth section over `Q` of the bundle of linear maps between the
pull-backs `f₀ *ᵖ TM₀` and `f₁ *ᵖ TM₁`, with `A q (df₀ q v) = df₁ q v`. Then there are open sets
`U₀ ⊆ M₀` and `U₁ ⊆ M₁` and a diffeomorphism `ψ : U₀ ≃ U₁` such that, for every `q`,
`f₀ q ∈ U₀`, `ψ (f₀ q) = f₁ q` and the derivative of `ψ` at `f₀ q` is `A q`, and `ψ` pulls the
restriction of `ω₁` to `U₁` back to the restriction of `ω₀` to `U₀`. Neither compactness of `Q`
nor closedness of the images is assumed. -/
theorem exists_symplectomorphism_opens_mfderiv_eq [SecondCountableTopology M₀]
    [SecondCountableTopology M₁]
    (f₀ : SmoothEmbedding J I₀ ∞ Q M₀) (f₁ : SmoothEmbedding J I₁ ∞ Q M₁)
    {ω₀ : SmoothTwoForm I₀ M₀} {ω₁ : SmoothTwoForm I₁ M₁}
    (hω₀ : ω₀.IsSymplectic) (hω₁ : ω₁.IsSymplectic)
    (A : ∀ q, TangentSpace I₀ (f₀ q) ≃L[ℝ] TangentSpace I₁ (f₁ q))
    (hA : ContMDiff J (J.prod 𝓘(ℝ, E₀ →L[ℝ] E₁)) ∞ (fun q ↦ TotalSpace.mk' (E₀ →L[ℝ] E₁)
      (E := fun q ↦ ((f₀ : Q → M₀) *ᵖ (TangentSpace I₀)) q →L[ℝ]
        ((f₁ : Q → M₁) *ᵖ (TangentSpace I₁)) q) q
        (A q : TangentSpace I₀ (f₀ q) →L[ℝ] TangentSpace I₁ (f₁ q))))
    (hAf : ∀ q v, A q (mfderiv J I₀ f₀ q v) = mfderiv J I₁ f₁ q v)
    (hAω : ∀ q, (hω₀.isNondegenerate.symplecticFormAt (f₀ q)).IsSymplectomorphism
      (hω₁.isNondegenerate.symplecticFormAt (f₁ q)) (A q).toLinearEquiv) :
    ∃ (U₀ : Opens M₀) (U₁ : Opens M₁) (ψ : U₀ ≃ₘ⟮I₀, I₁⟯ U₁),
      (∀ q, ∃ h : f₀ q ∈ U₀, (ψ ⟨f₀ q, h⟩ : M₁) = f₁ q ∧
        mfderiv I₀ I₁ ψ ⟨f₀ q, h⟩ =
          (A q : TangentSpace I₀ (f₀ q) →L[ℝ] TangentSpace I₁ (f₁ q))) ∧
      SmoothForm.mpullback ψ ψ.contMDiff
          (SmoothForm.mpullback (Subtype.val : U₁ → M₁) contMDiff_subtypeVal ω₁) =
        SmoothForm.mpullback (Subtype.val : U₀ → M₀) contMDiff_subtypeVal ω₀ := by
  obtain ⟨U₀, U₁, ψ', hψ'⟩ := exists_diffeomorph_opens_mfderiv_eq f₀ f₁ A hA hAf
  choose hfU hψ'f hψ'd using hψ'
  -- The forms `ω₀` and `ψ'^* ω₁` on `U₀`, and `f₀` as an embedding into `U₀`.
  set σ₀ := SmoothForm.mpullback (Subtype.val : U₀ → M₀) contMDiff_subtypeVal ω₀
  set σ₁ := SmoothForm.mpullback ψ' ψ'.contMDiff
    (SmoothForm.mpullback (Subtype.val : U₁ → M₁) contMDiff_subtypeVal ω₁)
  set g := f₀.codRestrict U₀ hfU
  have hg (q : Q) : g q = ⟨f₀ q, hfU q⟩ := Subtype.ext (f₀.val_codRestrict_apply U₀ hfU q)
  -- Since `A q` is symplectic, the two forms agree at `f₀ q`.
  have heq (q : Q) : σ₁.val (g q) = σ₀.val (g q) := by
    rw [hg q]
    exact SmoothTwoForm.coe_mpullback_apply_eq_of_mfderiv_eq ψ'.contMDiff _ _ (A q)
      (hω₀.isNondegenerate.isSymplectomorphism_mpullback_subtype_val hω₁.isNondegenerate
        (hψ'f q) (A q) (hAω q)) rfl (hψ'd q)
  obtain ⟨V₀, V₁, χ, hχf, hχ⟩ := g.exists_diffeomorph_opens_of_eq_along
    (hω₀.isClosed.mpullback _ _) ((hω₁.isClosed.mpullback _ _).mpullback _ _)
    (fun q ↦ (SmoothTwoForm.nondegenerate_bilinFormAt_mpullback_subtype_val_iff _).2
      (hω₀.isNondegenerate.nondegenerate_bilinFormAt _)) heq
  choose hgV hχfix hχd using hχf
  rcases isEmpty_or_nonempty Q with hQ | ⟨⟨q₀⟩⟩
  · -- Without points to work along, the empty open sets will do.
    obtain ⟨ψ, hψ⟩ := SmoothTwoForm.exists_diffeomorph_bot_mpullback_eq ω₀ ω₁
    exact ⟨⊥, ⊥, ψ, fun q ↦ (hQ.false q).elim, hψ⟩
  have hU₀ : Nonempty U₀ := ⟨g q₀⟩
  have hU₁ : Nonempty U₁ := ⟨ψ' (g q₀)⟩
  have hV₀ : Nonempty V₀ := ⟨⟨g q₀, hgV q₀⟩⟩
  have hV₁ : Nonempty V₁ := ⟨χ ⟨g q₀, hgV q₀⟩⟩
  -- `ψ = ψ' ∘ χ`, first as a partial diffeomorphism of `U₀` into `U₁`, then read in `M₀` and `M₁`,
  -- and finally as a diffeomorphism between the source and the target.
  let χ' : PartialDiffeomorph I₀ I₀ U₀ U₀ ∞ := χ.toPartialDiffeomorph.liftOpens hV₀ hV₁
  let Θ' : PartialDiffeomorph I₀ I₁ U₀ U₁ ∞ := χ'.trans ψ'.toPartialDiffeomorph
  let Θ : PartialDiffeomorph I₀ I₁ M₀ M₁ ∞ := Θ'.liftOpens hU₀ hU₁
  let ψ := Θ.toDiffeomorphSourceTarget
  have hχχ' : Subtype.val ∘ ⇑χ = ⇑χ' ∘ Subtype.val :=
    funext fun w ↦ by simp [χ']
  have hΘ' : ⇑Θ' = ⇑ψ' ∘ ⇑χ' := by simp [Θ']
  have hΘΘ' : Subtype.val ∘ ⇑Θ' = ⇑Θ ∘ Subtype.val :=
    funext fun y ↦ (Θ'.liftOpens_apply_coe hU₀ hU₁ y).symm
  have hψΘ : Subtype.val ∘ ⇑ψ = ⇑Θ ∘ Subtype.val := funext Θ.toDiffeomorphSourceTarget_apply_coe
  have hχ'source (w : V₀) : (w : U₀) ∈ χ'.source := by
    rw [PartialDiffeomorph.liftOpens_source]
    exact ⟨w, by simp, rfl⟩
  have hΘ'source {y : U₀} (hy : y ∈ χ'.source) : y ∈ Θ'.source := by
    simp [Θ', hy]
  -- At the points of `f₀ (Q)`, `χ'` is the identity, with identity derivative.
  have hχ'fix (q : Q) : χ' (g q) = g q :=
    (congrFun hχχ' ⟨g q, hgV q⟩).symm.trans (hχfix q)
  have hχ'd (q : Q) : mfderiv I₀ I₀ χ' (g q) = ContinuousLinearMap.id ℝ _ :=
    (Manifold.mfderiv_eq_id_iff_of_comp_subtype_val hχχ').1 (hχd q)
  have hgΘ (q : Q) : f₀ q ∈ Θ.source := by
    rw [PartialDiffeomorph.liftOpens_source]
    exact ⟨g q, hΘ'source (hχ'source ⟨g q, hgV q⟩), f₀.val_codRestrict_apply U₀ hfU q⟩
  refine ⟨_, _, ψ, fun q ↦ ⟨hgΘ q, ?_, ?_⟩, ?_⟩
  · -- `ψ (f₀ q) = ψ' (χ' (f₀ q)) = ψ' (f₀ q) = f₁ q`.
    have h := congrFun hΘΘ' (g q)
    rw [Function.comp_apply, Function.comp_apply, f₀.val_codRestrict_apply U₀ hfU q] at h
    rw [Θ.toDiffeomorphSourceTarget_apply_coe, ← h, hΘ', Function.comp_apply, hχ'fix, hg q,
      hψ'f q]
  · -- The derivative of `ψ` at `f₀ q` is that of `ψ' ∘ χ'`, that is, of `ψ'`.
    have hfix := hχ'fix q
    have hd := hχ'd q
    have hs : (⟨f₀ q, hfU q⟩ : U₀) ∈ χ'.source := by
      rw [← hg q]
      exact hχ'source ⟨g q, hgV q⟩
    rw [hg q] at hfix hd
    refine ContinuousLinearMap.ext fun v ↦ ?_
    have h₁ : mfderiv I₀ I₁ ψ ⟨f₀ q, hgΘ q⟩ v = mfderiv I₀ I₁ Θ (f₀ q) v := by
      rw [← Manifold.mfderiv_subtype_val_comp_apply, hψΘ, Manifold.mfderiv_comp_subtype_val_apply]
    -- The vector `v` is tangent to the source of `Θ`; read it as tangent to `U₀`.
    have h₂ (u : TangentSpace I₀ (⟨f₀ q, hfU q⟩ : U₀)) :
        mfderiv I₀ I₁ Θ' ⟨f₀ q, hfU q⟩ u = mfderiv I₀ I₁ Θ (f₀ q) u := by
      rw [← Manifold.mfderiv_subtype_val_comp_apply, hΘΘ', Manifold.mfderiv_comp_subtype_val_apply]
    have hdu (u : TangentSpace I₀ (⟨f₀ q, hfU q⟩ : U₀)) : mfderiv I₀ I₀ χ' ⟨f₀ q, hfU q⟩ u = u := by
      rw [hd]
      exact ContinuousLinearMap.id_apply u
    have h₃ : mfderiv I₀ I₁ Θ' ⟨f₀ q, hfU q⟩ =
        (A q : TangentSpace I₀ (f₀ q) →L[ℝ] TangentSpace I₁ (f₁ q)) := by
      refine ContinuousLinearMap.ext fun u ↦ ?_
      rw [hΘ', mfderiv_comp_apply _ (ψ'.contMDiff.mdifferentiableAt (by simp))
        (χ'.mdifferentiableAt (by simp) hs), hdu, hfix, hψ'd q]
      -- The two sides differ only in the base points of the tangent spaces, which are `E₁`.
      rfl
    rw [h₁, ← h₂ v, h₃]
    rfl
  · -- At a point `y` of the source of `Θ'`, `Θ'^* ω₁` is `χ^* ψ'^* ω₁` at the point of `V₀`
    -- that `y` is.
    refine Θ'.mpullback_toDiffeomorphSourceTarget_liftOpens hU₀ hU₁ fun y hy ↦ ?_
    have hyχ : y ∈ χ'.source := by simpa [Θ'] using hy
    obtain ⟨w, -, hwy⟩ : y ∈ Subtype.val '' χ.toPartialDiffeomorph.source :=
      χ.toPartialDiffeomorph.liftOpens_source hV₀ hV₁ ▸ hyχ
    have h := congrFun (congrArg Subtype.val hχ) w
    rw [SmoothForm.coe_mpullback_subtype_val_apply, SmoothForm.coe_mpullback_subtype_val_apply] at h
    rw [hΘ', mpullback_comp_at (χ'.mdifferentiableAt (by simp) hyχ)
        (ψ'.contMDiff.mdifferentiableAt (by simp)), ← hwy,
      mpullback_liftOpens_apply_coe χ.toPartialDiffeomorph (by simp) hV₀ hV₁ _ (by simp)]
    have hc : ⇑χ.toPartialDiffeomorph = ⇑χ := by
      simp only [Diffeomorph.toPartialDiffeomorph_toPartialEquiv, Equiv.toPartialEquiv_apply,
        Diffeomorph.coe_toEquiv]
    simp only [SmoothForm.coe_mpullback] at h
    rw [hc]
    exact h

end TauCeti.SmoothEmbedding

end
