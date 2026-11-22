/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.TubularNeighborhood.MFDeriv
public import SymplecticGeometry.Geometry.Symplectic.Moser.Relative
public import TauCeti.Geometry.Symplectic.SymplecticTransport
import SymplecticGeometry.Geometry.Manifold.Diffeomorph.Basic
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
symplectic, `ψ'^* ω₁` and `ω₀` agree on the whole tangent space of `U₀` at each point `f₀ q`.
The relative Moser theorem `TauCeti.SmoothEmbedding.exists_diffeomorph_opens_of_eq_along`,
applied on `U₀` along `f₀` with image restricted to `U₀`, gives a diffeomorphism `χ` between
open subsets of `U₀` that pulls `ψ'^* ω₁` back to `ω₀`, fixes `f₀ (Q)` and has derivative the
identity there. Then `ψ = ψ' ∘ χ`, read as a diffeomorphism between open subsets of `M₀` and
`M₁`. The reading of partial diffeomorphisms between open subsets in the ambient manifolds
follows the proof of `TauCeti.SmoothEmbedding.exists_diffeomorph_opens_of_eq_along`.

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

omit [FiniteDimensional ℝ E₀] [FiniteDimensional ℝ E₁] [I₀.Boundaryless] [I₁.Boundaryless]
  [T2Space M₀] [T2Space M₁] in
/-- A diffeomorphism `ψ` of open subsets whose derivative at `x₀` is a linear symplectomorphism
`T_{x₀} M₀ ≃ T_{x₁} M₁`, with `ψ x₀ = x₁`, pulls `ω₁` back to `ω₀` on the whole tangent space at
`x₀`. -/
private theorem mpullback_val_eq_of_mfderiv_eq {U₀ : Opens M₀} {U₁ : Opens M₁}
    (ψ : U₀ ≃ₘ⟮I₀, I₁⟯ U₁) {ω₀ : SmoothTwoForm I₀ M₀} {ω₁ : SmoothTwoForm I₁ M₁}
    (hω₀ : ω₀.IsNondegenerate) (hω₁ : ω₁.IsNondegenerate) {x₀ : M₀} {x₁ : M₁}
    (A : TangentSpace I₀ x₀ ≃L[ℝ] TangentSpace I₁ x₁)
    (hA : (hω₀.symplecticFormAt x₀).IsSymplectomorphism (hω₁.symplecticFormAt x₁) A.toLinearEquiv)
    (hx : x₀ ∈ U₀) (hψx : (ψ ⟨x₀, hx⟩ : M₁) = x₁)
    (hψA : mfderiv I₀ I₁ ψ ⟨x₀, hx⟩ = (A : TangentSpace I₀ x₀ →L[ℝ] TangentSpace I₁ x₁)) :
    (SmoothForm.mpullback ψ ψ.contMDiff
        (SmoothForm.mpullback (Subtype.val : U₁ → M₁) contMDiff_subtypeVal ω₁)).val ⟨x₀, hx⟩ =
      (SmoothForm.mpullback (Subtype.val : U₀ → M₀) contMDiff_subtypeVal ω₀).val ⟨x₀, hx⟩ := by
  have h (v w : TangentSpace I₀ x₀) :
      SmoothBundleForm.eval₂ ω₁ x₁ (A v) (A w) = SmoothBundleForm.eval₂ ω₀ x₀ v w := by
    simpa only [SmoothTwoForm.IsNondegenerate.symplecticFormAt_apply,
      ContinuousLinearEquiv.coe_toLinearEquiv] using hA.apply v w
  refine SmoothBundleForm.apply_eq_of_eval₂_eq fun v w ↦ ?_
  rw [SmoothForm.eval₂_mpullback, SmoothForm.eval₂_mpullback, SmoothForm.eval₂_mpullback, hψA]
  simp only [Manifold.mfderiv_subtype_val, ContinuousLinearEquiv.coe_coe,
    Manifold.tangentSpaceOpenEquiv_apply]
  rw [hψx, Manifold.tangentSpaceOpenEquiv_apply, Manifold.tangentSpaceOpenEquiv_apply]
  exact h v w

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
    exact mpullback_val_eq_of_mfderiv_eq ψ' hω₀.isNondegenerate hω₁.isNondegenerate (A q) (hAω q)
      (hfU q) (hψ'f q) (hψ'd q)
  obtain ⟨V₀, V₁, χ, hχf, hχ⟩ := g.exists_diffeomorph_opens_of_eq_along
    (hω₀.isClosed.mpullback _ _) ((hω₁.isClosed.mpullback _ _).mpullback _ _)
    (fun q ↦ (SmoothTwoForm.nondegenerate_bilinFormAt_mpullback_subtype_val_iff _).2
      (hω₀.isNondegenerate.nondegenerate_bilinFormAt _)) heq
  choose hgV hχfix hχd using hχf
  rcases isEmpty_or_nonempty Q with hQ | ⟨⟨q₀⟩⟩
  · -- Without points to work along, the empty open sets will do.
    have : IsEmpty (⊥ : Opens M₀) := ⟨fun x ↦ x.property⟩
    have : IsEmpty (⊥ : Opens M₁) := ⟨fun x ↦ x.property⟩
    exact ⟨⊥, ⊥, Diffeomorph.ofIsEmpty, fun q ↦ (hQ.false q).elim,
      Subtype.ext (funext fun x ↦ (IsEmpty.false x).elim)⟩
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
  · -- At a point `z` of the source, `ψ^* ω₁` is `χ^* ψ'^* ω₁` at the point of `V₀` that `z` is.
    apply Subtype.ext
    funext z
    obtain ⟨y, hy, hyz⟩ : (z : M₀) ∈ Subtype.val '' Θ'.source :=
      Θ'.liftOpens_source hU₀ hU₁ ▸ z.property
    have hyχ : y ∈ χ'.source := by simpa [Θ'] using hy
    obtain ⟨w, -, hwy⟩ : y ∈ Subtype.val '' χ.toPartialDiffeomorph.source :=
      χ.toPartialDiffeomorph.liftOpens_source hV₀ hV₁ ▸ hyχ
    have hψz : MDifferentiableAt I₀ I₁ ψ z := ψ.contMDiff.mdifferentiableAt (by simp)
    have hΘz : MDifferentiableAt I₀ I₁ Θ z := Θ.mdifferentiableAt (by simp) z.property
    have hval {U : Opens M₁} (x : U) : MDifferentiableAt I₁ I₁ (Subtype.val : U → M₁) x :=
      (contMDiff_subtypeVal (n := 1)).mdifferentiableAt one_ne_zero
    have h := congrFun (congrArg Subtype.val hχ) w
    rw [SmoothForm.coe_mpullback_subtype_val_apply, SmoothForm.coe_mpullback_subtype_val_apply] at h
    rw [SmoothForm.coe_mpullback_subtype_val_apply ω₀ z, SmoothForm.coe_mpullback,
      SmoothForm.coe_mpullback, ← mpullback_comp_at hψz (hval _), hψΘ,
      mpullback_comp_at (contMDiff_subtypeVal.mdifferentiableAt one_ne_zero) hΘz,
      TauCeti.mpullback_subtype_val_apply, ← hyz,
      mpullback_liftOpens_apply_coe Θ' (by simp) hU₀ hU₁ _ hy, hΘ',
      mpullback_comp_at (χ'.mdifferentiableAt (by simp) hyχ)
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
