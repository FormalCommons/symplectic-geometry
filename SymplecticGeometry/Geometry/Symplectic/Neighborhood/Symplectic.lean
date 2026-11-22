/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Neighborhood.Basic
public import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.Diffeomorph
public import TauCeti.Geometry.Symplectic.Lagrangian.Embedding.Symplectic.Normal
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Opens
import SymplecticGeometry.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Geometry.Manifold.VectorBundle.Pullback

/-!
# Neighbourhoods of symplectic submanifolds

Let `f₀ : Q₀ → M₀` and `f₁ : Q₁ → M₁` be smooth embeddings with symplectic tangent images into
symplectic manifolds `(M₀, σ₀)` and `(M₁, σ₁)`, let `φ : Q₀ → Q₁` be a diffeomorphism with
`φ^* (f₁^* σ₁) = f₀^* σ₀`, and let `Φ` be an isomorphism of the normal bundles of `f₀` and of
`f₁`, covering `φ`, smooth on total spaces and preserving Tau Ceti's normal symplectic forms
`TauCeti.SmoothEmbedding.symplecticNormalForm`. Then a neighbourhood of `f₀ (Q₀)` is
symplectomorphic to a neighbourhood of `f₁ (Q₁)` by a map `ψ` with `ψ ∘ f₀ = f₁ ∘ φ` whose
derivative carries the symplectic complement of each tangent space of `f₀` to that of `f₁` as `Φ`
does. This is
`TauCeti.SmoothTwoForm.IsNondegenerate.HasSymplecticTangentImages.exists_symplectomorphism_opens`.
The two submanifolds may be modelled on different spaces.

The normal bundle of a symplectic submanifold is identified with the symplectic complements of
its tangent spaces by Tau Ceti's symplectic representatives
`TauCeti.SmoothEmbedding.symplecticNormalRepresentative`, so the condition on `dψ` is stated with
them. Neither compactness of the submanifolds nor closedness of their images is needed.

## Proof

The comparison theorem `TauCeti.SmoothEmbedding.exists_symplectomorphism_opens_of_mpullback_eq` is
applied to `f₀` and `f₁ ∘ φ`, an embedding on the model of `Q₀` by
`TauCeti.SmoothEmbedding.compDiffeomorphOfBoundaryless`. Their restricted forms agree and are
nondegenerate, so of constant rank. The comparison theorem is applied with
`L q = rep₁ ∘ Φ q ∘ [·]` at each `q`: the normal class of a vector, carried by `Φ` and
represented in the symplectic complement. It is smooth by
`TauCeti.SmoothEmbedding.contMDiff_symplecticNormalRepresentative` and preserves the forms on the
symplectic complements since `Φ` does. The comparison theorem gives `dψ v - L q v` tangent to
`f₁ ∘ φ` for `v` in the symplectic complement of the tangent space of `f₀`. That difference is also
in the symplectic complement of the tangent space of `f₁`, as `dψ` is a linear symplectomorphism
carrying the tangent space of `f₀` onto that of `f₁ ∘ φ`. The tangent space of `f₁` being
symplectic, the difference vanishes.

## Main results

* `TauCeti.SmoothTwoForm.IsNondegenerate.HasSymplecticTangentImages.exists_symplectomorphism_opens`:
  the symplectic neighbourhood theorem.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Theorem 3.4.10, and the remarks on non-compact submanifolds on p. 124.
-/

public section

open Bundle Manifold Module TopologicalSpace
open scoped ContDiff Manifold Bundle

namespace TauCeti.SmoothTwoForm.IsNondegenerate

variable {EQ₀ EQ₁ E₀ E₁ P₀ P₁ HQ₀ HQ₁ H₀ H₁ Q₀ Q₁ M₀ M₁ : Type*}
  [NormedAddCommGroup EQ₀] [NormedSpace ℝ EQ₀] [FiniteDimensional ℝ EQ₀]
  [NormedAddCommGroup EQ₁] [NormedSpace ℝ EQ₁] [FiniteDimensional ℝ EQ₁]
  [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  [NormedAddCommGroup P₀] [NormedSpace ℝ P₀] [FiniteDimensional ℝ P₀]
  [NormedAddCommGroup P₁] [NormedSpace ℝ P₁] [FiniteDimensional ℝ P₁]
  [TopologicalSpace HQ₀] [TopologicalSpace HQ₁] [TopologicalSpace H₀] [TopologicalSpace H₁]
  {J₀ : ModelWithCorners ℝ EQ₀ HQ₀} {J₁ : ModelWithCorners ℝ EQ₁ HQ₁}
  {I₀ : ModelWithCorners ℝ E₀ H₀} {I₁ : ModelWithCorners ℝ E₁ H₁}
  [J₀.Boundaryless] [I₁.Boundaryless]
  [TopologicalSpace Q₀] [ChartedSpace HQ₀ Q₀] [IsManifold J₀ ∞ Q₀]
  [TopologicalSpace Q₁] [ChartedSpace HQ₁ Q₁] [IsManifold J₁ ∞ Q₁]
  [TopologicalSpace M₀] [ChartedSpace H₀ M₀] [IsManifold I₀ ∞ M₀]
  [TopologicalSpace M₁] [ChartedSpace H₁ M₁] [IsManifold I₁ ∞ M₁]
  {σ₀ : SmoothTwoForm I₀ M₀} {σ₁ : SmoothTwoForm I₁ M₁}
  {f₀ : SmoothEmbedding J₀ I₀ ∞ Q₀ M₀} {f₁ : SmoothEmbedding J₁ I₁ ∞ Q₁ M₁}

/-- The map `L q = rep₁ ∘ Φ q ∘ [·]` from the tangent spaces of `M₀` along `f₀` to those of `M₁`
along `f₁ ∘ φ` is a smooth section of the bundle of linear maps between the pull-backs. -/
private theorem contMDiff_symplecticNormalRepresentative_comp_normalClassL
    {hσ₁ : σ₁.IsNondegenerate} (h₁ : hσ₁.HasSymplecticTangentImages J₁ f₁)
    (φ : Q₀ ≃ₘ⟮J₀, J₁⟯ Q₁) (hn : (∞ : ℕ∞ω) ≠ 0) (hP₀ : finrank ℝ P₀ = finrank ℝ E₀ - finrank ℝ EQ₀)
    (hP₁ : finrank ℝ P₁ = finrank ℝ E₁ - finrank ℝ EQ₁)
    (Φ : ∀ q, f₀.NormalSpace q hn ≃L[ℝ] f₁.NormalSpace (φ q) hn)
    (hΦ : letI := f₀.normalSpaceFiberBundle hn hP₀
      letI := f₁.normalSpaceFiberBundle hn hP₁
      ContMDiff (J₀.prod 𝓘(ℝ, P₀)) (J₁.prod 𝓘(ℝ, P₁)) ∞
        (fun p : TotalSpace P₀ (fun q ↦ f₀.NormalSpace q hn) ↦
          (⟨φ p.proj, Φ p.proj p.snd⟩ : TotalSpace P₁ (fun q ↦ f₁.NormalSpace q hn)))) :
    ContMDiff J₀ (J₀.prod 𝓘(ℝ, E₀ →L[ℝ] E₁)) ∞ (fun q ↦ TotalSpace.mk' (E₀ →L[ℝ] E₁)
      (E := fun q ↦ ((f₀ : Q₀ → M₀) *ᵖ (TangentSpace I₀)) q →L[ℝ]
        ((f₁.compDiffeomorphOfBoundaryless φ (by simp) : Q₀ → M₁) *ᵖ (TangentSpace I₁)) q) q
      ((f₁.symplecticNormalRepresentative h₁ (φ q) hn).comp
        ((Φ q : _ →L[ℝ] _).comp (f₀.normalClassL q hn)))) := by
  let := f₀.normalSpaceFiberBundle hn hP₀
  let := f₁.normalSpaceFiberBundle hn hP₁
  have hK := f₀.contMDiff_normalQuotientMap (m := ∞) hn (by simp) hP₀
  have hG := f₁.contMDiff_symplecticNormalRepresentative h₁ hn (m := ∞) (by simp) (by simp) hP₁
  refine (contMDiff_hom_bundle_iff (F₁ := E₀) (F₂ := E₁)
    (E₁ := (f₀ : Q₀ → M₀) *ᵖ (TangentSpace I₀))
    (E₂ := (f₁.compDiffeomorphOfBoundaryless φ (by simp) : Q₀ → M₁) *ᵖ (TangentSpace I₁)) _).2 ?_
  rw [Pullback.contMDiff_iff _ (f₁.compDiffeomorphOfBoundaryless φ (by simp)).contMDiff]
  refine ⟨contMDiff_proj _, (hG.comp (hΦ.comp hK)).congr fun p ↦ ?_⟩
  rw [Function.comp_apply, Function.comp_apply, SmoothEmbedding.normalQuotientMap_apply]
  refine TotalSpace.ext (f₁.compDiffeomorphOfBoundaryless_apply φ (by simp) p.proj) (heq_of_eq ?_)
  -- `L` applied to a vector is the composite applied to it, by the definition of composition.
  exact congrArg (f₁.symplecticNormalRepresentative h₁ (φ p.proj) hn)
    (congrArg (Φ p.proj) (f₀.normalClassL_apply p.proj hn p.snd))

omit [FiniteDimensional ℝ EQ₀] [FiniteDimensional ℝ EQ₁] [J₀.Boundaryless] [I₁.Boundaryless]
  [IsManifold J₀ ∞ Q₀] [IsManifold J₁ ∞ Q₁] in
/-- Let `ψ` be a diffeomorphism of open sets pulling `σ₁` back to `σ₀`, with `ψ (f₀ q) = f₁ (φ q)`
and `dψ ∘ df₀ = df₁ ∘ dφ` at `q`. If `dψ` maps the symplectic representative of a normal vector
`v` of `f₀` to that of a normal vector `w` of `f₁` plus a tangent vector of `f₁`, then the
tangent vector is zero. -/
private theorem mfderiv_symplecticNormalRepresentative_eq {hσ₀ : σ₀.IsNondegenerate}
    {hσ₁ : σ₁.IsNondegenerate} (h₀ : hσ₀.HasSymplecticTangentImages J₀ f₀)
    (h₁ : hσ₁.HasSymplecticTangentImages J₁ f₁) (φ : Q₀ ≃ₘ⟮J₀, J₁⟯ Q₁) (hn : (∞ : ℕ∞ω) ≠ 0)
    {U₀ : Opens M₀} {U₁ : Opens M₁} (ψ : U₀ ≃ₘ⟮I₀, I₁⟯ U₁)
    (hψσ : SmoothForm.mpullback ψ ψ.contMDiff
        (SmoothForm.mpullback (Subtype.val : U₁ → M₁) contMDiff_subtypeVal σ₁) =
      SmoothForm.mpullback (Subtype.val : U₀ → M₀) contMDiff_subtypeVal σ₀)
    {q : Q₀} (h : f₀ q ∈ U₀) (hψq : (ψ ⟨f₀ q, h⟩ : M₁) = f₁ (φ q))
    (hdψ : ∀ v, mfderiv I₀ I₁ ψ ⟨f₀ q, h⟩ (mfderiv J₀ I₀ f₀ q v) =
      mfderiv J₁ I₁ f₁ (φ q) (mfderiv J₀ J₁ φ q v))
    (v : f₀.NormalSpace q hn) (w : f₁.NormalSpace (φ q) hn) (u : TangentSpace J₀ q)
    (hu : mfderiv I₀ I₁ ψ ⟨f₀ q, h⟩ (f₀.symplecticNormalRepresentative h₀ q hn v) =
      f₁.symplecticNormalRepresentative h₁ (φ q) hn w +
        mfderiv J₁ I₁ f₁ (φ q) (mfderiv J₀ J₁ φ q u)) :
    mfderiv J₁ I₁ f₁ (φ q) (mfderiv J₀ J₁ φ q u) = 0 := by
  -- `dψ` preserves the forms at `f₀ q`.
  have hpt := SmoothForm.eval₂_mfderiv_eq_of_mpullback_subtype_val_eq ψ.contMDiff hψσ ⟨f₀ q, h⟩
  rw [hψq] at hpt
  -- The tangent vector `df₁ (dφ u)` pairs to zero with the tangent space of `f₁`.
  refine (hasSymplecticTangentImages_iff.1 h₁) (φ q) _ fun x ↦ ?_
  obtain ⟨x, rfl⟩ := (φ.isInvertible_mfderiv hn).surjective x
  have h1 : SmoothBundleForm.eval₂ σ₁ (f₁ (φ q))
      (mfderiv I₀ I₁ ψ ⟨f₀ q, h⟩ (f₀.symplecticNormalRepresentative h₀ q hn v))
      (mfderiv J₁ I₁ f₁ (φ q) (mfderiv J₀ J₁ φ q x)) = 0 :=
    (congrArg (SmoothBundleForm.eval₂ σ₁ (f₁ (φ q)) _) (hdψ x).symm).trans
      ((hpt _ _).trans (f₀.eval₂_symplecticNormalRepresentative_mfderiv h₀ q hn v x))
  rw [eq_sub_of_add_eq' hu.symm]
  exact (SmoothBundleForm.eval₂_sub_left _ _ _ _ _).trans ((congrArg₂ (· - ·) h1
    (f₁.eval₂_symplecticNormalRepresentative_mfderiv h₁ (φ q) hn _ _)).trans (sub_zero 0))

variable [I₀.Boundaryless] [T2Space M₀] [T2Space M₁]
  [SecondCountableTopology M₀] [SecondCountableTopology M₁]

/-- **The symplectic neighbourhood theorem.** Let `f₀ : Q₀ → M₀` and `f₁ : Q₁ → M₁` be smooth
embeddings with symplectic tangent images into second countable Hausdorff manifolds without
boundary with symplectic forms `σ₀` and `σ₁`. Let `φ : Q₀ → Q₁` be a diffeomorphism with
`φ^* (f₁^* σ₁) = f₀^* σ₀`, and let `Φ q` be linear isomorphisms from the normal spaces of `f₀` at
`q` to those of `f₁` at `φ q` which preserve the normal symplectic forms and form a smooth map of
normal bundles, the normal bundles having model fibres `P₀` and `P₁` of the right dimensions.
Then there are open sets `U₀ ⊆ M₀` and `U₁ ⊆ M₁` and a diffeomorphism `ψ : U₀ ≃ U₁` pulling the
restriction of `σ₁` back to that of `σ₀`, such that for every `q`, `f₀ q ∈ U₀`,
`ψ (f₀ q) = f₁ (φ q)`, `dψ ∘ df₀ = df₁ ∘ dφ` at `q`, and `dψ` maps the symplectic
representative of each normal vector `v` of `f₀` at `q` to the symplectic representative of
`Φ q v`. Neither compactness of the `Qⱼ` nor closedness of the images is assumed. The two
submanifolds may be modelled on different spaces `J₀` and `J₁`, and `Q₀` has no boundary.

Milestone: *Symplectic neighbourhood theorem*. -/
theorem HasSymplecticTangentImages.exists_symplectomorphism_opens {hσ₀ : σ₀.IsSymplectic}
    {hσ₁ : σ₁.IsSymplectic} (h₀ : hσ₀.isNondegenerate.HasSymplecticTangentImages J₀ f₀)
    (h₁ : hσ₁.isNondegenerate.HasSymplecticTangentImages J₁ f₁) (φ : Q₀ ≃ₘ⟮J₀, J₁⟯ Q₁)
    (hφ : SmoothForm.mpullback φ φ.contMDiff (SmoothForm.mpullback f₁ f₁.contMDiff σ₁) =
      SmoothForm.mpullback f₀ f₀.contMDiff σ₀)
    (hn : (∞ : ℕ∞ω) ≠ 0) (hP₀ : finrank ℝ P₀ = finrank ℝ E₀ - finrank ℝ EQ₀)
    (hP₁ : finrank ℝ P₁ = finrank ℝ E₁ - finrank ℝ EQ₁)
    (Φ : ∀ q, f₀.NormalSpace q hn ≃L[ℝ] f₁.NormalSpace (φ q) hn)
    (hΦ : letI := f₀.normalSpaceFiberBundle hn hP₀
      letI := f₁.normalSpaceFiberBundle hn hP₁
      ContMDiff (J₀.prod 𝓘(ℝ, P₀)) (J₁.prod 𝓘(ℝ, P₁)) ∞
        (fun p : TotalSpace P₀ (fun q ↦ f₀.NormalSpace q hn) ↦
          (⟨φ p.proj, Φ p.proj p.snd⟩ : TotalSpace P₁ (fun q ↦ f₁.NormalSpace q hn))))
    (hΦσ : ∀ q v w, f₁.symplecticNormalForm h₁ (φ q) hn (Φ q v) (Φ q w) =
      f₀.symplecticNormalForm h₀ q hn v w) :
    ∃ (U₀ : Opens M₀) (U₁ : Opens M₁) (ψ : U₀ ≃ₘ⟮I₀, I₁⟯ U₁),
      (∀ q, ∃ h : f₀ q ∈ U₀, (ψ ⟨f₀ q, h⟩ : M₁) = f₁ (φ q) ∧
        (∀ v, mfderiv I₀ I₁ ψ ⟨f₀ q, h⟩ (mfderiv J₀ I₀ f₀ q v) =
          mfderiv J₁ I₁ f₁ (φ q) (mfderiv J₀ J₁ φ q v)) ∧
        ∀ v, mfderiv I₀ I₁ ψ ⟨f₀ q, h⟩ (f₀.symplecticNormalRepresentative h₀ q hn v) =
          f₁.symplecticNormalRepresentative h₁ (φ q) hn (Φ q v)) ∧
      SmoothForm.mpullback ψ ψ.contMDiff
          (SmoothForm.mpullback (Subtype.val : U₁ → M₁) contMDiff_subtypeVal σ₁) =
        SmoothForm.mpullback (Subtype.val : U₀ → M₀) contMDiff_subtypeVal σ₀ := by
  rcases isEmpty_or_nonempty Q₀ with hQ | ⟨⟨q₀⟩⟩
  · obtain ⟨ψ, hψ⟩ := SmoothTwoForm.exists_diffeomorph_bot_mpullback_eq σ₀ σ₁
    exact ⟨⊥, ⊥, ψ, fun q ↦ (hQ.false q).elim, hψ⟩
  -- Compare `f₀` with the reparametrization `g = f₁ ∘ φ`.
  set g := f₁.compDiffeomorphOfBoundaryless φ (by simp)
  have hg : ⇑g = f₁ ∘ φ := f₁.coe_compDiffeomorphOfBoundaryless φ (by simp)
  have hdg (q : Q₀) (v : TangentSpace J₀ q) :
      mfderiv J₀ I₁ g q v = mfderiv J₁ I₁ f₁ (φ q) (mfderiv J₀ J₁ φ q v) := by
    rw [f₁.mfderiv_compDiffeomorphOfBoundaryless φ (by simp) q]
    exact ContinuousLinearMap.comp_apply (M₃ := TangentSpace I₁ (f₁ (φ q))) _ _ _
  have hσ : SmoothForm.mpullback g g.contMDiff σ₁ = SmoothForm.mpullback f₀ f₀.contMDiff σ₀ := by
    rw [← hφ, ← LinearMap.comp_apply, ← SmoothForm.mpullback_comp]
    congr 2
  -- The restricted form is nondegenerate, so of constant rank `0`.
  have hk (q : Q₀) : finrank ℝ (LinearMap.ker
      ((SmoothForm.mpullback f₀ f₀.contMDiff σ₀).bilinFormAt q)) = 0 := by
    rw [((isNondegenerate_mpullback_iff f₀.contMDiff).2
      ⟨h₀, f₀.isImmersion.mfderiv_injective hn⟩).nondegenerate_bilinFormAt q |>.ker_eq_bot,
      finrank_bot]
  have hdim : finrank ℝ E₀ = finrank ℝ E₁ := by
    have h₀ := f₀.finrank_normalSpace_add_finrank q₀ hn
    have h₁ := f₁.finrank_normalSpace_add_finrank (φ q₀) hn
    have hΦ := (Φ q₀).toLinearEquiv.finrank_eq
    -- The diffeomorphism `φ` forces `Q₀` and `Q₁` to have models of equal dimension.
    have hQ := (φ.isLocalDiffeomorph q₀).finrank_eq (by simp)
    simp only [finrank_tangentSpace] at h₀ h₁
    omega
  have hgq (q : Q₀) : g q = f₁ (φ q) := f₁.compDiffeomorphOfBoundaryless_apply φ (by simp) q
  let L (q : Q₀) : TangentSpace I₀ (f₀ q) →L[ℝ] TangentSpace I₁ (f₁ (φ q)) :=
    (f₁.symplecticNormalRepresentative h₁ (φ q) hn).comp
      ((Φ q : _ →L[ℝ] _).comp (f₀.normalClassL q hn))
  have hLapply (q : Q₀) (v : TangentSpace I₀ (f₀ q)) :
      L q v = f₁.symplecticNormalRepresentative h₁ (φ q) hn (Φ q (f₀.normalClass q hn v)) := by
    simp only [L, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      SmoothEmbedding.normalClassL_apply]
  have hL (q : Q₀) : ∀ v ∈ (hσ₀.isNondegenerate.symplecticFormAt (f₀ q)).orthogonal
      (mfderiv J₀ I₀ f₀ q).range,
      L q v ∈ (hσ₁.isNondegenerate.symplecticFormAt (g q)).orthogonal
        (mfderiv J₀ I₁ g q).range := by
    intro v _
    rw [f₁.range_mfderiv_compDiffeomorphOfBoundaryless φ (by simp) q, hgq]
    exact f₁.symplecticNormalRepresentative_mem_orthogonal h₁ (φ q) hn _
  have hLω (q : Q₀) : ∀ v ∈ (hσ₀.isNondegenerate.symplecticFormAt (f₀ q)).orthogonal
      (mfderiv J₀ I₀ f₀ q).range, ∀ w ∈ (hσ₀.isNondegenerate.symplecticFormAt (f₀ q)).orthogonal
        (mfderiv J₀ I₀ f₀ q).range,
        hσ₁.isNondegenerate.symplecticFormAt (g q) (L q v) (L q w) =
          hσ₀.isNondegenerate.symplecticFormAt (f₀ q) v w := by
    intro v hv w hw
    rw [hgq, IsNondegenerate.symplecticFormAt_apply, IsNondegenerate.symplecticFormAt_apply,
      hLapply, hLapply, ← SmoothEmbedding.symplecticNormalForm_apply, hΦσ,
      SmoothEmbedding.symplecticNormalForm_apply,
      f₀.symplecticNormalRepresentative_normalClass_of_mem h₀ q hn hv,
      f₀.symplecticNormalRepresentative_normalClass_of_mem h₀ q hn hw]
  obtain ⟨U₀, U₁, ψ, hψ, hψσ⟩ := SmoothEmbedding.exists_symplectomorphism_opens_of_mpullback_eq
    f₀ g hσ₀ hσ₁ hσ hk hdim L
    (contMDiff_symplecticNormalRepresentative_comp_normalClassL h₁ φ hn hP₀ hP₁ Φ hΦ) hL hLω
  refine ⟨U₀, U₁, ψ, fun q ↦ ?_, hψσ⟩
  obtain ⟨h, hψq, hdψ, hψL⟩ := hψ q
  have hψq' := hψq.trans (hgq q)
  have hdψ' (v : TangentSpace J₀ q) := (hdψ v).trans (hdg q v)
  refine ⟨h, hψq', hdψ', fun v ↦ ?_⟩
  obtain ⟨u, hu⟩ := hψL _ (f₀.symplecticNormalRepresentative_mem_orthogonal h₀ q hn v)
  have hu' : mfderiv I₀ I₁ ψ ⟨f₀ q, h⟩ (f₀.symplecticNormalRepresentative h₀ q hn v) =
      f₁.symplecticNormalRepresentative h₁ (φ q) hn (Φ q v) +
        mfderiv J₁ I₁ f₁ (φ q) (mfderiv J₀ J₁ φ q u) :=
    hu.trans (congrArg₂ (· + ·) ((hLapply q _).trans (by
      rw [SmoothEmbedding.normalClass_symplecticNormalRepresentative])) (hdg q u))
  exact hu'.trans ((congrArg (_ + ·)
    (mfderiv_symplecticNormalRepresentative_eq h₀ h₁ φ hn ψ hψσ h hψq' hdψ' v _ u hu')).trans
      (add_zero _))

end TauCeti.SmoothTwoForm.IsNondegenerate

end
