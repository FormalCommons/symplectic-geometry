/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Blowup.Model
public import SymplecticGeometry.Geometry.Manifold.Complex.Blowup.Tautological
public import SymplecticGeometry.Geometry.Symplectic.Neighborhood.CodimTwo
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Symplectic.Manifold.NeighborhoodGerm
import TauCeti.Geometry.Symplectic.Manifold.Rescale

/-!
# A neighbourhood of a divisor modelled on `L(ε)`

Let `(M, σ)` be a symplectic manifold without boundary and
`f : ℙ ℂ (Fin (n + 1) → ℂ) → M` a smooth embedding with `f^* σ = l² ω_FS`, `l ≠ 0`. Suppose that the
normal bundle of `f` is isomorphic to the normal bundle of the zero section of the model blowup
`BlowupModel n`, which is the tautological line (`Blowup/Tautological.lean`), by a smooth
fibrewise isomorphism `Φ` preserving the orientations that the normal symplectic forms give, for
`σ` and for the form `ω̃_l = blowupForm n l` of the model. Then a neighbourhood of the image of
`f` is symplectomorphic to some `(L(ε), ω̃_l) = (openNbhd n ε, blowupForm n l)`, by a map sending
`f` to the zero section (McDuff, Lemma 2.1 and Corollary 2.2; McDuff–Salamon, p. 302).

For `n = 0` the divisor is a point, `ω_FS` vanishes, and the statement is Darboux's theorem
for a ball around that point, with `l` free.

## Main results

* `SymplecticGeometry.hasSymplecticTangentImages_of_mpullback_eq_smul_fubiniStudyForm`:
  a smooth map from `ℙ ℂ (Fin (n + 1) → ℂ)` pulling a nondegenerate form back to `l² ω_FS`,
  `l ≠ 0`, has symplectic tangent images.
* `SymplecticGeometry.BlowupModel.mpullback_zeroSectionRealEmbedding_blowupForm` and
  `SymplecticGeometry.BlowupModel.hasSymplecticTangentImages_zeroSectionRealEmbedding`: the
  real zero section of the model pulls `ω̃_l` back to `l² ω_FS`, so it has symplectic tangent
  images for `ω̃_l`.
* `SymplecticGeometry.BlowupModel.exists_symplectomorphism_blowupModel`: the neighbourhood
  theorem above, as a partial diffeomorphism from `M` to the model with target `openNbhd n ε`,
  whose source contains the image of `f`, sending `f q` to `zeroSection q` and symplectic from
  `σ` to `ω̃_l` on its source.

## Proof

The codimension-two symplectic neighbourhood theorem
`HasSymplecticTangentImages.exists_symplectomorphism_opens_of_finrank_eq_two`
(`Geometry/Symplectic/Neighborhood/CodimTwo.lean`), which rescales `Φ` to preserve the normal
forms, applies to `f` and the real zero section `zeroSectionRealEmbedding n`, with the identity
of `ℙ ℂ (Fin (n + 1) → ℂ)`: both pull their forms back to `l² ω_FS`. It gives a
symplectomorphism between open sets `U₀ ⊆ M` and `U₁ ⊆ BlowupModel n` with `U₁` containing the
exceptional divisor. By compactness of the divisor, `U₁` contains some `openNbhd n ε`
(`exists_openNbhd_subset`), and the symplectomorphism is restricted to its preimage.

## References

* [D. McDuff, *Blow ups and symplectic embeddings in dimension 4*][McDuff1991], Lemma 2.1 and
  Corollary 2.2.
* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §7.1, p. 302, and Theorem 3.4.10.
-/

public section

open Set Projectivization TauCeti Bundle Module TopologicalSpace
open scoped Topology Manifold ContDiff LinearAlgebra.Projectivization TauCeti.ComplexManifold

namespace SymplecticGeometry

variable {n : ℕ} {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

/-- A smooth map `g` from `ℙ ℂ (Fin (n + 1) → ℂ)` pulling a nondegenerate two-form `σ` back to
`l² ω_FS`, for `l ≠ 0`, has symplectic tangent images for `σ`. -/
theorem hasSymplecticTangentImages_of_mpullback_eq_smul_fubiniStudyForm {σ : SmoothTwoForm I M}
    (hσ : σ.IsNondegenerate) {g : ℙ ℂ (Fin (n + 1) → ℂ) → M}
    (hg : ContMDiff 𝓘(ℝ, Fin n → ℂ) I ∞ g) {l : ℝ} (hl : l ≠ 0)
    (h : SmoothForm.mpullback g hg σ = l ^ 2 • fubiniStudyForm n) :
    hσ.HasSymplecticTangentImages 𝓘(ℝ, Fin n → ℂ) g :=
  ((SmoothTwoForm.IsNondegenerate.isNondegenerate_mpullback_iff hg).1
    (h ▸ (isSymplectic_fubiniStudyForm n).isNondegenerate.smul _ (pow_ne_zero 2 hl))).1

namespace BlowupModel

/-- The real zero section of the model blowup pulls `ω̃_l = blowupForm n l` back to `l² ω_FS`. -/
theorem mpullback_zeroSectionRealEmbedding_blowupForm (l : ℝ) :
    SmoothForm.mpullback (zeroSectionRealEmbedding n) (zeroSectionRealEmbedding n).contMDiff
        (blowupForm n l) =
      l ^ 2 • fubiniStudyForm n :=
  (SmoothForm.mpullback_congr _ _ (coe_zeroSectionRealEmbedding n) _).trans
    (mpullback_zeroSection_blowupForm l)

/-- For `l ≠ 0`, the zero section of the model blowup has symplectic tangent images for the
symplectic form `ω̃_l = blowupForm n l`. -/
theorem hasSymplecticTangentImages_zeroSectionRealEmbedding {l : ℝ} (hl : l ≠ 0) :
    (isSymplectic_blowupForm (n := n) hl).isNondegenerate.HasSymplecticTangentImages
      𝓘(ℝ, Fin n → ℂ) (zeroSectionRealEmbedding n) :=
  hasSymplecticTangentImages_of_mpullback_eq_smul_fubiniStudyForm _ _ hl
    (mpullback_zeroSectionRealEmbedding_blowupForm l)

variable [I.Boundaryless] [T2Space M] [SecondCountableTopology M]
  {P₀ P₁ : Type*} [NormedAddCommGroup P₀] [NormedSpace ℝ P₀] [FiniteDimensional ℝ P₀]
  [NormedAddCommGroup P₁] [NormedSpace ℝ P₁] [FiniteDimensional ℝ P₁]

/-- **A neighbourhood of a divisor is modelled on `L(ε)`.** Let `σ` be a symplectic form on a
second countable Hausdorff manifold `M` without boundary, and `f` a smooth embedding of
`ℙ ℂ (Fin (n + 1) → ℂ)` into `M` with `f^* σ = l² ω_FS`, for `l ≠ 0`. Let `Φ q` be linear
isomorphisms from the normal spaces of `f` at `q` to those of the zero section of the model
blowup, forming a smooth map of normal bundles (of model fibres `P₀` and `P₁`), that send each
pair of positive normal symplectic pairing for `σ` to a pair of positive pairing for
`ω̃_l = blowupForm n l`. Then there are `ε > 0` and a partial diffeomorphism `Ψ` from `M` to the
model blowup, with target `openNbhd n ε`, whose source contains the image of `f`, with
`Ψ (f q) = zeroSection q` for all `q`, and which is symplectic from `σ` to `ω̃_l` on its source. -/
theorem exists_symplectomorphism_blowupModel [FiniteDimensional ℝ E] {σ : SmoothTwoForm I M}
    (hσ : σ.IsSymplectic) {f : SmoothEmbedding 𝓘(ℝ, Fin n → ℂ) I ∞ (ℙ ℂ (Fin (n + 1) → ℂ)) M}
    {l : ℝ} (hl : l ≠ 0) (hf : SmoothForm.mpullback f f.contMDiff σ = l ^ 2 • fubiniStudyForm n)
    (hn : (∞ : ℕ∞ω) ≠ 0) (hP₀ : finrank ℝ P₀ = finrank ℝ E - finrank ℝ (Fin n → ℂ))
    (hP₁ : finrank ℝ P₁ = finrank ℝ (Fin (n + 1) → ℂ) - finrank ℝ (Fin n → ℂ))
    (Φ : ∀ q, f.isImmersion.NormalSpace q hn ≃L[ℝ] (zeroSectionRealEmbedding n).isImmersion.NormalSpace q hn)
    (hΦ : letI := f.normalSpaceFiberBundle hn hP₀
      letI := (zeroSectionRealEmbedding n).normalSpaceFiberBundle hn hP₁
      ContMDiff (𝓘(ℝ, Fin n → ℂ).prod 𝓘(ℝ, P₀)) (𝓘(ℝ, Fin n → ℂ).prod 𝓘(ℝ, P₁)) ∞
        (fun p : TotalSpace P₀ (fun q ↦ f.isImmersion.NormalSpace q hn) ↦
          (⟨p.proj, Φ p.proj p.snd⟩ :
            TotalSpace P₁ (fun q ↦ (zeroSectionRealEmbedding n).isImmersion.NormalSpace q hn))))
    (hΦσ : ∀ q v w,
      0 < f.symplecticNormalForm (hasSymplecticTangentImages_of_mpullback_eq_smul_fubiniStudyForm
        hσ.isNondegenerate f.contMDiff hl hf) q hn v w →
      0 < (zeroSectionRealEmbedding n).symplecticNormalForm
        (hasSymplecticTangentImages_zeroSectionRealEmbedding hl) q hn (Φ q v) (Φ q w)) :
    ∃ ε > 0, ∃ Ψ : PartialDiffeomorph I 𝓘(ℝ, Fin (n + 1) → ℂ) M (BlowupModel n) ∞,
      Ψ.target = openNbhd n ε ∧ (∀ q, f q ∈ Ψ.source ∧ Ψ (f q) = zeroSection q) ∧
      σ.IsSymplecticMapOn (blowupForm n l) Ψ Ψ.source := by
  have h₀ := hasSymplecticTangentImages_of_mpullback_eq_smul_fubiniStudyForm
    hσ.isNondegenerate f.contMDiff hl hf
  have h₁ := hasSymplecticTangentImages_zeroSectionRealEmbedding (n := n) hl
  -- The normal bundles have rank two, as that of the zero section has.
  have h2 : finrank ℝ P₀ = 2 := by
    obtain ⟨q⟩ := (inferInstance : Nonempty (ℙ ℂ (Fin (n + 1) → ℂ)))
    -- The tangent spaces of `M` are the model space `E`, which `rfl` unfolds.
    rw [← finrank_normalSpace_zeroSectionRealEmbedding n hn q, ← (Φ q).toLinearEquiv.finrank_eq,
      Manifold.IsImmersion.finrank_normalSpace, hP₀]
    rfl
  obtain ⟨c, -, -, -, U₀, U₁, ψ, hψ, hψσ⟩ :=
    h₀.exists_symplectomorphism_opens_of_finrank_eq_two hσ (isSymplectic_blowupForm hl) h₁
      (Diffeomorph.refl _ _ _) (by
        rw [mpullback_zeroSectionRealEmbedding_blowupForm, hf]
        exact (SmoothForm.mpullback_congr _ contMDiff_id rfl _).trans
          (LinearMap.congr_fun SmoothForm.mpullback_id _))
      hn hP₀ hP₁ h2 Φ hΦ hΦσ
  obtain ⟨q₀⟩ := (inferInstance : Nonempty (ℙ ℂ (Fin (n + 1) → ℂ)))
  have hU₀ : Nonempty U₀ := ⟨⟨f q₀, (hψ q₀).1⟩⟩
  have hU₁ : Nonempty U₁ := ⟨ψ ⟨f q₀, (hψ q₀).1⟩⟩
  -- `U₁` is an open set containing the exceptional divisor, so it contains some `L(ε)`.
  obtain ⟨ε, hε, hεU⟩ := exists_openNbhd_subset (n := n) (U := U₁) <|
    U₁.isOpen.mem_nhdsSet.2 fun p hp ↦ by
      rw [exceptionalDivisor_eq_range] at hp
      obtain ⟨q, rfl⟩ := hp
      obtain ⟨h, hq, -⟩ := hψ q
      simpa [hq] using (ψ ⟨f q, h⟩).property
  let Φ₀ := ψ.toPartialDiffeomorph.liftOpens hU₀ hU₁
  have hs : IsOpen (Φ₀.source ∩ Φ₀ ⁻¹' openNbhd n ε) :=
    Φ₀.toOpenPartialHomeomorph.isOpen_inter_preimage (isOpen_openNbhd ε)
  refine ⟨ε, hε, Φ₀.restrOpen _ hs, ?_, fun q ↦ ?_, ?_⟩
  · refine Φ₀.restrOpen_target_eq_of_subset (fun y hy ↦ ?_) hs
    rw [ψ.toPartialDiffeomorph_liftOpens_target]
    exact hεU hy
  · obtain ⟨h, hq, -⟩ := hψ q
    have hΦ₀ : Φ₀ (f q) = zeroSection q := by
      have := PartialDiffeomorph.liftOpens_apply_coe ψ.toPartialDiffeomorph hU₀ hU₁ ⟨f q, h⟩
      simpa [hq] using this
    have hsrc : f q ∈ Φ₀.source := by
      rw [ψ.toPartialDiffeomorph_liftOpens_source]
      exact h
    rw [PartialDiffeomorph.restrOpen_source, PartialDiffeomorph.coe_restrOpen]
    refine ⟨⟨hsrc, hsrc, ?_⟩, hΦ₀⟩
    rw [mem_preimage, hΦ₀]
    exact exceptionalDivisor_subset_openNbhd hε (exceptionalDivisor_eq_range ▸ ⟨q, rfl⟩)
  · rw [PartialDiffeomorph.restrOpen_source, PartialDiffeomorph.coe_restrOpen]
    exact (ψ.isSymplecticMapOn_toPartialDiffeomorph_liftOpens hU₀ hU₁ hψσ).mono
      inter_subset_left

end BlowupModel

end SymplecticGeometry

end
