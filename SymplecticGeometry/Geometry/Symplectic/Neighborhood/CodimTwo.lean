/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Neighborhood.Symplectic
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import SymplecticGeometry.LinearAlgebra.BilinearMap.Alternating
import TauCeti.Geometry.Manifold.ContMDiff.Sqrt
import TauCeti.Geometry.Manifold.VectorBundle.Scalar

/-!
# Symplectic neighbourhoods in codimension two from oriented normal isomorphisms

Let `f₀ : Q₀ → M₀` and `f₁ : Q₁ → M₁` be embeddings with symplectic tangent images, of
codimension two, and let `Φ q` be linear isomorphisms from the normal spaces of `f₀` at `q` to
those of `f₁` at `φ q`, smooth on total spaces. Suppose only that `Φ` preserves the orientations
given by the normal symplectic forms `TauCeti.SmoothEmbedding.symplecticNormalForm`: a pair with
positive pairing goes to a pair with positive pairing. On a plane any two alternating forms are
proportional, so `Φ q` pulls the normal form of `f₁` back to `c q` times that of `f₀`, with
`c q > 0`, and `c` is smooth. The rescaled isomorphisms `(√(c q))⁻¹ • Φ q` then preserve the
normal symplectic forms, and the symplectic neighbourhood theorem
`TauCeti.SmoothTwoForm.IsNondegenerate.HasSymplecticTangentImages.exists_symplectomorphism_opens`
applies to them.

## Proof

The linear algebra is in `SymplecticGeometry.LinearAlgebra.BilinearMap.Alternating`:
`LinearMap.IsAlt.apply_eq_div_mul` gives the proportionality on the bases of the normal spaces
given by a local frame of the normal bundle, `LinearMap.IsAlt.apply_basis_div_apply_basis_pos`
its positivity, and `LinearMap.apply_inv_sqrt_smul_inv_sqrt_smul` the rescaling. Near a point,
`c` is the ratio of the two forms evaluated on the two sections of such a frame, and each
evaluation is smooth by `TauCeti.SmoothEmbedding.contMDiffAt_symplecticNormalForm`. The rescaled
map of total spaces is smooth by Tau Ceti's `ContMDiff.smul_totalSpace`.

## Main results

In the namespace `TauCeti.SmoothTwoForm.IsNondegenerate`:

* `HasSymplecticTangentImages.exists_contMDiff_pos_symplecticNormalForm_eq_mul`: an
  orientation-preserving normal isomorphism multiplies the normal forms by a smooth positive
  function.
* `HasSymplecticTangentImages.exists_symplectomorphism_opens_of_finrank_eq_two`: the symplectic
  neighbourhood theorem in codimension two for orientation-preserving normal isomorphisms.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Theorem 3.4.10.
* [D. McDuff, *Blow ups and symplectic embeddings in dimension 4*][McDuff1991], Lemma 2.1.
-/

public section

open Bundle Manifold Module TopologicalSpace
open scoped ContDiff Manifold Bundle Topology

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
  [TopologicalSpace Q₀] [ChartedSpace HQ₀ Q₀] [IsManifold J₀ ∞ Q₀]
  [TopologicalSpace Q₁] [ChartedSpace HQ₁ Q₁] [IsManifold J₁ ∞ Q₁]
  [TopologicalSpace M₀] [ChartedSpace H₀ M₀] [IsManifold I₀ ∞ M₀]
  [TopologicalSpace M₁] [ChartedSpace H₁ M₁] [IsManifold I₁ ∞ M₁]
  {σ₀ : SmoothTwoForm I₀ M₀} {σ₁ : SmoothTwoForm I₁ M₁}
  {f₀ : SmoothEmbedding J₀ I₀ ∞ Q₀ M₀} {f₁ : SmoothEmbedding J₁ I₁ ∞ Q₁ M₁}

/-- **An orientation-preserving normal isomorphism rescales the normal forms.** Let `f₀` and `f₁`
be embeddings with symplectic tangent images, with normal bundles of model fibres `P₀` and `P₁`,
`P₀` of dimension two, and let `Φ q` be linear maps from the normal spaces of `f₀` at `q` to those
of `f₁` at `φ q`, forming a smooth map of normal bundles, that send each pair with positive
normal symplectic pairing to a pair with positive pairing. Then there is a smooth positive
function `c` on `Q₀` with `ω₁ (Φ q v) (Φ q w) = c q * ω₀ v w` for all normal vectors `v` and `w`
of `f₀` at `q`. -/
theorem HasSymplecticTangentImages.exists_contMDiff_pos_symplecticNormalForm_eq_mul
    {hσ₀ : σ₀.IsNondegenerate} {hσ₁ : σ₁.IsNondegenerate}
    (h₀ : hσ₀.HasSymplecticTangentImages J₀ f₀) (h₁ : hσ₁.HasSymplecticTangentImages J₁ f₁)
    {φ : Q₀ → Q₁} (hn : (∞ : ℕ∞ω) ≠ 0) (hP₀ : finrank ℝ P₀ = finrank ℝ E₀ - finrank ℝ EQ₀)
    (hP₁ : finrank ℝ P₁ = finrank ℝ E₁ - finrank ℝ EQ₁) (h2 : finrank ℝ P₀ = 2)
    (Φ : ∀ q, f₀.isImmersion.NormalSpace q hn →L[ℝ] f₁.isImmersion.NormalSpace (φ q) hn)
    (hΦ : letI := f₀.normalSpaceFiberBundle hn hP₀
      letI := f₁.normalSpaceFiberBundle hn hP₁
      ContMDiff (J₀.prod 𝓘(ℝ, P₀)) (J₁.prod 𝓘(ℝ, P₁)) ∞
        (fun p : TotalSpace P₀ (fun q ↦ f₀.isImmersion.NormalSpace q hn) ↦
          (⟨φ p.proj, Φ p.proj p.snd⟩ : TotalSpace P₁ (fun q ↦ f₁.isImmersion.NormalSpace q hn))))
    (hΦσ : ∀ q v w, 0 < f₀.symplecticNormalForm h₀ q hn v w →
      0 < f₁.symplecticNormalForm h₁ (φ q) hn (Φ q v) (Φ q w)) :
    ∃ c : Q₀ → ℝ, ContMDiff J₀ 𝓘(ℝ) ∞ c ∧ (∀ q, 0 < c q) ∧
      ∀ q v w, f₁.symplecticNormalForm h₁ (φ q) hn (Φ q v) (Φ q w) =
        c q * f₀.symplecticNormalForm h₀ q hn v w := by
  let := f₀.normalSpaceFiberBundle hn hP₀
  let := f₀.normalSpaceVectorBundle hn hP₀
  let := f₀.normalSpaceContMDiffVectorBundle (m := ∞) hn (by simp) hP₀
  let := f₁.normalSpaceFiberBundle hn hP₁
  let b : Module.Basis (Fin 2) ℝ P₀ := Module.finBasisOfFinrankEq ℝ P₀ h2
  -- The basis of the normal space at `q` given by the preferred trivialization at `q`.
  let β (q : Q₀) := (trivializationAt P₀ (fun q ↦ f₀.isImmersion.NormalSpace q hn) q).basisAt b
    (mem_baseSet_trivializationAt P₀ _ q)
  -- The normal form of `f₀` at `q`, and the pullback by `Φ q` of that of `f₁` at `φ q`.
  let ω₀ (q : Q₀) := f₀.symplecticNormalForm h₀ q hn
  let B (q : Q₀) := (f₁.symplecticNormalForm h₁ (φ q) hn).toBilinForm.compl₁₂
    (Φ q).toLinearMap (Φ q).toLinearMap
  have hB_apply (q : Q₀) (v w) :
      B q v w = f₁.symplecticNormalForm h₁ (φ q) hn (Φ q v) (Φ q w) := by
    simp only [B, LinearMap.compl₁₂_apply, ContinuousLinearMap.coe_coe]
  have hB (q : Q₀) : (B q).IsAlt := fun v ↦ by
    rw [hB_apply]
    exact (f₁.symplecticNormalForm h₁ (φ q) hn).self_eq_zero _
  let c (q : Q₀) := B q (β q 0) (β q 1) / ω₀ q (β q 0) (β q 1)
  have hc (q : Q₀) (v w) : f₁.symplecticNormalForm h₁ (φ q) hn (Φ q v) (Φ q w) =
      c q * f₀.symplecticNormalForm h₀ q hn v w := by
    rw [← hB_apply]
    exact (hB q).apply_eq_div_mul (ω₀ q).isAlt (ω₀ q).separatingLeft (β q) v w
  refine ⟨c, fun q₀ ↦ ?_, fun q ↦ ?_, hc⟩
  · -- Near `q₀`, `c` is the ratio of the two forms on a local frame.
    let e := trivializationAt P₀ (fun q ↦ f₀.isImmersion.NormalSpace q hn) q₀
    have hq₀ : q₀ ∈ e.baseSet := mem_baseSet_trivializationAt P₀ _ q₀
    let s := e.localFrame b
    have hs (i : Fin 2) := contMDiffAt_localFrame_of_mem (I := J₀) (n := ∞) e b i hq₀
    have hΦs (i : Fin 2) : ContMDiffAt J₀ (J₁.prod 𝓘(ℝ, P₁)) ∞
        (fun q ↦ TotalSpace.mk' P₁ (E := fun q ↦ f₁.isImmersion.NormalSpace q hn) (φ q)
            (Φ q (s i q))) q₀ :=
      (hΦ _).comp q₀ (hs i)
    have hnum := SmoothEmbedding.contMDiffAt_symplecticNormalForm h₁ hn hP₁ (hΦs 0) (hΦs 1)
    have hden := SmoothEmbedding.contMDiffAt_symplecticNormalForm (u := id) h₀ hn hP₀ (hs 0)
      (hs 1)
    have hs' {q : Q₀} (hq : q ∈ e.baseSet) (i : Fin 2) : e.localFrame b i q = e.basisAt b hq i :=
      e.localFrame_apply_of_mem_baseSet b hq
    refine (hnum.div₀ hden ?_).congr_of_eventuallyEq ?_
    · simpa only [ω₀, id_eq, hs' hq₀] using
        (ω₀ q₀).isAlt.apply_basis_ne_zero (ω₀ q₀).separatingLeft (e.basisAt b hq₀)
    · filter_upwards [e.open_baseSet.mem_nhds hq₀] with q hq
      have hne := (ω₀ q).isAlt.apply_basis_ne_zero (ω₀ q).separatingLeft (e.basisAt b hq)
      simp only [Pi.div_apply, id_eq, s, hs' hq]
      rw [eq_div_iff hne]
      exact (hc q _ _).symm
  · exact (hB q).apply_basis_div_apply_basis_pos (ω₀ q).isAlt (ω₀ q).separatingLeft (β q)
      fun v w hvw ↦ (hB_apply q v w).symm ▸ hΦσ q v w hvw

variable [J₀.Boundaryless] [I₁.Boundaryless] [I₀.Boundaryless] [T2Space M₀] [T2Space M₁]
  [SecondCountableTopology M₀] [SecondCountableTopology M₁]

/-- **The symplectic neighbourhood theorem in codimension two, for orientation-preserving normal
isomorphisms.** Let `f₀`, `f₁`, `φ` and `Φ` be as in
`TauCeti.SmoothTwoForm.IsNondegenerate.HasSymplecticTangentImages.exists_symplectomorphism_opens`,
with normal bundles of rank two, except that `Φ` need only send each pair with positive normal
symplectic pairing to a pair with positive pairing. Then there is a smooth positive function `c`
on `Q₀` with `ω₁ (Φ q v) (Φ q w) = c q * ω₀ v w`, and open sets `U₀ ⊆ M₀` and `U₁ ⊆ M₁` with a
diffeomorphism `ψ : U₀ ≃ U₁` pulling the restriction of `σ₁` back to that of `σ₀`, such that for
every `q`, `f₀ q ∈ U₀`, `ψ (f₀ q) = f₁ (φ q)`, `dψ ∘ df₀ = df₁ ∘ dφ` at `q`, and `dψ` maps the
symplectic representative of each normal vector `v` of `f₀` at `q` to the symplectic
representative of `(√(c q))⁻¹ • Φ q v`. -/
theorem HasSymplecticTangentImages.exists_symplectomorphism_opens_of_finrank_eq_two
    (hσ₀ : σ₀.IsSymplectic) (hσ₁ : σ₁.IsSymplectic)
    (h₀ : hσ₀.isNondegenerate.HasSymplecticTangentImages J₀ f₀)
    (h₁ : hσ₁.isNondegenerate.HasSymplecticTangentImages J₁ f₁) (φ : Q₀ ≃ₘ⟮J₀, J₁⟯ Q₁)
    (hφ : SmoothForm.mpullback φ φ.contMDiff (SmoothForm.mpullback f₁ f₁.contMDiff σ₁) =
      SmoothForm.mpullback f₀ f₀.contMDiff σ₀)
    (hn : (∞ : ℕ∞ω) ≠ 0) (hP₀ : finrank ℝ P₀ = finrank ℝ E₀ - finrank ℝ EQ₀)
    (hP₁ : finrank ℝ P₁ = finrank ℝ E₁ - finrank ℝ EQ₁) (h2 : finrank ℝ P₀ = 2)
    (Φ : ∀ q, f₀.isImmersion.NormalSpace q hn ≃L[ℝ] f₁.isImmersion.NormalSpace (φ q) hn)
    (hΦ : letI := f₀.normalSpaceFiberBundle hn hP₀
      letI := f₁.normalSpaceFiberBundle hn hP₁
      ContMDiff (J₀.prod 𝓘(ℝ, P₀)) (J₁.prod 𝓘(ℝ, P₁)) ∞
        (fun p : TotalSpace P₀ (fun q ↦ f₀.isImmersion.NormalSpace q hn) ↦
          (⟨φ p.proj, Φ p.proj p.snd⟩ : TotalSpace P₁ (fun q ↦ f₁.isImmersion.NormalSpace q hn))))
    (hΦσ : ∀ q v w, 0 < f₀.symplecticNormalForm h₀ q hn v w →
      0 < f₁.symplecticNormalForm h₁ (φ q) hn (Φ q v) (Φ q w)) :
    ∃ c : Q₀ → ℝ, ContMDiff J₀ 𝓘(ℝ) ∞ c ∧ (∀ q, 0 < c q) ∧
      (∀ q v w, f₁.symplecticNormalForm h₁ (φ q) hn (Φ q v) (Φ q w) =
        c q * f₀.symplecticNormalForm h₀ q hn v w) ∧
      ∃ (U₀ : Opens M₀) (U₁ : Opens M₁) (ψ : U₀ ≃ₘ⟮I₀, I₁⟯ U₁),
        (∀ q, ∃ h : f₀ q ∈ U₀, (ψ ⟨f₀ q, h⟩ : M₁) = f₁ (φ q) ∧
          (∀ v, mfderiv I₀ I₁ ψ ⟨f₀ q, h⟩ (mfderiv J₀ I₀ f₀ q v) =
            mfderiv J₁ I₁ f₁ (φ q) (mfderiv J₀ J₁ φ q v)) ∧
          ∀ v, mfderiv I₀ I₁ ψ ⟨f₀ q, h⟩ (f₀.symplecticNormalRepresentative h₀ q hn v) =
            f₁.symplecticNormalRepresentative h₁ (φ q) hn ((√(c q))⁻¹ • Φ q v)) ∧
        SmoothForm.mpullback ψ ψ.contMDiff
            (SmoothForm.mpullback (Subtype.val : U₁ → M₁) contMDiff_subtypeVal σ₁) =
          SmoothForm.mpullback (Subtype.val : U₀ → M₀) contMDiff_subtypeVal σ₀ := by
  obtain ⟨c, hcs, hc0, hc⟩ := exists_contMDiff_pos_symplecticNormalForm_eq_mul h₀ h₁ hn hP₀ hP₁
    h2 (fun q ↦ (Φ q : f₀.isImmersion.NormalSpace q hn →L[ℝ] f₁.isImmersion.NormalSpace (φ q) hn))
        hΦ hΦσ
  have hc0' (q : Q₀) : (√(c q))⁻¹ ≠ 0 := inv_ne_zero (Real.sqrt_pos.2 (hc0 q)).ne'
  -- The rescaled isomorphisms.
  let Φ' (q : Q₀) : f₀.isImmersion.NormalSpace q hn ≃L[ℝ] f₁.isImmersion.NormalSpace (φ q) hn :=
    (Φ q).trans (ContinuousLinearEquiv.smulLeft (Units.mk0 _ (hc0' q)))
  have hΦ' (q : Q₀) (v : f₀.isImmersion.NormalSpace q hn) : Φ' q v = (√(c q))⁻¹ • Φ q v := by
    simp only [Φ', ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.smulLeft_apply_apply,
      Units.smul_mk0]
  have ha : ContMDiff J₀ 𝓘(ℝ) ∞ fun q ↦ (√(c q))⁻¹ :=
    (hcs.sqrt fun q ↦ (hc0 q).ne').inv₀ fun q ↦ (Real.sqrt_pos.2 (hc0 q)).ne'
  let := f₀.normalSpaceFiberBundle hn hP₀
  let := f₁.normalSpaceFiberBundle hn hP₁
  let := f₁.normalSpaceVectorBundle hn hP₁
  have hΦs := (ha.comp (contMDiff_proj _)).smul_totalSpace hΦ
  obtain ⟨U₀, U₁, ψ, hψ, hψσ⟩ := exists_symplectomorphism_opens hσ₀ hσ₁ h₀ h₁ φ hφ hn hP₀ hP₁ Φ'
    (by simpa only [hΦ', ContinuousLinearEquiv.coe_coe, Function.comp_apply] using hΦs)
    (fun q v w ↦ by
      rw [hΦ', hΦ']
      exact LinearMap.apply_inv_sqrt_smul_inv_sqrt_smul _ (hc0 q) (hc q v w))
  refine ⟨c, hcs, hc0, hc, U₀, U₁, ψ, fun q ↦ ?_, hψσ⟩
  obtain ⟨h, hψq, hdψ, hψΦ⟩ := hψ q
  exact ⟨h, hψq, hdψ, fun v ↦ (hψΦ v).trans (by rw [hΦ'])⟩

end TauCeti.SmoothTwoForm.IsNondegenerate

end
