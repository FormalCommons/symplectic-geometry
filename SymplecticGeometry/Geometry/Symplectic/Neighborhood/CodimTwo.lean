/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Neighborhood.Symplectic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import SymplecticGeometry.LinearAlgebra.BilinearMap.Alternating
import TauCeti.LinearAlgebra.BilinearForm.Basic
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

Proportionality is `LinearMap.IsAlt.apply_mul_eq_mul_apply_of_basis`, applied to the bases
of the normal spaces given by a local frame of the normal bundle. Near a point, `c` is the ratio
of the two forms evaluated on the two sections of such a frame. Each evaluation is smooth, as it
is the ambient form evaluated on the symplectic representatives
(`TauCeti.SmoothEmbedding.contMDiffAt_symplecticNormalForm`), the same argument as in the proof
of Tau Ceti's `TauCeti.SmoothEmbedding.contMDiff_symplecticNormalFlat`. The rescaled map of
total spaces is smooth by Tau Ceti's `ContMDiff.smul_totalSpace`.

## Main results

* `TauCeti.SmoothEmbedding.contMDiffAt_symplecticNormalForm`: the normal symplectic form
  evaluated on two smooth maps into the normal bundle is smooth.
* `TauCeti.SmoothEmbedding.contMDiff_totalSpace_smul`: rescaling a smooth map of normal bundles
  by a smooth function keeps it smooth.
In the namespace `TauCeti.SmoothTwoForm.IsNondegenerate`:

* `HasSymplecticTangentImages.exists_contMDiff_pos_symplecticNormalForm_eq_mul`: an
  orientation-preserving normal isomorphism multiplies the normal forms by a smooth positive
  function.
* `HasSymplecticTangentImages.symplecticNormalForm_inv_sqrt_smul`: the rescaled isomorphisms
  preserve the normal forms.
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

namespace TauCeti.SmoothEmbedding

variable {EQ HQ Q EN HN N EX HX X P : Type*} [NormedAddCommGroup EQ] [NormedSpace ℝ EQ]
  [FiniteDimensional ℝ EQ] [TopologicalSpace HQ] {J : ModelWithCorners ℝ EQ HQ}
  [TopologicalSpace Q] [ChartedSpace HQ Q] [IsManifold J ∞ Q]
  [NormedAddCommGroup EN] [NormedSpace ℝ EN] [FiniteDimensional ℝ EN]
  [TopologicalSpace HN] {K : ModelWithCorners ℝ EN HN} [TopologicalSpace N] [ChartedSpace HN N]
  [IsManifold K ∞ N] [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
  {L : ModelWithCorners ℝ EX HX} [TopologicalSpace X] [ChartedSpace HX X]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {σ : SmoothTwoForm K N} {hσ : σ.IsNondegenerate}

/-- The normal symplectic form of a symplectic submanifold, evaluated on two maps into its normal
bundle over the same base map that are smooth at a point, is smooth at that point. -/
theorem contMDiffAt_symplecticNormalForm {f : SmoothEmbedding J K ∞ Q N}
    (h : hσ.HasSymplecticTangentImages J f) (hn : (∞ : ℕ∞ω) ≠ 0)
    (hP : finrank ℝ P = finrank ℝ EN - finrank ℝ EQ) {u : X → Q}
    {v w : ∀ x, f.NormalSpace (u x) hn} {x₀ : X}
    (hv : letI := f.normalSpaceFiberBundle hn hP
      ContMDiffAt L (J.prod 𝓘(ℝ, P)) ∞
        (fun x ↦ TotalSpace.mk' P (E := fun q ↦ f.NormalSpace q hn) (u x) (v x)) x₀)
    (hw : letI := f.normalSpaceFiberBundle hn hP
      ContMDiffAt L (J.prod 𝓘(ℝ, P)) ∞
        (fun x ↦ TotalSpace.mk' P (E := fun q ↦ f.NormalSpace q hn) (u x) (w x)) x₀) :
    ContMDiffAt L 𝓘(ℝ) ∞ (fun x ↦ f.symplecticNormalForm h (u x) hn (v x) (w x)) x₀ := by
  let := f.normalSpaceFiberBundle hn hP
  have hrep := f.contMDiff_symplecticNormalRepresentative h hn (m := ∞) (by simp) (by simp) hP
  have hpair := σ.contMDiffAt_eval₂ (b := fun x ↦ f (u x)) ((hrep _).comp x₀ hv)
    ((hrep _).comp x₀ hw)
  rw [Bundle.contMDiffAt_totalSpace_iff] at hpair
  simpa [Trivial.fiberBundle_trivializationAt'] using hpair.2

/-- Multiplying a map of normal bundles, smooth on total spaces, by a smooth function on the base
keeps it smooth on total spaces. -/
theorem contMDiff_totalSpace_smul {EQ' HQ' Q' EN' HN' N' P' : Type*}
    [NormedAddCommGroup EQ'] [NormedSpace ℝ EQ'] [TopologicalSpace HQ']
    {J' : ModelWithCorners ℝ EQ' HQ'} [TopologicalSpace Q'] [ChartedSpace HQ' Q']
    [IsManifold J' ∞ Q'] [NormedAddCommGroup EN'] [NormedSpace ℝ EN'] [TopologicalSpace HN']
    {K' : ModelWithCorners ℝ EN' HN'} [TopologicalSpace N'] [ChartedSpace HN' N']
    [FiniteDimensional ℝ EQ'] [FiniteDimensional ℝ EN'] [IsManifold K' ∞ N']
    [NormedAddCommGroup P'] [NormedSpace ℝ P'] [FiniteDimensional ℝ P']
    {f : SmoothEmbedding J K ∞ Q N} {f' : SmoothEmbedding J' K' ∞ Q' N'} (hn : (∞ : ℕ∞ω) ≠ 0)
    (hP : finrank ℝ P = finrank ℝ EN - finrank ℝ EQ)
    (hP' : finrank ℝ P' = finrank ℝ EN' - finrank ℝ EQ') {φ : Q → Q'}
    (Φ : ∀ q, f.NormalSpace q hn →L[ℝ] f'.NormalSpace (φ q) hn)
    (hΦ : letI := f.normalSpaceFiberBundle hn hP
      letI := f'.normalSpaceFiberBundle hn hP'
      ContMDiff (J.prod 𝓘(ℝ, P)) (J'.prod 𝓘(ℝ, P')) ∞
        (fun p : TotalSpace P (fun q ↦ f.NormalSpace q hn) ↦
          (⟨φ p.proj, Φ p.proj p.snd⟩ : TotalSpace P' (fun q ↦ f'.NormalSpace q hn))))
    {a : Q → ℝ} (ha : ContMDiff J 𝓘(ℝ) ∞ a) :
    letI := f.normalSpaceFiberBundle hn hP
    letI := f'.normalSpaceFiberBundle hn hP'
    ContMDiff (J.prod 𝓘(ℝ, P)) (J'.prod 𝓘(ℝ, P')) ∞
      (fun p : TotalSpace P (fun q ↦ f.NormalSpace q hn) ↦
        (⟨φ p.proj, a p.proj • Φ p.proj p.snd⟩ : TotalSpace P' (fun q ↦ f'.NormalSpace q hn))) :=
  let := f.normalSpaceFiberBundle hn hP
  let := f'.normalSpaceFiberBundle hn hP'
  let := f'.normalSpaceVectorBundle hn hP'
  (ha.comp (contMDiff_proj _)).smul_totalSpace hΦ

end TauCeti.SmoothEmbedding

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

omit [FiniteDimensional ℝ EQ₀] [FiniteDimensional ℝ EQ₁] [FiniteDimensional ℝ P₀]
  [FiniteDimensional ℝ P₁] [IsManifold J₀ ∞ Q₀] [IsManifold J₁ ∞ Q₁] in
/-- On a two-dimensional normal space, a linear map `Φ` of normal spaces multiplies the normal
symplectic forms by a constant: if `β` is a basis of the normal space of `f₀` at `q`, then
`ω₀ (β 0) (β 1) ≠ 0` and `ω₁ (Φ u) (Φ v)` is `ω₁ (Φ (β 0)) (Φ (β 1)) / ω₀ (β 0) (β 1)` times
`ω₀ u v`. -/
private theorem symplecticNormalForm_comp_eq_div_mul {hσ₀ : σ₀.IsNondegenerate}
    {hσ₁ : σ₁.IsNondegenerate} (h₀ : hσ₀.HasSymplecticTangentImages J₀ f₀)
    (h₁ : hσ₁.HasSymplecticTangentImages J₁ f₁) (hn : (∞ : ℕ∞ω) ≠ 0) {q : Q₀} {q' : Q₁}
    (Φ : f₀.NormalSpace q hn →L[ℝ] f₁.NormalSpace q' hn)
    (β : Module.Basis (Fin 2) ℝ (f₀.NormalSpace q hn)) :
    f₀.symplecticNormalForm h₀ q hn (β 0) (β 1) ≠ 0 ∧ ∀ u v,
      f₁.symplecticNormalForm h₁ q' hn (Φ u) (Φ v) =
        f₁.symplecticNormalForm h₁ q' hn (Φ (β 0)) (Φ (β 1)) /
          f₀.symplecticNormalForm h₀ q hn (β 0) (β 1) * f₀.symplecticNormalForm h₀ q hn u v := by
  set ω₀ := f₀.symplecticNormalForm h₀ q hn
  set ω₁ := f₁.symplecticNormalForm h₁ q' hn
  have hne : ω₀ (β 0) (β 1) ≠ 0 := fun h0 ↦ one_ne_zero <|
    ω₀.isAlt.eq_zero_of_smul_apply_basis_eq_zero β ω₀.nondegenerate.1 ((one_smul ℝ _).trans h0)
  refine ⟨hne, fun u v ↦ ?_⟩
  have hB : (ω₁.toBilinForm.compl₁₂ Φ.toLinearMap Φ.toLinearMap).IsAlt :=
    fun x ↦ ω₁.isAlt (Φ x)
  have := hB.apply_mul_eq_mul_apply_of_basis ω₀.isAlt β u v
  simp only [LinearMap.compl₁₂_apply, ContinuousLinearMap.coe_coe] at this
  rw [div_mul_eq_mul_div, eq_div_iff hne]
  exact this.trans (mul_comm _ _)

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
    (Φ : ∀ q, f₀.NormalSpace q hn →L[ℝ] f₁.NormalSpace (φ q) hn)
    (hΦ : letI := f₀.normalSpaceFiberBundle hn hP₀
      letI := f₁.normalSpaceFiberBundle hn hP₁
      ContMDiff (J₀.prod 𝓘(ℝ, P₀)) (J₁.prod 𝓘(ℝ, P₁)) ∞
        (fun p : TotalSpace P₀ (fun q ↦ f₀.NormalSpace q hn) ↦
          (⟨φ p.proj, Φ p.proj p.snd⟩ : TotalSpace P₁ (fun q ↦ f₁.NormalSpace q hn))))
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
  let β (q : Q₀) := (trivializationAt P₀ (fun q ↦ f₀.NormalSpace q hn) q).basisAt b
    (mem_baseSet_trivializationAt P₀ _ q)
  let c (q : Q₀) := f₁.symplecticNormalForm h₁ (φ q) hn (Φ q (β q 0)) (Φ q (β q 1)) /
    f₀.symplecticNormalForm h₀ q hn (β q 0) (β q 1)
  have hc (q : Q₀) (v w) : f₁.symplecticNormalForm h₁ (φ q) hn (Φ q v) (Φ q w) =
      c q * f₀.symplecticNormalForm h₀ q hn v w :=
    (symplecticNormalForm_comp_eq_div_mul h₀ h₁ hn (Φ q) (β q)).2 v w
  refine ⟨c, fun q₀ ↦ ?_, fun q ↦ ?_, hc⟩
  · -- Near `q₀`, `c` is the ratio of the two forms on a local frame.
    let e := trivializationAt P₀ (fun q ↦ f₀.NormalSpace q hn) q₀
    have hq₀ : q₀ ∈ e.baseSet := mem_baseSet_trivializationAt P₀ _ q₀
    let s := e.localFrame b
    have hs (i : Fin 2) := contMDiffAt_localFrame_of_mem (I := J₀) (n := ∞) e b i hq₀
    have hΦs (i : Fin 2) : ContMDiffAt J₀ (J₁.prod 𝓘(ℝ, P₁)) ∞
        (fun q ↦ TotalSpace.mk' P₁ (E := fun q ↦ f₁.NormalSpace q hn) (φ q) (Φ q (s i q))) q₀ :=
      (hΦ _).comp q₀ (hs i)
    have hnum := SmoothEmbedding.contMDiffAt_symplecticNormalForm h₁ hn hP₁ (hΦs 0) (hΦs 1)
    have hden := SmoothEmbedding.contMDiffAt_symplecticNormalForm (u := id) h₀ hn hP₀ (hs 0)
      (hs 1)
    have hne := (symplecticNormalForm_comp_eq_div_mul h₀ h₁ hn (Φ q₀) (e.basisAt b hq₀)).1
    refine (hnum.div₀ hden ?_).congr_of_eventuallyEq ?_
    · simpa [s, hq₀, Bundle.Trivialization.basisAt] using hne
    · filter_upwards [e.open_baseSet.mem_nhds hq₀] with q hq
      have h := symplecticNormalForm_comp_eq_div_mul h₀ h₁ hn (Φ q) (e.basisAt b hq)
      have hs' (i : Fin 2) : s i q = e.basisAt b hq i := e.localFrame_apply_of_mem_baseSet b hq
      simp only [Pi.div_apply, id_eq, s, hs']
      exact (eq_div_iff h.1).2 (hc q _ _).symm
  · -- The basis vectors, in one order or the other, pair positively.
    obtain ⟨hne, -⟩ := symplecticNormalForm_comp_eq_div_mul h₀ h₁ hn (Φ q) (β q)
    rcases hne.lt_or_gt with hlt | hgt
    · have hpos : 0 < f₀.symplecticNormalForm h₀ q hn (β q 1) (β q 0) := by
        rw [← SymplecticForm.neg_eq]
        exact neg_pos.2 hlt
      have h := hc q (β q 1) (β q 0)
      exact pos_of_mul_pos_left (h ▸ hΦσ q _ _ hpos) hpos.le
    · exact div_pos (hΦσ q _ _ hgt) hgt

omit [FiniteDimensional ℝ EQ₀] [FiniteDimensional ℝ EQ₁] [FiniteDimensional ℝ P₀]
  [FiniteDimensional ℝ P₁] [IsManifold J₀ ∞ Q₀] [IsManifold J₁ ∞ Q₁] in
/-- If a linear map `Φ` of normal spaces multiplies the normal symplectic forms by `c > 0`, then
`(√c)⁻¹ • Φ` preserves them. -/
theorem HasSymplecticTangentImages.symplecticNormalForm_inv_sqrt_smul {hσ₀ : σ₀.IsNondegenerate}
    {hσ₁ : σ₁.IsNondegenerate} (h₀ : hσ₀.HasSymplecticTangentImages J₀ f₀)
    (h₁ : hσ₁.HasSymplecticTangentImages J₁ f₁) (hn : (∞ : ℕ∞ω) ≠ 0) {q : Q₀} {q' : Q₁}
    (Φ : f₀.NormalSpace q hn →L[ℝ] f₁.NormalSpace q' hn) {c : ℝ} (hc : 0 < c)
    (hΦ : ∀ v w, f₁.symplecticNormalForm h₁ q' hn (Φ v) (Φ w) =
      c * f₀.symplecticNormalForm h₀ q hn v w) (v w : f₀.NormalSpace q hn) :
    f₁.symplecticNormalForm h₁ q' hn ((√c)⁻¹ • Φ v) ((√c)⁻¹ • Φ w) =
      f₀.symplecticNormalForm h₀ q hn v w := by
  have hs : (√c)⁻¹ * (√c)⁻¹ * c = 1 := by
    rw [← mul_inv, Real.mul_self_sqrt hc.le, inv_mul_cancel₀ hc.ne']
  have h := hΦ v w
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h ⊢
  rw [h, ← mul_assoc, ← mul_assoc, hs, one_mul]

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
    (Φ : ∀ q, f₀.NormalSpace q hn ≃L[ℝ] f₁.NormalSpace (φ q) hn)
    (hΦ : letI := f₀.normalSpaceFiberBundle hn hP₀
      letI := f₁.normalSpaceFiberBundle hn hP₁
      ContMDiff (J₀.prod 𝓘(ℝ, P₀)) (J₁.prod 𝓘(ℝ, P₁)) ∞
        (fun p : TotalSpace P₀ (fun q ↦ f₀.NormalSpace q hn) ↦
          (⟨φ p.proj, Φ p.proj p.snd⟩ : TotalSpace P₁ (fun q ↦ f₁.NormalSpace q hn))))
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
    h2 (fun q ↦ (Φ q : f₀.NormalSpace q hn →L[ℝ] f₁.NormalSpace (φ q) hn)) hΦ hΦσ
  have hc0' (q : Q₀) : (√(c q))⁻¹ ≠ 0 := inv_ne_zero (Real.sqrt_pos.2 (hc0 q)).ne'
  -- The rescaled isomorphisms.
  let Φ' (q : Q₀) : f₀.NormalSpace q hn ≃L[ℝ] f₁.NormalSpace (φ q) hn :=
    (Φ q).trans (ContinuousLinearEquiv.smulLeft (Units.mk0 _ (hc0' q)))
  have hΦ' (q : Q₀) (v : f₀.NormalSpace q hn) : Φ' q v = (√(c q))⁻¹ • Φ q v := by
    simp only [Φ', ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.smulLeft_apply_apply,
      Units.smul_mk0]
  have ha : ContMDiff J₀ 𝓘(ℝ) ∞ fun q ↦ (√(c q))⁻¹ := fun q ↦
    (((Real.contDiffAt_sqrt (hc0 q).ne').contMDiffAt.comp q (hcs q)).inv₀
      (Real.sqrt_pos.2 (hc0 q)).ne')
  have hΦs := SmoothEmbedding.contMDiff_totalSpace_smul hn hP₀ hP₁
    (fun q ↦ (Φ q : f₀.NormalSpace q hn →L[ℝ] f₁.NormalSpace (φ q) hn)) hΦ ha
  obtain ⟨U₀, U₁, ψ, hψ, hψσ⟩ := exists_symplectomorphism_opens hσ₀ hσ₁ h₀ h₁ φ hφ hn hP₀ hP₁ Φ'
    (by simpa only [hΦ', ContinuousLinearEquiv.coe_coe] using hΦs)
    (fun q v w ↦ by
      rw [hΦ', hΦ']
      exact symplecticNormalForm_inv_sqrt_smul h₀ h₁ hn _ (hc0 q) (hc q) v w)
  refine ⟨c, hcs, hc0, hc, U₀, U₁, ψ, fun q ↦ ?_, hψσ⟩
  obtain ⟨h, hψq, hdψ, hψΦ⟩ := hψ q
  exact ⟨h, hψq, hdψ, fun v ↦ (hψΦ v).trans (by rw [hΦ'])⟩

end TauCeti.SmoothTwoForm.IsNondegenerate

end
