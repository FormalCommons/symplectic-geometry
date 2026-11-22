/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Analysis.InnerProductSpace.HodgeStar.Kahler.Lefschetz
public import TauCeti.Geometry.Manifold.DifferentialForm.AlmostComplexType
public import TauCeti.Geometry.Manifold.DifferentialForm.Closed
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Leibniz
public import TauCeti.Geometry.Manifold.Riemannian.HodgeStar
public import TauCeti.Geometry.Manifold.TwoForm.Basic
public import SymplecticGeometry.Geometry.Manifold.Complex.Integrable
public import TauCeti.Geometry.Manifold.Riemannian.Codifferential
public import TauCeti.Geometry.Manifold.DeRham.Harmonic
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.PartialDiffeomorph
import SymplecticGeometry.Geometry.Manifold.Complex.KahlerCoordinates
import SymplecticGeometry.Geometry.Manifold.DeRham.Hodge.Chart
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.AlmostComplexType
import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.Metric
import TauCeti.Geometry.Symplectic.Finrank

/-!
# The Lefschetz operator on smooth forms, the Kähler identity, and `[Δ, 𝒥] = 0`

Let `σ` be a smooth two-form on a manifold `M`. This file defines the Lefschetz operator
`L α = α ∧ σ` on smooth real forms, which raises the degree by two, and proves its zeroth-order
properties.

When the manifold carries a metric with `⟪v, w⟫ = σ(v, J w)` for a smooth almost complex
structure `J`, then `σ` is at each point the Kähler form of `J`
(`TauCeti.SmoothTwoForm.val_eq_alternatingFormEquiv_kahlerForm`, in
`SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.Metric`), and so `L` is, at each
point, the Lefschetz operator `TauCeti.AlmostComplexStructure.lefschetz` of `J x` on the tangent
space. When `σ` is closed, `L` commutes with the exterior derivative. Finally, on an oriented
manifold with a smooth metric, the Hodge star commutes with the derivation
`ContMDiffSection.realAlternatingDerivation` of every fibrewise skew-adjoint endomorphism field, in
particular with the derivation `𝒥` of an orthogonal almost complex structure; this is
`Orientation.formHodgeStar_fderivCompContinuousLinearMap` at each point.

The next part proves the first-order Kähler identity `[L, d^*] = -[𝒥, d]` when `J` is integrable
and `σ` is closed. Both sides are compared at each point `x₀`, in an osculating holomorphic chart
`ψ` (`IsIntegrable.exists_partialDiffeomorph_fderiv_gramInChart_eq_zero`, in the namespace
`TauCeti.SmoothAlmostComplexStructure`), in which `J` is a constant `J₀` and the metric has
derivative zero at `ψ x₀`. Then the Hodge star in the chart
(`SymplecticGeometry.fderiv_hodgeStarInChart_eq_zero`) and `σ` read in the chart have derivative
zero at `ψ x₀` too, so at `x₀` every term is a constant-coefficient operator applied to the
derivative there of `α` read in the chart. That derivative, carried to the tangent space at `x₀`
along the differential of `ψ`, is a linear map `B` from the tangent space to forms, and the
identity becomes the linear Kähler identity for `B`,
`TauCeti.AlmostComplexStructure.lefschetz_smul_formHodgeStar_alternatizeUncurryFin_sub`.

From this identity, the Hodge Laplacian `Δ = d^* d + d d^*` commutes with `𝒥`. With
`P = [𝒥, d]` and `Q = [𝒥, d^*]`, the commutator `[𝒥, Δ]` is `(P d^* + d^* P) + (Q d + d Q)`. The
Kähler identity and `d^* d^* = 0` give `P d^* + d^* P = 0`, and the Hodge star carries
`Q d + d Q` to `P d^* + d^* P` in the complementary degree, since it commutes with `𝒥` and carries
`d` to `d^*` up to signs that cancel. In degree zero `𝒥` vanishes. In the top degree and in
dimension one only some of these terms occur; dimension one is excluded by `J`, which forces the
dimension to be even. The four conjugation formulas `⋆ d^* d = d d^* ⋆`, `⋆ d d^* = d^* d ⋆`,
and their versions with a derivation `𝒜` in the middle, follow the steps of the proof of
`TauCeti.SmoothForm.hodgeStar_hodgeLaplacian`.

## Main definitions

* `TauCeti.SmoothTwoForm.lefschetz`: the Lefschetz operator `α ↦ α ∧ σ` of a smooth two-form.

## Main results

* `TauCeti.SmoothTwoForm.val_lefschetz`: under `⟪v, w⟫ = σ(v, J w)`, the value of `L α` at `x`
  is the linear Lefschetz operator of `J x` applied to the value of `α`.
* `TauCeti.SmoothTwoForm.mextDerivₗ_lefschetz`: `d (L α) = L (d α)` for a closed `σ`.
* `TauCeti.SmoothForm.hodgeStar_realAlternatingDerivation`: `⋆ 𝒜 α = 𝒜 ⋆ α` for the
  derivation `𝒜` of a skew-adjoint endomorphism field.
* `TauCeti.SmoothTwoForm.lefschetz_codifferential_sub`: the first-order Kähler identity
  `L d^* α - d^* L α = -(𝒥 dα - d 𝒥 α)`, with its edge cases
  `TauCeti.SmoothTwoForm.lefschetz_codifferential_of_lt` in the top degrees `m - 1` and `m`, where
  `L α = 0`, and `TauCeti.SmoothTwoForm.codifferential_lefschetz` on functions.
* `TauCeti.SmoothTwoForm.symbolInChart_lefschetz`: where `σ` read in a chart has derivative zero,
  the derivative of `L β` read in the chart, carried to the tangent space by
  `TauCeti.symbolInChart`, is the linear Lefschetz operator applied to that of `β`.
* `TauCeti.SmoothForm.hodgeLaplacian_realAlternatingDerivation`: `Δ 𝒥 α = 𝒥 Δ α` under the
  hypotheses of the Kähler identity, and
  `TauCeti.SmoothForm.realAlternatingDerivation_mem_harmonicForms`: `𝒥` preserves harmonic forms.
* `TauCeti.SmoothForm.hodgeStar_injective`: the Hodge star of smooth forms is injective.
* `TauCeti.SmoothForm.hodgeStar_codifferential_mextDerivₗ`,
  `TauCeti.SmoothForm.hodgeStar_mextDerivₗ_codifferential` and their versions with
  `realAlternatingDerivation` between `d` and `d^*`: the Hodge star conjugates `d^* d` to `d d^*`.

## References

* [P. Griffiths, J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978],
  Chapter 0, §7.
* Daniel Huybrechts, *Complex Geometry: An Introduction*, Universitext, Springer, 2005,
  Section 3.1.
-/

public section

noncomputable section

open Bundle
open scoped Manifold ContDiff RealInnerProductSpace

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {k : ℕ}

namespace TauCeti

namespace SmoothTwoForm

variable (σ : SmoothTwoForm I M)

/-- The **Lefschetz operator** of a smooth two-form `σ`: the wedge `α ↦ α ∧ σ` on smooth real
`k`-forms. As `σ` has even degree, `α ∧ σ` is also `σ ∧ α`. -/
def lefschetz : SmoothForm I M ℝ k →ₗ[ℝ] SmoothForm I M ℝ (k + 2) :=
  SmoothForm.wedge.flip σ

/-- The Lefschetz operator of `σ` is the smooth wedge `SmoothForm.wedge` with `σ` on the right. -/
theorem lefschetz_def : σ.lefschetz (k := k) = SmoothForm.wedge.flip σ := (rfl)

/-- The Lefschetz operator is the wedge with `σ` on the right. -/
theorem lefschetz_apply (α : SmoothForm I M ℝ k) : σ.lefschetz α = SmoothForm.wedge α σ := by
  rw [lefschetz_def, LinearMap.flip_apply]

/-- The Lefschetz operator commutes with the exterior derivative when `σ` is closed:
`d (α ∧ σ) = dα ∧ σ`. -/
theorem mextDerivₗ_lefschetz (hσ : σ.IsClosed) (α : SmoothForm I M ℝ k) :
    mextDerivₗ I (k + 2) (σ.lefschetz α) = σ.lefschetz (mextDerivₗ I k α) := by
  rw [lefschetz_apply, lefschetz_apply, SmoothForm.mextDerivₗ_wedge,
    (SmoothForm.isClosed_iff_mextDerivₗ_eq_zero σ).1 hσ, map_zero, map_zero, smul_zero, add_zero,
    LinearEquiv.cast_apply, cast_eq]

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [FiniteDimensional ℝ E] {σ}
  {J : SmoothAlmostComplexStructure I M}

/-- If the metric is `⟪v, w⟫ = σ(v, J w)`, then the value at `x` of the Lefschetz operator of `σ`
is the Lefschetz operator `TauCeti.AlmostComplexStructure.lefschetz` of `J x` on the tangent
space, applied to the value of `α`. -/
theorem val_lefschetz (hg : ∀ x (v w : TangentSpace I x), ⟪v, w⟫ = σ.eval₂ x v (J x w))
    (α : SmoothForm I M ℝ k) (x : M) :
    (σ.lefschetz α).val x =
      (letI : FiniteDimensional ℝ (TangentSpace I x) :=
        VectorBundle.finiteDimensional ℝ E (TangentSpace I) x
       (J.almostComplexStructureAt x).lefschetz (α.val x)) := by
  rw [lefschetz_apply, SmoothForm.coe_wedge_apply, AlmostComplexStructure.lefschetz_apply,
    val_eq_alternatingFormEquiv_kahlerForm hg x]

end SmoothTwoForm

end TauCeti

namespace TauCeti.SmoothForm

variable [FiniteDimensional ℝ E] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] {m l : ℕ}

/-- **The Hodge star commutes with skew-adjoint derivations**: on an oriented manifold with a
smooth metric, for an endomorphism field `A` that is skew-adjoint at every point,
`⋆ 𝒜 α = 𝒜 ⋆ α`, where `𝒜` is the derivation `ContMDiffSection.realAlternatingDerivation` of `A`
on smooth real forms. For an orthogonal almost complex structure `J`, the field
`J.toEndomorphism` is skew-adjoint, and `𝒜` is the derivation `𝒥`. -/
theorem hodgeStar_realAlternatingDerivation (o : Manifold.Orientation I M (Fin m))
    (hkl : k + l = m)
    {A : ContMDiffSection I (E →L[ℝ] E) ∞ fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x}
    (hA : ∀ x (u w : TangentSpace I x), ⟪A x u, w⟫ = -⟪u, A x w⟫) (α : SmoothForm I M ℝ k) :
    hodgeStar o hkl (A.realAlternatingDerivation α) =
      A.realAlternatingDerivation (hodgeStar o hkl α) := by
  refine Subtype.ext (funext fun x ↦ ?_)
  let _ := o.fact_finrank_tangentSpace x
  simp only [coe_hodgeStar, RoughForm.hodgeStar_apply,
    ContMDiffSection.coe_realAlternatingDerivation]
  exact (o.orientationAt x).formHodgeStar_fderivCompContinuousLinearMap _ (hA x) _

/-- The Hodge star of smooth forms is injective, since `⋆⋆` is a sign. -/
theorem hodgeStar_injective (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m) :
    Function.Injective (hodgeStar o hkl) := fun α β h ↦ by
  have := congrArg (hodgeStar o (show l + k = m by omega)) h
  rwa [hodgeStar_hodgeStar, hodgeStar_hodgeStar,
    smul_right_inj (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero))] at this

/-- The Hodge star carries `d*d` to `dd*`: `⋆ d* dβ = d d* ⋆β` for a `k`-form `β`. -/
theorem hodgeStar_codifferential_mextDerivₗ (o : Manifold.Orientation I M (Fin m))
    (hkl : k + 1 + l = m) (hkl' : k + (l + 1) = m) (hlk : l + 1 + k = m)
    (β : SmoothForm I M ℝ k) :
    hodgeStar o hkl' (codifferential o hkl (mextDerivₗ I k β)) =
      mextDerivₗ I l (codifferential o hlk (hodgeStar o hkl' β)) := by
  rw [hodgeStar_codifferential o hkl hkl', hodgeStar_mextDeriv o hkl' hlk hkl, map_smul,
    smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]

/-- The Hodge star carries `dd*` to `d*d`: `⋆ d d*α = d* d ⋆α` for a `(k + 1)`-form `α`. -/
theorem hodgeStar_mextDerivₗ_codifferential (o : Manifold.Orientation I M (Fin m))
    (hkl : k + 1 + l = m) (hkl' : k + (l + 1) = m) (hlk : l + 1 + k = m)
    (α : SmoothForm I M ℝ (k + 1)) :
    hodgeStar o hkl (mextDerivₗ I k (codifferential o hkl α)) =
      codifferential o hlk (mextDerivₗ I l (hodgeStar o hkl α)) := by
  rw [hodgeStar_mextDeriv o hkl' hlk hkl, hodgeStar_codifferential o hkl hkl', map_smul,
    smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]

/-- For the derivation `𝒜` of a skew-adjoint endomorphism field, the Hodge star carries `d* 𝒜 d`
to `d 𝒜 d*`: `⋆ d* 𝒜 dβ = d 𝒜 d* ⋆β` for a `k`-form `β`. -/
theorem hodgeStar_codifferential_realAlternatingDerivation_mextDerivₗ
    (o : Manifold.Orientation I M (Fin m)) (hkl : k + 1 + l = m) (hkl' : k + (l + 1) = m)
    (hlk : l + 1 + k = m)
    {A : ContMDiffSection I (E →L[ℝ] E) ∞ fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x}
    (hA : ∀ x (u w : TangentSpace I x), ⟪A x u, w⟫ = -⟪u, A x w⟫) (β : SmoothForm I M ℝ k) :
    hodgeStar o hkl' (codifferential o hkl (A.realAlternatingDerivation (mextDerivₗ I k β))) =
      mextDerivₗ I l (A.realAlternatingDerivation (codifferential o hlk (hodgeStar o hkl' β))) := by
  rw [hodgeStar_codifferential o hkl hkl', hodgeStar_realAlternatingDerivation o hkl hA,
    hodgeStar_mextDeriv o hkl' hlk hkl, map_smul, map_smul, smul_smul, ← mul_pow, neg_one_mul,
    neg_neg, one_pow, one_smul]

/-- For the derivation `𝒜` of a skew-adjoint endomorphism field, the Hodge star carries `d 𝒜 d*`
to `d* 𝒜 d`: `⋆ d 𝒜 d*α = d* 𝒜 d ⋆α` for a `(k + 1)`-form `α`. -/
theorem hodgeStar_mextDerivₗ_realAlternatingDerivation_codifferential
    (o : Manifold.Orientation I M (Fin m)) (hkl : k + 1 + l = m) (hkl' : k + (l + 1) = m)
    (hlk : l + 1 + k = m)
    {A : ContMDiffSection I (E →L[ℝ] E) ∞ fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x}
    (hA : ∀ x (u w : TangentSpace I x), ⟪A x u, w⟫ = -⟪u, A x w⟫)
    (α : SmoothForm I M ℝ (k + 1)) :
    hodgeStar o hkl (mextDerivₗ I k (A.realAlternatingDerivation (codifferential o hkl α))) =
      codifferential o hlk (A.realAlternatingDerivation (mextDerivₗ I l (hodgeStar o hkl α))) := by
  rw [hodgeStar_mextDeriv o hkl' hlk hkl, hodgeStar_realAlternatingDerivation o hkl' hA,
    hodgeStar_codifferential o hkl hkl', map_smul, map_smul, smul_smul, ← mul_pow, neg_one_mul,
    neg_neg, one_pow, one_smul]

end TauCeti.SmoothForm

/-! ### The first-order Kähler identity -/

namespace TauCeti.SmoothTwoForm

open _root_.ContinuousAlternatingMap Module SymplecticGeometry

variable {m j l l' : ℕ} [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- Where the reading of `σ` in the chart has derivative zero, `symbolInChart` carries `L β` to
the wedge of `symbolInChart` of `β` with `σ`. -/
theorem symbolInChart_lefschetz_apply (ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞)
    (σ : SmoothTwoForm I M) (β : SmoothForm I M ℝ j) {y : E} (hy : y ∈ ψ.target)
    (hσ : fderiv ℝ (F := E [⋀^Fin 2]→L[ℝ] ℝ) (mpullback 𝓘(ℝ, E) I ψ.symm σ.val) y = 0)
    (v : TangentSpace I (ψ.symm y)) :
    symbolInChart ψ (σ.lefschetz β).val y v =
      (symbolInChart ψ β.val y v).wedge (σ.val (ψ.symm y)) := by
  -- The step on `E`, for the value `b` and derivative `D` of `β` read in the chart, the value `Ω`
  -- and derivative `D₂` of `σ`, and the derivative `D'` of `β ∧ σ`.
  have key (T : TangentSpace I (ψ.symm y) →L[ℝ] E) (Ω : E [⋀^Fin 2]→L[ℝ] ℝ)
      (hT : Ω.compContinuousLinearMap T = σ.val (ψ.symm y)) (b : E [⋀^Fin j]→L[ℝ] ℝ)
      (D : E →L[ℝ] E [⋀^Fin j]→L[ℝ] ℝ) (D₂ : E →L[ℝ] E [⋀^Fin 2]→L[ℝ] ℝ) (hD₂ : D₂ = 0)
      (D' : E →L[ℝ] E [⋀^Fin (j + 2)]→L[ℝ] ℝ)
      (hD : ∀ u, D' u = (D u).wedge Ω + b.wedge (D₂ u)) :
      (D' (T v)).compContinuousLinearMap T =
        ((D (T v)).compContinuousLinearMap T).wedge (σ.val (ψ.symm y)) := by
    rw [hD, hD₂, zero_apply, wedge_zero_right, add_zero, ← hT, wedge_compContinuousLinearMap]
  rw [symbolInChart_apply, symbolInChart_apply]
  refine key _ _ (mpullback_symm_compContinuousLinearMap_mfderiv ψ (by simp) σ.val hy)
    (mpullback 𝓘(ℝ, E) I ψ.symm β.val y) _ _ hσ _ fun u ↦ ?_
  rw [lefschetz_apply]
  exact fderiv_mpullback_symm_wedge_apply ψ β σ hy u

variable [FiniteDimensional ℝ E] {σ : SmoothTwoForm I M} {J : SmoothAlmostComplexStructure I M}

/-- Under `⟪v, w⟫ = σ(v, J w)`, where the reading of `σ` in the chart has derivative zero,
`symbolInChart` carries `L β` to the Lefschetz operator of `J` at `ψ.symm y` composed with
`symbolInChart` of `β`. -/
theorem symbolInChart_lefschetz
    (hg : ∀ x (v w : TangentSpace I x), ⟪v, w⟫ = σ.eval₂ x v (J x w))
    (ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞) (β : SmoothForm I M ℝ j) {y : E}
    (hy : y ∈ ψ.target)
    (hσ : fderiv ℝ (F := E [⋀^Fin 2]→L[ℝ] ℝ) (mpullback 𝓘(ℝ, E) I ψ.symm σ.val) y = 0) :
    symbolInChart ψ (σ.lefschetz β).val y =
      (letI : FiniteDimensional ℝ (TangentSpace I (ψ.symm y)) :=
        VectorBundle.finiteDimensional ℝ E (TangentSpace I) (ψ.symm y)
       (J.almostComplexStructureAt (ψ.symm y)).lefschetz ∘L symbolInChart ψ β.val y) := by
  ext1 v
  rw [symbolInChart_lefschetz_apply ψ σ β hy hσ v, ContinuousLinearMap.comp_apply,
    AlmostComplexStructure.lefschetz_apply, val_eq_alternatingFormEquiv_kahlerForm hg]

/-- To prove that two smooth forms agree, it suffices to compare them at the points of osculating
holomorphic charts at which the metric in the chart has derivative zero. -/
private theorem eq_of_forall_osculating
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] (hJ : J.IsIntegrable)
    (hσ : σ.IsClosed) (hg : ∀ x (v w : TangentSpace I x), ⟪v, w⟫ = σ.eval₂ x v (J x w))
    {α β : SmoothForm I M ℝ j}
    (h : ∀ (ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞) (J₀ : AlmostComplexStructure E),
      (∀ p ∈ ψ.target, ∀ w : E, J.chartPushforward ψ.toOpenPartialHomeomorph p w = J₀ w) →
      ∀ y ∈ ψ.target, fderiv ℝ (gramInChart ψ) y = 0 → α.val (ψ.symm y) = β.val (ψ.symm y)) :
    α = β := by
  refine Subtype.ext (funext fun x₀ ↦ ?_)
  obtain ⟨ψ, J₀, hx₀, hψ, hgr⟩ :=
    hJ.exists_partialDiffeomorph_fderiv_gramInChart_eq_zero hσ hg x₀
  have hx : ψ.symm.toPartialEquiv (ψ.toPartialEquiv x₀) = x₀ := ψ.left_inv hx₀
  have := h ψ J₀ hψ (ψ x₀) (ψ.map_source hx₀) hgr
  rwa [hx] at this

variable [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- **The first-order Kähler identity** `[L, d^*] = -[𝒥, d]`: let `J` be an integrable almost
complex structure, `σ` a closed two-form, and let the metric be `⟪v, w⟫ = σ(v, J w)`, so that `σ`
is the Kähler form. On an oriented manifold of dimension `m`, for smooth real `(k + 1)`-forms `α`,
`L d^* α - d^* L α = -(𝒥 dα - d 𝒥 α)`, where `L` is the Lefschetz operator of `σ`, `d^*` Tau Ceti's
`codifferential` and `𝒥` the derivation `J.toEndomorphism.realAlternatingDerivation`. The
hypotheses `hkl` and `hkl'` are those of the codifferential in degrees `k + 1` and `k + 3`; when
`m < k + 3`, see `lefschetz_codifferential_of_lt`. -/
theorem lefschetz_codifferential_sub (o : Manifold.Orientation I M (Fin m))
    (hJ : J.IsIntegrable) (hσ : σ.IsClosed)
    (hg : ∀ x (v w : TangentSpace I x), ⟪v, w⟫ = σ.eval₂ x v (J x w))
    (hkl : k + 1 + l = m) (hkl' : k + 2 + 1 + l' = m) (α : SmoothForm I M ℝ (k + 1)) :
    σ.lefschetz (SmoothForm.codifferential o hkl α) -
        SmoothForm.codifferential o hkl' (σ.lefschetz α) =
      -(J.toEndomorphism.realAlternatingDerivation (mextDerivₗ I (k + 1) α) -
        mextDerivₗ I (k + 1) (J.toEndomorphism.realAlternatingDerivation α)) := by
  refine eq_of_forall_osculating hJ hσ hg fun ψ J₀ hψ y hy hgr ↦ ?_
  let _ := o.fact_finrank_tangentSpace (ψ.symm y)
  let _ : FiniteDimensional ℝ (TangentSpace I (ψ.symm y)) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace I) (ψ.symm y)
  have hm := (o.fact_finrank_tangentSpace (ψ.symm y)).out
  simp only [Submodule.coe_sub, Submodule.coe_neg, Pi.sub_apply, Pi.neg_apply]
  rw [val_lefschetz hg, val_codifferential_symm_of_fderiv_gramInChart_eq_zero o ψ hkl (by omega)
      α hy hgr,
    val_codifferential_symm_of_fderiv_gramInChart_eq_zero o ψ hkl' (by omega) (σ.lefschetz α) hy
      hgr,
    ContMDiffSection.coe_realAlternatingDerivation]
  beta_reduce
  rw [val_mextDerivₗ_symm_eq_alternatizeUncurryFin_symbolInChart ψ α hy,
    val_mextDerivₗ_symm_eq_alternatizeUncurryFin_symbolInChart ψ _ hy,
    symbolInChart_lefschetz hg ψ α hy
      (fderiv_mpullback_symm_eq_zero_of_fderiv_gramInChart_eq_zero hg ψ hψ hy hgr)]
  convert AlmostComplexStructure.lefschetz_smul_formHodgeStar_alternatizeUncurryFin_sub
    (SmoothAlmostComplexStructure.inner_almostComplexStructureAt_apply_apply hg (ψ.symm y))
    (o.orientationAt (ψ.symm y))
    (l := l) (l' := l') (by omega) (by omega) (by omega) (by omega) (symbolInChart ψ α.val y)
    using 4
  · rw [hm]
  · rw [formHodgeStarCLM_apply, formHodgeStarCLM_def]
  · rw [hm]
  · rw [formHodgeStarCLM_apply, formHodgeStarCLM_def]
  · ext u
    simp
  · ext1 v
    exact (symbolInChart_realAlternatingDerivation_apply J ψ
      (A₀ := J₀.toLinearMap.toContinuousLinearMap) (by simpa using hψ) α hy v).trans
      (congrArg _ (by ext u; simp))

/-- **The first-order Kähler identity in the top two degrees**: under the hypotheses of
`lefschetz_codifferential_sub`, if `m < k + 3`, that is if `α` has degree `m - 1` or `m`, then `L`
vanishes on the `(k + 1)`-forms and the identity reads `L d^* α = -(𝒥 dα - d 𝒥 α)`. -/
theorem lefschetz_codifferential_of_lt (o : Manifold.Orientation I M (Fin m))
    (hJ : J.IsIntegrable) (hσ : σ.IsClosed)
    (hg : ∀ x (v w : TangentSpace I x), ⟪v, w⟫ = σ.eval₂ x v (J x w))
    (hkl : k + 1 + l = m) (hk : m < k + 3) (α : SmoothForm I M ℝ (k + 1)) :
    σ.lefschetz (SmoothForm.codifferential o hkl α) =
      -(J.toEndomorphism.realAlternatingDerivation (mextDerivₗ I (k + 1) α) -
        mextDerivₗ I (k + 1) (J.toEndomorphism.realAlternatingDerivation α)) := by
  refine eq_of_forall_osculating hJ hσ hg fun ψ J₀ hψ y hy hgr ↦ ?_
  let _ := o.fact_finrank_tangentSpace (ψ.symm y)
  let _ : FiniteDimensional ℝ (TangentSpace I (ψ.symm y)) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace I) (ψ.symm y)
  have hm := (o.fact_finrank_tangentSpace (ψ.symm y)).out
  simp only [Submodule.coe_sub, Submodule.coe_neg, Pi.sub_apply, Pi.neg_apply]
  rw [val_lefschetz hg, val_codifferential_symm_of_fderiv_gramInChart_eq_zero o ψ hkl (by omega)
      α hy hgr,
    ContMDiffSection.coe_realAlternatingDerivation]
  beta_reduce
  rw [val_mextDerivₗ_symm_eq_alternatizeUncurryFin_symbolInChart ψ α hy,
    val_mextDerivₗ_symm_eq_alternatizeUncurryFin_symbolInChart ψ _ hy]
  convert AlmostComplexStructure.lefschetz_smul_formHodgeStar_alternatizeUncurryFin_of_lt
    (SmoothAlmostComplexStructure.inner_almostComplexStructureAt_apply_apply hg (ψ.symm y))
    (o.orientationAt (ψ.symm y))
    (l := l) (by omega) (by omega) (by omega) (symbolInChart ψ α.val y) using 4
  · rw [hm]
  · rw [formHodgeStarCLM_apply, formHodgeStarCLM_def]
  · ext u
    simp
  · ext1 v
    exact (symbolInChart_realAlternatingDerivation_apply J ψ
      (A₀ := J₀.toLinearMap.toContinuousLinearMap) (by simpa using hψ) α hy v).trans
      (congrArg _ (by ext u; simp))

/-- **The first-order Kähler identity on functions**: under the hypotheses of
`lefschetz_codifferential_sub`, for a smooth `0`-form `f`, `d^* (L f) = 𝒥 df`. This is that
identity one degree lower, where `d^* f` is not defined and `𝒥 f` vanishes. The hypothesis `hkl`
is that of the codifferential in degree `2`. -/
theorem codifferential_lefschetz (o : Manifold.Orientation I M (Fin m))
    (hJ : J.IsIntegrable) (hσ : σ.IsClosed)
    (hg : ∀ x (v w : TangentSpace I x), ⟪v, w⟫ = σ.eval₂ x v (J x w))
    (hkl : 1 + 1 + l = m) (f : SmoothForm I M ℝ 0) :
    SmoothForm.codifferential o hkl (σ.lefschetz f) =
      J.toEndomorphism.realAlternatingDerivation (mextDerivₗ I 0 f) := by
  refine eq_of_forall_osculating hJ hσ hg fun ψ J₀ hψ y hy hgr ↦ ?_
  let _ := o.fact_finrank_tangentSpace (ψ.symm y)
  let _ : FiniteDimensional ℝ (TangentSpace I (ψ.symm y)) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace I) (ψ.symm y)
  have hm := (o.fact_finrank_tangentSpace (ψ.symm y)).out
  rw [val_codifferential_symm_of_fderiv_gramInChart_eq_zero o ψ hkl (by omega) (σ.lefschetz f) hy
      hgr,
    ContMDiffSection.coe_realAlternatingDerivation]
  beta_reduce
  rw [val_mextDerivₗ_symm_eq_alternatizeUncurryFin_symbolInChart ψ f hy,
    symbolInChart_lefschetz hg ψ f hy
      (fderiv_mpullback_symm_eq_zero_of_fderiv_gramInChart_eq_zero hg ψ hψ hy hgr)]
  convert AlmostComplexStructure.smul_formHodgeStar_alternatizeUncurryFin_lefschetz_fin_zero
    (SmoothAlmostComplexStructure.inner_almostComplexStructureAt_apply_apply hg (ψ.symm y))
    (o.orientationAt (ψ.symm y))
    (l := l) (by omega) (by omega) (symbolInChart ψ f.val y) using 3
  · rw [hm]
  · rw [formHodgeStarCLM_apply, formHodgeStarCLM_def]
  · ext u
    simp

/-! ### The Hodge Laplacian commutes with `𝒥` -/

omit [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- A nonempty manifold of dimension `m` with an almost complex structure has `m` even. -/
private theorem even_of_orientation (o : Manifold.Orientation I M (Fin m))
    (J : SmoothAlmostComplexStructure I M) (x : M) : Even m := by
  let _ : FiniteDimensional ℝ (TangentSpace I x) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace I) x
  rw [← (o.fact_finrank_tangentSpace x).out]
  exact (J.almostComplexStructureAt x).even_finrank_real

/-- The Kähler identity at `d^* α`: `𝒥 d d^* α - d 𝒥 d^* α = d^* L d^* α`, as `d^* d^* = 0`. -/
private theorem realAlternatingDerivation_mextDerivₗ_codifferential_sub
    (o : Manifold.Orientation I M (Fin m)) (hJ : J.IsIntegrable) (hσ : σ.IsClosed)
    (hg : ∀ x (v w : TangentSpace I x), ⟪v, w⟫ = σ.eval₂ x v (J x w))
    (hkl : k + 1 + l = m) (hkl' : k + 1 + 1 + l' = m) (α : SmoothForm I M ℝ (k + 1)) :
    J.toEndomorphism.realAlternatingDerivation
          (mextDerivₗ I k (SmoothForm.codifferential o hkl α)) -
        mextDerivₗ I k
          (J.toEndomorphism.realAlternatingDerivation (SmoothForm.codifferential o hkl α)) =
      SmoothForm.codifferential o hkl' (σ.lefschetz (SmoothForm.codifferential o hkl α)) := by
  rcases k with _ | k
  · rw [ContMDiffSection.realAlternatingDerivation_fin_zero, _root_.map_zero, sub_zero]
    exact (codifferential_lefschetz o hJ hσ hg (by omega) _).symm
  · have := lefschetz_codifferential_sub o hJ hσ hg (l := l + 1) (l' := l') (by omega) (by omega)
      (SmoothForm.codifferential o hkl α)
    rw [SmoothForm.codifferential_codifferential, _root_.map_zero, zero_sub, neg_inj] at this
    exact this.symm

/-- The codifferential of the Kähler identity: `d^* (𝒥 dα - d 𝒥 α) = -d^* L d^* α`, as
`d^* d^* = 0`. -/
private theorem codifferential_realAlternatingDerivation_mextDerivₗ_sub
    (o : Manifold.Orientation I M (Fin m)) (hJ : J.IsIntegrable) (hσ : σ.IsClosed)
    (hg : ∀ x (v w : TangentSpace I x), ⟪v, w⟫ = σ.eval₂ x v (J x w))
    (hkl : k + 1 + l = m) (hkl' : k + 1 + 1 + l' = m) (α : SmoothForm I M ℝ (k + 1)) :
    SmoothForm.codifferential o hkl'
        (J.toEndomorphism.realAlternatingDerivation (mextDerivₗ I (k + 1) α) -
          mextDerivₗ I (k + 1) (J.toEndomorphism.realAlternatingDerivation α)) =
      -SmoothForm.codifferential o hkl' (σ.lefschetz (SmoothForm.codifferential o hkl α)) := by
  rcases l' with _ | l'
  · have hP := neg_eq_iff_eq_neg.1
      (lefschetz_codifferential_of_lt o hJ hσ hg hkl (by omega) α).symm
    rw [hP, map_neg]
  · have hP := neg_eq_iff_eq_neg.1
      (lefschetz_codifferential_sub o hJ hσ hg hkl (l' := l') (by omega) α).symm
    rw [hP, map_neg, map_sub, SmoothForm.codifferential_codifferential, sub_zero]

/-- `[𝒥, d] d^* + d^* [𝒥, d] = 0` on `(k + 1)`-forms below the top degree. -/
private theorem commutator_mextDerivₗ_codifferential_add
    (o : Manifold.Orientation I M (Fin m)) (hJ : J.IsIntegrable) (hσ : σ.IsClosed)
    (hg : ∀ x (v w : TangentSpace I x), ⟪v, w⟫ = σ.eval₂ x v (J x w))
    (hkl : k + 1 + l = m) (hkl' : k + 1 + 1 + l' = m) (α : SmoothForm I M ℝ (k + 1)) :
    J.toEndomorphism.realAlternatingDerivation
            (mextDerivₗ I k (SmoothForm.codifferential o hkl α)) -
          mextDerivₗ I k
            (J.toEndomorphism.realAlternatingDerivation (SmoothForm.codifferential o hkl α)) +
        (SmoothForm.codifferential o hkl'
            (J.toEndomorphism.realAlternatingDerivation (mextDerivₗ I (k + 1) α)) -
          SmoothForm.codifferential o hkl'
            (mextDerivₗ I (k + 1) (J.toEndomorphism.realAlternatingDerivation α))) = 0 := by
  rw [← map_sub, realAlternatingDerivation_mextDerivₗ_codifferential_sub o hJ hσ hg hkl hkl',
    codifferential_realAlternatingDerivation_mextDerivₗ_sub o hJ hσ hg hkl hkl', add_neg_cancel]

/-- `[𝒥, d] d^* = 0` on forms of the top degree. -/
private theorem commutator_mextDerivₗ_codifferential_of_top
    (o : Manifold.Orientation I M (Fin m)) (hJ : J.IsIntegrable) (hσ : σ.IsClosed)
    (hg : ∀ x (v w : TangentSpace I x), ⟪v, w⟫ = σ.eval₂ x v (J x w))
    (hkl : k + 1 + 0 = m) (α : SmoothForm I M ℝ (k + 1)) :
    J.toEndomorphism.realAlternatingDerivation
          (mextDerivₗ I k (SmoothForm.codifferential o hkl α)) -
        mextDerivₗ I k
          (J.toEndomorphism.realAlternatingDerivation (SmoothForm.codifferential o hkl α)) = 0 := by
  rcases k with _ | k
  · refine Subtype.ext (funext fun x ↦ absurd (even_of_orientation o J x) ?_)
    rw [← hkl]
    exact Nat.not_even_one
  · have := lefschetz_codifferential_of_lt o hJ hσ hg (l := 1) (by omega) (by omega)
      (SmoothForm.codifferential o hkl α)
    rwa [SmoothForm.codifferential_codifferential, _root_.map_zero, eq_comm, neg_eq_zero] at this

/-- `d^* [𝒥, d] = 0` on functions. -/
private theorem codifferential_commutator_mextDerivₗ_of_fin_zero
    (o : Manifold.Orientation I M (Fin m)) (hJ : J.IsIntegrable) (hσ : σ.IsClosed)
    (hg : ∀ x (v w : TangentSpace I x), ⟪v, w⟫ = σ.eval₂ x v (J x w))
    (hkl : 0 + 1 + l = m) (f : SmoothForm I M ℝ 0) :
    SmoothForm.codifferential o hkl
          (J.toEndomorphism.realAlternatingDerivation (mextDerivₗ I 0 f)) -
        SmoothForm.codifferential o hkl
          (mextDerivₗ I 0 (J.toEndomorphism.realAlternatingDerivation f)) = 0 := by
  rw [ContMDiffSection.realAlternatingDerivation_fin_zero, _root_.map_zero, _root_.map_zero,
    sub_zero]
  rcases l with _ | l
  · refine Subtype.ext (funext fun x ↦ absurd (even_of_orientation o J x) ?_)
    rw [← hkl]
    exact Nat.not_even_one
  · rw [← codifferential_lefschetz o hJ hσ hg (l := l) (by omega) f]
    exact SmoothForm.codifferential_codifferential o hkl _ _

end TauCeti.SmoothTwoForm

namespace TauCeti.SmoothForm

open SmoothTwoForm

variable [FiniteDimensional ℝ E] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] {m l : ℕ}
  {σ : SmoothTwoForm I M} {J : SmoothAlmostComplexStructure I M}

/-- **The Hodge Laplacian commutes with `𝒥`**: let `J` be an integrable almost complex structure,
`σ` a closed two-form, and let the metric be `⟪v, w⟫ = σ(v, J w)`. On an oriented manifold of
dimension `m`, for smooth real `k`-forms `α`, `Δ 𝒥 α = 𝒥 Δ α`, where `Δ` is Tau Ceti's Hodge
Laplacian `d^* d + d d^*` and `𝒥` the derivation `J.toEndomorphism.realAlternatingDerivation`. -/
theorem hodgeLaplacian_realAlternatingDerivation (o : Manifold.Orientation I M (Fin m))
    (hJ : J.IsIntegrable) (hσ : σ.IsClosed)
    (hg : ∀ x (v w : TangentSpace I x), ⟪v, w⟫ = σ.eval₂ x v (J x w))
    (hkl : k + l = m) (α : SmoothForm I M ℝ k) :
    hodgeLaplacian o hkl (J.toEndomorphism.realAlternatingDerivation α) =
      J.toEndomorphism.realAlternatingDerivation (hodgeLaplacian o hkl α) := by
  have hA := SmoothAlmostComplexStructure.inner_apply_left_eq_neg hg
  rcases k with _ | k <;> rcases l with _ | l
  · simp
  · simp
  · -- In the top degree, `Δ = d d^*`.
    rw [hodgeLaplacian_add_one_zero, hodgeLaplacian_add_one_zero]
    have hX := sub_eq_zero.1 (commutator_mextDerivₗ_codifferential_of_top o hJ hσ hg hkl α)
    have hY : mextDerivₗ I k (J.toEndomorphism.realAlternatingDerivation (codifferential o hkl α)) -
        mextDerivₗ I k (codifferential o hkl (J.toEndomorphism.realAlternatingDerivation α)) =
          0 := by
      refine (injective_iff_map_eq_zero (hodgeStar o hkl)).1 (hodgeStar_injective o hkl) _ ?_
      rw [map_sub, hodgeStar_mextDerivₗ_realAlternatingDerivation_codifferential o hkl (by omega)
          (by omega) hA,
        hodgeStar_mextDerivₗ_codifferential o hkl (by omega) (by omega),
        hodgeStar_realAlternatingDerivation o hkl hA]
      exact codifferential_commutator_mextDerivₗ_of_fin_zero o hJ hσ hg _ _
    rw [hX, sub_eq_zero.1 hY]
  · -- In the other degrees, `Δ = d^* d + d d^*`.
    rw [hodgeLaplacian_add_one_add_one o hkl (by omega),
      hodgeLaplacian_add_one_add_one o hkl (by omega), map_add]
    have hX := commutator_mextDerivₗ_codifferential_add o hJ hσ hg hkl (l' := l) (by omega) α
    have hY : J.toEndomorphism.realAlternatingDerivation
            (codifferential o (show k + 1 + 1 + l = m by omega) (mextDerivₗ I (k + 1) α)) -
          codifferential o (show k + 1 + 1 + l = m by omega)
            (J.toEndomorphism.realAlternatingDerivation (mextDerivₗ I (k + 1) α)) +
        (mextDerivₗ I k (J.toEndomorphism.realAlternatingDerivation (codifferential o hkl α)) -
          mextDerivₗ I k (codifferential o hkl (J.toEndomorphism.realAlternatingDerivation α))) =
          0 := by
      refine (injective_iff_map_eq_zero (hodgeStar o hkl)).1 (hodgeStar_injective o hkl) _ ?_
      rw [map_add, map_sub, map_sub, hodgeStar_realAlternatingDerivation o hkl hA,
        hodgeStar_codifferential_mextDerivₗ o _ hkl (by omega),
        hodgeStar_codifferential_realAlternatingDerivation_mextDerivₗ o _ hkl (by omega) hA,
        hodgeStar_mextDerivₗ_realAlternatingDerivation_codifferential o hkl (by omega)
          (by omega) hA,
        hodgeStar_mextDerivₗ_codifferential o hkl (by omega) (by omega),
        hodgeStar_realAlternatingDerivation o hkl hA]
      exact commutator_mextDerivₗ_codifferential_add o hJ hσ hg _ (l' := k) (by omega) _
    have := congrArg₂ (· + ·) hX hY
    rw [add_zero] at this
    rw [← sub_eq_zero, ← neg_eq_zero, ← this]
    abel

/-- Under the hypotheses of `hodgeLaplacian_realAlternatingDerivation`, the derivation `𝒥` maps
harmonic forms to harmonic forms. -/
theorem realAlternatingDerivation_mem_harmonicForms (o : Manifold.Orientation I M (Fin m))
    (hJ : J.IsIntegrable) (hσ : σ.IsClosed)
    (hg : ∀ x (v w : TangentSpace I x), ⟪v, w⟫ = σ.eval₂ x v (J x w))
    (hkl : k + l = m) {α : SmoothForm I M ℝ k} (hα : α ∈ harmonicForms o hkl) :
    J.toEndomorphism.realAlternatingDerivation α ∈ harmonicForms o hkl := by
  rw [mem_harmonicForms] at hα ⊢
  rw [hodgeLaplacian_realAlternatingDerivation o hJ hσ hg, hα, map_zero]

end TauCeti.SmoothForm

end
