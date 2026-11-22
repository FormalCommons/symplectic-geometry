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
import SymplecticGeometry.Analysis.Normed.Module.Alternating.Derivation
import SymplecticGeometry.Geometry.Manifold.Complex.KahlerCoordinates
import SymplecticGeometry.Geometry.Manifold.DeRham.Hodge.Chart
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.AlmostComplexType
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.PartialDiffeomorph
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.Chart
import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.Metric

/-!
# The Lefschetz operator on smooth forms, and the Hodge star against `𝒥`

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

The last part proves the first-order Kähler identity `[L, d^*] = -[𝒥, d]` when `J` is integrable
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

The proof of `TauCeti.SmoothTwoForm.inner_almostComplexStructureAt_apply_apply` is that of Tau
Ceti's private `TauCeti.inner_apply_apply_of_inner_eq`
(`Geometry/Symplectic/Manifold/AlmostComplex/Metric.lean`), with the hypothesis on the metric
stated through the value of `σ`.

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
  `TauCeti.SmoothTwoForm.lefschetz_codifferential_of_lt` above the middle degrees and
  `TauCeti.SmoothTwoForm.codifferential_lefschetz` on functions.

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

end TauCeti.SmoothForm

/-! ### The first-order Kähler identity -/

namespace TauCeti.SmoothTwoForm

open _root_.ContinuousAlternatingMap Module SymplecticGeometry

variable {m j l l' : ℕ}

/-- The derivative at `y` of the reading of `φ` in the chart `ψ`, transported to the tangent space
at `ψ.symm y` along the differential of `ψ`. At `ψ.symm y`, `d φ` is its alternation, and the
codifferential is computed from it where the metric in the chart has derivative zero. -/
private def symbolInChart (ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞) (φ : SmoothForm I M ℝ j)
    (y : E) : TangentSpace I (ψ.symm y) →L[ℝ] TangentSpace I (ψ.symm y) [⋀^Fin j]→L[ℝ] ℝ :=
  compContinuousLinearMapCLM
      (mfderiv I 𝓘(ℝ, E) ψ (ψ.symm y) : TangentSpace I (ψ.symm y) →L[ℝ] E) ∘L
    fderiv ℝ (F := E [⋀^Fin j]→L[ℝ] ℝ) (mpullback 𝓘(ℝ, E) I ψ.symm φ.val) y ∘L
      (mfderiv I 𝓘(ℝ, E) ψ (ψ.symm y) : TangentSpace I (ψ.symm y) →L[ℝ] E)

private theorem symbolInChart_apply (ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞)
    (φ : SmoothForm I M ℝ j) (y : E) (v : TangentSpace I (ψ.symm y)) :
    symbolInChart ψ φ y v =
      (fderiv ℝ (F := E [⋀^Fin j]→L[ℝ] ℝ) (mpullback 𝓘(ℝ, E) I ψ.symm φ.val) y
        (mfderiv I 𝓘(ℝ, E) ψ (ψ.symm y) v)).compContinuousLinearMap
        (mfderiv I 𝓘(ℝ, E) ψ (ψ.symm y) : TangentSpace I (ψ.symm y) →L[ℝ] E) :=
  (rfl)

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- The exterior derivative at `ψ.symm y` is the alternation of the symbol in the chart. -/
private theorem val_mextDerivₗ_symm (ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞)
    (φ : SmoothForm I M ℝ j) {y : E} (hy : y ∈ ψ.target) :
    (mextDerivₗ I j φ).val (ψ.symm y) = alternatizeUncurryFin (symbolInChart ψ φ y) := by
  rw [← mpullback_symm_compContinuousLinearMap_mfderiv ψ (by simp) (mextDerivₗ I j φ).val hy,
    mextDerivₗ_apply, mpullback_symm_mextDeriv ψ φ hy]
  -- `extDeriv` is the alternation of the derivative.
  exact alternatizeUncurryFin_compContinuousLinearMap (𝕜 := ℝ) (E := E)
    (fderiv ℝ (F := E [⋀^Fin j]→L[ℝ] ℝ) (mpullback 𝓘(ℝ, E) I ψ.symm φ.val) y) _

variable [FiniteDimensional ℝ E]

/-- Where the metric in the chart has derivative zero, the codifferential at `ψ.symm y` is the
symbol of `d^*` applied to the symbol in the chart, `± ⋆ Alt (⋆ ∘ B)`. -/
private theorem val_codifferential_symm
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    (o : Manifold.Orientation I M (Fin m))
    (ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞) (hkl : k + 1 + l = m) (hlk : l + 1 + k = m)
    (β : SmoothForm I M ℝ (k + 1)) {y : E} (hy : y ∈ ψ.target)
    (h : fderiv ℝ (gramInChart ψ) y = 0) :
    (SmoothForm.codifferential o hkl β).val (ψ.symm y) =
      (-1 : ℝ) ^ (m * (k + 2) + 1) • formHodgeStarCLM o hlk (ψ.symm y)
        (alternatizeUncurryFin (formHodgeStarCLM o hkl (ψ.symm y) ∘L symbolInChart ψ β y)) := by
  -- The step on `E`, for a map `T` that intertwines the two stars, and the derivative `C`.
  have key (T : TangentSpace I (ψ.symm y) →L[ℝ] E)
      (hT : ∀ {i i' : ℕ} (hii' : i + i' = m) (a : E [⋀^Fin i]→L[ℝ] ℝ),
        (hodgeStarInChart o ψ hii' y a).compContinuousLinearMap T =
          formHodgeStarCLM o hii' (ψ.symm y) (a.compContinuousLinearMap T))
      (C : E →L[ℝ] E [⋀^Fin (k + 1)]→L[ℝ] ℝ) :
      ((-1 : ℝ) ^ (m * (k + 2) + 1) • hodgeStarInChart o ψ hlk y
        (alternatizeUncurryFin (hodgeStarInChart o ψ hkl y ∘L C))).compContinuousLinearMap T =
      (-1 : ℝ) ^ (m * (k + 2) + 1) • formHodgeStarCLM o hlk (ψ.symm y)
        (alternatizeUncurryFin (formHodgeStarCLM o hkl (ψ.symm y) ∘L
          (compContinuousLinearMapCLM T ∘L C ∘L T))) := by
    rw [← compContinuousLinearMapCLM_apply, map_smul, compContinuousLinearMapCLM_apply, hT,
      alternatizeUncurryFin_compContinuousLinearMap]
    congr 3
    ext v w
    simp only [ContinuousLinearMap.comp_apply, compContinuousLinearMapCLM_apply, hT]
  rw [← mpullback_symm_compContinuousLinearMap_mfderiv ψ (by simp)
      (SmoothForm.codifferential o hkl β).val hy,
    mpullback_symm_codifferential_of_fderiv_gramInChart_eq_zero o ψ hkl hlk β hy h]
  exact key _ (fun hii' a ↦ compContinuousLinearMap_hodgeStarInChart o ψ hii' hy a) _

omit [FiniteDimensional ℝ E] in
/-- Where the reading of `σ` in the chart has derivative zero, the symbol of `L β` is the wedge of
the symbol of `β` with `σ`. -/
private theorem symbolInChart_lefschetz_apply (ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞)
    (σ : SmoothTwoForm I M) (β : SmoothForm I M ℝ j) {y : E} (hy : y ∈ ψ.target)
    (hσ : fderiv ℝ (F := E [⋀^Fin 2]→L[ℝ] ℝ) (mpullback 𝓘(ℝ, E) I ψ.symm σ.val) y = 0)
    (v : TangentSpace I (ψ.symm y)) :
    symbolInChart ψ (σ.lefschetz β) y v = (symbolInChart ψ β y v).wedge (σ.val (ψ.symm y)) := by
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
  refine key _ _ (mpullback_symm_compContinuousLinearMap_mfderiv ψ (by simp) σ.val hy)
    (mpullback 𝓘(ℝ, E) I ψ.symm β.val y) _ _ hσ _ fun u ↦ ?_
  rw [lefschetz_apply]
  exact fderiv_mpullback_symm_wedge_apply ψ β σ hy u

omit [FiniteDimensional ℝ E] in
/-- In a chart in which `J` is a constant `A₀`, the symbol of `𝒥 β` is the derivation of
`J (ψ.symm y)` applied to the symbol of `β`. -/
private theorem symbolInChart_realAlternatingDerivation_apply
    (J : SmoothAlmostComplexStructure I M)
    (ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞) {A₀ : E →L[ℝ] E}
    (hψ : ∀ p ∈ ψ.target, ∀ w, J.chartPushforward ψ.toOpenPartialHomeomorph p w = A₀ w)
    (β : SmoothForm I M ℝ j) {y : E} (hy : y ∈ ψ.target) (v : TangentSpace I (ψ.symm y)) :
    symbolInChart ψ (J.toEndomorphism.realAlternatingDerivation β) y v =
      (symbolInChart ψ β y v).fderivCompContinuousLinearMap (.id ℝ _)
        (J.toEndomorphism (ψ.symm y)) := by
  -- The step on `E`, for a map `T` that intertwines `A₀` and `J`.
  have key (T : TangentSpace I (ψ.symm y) →L[ℝ] E)
      (hT : A₀ ∘L T = T ∘L J.toEndomorphism (ψ.symm y)) (D D' : E →L[ℝ] E [⋀^Fin j]→L[ℝ] ℝ)
      (hD : ∀ u, D' u = (D u).fderivCompContinuousLinearMap (.id ℝ E) A₀) :
      (D' (T v)).compContinuousLinearMap T =
        ((D (T v)).compContinuousLinearMap T).fderivCompContinuousLinearMap (.id ℝ _)
          (J.toEndomorphism (ψ.symm y)) := by
    rw [hD, compContinuousLinearMap_fderivCompContinuousLinearMap_id _ hT]
  refine key _ ?_ _ _ (fderiv_mpullback_symm_realAlternatingDerivation_apply J ψ hψ β hy)
  ext u
  set e := ψ.mfderivSymmEquiv (by simp) hy
  have h1 := (congrArg (mfderiv 𝓘(ℝ, E) I ψ.symm y) (hψ y hy (e.symm u))).symm.trans
    (J.mfderiv_symm_apply_chartPushforward_apply ψ hy (e.symm u))
  rw [← ψ.coe_mfderivSymmEquiv (by simp) hy] at h1
  have hT (w : TangentSpace I (ψ.symm y)) : mfderiv I 𝓘(ℝ, E) ψ (ψ.symm y) w = e.symm w :=
    (congrFun (ψ.coe_mfderivSymmEquiv_symm (by simp) hy) w).symm
  exact (congrArg A₀ (hT u)).trans (((e.symm_apply_apply _).symm.trans
    (congrArg e.symm (h1.trans (congrArg _ (e.apply_symm_apply u))))).trans (hT _).symm)

variable {σ : SmoothTwoForm I M} {J : SmoothAlmostComplexStructure I M}

/-- Under `⟪v, w⟫ = σ(v, J w)`, the symbol of `L β` is the Lefschetz operator of `J` at
`ψ.symm y` composed with the symbol of `β`, where the reading of `σ` has derivative zero. -/
private theorem symbolInChart_lefschetz
    (hg : ∀ x (v w : TangentSpace I x), ⟪v, w⟫ = σ.val x ![v, J x w])
    (ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞) (β : SmoothForm I M ℝ j) {y : E}
    (hy : y ∈ ψ.target)
    (hσ : fderiv ℝ (F := E [⋀^Fin 2]→L[ℝ] ℝ) (mpullback 𝓘(ℝ, E) I ψ.symm σ.val) y = 0) :
    symbolInChart ψ (σ.lefschetz β) y =
      (letI : FiniteDimensional ℝ (TangentSpace I (ψ.symm y)) :=
        VectorBundle.finiteDimensional ℝ E (TangentSpace I) (ψ.symm y)
       (J.almostComplexStructureAt (ψ.symm y)).lefschetz ∘L symbolInChart ψ β y) := by
  ext1 v
  rw [symbolInChart_lefschetz_apply ψ σ β hy hσ v, ContinuousLinearMap.comp_apply,
    AlmostComplexStructure.lefschetz_apply, val_eq_alternatingFormEquiv_kahlerForm hg]

/-- To prove that two smooth forms agree, it suffices to compare them at the points of osculating
holomorphic charts at which the metric in the chart has derivative zero. -/
private theorem eq_of_forall_osculating
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] (hJ : J.IsIntegrable)
    (hσ : σ.IsClosed) (hg : ∀ x (v w : TangentSpace I x), ⟪v, w⟫ = σ.val x ![v, J x w])
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

omit [FiniteDimensional ℝ E] in
/-- Under `⟪v, w⟫ = σ(v, J w)`, the almost complex structure is orthogonal at each point `x`. -/
theorem inner_almostComplexStructureAt_apply_apply
    (hg : ∀ x (v w : TangentSpace I x), ⟪v, w⟫ = σ.val x ![v, J x w]) (x : M)
    (u v : TangentSpace I x) :
    ⟪J.almostComplexStructureAt x u, J.almostComplexStructureAt x v⟫ = ⟪u, v⟫ := by
  have hJ : ∀ x (u v : TangentSpace I x), ⟪u, v⟫ = σ.eval₂ x u (J x v) := fun x u v ↦ by
    rw [hg, SmoothBundleForm.eval₂_apply]
  simp only [SmoothAlmostComplexStructure.almostComplexStructureAt_apply]
  rw [hJ, SmoothAlmostComplexStructure.apply_apply, SmoothBundleForm.eval₂_neg_right,
    ← SmoothBundleForm.eval₂_swap, ← hJ, real_inner_comm]

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
    (hg : ∀ x (v w : TangentSpace I x), ⟪v, w⟫ = σ.val x ![v, J x w])
    (hkl : k + 1 + l = m) (hkl' : k + 2 + 1 + l' = m) (α : SmoothForm I M ℝ (k + 1)) :
    σ.lefschetz (SmoothForm.codifferential o hkl α) -
        SmoothForm.codifferential o hkl' (σ.lefschetz α) =
      -(J.toEndomorphism.realAlternatingDerivation (mextDerivₗ I (k + 1) α) -
        mextDerivₗ I (k + 1) (J.toEndomorphism.realAlternatingDerivation α)) := by
  refine eq_of_forall_osculating hJ hσ hg fun ψ J₀ hψ y hy hgr ↦ ?_
  have hψ' : ∀ p ∈ ψ.target, ∀ w, J.chartPushforward ψ.toOpenPartialHomeomorph p w =
      J₀.toLinearMap.toContinuousLinearMap w := by simpa using hψ
  let _ := o.fact_finrank_tangentSpace (ψ.symm y)
  let _ : FiniteDimensional ℝ (TangentSpace I (ψ.symm y)) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace I) (ψ.symm y)
  have hm : finrank ℝ (TangentSpace I (ψ.symm y)) = m := (o.fact_finrank_tangentSpace _).out
  have hs (i : ℕ) : (-1 : ℝ) ^ (m * i + 1) =
      (-1) ^ (finrank ℝ (TangentSpace I (ψ.symm y)) * i + 1) := by rw [hm]
  have hS {i i' : ℕ} (hii' : i + i' = m) : formHodgeStarCLM o hii' (ψ.symm y) =
      ((o.orientationAt (ψ.symm y)).formHodgeStar
        (hii'.trans hm.symm)).toContinuousLinearEquiv.toContinuousLinearMap :=
    ContinuousLinearMap.ext fun a ↦ formHodgeStarCLM_apply o hii' (ψ.symm y) a
  simp only [Submodule.coe_sub, Submodule.coe_neg, Pi.sub_apply, Pi.neg_apply]
  rw [val_lefschetz hg, val_codifferential_symm o ψ hkl (by omega) α hy hgr,
    val_codifferential_symm o ψ hkl' (by omega) (σ.lefschetz α) hy hgr,
    ContMDiffSection.coe_realAlternatingDerivation]
  beta_reduce
  rw [val_mextDerivₗ_symm ψ α hy, val_mextDerivₗ_symm ψ _ hy,
    symbolInChart_lefschetz hg ψ α hy
      (fderiv_mpullback_symm_eq_zero_of_fderiv_gramInChart_eq_zero hg ψ hψ hy hgr), hs, hs]
  convert AlmostComplexStructure.lefschetz_smul_formHodgeStar_alternatizeUncurryFin_sub
    (inner_almostComplexStructureAt_apply_apply hg (ψ.symm y)) (o.orientationAt (ψ.symm y))
    (l := l) (l' := l') (by omega) (by omega) (by omega) (by omega) (symbolInChart ψ α y)
    using 4
  · rw [formHodgeStarCLM_apply, hS]
  · rw [formHodgeStarCLM_apply, hS]
  · ext u
    simp
  · ext1 v
    exact (symbolInChart_realAlternatingDerivation_apply J ψ hψ' α hy v).trans
      (congrArg _ (by ext u; simp))


/-- **The first-order Kähler identity above the middle degrees**: under the hypotheses of
`lefschetz_codifferential_sub`, if `m < k + 3` then `L` vanishes on the `(k + 1)`-forms and the
identity reads `L d^* α = -(𝒥 dα - d 𝒥 α)`. This covers the forms of degree `m - 1`. -/
theorem lefschetz_codifferential_of_lt (o : Manifold.Orientation I M (Fin m))
    (hJ : J.IsIntegrable) (hσ : σ.IsClosed)
    (hg : ∀ x (v w : TangentSpace I x), ⟪v, w⟫ = σ.val x ![v, J x w])
    (hkl : k + 1 + l = m) (hk : m < k + 3) (α : SmoothForm I M ℝ (k + 1)) :
    σ.lefschetz (SmoothForm.codifferential o hkl α) =
      -(J.toEndomorphism.realAlternatingDerivation (mextDerivₗ I (k + 1) α) -
        mextDerivₗ I (k + 1) (J.toEndomorphism.realAlternatingDerivation α)) := by
  refine eq_of_forall_osculating hJ hσ hg fun ψ J₀ hψ y hy hgr ↦ ?_
  have hψ' : ∀ p ∈ ψ.target, ∀ w, J.chartPushforward ψ.toOpenPartialHomeomorph p w =
      J₀.toLinearMap.toContinuousLinearMap w := by simpa using hψ
  let _ := o.fact_finrank_tangentSpace (ψ.symm y)
  let _ : FiniteDimensional ℝ (TangentSpace I (ψ.symm y)) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace I) (ψ.symm y)
  have hm : finrank ℝ (TangentSpace I (ψ.symm y)) = m := (o.fact_finrank_tangentSpace _).out
  have hs (i : ℕ) : (-1 : ℝ) ^ (m * i + 1) =
      (-1) ^ (finrank ℝ (TangentSpace I (ψ.symm y)) * i + 1) := by rw [hm]
  have hS {i i' : ℕ} (hii' : i + i' = m) : formHodgeStarCLM o hii' (ψ.symm y) =
      ((o.orientationAt (ψ.symm y)).formHodgeStar
        (hii'.trans hm.symm)).toContinuousLinearEquiv.toContinuousLinearMap :=
    ContinuousLinearMap.ext fun a ↦ formHodgeStarCLM_apply o hii' (ψ.symm y) a
  simp only [Submodule.coe_sub, Submodule.coe_neg, Pi.sub_apply, Pi.neg_apply]
  rw [val_lefschetz hg, val_codifferential_symm o ψ hkl (by omega) α hy hgr,
    ContMDiffSection.coe_realAlternatingDerivation]
  beta_reduce
  rw [val_mextDerivₗ_symm ψ α hy, val_mextDerivₗ_symm ψ _ hy, hs]
  convert AlmostComplexStructure.lefschetz_smul_formHodgeStar_alternatizeUncurryFin_of_lt
    (inner_almostComplexStructureAt_apply_apply hg (ψ.symm y)) (o.orientationAt (ψ.symm y))
    (l := l) (by omega) (by omega) (by omega) (symbolInChart ψ α y) using 4
  · rw [formHodgeStarCLM_apply, hS]
  · ext u
    simp
  · ext1 v
    exact (symbolInChart_realAlternatingDerivation_apply J ψ hψ' α hy v).trans
      (congrArg _ (by ext u; simp))

/-- **The first-order Kähler identity on functions**: under the hypotheses of
`lefschetz_codifferential_sub`, for a smooth `0`-form `f`, `d^* (L f) = 𝒥 df`. This is that
identity one degree lower, where `d^* f` is not defined and `𝒥 f` vanishes. The hypothesis `hkl`
is that of the codifferential in degree `2`. -/
theorem codifferential_lefschetz (o : Manifold.Orientation I M (Fin m))
    (hJ : J.IsIntegrable) (hσ : σ.IsClosed)
    (hg : ∀ x (v w : TangentSpace I x), ⟪v, w⟫ = σ.val x ![v, J x w])
    (hkl : 1 + 1 + l = m) (f : SmoothForm I M ℝ 0) :
    SmoothForm.codifferential o hkl (σ.lefschetz f) =
      J.toEndomorphism.realAlternatingDerivation (mextDerivₗ I 0 f) := by
  refine eq_of_forall_osculating hJ hσ hg fun ψ J₀ hψ y hy hgr ↦ ?_
  let _ := o.fact_finrank_tangentSpace (ψ.symm y)
  let _ : FiniteDimensional ℝ (TangentSpace I (ψ.symm y)) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace I) (ψ.symm y)
  have hm : finrank ℝ (TangentSpace I (ψ.symm y)) = m := (o.fact_finrank_tangentSpace _).out
  have hs (i : ℕ) : (-1 : ℝ) ^ (m * i + 1) =
      (-1) ^ (finrank ℝ (TangentSpace I (ψ.symm y)) * i + 1) := by rw [hm]
  have hS {i i' : ℕ} (hii' : i + i' = m) : formHodgeStarCLM o hii' (ψ.symm y) =
      ((o.orientationAt (ψ.symm y)).formHodgeStar
        (hii'.trans hm.symm)).toContinuousLinearEquiv.toContinuousLinearMap :=
    ContinuousLinearMap.ext fun a ↦ formHodgeStarCLM_apply o hii' (ψ.symm y) a
  rw [val_codifferential_symm o ψ hkl (by omega) (σ.lefschetz f) hy hgr,
    ContMDiffSection.coe_realAlternatingDerivation]
  beta_reduce
  rw [val_mextDerivₗ_symm ψ f hy, symbolInChart_lefschetz hg ψ f hy
      (fderiv_mpullback_symm_eq_zero_of_fderiv_gramInChart_eq_zero hg ψ hψ hy hgr), hs]
  convert AlmostComplexStructure.smul_formHodgeStar_alternatizeUncurryFin_lefschetz_fin_zero
    (inner_almostComplexStructureAt_apply_apply hg (ψ.symm y)) (o.orientationAt (ψ.symm y))
    (l := l) (by omega) (by omega) (symbolInChart ψ f y) using 3
  · rw [formHodgeStarCLM_apply, hS]
  · ext u
    simp

end TauCeti.SmoothTwoForm

end
