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
import SymplecticGeometry.Analysis.Normed.Module.Alternating.Derivation

/-!
# The Lefschetz operator on smooth forms, and the Hodge star against `𝒥`

Let `σ` be a smooth two-form on a manifold `M`. This file defines the Lefschetz operator
`L α = α ∧ σ` on smooth real forms, which raises the degree by two, and proves its zeroth-order
properties.

When the manifold carries a metric with `⟪v, w⟫ = σ(v, J w)` for a smooth almost complex
structure `J`, the structure `J` is orthogonal, `σ` is the Kähler form `σ(v, w) = ⟪J v, w⟫` of `J`
at each point, and so `L` is, at each point, the Lefschetz operator
`TauCeti.AlmostComplexStructure.lefschetz` of `J x` on the tangent space. When `σ` is closed, `L`
commutes with the exterior derivative. Finally, on an oriented manifold with a smooth metric, the
Hodge star commutes with the derivation `ContMDiffSection.realAlternatingDerivation` of every
fibrewise skew-adjoint endomorphism field, in particular with the derivation `𝒥` of an orthogonal
almost complex structure; this is `Orientation.formHodgeStar_fderivCompContinuousLinearMap` at
each point.

## Main definitions

* `TauCeti.SmoothTwoForm.lefschetz`: the Lefschetz operator `α ↦ α ∧ σ` of a smooth two-form.

## Main results

* `TauCeti.SmoothTwoForm.val_lefschetz`: under `⟪v, w⟫ = σ(v, J w)`, the value of `L α` at `x`
  is the linear Lefschetz operator of `J x` applied to the value of `α`.
* `TauCeti.SmoothTwoForm.mextDerivₗ_lefschetz`: `d (L α) = L (d α)` for a closed `σ`.
* `TauCeti.SmoothForm.hodgeStar_realAlternatingDerivation`: `⋆ 𝒜 α = 𝒜 ⋆ α` for the
  derivation `𝒜` of a skew-adjoint endomorphism field.

## References

* [P. Griffiths, J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978],
  Chapter 0, §7.
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
  have hσ' : mextDerivₗ I 2 σ = 0 := Subtype.ext <| by
    rw [mextDerivₗ_apply, (SmoothForm.isClosed_def σ).1 hσ, ZeroMemClass.coe_zero]
  rw [lefschetz_apply, lefschetz_apply, SmoothForm.mextDerivₗ_wedge, hσ', map_zero, map_zero,
    smul_zero, add_zero]
  ext x v
  rw [SmoothForm.cast_apply]
  simp only [Function.comp_def, Fin.cast_eq_self]

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)] {σ}
  {J : SmoothAlmostComplexStructure I M}

/-- If the metric is `⟪v, w⟫ = σ(v, J w)`, then `J` is orthogonal. -/
theorem inner_apply_apply_of_inner_eq
    (hg : ∀ x (v w : TangentSpace I x), ⟪v, w⟫ = σ.val x ![v, J x w])
    (x : M) (u w : TangentSpace I x) : ⟪J x u, J x w⟫ = ⟪u, w⟫ := by
  -- `σ(J u, w) = -⟪J u, J w⟫` from `J (-J w) = w`, and `σ(J u, w) = -σ(w, J u) = -⟪w, u⟫`.
  have h₁ := hg x (J x u) (-(J x w))
  simp only [map_neg, J.apply_apply, neg_neg, inner_neg_right] at h₁
  have h₂ : σ.val x ![J x u, w] + σ.val x ![w, J x u] = 0 := by
    simpa using (σ.val x).map_swap_add ![w, J x u] (i := 0) (j := 1) (by decide)
  rw [← h₁, ← hg] at h₂
  linarith [real_inner_comm u w]

variable [FiniteDimensional ℝ E]

/-- If the metric is `⟪v, w⟫ = σ(v, J w)`, then at each point `σ` is the Kähler form
`σ(v, w) = ⟪J v, w⟫` of `J x`, the form of the Kähler two-vector
`TauCeti.AlmostComplexStructure.kahlerForm`. -/
theorem val_eq_alternatingFormEquiv_kahlerForm
    (hg : ∀ x (v w : TangentSpace I x), ⟪v, w⟫ = σ.val x ![v, J x w]) (x : M) :
    σ.val x =
      (letI : FiniteDimensional ℝ (TangentSpace I x) :=
        VectorBundle.finiteDimensional ℝ E (TangentSpace I) x
       alternatingFormEquiv (TangentSpace I x) 2 (J.almostComplexStructureAt x).kahlerForm) := by
  let _ : FiniteDimensional ℝ (TangentSpace I x) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace I) x
  have hJ : ∀ u w : TangentSpace I x,
      ⟪J.almostComplexStructureAt x u, J.almostComplexStructureAt x w⟫ = ⟪u, w⟫ := by
    simpa only [SmoothAlmostComplexStructure.almostComplexStructureAt_apply] using
      inner_apply_apply_of_inner_eq hg x
  ext v
  have hv : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
  rw [hv, alternatingFormEquiv_apply, AlmostComplexStructure.inner_kahlerForm_ιMulti hJ,
    AlmostComplexStructure.inner_apply_left hJ, ← inner_neg_right, hg,
    SmoothAlmostComplexStructure.almostComplexStructureAt_apply]
  simp

/-- If the metric is `⟪v, w⟫ = σ(v, J w)`, then the value at `x` of the Lefschetz operator of `σ`
is the Lefschetz operator `TauCeti.AlmostComplexStructure.lefschetz` of `J x` on the tangent
space, applied to the value of `α`. -/
theorem val_lefschetz (hg : ∀ x (v w : TangentSpace I x), ⟪v, w⟫ = σ.val x ![v, J x w])
    (α : SmoothForm I M ℝ k) (x : M) :
    (σ.lefschetz α).val x =
      (letI : FiniteDimensional ℝ (TangentSpace I x) :=
        VectorBundle.finiteDimensional ℝ E (TangentSpace I) x
       (J.almostComplexStructureAt x).lefschetz (α.val x)) := by
  rw [lefschetz_apply, SmoothForm.coe_wedge_apply, AlmostComplexStructure.lefschetz_apply,
    val_eq_alternatingFormEquiv_kahlerForm hg x]

end SmoothTwoForm

end TauCeti

namespace ContMDiffSection

open TauCeti

variable [IsManifold I 1 M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

omit [IsManifold I ∞ M] in
/-- At each point, the real derivation of a smooth form along an endomorphism field `A` is the
derivation `ContinuousAlternatingMap.fderivCompContinuousLinearMap` of the value at the identity in
the direction `A x`. The metric only supplies the norm on the tangent spaces that
`fderivCompContinuousLinearMap` requires. -/
theorem val_realAlternatingDerivation
    (A : ContMDiffSection I (E →L[ℝ] E) ∞ fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
    (φ : SmoothForm I M ℝ k) (x : M) :
    (A.realAlternatingDerivation φ).val x =
      (φ.val x).fderivCompContinuousLinearMap (.id ℝ (TangentSpace I x)) (A x) := by
  ext v
  rw [realAlternatingDerivation_apply,
    ContinuousAlternatingMap.fderivCompContinuousLinearMap_id_apply]

end ContMDiffSection

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
  rw [coe_hodgeStar, RoughForm.hodgeStar_apply, ContMDiffSection.val_realAlternatingDerivation,
    ContMDiffSection.val_realAlternatingDerivation, coe_hodgeStar, RoughForm.hodgeStar_apply]
  exact (o.orientationAt x).formHodgeStar_fderivCompContinuousLinearMap _ (hA x) _

end TauCeti.SmoothForm

end
