/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Coadjoint.LieGroup
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Induced
public import TauCeti.Geometry.Symplectic.Hamiltonian.EquivariantMomentMap.Basic
public import SymplecticGeometry.Geometry.Manifold.ContMDiff.Dual
import TauCeti.Geometry.Manifold.MFDeriv.ContinuousLinearMap
import SymplecticGeometry.Geometry.Lie.ProdFstMulAction
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.Smooth

/-!
# The induced form on `G × N`: slices, components and an equivariant moment map

Let `G` be a real Lie group with Lie algebra `𝔤`, `N` a manifold with a two-form `β`, and
`f : N → 𝔤*` a smooth map. Tau Ceti's `TauCeti.CotangentBundle.inducedForm` is the two-form
`-d⟨f, θ⟩ + pr_N^* β` on `G × N`, with `θ` the left-invariant Maurer–Cartan form. This file adds
to Tau Ceti's API for it:

* `TauCeti.CotangentBundle.mpullback_prodMk_inducedForm`: on the slice `G × {p}` the induced form
  is the left-invariant Kirillov form of `f p`, since `pr_N` is constant there.
* For a family `ν : N → 𝔤*` whose components `p ↦ ν p ξ` are smooth, so that `ν` is a smooth map
  to the continuous linear forms on `𝔤`
  (`SymplecticGeometry.contMDiff_toContinuousLinearMap_of_contMDiff_apply`), the values of the
  induced form in terms of the derivatives of the components:
  `TauCeti.CotangentBundle.eval₂_inducedForm_of_contMDiff_apply` on any tangent vectors,
  `TauCeti.CotangentBundle.eval₂_inducedForm_prodVectorField` on product vector fields
  `(X_{ξᵢ}, Yᵢ)` with `X_{ξᵢ}` left-invariant, and
  `TauCeti.CotangentBundle.eval₂_inducedForm_of_tangentSpaceProdEquiv_eq` with Fréchet derivatives
  when `N` is a normed space. They follow from Tau Ceti's
  `TauCeti.CotangentBundle.eval₂_inducedForm`.
* `TauCeti.CotangentBundle.isEquivariantMomentMap_inducedForm`: for an action of `G` on `G × N`
  by left multiplication of the first factor, `(g, p) ↦ Ad*_g (ν p)` is a coadjoint-equivariant
  moment map of the induced form. The moment map equation is Tau Ceti's
  `TauCeti.CotangentBundle.isMomentMap_inducedForm`, read through
  `TauCeti.InfinitesimalAction.fundamental_eq_prod_zero_of_smul_eq`; the equivariance holds because
  `Ad*` is a homomorphism.

## References

* [V. Guillemin and S. Sternberg][GuilleminSternberg1990]
* C.-M. Marle, *Modèle d'action hamiltonienne d'un groupe de Lie sur une variété symplectique*,
  Rend. Sem. Mat. Univ. Politec. Torino 43 (1985).
-/

public section

open Bundle SymplecticGeometry TauCeti.Manifold
open scoped Manifold ContDiff

noncomputable section

namespace TauCeti.CotangentBundle

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [FiniteDimensional ℝ E] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {N : Type*} {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

/-- On the slice `G × {p}`, the induced form `-d⟨f, θ⟩ + pr_N^* β` on `G × N` is the
left-invariant Kirillov form of `f p`: the term `pr_N^* β` vanishes there, as `pr_N` is constant
on the slice. -/
@[simp]
theorem mpullback_prodMk_inducedForm {f : N → E →L[ℝ] ℝ} (hf : ContMDiff J 𝓘(ℝ, E →L[ℝ] ℝ) ∞ f)
    (β : SmoothForm J N ℝ 2) (p : N) :
    SmoothForm.mpullback (fun g : G ↦ (g, p)) (contMDiff_id.prodMk contMDiff_const)
        (inducedForm I G β hf) =
      Module.Dual.leftInvariantKirillovForm (I := I) (G := G) (f p : E →ₗ[ℝ] ℝ) := by
  -- `Φ (g, f p)` and the left-invariant covector field of `f p` at `g` are covectors at `g` with
  -- the values `f p (d(L_{g⁻¹})_g v)`.
  have h : leftTrivialization I G ∘ Prod.map id f ∘ (fun g : G ↦ (g, p)) =
      Module.Dual.leftInvariantCovector (I := I) (G := G) (f p : E →ₗ[ℝ] ℝ) :=
    funext fun g ↦ CotangentBundle.ext
      (by
        simp only [Function.comp_apply, Prod.map_apply, id_eq, proj_leftTrivialization]
        exact (Module.Dual.proj_leftInvariantCovector _ g).symm) fun v ↦
      (leftTrivialization_snd_apply _ v).trans
        (Module.Dual.leftInvariantCovector_snd_apply (I := I) (G := G) _ g v).symm
  rw [inducedForm_def, neg_mextDerivₗ_inducedLiouvilleForm, map_add,
    SmoothForm.mpullback_prodMk_left_mpullback_snd, add_zero, SmoothForm.mpullback_mpullback,
    SmoothForm.mpullback_mpullback]
  refine Eq.trans ?_ (Module.Dual.leftInvariantKirillovForm_eq_mpullback_symplecticForm _).symm
  simp only [h]

/-! ### The form on tangent vectors, by components -/

variable
  -- `GroupLieAlgebra I G` is `E` by definition but carries no normed instances. So the casts
  -- `show E →ₗ[ℝ] ℝ from ν p` below read `ν p` as a linear form on the normed space `E`, and the
  -- uses of `contMDiff_toContinuousLinearMap_of_contMDiff_apply` give `(E := E)` explicitly.
  {ν : N → Module.Dual ℝ (GroupLieAlgebra I G)}

/-- **The induced form `-d⟨ν, θ⟩ + pr_N^* β` on tangent vectors, by components.** At `(g, p)` it
pairs the tangent vectors `uᵢ = (vᵢ, wᵢ)` to
`(ν p).kirillovForm ξ₁ ξ₂ - d(ν · ξ₂)_p w₁ + d(ν · ξ₁)_p w₂ + β_p (w₁, w₂)`, where
`ξᵢ = d(L_{g⁻¹})_g vᵢ` and `(ν p).kirillovForm ξ₁ ξ₂ = ν p ⁅ξ₁, ξ₂⁆`. -/
theorem eval₂_inducedForm_of_contMDiff_apply
    (hν : ∀ ξ, ContMDiff J 𝓘(ℝ) ∞ fun p ↦ ν p ξ) (β : SmoothForm J N ℝ 2) (g : G) (p : N)
    (u₁ u₂ : TangentSpace (I.prod J) (g, p)) :
    (inducedForm I G β (contMDiff_toContinuousLinearMap_of_contMDiff_apply (E := E) hν)).eval₂
        (g, p) u₁ u₂ =
      (ν p).kirillovForm (mfderiv I I (g⁻¹ * ·) g (tangentSpaceProdEquiv (g, p) u₁).1)
          (mfderiv I I (g⁻¹ * ·) g (tangentSpaceProdEquiv (g, p) u₂).1) -
        mvfderiv J (fun y ↦ ν y (mfderiv I I (g⁻¹ * ·) g (tangentSpaceProdEquiv (g, p) u₂).1)) p
          (tangentSpaceProdEquiv (g, p) u₁).2 +
        mvfderiv J (fun y ↦ ν y (mfderiv I I (g⁻¹ * ·) g (tangentSpaceProdEquiv (g, p) u₁).1)) p
          (tangentSpaceProdEquiv (g, p) u₂).2 +
        β.eval₂ p (tangentSpaceProdEquiv (g, p) u₁).2 (tangentSpaceProdEquiv (g, p) u₂).2 := by
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  have hf := contMDiff_toContinuousLinearMap_of_contMDiff_apply (E := E) hν
  have hd (ξ : GroupLieAlgebra I G) (w : TangentSpace J p) :
      mvfderiv J (fun y ↦ ν y ξ) p w =
        mvfderiv J (fun y ↦ LinearMap.toContinuousLinearMap (show E →ₗ[ℝ] ℝ from ν y)) p w ξ :=
    mvfderiv_clm_apply_const ((hf p).mdifferentiableAt (by simp)) ξ w
  have hk : Module.Dual.kirillovForm (L := GroupLieAlgebra I G)
      (LinearMap.toContinuousLinearMap (show E →ₗ[ℝ] ℝ from ν p) : E →ₗ[ℝ] ℝ) =
      (ν p).kirillovForm :=
    congrArg _ (LinearMap.coe_toContinuousLinearMap _)
  rw [eval₂_inducedForm hf, tangentSpaceProdEquiv_apply, tangentSpaceProdEquiv_apply]
  linear_combination hd (mfderiv I I (g⁻¹ * ·) g u₂.1) u₁.2 -
    hd (mfderiv I I (g⁻¹ * ·) g u₁.1) u₂.2 +
    LinearMap.congr_fun (LinearMap.congr_fun hk (mfderiv I I (g⁻¹ * ·) g u₁.1))
      (mfderiv I I (g⁻¹ * ·) g u₂.1)

/-- The induced form `-d⟨ν, θ⟩ + pr_N^* β` on `G × N` on the product vector fields `(X_{ξᵢ}, Yᵢ)`
of left-invariant vector fields `X_{ξᵢ}` on `G` and vector fields `Yᵢ` on `N`: at `(g, p)` it is
`ν p ⁅ξ₁, ξ₂⁆ - d(ν · ξ₂)_p (Y₁ p) + d(ν · ξ₁)_p (Y₂ p) + β_p (Y₁ p, Y₂ p)`. -/
theorem eval₂_inducedForm_prodVectorField
    (hν : ∀ ξ, ContMDiff J 𝓘(ℝ) ∞ fun p ↦ ν p ξ) (β : SmoothForm J N ℝ 2) (g : G) (p : N)
    (ξ₁ ξ₂ : GroupLieAlgebra I G) (Y₁ Y₂ : Π y : N, TangentSpace J y) :
    (inducedForm I G β (contMDiff_toContinuousLinearMap_of_contMDiff_apply (E := E) hν)).eval₂
        (g, p) (prodVectorField (mulInvariantVectorField ξ₁) Y₁ (g, p))
        (prodVectorField (mulInvariantVectorField ξ₂) Y₂ (g, p)) =
      ν p ⁅ξ₁, ξ₂⁆ - mvfderiv J (fun p ↦ ν p ξ₂) p (Y₁ p) +
        mvfderiv J (fun p ↦ ν p ξ₁) p (Y₂ p) + β.eval₂ p (Y₁ p) (Y₂ p) := by
  rw [eval₂_inducedForm_of_contMDiff_apply hν, tangentSpaceProdEquiv_prodVectorField,
    tangentSpaceProdEquiv_prodVectorField, mfderiv_inv_mul_mulInvariantVectorField,
    mfderiv_inv_mul_mulInvariantVectorField, Module.Dual.kirillovForm_apply]

/-- **The induced form `-d⟨ν, θ⟩ + pr_N^* β` on left-trivialized tangent vectors.** For `N` a
normed space `F`, at `(g, p)` the form pairs the tangent vectors `(d(L_g) ξᵢ, wᵢ)` to
`ν p ⁅ξ₁, ξ₂⁆ - d(ν · ξ₂)_p w₁ + d(ν · ξ₁)_p w₂ + β_p (w₁, w₂)`. -/
theorem eval₂_inducedForm_of_tangentSpaceProdEquiv_eq {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ν : F → Module.Dual ℝ (GroupLieAlgebra I G)}
    (hν : ∀ ξ, ContMDiff 𝓘(ℝ, F) 𝓘(ℝ) ∞ fun p ↦ ν p ξ) (β : SmoothForm 𝓘(ℝ, F) F ℝ 2)
    {g : G} {p : F} {u₁ u₂ : TangentSpace (I.prod 𝓘(ℝ, F)) (g, p)} {ξ₁ ξ₂ : GroupLieAlgebra I G}
    {w₁ w₂ : F} (hu₁ : tangentSpaceProdEquiv (g, p) u₁ = (mulInvariantVectorField ξ₁ g, w₁))
    (hu₂ : tangentSpaceProdEquiv (g, p) u₂ = (mulInvariantVectorField ξ₂ g, w₂)) :
    (inducedForm I G β (contMDiff_toContinuousLinearMap_of_contMDiff_apply (E := E) hν)).eval₂
        (g, p) u₁ u₂ =
      ν p ⁅ξ₁, ξ₂⁆ - fderiv ℝ (fun p ↦ ν p ξ₂) p w₁ + fderiv ℝ (fun p ↦ ν p ξ₁) p w₂ +
        β.eval₂ p w₁ w₂ := by
  rw [eval₂_inducedForm_of_contMDiff_apply hν, hu₁, hu₂, mfderiv_inv_mul_mulInvariantVectorField,
    mfderiv_inv_mul_mulInvariantVectorField, Module.Dual.kirillovForm_apply,
    mvfderiv_eq_fderiv_apply, mvfderiv_eq_fderiv_apply]

/-! ### An equivariant moment map -/

/-- **An equivariant moment map of the induced form.** For an action of `G` on `G × N` by left
multiplication of the first factor, `g • (h, p) = (g * h, p)`, the map `(g, p) ↦ Ad*_g (ν p)` is
a coadjoint-equivariant moment map of the induced form `-d⟨ν, θ⟩ + pr_N^* β`, for every two-form
`β` on `N`. -/
theorem isEquivariantMomentMap_inducedForm [CompleteSpace E'] [T2Space G] [I.Boundaryless]
    [MulAction G (G × N)] [ContMDiffSMul I (I.prod J) ∞ G (G × N)]
    (hsmul : ∀ (g : G) (q : G × N), g • q = (g * q.1, q.2))
    (hν : ∀ ξ, ContMDiff J 𝓘(ℝ) ∞ fun p ↦ ν p ξ) (β : SmoothForm J N ℝ 2) :
    SmoothTwoForm.IsEquivariantMomentMap
        (inducedForm I G β (contMDiff_toContinuousLinearMap_of_contMDiff_apply (E := E) hν))
      fun q : G × N ↦ Lie.coadjointRepresentation ℝ I G q.1 (ν q.2) := by
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  have h := isMomentMap_inducedForm (I := I) (G := G) (σ := β)
    (contMDiff_toContinuousLinearMap_of_contMDiff_apply (E := E) hν)
  rw [← InfinitesimalAction.fundamental_eq_prod_zero_of_smul_eq hsmul] at h
  -- `GroupLieAlgebra I G` is `E` by definition but has no normed instances, so `ν p` is read as
  -- a linear form on the normed space `E` to make it a continuous linear map.
  have hμ : (fun q : G × N ↦ Lie.coadjointRepresentation ℝ I G q.1
      (LinearMap.toContinuousLinearMap (show E →ₗ[ℝ] ℝ from ν q.2) : E →ₗ[ℝ] ℝ)) =
        fun q : G × N ↦ Lie.coadjointRepresentation ℝ I G q.1 (ν q.2) :=
    funext fun q ↦ congrArg _ (LinearMap.coe_toContinuousLinearMap _)
  rw [hμ] at h
  exact
    { toIsMomentMap := h
      apply_smul g q := by rw [hsmul, map_mul, mul_apply_eq_comp] }

end TauCeti.CotangentBundle

end
