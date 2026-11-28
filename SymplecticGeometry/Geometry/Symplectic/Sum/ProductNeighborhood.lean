/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Complex.Line
public import TauCeti.Geometry.Symplectic.Lagrangian.Embedding.Symplectic.Normal
public import TauCeti.Geometry.Symplectic.Lagrangian.Rescale
public import TauCeti.Geometry.Symplectic.Manifold.Prod
public import Mathlib.Analysis.CStarAlgebra.Classes
public import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.NormalSpace.CompDiffeomorphOfBoundaryless
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import SymplecticGeometry.Geometry.Symplectic.Neighborhood.Symplectic
import SymplecticGeometry.Geometry.Symplectic.Manifold.Prod
import TauCeti.Geometry.Symplectic.Lagrangian.Embedding.Symplectic.Basic
import TauCeti.Geometry.Symplectic.Lagrangian.Graph
import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Level
import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.Equiv
import TauCeti.Geometry.Manifold.VectorBundle.Trivial
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Opens
import SymplecticGeometry.Geometry.Manifold.IsManifold.SecondCountable
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Pullback
import SymplecticGeometry.Topology.MetricSpace.Tube
import SymplecticGeometry.LinearAlgebra.BilinearMap.Alternating
import TauCeti.Geometry.Manifold.ContMDiff.Sqrt
public import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.NormalSpace.ThomPairMap
public import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.Diffeomorph
import SymplecticGeometry.Geometry.Symplectic.Lagrangian.LocalDiffeomorph
import TauCeti.Geometry.Manifold.VectorBundle.Hom.Basic
public import TauCeti.Geometry.Symplectic.Lagrangian.SymplecticTangent
public import SymplecticGeometry.LinearAlgebra.Complex.Finrank
import TauCeti.Geometry.Symplectic.Lagrangian.Embedding.Symplectic.Normal.Bundle
import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-!
# Symplectic framings and product neighbourhoods

Let `ι : Q → M` be a smooth embedding with symplectic tangent images into a manifold with a
nondegenerate two-form `σ`, and let `τ = ι^* σ`. The model of a neighbourhood of `ι (Q)` is
`Q × ℂ` with the product form `τ ⊕ ω₀`, where `ω₀` is the constant form of Tau Ceti's
`TauCeti.stdComplexSymplecticForm`, along the zero slice `q ↦ (q, 0)`. This file packages the data
from which the symplectic fiber sum is built.

A *symplectic framing* of `ι` is a family of linear isomorphisms from the normal spaces of the zero
slice, which are the copies `{0} × ℂ` of `ℂ`, to those of `ι`, smooth as a map of normal bundles
and carrying the normal symplectic form of the zero slice, which is `ω₀`, to that of `ι`. These are
exactly the hypotheses of the symplectic neighbourhood theorem
`TauCeti.SmoothTwoForm.IsNondegenerate.HasSymplecticTangentImages.exists_symplectomorphism_opens`
for the zero slice, `ι` and the identity of `Q`, and
`SymplecticFraming.exists_symplectomorphism_opens`
is that theorem for them.

A *product neighbourhood* of radius `ε` is an open embedding `f` of `Q × B²(ε)` into `M`, a local
diffeomorphism, with `f (q, 0) = ι q`, `f^* σ = τ ⊕ ω₀`, and whose derivative along the zero slice
carries the symplectic complement of `Q` as the framing prescribes. For compact `Q`, the image of
each closed tube `Q × B̄²(δ)` with `δ < ε` is closed.

A bundled `TauCeti.SmoothEmbedding` with symplectic tangent images is what Tau
Ceti calls a symplectic submanifold embedding
(`TauCeti.SmoothTwoForm.IsNondegenerate.isSymplecticSubmanifoldEmbedding_iff_of_isSmoothEmbedding`),
so the hypotheses on `ι` are stated with `HasSymplecticTangentImages`.

## Main definitions

* `SymplecticGeometry.zeroSlice J Q`: the smooth embedding `q ↦ (q, 0)` of `Q` into `Q × ℂ`.
* `SymplecticGeometry.zeroSliceNormalEquiv J Q q`: the identification of the normal space of the
  zero slice at `q` with `ℂ`, by the `ℂ`-component of tangent vectors of `Q × ℂ`;
  `SymplecticGeometry.zeroSliceNormalBundleDiffeomorph J Q`, the resulting diffeomorphism of the
  normal bundle of the zero slice onto `Q × ℂ`. It is Tau Ceti's
  `TauCeti.SmoothEmbedding.normalBundleDiffeomorphOfKer` for the second projection, followed by
  `Bundle.Trivial.diffeomorphProd`.
* `SymplecticGeometry.SymplecticFraming hι hP`: symplectic framings of the normal bundle of `ι`;
  `SymplecticGeometry.SymplecticFraming.refl`, the identity framing of the zero slice itself;
  `SymplecticGeometry.SymplecticFraming.transLocalDiffeomorph`, the framing of `ι' = k ∘ ι` for
  `σ'` obtained from a framing of `ι` and a local diffeomorphism `k : M → M'`, possibly into a
  manifold on another model, with `k^* σ' = σ`. It follows the framing by the identification of
  normal spaces by `dk`, `TauCeti.SmoothEmbedding.normalSpaceEquivOfComp`, which is smooth by
  `TauCeti.SmoothEmbedding.contMDiff_normalSpaceEquivOfComp` and carries one normal form to the
  other by `TauCeti.SmoothEmbedding.symplecticNormalForm_normalSpaceEquivOfComp`;
  `SymplecticGeometry.SymplecticFraming.ofTransLocalDiffeomorph`, its inverse, from a framing of
  `ι'` to one of `ι`, by the inverse identification, which is smooth by Tau Ceti's
  `TauCeti.contMDiff_bundle_symm`; and `SymplecticGeometry.SymplecticFraming.transDiffeomorph`,
  the first along a diffeomorphism `ψ : M ≃ M'`, for the embedding `ψ ∘ ι`, whose tangent images
  are symplectic by
  `TauCeti.SmoothTwoForm.IsNondegenerate.hasSymplecticTangentImages_diffeomorph_comp_iff`;
  `SymplecticGeometry.SymplecticFraming.ofPos`, the framing obtained from linear isomorphisms
  `e q : ℂ ≃ N_q ι`, smooth in `q`, on which the normal form `ω_ι` of `ι` is positive, by rescaling
  `e q` by `(√(ω_ι (e q 1) (e q i)))⁻¹`. On the plane `ℂ` every alternating form is a multiple
  of `ω₀` (`LinearMap.IsAlt.apply_eq_div_mul`), so the rescaling carries `ω₀` exactly to `ω_ι`;
  the rescaling factor is smooth by `TauCeti.SmoothEmbedding.contMDiffAt_symplecticNormalForm`
  and `ContMDiff.sqrt`. The construction adapts the rescaled
  isomorphisms of `HasSymplecticTangentImages.exists_symplectomorphism_opens_of_finrank_eq_two`
  (namespace `TauCeti.SmoothTwoForm.IsNondegenerate`, `Geometry/Symplectic/Neighborhood/CodimTwo`),
  with an explicit factor in place of a ratio on a local frame.
  `SymplecticGeometry.SymplecticFraming.compDiffeomorphOfBoundaryless`, the framing of the
  reparametrised embedding `ι ∘ χ` for a diffeomorphism `χ : Q' ≃ Q`: `Φ (χ q')`, read through
  `zeroSliceNormalEquiv` on the zero slices and through
  `TauCeti.SmoothEmbedding.normalSpaceEquivCompDiffeomorphOfBoundaryless` on the normal spaces of
  `ι` and `ι ∘ χ`.
  `SymplecticGeometry.SymplecticFraming.smul` is the framing of `ι` for `c • σ`, `c > 0`, obtained
  from one for `σ` by first multiplying by `(√c)⁻¹`: the normal form of `ι` for `c • σ` is `c`
  times that for `σ` (`TauCeti.SmoothEmbedding.symplecticNormalForm_smul`).
* `SymplecticGeometry.prodBall Q ε`: the open set `Q × B²(ε)` of `Q × ℂ`, and
  `SymplecticGeometry.prodBallHomeomorph`, its homeomorphism with the product of `Q` and the disc.
* `SymplecticGeometry.ProductNeighborhood Φ ε`: product neighbourhoods of radius `ε` adapted to
  the framing `Φ`.

## Main results

* `SymplecticGeometry.symplecticNormalForm_zeroSlice`: the normal symplectic form of the zero
  slice for `τ ⊕ ω₀` is `ω₀`, read through `zeroSliceNormalEquiv`.
* `SymplecticGeometry.SymplecticFraming.exists_symplectomorphism_opens`: a framing gives a
  symplectomorphism between neighbourhoods of the zero slice and of `ι`.
* `SymplecticGeometry.ProductNeighborhood.isClosed_image_closedBall`: for compact `Q` and
  Hausdorff `M`, the image of the closed tube of radius `δ < ε` is closed, and its complement
  is open (`isOpen_compl_image_closedBall`).
* `SymplecticGeometry.ProductNeighborhood.exists_range_subset`: for compact `Q`, an open set `U`
  containing `ι (Q)` and every radius up to some `ε₀ > 0`, a framing has a product
  neighbourhood with range in `U`. The neighbourhood theorem for the framing gives a
  symplectomorphism `ψ` from an open neighbourhood `U₀` of the zero slice; by the tube lemma the
  open set of points of `U₀` that `ψ` sends into `U` contains some `Q × B²(ε₀)`, and the
  restriction of `ψ` to it is the product neighbourhood.
  `SymplecticGeometry.ProductNeighborhood.exists` is its case `U = M`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §7.2, pp. 318–319, and Theorem 3.4.10.
* [R. E. Gompf, *A new construction of symplectic manifolds*][Gompf1995].
-/

public section

noncomputable section

open Bundle Manifold Module TopologicalSpace TauCeti
open scoped ContDiff Manifold Bundle

namespace SymplecticGeometry

variable {EQ HQ E H M : Type*}
  [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] [TopologicalSpace HQ]
  {J : ModelWithCorners ℝ EQ HQ} {Q : Type*} [TopologicalSpace Q] [ChartedSpace HQ Q]
  [IsManifold J ∞ Q]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ### The zero slice -/

variable (J Q) in
/-- The zero slice `q ↦ (q, 0)` of `Q × ℂ`, as a smooth embedding. -/
def zeroSlice : SmoothEmbedding J (J.prod 𝓘(ℝ, ℂ)) ∞ Q (Q × ℂ) :=
  .ofIsSmoothEmbedding (fun q ↦ (q, 0))
    (isSmoothEmbedding_prodMkLeft_of_extChartAt_eq_zero (by simp))

@[simp]
theorem zeroSlice_apply (q : Q) : zeroSlice J Q q = (q, 0) :=
  SmoothEmbedding.ofIsSmoothEmbedding_apply _ _ q

theorem coe_zeroSlice : ⇑(zeroSlice J Q) = fun q ↦ (q, 0) :=
  funext zeroSlice_apply

/-- The zero slice pulls the product form `τ ⊕ ω₀` back to `τ`. -/
theorem mpullback_zeroSlice_prod (τ : SmoothTwoForm J Q) :
    SmoothForm.mpullback (zeroSlice J Q) (zeroSlice J Q).contMDiff
      (τ.prod stdComplexSymplecticForm.constSmooth) = τ := by
  rw [SmoothForm.mpullback_congr _ (contMDiff_id.prodMk contMDiff_const) coe_zeroSlice]
  exact SmoothTwoForm.mpullback_prodMk_left_prod τ stdComplexSymplecticForm.constSmooth 0

/-- For a nondegenerate `τ`, the zero slice has symplectic tangent images for `τ ⊕ ω₀`. -/
theorem hasSymplecticTangentImages_zeroSlice_prod {τ : SmoothTwoForm J Q}
    (hτ : τ.IsNondegenerate) :
    (hτ.prod (SymplecticForm.isNondegenerate_constSmooth
      stdComplexSymplecticForm)).HasSymplecticTangentImages J (zeroSlice J Q) := by
  rw [coe_zeroSlice]
  exact hτ.hasSymplecticTangentImages_prodMkLeft (SymplecticForm.isNondegenerate_constSmooth _) 0

variable {σ : SmoothTwoForm I M}

/-- If `ι` has symplectic tangent images for a nondegenerate `σ`, the form `ι^* σ ⊕ ω₀` of the
model `Q × ℂ` is nondegenerate. -/
theorem isNondegenerate_prod_of_hasSymplecticTangentImages {hσ : σ.IsNondegenerate}
    {ι : SmoothEmbedding J I ∞ Q M} (hι : hσ.HasSymplecticTangentImages J ι) :
    (SmoothTwoForm.prod (SmoothForm.mpullback ι ι.contMDiff σ)
      stdComplexSymplecticForm.constSmooth).IsNondegenerate :=
  ((SmoothTwoForm.IsNondegenerate.isSymplecticSubmanifoldEmbedding_iff_of_isSmoothEmbedding
    ι.isSmoothEmbedding).2 hι).isNondegenerate_mpullback.prod
    (SymplecticForm.isNondegenerate_constSmooth _)

/-- If `ι` has symplectic tangent images for a nondegenerate `σ`, the zero slice has symplectic
tangent images for the form `ι^* σ ⊕ ω₀` of the model. -/
theorem hasSymplecticTangentImages_zeroSlice {hσ : σ.IsNondegenerate}
    {ι : SmoothEmbedding J I ∞ Q M} (hι : hσ.HasSymplecticTangentImages J ι) :
    (isNondegenerate_prod_of_hasSymplecticTangentImages hι).HasSymplecticTangentImages J
      (zeroSlice J Q) :=
  hasSymplecticTangentImages_zeroSlice_prod
    ((SmoothTwoForm.IsNondegenerate.isSymplecticSubmanifoldEmbedding_iff_of_isSmoothEmbedding
      ι.isSmoothEmbedding).2 hι).isNondegenerate_mpullback

/-! ### The normal bundle of the zero slice

`Prod.snd : Q × ℂ → ℂ` vanishes on the zero slice and is a submersion, so its differential, the
second projection `T_(q,0)(Q × ℂ) = T_q Q × ℂ → ℂ`, identifies each normal space of the zero slice
with `ℂ`, and these identifications form a diffeomorphism of the normal bundle onto `Q × ℂ`. -/

section NormalBundle

variable [FiniteDimensional ℝ EQ]

/-- A tangent vector of `Q × ℂ` at `(q, 0)` is tangent to the zero slice exactly when its
`ℂ`-component vanishes. -/
theorem snd_eq_zero_iff_mem_tangentRange_zeroSlice (q : Q)
    (v : TangentSpace (J.prod 𝓘(ℝ, ℂ)) (zeroSlice J Q q)) :
    ContinuousLinearMap.snd ℝ EQ ℂ v = 0 ↔
      v ∈ (zeroSlice J Q).isImmersion.tangentRange q (WithTop.coe_ne_zero.2 ENat.top_ne_zero) := by
  rw [(zeroSlice J Q).tangentRange_eq_ker_mfderiv q _ (g := Prod.snd) (c := 0)
    (.of_forall fun _ ↦ by simp) (isRegularPoint_snd _) (by simp [finrank_prod]),
    LinearMap.mem_ker, mfderiv_snd]
  -- The tangent spaces of `Q` and `ℂ` at `q` and `0` are `EQ` and `ℂ`.
  rfl

/-- The normal spaces of the zero slice have real dimension two. -/
theorem finrank_normalSpace_zeroSlice (q : Q) :
    finrank ℝ ((zeroSlice J Q).isImmersion.NormalSpace q (WithTop.coe_ne_zero.2 ENat.top_ne_zero)) =
      finrank ℝ ℂ :=
  ((zeroSlice J Q).isImmersion.finrank_normalSpace q _).trans
      Complex.finrank_real_eq_finrank_prod_complex_sub.symm

variable (J Q) in
/-- The identification of the normal space of the zero slice at `q` with `ℂ`, sending the normal
class of a tangent vector of `Q × ℂ` at `(q, 0)` to its `ℂ`-component. -/
def zeroSliceNormalEquiv (q : Q) :
    (zeroSlice J Q).isImmersion.NormalSpace q (WithTop.coe_ne_zero.2 ENat.top_ne_zero) ≃L[ℝ] ℂ :=
  (zeroSlice J Q).isImmersion.normalSpaceEquivOfKer q _ (ContinuousLinearMap.snd ℝ EQ ℂ)
    (snd_eq_zero_iff_mem_tangentRange_zeroSlice q) (finrank_normalSpace_zeroSlice q)

theorem zeroSliceNormalEquiv_def (q : Q) :
    zeroSliceNormalEquiv J Q q =
      (zeroSlice J Q).isImmersion.normalSpaceEquivOfKer q _ (ContinuousLinearMap.snd ℝ EQ ℂ)
        (snd_eq_zero_iff_mem_tangentRange_zeroSlice q) (finrank_normalSpace_zeroSlice q) :=
  (rfl)

/-- `zeroSliceNormalEquiv` sends the normal class of a tangent vector of `Q × ℂ` at `(q, 0)` to
its `ℂ`-component. -/
@[simp]
theorem zeroSliceNormalEquiv_normalClass (q : Q)
    (v : TangentSpace (J.prod 𝓘(ℝ, ℂ)) (zeroSlice J Q q)) :
    zeroSliceNormalEquiv J Q q
        ((zeroSlice J Q).isImmersion.normalClass q (WithTop.coe_ne_zero.2 ENat.top_ne_zero) v) =
            v.2 :=
  (zeroSlice J Q).isImmersion.normalSpaceEquivOfKer_normalClass q _ _ _ _ v

/-- The inverse of `zeroSliceNormalEquiv` sends `z` to the normal class of the vertical vector
`(0, z)`. -/
theorem zeroSliceNormalEquiv_symm_apply (q : Q) (z : ℂ) :
    (zeroSliceNormalEquiv J Q q).symm z =
      (zeroSlice J Q).isImmersion.normalClass q (WithTop.coe_ne_zero.2 ENat.top_ne_zero)
          ((0, z) : EQ × ℂ) :=
  (zeroSlice J Q).isImmersion.normalSpaceEquivOfKer_symm_apply q _ _ _ _ ((0, z) : EQ × ℂ)

variable (J Q) in
/-- The normal bundle of the zero slice, with the bundle structure that `SymplecticFraming` uses,
is diffeomorphic to `Q × ℂ` over the identity of `Q`, by `zeroSliceNormalEquiv` on each fibre. -/
def zeroSliceNormalBundleDiffeomorph :
    letI := (zeroSlice J Q).normalSpaceFiberBundle (WithTop.coe_ne_zero.2 ENat.top_ne_zero)
      (Complex.finrank_real_eq_finrank_prod_complex_sub (F := EQ))
    TotalSpace ℂ (fun q ↦ (zeroSlice J Q).isImmersion.NormalSpace q
        (WithTop.coe_ne_zero.2 ENat.top_ne_zero))
      ≃ₘ⟮J.prod 𝓘(ℝ, ℂ), J.prod 𝓘(ℝ, ℂ)⟯ Q × ℂ :=
  letI := (zeroSlice J Q).normalSpaceFiberBundle (WithTop.coe_ne_zero.2 ENat.top_ne_zero)
    (Complex.finrank_real_eq_finrank_prod_complex_sub (F := EQ))
  ((zeroSlice J Q).normalBundleDiffeomorphOfKer (m := ∞) _ (by simp)
    Complex.finrank_real_eq_finrank_prod_complex_sub (E₂ := Trivial Q ℂ) (W := ℂ)
    (fun _ ↦ ContinuousLinearMap.snd ℝ EQ ℂ) snd_eq_zero_iff_mem_tangentRange_zeroSlice
    finrank_normalSpace_zeroSlice (by
      -- The `ℂ`-component of an ambient tangent vector is its image by the differential of
      -- `Prod.snd`.
      refine Trivial.contMDiff_mk_iff.2 ⟨contMDiff_proj _, ?_⟩
      refine (Pullback.contMDiff_mfderiv_apply (zeroSlice J Q) (zeroSlice J Q).contMDiff
        contMDiff_snd le_rfl).congr fun p ↦ ?_
      exact (DFunLike.congr_fun mfderiv_snd p.snd).symm)).trans
    (Trivial.diffeomorphProd J Q ℂ ∞)

/-- The diffeomorphism sends a normal vector at `q` to `q` and its `ℂ`-component. -/
@[simp]
theorem zeroSliceNormalBundleDiffeomorph_apply
    (p : TotalSpace ℂ
      (fun q ↦ (zeroSlice J Q).isImmersion.NormalSpace q
          (WithTop.coe_ne_zero.2 ENat.top_ne_zero))) :
    letI := (zeroSlice J Q).normalSpaceFiberBundle (WithTop.coe_ne_zero.2 ENat.top_ne_zero)
      (Complex.finrank_real_eq_finrank_prod_complex_sub (F := EQ))
    zeroSliceNormalBundleDiffeomorph J Q p = (p.proj, zeroSliceNormalEquiv J Q p.proj p.snd) := by
  let := (zeroSlice J Q).normalSpaceFiberBundle (WithTop.coe_ne_zero.2 ENat.top_ne_zero)
    (Complex.finrank_real_eq_finrank_prod_complex_sub (F := EQ))
  exact (congrArg (Trivial.diffeomorphProd J Q ℂ ∞)
    ((zeroSlice J Q).normalBundleDiffeomorphOfKer_apply _ _ _ _ _ _ _ p)).trans
    (Trivial.diffeomorphProd_apply ..)

/-- The inverse diffeomorphism sends `(q, z)` to the normal vector at `q` with `ℂ`-component
`z`. -/
@[simp]
theorem zeroSliceNormalBundleDiffeomorph_symm_apply (x : Q × ℂ) :
    letI := (zeroSlice J Q).normalSpaceFiberBundle (WithTop.coe_ne_zero.2 ENat.top_ne_zero)
      (Complex.finrank_real_eq_finrank_prod_complex_sub (F := EQ))
    (zeroSliceNormalBundleDiffeomorph J Q).symm x =
      ⟨x.1, (zeroSliceNormalEquiv J Q x.1).symm x.2⟩ := by
  let := (zeroSlice J Q).normalSpaceFiberBundle (WithTop.coe_ne_zero.2 ENat.top_ne_zero)
    (Complex.finrank_real_eq_finrank_prod_complex_sub (F := EQ))
  exact ((zeroSlice J Q).normalBundleDiffeomorphOfKer_symm_apply (m := ∞) _ (by simp) _ _ _ _ _
    ((Trivial.diffeomorphProd J Q ℂ ∞).symm x)).trans
      (by rw [Trivial.diffeomorphProd_symm_apply, zeroSliceNormalEquiv_def])

/-- The identification of the normal bundle of the zero slice with `Q × ℂ` is smooth. -/
theorem contMDiff_zeroSliceNormalEquiv :
    letI := (zeroSlice J Q).normalSpaceFiberBundle (WithTop.coe_ne_zero.2 ENat.top_ne_zero)
      (Complex.finrank_real_eq_finrank_prod_complex_sub (F := EQ))
    ContMDiff (J.prod 𝓘(ℝ, ℂ)) (J.prod 𝓘(ℝ, ℂ)) ∞
      (fun p : TotalSpace ℂ
          (fun q ↦ (zeroSlice J Q).isImmersion.NormalSpace q
              (WithTop.coe_ne_zero.2 ENat.top_ne_zero)) ↦
        (p.proj, zeroSliceNormalEquiv J Q p.proj p.snd)) := by
  let := (zeroSlice J Q).normalSpaceFiberBundle (WithTop.coe_ne_zero.2 ENat.top_ne_zero)
    (Complex.finrank_real_eq_finrank_prod_complex_sub (F := EQ))
  exact (zeroSliceNormalBundleDiffeomorph J Q).contMDiff.congr
    fun p ↦ (zeroSliceNormalBundleDiffeomorph_apply p).symm

/-- The inverse identification of `Q × ℂ` with the normal bundle of the zero slice is smooth. -/
theorem contMDiff_zeroSliceNormalEquiv_symm :
    letI := (zeroSlice J Q).normalSpaceFiberBundle (WithTop.coe_ne_zero.2 ENat.top_ne_zero)
      (Complex.finrank_real_eq_finrank_prod_complex_sub (F := EQ))
    ContMDiff (J.prod 𝓘(ℝ, ℂ)) (J.prod 𝓘(ℝ, ℂ)) ∞
      (fun x : Q × ℂ ↦ (⟨x.1, (zeroSliceNormalEquiv J Q x.1).symm x.2⟩ : TotalSpace ℂ
          (fun q ↦ (zeroSlice J Q).isImmersion.NormalSpace q
              (WithTop.coe_ne_zero.2 ENat.top_ne_zero)))) := by
  let := (zeroSlice J Q).normalSpaceFiberBundle (WithTop.coe_ne_zero.2 ENat.top_ne_zero)
    (Complex.finrank_real_eq_finrank_prod_complex_sub (F := EQ))
  exact (zeroSliceNormalBundleDiffeomorph J Q).symm.contMDiff.congr
    fun x ↦ (zeroSliceNormalBundleDiffeomorph_symm_apply x).symm

/-- The symplectic complement of the zero slice for `τ ⊕ ω₀` contains the vertical vectors: a
tangent vector of `Q × ℂ` at `(q, 0)` with vanishing `Q`-component pairs to zero with every vector
tangent to the zero slice. -/
theorem mem_orthogonal_tangentRange_zeroSlice {τ : SmoothTwoForm J Q}
    (hτ : (τ.prod stdComplexSymplecticForm.constSmooth).IsNondegenerate) (q : Q)
    {v : TangentSpace (J.prod 𝓘(ℝ, ℂ)) (zeroSlice J Q q)} (hv : v.1 = 0) :
    v ∈ (hτ.symplecticFormAt (zeroSlice J Q q)).orthogonal
      ((zeroSlice J Q).isImmersion.tangentRange q (WithTop.coe_ne_zero.2 ENat.top_ne_zero)) := by
  refine SymplecticForm.mem_orthogonal_iff.2 fun u hu ↦ ?_
  have hu2 : u.2 = 0 := (snd_eq_zero_iff_mem_tangentRange_zeroSlice q u).2 hu
  rw [SmoothTwoForm.IsNondegenerate.symplecticFormAt_apply, SmoothTwoForm.eval₂_prod_eq_add, hv,
    hu2]
  exact (congrArg₂ (· + ·) (SmoothBundleForm.eval₂_zero_right τ _ _)
    (SmoothBundleForm.eval₂_zero_left _ _ _)).trans (add_zero 0)

/-- The normal symplectic form of the zero slice of `(Q × ℂ, τ ⊕ ω₀)` is `ω₀`, read through the
identification `zeroSliceNormalEquiv` of the normal spaces with `ℂ`. -/
theorem symplecticNormalForm_zeroSlice {τ : SmoothTwoForm J Q}
    {hτ : (τ.prod stdComplexSymplecticForm.constSmooth).IsNondegenerate}
    (h : hτ.HasSymplecticTangentImages J (zeroSlice J Q)) (q : Q)
    (v w : (zeroSlice J Q).isImmersion.NormalSpace q (WithTop.coe_ne_zero.2 ENat.top_ne_zero)) :
    (zeroSlice J Q).symplecticNormalForm h q (WithTop.coe_ne_zero.2 ENat.top_ne_zero) v w =
      stdComplexSymplecticForm (zeroSliceNormalEquiv J Q q v) (zeroSliceNormalEquiv J Q q w) := by
  obtain ⟨z, rfl⟩ := (zeroSliceNormalEquiv J Q q).symm.surjective v
  obtain ⟨z', rfl⟩ := (zeroSliceNormalEquiv J Q q).symm.surjective w
  rw [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply,
    zeroSliceNormalEquiv_symm_apply, zeroSliceNormalEquiv_symm_apply]
  refine ((zeroSlice J Q).symplecticNormalForm_normalClass_normalClass h q _ ((0, z) : EQ × ℂ)
    (mem_orthogonal_tangentRange_zeroSlice hτ q (v := ((0, z') : EQ × ℂ)) rfl)).trans ?_
  -- The components of the vertical vectors `(0, z)` and `(0, z')` are `0` and `z`, `z'`.
  exact ((SmoothTwoForm.eval₂_prod_eq_add τ _ _ ((0, z) : EQ × ℂ) ((0, z') : EQ × ℂ)).trans
    (congrArg₂ (· + ·) (SmoothBundleForm.eval₂_zero_left τ _ _)
      (SymplecticForm.constSmooth_apply _ _ z z'))).trans (zero_add _)

end NormalBundle

/-! ### Symplectic framings -/

variable [FiniteDimensional ℝ EQ] [FiniteDimensional ℝ E]

/-- A **symplectic framing** of the normal bundle of a smooth embedding `ι : Q → M` with symplectic
tangent images: linear isomorphisms `Φ q` from the normal space of the zero slice `q ↦ (q, 0)` of
`Q × ℂ` at `q` onto that of `ι` at `q`, smooth as a map of normal bundles with model fibre `ℂ`,
which carry the normal symplectic form of the zero slice for `ι^* σ ⊕ ω₀` (that is, `ω₀`) to the
normal symplectic form of `ι`. The hypothesis `hP` says that `ι` has codimension two. -/
structure SymplecticFraming {hσ : σ.IsNondegenerate} {ι : SmoothEmbedding J I ∞ Q M}
    (hι : hσ.HasSymplecticTangentImages J ι)
    (hP : finrank ℝ ℂ = finrank ℝ E - finrank ℝ EQ) where
  /-- The isomorphism of normal spaces at `q`. -/
  toFun : ∀ q, (zeroSlice J Q).isImmersion.NormalSpace q (WithTop.coe_ne_zero.2 ENat.top_ne_zero)
      ≃L[ℝ]
    ι.isImmersion.NormalSpace q (WithTop.coe_ne_zero.2 ENat.top_ne_zero)
  /-- The framing is smooth as a map of normal bundles. -/
  contMDiff_toFun :
    letI := (zeroSlice J Q).normalSpaceFiberBundle (WithTop.coe_ne_zero.2 ENat.top_ne_zero)
      (Complex.finrank_real_eq_finrank_prod_complex_sub (F := EQ))
    letI := ι.normalSpaceFiberBundle (WithTop.coe_ne_zero.2 ENat.top_ne_zero) hP
    ContMDiff (J.prod 𝓘(ℝ, ℂ)) (J.prod 𝓘(ℝ, ℂ)) ∞
      (fun p : TotalSpace ℂ
          (fun q ↦ (zeroSlice J Q).isImmersion.NormalSpace q
              (WithTop.coe_ne_zero.2 ENat.top_ne_zero)) ↦
        (⟨p.proj, toFun p.proj p.snd⟩ :
          TotalSpace ℂ (fun q ↦ ι.isImmersion.NormalSpace q
              (WithTop.coe_ne_zero.2 ENat.top_ne_zero))))
  /-- The framing carries the normal symplectic form of the zero slice to that of `ι`. -/
  symplecticNormalForm_toFun : ∀ q v w,
    ι.symplecticNormalForm hι q (WithTop.coe_ne_zero.2 ENat.top_ne_zero) (toFun q v)
      (toFun q w) =
      (zeroSlice J Q).symplecticNormalForm (hasSymplecticTangentImages_zeroSlice hι) q
        (WithTop.coe_ne_zero.2 ENat.top_ne_zero) v w

namespace SymplecticFraming

section Basic

variable {hσ : σ.IsNondegenerate} {ι : SmoothEmbedding J I ∞ Q M}
  {hι : hσ.HasSymplecticTangentImages J ι} {hP : finrank ℝ ℂ = finrank ℝ E - finrank ℝ EQ}

attribute [coe] toFun

instance : CoeFun (SymplecticFraming hι hP) fun _ ↦ ∀ q,
    (zeroSlice J Q).isImmersion.NormalSpace q (WithTop.coe_ne_zero.2 ENat.top_ne_zero) ≃L[ℝ]
      ι.isImmersion.NormalSpace q (WithTop.coe_ne_zero.2 ENat.top_ne_zero) :=
  ⟨toFun⟩

/-- Two framings are equal if their isomorphisms of normal spaces agree at every point. -/
@[ext]
theorem ext {Φ Ψ : SymplecticFraming hι hP} (h : ∀ q, Φ q = Ψ q) : Φ = Ψ := by
  cases Φ
  cases Ψ
  congr
  exact funext h

end Basic

/-- The **identity framing** of the zero slice of `(Q × ℂ, τ ⊕ ω₀)`, for a nondegenerate `τ`. -/
def refl {τ : SmoothTwoForm J Q} (hτ : τ.IsNondegenerate) :
    SymplecticFraming (hasSymplecticTangentImages_zeroSlice_prod hτ)
      Complex.finrank_real_eq_finrank_prod_complex_sub where
  toFun _ := .refl ℝ _
  contMDiff_toFun := by
    let := (zeroSlice J Q).normalSpaceFiberBundle (WithTop.coe_ne_zero.2 ENat.top_ne_zero)
      (Complex.finrank_real_eq_finrank_prod_complex_sub (F := EQ))
    -- The map of total spaces is the identity, up to the eta rule for `TotalSpace`.
    exact contMDiff_id
  symplecticNormalForm_toFun q v w :=
    congrArg (fun s : SymplecticForm _ ↦ s v w) (SmoothEmbedding.symplecticNormalForm_congr
      (congrArg (SmoothTwoForm.prod · stdComplexSymplecticForm.constSmooth)
        (mpullback_zeroSlice_prod τ).symm) _ _ q _)

@[simp]
theorem refl_apply {τ : SmoothTwoForm J Q} (hτ : τ.IsNondegenerate) (q : Q) :
    refl hτ q = .refl ℝ _ :=
  (rfl)

section TransLocalDiffeomorph

variable {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M']
  [ChartedSpace H' M'] [IsManifold I' ∞ M'] {σ' : SmoothTwoForm I' M'}
  {hσ : σ.IsNondegenerate} {hσ' : σ'.IsNondegenerate} {ι : SmoothEmbedding J I ∞ Q M}
  {ι' : SmoothEmbedding J I' ∞ Q M'} {hι : hσ.HasSymplecticTangentImages J ι}
  {hι' : hσ'.HasSymplecticTangentImages J ι'} {hP : finrank ℝ ℂ = finrank ℝ E - finrank ℝ EQ}
  {hP' : finrank ℝ ℂ = finrank ℝ E' - finrank ℝ EQ} {k : M → M'}
  (hk : IsLocalDiffeomorph I I' ∞ k) (hkσ : SmoothForm.mpullback k hk.contMDiff σ' = σ)
  (hkι : k ∘ ι = ι')

/-- **A framing moved along a local symplectomorphism.** Let `k : M → M'` be a local
diffeomorphism, possibly into a manifold on another model, pulling `σ'` back to `σ`, and let `ι'`
be the embedding `k ∘ ι`. A framing `Φ` of `ι` for `σ` gives the framing of `ι'` for `σ'` that
follows `Φ q` by the identification of the normal spaces of `ι` and of `ι'` at `q` induced by the
derivative of `k` (`TauCeti.SmoothEmbedding.normalSpaceEquivOfComp`). -/
def transLocalDiffeomorph (Φ : SymplecticFraming hι hP) : SymplecticFraming hι' hP' where
  toFun q := (Φ q).trans (ι.normalSpaceEquivOfComp ι' _ _
    (fun q ↦ hk.isInvertible_mfderiv (by simp) (ι q)) hkι q)
  contMDiff_toFun := by
    let := (zeroSlice J Q).normalSpaceFiberBundle (WithTop.coe_ne_zero.2 ENat.top_ne_zero)
      (Complex.finrank_real_eq_finrank_prod_complex_sub (F := EQ))
    let := ι.normalSpaceFiberBundle (WithTop.coe_ne_zero.2 ENat.top_ne_zero) hP
    let := ι'.normalSpaceFiberBundle (WithTop.coe_ne_zero.2 ENat.top_ne_zero) hP'
    exact (ι.contMDiff_normalSpaceEquivOfComp (r := ∞) ι' _ _ le_rfl le_rfl hP hP' hk.contMDiff
      (fun q ↦ hk.isInvertible_mfderiv (by simp) (ι q)) hkι).comp Φ.contMDiff_toFun
  symplecticNormalForm_toFun q v w := by
    rw [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.trans_apply,
      ι.symplecticNormalForm_normalSpaceEquivOfComp ι' hι hι' _ _ _ hkι q
        (fun a b ↦ by rw [← hkσ, SmoothForm.eval₂_mpullback]),
      Φ.symplecticNormalForm_toFun, symplecticNormalForm_zeroSlice, symplecticNormalForm_zeroSlice]

/-- The framing `Φ.transLocalDiffeomorph hk hkσ hkι` sends a normal vector `v` of the zero slice
at `q` to the image of `Φ q v` under the identification of the normal spaces of `ι` and of
`ι' = k ∘ ι` induced by the derivative of `k`. -/
@[simp]
theorem transLocalDiffeomorph_apply (Φ : SymplecticFraming hι hP) (q : Q)
    (v : (zeroSlice J Q).isImmersion.NormalSpace q (WithTop.coe_ne_zero.2 ENat.top_ne_zero)) :
    Φ.transLocalDiffeomorph (hι' := hι') (hP' := hP') hk hkσ hkι q v =
      ι.normalSpaceEquivOfComp ι' _ _ (fun q ↦ hk.isInvertible_mfderiv (by simp) (ι q)) hkι q
        (Φ q v) :=
  (rfl)

/-- **A framing pulled back along a local symplectomorphism.** Let `k : M → M'` be a local
diffeomorphism, possibly into a manifold on another model, pulling `σ'` back to `σ`, and let `ι'`
be the embedding `k ∘ ι`. A framing `Φ'` of `ι'` for `σ'` gives the framing of `ι` for `σ` that
follows `Φ' q` by the inverse of the identification of the normal spaces of `ι` and of `ι'` at
`q` induced by the derivative of `k`. This undoes `transLocalDiffeomorph`. -/
def ofTransLocalDiffeomorph (Φ' : SymplecticFraming hι' hP') : SymplecticFraming hι hP where
  toFun q := (Φ' q).trans (ι.normalSpaceEquivOfComp ι' _ _
    (fun q ↦ hk.isInvertible_mfderiv (by simp) (ι q)) hkι q).symm
  contMDiff_toFun := by
    let := (zeroSlice J Q).normalSpaceFiberBundle (WithTop.coe_ne_zero.2 ENat.top_ne_zero)
      (Complex.finrank_real_eq_finrank_prod_complex_sub (F := EQ))
    let := ι.normalSpaceFiberBundle (WithTop.coe_ne_zero.2 ENat.top_ne_zero) hP
    let := ι.normalSpaceVectorBundle (WithTop.coe_ne_zero.2 ENat.top_ne_zero) hP
    let := ι'.normalSpaceFiberBundle (WithTop.coe_ne_zero.2 ENat.top_ne_zero) hP'
    let := ι'.normalSpaceVectorBundle (WithTop.coe_ne_zero.2 ENat.top_ne_zero) hP'
    -- The inverse identification is smooth, as the inverse of a smooth fibrewise isomorphism.
    exact (contMDiff_bundle_symm _ (ι.contMDiff_normalSpaceEquivOfComp (r := ∞) ι' _ _ le_rfl
      le_rfl hP hP' hk.contMDiff (fun q ↦ hk.isInvertible_mfderiv (by simp) (ι q)) hkι)).comp
        Φ'.contMDiff_toFun
  symplecticNormalForm_toFun q v w := by
    rw [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.trans_apply,
      ← ι.symplecticNormalForm_normalSpaceEquivOfComp ι' hι hι' (by simp) (by simp)
        (fun q ↦ hk.isInvertible_mfderiv (by simp) (ι q)) hkι q
        (fun a b ↦ by rw [← hkσ, SmoothForm.eval₂_mpullback]),
      ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply,
      Φ'.symplecticNormalForm_toFun, symplecticNormalForm_zeroSlice, symplecticNormalForm_zeroSlice]

/-- The framing `Φ'.ofTransLocalDiffeomorph hk hkσ hkι` sends a normal vector `v` of the zero
slice at `q` to the preimage of `Φ' q v` under the identification of the normal spaces of `ι` and
of `ι' = k ∘ ι` induced by the derivative of `k`. -/
@[simp]
theorem ofTransLocalDiffeomorph_apply (Φ' : SymplecticFraming hι' hP') (q : Q)
    (v : (zeroSlice J Q).isImmersion.NormalSpace q (WithTop.coe_ne_zero.2 ENat.top_ne_zero)) :
    Φ'.ofTransLocalDiffeomorph (hι := hι) (hP := hP) hk hkσ hkι q v =
      (ι.normalSpaceEquivOfComp ι' _ _ (fun q ↦ hk.isInvertible_mfderiv (by simp) (ι q)) hkι
        q).symm (Φ' q v) :=
  (rfl)

/-- Pulling back a framing along `k` after moving it along `k` gives the framing back. -/
@[simp]
theorem ofTransLocalDiffeomorph_transLocalDiffeomorph (Φ : SymplecticFraming hι hP) :
    (Φ.transLocalDiffeomorph (hι' := hι') (hP' := hP') hk hkσ hkι).ofTransLocalDiffeomorph hk hkσ
      hkι = Φ := by
  ext q v
  simp

/-- Moving a framing along `k` after pulling it back along `k` gives the framing back. -/
@[simp]
theorem transLocalDiffeomorph_ofTransLocalDiffeomorph (Φ' : SymplecticFraming hι' hP') :
    (Φ'.ofTransLocalDiffeomorph (hι := hι) (hP := hP) hk hkσ hkι).transLocalDiffeomorph hk hkσ
      hkι = Φ' := by
  ext q v
  simp

end TransLocalDiffeomorph

section TransDiffeomorph

variable [J.Boundaryless] {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [FiniteDimensional ℝ E'] [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
  [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M'] {σ' : SmoothTwoForm I' M'}
  {hσ : σ.IsNondegenerate} {ι : SmoothEmbedding J I ∞ Q M}
  {hι : hσ.HasSymplecticTangentImages J ι} {hP : finrank ℝ ℂ = finrank ℝ E - finrank ℝ EQ}

/-- **A framing moved along a symplectomorphism of the target.** Let `ψ : M ≃ M'` be a
diffeomorphism, possibly onto a manifold on another model, pulling a nondegenerate form `σ'` back
to `σ`, such as `σ' = (ψ⁻¹)^* σ`. A framing `Φ` of `ι` for `σ` gives the framing of `ψ ∘ ι` for
`σ'` that follows `Φ q` by the identification of the normal spaces of `ι` and of `ψ ∘ ι` at `q`
induced by the derivative of `ψ` (`TauCeti.SmoothEmbedding.normalSpaceEquivOfComp` for the
triangle `ψ ∘ ι = ψ ∘ ι`): `transLocalDiffeomorph` along `ψ`. -/
def transDiffeomorph (Φ : SymplecticFraming hι hP) (ψ : M ≃ₘ⟮I, I'⟯ M')
    (hσ' : σ'.IsNondegenerate) (hψ : SmoothForm.mpullback ψ ψ.contMDiff σ' = σ)
    (hP' : finrank ℝ ℂ = finrank ℝ E' - finrank ℝ EQ) :
    SymplecticFraming (hσ := hσ') (ι := ι.transDiffeomorphOfBoundaryless ψ (by simp))
      (SmoothEmbedding.coe_transDiffeomorphOfBoundaryless ι ψ _ ▸
        (SmoothTwoForm.IsNondegenerate.hasSymplecticTangentImages_diffeomorph_comp_iff ψ hψ).2 hι)
      hP' :=
  Φ.transLocalDiffeomorph ψ.isLocalDiffeomorph hψ
    (SmoothEmbedding.coe_transDiffeomorphOfBoundaryless ι ψ _).symm

/-- The framing `Φ.transDiffeomorph ψ hσ' hψ hP'` sends a normal vector `v` of the zero slice at
`q` to the image of `Φ q v` under the identification of the normal spaces of `ι` and of `ψ ∘ ι`
induced by the derivative of `ψ`. -/
@[simp]
theorem transDiffeomorph_apply (Φ : SymplecticFraming hι hP) (ψ : M ≃ₘ⟮I, I'⟯ M')
    (hσ' : σ'.IsNondegenerate) (hψ : SmoothForm.mpullback ψ ψ.contMDiff σ' = σ)
    (hP' : finrank ℝ ℂ = finrank ℝ E' - finrank ℝ EQ) (q : Q)
    (v : (zeroSlice J Q).isImmersion.NormalSpace q (WithTop.coe_ne_zero.2 ENat.top_ne_zero)) :
    Φ.transDiffeomorph ψ hσ' hψ hP' q v =
      ι.normalSpaceEquivOfComp (ι.transDiffeomorphOfBoundaryless ψ (by simp)) _ _
        (fun _ ↦ ψ.isInvertible_mfderiv (by simp))
        (SmoothEmbedding.coe_transDiffeomorphOfBoundaryless ι ψ _).symm q (Φ q v) :=
  (rfl)

end TransDiffeomorph

section OfPos

variable {hσ : σ.IsNondegenerate} {ι : SmoothEmbedding J I ∞ Q M}
  {hι : hσ.HasSymplecticTangentImages J ι} {hP : finrank ℝ ℂ = finrank ℝ E - finrank ℝ EQ}
  {e : ∀ q, ℂ ≃L[ℝ] ι.isImmersion.NormalSpace q (WithTop.coe_ne_zero.2 ENat.top_ne_zero)}

variable (e) in
/-- **The symplectic framing of a positive trivialization of the normal bundle.** Let
`e q : ℂ ≃ N_q ι` be linear isomorphisms such that `(q, z) ↦ e q z` is a smooth map of `Q × ℂ` to
the normal bundle of `ι`, and such that `λ q = ω_ι (e q 1) (e q i)` is positive, where `ω_ι` is
the normal symplectic form of `ι`. The framing at `q` identifies the normal space of the zero
slice with `ℂ` (`zeroSliceNormalEquiv`), multiplies by `λ q ^ (-1/2) = (√(λ q))⁻¹`, and then
applies `e q`. It carries `ω₀` to `ω_ι`: since `ω₀ 1 i = 1` and alternating forms on `ℂ` are
proportional, `ω_ι (e q u) (e q v) = λ q * ω₀ u v`. -/
def ofPos
    (he : letI := ι.normalSpaceFiberBundle (WithTop.coe_ne_zero.2 ENat.top_ne_zero) hP
      ContMDiff (J.prod 𝓘(ℝ, ℂ)) (J.prod 𝓘(ℝ, ℂ)) ∞
        (fun x : Q × ℂ ↦ (⟨x.1, e x.1 x.2⟩ :
          TotalSpace ℂ (fun q ↦ ι.isImmersion.NormalSpace q
              (WithTop.coe_ne_zero.2 ENat.top_ne_zero)))))
    (hpos : ∀ q, 0 < ι.symplecticNormalForm hι q (WithTop.coe_ne_zero.2 ENat.top_ne_zero)
      (e q 1) (e q Complex.I)) :
    SymplecticFraming hι hP where
  toFun q := (zeroSliceNormalEquiv J Q q).trans
    ((ContinuousLinearEquiv.smulLeft (Units.mk0 (√(ι.symplecticNormalForm hι q _ (e q 1)
      (e q Complex.I)))⁻¹ (inv_ne_zero (Real.sqrt_pos.2 (hpos q)).ne'))).trans (e q))
  contMDiff_toFun := by
    let := (zeroSlice J Q).normalSpaceFiberBundle (WithTop.coe_ne_zero.2 ENat.top_ne_zero)
      (Complex.finrank_real_eq_finrank_prod_complex_sub (F := EQ))
    let := ι.normalSpaceFiberBundle (WithTop.coe_ne_zero.2 ENat.top_ne_zero) hP
    -- The normal form of `ι` on the sections `q ↦ e q 1` and `q ↦ e q i` is smooth.
    have hl : ContMDiff J 𝓘(ℝ) ∞ fun q ↦
        ι.symplecticNormalForm hι q _ (e q 1) (e q Complex.I) := fun q ↦
      SmoothEmbedding.contMDiffAt_symplecticNormalForm (u := id) hι _ hP
        ((he.comp (contMDiff_id.prodMk contMDiff_const)) q)
        ((he.comp (contMDiff_id.prodMk contMDiff_const)) q)
    have ha : ContMDiff J 𝓘(ℝ) ∞ fun q ↦
        (√(ι.symplecticNormalForm hι q _ (e q 1) (e q Complex.I)))⁻¹ :=
      (hl.sqrt fun q ↦ (hpos q).ne').inv₀ fun q ↦ (Real.sqrt_pos.2 (hpos q)).ne'
    -- The framing is the identification with `Q × ℂ`, a rescaling of `Q × ℂ`, and `e`.
    refine (he.comp ((contMDiff_fst.prodMk ((ha.comp contMDiff_fst).smul contMDiff_snd)).comp
      contMDiff_zeroSliceNormalEquiv)).congr fun p ↦ ?_
    simp only [Function.comp_apply, Pi.smul_apply', ContinuousLinearEquiv.trans_apply,
      ContinuousLinearEquiv.smulLeft_apply_apply, Units.smul_mk0]
  symplecticNormalForm_toFun q v w := by
    simp only [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.smulLeft_apply_apply,
      Units.smul_mk0, symplecticNormalForm_zeroSlice]
    rw [(e q).map_smul, (e q).map_smul]
    -- On the plane `ℂ`, the normal form of `ι` read through `e q` is a multiple of `ω₀`.
    exact LinearMap.apply_inv_sqrt_smul_inv_sqrt_smul _ (hpos q)
      (by simpa using (LinearMap.IsAlt.apply_eq_div_mul (B := (ι.symplecticNormalForm hι q
        _).toBilinForm.compl₁₂ (e q).toLinearMap (e q).toLinearMap)
        (fun u ↦ (ι.symplecticNormalForm hι q _).self_eq_zero (e q u))
        stdComplexSymplecticForm.isAlt stdComplexSymplecticForm.separatingLeft
        Complex.basisOneI _ _))

/-- The framing `ofPos e he hpos` sends a normal vector `v` of the zero slice at `q` to
`e q ((√(λ q))⁻¹ • z)`, where `z ∈ ℂ` is the `ℂ`-component of `v` and
`λ q = ω_ι (e q 1) (e q i)`. -/
@[simp]
theorem ofPos_apply
    (he : letI := ι.normalSpaceFiberBundle (WithTop.coe_ne_zero.2 ENat.top_ne_zero) hP
      ContMDiff (J.prod 𝓘(ℝ, ℂ)) (J.prod 𝓘(ℝ, ℂ)) ∞
        (fun x : Q × ℂ ↦ (⟨x.1, e x.1 x.2⟩ :
          TotalSpace ℂ (fun q ↦ ι.isImmersion.NormalSpace q
              (WithTop.coe_ne_zero.2 ENat.top_ne_zero)))))
    (hpos : ∀ q, 0 < ι.symplecticNormalForm hι q (WithTop.coe_ne_zero.2 ENat.top_ne_zero)
      (e q 1) (e q Complex.I)) (q : Q)
    (v : (zeroSlice J Q).isImmersion.NormalSpace q (WithTop.coe_ne_zero.2 ENat.top_ne_zero)) :
    ofPos e he hpos q v = e q ((√(ι.symplecticNormalForm hι q
      (WithTop.coe_ne_zero.2 ENat.top_ne_zero) (e q 1) (e q Complex.I)))⁻¹ •
        zeroSliceNormalEquiv J Q q v) := by
  simp only [ofPos, ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.smulLeft_apply_apply,
    Units.smul_mk0]

end OfPos

section CompDiffeomorph

variable [I.Boundaryless] {EQ' HQ' : Type*} [NormedAddCommGroup EQ'] [NormedSpace ℝ EQ']
  [FiniteDimensional ℝ EQ'] [TopologicalSpace HQ'] {J' : ModelWithCorners ℝ EQ' HQ'}
  [J'.Boundaryless] {Q' : Type*} [TopologicalSpace Q'] [ChartedSpace HQ' Q'] [IsManifold J' ∞ Q']
  {hσ : σ.IsNondegenerate} {ι : SmoothEmbedding J I ∞ Q M}
  {hι : hσ.HasSymplecticTangentImages J ι} {hP : finrank ℝ ℂ = finrank ℝ E - finrank ℝ EQ}

/-- **A framing along a diffeomorphism of the source.** For a framing `Φ` of `ι` and a
diffeomorphism `χ : Q' ≃ Q`, the framing of the reparametrised embedding `ι ∘ χ`
(`TauCeti.SmoothEmbedding.compDiffeomorphOfBoundaryless`) for the same form `σ`. At `q'` it
identifies the normal space of the zero slice of `Q' × ℂ` with `ℂ` and then with the normal space
of the zero slice of `Q × ℂ` at `χ q'` (`zeroSliceNormalEquiv`), applies `Φ (χ q')`, and
identifies the normal space of `ι` at `χ q'` with that of `ι ∘ χ` at `q'`
(`TauCeti.SmoothEmbedding.normalSpaceEquivCompDiffeomorphOfBoundaryless`). The hypothesis `hι'`
follows from `hι` by
`TauCeti.SmoothEmbedding.hasSymplecticTangentImages_compDiffeomorphOfBoundaryless_iff`, and `hP'`
from `hP` when `Q'` is nonempty. -/
def compDiffeomorphOfBoundaryless (Φ : SymplecticFraming hι hP) (χ : Q' ≃ₘ⟮J', J⟯ Q)
    (hι' : hσ.HasSymplecticTangentImages J' (ι.compDiffeomorphOfBoundaryless χ (by simp)))
    (hP' : finrank ℝ ℂ = finrank ℝ E - finrank ℝ EQ') :
    SymplecticFraming hι' hP' where
  toFun q := (zeroSliceNormalEquiv J' Q' q).trans ((zeroSliceNormalEquiv J Q (χ q)).symm.trans
    ((Φ (χ q)).trans (ι.normalSpaceEquivCompDiffeomorphOfBoundaryless χ _ _ q).symm))
  contMDiff_toFun := by
    let := (zeroSlice J' Q').normalSpaceFiberBundle (WithTop.coe_ne_zero.2 ENat.top_ne_zero)
      (Complex.finrank_real_eq_finrank_prod_complex_sub (F := EQ'))
    let := (zeroSlice J Q).normalSpaceFiberBundle (WithTop.coe_ne_zero.2 ENat.top_ne_zero)
      (Complex.finrank_real_eq_finrank_prod_complex_sub (F := EQ))
    let := ι.normalSpaceFiberBundle (WithTop.coe_ne_zero.2 ENat.top_ne_zero) hP
    -- Read through the identification of normal spaces, the framing is `Φ` over `χ`, after the
    -- identifications of the normal bundles of the zero slices with `Q' × ℂ` and `Q × ℂ`.
    refine (ι.contMDiff_normalSpaceEquivCompDiffeomorphOfBoundaryless_symm_iff χ _ _ (by simp) hP
      hP' le_rfl (u := TotalSpace.proj)).2 ?_
    exact Φ.contMDiff_toFun.comp (contMDiff_zeroSliceNormalEquiv_symm.comp
      (((χ.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd).comp
        contMDiff_zeroSliceNormalEquiv))
  symplecticNormalForm_toFun q v w := by
    refine (ι.symplecticNormalForm_normalSpaceEquivCompDiffeomorphOfBoundaryless χ _ _ hι hι' q _
      _).symm.trans ?_
    simp only [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.apply_symm_apply]
    -- On both zero slices the normal form is `ω₀`, read through `zeroSliceNormalEquiv`.
    refine ((Φ.symplecticNormalForm_toFun (χ q) _ _).trans ?_).trans
      (symplecticNormalForm_zeroSlice _ q v w).symm
    rw [symplecticNormalForm_zeroSlice, ContinuousLinearEquiv.apply_symm_apply,
      ContinuousLinearEquiv.apply_symm_apply]

/-- The framing `Φ.compDiffeomorphOfBoundaryless χ hι' hP'` at `q'` is `Φ (χ q')` read through the
identifications of the normal spaces of the zero slices with `ℂ` and of those of `ι` and `ι ∘ χ`. -/
@[simp]
theorem compDiffeomorphOfBoundaryless_apply (Φ : SymplecticFraming hι hP) (χ : Q' ≃ₘ⟮J', J⟯ Q)
    (hι' : hσ.HasSymplecticTangentImages J' (ι.compDiffeomorphOfBoundaryless χ (by simp)))
    (hP' : finrank ℝ ℂ = finrank ℝ E - finrank ℝ EQ') (q : Q')
    (v : (zeroSlice J' Q').isImmersion.NormalSpace q (WithTop.coe_ne_zero.2 ENat.top_ne_zero)) :
    Φ.compDiffeomorphOfBoundaryless χ hι' hP' q v =
      (ι.normalSpaceEquivCompDiffeomorphOfBoundaryless χ (by simp)
          (WithTop.coe_ne_zero.2 ENat.top_ne_zero) q).symm
        (Φ (χ q) ((zeroSliceNormalEquiv J Q (χ q)).symm (zeroSliceNormalEquiv J' Q' q v))) :=
  (rfl)

end CompDiffeomorph

section Smul

variable {hσ : σ.IsNondegenerate} {ι : SmoothEmbedding J I ∞ Q M}
  {hι : hσ.HasSymplecticTangentImages J ι} {hP : finrank ℝ ℂ = finrank ℝ E - finrank ℝ EQ}

/-- **The framing for a constant rescaling of the ambient form.** For a framing `Φ` of `ι` for
`σ` and `c > 0`, the framing of `ι` for `c • σ` whose isomorphism at `q` multiplies by
`(√c)⁻¹` and then applies `Φ q`. It carries `ω₀` to the normal form of `ι` for `c • σ`, which is
`c` times that for `σ` (`TauCeti.SmoothEmbedding.symplecticNormalForm_smul`). -/
def smul (Φ : SymplecticFraming hι hP) {c : ℝ} (hc : 0 < c) :
    SymplecticFraming ((hσ.hasSymplecticTangentImages_smul_iff c hc.ne').2 hι) hP where
  toFun q := (ContinuousLinearEquiv.smulLeft
    (Units.mk0 (√c)⁻¹ (inv_ne_zero (Real.sqrt_pos.2 hc).ne'))).trans (Φ q)
  contMDiff_toFun := by
    let := (zeroSlice J Q).normalSpaceFiberBundle (WithTop.coe_ne_zero.2 ENat.top_ne_zero)
      (Complex.finrank_real_eq_finrank_prod_complex_sub (F := EQ))
    let := ι.normalSpaceFiberBundle (WithTop.coe_ne_zero.2 ENat.top_ne_zero) hP
    -- Rescale the `ℂ`-component of the normal bundle of the zero slice read in `Q × ℂ`.
    refine (Φ.contMDiff_toFun.comp (contMDiff_zeroSliceNormalEquiv_symm.comp
      ((contMDiff_fst.prodMk ((contMDiff_const : ContMDiff (J.prod 𝓘(ℝ, ℂ)) 𝓘(ℝ) ∞
        fun _ : Q × ℂ ↦ (√c)⁻¹).smul contMDiff_snd)).comp
        contMDiff_zeroSliceNormalEquiv))).congr fun p ↦ ?_
    simp only [Function.comp_apply, ContinuousLinearEquiv.trans_apply,
      ContinuousLinearEquiv.smulLeft_apply_apply, Units.smul_mk0, Pi.smul_apply', map_smul,
      ContinuousLinearEquiv.symm_apply_apply]
  symplecticNormalForm_toFun q v w := by
    simp only [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.smulLeft_apply_apply,
      Units.smul_mk0]
    -- The normal form of `ι` for `c • σ`, read through `Φ q`, is `c` times `ω₀`.
    refine LinearMap.apply_inv_sqrt_smul_inv_sqrt_smul ((ι.symplecticNormalForm
      ((hσ.hasSymplecticTangentImages_smul_iff c hc.ne').2 hι) q _).toBilinForm.compl₁₂
        (Φ q).toLinearMap (Φ q).toLinearMap) hc ?_
    simp only [LinearMap.compl₁₂_apply]
    rw [ι.symplecticNormalForm_smul hι hc.ne']
    simp only [SymplecticForm.rescale_apply, symplecticNormalForm_zeroSlice]
    -- A symplectic form applied to two vectors is its bilinear form applied to them.
    exact congrArg (c * ·)
      ((Φ.symplecticNormalForm_toFun q v w).trans (symplecticNormalForm_zeroSlice _ q v w))

/-- The framing `Φ.smul hc` sends a normal vector `v` of the zero slice to `Φ q ((√c)⁻¹ • v)`. -/
@[simp]
theorem smul_apply (Φ : SymplecticFraming hι hP) {c : ℝ} (hc : 0 < c) (q : Q)
    (v : (zeroSlice J Q).isImmersion.NormalSpace q (WithTop.coe_ne_zero.2 ENat.top_ne_zero)) :
    Φ.smul hc q v = Φ q ((√c)⁻¹ • v) := by
  simp only [smul, ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.smulLeft_apply_apply,
    Units.smul_mk0]

end Smul

variable (hσ : σ.IsSymplectic) {ι : SmoothEmbedding J I ∞ Q M}
  {hι : hσ.isNondegenerate.HasSymplecticTangentImages J ι}
  {hP : finrank ℝ ℂ = finrank ℝ E - finrank ℝ EQ}

/-- **The neighbourhood theorem for a framing.** A symplectic framing `Φ` of `ι` gives open sets
`U₀ ⊆ Q × ℂ` and `U₁ ⊆ M` and a diffeomorphism `ψ : U₀ ≃ U₁` pulling `σ` back to `ι^* σ ⊕ ω₀`, with
`ψ (q, 0) = ι q` and whose derivative maps the symplectic representative of each normal vector `v`
of the zero slice to that of `Φ q v`. -/
theorem exists_symplectomorphism_opens [J.Boundaryless] [I.Boundaryless] [T2Space Q]
    [SecondCountableTopology Q] [T2Space M]
    (Φ : SymplecticFraming hι hP) :
    ∃ (U₀ : Opens (Q × ℂ)) (U₁ : Opens M) (ψ : U₀ ≃ₘ⟮J.prod 𝓘(ℝ, ℂ), I⟯ U₁),
      (∀ q, ∃ h : zeroSlice J Q q ∈ U₀, (ψ ⟨zeroSlice J Q q, h⟩ : M) = ι q ∧
        ∀ v, mfderiv (J.prod 𝓘(ℝ, ℂ)) I ψ ⟨zeroSlice J Q q, h⟩
            ((zeroSlice J Q).symplecticNormalRepresentative
              (hasSymplecticTangentImages_zeroSlice hι) q
              (WithTop.coe_ne_zero.2 ENat.top_ne_zero) v) =
          ι.symplecticNormalRepresentative hι q (WithTop.coe_ne_zero.2 ENat.top_ne_zero)
            (Φ q v)) ∧
      SmoothForm.mpullback ψ ψ.contMDiff
          (SmoothForm.mpullback (Subtype.val : U₁ → M) contMDiff_subtypeVal σ) =
        SmoothForm.mpullback (Subtype.val : U₀ → Q × ℂ) contMDiff_subtypeVal
          (SmoothTwoForm.prod (SmoothForm.mpullback ι ι.contMDiff σ)
            stdComplexSymplecticForm.constSmooth) := by
  have hτ : (SmoothTwoForm.prod (SmoothForm.mpullback ι ι.contMDiff σ)
      stdComplexSymplecticForm.constSmooth).IsSymplectic :=
    (hι.isSymplectic_mpullback hσ ι.contMDiff (ι.isImmersion.mfderiv_injective (by simp))).prod
      (SymplecticForm.isSymplectic_constSmooth _)
  obtain ⟨U₀, U₁, ψ, hψ, hψσ⟩ :=
    SmoothTwoForm.IsNondegenerate.HasSymplecticTangentImages.exists_symplectomorphism_opens
      hτ hσ (hasSymplecticTangentImages_zeroSlice hι) hι
      (Diffeomorph.refl J Q ∞) (by
        rw [mpullback_zeroSlice_prod,
          SmoothForm.mpullback_eq_self_of_eq_id _ (Diffeomorph.coe_refl _ _ _)])
      (WithTop.coe_ne_zero.2 ENat.top_ne_zero) Complex.finrank_real_eq_finrank_prod_complex_sub
      hP Φ
      Φ.contMDiff_toFun Φ.symplecticNormalForm_toFun
  exact ⟨U₀, U₁, ψ, fun q ↦ (hψ q).imp fun _ h ↦ ⟨h.1, h.2.2⟩, hψσ⟩

end SymplecticFraming

/-! ### Product neighbourhoods -/

variable (Q) in
/-- The open set `Q × B²(ε)` of `Q × ℂ`, where `B²(ε)` is the open disc of radius `ε`. -/
def prodBall (ε : ℝ) : Opens (Q × ℂ) :=
  ⟨Set.univ ×ˢ Metric.ball 0 ε, isOpen_univ.prod Metric.isOpen_ball⟩

@[simp]
theorem coe_prodBall (ε : ℝ) : (prodBall Q ε : Set (Q × ℂ)) = Set.univ ×ˢ Metric.ball 0 ε :=
  (rfl)

@[simp]
theorem mem_prodBall {ε : ℝ} {p : Q × ℂ} : p ∈ prodBall Q ε ↔ ‖p.2‖ < ε := by
  simp [← SetLike.mem_coe]

variable (Q) in
/-- The product `Q × B²(ε)` of `Q` with the open disc is homeomorphic to the open set
`prodBall Q ε` of `Q × ℂ`. -/
def prodBallHomeomorph (ε : ℝ) : Q × Metric.ball (0 : ℂ) ε ≃ₜ prodBall Q ε where
  toFun w := ⟨(w.1, w.2), mem_prodBall.2 (mem_ball_zero_iff.1 w.2.property)⟩
  invFun w := ((w : Q × ℂ).1, ⟨(w : Q × ℂ).2, mem_ball_zero_iff.2 (mem_prodBall.1 w.property)⟩)
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem coe_prodBallHomeomorph_apply {ε : ℝ} (w : Q × Metric.ball (0 : ℂ) ε) :
    (prodBallHomeomorph Q ε w : Q × ℂ) = (w.1, (w.2 : ℂ)) :=
  (rfl)

@[simp]
theorem prodBallHomeomorph_symm_apply {ε : ℝ} (w : prodBall Q ε) :
    (prodBallHomeomorph Q ε).symm w =
      ((w : Q × ℂ).1, ⟨(w : Q × ℂ).2, mem_ball_zero_iff.2 (mem_prodBall.1 w.property)⟩) :=
  (rfl)

/-- For a point `(q, z)` of `Q × B²(ε)` and `t ∈ [0, 1]`, the point `(q, t • z)` is in
`Q × B²(ε)` too. -/
theorem mk_smul_mem_prodBall {ε : ℝ} (p : prodBall Q ε) (t : unitInterval) :
    ((p : Q × ℂ).1, (t : ℝ) • (p : Q × ℂ).2) ∈ prodBall Q ε := by
  rw [mem_prodBall, norm_smul, Real.norm_eq_abs, abs_of_nonneg t.property.1]
  exact (mul_le_of_le_one_left (norm_nonneg _) t.property.2).trans_lt (mem_prodBall.1 p.property)

/-- A **product neighbourhood** of radius `ε` of a smooth embedding `ι` with symplectic tangent
images, adapted to a symplectic framing `Φ`: an open embedding `f` of `Q × B²(ε)` into `M` that is
a local diffeomorphism, with `f (q, 0) = ι q`, pulling `σ` back to `ι^* σ ⊕ ω₀`, and whose
derivative at `(q, 0)` maps the symplectic representative of each normal vector `v` of the zero
slice to that of `Φ q v`. -/
structure ProductNeighborhood {hσ : σ.IsNondegenerate} {ι : SmoothEmbedding J I ∞ Q M}
    {hι : hσ.HasSymplecticTangentImages J ι} {hP : finrank ℝ ℂ = finrank ℝ E - finrank ℝ EQ}
    (Φ : SymplecticFraming hι hP) (ε : ℝ) where
  /-- The underlying map. -/
  toFun : prodBall Q ε → M
  isOpenEmbedding' : Topology.IsOpenEmbedding toFun
  isLocalDiffeomorph' : IsLocalDiffeomorph (J.prod 𝓘(ℝ, ℂ)) I ∞ toFun
  apply_zeroSlice' : ∀ q (h : zeroSlice J Q q ∈ prodBall Q ε), toFun ⟨zeroSlice J Q q, h⟩ = ι q
  mpullback_eq' : SmoothForm.mpullback toFun isLocalDiffeomorph'.contMDiff σ =
    SmoothForm.mpullback (Subtype.val : prodBall Q ε → Q × ℂ) contMDiff_subtypeVal
      (SmoothTwoForm.prod (SmoothForm.mpullback ι ι.contMDiff σ)
        stdComplexSymplecticForm.constSmooth)
  mfderiv_symplecticNormalRepresentative' : ∀ q (h : zeroSlice J Q q ∈ prodBall Q ε) v,
    mfderiv (J.prod 𝓘(ℝ, ℂ)) I toFun ⟨zeroSlice J Q q, h⟩
        ((zeroSlice J Q).symplecticNormalRepresentative (hasSymplecticTangentImages_zeroSlice hι)
          q (WithTop.coe_ne_zero.2 ENat.top_ne_zero) v) =
      ι.symplecticNormalRepresentative hι q (WithTop.coe_ne_zero.2 ENat.top_ne_zero)
        (Φ q v)

namespace ProductNeighborhood

variable {hσ : σ.IsNondegenerate} {ι : SmoothEmbedding J I ∞ Q M}
  {hι : hσ.HasSymplecticTangentImages J ι} {hP : finrank ℝ ℂ = finrank ℝ E - finrank ℝ EQ}
  {Φ : SymplecticFraming hι hP} {ε : ℝ}

instance : FunLike (ProductNeighborhood Φ ε) (prodBall Q ε) M where
  coe f := f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr

@[simp]
theorem toFun_eq_coe (f : ProductNeighborhood Φ ε) : f.toFun = ⇑f :=
  rfl

@[ext]
theorem ext {f g : ProductNeighborhood Φ ε} (h : ∀ p, f p = g p) : f = g :=
  DFunLike.ext _ _ h

theorem isOpenEmbedding (f : ProductNeighborhood Φ ε) : Topology.IsOpenEmbedding f :=
  f.isOpenEmbedding'

theorem continuous (f : ProductNeighborhood Φ ε) : Continuous f :=
  f.isOpenEmbedding.continuous

theorem isOpen_range (f : ProductNeighborhood Φ ε) : IsOpen (Set.range f) :=
  f.isOpenEmbedding.isOpen_range

theorem isLocalDiffeomorph (f : ProductNeighborhood Φ ε) :
    IsLocalDiffeomorph (J.prod 𝓘(ℝ, ℂ)) I ∞ f :=
  f.isLocalDiffeomorph'

theorem contMDiff (f : ProductNeighborhood Φ ε) : ContMDiff (J.prod 𝓘(ℝ, ℂ)) I ∞ f :=
  f.isLocalDiffeomorph.contMDiff

theorem apply_zeroSlice (f : ProductNeighborhood Φ ε) (q : Q)
    (h : zeroSlice J Q q ∈ prodBall Q ε) : f ⟨zeroSlice J Q q, h⟩ = ι q :=
  f.apply_zeroSlice' q h

/-- A product neighbourhood sends `(q, 0)` to `ι q`. -/
@[simp]
theorem apply_mk_zero (f : ProductNeighborhood Φ ε) (q : Q) (h : (q, (0 : ℂ)) ∈ prodBall Q ε) :
    f ⟨(q, 0), h⟩ = ι q := by
  rw [← f.apply_zeroSlice q (by rwa [zeroSlice_apply])]
  simp only [zeroSlice_apply]

/-- A point `f p` of the range of a product neighbourhood lies on `ι (Q)` exactly when the disc
coordinate of `p` vanishes. -/
theorem apply_mem_range_embedding_iff (f : ProductNeighborhood Φ ε) {p : prodBall Q ε} :
    f p ∈ Set.range ι ↔ (p : Q × ℂ).2 = 0 := by
  refine ⟨?_, fun h ↦ ⟨(p : Q × ℂ).1, ?_⟩⟩
  · rintro ⟨q, hq⟩
    have hq0 : (q, (0 : ℂ)) ∈ prodBall Q ε := mem_prodBall.2 (by
      simpa using (norm_nonneg _).trans_lt (mem_prodBall.1 p.property))
    rw [← f.apply_mk_zero q hq0] at hq
    rw [← f.isOpenEmbedding.injective hq]
  · have hp : p = ⟨((p : Q × ℂ).1, 0), h ▸ p.property⟩ := Subtype.ext (Prod.ext rfl h)
    rw [hp, f.apply_mk_zero]

/-- A product neighbourhood pulls `σ` back to the restriction of `ι^* σ ⊕ ω₀`. -/
theorem mpullback_eq (f : ProductNeighborhood Φ ε) :
    SmoothForm.mpullback f f.contMDiff σ =
      SmoothForm.mpullback (Subtype.val : prodBall Q ε → Q × ℂ) contMDiff_subtypeVal
        (SmoothTwoForm.prod (SmoothForm.mpullback ι ι.contMDiff σ)
          stdComplexSymplecticForm.constSmooth) :=
  f.mpullback_eq'

theorem mfderiv_symplecticNormalRepresentative (f : ProductNeighborhood Φ ε) (q : Q)
    (h : zeroSlice J Q q ∈ prodBall Q ε)
    (v : (zeroSlice J Q).isImmersion.NormalSpace q (WithTop.coe_ne_zero.2 ENat.top_ne_zero)) :
    mfderiv (J.prod 𝓘(ℝ, ℂ)) I f ⟨zeroSlice J Q q, h⟩
        ((zeroSlice J Q).symplecticNormalRepresentative (hasSymplecticTangentImages_zeroSlice hι)
          q (WithTop.coe_ne_zero.2 ENat.top_ne_zero) v) =
      ι.symplecticNormalRepresentative hι q (WithTop.coe_ne_zero.2 ENat.top_ne_zero)
        (Φ q v) :=
  f.mfderiv_symplecticNormalRepresentative' q h v

/-- For compact `Q` and Hausdorff `M`, a product neighbourhood of radius `ε` maps the closed tube
`Q × B̄²(δ)`, for `δ < ε`, onto a closed set. -/
theorem isClosed_image_closedBall [CompactSpace Q] [T2Space M] (f : ProductNeighborhood Φ ε)
    {δ : ℝ} (hδ : δ < ε) :
    IsClosed (f '' {p | ‖(p : Q × ℂ).2‖ ≤ δ}) := by
  refine (IsCompact.image ?_ f.continuous).isClosed
  rw [Subtype.isCompact_iff]
  convert (isCompact_univ (X := Q)).prod (isCompact_closedBall (0 : ℂ) δ) using 1
  ext p
  simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_prod, Set.mem_univ, true_and,
    Metric.mem_closedBall, dist_zero_right]
  refine ⟨?_, fun hp ↦ ⟨⟨p, mem_prodBall.2 (hp.trans_lt hδ)⟩, hp, rfl⟩⟩
  rintro ⟨p, hp, rfl⟩
  exact hp

/-- For compact `Q` and Hausdorff `M`, the complement of the image of the closed tube
`Q × B̄²(δ)`, for `δ < ε`, is open: it is the piece of `M` that the fiber sum keeps. -/
theorem isOpen_compl_image_closedBall [CompactSpace Q] [T2Space M]
    (f : ProductNeighborhood Φ ε) {δ : ℝ} (hδ : δ < ε) :
    IsOpen (f '' {p | ‖(p : Q × ℂ).2‖ ≤ δ})ᶜ :=
  (f.isClosed_image_closedBall hδ).isOpen_compl

variable (Φ) in
/-- The restriction to `Q × B²(ε)` of a symplectomorphism `ψ : U₀ ≃ U₁` given by
`SymplecticFraming.exists_symplectomorphism_opens`, for `Q × B²(ε) ⊆ U₀`, is a product
neighbourhood. -/
private def ofSymplectomorphism {U₀ : Opens (Q × ℂ)}
    {U₁ : Opens M} (ψ : U₀ ≃ₘ⟮J.prod 𝓘(ℝ, ℂ), I⟯ U₁)
    (hψ : ∀ q, ∃ h : zeroSlice J Q q ∈ U₀, (ψ ⟨zeroSlice J Q q, h⟩ : M) = ι q ∧
      ∀ v, mfderiv (J.prod 𝓘(ℝ, ℂ)) I ψ ⟨zeroSlice J Q q, h⟩
          ((zeroSlice J Q).symplecticNormalRepresentative
            (hasSymplecticTangentImages_zeroSlice hι) q
            (WithTop.coe_ne_zero.2 ENat.top_ne_zero) v) =
        ι.symplecticNormalRepresentative hι q (WithTop.coe_ne_zero.2 ENat.top_ne_zero)
          (Φ q v))
    (hψσ : SmoothForm.mpullback ψ ψ.contMDiff
        (SmoothForm.mpullback (Subtype.val : U₁ → M) contMDiff_subtypeVal σ) =
      SmoothForm.mpullback (Subtype.val : U₀ → Q × ℂ) contMDiff_subtypeVal
        (SmoothTwoForm.prod (SmoothForm.mpullback ι ι.contMDiff σ)
          stdComplexSymplecticForm.constSmooth))
    (hle : prodBall Q ε ≤ U₀) : ProductNeighborhood Φ ε where
  toFun := Subtype.val ∘ ψ ∘ Opens.inclusion hle
  isOpenEmbedding' := U₁.isOpen.isOpenEmbedding_subtypeVal.comp
    (ψ.toHomeomorph.isOpenEmbedding.comp
      (Topology.IsOpenEmbedding.inclusion hle (prodBall Q ε).isOpen.preimage_val))
  isLocalDiffeomorph' p := (isLocalDiffeomorph_inclusion (n := ∞) hle p).comp (hg :=
    ψ.isLocalDiffeomorph_subtypeVal_comp _)
  apply_zeroSlice' q _ := (hψ q).2.1
  mpullback_eq' := by
    refine (SmoothForm.mpullback_mpullback (Opens.inclusion hle) (Subtype.val ∘ ψ)
      (contMDiff_inclusion hle) (contMDiff_subtypeVal.comp ψ.contMDiff) σ).symm.trans ?_
    rw [← SmoothForm.mpullback_mpullback ψ Subtype.val ψ.contMDiff contMDiff_subtypeVal, hψσ,
      SmoothForm.mpullback_mpullback]
    exact SmoothForm.mpullback_congr _ _ rfl _
  mfderiv_symplecticNormalRepresentative' q h v :=
    -- The tangent spaces of `prodBall Q ε`, `U₀` and `Q × ℂ` are all the model space `EQ × ℂ`.
    (TauCeti.Manifold.mfderiv_subtype_val_comp_apply (I := I) (f := ψ ∘ Opens.inclusion hle)
      _).trans <| (mfderiv_comp_inclusion_apply hle _ _).trans ((hψ q).2.2 v)

section Exists

variable [J.Boundaryless] [I.Boundaryless] [T2Space Q] [T2Space M]
  (hσ : σ.IsSymplectic) {ι : SmoothEmbedding J I ∞ Q M}
  {hι : hσ.isNondegenerate.HasSymplecticTangentImages J ι}
  {hP : finrank ℝ ℂ = finrank ℝ E - finrank ℝ EQ}

/-- **Existence of product neighbourhoods inside an open set.** For compact `Q` and closed
nondegenerate `σ`, a symplectic framing `Φ` of `ι` and an open set `U ⊇ ι (Q)`, there is `ε₀ > 0`
such that `Φ` has a product neighbourhood of every radius `ε ≤ ε₀` whose range lies in `U`. -/
theorem exists_range_subset [CompactSpace Q] (Φ : SymplecticFraming hι hP) {U : Set M}
    (hU : IsOpen U) (hιU : Set.range ι ⊆ U) :
    ∃ ε₀ > 0, ∀ ε ≤ ε₀, ∃ f : ProductNeighborhood Φ ε, Set.range f ⊆ U := by
  -- A compact manifold over a finite-dimensional model is second countable.
  have := J.secondCountableTopology_of_sigmaCompact Q
  obtain ⟨U₀, U₁, ψ, hψ, hψσ⟩ := Φ.exists_symplectomorphism_opens hσ
  -- The points of `U₀` that `ψ` sends into `U` form an open neighbourhood of the zero slice.
  set W : Set (Q × ℂ) := Subtype.val '' ((Subtype.val ∘ ψ) ⁻¹' U)
  have hWo : IsOpen W := U₀.isOpen.isOpenMap_subtypeVal _
    (hU.preimage (continuous_subtypeVal.comp ψ.continuous))
  have hWU₀ : W ⊆ U₀ := Subtype.coe_image_subset _ _
  have hW₀ : (Set.univ : Set Q) ×ˢ {(0 : ℂ)} ⊆ W := by
    rintro ⟨q, z⟩ ⟨-, rfl : z = 0⟩
    obtain ⟨h, hq, -⟩ := hψ q
    refine ⟨⟨zeroSlice J Q q, h⟩, ?_, zeroSlice_apply q⟩
    rw [Set.mem_preimage, Function.comp_apply, hq]
    exact hιU (Set.mem_range_self q)
  obtain ⟨ε₀, hε₀, hε₀W⟩ := isCompact_univ.exists_prod_ball_subset hWo hW₀
  have hle : ∀ {ε}, ε ≤ ε₀ → ∀ p ∈ prodBall Q ε, p ∈ W := fun hε p hp ↦
    hε₀W ⟨trivial, Metric.ball_subset_ball hε (by simpa using hp)⟩
  refine ⟨ε₀, hε₀, fun ε hε ↦
    ⟨ofSymplectomorphism Φ ψ hψ hψσ (ε := ε) fun p hp ↦ hWU₀ (hle hε p hp), ?_⟩⟩
  rintro _ ⟨p, rfl⟩
  obtain ⟨y, hy, hyp⟩ := hle hε p p.property
  obtain rfl : y = Opens.inclusion (fun p hp ↦ hWU₀ (hle hε p hp)) p := Subtype.ext hyp
  exact hy

/-- **Existence of product neighbourhoods.** For compact `Q` and closed nondegenerate `σ`, a
symplectic framing `Φ` of `ι` has product neighbourhoods of every radius `ε ≤ ε₀`, for some
`ε₀ > 0`. -/
theorem «exists» [CompactSpace Q] (Φ : SymplecticFraming hι hP) :
    ∃ ε₀ > 0, ∀ ε ≤ ε₀, Nonempty (ProductNeighborhood Φ ε) :=
  (exists_range_subset hσ Φ isOpen_univ (Set.subset_univ _)).imp fun _ ⟨hε₀, h⟩ ↦
    ⟨hε₀, fun ε hε ↦ (h ε hε).elim fun f _ ↦ ⟨f⟩⟩

end Exists

end ProductNeighborhood

end SymplecticGeometry
