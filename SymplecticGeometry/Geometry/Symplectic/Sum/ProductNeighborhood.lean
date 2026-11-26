/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Neighborhood.Symplectic
public import SymplecticGeometry.Geometry.Symplectic.Manifold.Prod
public import TauCeti.Geometry.Symplectic.Complex.Line
import TauCeti.Geometry.Symplectic.Lagrangian.Embedding.Symplectic.Basic
import TauCeti.Geometry.Symplectic.Lagrangian.Graph
import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Level
import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.Equiv
import TauCeti.Geometry.Manifold.VectorBundle.Trivial
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import SymplecticGeometry.Geometry.Manifold.IsManifold.SecondCountable
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Pullback
import SymplecticGeometry.Topology.MetricSpace.Tube
import SymplecticGeometry.LinearAlgebra.BilinearMap.Alternating
import TauCeti.Geometry.Manifold.ContMDiff.Sqrt
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
  `SymplecticGeometry.SymplecticFraming.ofPos`, the framing obtained from linear isomorphisms
  `e q : ℂ ≃ N_q ι`, smooth in `q`, on which the normal form `ω_ι` of `ι` is positive, by rescaling
  `e q` by `(√(ω_ι (e q 1) (e q i)))⁻¹`. On the plane `ℂ` every alternating form is a multiple
  of `ω₀` (`LinearMap.IsAlt.apply_eq_div_mul`), so the rescaling carries `ω₀` exactly to `ω_ι`;
  the rescaling factor is smooth by `TauCeti.SmoothEmbedding.contMDiffAt_symplecticNormalForm`
  and `ContMDiff.sqrt`. The construction adapts the rescaled
  isomorphisms of `HasSymplecticTangentImages.exists_symplectomorphism_opens_of_finrank_eq_two`
  (namespace `TauCeti.SmoothTwoForm.IsNondegenerate`, `Geometry/Symplectic/Neighborhood/CodimTwo`),
  with an explicit factor in place of a ratio on a local frame.
* `SymplecticGeometry.prodBall Q ε`: the open set `Q × B²(ε)` of `Q × ℂ`.
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
* `SymplecticGeometry.ProductNeighborhood.exists`: for compact `Q`, a framing has product
  neighbourhoods of every radius up to some `ε₀ > 0`. The neighbourhood theorem for the framing
  gives a symplectomorphism `ψ` from an open neighbourhood `U₀` of the zero slice; by the tube
  lemma `U₀` contains some `Q × B²(ε₀)`, and the restriction of `ψ` to it is the product
  neighbourhood.

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

/-- The real dimension of `ℂ` is the codimension of `Q` in `Q × ℂ`. This is the hypothesis on the
model fibre that `TauCeti.SmoothEmbedding.normalSpaceFiberBundle` takes for the zero slice. -/
theorem finrank_complex_eq_finrank_prod_sub [FiniteDimensional ℝ EQ] :
    finrank ℝ ℂ = finrank ℝ (EQ × ℂ) - finrank ℝ EQ := by
  rw [finrank_prod, Nat.add_sub_cancel_left]

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
  ((zeroSlice J Q).isImmersion.finrank_normalSpace q _).trans finrank_complex_eq_finrank_prod_sub.symm

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
        ((zeroSlice J Q).isImmersion.normalClass q (WithTop.coe_ne_zero.2 ENat.top_ne_zero) v) = v.2 :=
  (zeroSlice J Q).isImmersion.normalSpaceEquivOfKer_normalClass q _ _ _ _ v

/-- The inverse of `zeroSliceNormalEquiv` sends `z` to the normal class of the vertical vector
`(0, z)`. -/
theorem zeroSliceNormalEquiv_symm_apply (q : Q) (z : ℂ) :
    (zeroSliceNormalEquiv J Q q).symm z =
      (zeroSlice J Q).isImmersion.normalClass q (WithTop.coe_ne_zero.2 ENat.top_ne_zero) ((0, z) : EQ × ℂ) :=
  (zeroSlice J Q).isImmersion.normalSpaceEquivOfKer_symm_apply q _ _ _ _ ((0, z) : EQ × ℂ)

variable (J Q) in
/-- The normal bundle of the zero slice, with the bundle structure that `SymplecticFraming` uses,
is diffeomorphic to `Q × ℂ` over the identity of `Q`, by `zeroSliceNormalEquiv` on each fibre. -/
def zeroSliceNormalBundleDiffeomorph :
    letI := (zeroSlice J Q).normalSpaceFiberBundle (WithTop.coe_ne_zero.2 ENat.top_ne_zero)
      (finrank_complex_eq_finrank_prod_sub (EQ := EQ))
    TotalSpace ℂ (fun q ↦ (zeroSlice J Q).isImmersion.NormalSpace q (WithTop.coe_ne_zero.2 ENat.top_ne_zero))
      ≃ₘ⟮J.prod 𝓘(ℝ, ℂ), J.prod 𝓘(ℝ, ℂ)⟯ Q × ℂ :=
  letI := (zeroSlice J Q).normalSpaceFiberBundle (WithTop.coe_ne_zero.2 ENat.top_ne_zero)
    (finrank_complex_eq_finrank_prod_sub (EQ := EQ))
  ((zeroSlice J Q).normalBundleDiffeomorphOfKer (m := ∞) _ (by simp)
    finrank_complex_eq_finrank_prod_sub (E₂ := Trivial Q ℂ) (W := ℂ)
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
      (fun q ↦ (zeroSlice J Q).isImmersion.NormalSpace q (WithTop.coe_ne_zero.2 ENat.top_ne_zero))) :
    letI := (zeroSlice J Q).normalSpaceFiberBundle (WithTop.coe_ne_zero.2 ENat.top_ne_zero)
      (finrank_complex_eq_finrank_prod_sub (EQ := EQ))
    zeroSliceNormalBundleDiffeomorph J Q p = (p.proj, zeroSliceNormalEquiv J Q p.proj p.snd) := by
  let := (zeroSlice J Q).normalSpaceFiberBundle (WithTop.coe_ne_zero.2 ENat.top_ne_zero)
    (finrank_complex_eq_finrank_prod_sub (EQ := EQ))
  exact (congrArg (Trivial.diffeomorphProd J Q ℂ ∞)
    ((zeroSlice J Q).normalBundleDiffeomorphOfKer_apply _ _ _ _ _ _ _ p)).trans
    (Trivial.diffeomorphProd_apply ..)

/-- The inverse diffeomorphism sends `(q, z)` to the normal vector at `q` with `ℂ`-component
`z`. -/
@[simp]
theorem zeroSliceNormalBundleDiffeomorph_symm_apply (x : Q × ℂ) :
    letI := (zeroSlice J Q).normalSpaceFiberBundle (WithTop.coe_ne_zero.2 ENat.top_ne_zero)
      (finrank_complex_eq_finrank_prod_sub (EQ := EQ))
    (zeroSliceNormalBundleDiffeomorph J Q).symm x =
      ⟨x.1, (zeroSliceNormalEquiv J Q x.1).symm x.2⟩ := by
  let := (zeroSlice J Q).normalSpaceFiberBundle (WithTop.coe_ne_zero.2 ENat.top_ne_zero)
    (finrank_complex_eq_finrank_prod_sub (EQ := EQ))
  exact ((zeroSlice J Q).normalBundleDiffeomorphOfKer_symm_apply (m := ∞) _ (by simp) _ _ _ _ _
    ((Trivial.diffeomorphProd J Q ℂ ∞).symm x)).trans
      (by rw [Trivial.diffeomorphProd_symm_apply, zeroSliceNormalEquiv_def])

/-- The identification of the normal bundle of the zero slice with `Q × ℂ` is smooth. -/
theorem contMDiff_zeroSliceNormalEquiv :
    letI := (zeroSlice J Q).normalSpaceFiberBundle (WithTop.coe_ne_zero.2 ENat.top_ne_zero)
      (finrank_complex_eq_finrank_prod_sub (EQ := EQ))
    ContMDiff (J.prod 𝓘(ℝ, ℂ)) (J.prod 𝓘(ℝ, ℂ)) ∞
      (fun p : TotalSpace ℂ
          (fun q ↦ (zeroSlice J Q).isImmersion.NormalSpace q (WithTop.coe_ne_zero.2 ENat.top_ne_zero)) ↦
        (p.proj, zeroSliceNormalEquiv J Q p.proj p.snd)) := by
  let := (zeroSlice J Q).normalSpaceFiberBundle (WithTop.coe_ne_zero.2 ENat.top_ne_zero)
    (finrank_complex_eq_finrank_prod_sub (EQ := EQ))
  exact (zeroSliceNormalBundleDiffeomorph J Q).contMDiff.congr
    fun p ↦ (zeroSliceNormalBundleDiffeomorph_apply p).symm

/-- The inverse identification of `Q × ℂ` with the normal bundle of the zero slice is smooth. -/
theorem contMDiff_zeroSliceNormalEquiv_symm :
    letI := (zeroSlice J Q).normalSpaceFiberBundle (WithTop.coe_ne_zero.2 ENat.top_ne_zero)
      (finrank_complex_eq_finrank_prod_sub (EQ := EQ))
    ContMDiff (J.prod 𝓘(ℝ, ℂ)) (J.prod 𝓘(ℝ, ℂ)) ∞
      (fun x : Q × ℂ ↦ (⟨x.1, (zeroSliceNormalEquiv J Q x.1).symm x.2⟩ : TotalSpace ℂ
          (fun q ↦ (zeroSlice J Q).isImmersion.NormalSpace q (WithTop.coe_ne_zero.2 ENat.top_ne_zero)))) := by
  let := (zeroSlice J Q).normalSpaceFiberBundle (WithTop.coe_ne_zero.2 ENat.top_ne_zero)
    (finrank_complex_eq_finrank_prod_sub (EQ := EQ))
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
  toFun : ∀ q, (zeroSlice J Q).isImmersion.NormalSpace q (WithTop.coe_ne_zero.2 ENat.top_ne_zero) ≃L[ℝ]
    ι.isImmersion.NormalSpace q (WithTop.coe_ne_zero.2 ENat.top_ne_zero)
  /-- The framing is smooth as a map of normal bundles. -/
  contMDiff_toFun :
    letI := (zeroSlice J Q).normalSpaceFiberBundle (WithTop.coe_ne_zero.2 ENat.top_ne_zero)
      (finrank_complex_eq_finrank_prod_sub (EQ := EQ))
    letI := ι.normalSpaceFiberBundle (WithTop.coe_ne_zero.2 ENat.top_ne_zero) hP
    ContMDiff (J.prod 𝓘(ℝ, ℂ)) (J.prod 𝓘(ℝ, ℂ)) ∞
      (fun p : TotalSpace ℂ
          (fun q ↦ (zeroSlice J Q).isImmersion.NormalSpace q (WithTop.coe_ne_zero.2 ENat.top_ne_zero)) ↦
        (⟨p.proj, toFun p.proj p.snd⟩ :
          TotalSpace ℂ (fun q ↦ ι.isImmersion.NormalSpace q (WithTop.coe_ne_zero.2 ENat.top_ne_zero))))
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
      finrank_complex_eq_finrank_prod_sub where
  toFun _ := .refl ℝ _
  contMDiff_toFun := by
    let := (zeroSlice J Q).normalSpaceFiberBundle (WithTop.coe_ne_zero.2 ENat.top_ne_zero)
      (finrank_complex_eq_finrank_prod_sub (EQ := EQ))
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
          TotalSpace ℂ (fun q ↦ ι.isImmersion.NormalSpace q (WithTop.coe_ne_zero.2 ENat.top_ne_zero)))))
    (hpos : ∀ q, 0 < ι.symplecticNormalForm hι q (WithTop.coe_ne_zero.2 ENat.top_ne_zero)
      (e q 1) (e q Complex.I)) :
    SymplecticFraming hι hP where
  toFun q := (zeroSliceNormalEquiv J Q q).trans
    ((ContinuousLinearEquiv.smulLeft (Units.mk0 (√(ι.symplecticNormalForm hι q _ (e q 1)
      (e q Complex.I)))⁻¹ (inv_ne_zero (Real.sqrt_pos.2 (hpos q)).ne'))).trans (e q))
  contMDiff_toFun := by
    let := (zeroSlice J Q).normalSpaceFiberBundle (WithTop.coe_ne_zero.2 ENat.top_ne_zero)
      (finrank_complex_eq_finrank_prod_sub (EQ := EQ))
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
          TotalSpace ℂ (fun q ↦ ι.isImmersion.NormalSpace q (WithTop.coe_ne_zero.2 ENat.top_ne_zero)))))
    (hpos : ∀ q, 0 < ι.symplecticNormalForm hι q (WithTop.coe_ne_zero.2 ENat.top_ne_zero)
      (e q 1) (e q Complex.I)) (q : Q)
    (v : (zeroSlice J Q).isImmersion.NormalSpace q (WithTop.coe_ne_zero.2 ENat.top_ne_zero)) :
    ofPos e he hpos q v = e q ((√(ι.symplecticNormalForm hι q
      (WithTop.coe_ne_zero.2 ENat.top_ne_zero) (e q 1) (e q Complex.I)))⁻¹ •
        zeroSliceNormalEquiv J Q q v) := by
  simp only [ofPos, ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.smulLeft_apply_apply,
    Units.smul_mk0]

end OfPos

variable (hσ : σ.IsSymplectic) {ι : SmoothEmbedding J I ∞ Q M}
  {hι : hσ.isNondegenerate.HasSymplecticTangentImages J ι}
  {hP : finrank ℝ ℂ = finrank ℝ E - finrank ℝ EQ}

/-- **The neighbourhood theorem for a framing.** A symplectic framing `Φ` of `ι` gives open sets
`U₀ ⊆ Q × ℂ` and `U₁ ⊆ M` and a diffeomorphism `ψ : U₀ ≃ U₁` pulling `σ` back to `ι^* σ ⊕ ω₀`, with
`ψ (q, 0) = ι q` and whose derivative maps the symplectic representative of each normal vector `v`
of the zero slice to that of `Φ q v`. -/
theorem exists_symplectomorphism_opens [J.Boundaryless] [I.Boundaryless] [T2Space Q]
    [SecondCountableTopology Q] [T2Space M] [SecondCountableTopology M]
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
          SmoothForm.mpullback_congr _ contMDiff_id (Diffeomorph.coe_refl _ _ _)]
        exact LinearMap.congr_fun SmoothForm.mpullback_id _)
      (WithTop.coe_ne_zero.2 ENat.top_ne_zero) finrank_complex_eq_finrank_prod_sub hP Φ
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
    (ψ.isLocalDiffeomorph _).comp (hg := TauCeti.isLocalDiffeomorph_subtype_val _))
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
      _).trans <| (mfderiv_comp_apply _ (ψ.contMDiff.mdifferentiableAt (by simp))
        ((contMDiff_inclusion (n := 1) hle).mdifferentiableAt one_ne_zero) _).trans <|
      (congrArg _ (TauCeti.Manifold.mfderiv_inclusion_apply hle _ _)).trans ((hψ q).2.2 v)

section Exists

variable [J.Boundaryless] [I.Boundaryless] [T2Space Q] [T2Space M] [SecondCountableTopology M]
  (hσ : σ.IsSymplectic) {ι : SmoothEmbedding J I ∞ Q M}
  {hι : hσ.isNondegenerate.HasSymplecticTangentImages J ι}
  {hP : finrank ℝ ℂ = finrank ℝ E - finrank ℝ EQ}

/-- **Existence of product neighbourhoods.** For compact `Q` and closed nondegenerate `σ`, a
symplectic framing `Φ` of `ι` has product neighbourhoods of every radius `ε ≤ ε₀`, for some
`ε₀ > 0`. -/
theorem «exists» [CompactSpace Q] (Φ : SymplecticFraming hι hP) :
    ∃ ε₀ > 0, ∀ ε ≤ ε₀, Nonempty (ProductNeighborhood Φ ε) := by
  -- A compact manifold over a finite-dimensional model is second countable.
  have := J.secondCountableTopology_of_sigmaCompact Q
  obtain ⟨U₀, U₁, ψ, hψ, hψσ⟩ := Φ.exists_symplectomorphism_opens hσ
  have hU₀ : (Set.univ : Set Q) ×ˢ {(0 : ℂ)} ⊆ U₀ := by
    rintro ⟨q, z⟩ ⟨-, rfl : z = 0⟩
    simpa using (hψ q).1
  obtain ⟨ε₀, hε₀, hε₀U⟩ := isCompact_univ.exists_prod_ball_subset U₀.isOpen hU₀
  refine ⟨ε₀, hε₀, fun ε hε ↦
    ⟨ofSymplectomorphism Φ ψ hψ hψσ (ε := ε) fun p hp ↦ hε₀U ⟨trivial, ?_⟩⟩⟩
  exact Metric.ball_subset_ball hε (by simpa using hp)

end Exists

end ProductNeighborhood

end SymplecticGeometry
