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
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import SymplecticGeometry.Geometry.Manifold.IsManifold.SecondCountable
import SymplecticGeometry.Topology.MetricSpace.Tube

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
* `SymplecticGeometry.SymplecticFraming hι hP`: symplectic framings of the normal bundle of `ι`;
  `SymplecticGeometry.SymplecticFraming.refl`, the identity framing of the zero slice itself.
* `SymplecticGeometry.prodBall Q ε`: the open set `Q × B²(ε)` of `Q × ℂ`.
* `SymplecticGeometry.ProductNeighborhood Φ ε`: product neighbourhoods of radius `ε` adapted to
  the framing `Φ`.

## Main results

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
  toFun : ∀ q, (zeroSlice J Q).NormalSpace q (WithTop.coe_ne_zero.2 ENat.top_ne_zero) ≃L[ℝ]
    ι.NormalSpace q (WithTop.coe_ne_zero.2 ENat.top_ne_zero)
  /-- The framing is smooth as a map of normal bundles. -/
  contMDiff_toFun :
    letI := (zeroSlice J Q).normalSpaceFiberBundle (WithTop.coe_ne_zero.2 ENat.top_ne_zero)
      (finrank_complex_eq_finrank_prod_sub (EQ := EQ))
    letI := ι.normalSpaceFiberBundle (WithTop.coe_ne_zero.2 ENat.top_ne_zero) hP
    ContMDiff (J.prod 𝓘(ℝ, ℂ)) (J.prod 𝓘(ℝ, ℂ)) ∞
      (fun p : TotalSpace ℂ
          (fun q ↦ (zeroSlice J Q).NormalSpace q (WithTop.coe_ne_zero.2 ENat.top_ne_zero)) ↦
        (⟨p.proj, toFun p.proj p.snd⟩ :
          TotalSpace ℂ (fun q ↦ ι.NormalSpace q (WithTop.coe_ne_zero.2 ENat.top_ne_zero))))
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
    (zeroSlice J Q).NormalSpace q (WithTop.coe_ne_zero.2 ENat.top_ne_zero) ≃L[ℝ]
      ι.NormalSpace q (WithTop.coe_ne_zero.2 ENat.top_ne_zero) :=
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
      (hσ₀ := hτ) (hσ₁ := hσ) (hasSymplecticTangentImages_zeroSlice hι) hι
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
    (v : (zeroSlice J Q).NormalSpace q (WithTop.coe_ne_zero.2 ENat.top_ne_zero)) :
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
