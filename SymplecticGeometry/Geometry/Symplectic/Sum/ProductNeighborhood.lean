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

/-- The normal spaces of the zero slice have the dimension of `ℂ`, the model fibre of its normal
bundle. -/
theorem finrank_zeroSlice [FiniteDimensional ℝ EQ] :
    finrank ℝ ℂ = finrank ℝ (EQ × ℂ) - finrank ℝ EQ := by
  rw [finrank_prod, Nat.add_sub_cancel_left]

/-- The zero slice pulls the product form `τ ⊕ ω₀` back to `τ`. -/
theorem mpullback_zeroSlice_prod (τ : SmoothTwoForm J Q) :
    SmoothForm.mpullback (zeroSlice J Q) (zeroSlice J Q).contMDiff
      (τ.prod stdComplexSymplecticForm.constSmooth) = τ := by
  convert SmoothTwoForm.mpullback_prodMk_left_prod τ stdComplexSymplecticForm.constSmooth
    (0 : ℂ) using 3
  exact coe_zeroSlice (J := J) (Q := Q)

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
      (finrank_zeroSlice (EQ := EQ))
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

omit [IsManifold J ∞ Q] [FiniteDimensional ℝ EQ] [FiniteDimensional ℝ E] in
/-- The normal symplectic form depends only on the ambient form, not on the proofs. -/
private theorem symplecticNormalForm_congr {EN HN N : Type*} [NormedAddCommGroup EN]
    [NormedSpace ℝ EN] [FiniteDimensional ℝ EN] [TopologicalSpace HN] {K : ModelWithCorners ℝ EN HN}
    [TopologicalSpace N]
    [ChartedSpace HN N] [IsManifold K ∞ N] {σ₁ σ₂ : SmoothTwoForm K N} (h : σ₁ = σ₂)
    {hσ₁ : σ₁.IsNondegenerate} {hσ₂ : σ₂.IsNondegenerate} {f : SmoothEmbedding J K ∞ Q N}
    (h₁ : hσ₁.HasSymplecticTangentImages J f) (h₂ : hσ₂.HasSymplecticTangentImages J f) (q : Q)
    (hn : (∞ : ℕ∞ω) ≠ 0) :
    f.symplecticNormalForm h₁ q hn = f.symplecticNormalForm h₂ q hn := by
  subst h
  rfl

/-- The **identity framing** of the zero slice of `(Q × ℂ, τ ⊕ ω₀)`, for a nondegenerate `τ`. -/
def refl {τ : SmoothTwoForm J Q} (hτ : τ.IsNondegenerate) :
    SymplecticFraming (hasSymplecticTangentImages_zeroSlice_prod hτ) finrank_zeroSlice where
  toFun _ := .refl ℝ _
  contMDiff_toFun := by
    let := (zeroSlice J Q).normalSpaceFiberBundle (WithTop.coe_ne_zero.2 ENat.top_ne_zero)
      (finrank_zeroSlice (EQ := EQ))
    -- The map of total spaces is the identity, up to the eta rule for `TotalSpace`.
    exact contMDiff_id
  symplecticNormalForm_toFun q v w :=
    congrArg (fun s : SymplecticForm _ ↦ s v w) (symplecticNormalForm_congr
      (congrArg (SmoothTwoForm.prod · stdComplexSymplecticForm.constSmooth)
        (mpullback_zeroSlice_prod τ).symm) _ _ q _)

theorem refl_toFun {τ : SmoothTwoForm J Q} (hτ : τ.IsNondegenerate) (q : Q) :
    (refl hτ).toFun q = .refl ℝ _ :=
  (rfl)

variable {hσ : σ.IsSymplectic} {ι : SmoothEmbedding J I ∞ Q M}
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
            (Φ.toFun q v)) ∧
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
        rw [mpullback_zeroSlice_prod]
        -- The identity diffeomorphism coerces to `id` by definition.
        -- (`Diffeomorph.coe_refl` cannot be rewritten under the smoothness proof.)
        exact LinearMap.congr_fun SmoothForm.mpullback_id _)
      (WithTop.coe_ne_zero.2 ENat.top_ne_zero) finrank_zeroSlice hP Φ.toFun Φ.contMDiff_toFun
      Φ.symplecticNormalForm_toFun
  exact ⟨U₀, U₁, ψ, fun q ↦ (hψ q).imp fun _ h ↦ ⟨h.1, h.2.2⟩, hψσ⟩

end SymplecticFraming

/-! ### Product neighbourhoods -/

variable (Q) in
/-- The open set `Q × B²(ε)` of `Q × ℂ`, where `B²(ε)` is the open disc of radius `ε`. -/
def prodBall (ε : ℝ) : Opens (Q × ℂ) :=
  ⟨Set.univ ×ˢ Metric.ball 0 ε, isOpen_univ.prod Metric.isOpen_ball⟩

@[simp]
theorem mem_prodBall {ε : ℝ} {p : Q × ℂ} : p ∈ prodBall Q ε ↔ ‖p.2‖ < ε := by
  simp [prodBall]

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
        (Φ.toFun q v)

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
        (Φ.toFun q v) :=
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

end ProductNeighborhood

end SymplecticGeometry
