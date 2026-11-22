/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.ImmersionDiff
public import SymplecticGeometry.Geometry.Manifold.Immersion.TangentEndomorphism
public import TauCeti.Geometry.Manifold.DifferentialForm.Closed
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Basic
public import TauCeti.Geometry.Symplectic.Lagrangian.Embedding.Symplectic.Basic

/-!
# Complex submanifolds of almost complex manifolds

Let `J` be a smooth almost complex structure on `M` and `f : N → M` a smooth embedding whose
tangent images `df_x (T_x N)` are `J`-invariant, the hypothesis being written
`hJ : ∀ x, ∀ v ∈ f.tangentRange x hn, J (f x) v ∈ f.tangentRange x hn` as in
`SymplecticGeometry/Geometry/Manifold/SmoothEmbedding/NormalSpace/ComplexStructure.lean`.

Then `J` restricts to a smooth almost complex structure `J.restrict f hJ` on `N`, given at `x` by
`(df_x)⁻¹ ∘ J_{f x} ∘ df_x`, where `(df_x)⁻¹` is any left inverse of `df_x`: since `J_{f x}`
preserves the image of `df_x`, the choice does not matter (`restrict_apply`). It is the unique
almost complex structure on `N` for which every differential of `f` is complex linear
(`mfderiv_restrict_apply`, `eq_restrict_iff`). Its smoothness is
`ContMDiff.tangentEnd_of_mfderiv`, which tests it after the differential of `f`.

A two-form `σ` on `M` taming `J` pulls back to a form taming the restriction, hence a
nondegenerate one; invariance and compatibility pass to the pull-back in the same way. So `f` is a
symplectic submanifold embedding for `σ` in the sense of Tau Ceti's
`TauCeti.SmoothTwoForm.IsNondegenerate.IsSymplecticSubmanifoldEmbedding`, and if `σ` is
symplectic, so is its pull-back. Each of these is checked on `df_x v`, so the linear facts on the
image of `df_x`, such as Tau Ceti's `TauCeti.SymplecticForm.Compatible.restrict`, are not needed.

The API of the restriction and the three form lemmas adapt Tau Ceti's
`TauCeti.SmoothAlmostComplexStructure.pullback`,
`TauCeti.ContMDiffAlmostComplexStructure.eq_pullback_iff`, `TauCeti.SmoothTwoForm.Tames.pullback`,
`TauCeti.SmoothTwoForm.Invariant.pullback` and `TauCeti.SmoothTwoForm.Compatible.pullback`, from
`TauCeti/Geometry/Symplectic/Manifold/AlmostComplex/Pullback.lean`, from diffeomorphisms to
embeddings.

Nothing here assumes `N` nonempty or of positive dimension.

## Main definitions

* `TauCeti.SmoothAlmostComplexStructure.restrict`: the almost complex structure that `J` induces
  on a submanifold with `J`-invariant tangent spaces.

## Main results

* `TauCeti.SmoothAlmostComplexStructure.mfderiv_restrict_apply`: the differentials of the
  embedding are complex linear, `df_x ∘ (J.restrict f hJ)_x = J_{f x} ∘ df_x`.
* `TauCeti.SmoothAlmostComplexStructure.eq_restrict_iff`: the restriction is the only structure
  with this property.
* `TauCeti.SmoothTwoForm.Tames.restrict`, `TauCeti.SmoothTwoForm.Invariant.restrict`,
  `TauCeti.SmoothTwoForm.Compatible.restrict`: taming, invariance and compatibility pass to the
  pull-back of the form and the restriction of the structure.
* `TauCeti.SmoothTwoForm.Tames.isSymplecticSubmanifoldEmbedding`: the embedding of a complex
  submanifold is a symplectic submanifold embedding for a taming form.
* `TauCeti.SmoothTwoForm.Tames.isSymplectic_mpullback`: a symplectic form taming `J` pulls back to
  a symplectic form.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Exercise 4.3.5.
-/

public section

noncomputable section

open Bundle Function ContinuousLinearMap
open scoped Manifold ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  {hn : (∞ : ℕ∞ω) ≠ 0}

namespace SmoothAlmostComplexStructure

variable (J : SmoothAlmostComplexStructure I M) (f : SmoothEmbedding I' I ∞ N M)

/-- The endomorphism `L ∘ J_{f x} ∘ df_x` of `T_x N`, for the left inverse `L` of `df_x` chosen
by `HasLeftInverse.leftInverse`; `df_x` has one since `f` is an immersion. -/
private def restrictEnd (x : N) : TangentSpace I' x →L[ℝ] TangentSpace I' x :=
  (isDiffImmersionAt_iff.mp (f.isImmersion.isDiffImmersionAt (by simp) x)).leftInverse ∘L
    J.toEndomorphism (f x) ∘L mfderiv I' I f x

variable {J f}

/-- If `J` preserves the tangent image at `x`, then for every left inverse `L` of `df_x`, the
differential `df_x` carries `L ∘ J_{f x} ∘ df_x` to `J_{f x} ∘ df_x`. -/
private theorem mfderiv_apply_of_leftInverse
    (hJ : ∀ x, ∀ v ∈ f.tangentRange x hn, J (f x) v ∈ f.tangentRange x hn) {x : N}
    {L : TangentSpace I (f x) →L[ℝ] TangentSpace I' x} (hL : LeftInverse L (mfderiv I' I f x))
    (v : TangentSpace I' x) :
    mfderiv I' I f x (L (J (f x) (mfderiv I' I f x v))) = J (f x) (mfderiv I' I f x v) := by
  obtain ⟨u, hu⟩ := (f.mem_tangentRange_iff x hn _).1
    (hJ x _ ((f.mem_tangentRange_iff x hn _).2 ⟨v, rfl⟩))
  rw [← hu, hL u]

private theorem mfderiv_restrictEnd_apply
    (hJ : ∀ x, ∀ v ∈ f.tangentRange x hn, J (f x) v ∈ f.tangentRange x hn) (x : N)
    (v : TangentSpace I' x) :
    mfderiv I' I f x (restrictEnd J f x v) = J (f x) (mfderiv I' I f x v) :=
  mfderiv_apply_of_leftInverse hJ
    (isDiffImmersionAt_iff.mp (f.isImmersion.isDiffImmersionAt (by simp) x)).leftInverse_leftInverse
    v

variable [CompleteSpace E'] [IsManifold I' ∞ N] (J f)

/-- The almost complex structure induced by `J` on the source of a smooth embedding `f` whose
tangent images are `J`-invariant: at `x` it is `(df_x)⁻¹ ∘ J_{f x} ∘ df_x`, for any left
inverse `(df_x)⁻¹` of `df_x`. -/
def restrict (hJ : ∀ x, ∀ v ∈ f.tangentRange x hn, J (f x) v ∈ f.tangentRange x hn) :
    SmoothAlmostComplexStructure I' N where
  toEndomorphism :=
    ⟨restrictEnd J f, f.contMDiff.tangentEnd_of_mfderiv (by simp)
      (fun x ↦ isDiffImmersionAt_iff.mp (f.isImmersion.isDiffImmersionAt (by simp) x))
      (fun x ↦ J.toEndomorphism.contMDiff.comp f.contMDiff x)
      fun x ↦ ContinuousLinearMap.ext (mfderiv_restrictEnd_apply hJ x)⟩
  square_neg x := ContinuousLinearMap.ext fun v ↦ f.isImmersion.mfderiv_injective (by simp) x <| by
    simp only [ContinuousLinearMap.comp_apply, ContMDiffSection.coeFn_mk,
      mfderiv_restrictEnd_apply hJ, _root_.neg_apply, ContinuousLinearMap.id_apply, map_neg]
    exact J.apply_apply (f x) _

variable {f J}
variable (hJ : ∀ x, ∀ v ∈ f.tangentRange x hn, J (f x) v ∈ f.tangentRange x hn)
include hJ

/-- The restricted structure at `x` is `L ∘ J_{f x} ∘ df_x` for every left inverse `L` of
`df_x`. -/
theorem restrict_apply {x : N} {L : TangentSpace I (f x) →L[ℝ] TangentSpace I' x}
    (hL : LeftInverse L (mfderiv I' I f x)) (v : TangentSpace I' x) :
    J.restrict f hJ x v = L (J (f x) (mfderiv I' I f x v)) :=
  f.isImmersion.mfderiv_injective (by simp) x <| (mfderiv_restrictEnd_apply hJ x v).trans
    (mfderiv_apply_of_leftInverse hJ hL v).symm

/-- The differentials of the embedding are complex linear from the restricted structure to `J`:
`df_x ((J.restrict f hJ)_x v) = J_{f x} (df_x v)`. -/
@[simp]
theorem mfderiv_restrict_apply (x : N) (v : TangentSpace I' x) :
    mfderiv I' I f x (J.restrict f hJ x v) = J (f x) (mfderiv I' I f x v) :=
  mfderiv_restrictEnd_apply hJ x v

/-- The differential of the embedding at `x` is complex linear for the restricted structure and
`J`. -/
theorem isComplexLinearMap_mfderiv (x : N) :
    IsComplexLinearMap ((J.restrict f hJ).almostComplexStructureAt x)
      (J.almostComplexStructureAt (f x)) (mfderiv I' I f x).toLinearMap := by
  rw [isComplexLinearMap_iff_apply]
  intro v
  simp only [ContinuousLinearMap.coe_coe, almostComplexStructureAt_apply,
    mfderiv_restrict_apply]

/-- The restricted structure is the only almost complex structure on `N` for which every
differential of the embedding is complex linear into `J`. -/
theorem eq_restrict_iff {K : SmoothAlmostComplexStructure I' N} :
    K = J.restrict f hJ ↔
      ∀ (x : N) (v : TangentSpace I' x),
        mfderiv I' I f x (K x v) = J (f x) (mfderiv I' I f x v) := by
  refine ⟨fun h x v ↦ h ▸ mfderiv_restrict_apply hJ x v, fun h ↦ ext fun x v ↦ ?_⟩
  exact f.isImmersion.mfderiv_injective (by simp) x
    ((h x v).trans (mfderiv_restrict_apply hJ x v).symm)

end SmoothAlmostComplexStructure

namespace SmoothTwoForm

variable [CompleteSpace E'] [IsManifold I' ∞ N]
  {σ : SmoothTwoForm I M} {J : SmoothAlmostComplexStructure I M}
  {f : SmoothEmbedding I' I ∞ N M}
  (hJ : ∀ x, ∀ v ∈ f.tangentRange x hn, J (f x) v ∈ f.tangentRange x hn)
include hJ

/-- If `σ` tames `J`, then the pull-back of `σ` to a complex submanifold tames the restricted
structure. In particular the pull-back is nondegenerate (`SmoothTwoForm.Tames.isNondegenerate`). -/
theorem Tames.restrict (hσ : σ.Tames J) :
    SmoothTwoForm.Tames (SmoothForm.mpullback f f.contMDiff σ) (J.restrict f hJ) := by
  rw [tames_iff]
  intro x v hv
  rw [SmoothForm.eval₂_mpullback, SmoothAlmostComplexStructure.mfderiv_restrict_apply]
  exact tames_iff.1 hσ (f x) _
    ((map_ne_zero_iff _ (f.isImmersion.mfderiv_injective (by simp) x)).2 hv)

/-- If `σ` is invariant under `J`, then the pull-back of `σ` to a complex submanifold is invariant
under the restricted structure. -/
theorem Invariant.restrict (hσ : σ.Invariant J) :
    SmoothTwoForm.Invariant (SmoothForm.mpullback f f.contMDiff σ) (J.restrict f hJ) := by
  rw [invariant_iff]
  intro x v w
  simp only [SmoothForm.eval₂_mpullback, SmoothAlmostComplexStructure.mfderiv_restrict_apply]
  exact invariant_iff.1 hσ (f x) _ _

/-- If `σ` is compatible with `J`, then the pull-back of `σ` to a complex submanifold is
compatible with the restricted structure. -/
theorem Compatible.restrict (hσ : σ.Compatible J) :
    SmoothTwoForm.Compatible (SmoothForm.mpullback f f.contMDiff σ) (J.restrict f hJ) :=
  ⟨hσ.invariant.restrict hJ, hσ.tames.restrict hJ⟩

/-- If `σ` tames `J`, then a smooth embedding with `J`-invariant tangent images is a symplectic
submanifold embedding for `σ`. -/
theorem Tames.isSymplecticSubmanifoldEmbedding (hσ : σ.Tames J) :
    hσ.isNondegenerate.IsSymplecticSubmanifoldEmbedding I' f :=
  (IsNondegenerate.isSymplecticSubmanifoldEmbedding_iff_isNondegenerate_mpullback
    f.isSmoothEmbedding).2 (hσ.restrict hJ).isNondegenerate

/-- A symplectic form taming `J` pulls back to a symplectic form on a complex submanifold. -/
theorem Tames.isSymplectic_mpullback (hσ : σ.Tames J) (hσs : σ.IsSymplectic) :
    SmoothTwoForm.IsSymplectic (SmoothForm.mpullback f f.contMDiff σ) :=
  ⟨hσs.isClosed.mpullback f f.contMDiff, (hσ.restrict hJ).isNondegenerate⟩

end SmoothTwoForm

end TauCeti
