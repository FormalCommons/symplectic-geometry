/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.ImmersionDiff
public import SymplecticGeometry.Geometry.Manifold.Immersion.TangentEndomorphism
public import SymplecticGeometry.Geometry.Symplectic.Manifold.Nijenhuis
public import TauCeti.Geometry.Manifold.DifferentialForm.Closed
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Basic
public import TauCeti.Geometry.Symplectic.Lagrangian.Embedding.Symplectic.Basic
public import SymplecticGeometry.Geometry.Manifold.Complex.Integrable
public import TauCeti.Geometry.Symplectic.Manifold.Kahler
import SymplecticGeometry.LinearAlgebra.ComplexStructure.Hom
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import SymplecticGeometry.Geometry.Manifold.VectorField.Immersion

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

The Nijenhuis tensor of the restriction is read through `df_x`:
`df_x (N_{J|_N}(v, w)) = N_J(df_x v, df_x w)`. Every tangent vector of `N` is the value of a field
that is `f`-related near `x` to a field on `M`
(`Manifold.IsImmersionAt.exists_vectorField_mfderiv_eventuallyEq`), and `J|_N` intertwines with
`J` through `df`, so this is the naturality of the Nijenhuis tensor for related fields,
`TauCeti.SmoothAlmostComplexStructure.mfderiv_nijenhuis_of_eventually_related`. Hence
`N_J = 0` gives `N_{J|_N} = 0`, and a Kähler pair in the sense of Tau Ceti's
`TauCeti.SmoothTwoForm.IsKahler`, which asks for `N_J = 0`, restricts to a Kähler pair.

The API of the restriction and the three form lemmas adapt Tau Ceti's
`TauCeti.SmoothAlmostComplexStructure.pullback`,
`TauCeti.ContMDiffAlmostComplexStructure.eq_pullback_iff`, `TauCeti.SmoothTwoForm.Tames.pullback`,
`TauCeti.SmoothTwoForm.Invariant.pullback` and `TauCeti.SmoothTwoForm.Compatible.pullback`, from
`TauCeti/Geometry/Symplectic/Manifold/AlmostComplex/Pullback.lean`, from diffeomorphisms to
embeddings.

If `J` is integrable and `N` has no boundary, the restriction is integrable
(`IsIntegrable.restrict`). Around `x : N`, take a chart `ψ` of `M` at `f x` in which `J` is a
constant `J₀`. The differential `A` of `ψ ∘ f` at `x` is injective and complex linear, so it has
a complex linear left inverse `G` (`TauCeti.IsComplexLinearMap.exists_leftInverse_of_injective`).
The differential of `G ∘ ψ ∘ f` at `x` is the identity, so by the inverse function theorem (Tau
Ceti's `isLocalDiffeomorphAt_of_mfderiv_eq`) it is a local diffeomorphism at `x`, and on
`f⁻¹(ψ.source)` its differential carries the restricted structure to the constant structure that
it has at `x`; this gives integrability by `isIntegrable_of_forall_exists_isLocalDiffeomorphAt`.
The hypothesis on the boundary is needed, since integrability asks for charts onto open subsets
of the model space.

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
* `TauCeti.SmoothAlmostComplexStructure.mfderiv_nijenhuis_restrict`,
  `TauCeti.SmoothAlmostComplexStructure.nijenhuis_restrict_apply`: the Nijenhuis tensor of the
  restriction is the Nijenhuis tensor of `J` read through `df_x`.
* `TauCeti.SmoothAlmostComplexStructure.nijenhuis_restrict_eq_zero`,
  `TauCeti.SmoothTwoForm.IsKahler.restrict`: vanishing of the Nijenhuis tensor and the Kähler
  condition pass to complex submanifolds.
* `TauCeti.SmoothTwoForm.Tames.complex_submanifold`: these statements together.
* `TauCeti.SmoothAlmostComplexStructure.IsIntegrable.restrict`: integrability passes to the
  restriction on a boundaryless submanifold.

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

/-- **Integrability passes to complex submanifolds.** If `J` is integrable, then so is its
restriction to a boundaryless submanifold with `J`-invariant tangent spaces.

The hypothesis that `N` has no boundary cannot be dropped: integrability asks for charts onto
open subsets of the model space around every point, which a boundary point does not have. For
instance, a closed half-disc in a complex line of `ℂ²` has `J`-invariant tangent spaces, but its
restricted structure is not integrable. -/
theorem IsIntegrable.restrict [FiniteDimensional ℝ E] [BoundarylessManifold I' N]
    (hint : J.IsIntegrable) : (J.restrict f hJ).IsIntegrable := by
  rw [isIntegrable_iff_mfderiv] at hint
  refine isIntegrable_of_forall_exists_isLocalDiffeomorphAt _ fun x ↦ ?_
  obtain ⟨ψ, J₀, hx, hψ⟩ := hint (f x)
  have hfd (y : N) : MDifferentiableAt I' I f y := f.contMDiff.mdifferentiable hn y
  -- The differential `A = dψ ∘ df` of `ψ ∘ f` at `x` is injective and complex linear from the
  -- restricted structure `K` at `x` to `J₀`, so it has a complex linear left inverse `G`.
  let K : AlmostComplexStructure E' := (J.restrict f hJ).almostComplexStructureAt x
  have hψc : IsComplexLinearMap (J.almostComplexStructureAt (f x)) J₀
      (mfderiv I 𝓘(ℝ, E) ψ (f x)).toLinearMap :=
    (isComplexLinearMap_iff_apply _ _ _).2 fun v ↦
      (congrArg (mfderiv I 𝓘(ℝ, E) ψ (f x)) (almostComplexStructureAt_apply J (f x) v)).trans
        (hψ _ hx v)
  have hA : IsComplexLinearMap K J₀
      ((mfderiv I 𝓘(ℝ, E) ψ (f x)).toLinearMap ∘ₗ (mfderiv I' I f x).toLinearMap) :=
    hψc.comp (isComplexLinearMap_mfderiv hJ x)
  have hAinj : Injective
      ((mfderiv I 𝓘(ℝ, E) ψ (f x)).toLinearMap ∘ₗ (mfderiv I' I f x).toLinearMap) :=
    (ψ.isInvertible_mfderiv hn hx).injective.comp (f.isImmersion.mfderiv_injective (by simp) x)
  obtain ⟨G, hGJ, hGA⟩ := hA.exists_leftInverse_of_injective hAinj
  let Gc : E →L[ℝ] E' := LinearMap.toContinuousLinearMap G
  -- The map `φ = G ∘ ψ ∘ f` is smooth on the open set `s = f⁻¹(ψ.source)`.
  let φ : N → E' := Gc ∘ ψ ∘ f
  let s : Set N := f ⁻¹' ψ.source
  have hs : IsOpen s := ψ.open_source.preimage f.contMDiff.continuous
  have hxs : x ∈ s := hx
  have hφ : ContMDiffOn I' 𝓘(ℝ, E') ∞ φ s :=
    Gc.contMDiff.comp_contMDiffOn (ψ.contMDiffOn.comp f.contMDiff.contMDiffOn fun _ h ↦ h)
  have hdφ (y : N) (hy : y ∈ s) (v : TangentSpace I' y) :
      mfderiv I' 𝓘(ℝ, E') φ y v = G (mfderiv I 𝓘(ℝ, E) ψ (f y) (mfderiv I' I f y v)) := by
    have hψy : MDifferentiableAt I 𝓘(ℝ, E) ψ (f y) := ψ.mdifferentiableAt hn hy
    rw [mfderiv_comp_apply y Gc.mdifferentiableAt (hψy.comp y (hfd y)),
      mfderiv_comp_apply y hψy (hfd y), Gc.mfderiv_eq]
    exact congrFun (LinearMap.coe_toContinuousLinearMap' G) _
  -- Its differential at `x` is `G ∘ A = id`, so by the inverse function theorem it is a local
  -- diffeomorphism at `x`; on `s` its differential carries the restricted structure to `K`.
  refine ⟨φ, s, K, hs.mem_nhds hxs, ?_, fun y hy v ↦ ?_⟩
  · refine isLocalDiffeomorphAt_of_mfderiv_eq hφ hs hxs BoundarylessManifold.isInteriorPoint
      (by simp) (e := ContinuousLinearEquiv.refl ℝ E') ?_
    ext v
    rw [hdφ x hxs v]
    exact (LinearMap.congr_fun hGA v).symm
  · rw [hdφ y hy, mfderiv_restrict_apply, hψ _ hy, hdφ y hy]
    exact (isComplexLinearMap_iff_apply _ _ _).1 hGJ _

section Nijenhuis

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']

/-- The differential of the embedding carries the Nijenhuis tensor of the restricted structure to
the Nijenhuis tensor of `J`: `df_x (N_{J|_N}(v, w)) = N_J(df_x v, df_x w)`. -/
theorem mfderiv_nijenhuis_restrict (x : N) (v w : TangentSpace I' x) :
    mfderiv I' I f x ((J.restrict f hJ).nijenhuis x v w) =
      J.nijenhuis (f x) (mfderiv I' I f x v) (mfderiv I' I f x w) := by
  have hf := f.isImmersion.isImmersionAt x
  obtain ⟨X, V, hX, hV, hXv, hXV⟩ := hf.exists_vectorField_mfderiv_eventuallyEq (m := 1)
    (by simp) v
  obtain ⟨Y, W, hY, hW, hYw, hYW⟩ := hf.exists_vectorField_mfderiv_eventuallyEq (m := 1)
    (by simp) w
  have h := (J.restrict f hJ).mfderiv_nijenhuis_of_eventually_related J
    ((f.contMDiff x).of_le (by simp))
    (.of_forall fun z u ↦ mfderiv_restrict_apply hJ z u) (hX.mdifferentiableAt one_ne_zero)
    (hY.mdifferentiableAt one_ne_zero) (hV.mdifferentiableAt one_ne_zero)
    (hW.mdifferentiableAt one_ne_zero) hXV hYW
  rwa [← hXV.self_of_nhds, ← hYW.self_of_nhds, hXv, hYw] at h

/-- The Nijenhuis tensor of the restricted structure at `x` is
`N_{J|_N}(v, w) = L (N_J(df_x v, df_x w))` for every left inverse `L` of `df_x`. -/
theorem nijenhuis_restrict_apply {x : N} {L : TangentSpace I (f x) →L[ℝ] TangentSpace I' x}
    (hL : LeftInverse L (mfderiv I' I f x)) (v w : TangentSpace I' x) :
    (J.restrict f hJ).nijenhuis x v w =
      L (J.nijenhuis (f x) (mfderiv I' I f x v) (mfderiv I' I f x w)) := by
  rw [← mfderiv_nijenhuis_restrict hJ, hL]

/-- If the Nijenhuis tensor of `J` vanishes, so does that of the restricted structure. -/
theorem nijenhuis_restrict_eq_zero (h : J.nijenhuis = 0) : (J.restrict f hJ).nijenhuis = 0 := by
  funext x
  ext v w
  refine f.isImmersion.mfderiv_injective (by simp) x ?_
  simp [mfderiv_nijenhuis_restrict hJ, h]

end Nijenhuis

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

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']

/-- A Kähler pair `(σ, J)` restricts to a Kähler pair on a complex submanifold: the pull-back of
`σ` and the restricted structure. -/
theorem IsKahler.restrict (hσ : σ.IsKahler J) :
    SmoothTwoForm.IsKahler (SmoothForm.mpullback f f.contMDiff σ) (J.restrict f hJ) :=
  ⟨hσ.isClosed.mpullback f f.contMDiff, hσ.compatible.restrict hJ,
    SmoothAlmostComplexStructure.nijenhuis_restrict_eq_zero hJ hσ.nijenhuis_eq_zero⟩

/-- **Complex submanifolds of tame and Kähler manifolds.** Let `σ` be a two-form on `M` taming a
smooth almost complex structure `J` (so `σ` is nondegenerate), and let `f : N → M` be a smooth
embedding whose tangent images are `J`-invariant, with restricted structure `J|_N`. Then

1. the pull-back `f^* σ` is nondegenerate, and it tames `J|_N`;
2. if `σ` is compatible with `J`, then `f^* σ` is compatible with `J|_N`;
3. if `σ` is closed, then `f` is a symplectic submanifold embedding for `σ`, and `f^* σ` is
   symplectic;
4. if `(σ, J)` is Kähler (closed, compatible, with vanishing Nijenhuis tensor), then so is
   `(f^* σ, J|_N)`.

Milestone: *Complex submanifolds of Kähler manifolds*. -/
theorem Tames.complex_submanifold (hσ : σ.Tames J) :
    SmoothTwoForm.IsNondegenerate (SmoothForm.mpullback f f.contMDiff σ) ∧
      SmoothTwoForm.Tames (SmoothForm.mpullback f f.contMDiff σ) (J.restrict f hJ) ∧
      (σ.Compatible J →
        SmoothTwoForm.Compatible (SmoothForm.mpullback f f.contMDiff σ) (J.restrict f hJ)) ∧
      (σ.IsClosed → hσ.isNondegenerate.IsSymplecticSubmanifoldEmbedding I' f ∧
        SmoothTwoForm.IsSymplectic (SmoothForm.mpullback f f.contMDiff σ)) ∧
      (σ.IsKahler J →
        SmoothTwoForm.IsKahler (SmoothForm.mpullback f f.contMDiff σ) (J.restrict f hJ)) :=
  ⟨(hσ.restrict hJ).isNondegenerate, hσ.restrict hJ, fun h ↦ h.restrict hJ,
    fun h ↦ ⟨hσ.isSymplecticSubmanifoldEmbedding hJ, hσ.isSymplectic_mpullback hJ
      ⟨h, hσ.isNondegenerate⟩⟩, fun h ↦ h.restrict hJ⟩

end SmoothTwoForm

end TauCeti
