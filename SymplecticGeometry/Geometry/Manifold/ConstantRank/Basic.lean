/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.ConstantRank.Basic
import TauCeti.LinearAlgebra.Dimension.Submodule

/-!
# The rank theorem with partial diffeomorphisms as coordinates

The derivative `mfderiv I J f x : TangentSpace I x →L[𝕜] TangentSpace J (f x)` of a map between
manifolds modelled on `E` and `F`, read through the identifications `tangentSpaceCastModel` of
the tangent spaces with the model spaces, is a continuous linear map `E →L[𝕜] F`,
`SymplecticGeometry.mfderivModel I J f x`. Its range has dimension the rank
`TauCeti.mfderivRank I J f x`, and its kernel is the image of the kernel of the derivative.

Tau Ceti's rank theorem `ContMDiffOn.exists_openPartialHomeomorph_comp_eq_mfderiv_comp` gives,
near a point `x` of an open set on which the rank of `f` is at most its rank at `x`, open partial
homeomorphisms `φ` of `M` and `ψ` of `N`, smooth with smooth inverses, in which `f` reads as this
linear map. Here the same statement is given with `φ` and `ψ` as partial diffeomorphisms, so that
the lemmas about `PartialDiffeomorph` apply to them directly.

## Main definitions

* `SymplecticGeometry.mfderivModel`: the derivative of `f` at `x`, as a map between the model
  spaces.

## Main results

* `SymplecticGeometry.finrank_range_mfderivModel`: its range has dimension the rank of `f` at `x`.
* `SymplecticGeometry.ker_mfderivModel`: its kernel is that of `mfderiv I J f x`.
* `ContMDiffOn.exists_partialDiffeomorph_comp_eq_mfderivModel_comp`: the rank theorem, with
  partial diffeomorphisms as coordinates.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Theorem 4.12 (the rank theorem).
-/

public section

noncomputable section

open Set Function Module Manifold
open scoped ContDiff

namespace SymplecticGeometry

section Model

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E F H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace H] [TopologicalSpace G]
  (I : ModelWithCorners 𝕜 E H) (J : ModelWithCorners 𝕜 F G)
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N]

/-- The derivative of `f : M → N` at `x`, as a continuous linear map between the model spaces
`E` and `F`: `mfderiv I J f x` composed with the identifications `tangentSpaceCastModel` of the
tangent spaces at `x` and `f x` with `E` and `F`. -/
def mfderivModel (f : M → N) (x : M) : E →L[𝕜] F :=
  (tangentSpaceCastModel J (f x)).toContinuousLinearMap ∘L mfderiv I J f x ∘L
    (tangentSpaceCastModel I x).symm.toContinuousLinearMap

theorem mfderivModel_def (f : M → N) (x : M) :
    mfderivModel I J f x = (tangentSpaceCastModel J (f x)).toContinuousLinearMap ∘L
      mfderiv I J f x ∘L (tangentSpaceCastModel I x).symm.toContinuousLinearMap :=
  (rfl)

@[simp]
theorem mfderivModel_apply (f : M → N) (x : M) (v : E) :
    mfderivModel I J f x v =
      tangentSpaceCastModel J (f x) (mfderiv I J f x ((tangentSpaceCastModel I x).symm v)) := by
  simp [mfderivModel_def]

/-- The range of `mfderivModel I J f x` has dimension the rank of `f` at `x`. -/
@[simp]
theorem finrank_range_mfderivModel (f : M → N) (x : M) :
    finrank 𝕜 (LinearMap.range (mfderivModel I J f x).toLinearMap) =
      TauCeti.mfderivRank I J f x := by
  rw [TauCeti.mfderivRank_def, mfderivModel_def, ContinuousLinearMap.toLinearMap_comp,
    ContinuousLinearMap.toLinearMap_comp]
  exact LinearMap.finrank_range_comp_comp _ (mfderiv I J f x).toLinearMap _
    (tangentSpaceCastModel J (f x)).injective (tangentSpaceCastModel I x).symm.surjective

/-- The kernel of `mfderivModel I J f x` is the kernel of `mfderiv I J f x`, carried to `E` by
`tangentSpaceCastModel`. -/
theorem ker_mfderivModel (f : M → N) (x : M) :
    LinearMap.ker (mfderivModel I J f x).toLinearMap = (mfderiv I J f x).ker.map
      ((tangentSpaceCastModel I x).toLinearEquiv : TangentSpace I x →ₗ[𝕜] E) := by
  ext v
  simp [Submodule.mem_map_equiv]

end Model

end SymplecticGeometry

open SymplecticGeometry

variable {𝕜 E F H G M N : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  {J : ModelWithCorners 𝕜 F G} [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω} [IsManifold I n M] [IsManifold J n N]
  {f : M → N} {U : Set M} {x : M}

/-- **The rank theorem, with partial diffeomorphisms as coordinates.** Let `f` be `C^n`,
`1 ≤ n`, on an open set `U ∋ x`, with rank on `U` at most its rank at `x`. Then there are
`C^n` partial diffeomorphisms `Φ` from `M` to `E` and `Ψ` from `N` to `F`, with `x` in the source
of `Φ`, that source inside `U` and mapped by `f` into the source of `Ψ`, sending `x` and `f x`
to `0`, in which `f` is the linear map `mfderivModel I J f x`: `Ψ ∘ f = mfderivModel I J f x ∘ Φ`
on the source of `Φ`. -/
theorem ContMDiffOn.exists_partialDiffeomorph_comp_eq_mfderivModel_comp
    (hf : ContMDiffOn I J n f U) (hU : IsOpen U) (hx : x ∈ U) (hn : 1 ≤ n)
    (hrank : ∀ y ∈ U, TauCeti.mfderivRank I J f y ≤ TauCeti.mfderivRank I J f x) :
    ∃ (Φ : PartialDiffeomorph I 𝓘(𝕜, E) M E n) (Ψ : PartialDiffeomorph J 𝓘(𝕜, F) N F n),
      x ∈ Φ.source ∧ Φ.source ⊆ U ∧ Φ x = 0 ∧ Ψ (f x) = 0 ∧ MapsTo f Φ.source Ψ.source ∧
      EqOn (Ψ ∘ f) (mfderivModel I J f x ∘ Φ) Φ.source := by
  obtain ⟨φ, ψ, hxφ, hφU, hφx, hφ, hφi, hψx, hψ, hψi, hmap, hlin⟩ :=
    hf.exists_openPartialHomeomorph_comp_eq_mfderiv_comp hU hx hn hrank
  refine ⟨{ φ with contMDiffOn_toFun := hφ, contMDiffOn_invFun := hφi },
    { ψ with contMDiffOn_toFun := hψ, contMDiffOn_invFun := hψi }, hxφ, hφU, hφx, hψx, hmap,
    fun y hy ↦ ?_⟩
  rw [comp_apply, comp_apply, mfderivModel_apply]
  exact hlin y hy
