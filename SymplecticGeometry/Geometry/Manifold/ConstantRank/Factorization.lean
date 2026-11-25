/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.ConstantRank.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Local factorization of a map of constant rank

A smooth map `f : M → N` of constant rank `r`, from a finite-dimensional boundaryless manifold
to a boundaryless manifold, factors near each point as a submersion `q` onto an open set `U` of
`EuclideanSpace 𝕜 (Fin r)` followed by a map `g` on `U` with injective derivative. In the
coordinates of Tau Ceti's rank theorem
`ContMDiffOn.exists_openPartialHomeomorph_comp_eq_mfderiv_comp` the map is a linear map `A` of
rank `r`; writing `A = j ∘ p` with `p` onto `EuclideanSpace 𝕜 (Fin r)` and `j` injective, `q` is
`p` after the source chart and `g` is the inverse of the target chart after `j`.

## Main results

* `ContMDiff.exists_comp_eq_of_mfderivRank_eq`: the local factorization.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Theorem 4.12 (the rank theorem).
-/

public section

open Set Function Module Manifold
open scoped ContDiff

variable {𝕜 E F H G M N : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  {J : ModelWithCorners 𝕜 F G} [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω} [IsManifold I n M] [IsManifold J n N]

/-- **Local factorization of a map of constant rank.** Near each point `x`, a `C^n` map `f` of
constant rank `r`, `1 ≤ n`, is `g ∘ q` on an open set `V ∋ x`, where `q` is `C^n` on `V` with
surjective derivatives and maps `V` onto an open set `U` of `EuclideanSpace 𝕜 (Fin r)`, and `g`
is `C^n` on `U` with injective derivatives. -/
theorem ContMDiff.exists_comp_eq_of_mfderivRank_eq {f : M → N} (hf : ContMDiff I J n f)
    (hn : 1 ≤ n) {r : ℕ} (hr : ∀ y, TauCeti.mfderivRank I J f y = r) (x : M) :
    ∃ (V : Set M) (U : Set (EuclideanSpace 𝕜 (Fin r))) (q : M → EuclideanSpace 𝕜 (Fin r))
      (g : EuclideanSpace 𝕜 (Fin r) → N),
      IsOpen V ∧ x ∈ V ∧ IsOpen U ∧ q '' V = U ∧ (∀ y ∈ V, g (q y) = f y) ∧
      ContMDiffOn I 𝓘(𝕜, EuclideanSpace 𝕜 (Fin r)) n q V ∧
      (∀ y ∈ V, Surjective (mfderiv I 𝓘(𝕜, EuclideanSpace 𝕜 (Fin r)) q y)) ∧
      ContMDiffOn 𝓘(𝕜, EuclideanSpace 𝕜 (Fin r)) J n g U ∧
      ∀ u ∈ U, Injective (mfderiv 𝓘(𝕜, EuclideanSpace 𝕜 (Fin r)) J g u) := by
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  obtain ⟨φ, ψ, hxφ, -, -, hφ, hφi, -, hψ, hψi, hmap, hlin⟩ :=
    hf.contMDiffOn.exists_openPartialHomeomorph_comp_eq_mfderiv_comp isOpen_univ (mem_univ x) hn
      fun y _ ↦ ((hr y).trans (hr x).symm).le
  -- The linear map `A` that `f` is in these coordinates, and its rank.
  set A : E →L[𝕜] F := (tangentSpaceCastModel J (f x)).toContinuousLinearMap ∘L
    mfderiv I J f x ∘L (tangentSpaceCastModel I x).symm.toContinuousLinearMap with hA
  have hrA : finrank 𝕜 (LinearMap.range A.toLinearMap) = r := by
    rw [← hr x, TauCeti.mfderivRank_def, hA, ContinuousLinearMap.toLinearMap_comp,
      ContinuousLinearMap.toLinearMap_comp, LinearMap.range_comp,
      LinearMap.range_comp_of_range_eq_top]
    · exact (Submodule.equivMapOfInjective _
        (tangentSpaceCastModel J (f x)).injective _).finrank_eq.symm
    · exact LinearMap.range_eq_top.2 (tangentSpaceCastModel I x).symm.surjective
  have hlin' (y : M) (hy : y ∈ φ.source) : ψ (f y) = A (φ y) := by
    rw [hlin y hy, hA, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.coe_coe]
  -- Factor `A = j ∘ p`, with `p` onto `EuclideanSpace 𝕜 (Fin r)` and `j` injective.
  let e : LinearMap.range A.toLinearMap ≃ₗ[𝕜] EuclideanSpace 𝕜 (Fin r) :=
    LinearEquiv.ofFinrankEq _ _ (by simp [hrA])
  let p : E →L[𝕜] EuclideanSpace 𝕜 (Fin r) :=
    LinearMap.toContinuousLinearMap (e.toLinearMap ∘ₗ A.toLinearMap.rangeRestrict)
  let j : EuclideanSpace 𝕜 (Fin r) →L[𝕜] F :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.range A.toLinearMap).subtype ∘ₗ e.symm.toLinearMap)
  have hjp (v : E) : j (p v) = A v := by simp [p, j]
  have hp : Surjective p := e.surjective.comp A.toLinearMap.surjective_rangeRestrict
  have hj : Injective j := Subtype.val_injective.comp e.symm.injective
  -- `φ` and the inverse of `ψ` are partial diffeomorphisms.
  let Φ : PartialDiffeomorph I 𝓘(𝕜, E) M E n :=
    { toPartialEquiv := φ.toPartialEquiv, open_source := φ.open_source,
      open_target := φ.open_target, contMDiffOn_toFun := hφ, contMDiffOn_invFun := hφi }
  let Ψ : PartialDiffeomorph 𝓘(𝕜, F) J F N n :=
    { toPartialEquiv := ψ.symm.toPartialEquiv, open_source := ψ.open_target,
      open_target := ψ.open_source, contMDiffOn_toFun := hψi,
      contMDiffOn_invFun := hψ }
  have hmapsTo : MapsTo j (p '' φ.target) ψ.target := by
    rintro _ ⟨v, hv, rfl⟩
    rw [hjp, ← φ.right_inv hv, ← hlin' _ (φ.map_target hv)]
    exact ψ.map_source (hmap (φ.map_target hv))
  refine ⟨φ.source, p '' φ.target, p ∘ φ, ψ.symm ∘ j, φ.open_source, hxφ,
    p.toLinearMap.isOpenMap_of_finiteDimensional hp _ φ.open_target, ?_, fun y hy ↦ ?_,
    p.contMDiff.comp_contMDiffOn hφ, fun y hy ↦ ?_, hψi.comp j.contMDiff.contMDiffOn hmapsTo,
    fun u hu ↦ ?_⟩
  · rw [image_comp, φ.image_source_eq_target]
  · rw [comp_apply, comp_apply, hjp, ← hlin' y hy, ψ.left_inv (hmap hy)]
  · have hloc : IsLocalDiffeomorphAt I 𝓘(𝕜, E) n φ y :=
      PartialDiffeomorph.isLocalDiffeomorphAt I 𝓘(𝕜, E) n Φ hy
    obtain ⟨L, hL⟩ := hloc.isInvertible_mfderiv hn0
    rw [mfderiv_comp y p.mdifferentiableAt (hloc.mdifferentiableAt hn0), p.mfderiv_eq, ← hL]
    exact hp.comp L.surjective
  · have hloc : IsLocalDiffeomorphAt 𝓘(𝕜, F) J n ψ.symm (j u) :=
      PartialDiffeomorph.isLocalDiffeomorphAt 𝓘(𝕜, F) J n Ψ (hmapsTo hu)
    obtain ⟨L, hL⟩ := hloc.isInvertible_mfderiv hn0
    rw [mfderiv_comp u (hloc.mdifferentiableAt hn0) j.mdifferentiableAt, j.mfderiv_eq, ← hL]
    exact L.injective.comp hj
