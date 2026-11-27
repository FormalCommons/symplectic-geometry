/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Geometry.Manifold.RegularValue.Rank
import SymplecticGeometry.Geometry.Manifold.ConstantRank.Basic
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Local factorization of a map of locally maximal rank

Let `f : M → N` be a `C^n` map, `1 ≤ n`, from a finite-dimensional boundaryless manifold to a
boundaryless manifold, on an open set `s ∋ x` where its rank is at most its rank `r` at `x`; for
instance, a map of constant rank `r`. Near `x`, `f` factors as a submersion `q` onto an open set
`U` of `EuclideanSpace 𝕜 (Fin r)` followed by a map `g` on `U` with injective derivative. In the
coordinates of the rank theorem `ContMDiffOn.exists_partialDiffeomorph_comp_eq_mfderivModel_comp`
the map is the linear map `A = mfderivModel I J f x` of rank `r`; writing `A = j ∘ p` with `p`
onto `EuclideanSpace 𝕜 (Fin r)` and `j` injective, `q` is `p` after the source chart and `g` is
the inverse of the target chart after `j`.

## Main results

* `ContMDiffOn.exists_comp_eq_of_mfderivRank_le`: the local factorization.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Theorem 4.12 (the rank theorem).
-/

public section

open Set Function Module Manifold SymplecticGeometry
open scoped ContDiff

variable {𝕜 E F H G M N : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  {J : ModelWithCorners 𝕜 F G} [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω} [IsManifold I n M] [IsManifold J n N]

/-- **Local factorization of a map of locally maximal rank.** Let `f` be `C^n`, `1 ≤ n`, on an
open set `s ∋ x`, with rank on `s` at most its rank `r` at `x`. Then on an open set `V` with
`x ∈ V ⊆ s`, `f` is `g ∘ q`, where `q` is `C^n` on `V` with surjective derivatives and maps `V`
onto an open set `U` of `EuclideanSpace 𝕜 (Fin r)`, and `g` is `C^n` on `U` with injective
derivatives. -/
theorem ContMDiffOn.exists_comp_eq_of_mfderivRank_le {f : M → N} {s : Set M} {x : M}
    (hf : ContMDiffOn I J n f s) (hs : IsOpen s) (hx : x ∈ s) (hn : 1 ≤ n)
    (hr : ∀ y ∈ s, TauCeti.mfderivRank I J f y ≤ TauCeti.mfderivRank I J f x) :
    ∃ (V : Set M) (U : Set (EuclideanSpace 𝕜 (Fin (TauCeti.mfderivRank I J f x))))
      (q : M → EuclideanSpace 𝕜 (Fin (TauCeti.mfderivRank I J f x)))
      (g : EuclideanSpace 𝕜 (Fin (TauCeti.mfderivRank I J f x)) → N),
      IsOpen V ∧ x ∈ V ∧ V ⊆ s ∧ IsOpen U ∧ q '' V = U ∧ (∀ y ∈ V, g (q y) = f y) ∧
      ContMDiffOn I 𝓘(𝕜, EuclideanSpace 𝕜 (Fin (TauCeti.mfderivRank I J f x))) n q V ∧
      (∀ y ∈ V, Surjective
        (mfderiv I 𝓘(𝕜, EuclideanSpace 𝕜 (Fin (TauCeti.mfderivRank I J f x))) q y)) ∧
      ContMDiffOn 𝓘(𝕜, EuclideanSpace 𝕜 (Fin (TauCeti.mfderivRank I J f x))) J n g U ∧
      ∀ u ∈ U, Injective
        (mfderiv 𝓘(𝕜, EuclideanSpace 𝕜 (Fin (TauCeti.mfderivRank I J f x))) J g u) := by
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  set r := TauCeti.mfderivRank I J f x
  obtain ⟨Φ, Ψ, hxΦ, hΦs, -, -, hmap, hlin⟩ :=
    hf.exists_partialDiffeomorph_comp_eq_mfderivModel_comp hs hx hn hr
  -- The linear map `A` that `f` is in these coordinates, and its rank.
  set A : E →L[𝕜] F := mfderivModel I J f x
  have hrA : finrank 𝕜 (LinearMap.range A.toLinearMap) = r := finrank_range_mfderivModel I J f x
  have hlin' (y : M) (hy : y ∈ Φ.source) : Ψ (f y) = A (Φ y) := hlin hy
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
  have hmapsTo : MapsTo j (p '' Φ.target) Ψ.target := by
    rintro _ ⟨v, hv, rfl⟩
    rw [hjp, ← Φ.right_inv hv, ← hlin' _ (Φ.map_target hv)]
    exact Ψ.map_source (hmap (Φ.map_target hv))
  refine ⟨Φ.source, p '' Φ.target, p ∘ Φ, Ψ.symm ∘ j, Φ.open_source, hxΦ, hΦs,
    p.toLinearMap.isOpenMap_of_finiteDimensional hp _ Φ.open_target, ?_, fun y hy ↦ ?_,
    p.contMDiff.comp_contMDiffOn Φ.contMDiffOn, fun y hy ↦ ?_,
    Ψ.symm.contMDiffOn.comp j.contMDiff.contMDiffOn hmapsTo, fun u hu ↦ ?_⟩
  · rw [image_comp, Φ.image_source_eq_target]
  · simp [hjp, ← hlin' y hy, hmap hy]
  · have hloc : IsLocalDiffeomorphAt I 𝓘(𝕜, E) n Φ y :=
      Φ.isLocalDiffeomorphAt I 𝓘(𝕜, E) n hy
    obtain ⟨L, hL⟩ := hloc.isInvertible_mfderiv hn0
    rw [mfderiv_comp y p.mdifferentiableAt (hloc.mdifferentiableAt hn0), p.mfderiv_eq, ← hL]
    exact hp.comp L.surjective
  · have hloc : IsLocalDiffeomorphAt 𝓘(𝕜, F) J n Ψ.symm (j u) :=
      Ψ.symm.isLocalDiffeomorphAt 𝓘(𝕜, F) J n (hmapsTo hu)
    obtain ⟨L, hL⟩ := hloc.isInvertible_mfderiv hn0
    rw [mfderiv_comp u (hloc.mdifferentiableAt hn0) j.mdifferentiableAt, j.mfderiv_eq, ← hL]
    exact L.injective.comp hj
