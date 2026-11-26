/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.Basic
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.DefiningFunctions

/-!
# The normal trivialization of a global regular level

Let `f : M → N` be an embedding and `g : N → P` a single map that is a defining function of `f`
near every point: it is `C^n` at the image of every point, constant on the image of `f` near every
point, and its differential is onto there. At each `x`, Tau Ceti's
`TauCeti.SmoothEmbedding.normalSpaceEquivOfLevel` identifies the normal space of `f` at `x` with
`P` by the differential of `g`. This file shows that the inverses of these identifications form a
`C^m` trivialization of the normal bundle, `m + 1 ≤ n`: the map `(x, z) ↦ (x, dg_x⁻¹ z)` from
`M × P` to the normal bundle is `C^m`.

The proof goes through Tau Ceti's transition-cocycle model of the normal bundle. The atlas
`TauCeti.SmoothEmbedding.DefiningFunctions.ofLevel` uses `g` at every point, with all of `M` as
base set, so its transitions are the identity (`DefiningFunctions.ofLevel_coordChange`), the
model is the product bundle `M × P`, and
`TauCeti.SmoothEmbedding.DefiningFunctions.normalBundleDiffeomorph` carries it to the normal bundle.

## Main definitions and results

* `TauCeti.SmoothEmbedding.DefiningFunctions.ofLevel`: the atlas of defining functions given by a
  single map.
* `TauCeti.SmoothEmbedding.DefiningFunctions.ofLevel_normalEquiv`: its normal identifications are
  those of `normalSpaceEquivOfLevel`.
* `TauCeti.SmoothEmbedding.contMDiff_normalSpaceEquivOfLevel_symm`: the inverse identifications
  form a `C^m` map `M × P → ν f`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 5 (local defining
  functions).
-/

public section

open Bundle Filter Topology Module
open scoped Manifold ContDiff

namespace TauCeti.SmoothEmbedding

variable {𝕜 E V P H G M N : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedAddCommGroup P] [NormedSpace 𝕜 P]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 V G}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N]
  {n m : ℕ∞ω} {f : SmoothEmbedding I J n M N} {g : N → P}

namespace DefiningFunctions

/-- The atlas of defining functions of an embedding `f` given by a single map `g` that is `C^n`
at the image of every point, constant on the image of `f` near every point, and has onto
differential there: every base set is all of `M`, and the defining function is always `g`. -/
noncomputable def ofLevel (hg : ∀ x, ContMDiffAt J 𝓘(𝕜, P) n g (f x))
    (hgf : ∀ x, ∀ᶠ y in 𝓝 x, g (f y) = g (f x))
    (hreg : ∀ x, IsRegularPoint J 𝓘(𝕜, P) g (f x)) : f.DefiningFunctions P where
  baseSet _ := Set.univ
  isOpen_baseSet _ := isOpen_univ
  mem_baseSet _ := Set.mem_univ _
  toFun _ := g
  contMDiffAt _ y _ := hg y
  eventually_eq _ y _ := hgf y
  isRegularPoint _ y _ := hreg y

variable (hg : ∀ x, ContMDiffAt J 𝓘(𝕜, P) n g (f x))
  (hgf : ∀ x, ∀ᶠ y in 𝓝 x, g (f y) = g (f x))
  (hreg : ∀ x, IsRegularPoint J 𝓘(𝕜, P) g (f x))

/-- Every base set of the atlas given by a single map is all of `M`. -/
@[simp]
theorem ofLevel_baseSet (x : M) : (ofLevel hg hgf hreg).baseSet x = Set.univ := (rfl)

/-- The defining function chosen at every point is the given map. -/
@[simp]
theorem ofLevel_apply (x : M) : ofLevel hg hgf hreg x = g := (rfl)

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 V] (hn : n ≠ 0)
  (hdim : finrank 𝕜 E + finrank 𝕜 P = finrank 𝕜 V)

/-- The normal identifications of the atlas given by `g` are those induced by the differential
of `g`. -/
theorem ofLevel_normalEquiv (x : M) {y : M} (hy : y ∈ (ofLevel hg hgf hreg).baseSet x) :
    (ofLevel hg hgf hreg).normalEquiv hn hdim x hy =
      f.normalSpaceEquivOfLevel y hn (hgf y) (hreg y) hdim := by
  ext ν
  obtain ⟨v, rfl⟩ := f.normalClass_surjective y hn ν
  rw [normalEquiv_normalClass, normalSpaceEquivOfLevel_normalClass, ofLevel_apply]

/-- The transitions of the atlas given by a single map are the identity. -/
theorem ofLevel_coordChange (x₀ x₁ y : M) :
    (ofLevel hg hgf hreg).coordChange hn hdim x₀ x₁ y = ContinuousLinearMap.id 𝕜 P := by
  ext w
  obtain ⟨v, rfl⟩ := ((ofLevel hg hgf hreg).normalEquiv hn hdim x₀ (Set.mem_univ y)).surjective w
  refine ((ofLevel hg hgf hreg).coordChange_normalEquiv hn hdim (Set.mem_univ y)
    (Set.mem_univ y) v).trans ?_
  exact DFunLike.congr_fun ((ofLevel_normalEquiv hg hgf hreg hn hdim x₁ _).trans
    (ofLevel_normalEquiv hg hgf hreg hn hdim x₀ _).symm) v

end DefiningFunctions

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 V] [FiniteDimensional 𝕜 P]
  [FiniteDimensional 𝕜 E] [IsManifold I 1 M] [IsManifold J 1 N]
  [IsManifold I (m + 1) M] [IsManifold J (m + 1) N]
  (hg : ∀ x, ContMDiffAt J 𝓘(𝕜, P) n g (f x))
  (hgf : ∀ x, ∀ᶠ y in 𝓝 x, g (f y) = g (f x))
  (hreg : ∀ x, IsRegularPoint J 𝓘(𝕜, P) g (f x)) (hn : n ≠ 0)
  (hdim : finrank 𝕜 E + finrank 𝕜 P = finrank 𝕜 V)

include hg in
/-- **The normal trivialization of a global regular level.** If a single map `g : N → P` is a
`C^n` defining function of the embedding `f` near every point, then the inverses of the
identifications `normalSpaceEquivOfLevel` of the normal spaces of `f` with `P` by the
differential of `g` form a `C^m` map `(x, z) ↦ (x, dg_x⁻¹ z)` from `M × P` to the normal bundle
of `f`, for `m + 1 ≤ n`. -/
theorem contMDiff_normalSpaceEquivOfLevel_symm (hm : m + 1 ≤ n) :
    letI := f.normalSpaceFiberBundle hn (P := P) (Nat.eq_sub_of_add_eq' hdim)
    ContMDiff (I.prod 𝓘(𝕜, P)) (I.prod 𝓘(𝕜, P)) m
      (fun x : M × P ↦ (⟨x.1, (f.normalSpaceEquivOfLevel x.1 hn (hgf x.1) (hreg x.1)
        hdim).symm x.2⟩ : TotalSpace P (fun x ↦ f.NormalSpace x hn))) := by
  let := f.normalSpaceFiberBundle hn (P := P) (Nat.eq_sub_of_add_eq' hdim)
  set φ := DefiningFunctions.ofLevel hg hgf hreg
  -- With identity transitions, `(x, z) ↦ (x, z)` is smooth into the transition-cocycle model.
  have hc : ContMDiff (I.prod 𝓘(𝕜, P)) (I.prod 𝓘(𝕜, P)) m
      (fun x : M × P ↦ TotalSpace.mk' P (E := (φ.core hn hdim).Fiber) x.1 x.2) := by
    intro x
    rw [contMDiffAt_totalSpace_iff]
    refine ⟨contMDiffAt_fst, ?_⟩
    simp only [VectorBundleCore.trivializationAt, VectorBundleCore.localTrivAt,
      VectorBundleCore.localTriv_apply, DefiningFunctions.core_indexAt,
      DefiningFunctions.core_coordChange, φ, DefiningFunctions.ofLevel_coordChange,
      ContinuousLinearMap.id_apply]
    exact contMDiffAt_snd
  refine ((φ.normalBundleDiffeomorph hn hdim hm).symm.contMDiff.comp hc).congr fun x ↦ ?_
  rw [Function.comp_apply, DefiningFunctions.normalBundleDiffeomorph_symm_apply,
    DefiningFunctions.ofLevel_normalEquiv]

end TauCeti.SmoothEmbedding

end
