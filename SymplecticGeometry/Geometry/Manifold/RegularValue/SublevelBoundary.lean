/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.RegularValue.Scalar.Boundary
public import TauCeti.Geometry.Manifold.Boundary.Charts
import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.Comp
import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.Lift
import TauCeti.Geometry.Manifold.RegularValue.Level
import TauCeti.Geometry.Manifold.SmoothEmbedding.Diffeomorph

/-!
# Maps into the boundary of a regular sublevel

Let `f : M → ℝ` be a `C^m` function, `1 ≤ m`, on a boundaryless manifold modelled on a real space
`E` of dimension `n + 1`, and let `a` be a regular value of `f`. For Tau Ceti's atlas
`TauCeti.scalarRegularSublevelChartedSpace`, the sublevel `{x | f x ≤ a}` is a manifold with
boundary, and its boundary `(𝓡∂ (n + 1)).boundary {x | f x ≤ a}`, the level `f⁻¹(a)` as a set
(`TauCeti.boundary_scalarRegularSublevel`), is a manifold modelled on
`EuclideanSpace ℝ (Fin n)`.

This file shows that the inclusion `ι` of this boundary into `M`, the composite of the inclusions
of the boundary into the sublevel and of the sublevel into `M`, is a `C^m` smooth embedding
(`TauCeti.isSmoothEmbedding_coe_boundary_scalarRegularSublevel`). Tau Ceti identifies the
boundary with the regular level `{x // f x = a}` by a diffeomorphism which is the identity on
points (`TauCeti.scalarRegularSublevelBoundaryDiffeomorph`), and the inclusion of the regular level
is a smooth embedding (`TauCeti.isSmoothEmbedding_coe_regularLevel`), so `ι` is their composite.

So a map `g'` into the boundary is as regular as the map `ι ∘ g'` into `M`, whose range lies in
`f⁻¹(a)`:

* `TauCeti.contMDiff_iff_comp_coe_boundary_scalarRegularSublevel` and
  `TauCeti.mdifferentiableAt_iff_comp_coe_boundary_scalarRegularSublevel`: `g'` is `C^k`, for
  `k ≤ m`, or differentiable at a point, exactly when `ι ∘ g'` is;
* `TauCeti.mfderiv_comp_coe_boundary_scalarRegularSublevel`: the differential of `ι ∘ g'` is that
  of `g'` followed by those of the two inclusions;
* `TauCeti.isSmoothEmbedding_of_isImmersion_comp_coe_boundary_scalarRegularSublevel`: if the source
  of `g'` is compact and boundaryless, `M` is Hausdorff and `ι ∘ g'` is an injective `C^k`
  immersion, `1 ≤ k ≤ m`, then `g'` is a `C^k` smooth embedding.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Proposition 5.47 (regular sublevel sets are regular domains, with boundary the
  level).
-/

public section

open Function Manifold Module Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {f : M → ℝ} {a : ℝ}
  {n : ℕ} [I.Boundaryless] [FiniteDimensional ℝ E] {m : ℕ∞ω} [IsManifold I m M]
  (hreg : IsRegularValue I 𝓘(ℝ) f a) (hn : finrank ℝ E = n + 1) (hm : 1 ≤ m)
  (hfm : ContMDiff I 𝓘(ℝ) m f)
  {EN HN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  {J : ModelWithCorners ℝ EN HN} [TopologicalSpace N] [ChartedSpace HN N]

/-- **The boundary of a regular sublevel is embedded in the manifold.** Let `a` be a regular value
of a `C^m` function `f : M → ℝ`, `1 ≤ m`. The inclusion into `M` of the boundary of the sublevel
`{x | f x ≤ a}`, for the boundary atlas of the preferred atlas of the sublevel, is a `C^m` smooth
embedding. -/
theorem isSmoothEmbedding_coe_boundary_scalarRegularSublevel :
    letI := scalarRegularSublevelChartedSpace (hfm.of_le hm) hreg hn
    IsSmoothEmbedding 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I m
      (fun q : (𝓡∂ (n + 1)).boundary {x | f x ≤ a} ↦ ((q : {x | f x ≤ a}) : M)) := by
  have : IsManifold I 1 M := .of_le hm
  let := scalarRegularSublevelChartedSpace (hfm.of_le hm) hreg hn
  have := isManifold_scalarRegularSublevel hreg hn hm hfm
  have := isManifold_boundary (n := n) (k := m) {x | f x ≤ a}
  let := regularLevelChartedSpace (fun _ _ ↦ (hfm.of_le hm).contMDiffAt) hreg
    (finrank_sub_finrank_real_eq hn)
  have := isManifold_regularLevel hm (fun x _ ↦ hfm x) hreg (finrank_sub_finrank_real_eq hn)
  have hΦ := (scalarRegularSublevelBoundaryDiffeomorph (hfm.of_le hm) hreg hn
    m).isSmoothEmbedding_comp hm IsSmoothEmbedding.id
  have hι := (isSmoothEmbedding_coe_regularLevel hm (fun x _ ↦ hfm x) hreg
    (finrank_sub_finrank_real_eq hn)).comp_of_boundaryless hΦ hm
  convert hι using 1
  funext q
  simp

/-- A map into the boundary of a regular sublevel of a `C^m` function is `C^k`, for `k ≤ m`, if
and only if its composite with the inclusion of the boundary into `M` is. -/
theorem contMDiff_iff_comp_coe_boundary_scalarRegularSublevel {k : ℕ∞ω} (hkm : k ≤ m)
    {g : N → letI := scalarRegularSublevelChartedSpace (hfm.of_le hm) hreg hn
      (𝓡∂ (n + 1)).boundary {x | f x ≤ a}} :
    letI := scalarRegularSublevelChartedSpace (hfm.of_le hm) hreg hn
    ContMDiff J 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) k g ↔
      ContMDiff J I k (fun y ↦ ((g y : {x | f x ≤ a}) : M)) :=
  ((isSmoothEmbedding_coe_boundary_scalarRegularSublevel hreg hn hm hfm).of_le
    hkm).contMDiff_iff_comp

/-- A map into the boundary of a regular sublevel of a `C^m` function, `1 ≤ m`, is differentiable
at a point if and only if its composite with the inclusion of the boundary into `M` is. -/
theorem mdifferentiableAt_iff_comp_coe_boundary_scalarRegularSublevel
    {g : N → letI := scalarRegularSublevelChartedSpace (hfm.of_le hm) hreg hn
      (𝓡∂ (n + 1)).boundary {x | f x ≤ a}} {y : N} :
    letI := scalarRegularSublevelChartedSpace (hfm.of_le hm) hreg hn
    MDifferentiableAt J 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) g y ↔
      MDifferentiableAt J I (fun y ↦ ((g y : {x | f x ≤ a}) : M)) y :=
  (isSmoothEmbedding_coe_boundary_scalarRegularSublevel hreg hn hm hfm).mdifferentiableAt_iff_comp
    (by rintro rfl; simp at hm)

/-- **The differential of a map into the boundary of a regular sublevel.** Let `a` be a regular
value of a `C^m` function `f : M → ℝ`, `1 ≤ m`, and `g` a map into the boundary of the sublevel
`{x | f x ≤ a}` which is differentiable at `y`. The differential at `y` of the composite of `g`
with the inclusion of the boundary into `M` is the differential of `g`, followed by those of the
inclusion of the boundary into the sublevel and of the inclusion of the sublevel into `M`. -/
theorem mfderiv_comp_coe_boundary_scalarRegularSublevel
    {g : N → letI := scalarRegularSublevelChartedSpace (hfm.of_le hm) hreg hn
      (𝓡∂ (n + 1)).boundary {x | f x ≤ a}} {y : N}
    (hg : letI := scalarRegularSublevelChartedSpace (hfm.of_le hm) hreg hn
      MDifferentiableAt J 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) g y) :
    letI := scalarRegularSublevelChartedSpace (hfm.of_le hm) hreg hn
    mfderiv J I (fun y ↦ ((g y : {x | f x ≤ a}) : M)) y =
      (mfderiv (𝓡∂ (n + 1)) I (Subtype.val : {x | f x ≤ a} → M) (g y)).comp
        ((mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
          (Subtype.val : (𝓡∂ (n + 1)).boundary {x | f x ≤ a} → {x | f x ≤ a}) (g y)).comp
          (mfderiv J 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) g y)) := by
  let := scalarRegularSublevelChartedSpace (hfm.of_le hm) hreg hn
  have := isManifold_scalarRegularSublevel hreg hn hm hfm
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have hval := ((isSmoothEmbedding_subtypeVal_boundary (n := n) (k := m)
    {x | f x ≤ a}).contMDiff (g y)).mdifferentiableAt hm0
  have hval' := (contMDiff_subtypeVal_scalarRegularSublevel hreg hn hm hfm
    (g y : {x | f x ≤ a})).mdifferentiableAt hm0
  rw [← mfderiv_comp y hval hg]
  exact mfderiv_comp y hval' (hval.comp y hg)

/-- **Compact injective immersions into the boundary of a regular sublevel are embeddings.** Let
`a` be a regular value of a `C^m` function `f : M → ℝ` on a Hausdorff manifold, and `1 ≤ k ≤ m`.
A map `g` from a compact boundaryless manifold into the boundary of the sublevel `{x | f x ≤ a}`,
whose composite with the inclusion of the boundary into `M` is an injective `C^k` immersion, is a
`C^k` smooth embedding. -/
theorem isSmoothEmbedding_of_isImmersion_comp_coe_boundary_scalarRegularSublevel [T2Space M]
    [J.Boundaryless] [CompactSpace N] {k : ℕ∞ω} [IsManifold J k N] (hk : 1 ≤ k) (hkm : k ≤ m)
    {g : N → letI := scalarRegularSublevelChartedSpace (hfm.of_le hm) hreg hn
      (𝓡∂ (n + 1)).boundary {x | f x ≤ a}}
    (himm : IsImmersion J I k (fun y ↦ ((g y : {x | f x ≤ a}) : M)))
    (hinj : Injective (fun y ↦ ((g y : {x | f x ≤ a}) : M))) :
    letI := scalarRegularSublevelChartedSpace (hfm.of_le hm) hreg hn
    IsSmoothEmbedding J 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) k g := by
  let := scalarRegularSublevelChartedSpace (hfm.of_le hm) hreg hn
  have := (isManifold_scalarRegularSublevel hreg hn hm hfm).of_le hkm
  have := isManifold_boundary (n := n) (k := k) {x | f x ≤ a}
  exact ((isSmoothEmbedding_coe_boundary_scalarRegularSublevel hreg hn hm hfm).of_le hkm).of_comp
    hk ⟨himm, (himm.contMDiff.continuous.isClosedEmbedding hinj).isEmbedding⟩

end TauCeti

end
