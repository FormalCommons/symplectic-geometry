/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.JConvex.Hypersurface
public import SymplecticGeometry.Geometry.Manifold.Complex.LeviForm
public import SymplecticGeometry.Geometry.Manifold.Complex.TotallyReal.AdaptedChart
public import SymplecticGeometry.Geometry.Manifold.Immersion.Slice
public import SymplecticGeometry.Geometry.Manifold.Morse.Hessian
public import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.ContMDiff
public import SymplecticGeometry.LinearAlgebra.TotallyReal.Basic
public import TauCeti.Geometry.Contact.Pullback
public import TauCeti.Geometry.Manifold.Complex.TotallyReal.AdaptedChart
public import TauCeti.Geometry.Symplectic.Lagrangian.TotallyReal
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import TauCeti.LinearAlgebra.TotallyReal.Basic

/-!
# Totally real submanifolds and J-convex functions

Let `M` be a complex manifold modelled on `E`, seen as a real manifold, with the complex structure
`J = ofComplexManifold E M`. For a smooth real function `f`, write `λ_f = -df ∘ J` and
`ω_f = dλ_f`, as in `SymplecticGeometry.Geometry.Manifold.Complex.Plurisubharmonic`.

This file proves that isotropic submanifolds of a J-convex level that are tangent to its
complex tangencies are totally real:

* `SymplecticGeometry.isTotallyReal_of_isManifoldStrictlyPlurisubharmonicAt`: if `f` is
  strictly plurisubharmonic at `x`, a subspace of `T_x M` on which `ω_f` vanishes is totally real
  for `J`. At `x`, `ω_f` is a symplectic form tamed by `J` (Tau Ceti's
  `TauCeti.SymplecticForm.ofTames`), so this follows from Tau Ceti's
  `TauCeti.SymplecticForm.IsIsotropic.disjoint_map_of_tames`.
* `SymplecticGeometry.isTotallyReal_range_mfderiv_of_isHorizontalMap`: a smooth map `ι` whose
  tangent vectors `v` satisfy `df(i dι(v)) = 0` has a totally real tangent image wherever `f` is
  strictly plurisubharmonic. Such a map pulls `λ_f` back to zero, hence `ω_f` too, by Tau Ceti's
  `TauCeti.SmoothForm.mpullback_mextDerivₗ_eq_zero_of_isHorizontalMap`.
* `SymplecticGeometry.IsJConvexLevel.isTotallyReal_range_mfderiv`: the case of a smooth map into
  a J-convex level `f ⁻¹' {c}` whose tangent vectors are tangent to the complex tangencies of the
  level.

It also gives a criterion for strict plurisubharmonicity in terms of the real critical Hessian
`Hess f = TauCeti.criticalHessian 𝓘(ℝ, E) f x`, adapted to functions such as squared distances
to a totally real submanifold, whose Hessian degenerates along the submanifold:

* `SymplecticGeometry.isManifoldStrictlyPlurisubharmonicAt_of_criticalHessian_pos`: if
  `Hess f(v, v) > 0` for every `v` outside a real subspace `L` that is totally real for `J`
  (Tau Ceti's `TauCeti.IsTotallyReal`), then `f` is strictly plurisubharmonic at `x`. By Tau
  Ceti's `isManifoldStrictlyPlurisubharmonicAt_iff_criticalHessian`, one has to show
  `Hess f(v, v) + Hess f(i v, i v) > 0` for `v ≠ 0`, which is
  `TauCeti.IsTotallyReal.add_pos_of_forall_notMem_pos` for `J`.
* `SymplecticGeometry.setOfPred_isManifoldStrictlyPlurisubharmonicAt_mem_nhdsSet_range`: for a map
  `ι : S → M` with totally real tangent images, and `f` real `C²` along `ι(S)` with Hessian
  positive at each point `ι s` off the tangent image of `ι` at `s`, the function `f` is strictly
  plurisubharmonic on a neighbourhood of `ι(S)`. This combines the criterion with
  `TauCeti.IsManifoldStrictlyPlurisubharmonicAt.eventually`.

A nonnegative function that vanishes along `ι(S)` has a critical point at each point of `ι(S)`,
where its Hessian does not depend on the chart; the statements here do not need this, since
Tau Ceti's criterion holds at every point for the Hessian in the preferred chart.

Finally it applies the criterion to the squared distance in an adapted chart. For a totally real
embedding `ι : N → M` with `N` modelled on `F`, Tau Ceti's
`TauCeti.IsTotallyRealEmbedding.exists_adaptedChart` gives charts `ψ : M → F × F` that flatten
the image of `ι` onto `F × {0}` (`TauCeti.IsAdaptedChart`). Fix a linear isomorphism
`e : F ≃L[ℝ] W` onto a real inner product space, which amounts to choosing an inner product on
`F`. For such a chart:

* `TauCeti.IsAdaptedChart.norm_sq_snd_eq_zero_iff`: on the source of `ψ`, the function
  `x ↦ ‖e (ψ x).2‖²` vanishes exactly on the image, where it has critical points
  (`TauCeti.IsAdaptedChart.mem_criticalPoints_norm_sq_snd`, from the general
  `TauCeti.mem_criticalPoints_norm_sq_of_eq_zero` for `‖φ‖²` at a zero of `φ`);
* `TauCeti.IsAdaptedChart.criticalHessian_norm_sq_snd_apply`: its critical Hessian at a point of
  the image is `2 ⟪e (dψ u).2, e (dψ w).2⟫`, by the general
  `TauCeti.criticalHessian_norm_sq_continuousLinearMap_comp_apply_of_eq_zero` of
  `SymplecticGeometry.Geometry.Manifold.Morse.Hessian`, for the map `e ∘L snd`;
* `TauCeti.IsAdaptedChart.criticalHessian_norm_sq_snd_pos`: this Hessian is positive off the
  tangent image of `ι`, since `dψ` sends exactly that image into `F × {0}`
  (`TauCeti.IsAdaptedChart.snd_mfderiv_eq_zero_iff`, in
  `SymplecticGeometry.Geometry.Manifold.Complex.TotallyReal.AdaptedChart`);
* `IsTotallyRealEmbedding.setOfPred_isManifoldStrictlyPlurisubharmonicAt_norm_sq_snd_mem_nhdsSet`:
  for a complex manifold, with the adapted chart taken for
  `(ofComplexManifold E M).toContMDiff ℓ`, `ℓ ≥ 2`, the function is strictly plurisubharmonic on a
  neighbourhood of the part of the image in the source of `ψ`;
* `TauCeti.IsTotallyRealEmbedding.exists_isAdaptedChart_norm_sq_snd`: such charts exist near each
  point of the image of a `C³` totally real embedding. Total reality for `ofComplexManifold E M`
  and for its `C^ℓ` version agree, since both have the same pointwise structures
  (`TauCeti.SmoothAlmostComplexStructure.almostComplexStructureAt_toContMDiff`).

Gluing these local functions with a partition of unity gives the global statement:

* `IsTotallyRealEmbedding.exists_contMDiff_isManifoldStrictlyPlurisubharmonicAt_of_isClosed_range`:
  for a `C^k` totally real embedding `ι` with closed image into a Hausdorff σ-compact complex
  manifold, and `2 ≤ ℓ` with `ℓ + 1 ≤ k`, there is a nonnegative `C^ℓ` function `φ` vanishing
  exactly on the image of `ι`, with critical Hessian positive off the tangent images of `ι`, and
  strictly plurisubharmonic on a neighbourhood of the image. It is `∑ᵢ ρᵢ gᵢ` for a partition
  of unity `ρᵢ` subordinate to the sources of adapted charts covering the image and to the
  complement of the image, where `gᵢ` is the squared distance `φᵢ` in a chart and the constant
  `1` on the complement. At a point of the image only the chart terms contribute, and each `φᵢ`
  and its differential vanish there, so the critical Hessian of the sum is `∑ᵢ ρᵢ Hess φᵢ`
  (`SmoothPartitionOfUnity.criticalHessian_finsum_smul_pos`), and the criterion above applies.

Adapted charts force the dimension of `N` to be half that of `M`. Without that, near a compact
part of the image:

* `Manifold.IsSmoothEmbedding.exists_contMDiff_isManifoldStrictlyPlurisubharmonicAt_of_isCompact`:
  for a `C^n` embedding `ι`, `n ≥ 2`, of a boundaryless manifold into a Hausdorff complex
  manifold, and a compact `K` at whose points the tangent images of `ι` are totally real, there
  is a nonnegative `C^n` function `ρ` that, on an open neighbourhood `V` of `ι '' K`, vanishes
  exactly on the image of `ι` and is strictly plurisubharmonic, with critical Hessian positive off
  the tangent images of `ι` at the points of `K`. The proof follows that of the previous theorem,
  with the squared normal coordinates of slice charts of `ι`
  (`Manifold.IsSmoothEmbedding.exists_contMDiffOn_criticalHessian_pos`) in place of adapted
  charts. Finitely many of them suffice, by compactness of `K`, and they are glued by smooth bump
  functions instead of a partition of unity, so that `M` need not be σ-compact; the critical
  Hessian of the sum is then positive by `TauCeti.criticalHessian_sum_mul_pos`.

## References

* [K. Cieliebak, Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Chapter 2, on J-convex functions and hypersurfaces, and on squared distances to totally real
  submanifolds.
-/

public section

noncomputable section

open Set Module Filter Topology
open scoped Manifold ContDiff TauCeti.ComplexManifold

namespace SymplecticGeometry

open TauCeti TauCeti.SmoothAlmostComplexStructure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
  {F H S : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
  {I : ModelWithCorners ℝ F H} [TopologicalSpace S] [ChartedSpace H S]

/-- **Isotropic subspaces at strictly plurisubharmonic points are totally real.** Let `f` be a
smooth real function strictly plurisubharmonic at `x`. A subspace `V` of `T_x M` on each pair of
vectors of which `ω_f = d(-df ∘ J)` vanishes at `x` is totally real for the complex structure `J`
of `M`. -/
theorem isTotallyReal_of_isManifoldStrictlyPlurisubharmonicAt
    {f : C^∞⟮𝓘(ℝ, E), M; ℝ⟯} {x : M} (hf : IsManifoldStrictlyPlurisubharmonicAt E f x)
    {V : Submodule ℝ (TangentSpace 𝓘(ℝ, E) x)}
    (hV : ∀ v ∈ V, ∀ w ∈ V,
      SmoothBundleForm.eval₂ (mextDerivₗ 𝓘(ℝ, E) 1 ((ofComplexManifold E M).covectorComplexStructure
          (mextDerivₗ 𝓘(ℝ, E) 0 (SmoothForm.ofFunction f)))) x v w = 0) :
    IsTotallyReal ((ofComplexManifold E M).toEndomorphism x).toLinearMap V := by
  set σ := mextDerivₗ 𝓘(ℝ, E) 1 ((ofComplexManifold E M).covectorComplexStructure
      (mextDerivₗ 𝓘(ℝ, E) 0 (SmoothForm.ofFunction f)))
  -- At `x`, `ω_f` is positive on `(v, J v)`, so it is a symplectic form tamed by `J`.
  have hpos : ∀ v, v ≠ 0 → 0 < σ.bilinFormAt x v
      ((ofComplexManifold E M).almostComplexStructureAt x v) := fun v hv ↦ by
    have hJ : (ofComplexManifold E M).toEndomorphism x v = Complex.I • (show E from v) :=
      ofComplexManifold_apply (E := E) x _
    rw [SmoothForm.bilinFormAt_apply, SmoothBundleForm.eval₂_apply]
    simp only [almostComplexStructureAt_apply, hJ]
    exact (isManifoldStrictlyPlurisubharmonicAt_iff_forall_pos f x).1 hf v hv
  rw [isTotallyReal_iff, ← almostComplexStructureAt_toLinearMap]
  refine SymplecticForm.IsIsotropic.disjoint_map_of_tames ?_
    (SymplecticForm.tames_ofTames (SmoothForm.isAlt_bilinFormAt σ x) hpos)
  rw [SymplecticForm.isIsotropic_iff]
  intro v hv w hw
  simpa using hV v hv w hw

/-- **Maps tangent to `ker λ_f` have totally real tangent images at strictly plurisubharmonic
points.** Let `ι : S → M` be a smooth map whose tangent vectors stay in the kernel of `df` after
multiplication by `i`: `df(i dι(v)) = 0`, that is, `λ_f(dι(v)) = 0`. If `f` is strictly
plurisubharmonic at `ι s`, then the tangent image `dι_s(T_s S)` is totally real for the complex
structure `J` of `M`. -/
theorem isTotallyReal_range_mfderiv_of_isHorizontalMap [IsManifold I ∞ S]
    {f : C^∞⟮𝓘(ℝ, E), M; ℝ⟯} {ι : S → M} (hι : ContMDiff I 𝓘(ℝ, E) ∞ ι)
    (hξ : ∀ s (v : TangentSpace I s),
      mvfderiv 𝓘(ℝ, E) f (ι s) (Complex.I • (show E from mfderiv I 𝓘(ℝ, E) ι s v)) = 0)
    {s : S} (hf : IsManifoldStrictlyPlurisubharmonicAt E f (ι s)) :
    IsTotallyReal ((ofComplexManifold E M).toEndomorphism (ι s)).toLinearMap
      (LinearMap.range (mfderiv I 𝓘(ℝ, E) ι s).toLinearMap) := by
  -- `ι` pulls `λ_f` back to zero, hence also `ω_f = dλ_f`.
  have hhor : IsHorizontalMap I ((ofComplexManifold E M).covectorComplexStructure
      (mextDerivₗ 𝓘(ℝ, E) 0 (SmoothForm.ofFunction f))).kerDistribution ι := by
    refine isHorizontalMap_iff_range_mfderiv_le.2 fun s' ↦ ?_
    rintro _ ⟨v, rfl⟩
    rw [SmoothForm.mem_kerDistribution, ContinuousLinearMap.coe_coe,
      covectorComplexStructure_ofComplexManifold_mextDerivₗ_apply, hξ, neg_zero]
  have hω := SmoothForm.mpullback_mextDerivₗ_eq_zero_of_isHorizontalMap hι hhor
  refine isTotallyReal_of_isManifoldStrictlyPlurisubharmonicAt hf ?_
  rintro _ ⟨v, rfl⟩ _ ⟨w, rfl⟩
  simp only [ContinuousLinearMap.coe_coe]
  rw [← SmoothForm.eval₂_mpullback ι hι, hω, SmoothBundleForm.eval₂_apply]
  simp

/-- **Isotropic submanifolds of a J-convex level tangent to its complex tangencies are totally
real.** Let `f ⁻¹' {c}` be a J-convex level and `ι : S → M` a smooth map with image in the level
whose tangent vectors stay in the kernel of `df` after multiplication by `i`:
`df(i dι(v)) = 0`. Then each tangent image `dι_s(T_s S)` is totally real for the complex
structure `J` of `M`. -/
theorem IsJConvexLevel.isTotallyReal_range_mfderiv [IsManifold I ∞ S]
    {f : C^∞⟮𝓘(ℝ, E), M; ℝ⟯} {c : ℝ} (hf : IsJConvexLevel E f c) {ι : S → M}
    (hι : ContMDiff I 𝓘(ℝ, E) ∞ ι) (hιc : ∀ s, f (ι s) = c)
    (hξ : ∀ s (v : TangentSpace I s),
      mvfderiv 𝓘(ℝ, E) f (ι s) (Complex.I • (show E from mfderiv I 𝓘(ℝ, E) ι s v)) = 0)
    (s : S) :
    IsTotallyReal ((ofComplexManifold E M).toEndomorphism (ι s)).toLinearMap
      (LinearMap.range (mfderiv I 𝓘(ℝ, E) ι s).toLinearMap) :=
  isTotallyReal_range_mfderiv_of_isHorizontalMap hι hξ
    (hf.isManifoldStrictlyPlurisubharmonicAt _ (hιc s))

section Hessian

variable {f : M → ℝ} {x : M}

/-- **Strict plurisubharmonicity from a Hessian degenerate along a totally real subspace.** Let
`L` be a real subspace of the tangent space at `x` that is totally real for the complex structure
of `M`. If the critical Hessian of `f` at `x` satisfies `Hess f(v, v) > 0` for every `v ∉ L`,
then `f` is strictly plurisubharmonic at `x`. -/
theorem isManifoldStrictlyPlurisubharmonicAt_of_criticalHessian_pos
    {L : Submodule ℝ (TangentSpace 𝓘(ℝ, E) x)}
    (hL : IsTotallyReal ((ofComplexManifold E M).toEndomorphism x).toLinearMap L)
    (hpos : ∀ v ∉ L, 0 < criticalHessian 𝓘(ℝ, E) f x v v) :
    IsManifoldStrictlyPlurisubharmonicAt E f x := by
  rw [isManifoldStrictlyPlurisubharmonicAt_iff_criticalHessian]
  have hJv (v : E) : ((ofComplexManifold E M).toEndomorphism x).toLinearMap v = Complex.I • v :=
    -- `toLinearMap` and `toEndomorphism` only coerce `ofComplexManifold E M x`.
    ofComplexManifold_apply x v
  intro v hv
  have h := hL.add_pos_of_forall_notMem_pos ((ofComplexManifold E M).injective x) hpos hv
  rw [← hJv v]
  exact h

/-- **Strict plurisubharmonicity near a totally real submanifold.** Let `ι : S → M` have totally
real tangent images for the complex structure of `M`, and let `f` be real `C²` at each point
`ι s`, with critical Hessian `Hess f(v, v) > 0` at `ι s` for every `v` outside the tangent image
of `ι` at `s`. Then `f` is strictly plurisubharmonic at every point of a neighbourhood of the
image of `ι`. -/
theorem setOfPred_isManifoldStrictlyPlurisubharmonicAt_mem_nhdsSet_range [FiniteDimensional ℂ E]
    {ι : S → M} (hf : ∀ s, ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 f (ι s))
    (hι : ∀ s,
      IsTotallyReal ((ofComplexManifold E M).toEndomorphism (ι s)).toLinearMap
        (LinearMap.range (mfderiv I 𝓘(ℝ, E) ι s).toLinearMap))
    (hpos : ∀ s, ∀ v ∉ LinearMap.range (mfderiv I 𝓘(ℝ, E) ι s).toLinearMap,
      0 < criticalHessian 𝓘(ℝ, E) f (ι s) v v) :
    {x | IsManifoldStrictlyPlurisubharmonicAt E f x} ∈ 𝓝ˢ (range ι) := by
  rw [mem_nhdsSet_iff_forall]
  rintro _ ⟨s, rfl⟩
  exact ((isManifoldStrictlyPlurisubharmonicAt_of_criticalHessian_pos (hι s) (hpos s)).eventually
    (hf s))

end Hessian

end SymplecticGeometry

/-! ### Squared distance in an adapted chart -/

namespace TauCeti.IsAdaptedChart

variable {E H M F W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {ℓ : ℕ∞} {J : ContMDiffAlmostComplexStructure I ℓ M} {s : Set M}
  {ψ : OpenPartialHomeomorph M (F × F)} {e : F ≃L[ℝ] W}

/-- In a chart adapted to `s`, and for a linear isomorphism `e` from the normal coordinate space
onto an inner product space, the function `x ↦ ‖e (ψ x).2‖²` vanishes on the source exactly at
the points of `s`. -/
theorem norm_sq_snd_eq_zero_iff (hψ : IsAdaptedChart J s ψ) {x : M} (hx : x ∈ ψ.source) :
    ‖e (ψ x).2‖ ^ 2 = 0 ↔ x ∈ s := by
  rw [← hψ.isImage hx]
  simp

/-- In a chart adapted to `s`, the points of `s` in the source are critical points of
`x ↦ ‖e (ψ x).2‖²`, which takes its minimum `0` there. -/
theorem mem_criticalPoints_norm_sq_snd [I.Boundaryless] (hψ : IsAdaptedChart J s ψ) {x : M}
    (hx : x ∈ ψ.source ∩ s) : x ∈ criticalPoints I (fun y ↦ ‖e (ψ y).2‖ ^ 2) :=
  mem_criticalPoints_norm_sq_of_eq_zero (by rw [(hψ.isImage hx.1).2 hx.2, map_zero])
    BoundarylessManifold.isInteriorPoint

/-- For a chart adapted with regularity `ℓ`, the function `y ↦ ‖e (ψ y).2‖²` is `C^ℓ` at each
point of the source. -/
theorem contMDiffAt_norm_sq_snd (hψ : IsAdaptedChart J s ψ) {x : M} (hx : x ∈ ψ.source) :
    ContMDiffAt I 𝓘(ℝ) ℓ (fun y ↦ ‖e (ψ y).2‖ ^ 2) x :=
  (contDiff_norm_sq ℝ).contMDiff.contMDiffAt.comp x
    ((e.contDiff.comp contDiff_snd).contMDiff.contMDiffAt.comp x (hψ.contMDiffAt hx))

/-- **The Hessian of the squared distance in an adapted chart.** At a point `x` of `s` in the
source of a chart `ψ` adapted to `s` with regularity `ℓ ≥ 2`, the critical Hessian of
`y ↦ ‖e (ψ y).2‖²` is `2 ⟪e (dψ u).2, e (dψ w).2⟫`. -/
theorem criticalHessian_norm_sq_snd_apply [I.Boundaryless] (hψ : IsAdaptedChart J s ψ)
    (hℓ : 2 ≤ ℓ) {x : M} (hx : x ∈ ψ.source ∩ s) (u w : TangentSpace I x) :
    criticalHessian I (fun y ↦ ‖e (ψ y).2‖ ^ 2) x u w =
      2 * inner ℝ (e (mfderiv I 𝓘(ℝ, F × F) ψ x u).2) (e (mfderiv I 𝓘(ℝ, F × F) ψ x w).2) := by
  have := criticalHessian_norm_sq_continuousLinearMap_comp_apply_of_eq_zero
    (A := (e : F →L[ℝ] W).comp (ContinuousLinearMap.snd ℝ F F))
    ((hψ.contMDiffAt hx.1).of_le (WithTop.coe_le_coe.2 hℓ))
    (by
      simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_snd']
      rw [(hψ.isImage hx.1).2 hx.2, map_zero]) u w
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearMap.coe_snd'] at this
  exact this

section Embedding

variable {H' N : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ F H'} [TopologicalSpace N]
  [ChartedSpace H' N] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] {k : ℕ∞ω}
  {A : ∀ y : M, AlmostComplexStructure (TangentSpace I y)} {ι : N → M}

/-- **Positivity of the Hessian off the tangent image.** Let `ψ` be a chart adapted, with
regularity `ℓ ≥ 2`, to the image of a `C^k` totally real embedding `ι`, `k ≥ 1`. At a point `ι y`
of the source of `ψ`, the critical Hessian of `x ↦ ‖e (ψ x).2‖²` is positive on every tangent
vector that is not tangent to `ι`. -/
theorem criticalHessian_norm_sq_snd_pos [I.Boundaryless] (h : IsTotallyRealEmbedding I' I k A ι)
    (hk : 1 ≤ k) (hψ : IsAdaptedChart J (range ι) ψ) (hℓ : 2 ≤ ℓ) {y : N} (hy : ι y ∈ ψ.source)
    {v : TangentSpace I (ι y)} (hv : v ∉ LinearMap.range (mfderiv I' I ι y).toLinearMap) :
    0 < criticalHessian I (fun x ↦ ‖e (ψ x).2‖ ^ 2) (ι y) v v := by
  rw [hψ.criticalHessian_norm_sq_snd_apply hℓ ⟨hy, mem_range_self y⟩, real_inner_self_eq_norm_sq]
  have := (hψ.snd_mfderiv_eq_zero_iff h hk (one_le_two.trans hℓ) hy v).not.2 hv
  have : e (mfderiv I 𝓘(ℝ, F × F) ψ (ι y) v).2 ≠ 0 := by simpa using this
  positivity

end Embedding

end TauCeti.IsAdaptedChart

namespace TauCeti.IsTotallyRealEmbedding

open SmoothAlmostComplexStructure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
  {F W H' N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ F H'} [TopologicalSpace N] [ChartedSpace H' N]
  {k : ℕ∞ω} {ι : N → M}

/-- The tangent images of a totally real embedding into a complex manifold are totally real for
multiplication by `i` on the tangent spaces of `M`. -/
theorem isTotallyReal_range_mfderiv
    (h : IsTotallyRealEmbedding I' 𝓘(ℝ, E) k (ofComplexManifold E M).almostComplexStructureAt ι)
    (y : N) :
    IsTotallyReal ((ofComplexManifold E M).toEndomorphism (ι y)).toLinearMap
      (LinearMap.range (mfderiv I' 𝓘(ℝ, E) ι y).toLinearMap) := by
  rw [← almostComplexStructureAt_toLinearMap]
  exact (isMaximalTotallyRealMap_iff.1 h.isMaximalTotallyRealMap y).isTotallyReal

/-- **The squared distance in an adapted chart is strictly plurisubharmonic near a totally real
submanifold.** Let `ι` be a `C^k` totally real embedding, `k ≥ 1`, into a complex manifold,
`ψ` a chart adapted, with regularity `ℓ ≥ 2`, to its image and to the complex structure, and `e`
a linear isomorphism from the normal coordinate space onto an inner product space. Then
`x ↦ ‖e (ψ x).2‖²`, a squared distance to the zero section in the chart, is strictly
plurisubharmonic on a neighbourhood of the part of the image in the source of `ψ`. -/
theorem setOfPred_isManifoldStrictlyPlurisubharmonicAt_norm_sq_snd_mem_nhdsSet
    (h : IsTotallyRealEmbedding I' 𝓘(ℝ, E) k (ofComplexManifold E M).almostComplexStructureAt ι)
    (hk : 1 ≤ k) {ℓ : ℕ∞} {ψ : OpenPartialHomeomorph M (F × F)}
    (hψ : IsAdaptedChart ((ofComplexManifold E M).toContMDiff ℓ) (range ι) ψ) (hℓ : 2 ≤ ℓ)
    (e : F ≃L[ℝ] W) :
    {x | IsManifoldStrictlyPlurisubharmonicAt E (fun x ↦ ‖e (ψ x).2‖ ^ 2) x} ∈
      𝓝ˢ (ψ.source ∩ range ι) := by
  rw [mem_nhdsSet_iff_forall]
  rintro _ ⟨hy, y, rfl⟩
  exact (SymplecticGeometry.isManifoldStrictlyPlurisubharmonicAt_of_criticalHessian_pos
    (h.isTotallyReal_range_mfderiv y)
    fun v hv ↦ hψ.criticalHessian_norm_sq_snd_pos h hk hℓ hy hv).eventually
    ((hψ.contMDiffAt_norm_sq_snd hy).of_le (WithTop.coe_le_coe.2 hℓ))

/-- **Adapted charts in which the squared distance is strictly plurisubharmonic.** Let `ι` be a
`C^k` totally real embedding, `k ≥ 3`, into a complex manifold, and `e` a linear isomorphism
from the model space of its source onto an inner product space (such as `toEuclidean`). Near
each point `ι y` of its image there is a chart `ψ`, adapted with regularity `2` to the image and
to the complex structure, such that `x ↦ ‖e (ψ x).2‖²` is strictly plurisubharmonic on a
neighbourhood of the part of the image in the source of `ψ`. -/
theorem exists_isAdaptedChart_norm_sq_snd
    [I'.Boundaryless] [IsManifold I' k N]
    (h : IsTotallyRealEmbedding I' 𝓘(ℝ, E) k (ofComplexManifold E M).almostComplexStructureAt ι)
    (hk : 3 ≤ k) (e : F ≃L[ℝ] W) (y : N) :
    ∃ ψ : OpenPartialHomeomorph M (F × F), ι y ∈ ψ.source ∧
      IsAdaptedChart ((ofComplexManifold E M).toContMDiff 2) (range ι) ψ ∧
      {x | IsManifoldStrictlyPlurisubharmonicAt E (fun x ↦ ‖e (ψ x).2‖ ^ 2) x} ∈
        𝓝ˢ (ψ.source ∩ range ι) := by
  have h' : IsTotallyRealEmbedding I' 𝓘(ℝ, E) k
      ((ofComplexManifold E M).toContMDiff 2).almostComplexStructureAt ι := by
    rwa [almostComplexStructureAt_toContMDiff]
  obtain ⟨ψ, -, -, -, -, hy, -, hψ⟩ := h'.exists_adaptedChart one_le_two hk y
  exact ⟨ψ, hy, hψ, h.setOfPred_isManifoldStrictlyPlurisubharmonicAt_norm_sq_snd_mem_nhdsSet
    (le_trans (by norm_num) hk) hψ le_rfl e⟩

/-- **A nonnegative function strictly plurisubharmonic near a closed totally real submanifold.**
Let `ι : N → M` be a `C^k` totally real embedding of a manifold without boundary, with closed
image, into a complex manifold that is Hausdorff and σ-compact, and let `2 ≤ ℓ` with
`ℓ + 1 ≤ k` (for a smooth embedding, `ℓ = ∞`). Then there is a `C^ℓ` function `φ : M → ℝ`,
nonnegative and vanishing exactly on the image of `ι`,
whose critical Hessian at each point `ι y` is positive on every vector outside the tangent image
of `ι` at `y`, and which is strictly plurisubharmonic on a neighbourhood of the image of `ι`.

The function constructed is `∑ᵢ ρᵢ gᵢ` for a smooth partition of unity `ρᵢ` subordinate to
the sources of adapted charts that cover the image and to the complement of the image. The term
`gᵢ` for a chart is the squared distance to the zero section in that chart, and the term for the
complement is the constant `1`. -/
theorem exists_contMDiff_isManifoldStrictlyPlurisubharmonicAt_of_isClosed_range
    [T2Space M] [SigmaCompactSpace M]
    [I'.Boundaryless] [IsManifold I' k N]
    (h : IsTotallyRealEmbedding I' 𝓘(ℝ, E) k (ofComplexManifold E M).almostComplexStructureAt ι)
    (hclosed : IsClosed (range ι)) {ℓ : ℕ∞} (hℓ : 2 ≤ ℓ) (hk : (ℓ : ℕ∞ω) + 1 ≤ k) :
    ∃ φ : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ℓ φ ∧ (∀ x, 0 ≤ φ x) ∧
      (∀ x, φ x = 0 ↔ x ∈ range ι) ∧
      (∀ y, ∀ v ∉ LinearMap.range (mfderiv I' 𝓘(ℝ, E) ι y).toLinearMap,
        0 < criticalHessian 𝓘(ℝ, E) φ (ι y) v v) ∧
      {x | IsManifoldStrictlyPlurisubharmonicAt E φ x} ∈ 𝓝ˢ (range ι) := by
  classical
  set e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ F)) := toEuclidean
  -- Adapted charts at the points of the image.
  have h' : IsTotallyRealEmbedding I' 𝓘(ℝ, E) k
      ((ofComplexManifold E M).toContMDiff ℓ).almostComplexStructureAt ι := by
    rwa [almostComplexStructureAt_toContMDiff]
  have hex (y : N) : ∃ ψ : OpenPartialHomeomorph M (F × F), ι y ∈ ψ.source ∧
      IsAdaptedChart ((ofComplexManifold E M).toContMDiff ℓ) (range ι) ψ := by
    obtain ⟨ψ, -, -, -, -, hy, -, hψ⟩ := h'.exists_adaptedChart (one_le_two.trans hℓ) hk y
    exact ⟨ψ, hy, hψ⟩
  choose ψ hyψ hψ using hex
  -- A partition of unity subordinate to their sources and to the complement of the image.
  let U : Option N → Set M := fun i ↦ i.elim (range ι)ᶜ fun y ↦ (ψ y).source
  have hUo (i : Option N) : IsOpen (U i) := by
    cases i with
    | none => exact hclosed.isOpen_compl
    | some y => exact (ψ y).open_source
  have hUcov : univ ⊆ ⋃ i, U i := by
    intro x _
    by_cases hx : x ∈ range ι
    · obtain ⟨y, rfl⟩ := hx
      exact mem_iUnion.2 ⟨some y, hyψ y⟩
    · exact mem_iUnion.2 ⟨none, hx⟩
  obtain ⟨ρ, hρ⟩ :=
    SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, E) isClosed_univ U hUo hUcov
  let g : Option N → M → ℝ := fun i ↦ i.elim (fun _ ↦ 1) fun y x ↦ ‖e (ψ y x).2‖ ^ 2
  have hg (i : Option N) {x : M} (hx : x ∈ U i) : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) ℓ (g i) x := by
    cases i with
    | none => exact contMDiffAt_const
    | some y => exact (hψ y).contMDiffAt_norm_sq_snd hx
  have hg0 (i : Option N) (x : M) : 0 ≤ g i x := by
    cases i with
    | none => exact zero_le_one
    | some y => exact sq_nonneg _
  -- The points of the image lie in no `U none`.
  have hsome {i : Option N} {y : N} (hi : ι y ∈ U i) :
      ∃ z, i = some z ∧ ι y ∈ (ψ z).source := by
    cases i with
    | none => exact absurd hi (by simp [U])
    | some z => exact ⟨z, rfl, hi⟩
  set φ : M → ℝ := fun x ↦ ∑ᶠ i, ρ i x • g i x
  have hφ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ℓ φ :=
    ρ.contMDiff_finsum_smul fun i x hx ↦ hg i (hρ i hx)
  have hφ0 (x : M) : 0 ≤ φ x := finsum_nonneg fun i ↦ smul_nonneg (ρ.nonneg i x) (hg0 i x)
  -- At `ι y`, every local term with `ι y ∈ U i` vanishes to second order and has a Hessian
  -- positive on `v`.
  have hHess (y : N) (v : TangentSpace 𝓘(ℝ, E) (ι y))
      (hv : v ∉ LinearMap.range (mfderiv I' 𝓘(ℝ, E) ι y).toLinearMap) :
      0 < criticalHessian 𝓘(ℝ, E) φ (ι y) v v := by
    refine ρ.criticalHessian_finsum_smul_pos hρ (mem_univ _) BoundarylessManifold.isInteriorPoint
      (fun i hi ↦ (hg i hi).of_le (WithTop.coe_le_coe.2 hℓ)) (fun i hi ↦ ?_) (fun i hi ↦ ?_)
      fun i hi ↦ ?_ <;> obtain ⟨z, rfl, hz⟩ := hsome hi
    · exact ((hψ z).norm_sq_snd_eq_zero_iff hz).2 (mem_range_self y)
    · exact (hψ z).mem_criticalPoints_norm_sq_snd ⟨hz, mem_range_self y⟩
    · exact (hψ z).criticalHessian_norm_sq_snd_pos h' (le_trans (by norm_num) hk) hℓ hz hv
  refine ⟨φ, hφ, hφ0, fun x ↦ ⟨fun hx ↦ ?_, ?_⟩, hHess, ?_⟩
  · -- Off the image, some `ρ i • g i` is positive at `x`.
    by_contra hxι
    have hpos : 0 < φ x := by
      rw [show φ x = _ from (ρ.sum_finsupport_smul_eq_finsum x g).symm]
      refine Finset.sum_pos (fun i hi ↦ ?_)
        (Finset.nonempty_of_sum_ne_zero ((ρ.sum_finsupport x (mem_univ x)).symm ▸ one_ne_zero))
      have hρi : 0 < ρ i x :=
        lt_of_le_of_ne (ρ.nonneg i x) (Ne.symm ((ρ.mem_finsupport x).1 hi))
      have hxU := hρ i (subset_tsupport _ ((ρ.mem_finsupport x).1 hi))
      refine smul_pos hρi ?_
      cases i with
      | none => exact zero_lt_one
      | some z =>
        exact lt_of_le_of_ne (sq_nonneg _)
          (Ne.symm (((hψ z).norm_sq_snd_eq_zero_iff hxU).not.2 hxι))
    exact hpos.ne' hx
  · rintro ⟨y, rfl⟩
    refine finsum_eq_zero_of_forall_eq_zero fun i ↦ ?_
    by_cases hi : ι y ∈ tsupport (ρ i)
    · obtain ⟨z, rfl, hz⟩ := hsome (hρ i hi)
      simp [g, ((hψ z).norm_sq_snd_eq_zero_iff hz).2 (mem_range_self y)]
    · simp [image_eq_zero_of_notMem_tsupport hi]
  · exact SymplecticGeometry.setOfPred_isManifoldStrictlyPlurisubharmonicAt_mem_nhdsSet_range
      (fun y ↦ (hφ (ι y)).of_le (WithTop.coe_le_coe.2 hℓ)) h.isTotallyReal_range_mfderiv hHess

end TauCeti.IsTotallyRealEmbedding


/-! ### Squared distance near a compact part of an embedding -/

namespace Manifold.IsSmoothEmbedding

open TauCeti TauCeti.SmoothAlmostComplexStructure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
  {F H' N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ F H'} [TopologicalSpace N] [ChartedSpace H' N]
  {ι : N → M}

/-- **A nonnegative function strictly plurisubharmonic near a compact part of a totally real
submanifold.** Let `ι : N → M` be a `C^n` embedding, `n ≥ 2`, of a manifold without boundary into
a Hausdorff complex manifold, let `K ⊆ N` be compact, and let the tangent images of `ι` at the
points of `K` be totally real for the complex structure of `M`. Then there are a nonnegative
`C^n` function `ρ : M → ℝ` and an open set `V ⊇ ι '' K` such that on `V` the function `ρ`
vanishes exactly on the image of `ι` and is strictly plurisubharmonic, and at each point `ι y`
with `y ∈ K` the critical Hessian of `ρ` is positive on every vector outside the tangent image of
`ι` at `y`.

No relation between the dimensions of `N` and `M` is assumed. The function constructed is
`∑ᵢ bᵢ gᵢ` over finitely many points `yᵢ ∈ K`, where `gᵢ` is a squared normal coordinate of `ι`
near `ι yᵢ` and `bᵢ` a smooth bump function at `ι yᵢ` supported where `gᵢ` is defined. -/
theorem exists_contMDiff_isManifoldStrictlyPlurisubharmonicAt_of_isCompact [T2Space M]
    [I'.Boundaryless] {n : ℕ∞} (h : IsSmoothEmbedding I' 𝓘(ℝ, E) n ι) (hn : 2 ≤ n)
    {K : Set N} (hK : IsCompact K)
    (hι : ∀ y ∈ K, IsTotallyReal ((ofComplexManifold E M).toEndomorphism (ι y)).toLinearMap
      (LinearMap.range (mfderiv I' 𝓘(ℝ, E) ι y).toLinearMap)) :
    ∃ ρ : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) n ρ ∧ (∀ x, 0 ≤ ρ x) ∧
      ∃ V : Set M, IsOpen V ∧ ι '' K ⊆ V ∧ (∀ x ∈ V, ρ x = 0 ↔ x ∈ range ι) ∧
        (∀ x ∈ V, IsManifoldStrictlyPlurisubharmonicAt E ρ x) ∧
        ∀ y ∈ K, ∀ v ∉ LinearMap.range (mfderiv I' 𝓘(ℝ, E) ι y).toLinearMap,
          0 < criticalHessian 𝓘(ℝ, E) ρ (ι y) v v := by
  classical
  have hn' : ((2 : ℕ∞) : WithTop ℕ∞) ≤ n := WithTop.coe_le_coe.2 hn
  -- Local squared normal coordinates, and bump functions supported where they are defined.
  choose U hUo hyU g hg hg0 hgU hgc using fun y ↦
    h.exists_contMDiffOn_criticalHessian_pos hn' y
  choose b hbU using fun y ↦
    ((SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, E)) (ι y)).mem_iff.1
      ((hUo y).mem_nhds (hyU y))).imp fun _ h ↦ h.2
  -- Finitely many of their supports cover `ι '' K`.
  obtain ⟨t, -, htK⟩ := hK.elim_nhds_subcover (fun y ↦ ι ⁻¹' Function.support (b y)) fun y _ ↦
    h.isEmbedding.continuous.continuousAt.preimage_mem_nhds ((b y).isOpen_support.mem_nhds
      (b y).c_mem_support)
  have hcov (z : N) (hz : z ∈ K) : ∃ y ∈ t, 0 < b y (ι z) := by
    obtain ⟨y, hy, hyz⟩ := mem_iUnion₂.1 (htK hz)
    exact ⟨y, hy, (b y).nonneg.lt_of_ne (Ne.symm hyz)⟩
  set ρ : M → ℝ := ∑ y ∈ t, ⇑(b y) * g y with hρ_def
  have hρ (x : M) : ρ x = ∑ y ∈ t, b y x * g y x := by simp [hρ_def]
  have hterm (y : N) : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) n (⇑(b y) * g y) :=
    contMDiff_of_tsupport fun x hx ↦
      have hxU := hbU y (tsupport_mul_subset_left hx)
      ((b y).contMDiffAt.of_le (WithTop.coe_le_coe.2 le_top)).mul
        ((hg y).contMDiffAt ((hUo y).mem_nhds hxU))
  have hρs : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) n ρ := contMDiff_finsetSum' fun y _ ↦ hterm y
  have hρ0 (x : M) : 0 ≤ ρ x := by
    rw [hρ]; exact Finset.sum_nonneg fun y _ ↦ mul_nonneg (b y).nonneg (hg0 y x)
  have hHess (z : N) (hz : z ∈ K) (v : TangentSpace 𝓘(ℝ, E) (ι z))
      (hv : v ∉ LinearMap.range (mfderiv I' 𝓘(ℝ, E) ι z).toLinearMap) :
      0 < criticalHessian 𝓘(ℝ, E) ρ (ι z) v v :=
    criticalHessian_sum_mul_pos BoundarylessManifold.isInteriorPoint (fun y _ ↦ hbU y)
      (fun y _ ↦ (b y).contMDiffAt.of_le (WithTop.coe_le_coe.2 le_top)) (fun y _ ↦ (b y).nonneg)
      (fun y _ hy ↦ ((hg y).contMDiffAt ((hUo y).mem_nhds hy)).of_le hn')
      (fun y _ hy ↦ (hgU y _ hy).2 (mem_range_self z)) (fun y _ hy ↦ (hgc y z hy).1)
      (fun y _ hy ↦ (hgc y z hy).2 v hv) (hcov z hz)
  -- Strict plurisubharmonicity at the points of `ι '' K` spreads to a neighbourhood.
  have hpsh : {x | IsManifoldStrictlyPlurisubharmonicAt E ρ x} ∈ 𝓝ˢ (ι '' K) := by
    rw [mem_nhdsSet_iff_forall]
    rintro _ ⟨z, hz, rfl⟩
    exact (SymplecticGeometry.isManifoldStrictlyPlurisubharmonicAt_of_criticalHessian_pos
      (hι z hz) (hHess z hz)).eventually ((hρs (ι z)).of_le hn')
  obtain ⟨W, hWo, hKW, hW⟩ := mem_nhdsSet_iff_exists.1 hpsh
  refine ⟨ρ, hρs, hρ0, W ∩ ⋃ y ∈ t, Function.support (b y),
    hWo.inter (isOpen_biUnion fun y _ ↦ (b y).isOpen_support),
    fun _ ⟨z, hz, hzx⟩ ↦ hzx ▸ ⟨hKW ⟨z, hz, rfl⟩, by simpa using htK hz⟩,
    fun x ⟨_, hx⟩ ↦ ⟨fun hρx ↦ ?_, fun hx ↦ ?_⟩, fun x hx ↦ hW hx.1, hHess⟩
  · obtain ⟨y, hy, hyx⟩ := mem_iUnion₂.1 hx
    rw [hρ, Finset.sum_eq_zero_iff_of_nonneg fun y _ ↦ mul_nonneg (b y).nonneg (hg0 y x)]
      at hρx
    have hxU := hbU y (subset_tsupport _ hyx)
    exact (hgU y x hxU).1 ((mul_eq_zero.1 (hρx y hy)).resolve_left hyx)
  · rw [hρ]
    refine Finset.sum_eq_zero fun y _ ↦ ?_
    by_cases hyx : b y x = 0
    · rw [hyx, zero_mul]
    · rw [(hgU y x (hbU y (subset_tsupport _ hyx))).2 hx, mul_zero]

end Manifold.IsSmoothEmbedding

end
