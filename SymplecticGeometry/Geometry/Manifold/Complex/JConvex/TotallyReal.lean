/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.JConvex.Hypersurface
public import SymplecticGeometry.Geometry.Manifold.Complex.LeviForm
public import SymplecticGeometry.LinearAlgebra.TotallyReal.Basic
public import TauCeti.Analysis.InnerProductSpace.Calculus
public import TauCeti.Geometry.Contact.Pullback
public import TauCeti.Geometry.Manifold.Complex.TotallyReal.AdaptedChart
public import TauCeti.Geometry.Symplectic.Lagrangian.TotallyReal
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
* `SymplecticGeometry.setOf_isManifoldStrictlyPlurisubharmonicAt_mem_nhdsSet_range`: for a map
  `ι : S → M` with totally real tangent images, and `f` real `C²` along `ι(S)` with Hessian
  positive at each point `ι s` off the tangent image of `ι` at `s`, the function `f` is strictly
  plurisubharmonic on a neighbourhood of `ι(S)`. This combines the criterion with
  `TauCeti.IsManifoldStrictlyPlurisubharmonicAt.eventually`.

A nonnegative function that vanishes along `ι(S)` has a critical point at each point of `ι(S)`,
where its Hessian does not depend on the chart; the statements here do not need this, since
Tau Ceti's criterion holds at every point for the Hessian in the preferred chart.

Finally it applies the criterion to the squared distance in an adapted chart. For a totally real
embedding `ι : N → M` modelled on a real inner product space `V`, Tau Ceti's
`TauCeti.IsTotallyRealEmbedding.exists_adaptedChart` gives charts `ψ : M → V × V` that flatten
the image of `ι` onto `V × {0}` (`TauCeti.IsAdaptedChart`). For such a chart:

* `TauCeti.IsAdaptedChart.norm_sq_snd_eq_zero_iff`: on the source of `ψ`, the function
  `x ↦ ‖(ψ x).2‖²` vanishes exactly on the image, where it has critical points
  (`TauCeti.IsAdaptedChart.mem_criticalPoints_norm_sq_snd`);
* `TauCeti.IsAdaptedChart.criticalHessian_norm_sq_snd_apply`: its critical Hessian at a point of
  the image is `2 ⟪(dψ u).2, (dψ w).2⟫`, by Tau Ceti's second-order chain rule
  `TauCeti.criticalHessian_comp_apply`;
* `TauCeti.IsAdaptedChart.snd_mfderiv_eq_zero_iff` and
  `TauCeti.IsAdaptedChart.criticalHessian_norm_sq_snd_pos`: `dψ` sends exactly the tangent image
  of `ι` into `V × {0}`, so this Hessian is positive off the tangent image;
* `IsTotallyRealEmbedding.setOf_isManifoldStrictlyPlurisubharmonicAt_norm_sq_snd_mem_nhdsSet`:
  for a complex manifold, with the adapted chart taken for
  `(ofComplexManifold E M).toContMDiff ℓ`, `ℓ ≥ 2`, the function is strictly plurisubharmonic on a
  neighbourhood of the part of the image in the source of `ψ`;
* `TauCeti.IsTotallyRealEmbedding.exists_isAdaptedChart_norm_sq_snd`: such charts exist near each
  point of the image of a `C³` totally real embedding. Total reality for `ofComplexManifold E M`
  and for its `C^ℓ` version agree, since both have the same pointwise structures
  (`TauCeti.SmoothAlmostComplexStructure.almostComplexStructureAt_toContMDiff`).

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
theorem setOf_isManifoldStrictlyPlurisubharmonicAt_mem_nhdsSet_range [FiniteDimensional ℂ E]
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

namespace TauCeti.SmoothAlmostComplexStructure

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Viewing a smooth almost complex structure at a finite regularity leaves its pointwise
structures unchanged. -/
@[simp]
theorem almostComplexStructureAt_toContMDiff (J : SmoothAlmostComplexStructure I M) (n : ℕ∞) :
    (J.toContMDiff n).almostComplexStructureAt = J.almostComplexStructureAt := by
  funext x
  ext v
  rw [ContMDiffAlmostComplexStructure.almostComplexStructureAt_toLinearMap,
    almostComplexStructureAt_toLinearMap, toContMDiff_toEndomorphism_apply]

end TauCeti.SmoothAlmostComplexStructure

namespace TauCeti.IsAdaptedChart

variable {E H M V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] {ℓ : ℕ∞}
  {J : ContMDiffAlmostComplexStructure I ℓ M} {s : Set M} {ψ : OpenPartialHomeomorph M (V × V)}

/-- In a chart adapted to `s`, the squared norm of the normal coordinate vanishes on the source
exactly at the points of `s`. -/
theorem norm_sq_snd_eq_zero_iff (hψ : IsAdaptedChart J s ψ) {x : M} (hx : x ∈ ψ.source) :
    ‖(ψ x).2‖ ^ 2 = 0 ↔ x ∈ s := by
  rw [← hψ.isImage hx]
  simp

/-- In a chart adapted to `s`, the points of `s` in the source are critical points of the
squared norm of the normal coordinate, which is its minimum there. -/
theorem mem_criticalPoints_norm_sq_snd [I.Boundaryless] (hψ : IsAdaptedChart J s ψ) {x : M}
    (hx : x ∈ ψ.source ∩ s) : x ∈ criticalPoints I (fun y ↦ ‖(ψ y).2‖ ^ 2) := by
  refine IsLocalMin.mem_criticalPoints (Filter.Eventually.of_forall fun y ↦ ?_)
    BoundarylessManifold.isInteriorPoint
  dsimp only
  rw [(hψ.norm_sq_snd_eq_zero_iff hx.1).2 hx.2]
  positivity

/-- A chart adapted with regularity `ℓ ≥ 2` is `C²` at each point of its source. -/
theorem contMDiffAt (hψ : IsAdaptedChart J s ψ) (hℓ : 2 ≤ ℓ) {x : M} (hx : x ∈ ψ.source) :
    ContMDiffAt I 𝓘(ℝ, V × V) 2 ψ x :=
  ((hψ.contMDiffOn x hx).contMDiffAt (ψ.open_source.mem_nhds hx)).of_le (WithTop.coe_le_coe.2 hℓ)

/-- The squared norm of the normal coordinate of a chart adapted with regularity `ℓ ≥ 2` is `C²`
at each point of its source. -/
theorem contMDiffAt_norm_sq_snd (hψ : IsAdaptedChart J s ψ) (hℓ : 2 ≤ ℓ) {x : M}
    (hx : x ∈ ψ.source) : ContMDiffAt I 𝓘(ℝ) 2 (fun y ↦ ‖(ψ y).2‖ ^ 2) x :=
  (contDiff_norm_sq ℝ).contMDiff.contMDiffAt.comp x
    (contDiff_snd.contMDiff.contMDiffAt.comp x (hψ.contMDiffAt hℓ hx))

/-- **The Hessian of the squared distance in an adapted chart.** At a point `x` of `s` in the
source of a chart `ψ` adapted to `s` with regularity `ℓ ≥ 2`, the critical Hessian of
`y ↦ ‖(ψ y).2‖²` is `2 ⟪(dψ u).2, (dψ w).2⟫`. -/
theorem criticalHessian_norm_sq_snd_apply [I.Boundaryless] (hψ : IsAdaptedChart J s ψ)
    (hℓ : 2 ≤ ℓ) {x : M} (hx : x ∈ ψ.source ∩ s) (u w : TangentSpace I x) :
    criticalHessian I (fun y ↦ ‖(ψ y).2‖ ^ 2) x u w =
      2 * inner ℝ (mfderiv I 𝓘(ℝ, V × V) ψ x u).2 (mfderiv I 𝓘(ℝ, V × V) ψ x w).2 := by
  have hψx := hψ.contMDiffAt hℓ hx.1
  have hφ : ContMDiffAt I 𝓘(ℝ, V) 2 (fun y ↦ (ψ y).2) x :=
    contDiff_snd.contMDiff.contMDiffAt.comp x hψx
  have hcrit : (ψ x).2 ∈ criticalPoints 𝓘(ℝ, V) (fun z : V ↦ ‖z‖ ^ 2) := by
    refine IsLocalMin.mem_criticalPoints (Filter.Eventually.of_forall fun z ↦ ?_)
      BoundarylessManifold.isInteriorPoint
    rw [show (ψ x).2 = 0 from (hψ.isImage hx.1).2 hx.2]
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    positivity
  -- The second-order chain rule at the critical point `(ψ x).2 = 0` of `‖·‖²`.
  have h := criticalHessian_comp_apply (f := fun z : V ↦ ‖z‖ ^ 2) rfl
    (contDiff_norm_sq ℝ).contMDiff.contMDiffAt hφ hcrit u w
  have hD : mfderiv I 𝓘(ℝ, V) (fun y ↦ (ψ y).2) x =
      (ContinuousLinearMap.snd ℝ V V).comp (mfderiv I 𝓘(ℝ, V × V) ψ x) :=
    (hasFDerivAt_snd.hasMFDerivAt.comp x (hψx.mdifferentiableAt two_ne_zero).hasMFDerivAt).mfderiv
  rw [hD, criticalHessian_modelSpace] at h
  -- `(snd ∘L dψ) u` is `(dψ u).2` by definition, read in `TangentSpace 𝓘(ℝ, V) (ψ x).2 = V`.
  exact h.trans (TauCeti.fderiv_fderiv_norm_sq_apply (E := V) _ _ _)

section Embedding

variable {H' N : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ V H'} [TopologicalSpace N]
  [ChartedSpace H' N] [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] {k : ℕ∞ω}
  {A : ∀ y : M, AlmostComplexStructure (TangentSpace I y)} {ι : N → M}

/-- **The tangent image in an adapted chart.** Let `ψ` be a chart adapted to the image of a
`C^k` totally real embedding `ι`, with `k, ℓ ≥ 1`. At a point `ι y` of the source of `ψ`, the
derivative of `ψ` sends a tangent vector into the zero section `V × {0}` exactly when the vector
is tangent to `ι`. -/
theorem snd_mfderiv_eq_zero_iff (h : IsTotallyRealEmbedding I' I k A ι) (hk : 1 ≤ k)
    (hψ : IsAdaptedChart J (range ι) ψ) (hℓ : 1 ≤ ℓ) {y : N} (hy : ι y ∈ ψ.source)
    (v : TangentSpace I (ι y)) :
    (mfderiv I 𝓘(ℝ, V × V) ψ (ι y) v).2 = 0 ↔
      v ∈ LinearMap.range (mfderiv I' I ι y).toLinearMap := by
  have hℓ0 : (ℓ : ℕ∞ω) ≠ 0 := by exact_mod_cast (zero_lt_one.trans_le hℓ).ne'
  have hψd : ψ.MDifferentiable I 𝓘(ℝ, V × V) :=
    ⟨hψ.contMDiffOn.mdifferentiableOn hℓ0, hψ.contMDiffOn_symm.mdifferentiableOn hℓ0⟩
  have hψy := hψd.mdifferentiableAt hy
  have hιy : MDifferentiableAt I' I ι y :=
    (h.isSmoothEmbedding.contMDiff y).mdifferentiableAt (zero_lt_one.trans_le hk).ne'
  set D := mfderiv I 𝓘(ℝ, V × V) ψ (ι y)
  set K := LinearMap.ker ((LinearMap.snd ℝ V V).comp D.toLinearMap)
  -- Membership in `K` is by definition the vanishing of `(dψ v).2`.
  change v ∈ K ↔ _
  -- `ψ ∘ ι` stays in the zero section near `y`, so `dψ ∘ dι` takes values in `V × {0}`.
  have hle : LinearMap.range (mfderiv I' I ι y).toLinearMap ≤ K := by
    have hzero : Prod.snd ∘ ψ ∘ ι =ᶠ[𝓝 y] fun _ ↦ (0 : V) :=
      eventually_of_mem (h.isSmoothEmbedding.contMDiff.continuous.continuousAt.preimage_mem_nhds
        (ψ.open_source.mem_nhds hy)) fun z hz ↦ (hψ.isImage hz).2 (mem_range_self z)
    have hcomp := (hasFDerivAt_snd.hasMFDerivAt.comp y
      (hψy.hasMFDerivAt.comp y hιy.hasMFDerivAt)).mfderiv
    rw [hzero.mfderiv_eq, mfderiv_const] at hcomp
    rintro _ ⟨t, rfl⟩
    exact congr($hcomp.symm t)
  -- Both have the dimension of `V`: `dι` is injective and `dψ` is onto.
  suffices hK : LinearMap.range (mfderiv I' I ι y).toLinearMap = K by rw [hK]
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  have hsurj : LinearMap.range ((LinearMap.snd ℝ V V).comp D.toLinearMap) = ⊤ :=
    LinearMap.range_eq_top.2 ((LinearMap.snd_surjective (R := ℝ) (M := V) (M₂ := V)).comp
      (hψd.mfderiv_surjective hy))
  have hrn := LinearMap.finrank_range_add_finrank_ker ((LinearMap.snd ℝ V V).comp D.toLinearMap)
  rw [hsurj, finrank_top, TauCeti.finrank_tangentSpace, ← h.two_mul_finrank] at hrn
  rw [LinearMap.finrank_range_of_inj (h.mfderiv_injective y), TauCeti.finrank_tangentSpace]
  -- Unfold `K`, so that `omega` sees the kernel of `hrn`.
  change _ = finrank ℝ (LinearMap.ker ((LinearMap.snd ℝ V V).comp D.toLinearMap))
  omega

/-- **Positivity of the Hessian off the tangent image.** Let `ψ` be a chart adapted, with
regularity `ℓ ≥ 2`, to the image of a `C^k` totally real embedding `ι`, `k ≥ 1`. At a point `ι y`
of the source of `ψ`, the critical Hessian of `x ↦ ‖(ψ x).2‖²` is positive on every tangent vector
that is not tangent to `ι`. -/
theorem criticalHessian_norm_sq_snd_pos [I.Boundaryless] (h : IsTotallyRealEmbedding I' I k A ι)
    (hk : 1 ≤ k) (hψ : IsAdaptedChart J (range ι) ψ) (hℓ : 2 ≤ ℓ) {y : N} (hy : ι y ∈ ψ.source)
    {v : TangentSpace I (ι y)} (hv : v ∉ LinearMap.range (mfderiv I' I ι y).toLinearMap) :
    0 < criticalHessian I (fun x ↦ ‖(ψ x).2‖ ^ 2) (ι y) v v := by
  rw [hψ.criticalHessian_norm_sq_snd_apply hℓ ⟨hy, mem_range_self y⟩, real_inner_self_eq_norm_sq]
  have := (hψ.snd_mfderiv_eq_zero_iff h hk (one_le_two.trans hℓ) hy v).not.2 hv
  positivity

end Embedding

end TauCeti.IsAdaptedChart

namespace TauCeti.IsTotallyRealEmbedding

open SmoothAlmostComplexStructure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
  {V H' N : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ V H'} [TopologicalSpace N] [ChartedSpace H' N]
  {k : ℕ∞ω} {ι : N → M}

/-- **The squared distance in an adapted chart is strictly plurisubharmonic near a totally real
submanifold.** Let `ι` be a `C^k` totally real embedding, `k ≥ 1`, into a complex manifold, and
`ψ` a chart adapted, with regularity `ℓ ≥ 2`, to its image and to the complex structure. Then
`x ↦ ‖(ψ x).2‖²`, the squared distance to the zero section in the chart, is strictly
plurisubharmonic on a neighbourhood of the part of the image in the source of `ψ`. -/
theorem setOf_isManifoldStrictlyPlurisubharmonicAt_norm_sq_snd_mem_nhdsSet
    (h : IsTotallyRealEmbedding I' 𝓘(ℝ, E) k (ofComplexManifold E M).almostComplexStructureAt ι)
    (hk : 1 ≤ k) {ℓ : ℕ∞} {ψ : OpenPartialHomeomorph M (V × V)}
    (hψ : IsAdaptedChart ((ofComplexManifold E M).toContMDiff ℓ) (range ι) ψ) (hℓ : 2 ≤ ℓ) :
    {x | IsManifoldStrictlyPlurisubharmonicAt E (fun x ↦ ‖(ψ x).2‖ ^ 2) x} ∈
      𝓝ˢ (ψ.source ∩ range ι) := by
  rw [mem_nhdsSet_iff_forall]
  rintro _ ⟨hy, y, rfl⟩
  have hL : IsTotallyReal ((ofComplexManifold E M).toEndomorphism (ι y)).toLinearMap
      (LinearMap.range (mfderiv I' 𝓘(ℝ, E) ι y).toLinearMap) := by
    rw [← almostComplexStructureAt_toLinearMap]
    exact (isMaximalTotallyRealMap_iff.1 h.isMaximalTotallyRealMap y).isTotallyReal
  exact (SymplecticGeometry.isManifoldStrictlyPlurisubharmonicAt_of_criticalHessian_pos hL
    fun v hv ↦ hψ.criticalHessian_norm_sq_snd_pos h hk hℓ hy hv).eventually
    (hψ.contMDiffAt_norm_sq_snd hℓ hy)

/-- **Adapted charts in which the squared distance is strictly plurisubharmonic.** Let `ι` be a
`C^k` totally real embedding, `k ≥ 3`, into a complex manifold. Near each point `ι y` of its
image there is a chart `ψ`, adapted with regularity `2` to the image and to the complex structure,
such that `x ↦ ‖(ψ x).2‖²` is strictly plurisubharmonic on a neighbourhood of the part of the
image in the source of `ψ`. -/
theorem exists_isAdaptedChart_norm_sq_snd
    [I'.Boundaryless] [IsManifold I' k N]
    (h : IsTotallyRealEmbedding I' 𝓘(ℝ, E) k (ofComplexManifold E M).almostComplexStructureAt ι)
    (hk : 3 ≤ k) (y : N) :
    ∃ ψ : OpenPartialHomeomorph M (V × V), ι y ∈ ψ.source ∧
      IsAdaptedChart ((ofComplexManifold E M).toContMDiff 2) (range ι) ψ ∧
      {x | IsManifoldStrictlyPlurisubharmonicAt E (fun x ↦ ‖(ψ x).2‖ ^ 2) x} ∈
        𝓝ˢ (ψ.source ∩ range ι) := by
  have h' : IsTotallyRealEmbedding I' 𝓘(ℝ, E) k
      ((ofComplexManifold E M).toContMDiff 2).almostComplexStructureAt ι := by
    rwa [almostComplexStructureAt_toContMDiff]
  obtain ⟨ψ, -, -, -, -, hy, -, hψ⟩ := h'.exists_adaptedChart one_le_two hk y
  exact ⟨ψ, hy, hψ, h.setOf_isManifoldStrictlyPlurisubharmonicAt_norm_sq_snd_mem_nhdsSet
    (le_trans (by norm_num) hk) hψ le_rfl⟩

end TauCeti.IsTotallyRealEmbedding

end
