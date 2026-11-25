/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.JConvex.Hypersurface
public import SymplecticGeometry.Geometry.Manifold.Complex.LeviForm
public import SymplecticGeometry.LinearAlgebra.TotallyReal.Basic
public import TauCeti.Geometry.Contact.Pullback
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

## References

* [K. Cieliebak, Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Chapter 2, on J-convex functions and hypersurfaces.
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

end
