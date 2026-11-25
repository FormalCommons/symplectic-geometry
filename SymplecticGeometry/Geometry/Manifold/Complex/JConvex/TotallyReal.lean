/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.JConvex.Hypersurface
public import TauCeti.Geometry.Contact.Pullback
public import TauCeti.LinearAlgebra.TotallyReal.Basic

/-!
# Totally real submanifolds and J-convex functions

Let `M` be a complex manifold modelled on `E`, seen as a real manifold, with the complex structure
`J = ofComplexManifold E M`. For a smooth real function `f`, write `λ_f = -df ∘ J` and
`ω_f = dλ_f`, as in `SymplecticGeometry.Geometry.Manifold.Complex.Plurisubharmonic`.

This file proves that isotropic submanifolds of a J-convex level that are tangent to its
complex tangencies are totally real:

* `SymplecticGeometry.isTotallyReal_range_mfderiv_of_isManifoldStrictlyPlurisubharmonicAt`: if
  `f` is strictly plurisubharmonic at `ι s` and `ω_f` vanishes on the tangent image of `ι` at `s`,
  then that tangent image is totally real for `J`. A vector `u` of the tangent image with `J u` in
  it too would give `ω_f(u, J u) = 0`, which strict plurisubharmonicity rules out unless `u = 0`.
  The argument is that of Tau Ceti's `TauCeti.SymplecticForm.IsIsotropic.disjoint_map_of_tames`,
  for a form that need not be nondegenerate away from the point.
* `SymplecticGeometry.IsJConvexLevel.isTotallyReal_range_mfderiv`: a smooth map into a J-convex
  level `f ⁻¹' {c}` whose tangent vectors `v` satisfy `df(i v) = 0`, that is, are tangent to the
  complex tangencies of the level, has totally real tangent images. Such a map pulls `λ_f` back to
  zero, hence `ω_f` too, by Tau Ceti's
  `TauCeti.SmoothForm.mpullback_mextDerivₗ_eq_zero_of_isHorizontalMap`.

## References

* [K. Cieliebak, Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Chapter 2, on J-convex functions and hypersurfaces.
-/

public section

noncomputable section

open Set Module
open scoped Manifold ContDiff TauCeti.ComplexManifold

namespace SymplecticGeometry

open TauCeti TauCeti.SmoothAlmostComplexStructure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
  {F H S : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
  {I : ModelWithCorners ℝ F H} [TopologicalSpace S] [ChartedSpace H S]

/-- **Isotropic tangent images at strictly plurisubharmonic points are totally real.** Let
`ι : S → M` be a map, `s` a point, and `f` a smooth real function strictly plurisubharmonic at
`ι s`. If `ω_f = d(-df ∘ J)` vanishes at `ι s` on each pair of vectors of the tangent image
`dι_s(T_s S)`, then that tangent image is totally real for the complex structure `J` of `M`. -/
theorem isTotallyReal_range_mfderiv_of_isManifoldStrictlyPlurisubharmonicAt
    {f : C^∞⟮𝓘(ℝ, E), M; ℝ⟯} {ι : S → M} {s : S}
    (hf : IsManifoldStrictlyPlurisubharmonicAt E f (ι s))
    (hι : ∀ v w : TangentSpace I s,
      SmoothBundleForm.eval₂ (mextDerivₗ 𝓘(ℝ, E) 1 ((ofComplexManifold E M).covectorComplexStructure
          (mextDerivₗ 𝓘(ℝ, E) 0 (SmoothForm.ofFunction f)))) (ι s)
        (mfderiv I 𝓘(ℝ, E) ι s v) (mfderiv I 𝓘(ℝ, E) ι s w) = 0) :
    IsTotallyReal ((ofComplexManifold E M).toEndomorphism (ι s)).toLinearMap
      (LinearMap.range (mfderiv I 𝓘(ℝ, E) ι s).toLinearMap) := by
  rw [isTotallyReal_iff, Submodule.disjoint_def]
  rintro _ ⟨w, rfl⟩ ⟨_, ⟨v, rfl⟩, hvw⟩
  -- `u = dι(v)` has `J u = dι(w)` in the tangent image, so `ω_f(u, J u) = 0`, and `u = 0`.
  have hJ : (ofComplexManifold E M).toEndomorphism (ι s) (mfderiv I 𝓘(ℝ, E) ι s v) =
      Complex.I • (show E from mfderiv I 𝓘(ℝ, E) ι s v) :=
    ofComplexManifold_apply (E := E) (ι s) _
  simp only [ContinuousLinearMap.coe_coe] at hvw
  have h0 := hι v w
  rw [SmoothBundleForm.eval₂_apply, ← hvw, hJ] at h0
  have hv : mfderiv I 𝓘(ℝ, E) ι s v = 0 := by
    by_contra hne
    exact ((isManifoldStrictlyPlurisubharmonicAt_iff_forall_pos f (ι s)).1 hf _ hne).ne' h0
  rw [ContinuousLinearMap.coe_coe, ← hvw, hv, map_zero]

/-- **Isotropic submanifolds of a J-convex level tangent to its complex tangencies are totally
real.** Let `f ⁻¹' {c}` be a J-convex level and `ι : S → M` a smooth map with image in the level
whose tangent vectors stay in the kernel of `df` after multiplication by `i`:
`df(i dι(v)) = 0`. Then each tangent image `dι_s(T_s S)` is totally real for the complex
structure `J` of `M`. Such a map is isotropic for `ω_f`: it pulls `λ_f` back to zero, so it pulls
back `ω_f = dλ_f` to zero too. -/
theorem IsJConvexLevel.isTotallyReal_range_mfderiv [IsManifold I ∞ S]
    {f : C^∞⟮𝓘(ℝ, E), M; ℝ⟯} {c : ℝ} (hf : IsJConvexLevel E f c) {ι : S → M}
    (hι : ContMDiff I 𝓘(ℝ, E) ∞ ι) (hιc : ∀ s, f (ι s) = c)
    (hξ : ∀ s (v : TangentSpace I s),
      mvfderiv 𝓘(ℝ, E) f (ι s) (Complex.I • (show E from mfderiv I 𝓘(ℝ, E) ι s v)) = 0)
    (s : S) :
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
  refine isTotallyReal_range_mfderiv_of_isManifoldStrictlyPlurisubharmonicAt
    (hf.isManifoldStrictlyPlurisubharmonicAt _ (hιc s)) fun v w ↦ ?_
  rw [← SmoothForm.eval₂_mpullback ι hι, hω, SmoothBundleForm.eval₂_apply]
  simp

end SymplecticGeometry

end
