/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.JConvex.Hypersurface
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

end SymplecticGeometry

end
