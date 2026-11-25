/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.Plurisubharmonic
public import TauCeti.Geometry.Symplectic.Liouville.ContactType
import TauCeti.Geometry.Symplectic.Manifold.Flat

/-!
# J-convex hypersurfaces and their contact structure

Let `M` be a complex manifold modelled on `E`, seen as a real manifold, with the complex structure
`J = ofComplexManifold E M`. For a smooth real function `f`, write `λ_f = -df ∘ J` and
`ω_f = dλ_f`, as in `SymplecticGeometry.Geometry.Manifold.Complex.Plurisubharmonic`.

The level `f ⁻¹' {c}` is a **J-convex level** (`SymplecticGeometry.IsJConvexLevel E f c`) when
`c` is a regular value of `f` (Tau Ceti's `TauCeti.IsRegularValue`) and `f` is strictly
plurisubharmonic at each point of the level. This file proves that such a level carries the
contact structure of its complex tangencies:

* `SymplecticGeometry.IsJConvexLevel.isContactForm_mpullback`: for a smooth immersion `ι : S → M`
  of a manifold of one dimension less, with image in the level, the pullback `ι^* λ_f` is a
  contact form. At each point, `ω_f` is nondegenerate, and the vector `z` with `ι_z ω_f = λ_f`
  satisfies `df(z) = ω_f(z, i z) > 0`, so it is transverse to the level; Tau Ceti's pointwise
  `TauCeti.isContactFormAt_mpullback` concludes.
* `SymplecticGeometry.mem_kerDistribution_mpullback_covectorComplexStructure_iff`: for such an
  immersion into a level of `f`, at a regular point, the kernel of `ι^* λ_f` at `s` consists of
  the vectors `v` whose image `dι(v)` stays tangent after multiplication by `i`: the complex
  tangencies of the hypersurface. The tangent image of `ι` is the kernel of `df`, by Tau Ceti's
  `TauCeti.IsRegularPoint.range_mfderiv_eq_ker_mfderiv`.

The Levi form of a level, `L_f` restricted to the complex tangencies `ker ∂f` of `{f = 0}`,
depends on the defining function only through a factor:
`SymplecticGeometry.manifoldLeviForm_apply_of_eventuallyEq_mul` shows that for `g = a f` near
`x`, with `f x = 0`, the Levi form of `g` there is `a x` times that of `f`. It is the pointwise
product rule `TauCeti.manifoldLeviForm_mul_apply` of Tau Ceti.

Examples: the regular levels of a Stein function
(`SymplecticGeometry.IsSteinFunction.isJConvexLevel`) and the spheres `‖z‖² = c`, `c > 0`, of a
complex inner product space
(`SymplecticGeometry.isJConvexLevel_norm_sq`).

## References

* [K. Cieliebak, Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Chapter 2, on J-convex functions and hypersurfaces.
-/

public section

noncomputable section

open Set Filter Topology Module
open scoped Manifold ContDiff TauCeti.ComplexManifold ComplexConjugate

namespace SymplecticGeometry

open TauCeti TauCeti.SmoothAlmostComplexStructure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

/-! ### J-convex levels -/

variable (E) in
/-- The level `f ⁻¹' {c}` of a real function `f` on a complex manifold is a **J-convex level**
when `c` is a regular value of `f` and `f` is strictly plurisubharmonic at each point of the
level. -/
structure IsJConvexLevel (f : M → ℝ) (c : ℝ) : Prop where
  /-- The value `c` is a regular value of `f`. -/
  isRegularValue : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f c
  /-- The function `f` is strictly plurisubharmonic at each point of the level. -/
  isManifoldStrictlyPlurisubharmonicAt :
    ∀ x, f x = c → IsManifoldStrictlyPlurisubharmonicAt E f x

/-- A regular level of a Stein function is a J-convex level. -/
theorem IsSteinFunction.isJConvexLevel {φ : M → ℝ} (hφ : IsSteinFunction E φ) {c : ℝ}
    (hc : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) φ c) : IsJConvexLevel E φ c :=
  ⟨hc, fun x _ ↦ hφ.isStrictlyPlurisubharmonic x⟩

/-- **The spheres of a complex inner product space are J-convex levels** of the squared norm. -/
theorem isJConvexLevel_norm_sq {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] {c : ℝ} (hc : 0 < c) :
    IsJConvexLevel V (fun z : V ↦ ‖z‖ ^ 2) c := by
  refine isSteinFunction_norm_sq.isJConvexLevel <| isRegularValue_iff.2 fun z hz ↦
    isRegularPoint_iff_mvfderiv_ne_zero.2 fun h0 ↦ ?_
  have h := congrArg (fun L ↦ L z) h0
  erw [mvfderiv_eq_fderiv_apply] at h
  let : InnerProductSpace ℝ V := InnerProductSpace.rclikeToReal ℂ V
  simp only [fderiv_norm_sq_apply, smul_apply, innerSL_apply_apply, real_inner_self_eq_norm_sq,
    hz] at h
  have h' : 2 • c = 0 := h
  simp only [smul_eq_zero, OfNat.ofNat_ne_zero, false_or] at h'
  exact hc.ne' h'

/-! ### The Levi form of a level -/

/-- **The Levi form of a level depends on the defining function only up to a factor.** Let `f`
vanish at `x`, and let `g = a f` near `x`, for `f` and `a` of class `C²` at `x`. On vectors `v`,
`w` tangent to the complex tangencies of `{f = 0}` at `x`, that is with
`df(v) = df(i v) = df(w) = df(i w) = 0`, the Levi form of `g` at `x` is `a x` times that of
`f`. -/
theorem manifoldLeviForm_apply_of_eventuallyEq_mul {f g a : M → ℝ} {x : M}
    (hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 f x) (ha : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 a x)
    (hfx : f x = 0) (hg : g =ᶠ[𝓝 x] a * f) {v w : E}
    (hv : mvfderiv 𝓘(ℝ, E) f x v = 0) (hIv : mvfderiv 𝓘(ℝ, E) f x (Complex.I • v) = 0)
    (hw : mvfderiv 𝓘(ℝ, E) f x w = 0) (hIw : mvfderiv 𝓘(ℝ, E) f x (Complex.I • w) = 0) :
    manifoldLeviForm E g x v w = a x * manifoldLeviForm E f x v w := by
  have hdel {u : E} (hu : mvfderiv 𝓘(ℝ, E) f x u = 0)
      (hIu : mvfderiv 𝓘(ℝ, E) f x (Complex.I • u) = 0) :
      (StrongDual.extendRCLike (F := E) (mvfderiv 𝓘(ℝ, E) f x) : StrongDual ℂ E) u = 0 := by
    erw [StrongDual.extendRCLike_apply, hu, hIu]
    simp
  rw [manifoldLeviForm_congr_of_eventuallyEq hg, manifoldLeviForm_mul_apply ha hf v w, hfx,
    hdel hv hIv, hdel hw hIw]
  simp

/-! ### The contact structure of a J-convex level -/

variable [IsManifold 𝓘(ℂ, E) ∞ M]
  {F H S : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
  {I : ModelWithCorners ℝ F H} [TopologicalSpace S] [ChartedSpace H S]

/-- **The complex tangencies of a hypersurface in a level are the kernel of `λ_f`.** Let
`ι : S → M` be a smooth map, from a manifold of one dimension less, with image in the level
`f ⁻¹' {c}`, and let `s` be a point where the differential of `ι` is injective and `ι s` is a
regular point of `f`. A vector `v` at `s` lies in the kernel of
`ι^* λ_f`, for `λ_f = -df ∘ J`, iff `i dι(v)` lies in the image of `dι`. -/
theorem mem_kerDistribution_mpullback_covectorComplexStructure_iff [IsManifold I 2 S]
    {f : C^∞⟮𝓘(ℝ, E), M; ℝ⟯} {c : ℝ} [FiniteDimensional ℂ E] {ι : S → M}
    (hι : ContMDiff I 𝓘(ℝ, E) ∞ ι) (hιc : ∀ s, f (ι s) = c)
    (hdim : finrank ℝ F + 1 = finrank ℝ E) {s : S}
    (hιs : Function.Injective (mfderiv I 𝓘(ℝ, E) ι s))
    (hreg : IsRegularPoint 𝓘(ℝ, E) 𝓘(ℝ) f (ι s)) (v : TangentSpace I s) :
    v ∈ (SmoothForm.mpullback ι hι ((ofComplexManifold E M).covectorComplexStructure
        (mextDerivₗ 𝓘(ℝ, E) 0 (SmoothForm.ofFunction f)))).kerDistribution s ↔
      Complex.I • (show E from mfderiv I 𝓘(ℝ, E) ι s v) ∈
        (mfderiv I 𝓘(ℝ, E) ι s).range := by
  have hrange := hreg.range_mfderiv_eq_ker_mfderiv (Eventually.of_forall hιc) hιs
    (by simpa using hdim)
  have hv :
      (fun i ↦ mfderiv I 𝓘(ℝ, E) ι s (![v] i)) = ![mfderiv I 𝓘(ℝ, E) ι s v] := by
    ext i
    fin_cases i
    rfl
  rw [SmoothForm.mem_kerDistribution, SmoothForm.coe_mpullback, mpullback_apply, hrange,
    ← ker_mvfderiv, hv]
  erw [covectorComplexStructure_ofComplexManifold_mextDerivₗ_apply]
  exact neg_eq_zero.trans LinearMap.mem_ker.symm

/-- **A J-convex level carries a contact form.** Let `ι : S → M` be a smooth immersion of a
manifold of one dimension less, with image in a J-convex level `f ⁻¹' {c}`. Then the pullback
`ι^* λ_f` of `λ_f = -df ∘ J` is a contact form on `S`. -/
theorem IsJConvexLevel.isContactForm_mpullback [IsManifold I 2 S] [FiniteDimensional ℂ E]
    {f : C^∞⟮𝓘(ℝ, E), M; ℝ⟯} {c : ℝ} (hf : IsJConvexLevel E f c) {ι : S → M}
    (hι : ContMDiff I 𝓘(ℝ, E) ∞ ι) (hιc : ∀ s, f (ι s) = c)
    (hιs : ∀ s, Function.Injective (mfderiv I 𝓘(ℝ, E) ι s))
    (hdim : finrank ℝ F + 1 = finrank ℝ E) :
    (SmoothForm.mpullback ι hι ((ofComplexManifold E M).covectorComplexStructure
      (mextDerivₗ 𝓘(ℝ, E) 0 (SmoothForm.ofFunction f)))).IsContactForm := by
  have : FiniteDimensional ℝ E := .complexToReal E
  refine SmoothForm.isContactForm_iff_forall_isContactFormAt.2 fun s ↦ ?_
  rw [SmoothForm.coe_mpullback]
  set x := ι s
  have hpos := (isManifoldStrictlyPlurisubharmonicAt_iff_forall_pos f x).1
    (hf.isManifoldStrictlyPlurisubharmonicAt x (hιc s))
  have hαv (v : E) : _ = -mvfderiv 𝓘(ℝ, E) f x (Complex.I • v) :=
    covectorComplexStructure_ofComplexManifold_mextDerivₗ_apply f x v
  set α := (ofComplexManifold E M).covectorComplexStructure
    (mextDerivₗ 𝓘(ℝ, E) 0 (SmoothForm.ofFunction f))
  set σ := mextDerivₗ 𝓘(ℝ, E) 1 α with hσ_def
  -- `ω_f` is nondegenerate at `x`, since `ω_f(v, i v) > 0` for `v ≠ 0`.
  have hσ : ∀ v : TangentSpace 𝓘(ℝ, E) x, (∀ w, σ.val x ![v, w] = 0) → v = 0 := by
    intro v hv
    by_contra h0
    exact (hpos v h0).ne' (hv _)
  -- The vector `z` with `ι_z ω_f = λ_f` at `x`.
  obtain ⟨z, hz⟩ : ∃ z : E, ∀ v : E, σ.val x ![z, v] = α.val x ![v] := by
    have hnd : (σ.bilinFormAt x).Nondegenerate :=
      (SmoothForm.isAlt_bilinFormAt σ x).isRefl.nondegenerate_iff_separatingLeft.2
        fun v hv ↦ hσ v fun w ↦ (SmoothBundleForm.eval₂_apply _ x v w).symm.trans
          ((SmoothForm.bilinFormAt_apply σ x v w).symm.trans (hv w))
    obtain ⟨z, hz⟩ := (SmoothTwoForm.isInvertible_flat_iff.2 hnd).surjective
      (SmoothForm.degreeOneEquiv α x)
    exact ⟨z, fun v ↦ (SmoothBundleForm.eval₂_apply _ x z v).symm.trans
      ((SmoothTwoForm.flat_apply σ x z v).symm.trans ((congrArg (fun L ↦ L v) hz).trans
        (SmoothForm.degreeOneEquiv_apply_apply_vec α x v)))⟩
  refine isContactFormAt_mpullback hdim ((hι s).of_le (by simp)) (hιs s) hσ
    ((α.contMDiff x).of_le (by simp)) (by rw [hσ_def, mextDerivₗ_apply]) ?_ hz
  -- `z` is transverse: `df(z) = λ_f(i z) = ω_f(z, i z)`, which is positive unless `z = 0`, and
  -- `z ≠ 0` since `λ_f` does not vanish at `x`.
  intro hzr
  have hdz : mvfderiv 𝓘(ℝ, E) f x z = 0 := by
    have :=
      range_mfderiv_le_ker_mfderiv_of_eventually_eq (J := 𝓘(ℝ)) (Eventually.of_forall hιc) hzr
    rw [← ker_mvfderiv] at this
    exact this
  by_cases hz0 : z = 0
  · refine isRegularPoint_iff_mvfderiv_ne_zero.1 (hf.isRegularValue.isRegularPoint (hιc s))
      (ContinuousLinearMap.ext fun (v : E) ↦ ?_)
    have h1 := (hz (-(Complex.I • v))).trans (hαv (-(Complex.I • v)))
    have h0 : σ.val x ![z, -(Complex.I • v)] = 0 :=
      (σ.val x).map_coord_zero 0 hz0
    rw [h0, smul_neg, smul_smul, Complex.I_mul_I, neg_one_smul, _root_.neg_neg, eq_comm,
      neg_eq_zero] at h1
    exact h1
  · have h1 := (hpos z hz0).trans_eq ((hz (Complex.I • z)).trans (hαv _))
    rw [smul_smul, Complex.I_mul_I, neg_one_smul,
      show mvfderiv 𝓘(ℝ, E) f x (-z) = -mvfderiv 𝓘(ℝ, E) f x z from map_neg _ z,
      _root_.neg_neg] at h1
    exact h1.ne' hdz

end SymplecticGeometry

end
