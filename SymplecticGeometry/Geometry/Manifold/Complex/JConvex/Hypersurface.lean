/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.Plurisubharmonic
public import TauCeti.Geometry.Symplectic.Liouville.ContactType
import SymplecticGeometry.Geometry.Manifold.RegularValue.DefiningFunction
import SymplecticGeometry.Geometry.Symplectic.Manifold.Flat
import TauCeti.Geometry.Manifold.RegularValue.NormSq
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Dolbeault.Potential

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
  immersion that maps a neighbourhood of `s` into a level of `f`, with `ι s` a regular point,
  the kernel of `ι^* λ_f` at `s` consists of the vectors `v` whose image `dι(v)` stays tangent
  after multiplication by `i`: the complex tangencies of the hypersurface. The tangent image of
  `ι` is the kernel of `df`, by Tau Ceti's
  `TauCeti.IsRegularPoint.range_mfderiv_eq_ker_mfderiv`.

On the complex tangencies `ker ∂f` of `{f = 0}` at a point `x` with `f x = 0`, the Levi form of
`a * f` is `a x` times that of `f`
(`SymplecticGeometry.manifoldLeviForm_apply_of_eventuallyEq_mul`), by Tau Ceti's pointwise
product rule `TauCeti.manifoldLeviForm_mul_apply`. Hence the Levi form on these tangencies does
not depend on the defining function, up to a positive factor: if `g` is `C³` and vanishes near
`x` where `f` does, `f` is `C³` with `df_x ≠ 0`, and `dg_x = c • df_x`, then the Levi form of `g`
there is `c` times that of `f` (`SymplecticGeometry.manifoldLeviForm_apply_of_mvfderiv_eq_smul`),
since `g = a * f` near `x` with `a x = c`, by
`ContMDiffAt.exists_contMDiffAt_eventuallyEq_mul_of_mvfderiv_eq_smul`. For `c > 0`, the Levi form
of `f` is positive on the complex tangencies of `{f = 0}` at `x` iff that of `g` is positive on
those of `{g = 0}` (`SymplecticGeometry.forall_re_manifoldLeviForm_pos_iff_of_mvfderiv_eq_smul`).

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
  let : InnerProductSpace ℝ V := InnerProductSpace.rclikeToReal ℂ V
  exact isSteinFunction_norm_sq.isJConvexLevel (isRegularValue_norm_sq hc.ne')

/-! ### The Levi form of a level -/

/-- **The Levi form of a multiple of `f` on the complex tangencies of `{f = 0}`.** Let `f` vanish
at `x`, and let `g` agree with `a * f` near `x`, for `f` and `a` of class `C²` at `x`. On vectors
`v`, `w` in the complex tangent space of `{f = 0}` at `x`, that is with
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
    -- `erw`: Tau Ceti's `manifoldLeviForm_mul_apply` applies `StrongDual.extendRCLike` to
    -- `mvfderiv`, a covector on `TangentSpace 𝓘(ℝ, E) x` rather than on `E`, and the lemma
    -- writes `RCLike.I` for `Complex.I`; both match only up to unfolding, and `rw` and `simp`
    -- fail on that term.
    erw [StrongDual.extendRCLike_apply, hu, hIu]
    simp
  rw [manifoldLeviForm_congr_of_eventuallyEq hg, manifoldLeviForm_mul_apply ha hf v w, hfx,
    hdel hv hIv, hdel hw hIw]
  simp

/-- **The Levi form of a level does not depend on the defining function.** Let `f` and `g` be
`C³` at `x`, with `f x = 0`, `df_x ≠ 0`, `dg_x = c • df_x`, and `g = 0` near `x` wherever
`f = 0`. On vectors `v`, `w` in the complex tangent space of `{f = 0}` at `x`, that is with
`df(v) = df(i v) = df(w) = df(i w) = 0`, the Levi form of `g` at `x` is `c` times that of `f`. -/
theorem manifoldLeviForm_apply_of_mvfderiv_eq_smul [CompleteSpace E] {f g : M → ℝ} {x : M}
    (hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 3 f x) (hg : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 3 g x)
    (hfx : f x = 0) (hf' : mvfderiv 𝓘(ℝ, E) f x ≠ 0) {c : ℝ}
    (hgf : mvfderiv 𝓘(ℝ, E) g x = c • mvfderiv 𝓘(ℝ, E) f x)
    (hfg : ∀ᶠ y in 𝓝 x, f y = 0 → g y = 0) {v w : E}
    (hv : mvfderiv 𝓘(ℝ, E) f x v = 0) (hIv : mvfderiv 𝓘(ℝ, E) f x (Complex.I • v) = 0)
    (hw : mvfderiv 𝓘(ℝ, E) f x w = 0) (hIw : mvfderiv 𝓘(ℝ, E) f x (Complex.I • w) = 0) :
    manifoldLeviForm E g x v w = c * manifoldLeviForm E f x v w := by
  obtain ⟨a, ha, hga, hax⟩ :=
    hf.exists_contMDiffAt_eventuallyEq_mul_of_mvfderiv_eq_smul (n := 2) hg hfx hf' hgf hfg
  rw [manifoldLeviForm_apply_of_eventuallyEq_mul (hf.of_le (by norm_num)) ha hfx hga hv hIv hw
    hIw, hax]

/-- **Positivity of the Levi form on the complex tangencies of a level does not depend on the
defining function.** Let `f` and `g` be `C³` at `x`, with `f x = 0`, `df_x ≠ 0`,
`dg_x = c • df_x` for some `c > 0`, and `g = 0` near `x` wherever `f = 0`. Then the Levi form of
`g` at `x` has positive real part on the nonzero vectors `v` with `dg(v) = dg(i v) = 0` iff the
Levi form of `f` has positive real part on the nonzero vectors `v` with `df(v) = df(i v) = 0`. -/
theorem forall_re_manifoldLeviForm_pos_iff_of_mvfderiv_eq_smul [CompleteSpace E] {f g : M → ℝ}
    {x : M} (hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 3 f x) (hg : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 3 g x)
    (hfx : f x = 0) (hf' : mvfderiv 𝓘(ℝ, E) f x ≠ 0) {c : ℝ} (hc : 0 < c)
    (hgf : mvfderiv 𝓘(ℝ, E) g x = c • mvfderiv 𝓘(ℝ, E) f x)
    (hfg : ∀ᶠ y in 𝓝 x, f y = 0 → g y = 0) :
    (∀ v : E, mvfderiv 𝓘(ℝ, E) g x v = 0 → mvfderiv 𝓘(ℝ, E) g x (Complex.I • v) = 0 →
        v ≠ 0 → 0 < (manifoldLeviForm E g x v v).re) ↔
      ∀ v : E, mvfderiv 𝓘(ℝ, E) f x v = 0 → mvfderiv 𝓘(ℝ, E) f x (Complex.I • v) = 0 →
        v ≠ 0 → 0 < (manifoldLeviForm E f x v v).re := by
  have hdg (u : TangentSpace 𝓘(ℝ, E) x) :
      mvfderiv 𝓘(ℝ, E) g x u = 0 ↔ mvfderiv 𝓘(ℝ, E) f x u = 0 := by
    rw [hgf, smul_apply, smul_eq_zero, or_iff_right hc.ne']
  refine forall_congr' fun v ↦ ?_
  refine imp_congr_ctx (hdg v) fun hv ↦ imp_congr_ctx (hdg _) fun hIv ↦ imp_congr_right fun _ ↦ ?_
  rw [manifoldLeviForm_apply_of_mvfderiv_eq_smul hf hg hfx hf' hgf hfg hv hIv hv hIv,
    Complex.re_ofReal_mul, mul_pos_iff_of_pos_left hc]

/-! ### The contact structure of a J-convex level -/

variable [IsManifold 𝓘(ℂ, E) ∞ M]
  {F H S : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
  {I : ModelWithCorners ℝ F H} [TopologicalSpace S] [ChartedSpace H S]

/-- **The complex tangencies of a hypersurface in a level are the kernel of `λ_f`.** Let
`ι : S → M` be a smooth map from a manifold of one dimension less, and `s` a point such that
`ι` maps a neighbourhood of `s` into the level `f ⁻¹' {c}`, the differential of `ι` at `s` is
injective, and `ι s` is a regular point of `f`. A vector `v` at `s` lies in the kernel of
`ι^* λ_f`, for `λ_f = -df ∘ J`, iff `i dι(v)` lies in the image of `dι`. -/
theorem mem_kerDistribution_mpullback_covectorComplexStructure_iff [IsManifold I 2 S]
    {f : C^∞⟮𝓘(ℝ, E), M; ℝ⟯} {c : ℝ} [FiniteDimensional ℂ E] {ι : S → M}
    (hι : ContMDiff I 𝓘(ℝ, E) ∞ ι) (hdim : finrank ℝ F + 1 = finrank ℝ E) {s : S}
    (hιc : ∀ᶠ s' in 𝓝 s, f (ι s') = c) (hιs : Function.Injective (mfderiv I 𝓘(ℝ, E) ι s))
    (hreg : IsRegularPoint 𝓘(ℝ, E) 𝓘(ℝ) f (ι s)) (v : TangentSpace I s) :
    v ∈ (SmoothForm.mpullback ι hι ((ofComplexManifold E M).covectorComplexStructure
        (mextDerivₗ 𝓘(ℝ, E) 0 (SmoothForm.ofFunction f)))).kerDistribution s ↔
      Complex.I • (show E from mfderiv I 𝓘(ℝ, E) ι s v) ∈
        (mfderiv I 𝓘(ℝ, E) ι s).range := by
  have hrange := hreg.range_mfderiv_eq_ker_mfderiv hιc hιs (by simpa using hdim)
  rw [SmoothForm.mem_kerDistribution, SmoothForm.mpullback_apply_one, hrange, ← ker_mvfderiv,
    covectorComplexStructure_ofComplexManifold_mextDerivₗ_apply]
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
  obtain ⟨z, hz⟩ : ∃ z : E, ∀ v : E, σ.val x ![z, v] = α.val x ![v] :=
    (SmoothTwoForm.exists_forall_val_apply_eq σ hσ (SmoothForm.degreeOneEquiv α x)).imp
      fun z hz v ↦ (hz v).trans (SmoothForm.degreeOneEquiv_apply_apply_vec α x v)
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
