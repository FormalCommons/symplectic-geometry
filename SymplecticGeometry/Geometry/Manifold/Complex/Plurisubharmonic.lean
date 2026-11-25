/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.DdbarForm.Basic
public import TauCeti.Geometry.Manifold.Complex.Pseudoconvex.Morse
public import TauCeti.Geometry.Manifold.Complex.SquaredDistance
public import TauCeti.Geometry.Symplectic.Manifold.Kahler
public import TauCeti.Topology.Maps.Proper.Metric
public import SymplecticGeometry.Analysis.Convex.Deriv
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Dolbeault.Potential

/-!
# Stein functions and their Kähler forms

Let `M` be a complex manifold modelled on `E`, seen as a real manifold, with the almost complex
structure `J = ofComplexManifold E M` (multiplication by `i` on each tangent space). For a smooth
real function `f`, write `ω_f = d(-df ∘ J)`, the real two-form
`mextDerivₗ 𝓘(ℝ, E) 1 (J.covectorComplexStructure (mextDerivₗ 𝓘(ℝ, E) 0 (ofFunction f)))`.
By `coe_mextDerivₗ_covectorComplexStructure_eq_two_smul_ddbarForm`, it is `2 i∂∂bar f`, so
`ω_f(v, J v)` is four times the real part of the Levi form of `f` on `v`.

A **Stein function** on `M` is a smooth, proper function, bounded below and strictly
plurisubharmonic at every point. Its form `ω_f` is a Kähler form for `J`, and hence symplectic.

## Main declarations

* `SymplecticGeometry.isManifoldStrictlyPlurisubharmonicAt_iff_forall_pos`: a smooth `f` is
  strictly plurisubharmonic at `x` iff `0 < ω_f(v, i v)` at `x` for every `v ≠ 0`.
* `SymplecticGeometry.IsSteinFunction E φ`: smooth, proper, bounded below and strictly
  plurisubharmonic everywhere.
* `SymplecticGeometry.IsSteinFunction.comp`: `h ∘ φ` is a Stein function for a smooth
  `h : ℝ → ℝ` with `h' > 0` and `h'' ≥ 0`.
* `SymplecticGeometry.IsSteinFunction.exists_isMorse`: a Stein function on a Hausdorff manifold
  is `C⁰`-close to a Stein Morse function, by Tau Ceti's
  `exists_isMorse_isProperMap_bddBelow_isManifoldStrictlyPlurisubharmonicAt`.
* `SymplecticGeometry.isSteinFunction_norm_sq`: `‖z‖²` on a finite-dimensional complex inner
  product space.
* `SymplecticGeometry.IsSteinFunction.isKahler`, `SymplecticGeometry.IsSteinFunction.isSymplectic`:
  `ω_f` of a Stein function is Kähler for `J`, and symplectic.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  Definitions 7.4.7 and 7.4.8.
* [K. Cieliebak, Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Chapter 2.
-/

public section

noncomputable section

open Set Filter Topology Module
open scoped Manifold ContDiff TauCeti.ComplexManifold

namespace SymplecticGeometry

open TauCeti TauCeti.SmoothAlmostComplexStructure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

/-! ### Positivity of `ω_f` -/

/-- The value of `ω_f = d(-df ∘ J)` at `x` on `(v, i v)` is `4 Re L_f(x)(v, v)`, where `L_f` is
the Levi form of `f`. -/
theorem mextDerivₗ_covectorComplexStructure_apply_I_smul (f : C^∞⟮𝓘(ℝ, E), M; ℝ⟯) (x : M)
    (v : E) :
    (mextDerivₗ 𝓘(ℝ, E) 1 ((ofComplexManifold E M).covectorComplexStructure
        (mextDerivₗ 𝓘(ℝ, E) 0 (SmoothForm.ofFunction f)))).val x ![v, Complex.I • v] =
      4 * (manifoldLeviForm E f x v v).re := by
  have hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 f x := f.contMDiff.contMDiffAt.of_le (by simp)
  have h := congrArg Complex.re (mk_ddbarForm_apply_eq_two_mul_manifoldLeviForm hf v v)
  rw [coe_mextDerivₗ_covectorComplexStructure_eq_two_smul_ddbarForm (u := f) _
    (fun y ↦ congrFun (SmoothForm.ofFunction_apply_zero f) y)]
  simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero] at h
  simp only [Pi.smul_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul, h]
  ring

/-- **Strict plurisubharmonicity is positivity of `ω_f`.** A smooth real function `f` on a complex
manifold is strictly plurisubharmonic at `x` iff `0 < ω_f(v, i v)` at `x` for every `v ≠ 0`,
where `ω_f = d(-df ∘ J)`. -/
theorem isManifoldStrictlyPlurisubharmonicAt_iff_forall_pos (f : C^∞⟮𝓘(ℝ, E), M; ℝ⟯) (x : M) :
    IsManifoldStrictlyPlurisubharmonicAt E f x ↔ ∀ v : E, v ≠ 0 →
      0 < (mextDerivₗ 𝓘(ℝ, E) 1 ((ofComplexManifold E M).covectorComplexStructure
        (mextDerivₗ 𝓘(ℝ, E) 0 (SmoothForm.ofFunction f)))).val x ![v, Complex.I • v] := by
  simp only [isManifoldStrictlyPlurisubharmonicAt_iff,
    mextDerivₗ_covectorComplexStructure_apply_I_smul]
  exact forall₂_congr fun _ _ ↦ by constructor <;> intro h <;> linarith

/-! ### Stein functions -/

variable (E) in
/-- A **Stein function** on a complex manifold `M` modelled on `E`: a smooth real function that is
proper, bounded below and strictly plurisubharmonic at every point. -/
structure IsSteinFunction (φ : M → ℝ) : Prop where
  /-- A Stein function is smooth on the underlying real manifold. -/
  contMDiff : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ φ
  /-- A Stein function is proper. -/
  isProperMap : IsProperMap φ
  /-- A Stein function is bounded below. -/
  bddBelow : BddBelow (range φ)
  /-- A Stein function is strictly plurisubharmonic at every point. -/
  isStrictlyPlurisubharmonic : ∀ x, IsManifoldStrictlyPlurisubharmonicAt E φ x

namespace IsSteinFunction

variable {φ : M → ℝ}

omit [IsManifold 𝓘(ℂ, E) ∞ M] in
/-- Composing a Stein function with a smooth `h : ℝ → ℝ` with `h' > 0` and `h'' ≥ 0` gives a
Stein function. -/
theorem comp (hφ : IsSteinFunction E φ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (hh₁ : ∀ t, 0 < deriv h t) (hh₂ : ∀ t, 0 ≤ iteratedDeriv 2 h t) :
    IsSteinFunction E (h ∘ φ) where
  contMDiff := hh.contMDiff.comp hφ.contMDiff
  isProperMap := by
    have hc : Continuous (h ∘ φ) := hh.continuous.comp hφ.contMDiff.continuous
    refine isProperMap_iff_isCompact_preimage.2 ⟨hc, fun K hK ↦ ?_⟩
    -- A convex `h` with `h' > 0` tends to `∞`, so `h ∘ φ ∈ K` bounds `φ` above.
    have hd : Differentiable ℝ h := hh.differentiable (by simp)
    have hconv : ConvexOn ℝ univ h := convexOn_univ_of_deriv2_nonneg hd
      ((hh.iterate_deriv 1).differentiable (by simp))
      fun t ↦ by simpa only [iteratedDeriv_eq_iterate] using hh₂ t
    have hh_tendsto := ConvexOn.tendsto_atTop_of_hasDerivWithinAt_Ioi_pos (x := 0)
      (hconv.subset (subset_univ _) (convex_Ici 0)) (hd 0).hasDerivAt.hasDerivWithinAt (hh₁ 0)
    obtain ⟨c, hc'⟩ := hK.bddAbove
    obtain ⟨b, hb⟩ := (hh_tendsto.eventually_gt_atTop c).exists_forall_of_atTop
    obtain ⟨m, hm⟩ := hφ.bddBelow
    have hsub : h ∘ φ ⁻¹' K ⊆ φ ⁻¹' Icc m b := fun x hx ↦
      ⟨hm ⟨x, rfl⟩, (not_le.1 fun hbx ↦ (hb _ hbx).not_ge (hc' hx)).le⟩
    exact (hφ.isProperMap.isCompact_preimage isCompact_Icc).of_isClosed_subset
      (hK.isClosed.preimage hc) hsub
  bddBelow := by
    obtain ⟨m, hm⟩ := hφ.bddBelow
    refine ⟨h m, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact (strictMono_of_deriv_pos hh₁).monotone (hm ⟨x, rfl⟩)
  isStrictlyPlurisubharmonic x :=
    (hφ.isStrictlyPlurisubharmonic x).scalar_comp (hh.contDiffAt.of_le (by simp))
      (hφ.contMDiff.contMDiffAt.of_le (by simp)) (hh₁ _) (hh₂ _)

/-- **Morse perturbation of a Stein function.** On a Hausdorff complex manifold, every Stein
function `φ` is within `C⁰` distance `1` of a Stein Morse function whose critical points have
real Morse index at most `dim_ℂ E`. -/
theorem exists_isMorse [FiniteDimensional ℂ E] [T2Space M] (hφ : IsSteinFunction E φ) :
    ∃ g : C^∞⟮𝓘(ℝ, E), M; ℝ⟯, IsMorse 𝓘(ℝ, E) g ∧ IsSteinFunction E g ∧
      (∀ x ∈ criticalPoints 𝓘(ℝ, E) g, manifoldMorseIndex 𝓘(ℝ, E) g x ≤ finrank ℂ E) ∧
      ∀ x, |g x - φ x| < 1 := by
  obtain ⟨g, hgm, hgp, hgb, hgs, hgi, hgφ⟩ :=
    exists_isMorse_isProperMap_bddBelow_isManifoldStrictlyPlurisubharmonicAt hφ.contMDiff
      hφ.isProperMap hφ.bddBelow hφ.isStrictlyPlurisubharmonic
  exact ⟨g, hgm, ⟨g.contMDiff, hgp, hgb, hgs⟩, hgi, hgφ⟩

/-! ### The Kähler form of a Stein function -/

variable [FiniteDimensional ℂ E]

/-- **The Kähler form of a Stein function.** For a Stein function `f`, the two-form
`ω_f = d(-df ∘ J)` is a Kähler form for the complex structure of `M`. -/
theorem isKahler {f : C^∞⟮𝓘(ℝ, E), M; ℝ⟯} (hf : IsSteinFunction E f) :
    SmoothTwoForm.IsKahler (mextDerivₗ 𝓘(ℝ, E) 1 ((ofComplexManifold E M).covectorComplexStructure
        (mextDerivₗ 𝓘(ℝ, E) 0 (SmoothForm.ofFunction f)))) (ofComplexManifold E M) := by
  have hω := coe_mextDerivₗ_covectorComplexStructure_eq_two_smul_ddbarForm (u := f)
    (SmoothForm.ofFunction f) fun y ↦ congrFun (SmoothForm.ofFunction_apply_zero f) y
  -- Each tangent space is `E`, on which the complex structure is multiplication by `I`.
  have hJ (x : M) (v : TangentSpace 𝓘(ℝ, E) x) :
      (ofComplexManifold E M).toEndomorphism x v = Complex.I • (show E from v) :=
    ofComplexManifold_apply (E := E) x v
  refine SmoothTwoForm.isKahler_ofComplexManifold_iff.2
    ⟨SmoothForm.isClosed_mextDerivₗ _, ⟨SmoothTwoForm.invariant_iff.2 fun x v w ↦ ?_,
      SmoothTwoForm.tames_iff.2 fun x v hv ↦ ?_⟩⟩
  · simp only [SmoothBundleForm.eval₂_apply]
    rw [hJ, hJ, hω]
    simpa using ddbarForm_apply_I_smul (E := E) f x v w
  · simp only [SmoothBundleForm.eval₂_apply]
    rw [hJ]
    exact (isManifoldStrictlyPlurisubharmonicAt_iff_forall_pos f x).1
      (hf.isStrictlyPlurisubharmonic x) v hv

/-- For a Stein function `f`, the two-form `ω_f = d(-df ∘ J)` is symplectic. -/
theorem isSymplectic {f : C^∞⟮𝓘(ℝ, E), M; ℝ⟯} (hf : IsSteinFunction E f) :
    SmoothTwoForm.IsSymplectic (mextDerivₗ 𝓘(ℝ, E) 1
      ((ofComplexManifold E M).covectorComplexStructure
        (mextDerivₗ 𝓘(ℝ, E) 0 (SmoothForm.ofFunction f)))) :=
  hf.isKahler.isSymplectic

end IsSteinFunction

/-- **The squared norm is a Stein function** on a finite-dimensional complex inner product
space. -/
theorem isSteinFunction_norm_sq {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] : IsSteinFunction V fun z : V ↦ ‖z‖ ^ 2 where
  contMDiff := by
    let : InnerProductSpace ℝ V := InnerProductSpace.rclikeToReal ℂ V
    exact (contDiff_norm_sq ℝ).contMDiff
  isProperMap := by simpa using isProperMap_norm_sq_sub (0 : V)
  bddBelow := ⟨0, by rintro _ ⟨z, rfl⟩; positivity⟩
  isStrictlyPlurisubharmonic z := by
    have h := (isManifoldStrictlyPlurisubharmonicAt_norm_sq_sub_comp_iff (E := V) (a := 0)
      (i := id) (x := z) contMDiffAt_id).2
      (by simpa using (NormedSpace.fromTangentSpace z).injective)
    simpa using h

end SymplecticGeometry

end
