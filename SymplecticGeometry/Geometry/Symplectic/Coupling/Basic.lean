/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Icc
public import SymplecticGeometry.Geometry.Manifold.FiberBundle.Principal.CircleConnection
public import SymplecticGeometry.Geometry.Manifold.GroupAction.Circle
public import TauCeti.Geometry.Manifold.DifferentialForm.Closed
public import TauCeti.Geometry.Manifold.DifferentialForm.Interior
public import TauCeti.Geometry.Manifold.TwoForm.Basic
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
import Mathlib.Tactic.Module
import SymplecticGeometry.LinearAlgebra.BilinearForm.Nondegenerate
import TauCeti.Geometry.Manifold.MFDeriv.Prod

/-!
# Coupling forms

Let `P` be a smooth principal `Circle`-bundle over `B`, with charted total space
`TauCeti.ManifoldTotalSpace Circle P` and projection `π`, and let `a < b`. A **coupling form**
for a family `τ : Set.Icc a b → SmoothTwoForm IB B` of two-forms on the base is a closed two-form
`σ` on `ManifoldTotalSpace Circle P × Set.Icc a b` which

* is invariant under the circle action `(p, t) ↦ (p • z, t)`;
* has the coordinate `t ↦ t` of the interval as Hamiltonian for the period-one circle action, in
  the sign `ι_{(X, 0)} σ = -dt`, where `X` is the fundamental vector field of the period-one
  action. This is the library's sign `ι_{X_H} ω = -dH` (`DESIGN.md`, *The Hamiltonian sign*).
  McDuff–Salamon use the opposite sign (Remark 3.1.6), so in their convention the Hamiltonian
  of a coupling form is `-t`;
* has slice `π^* (τ t)` at each level `t`: its pull-back along `p ↦ (p, t)` is the pull-back of
  `τ t` along `π`.

These are the forms of McDuff–Salamon, Proposition 5.1.9. There, a compact band `H⁻¹([a, b])` of
a Hamiltonian circle action that is free on it is identified with `P × [a, b]`, the levels of `H`
becoming the slices `t = const`, and the reduced form at level `t` becoming `τ t` on `B`.

## Main definitions

* `SymplecticGeometry.couplingField IB P a b`: the field `(X, 0)` on the product, where
  `X = rightFundamentalVectorField (IB.prod (𝓡 1)) circlePeriodOneGenerator` is the fundamental
  vector field of the period-one circle action.
* `SymplecticGeometry.IsCouplingForm σ τ`: `σ` is a coupling form for `τ`.

## Main results

* `SymplecticGeometry.IsCouplingForm.apply_couplingField`: pointwise, `σ((X, 0), v) = -dt(v)`.
* `SymplecticGeometry.IsCouplingForm.isClosed_apply`: each `τ t` is closed, since its pull-back
  along the submersion `π` is the closed slice of `σ`; so it has a de Rham class.
* `SymplecticGeometry.IsCouplingForm.lineMap`: coupling forms for the same `τ` form an affine
  space: `σ₀ + s • (σ₁ - σ₀)` is one for every real `s`.
* `SymplecticGeometry.IsCouplingForm.eval₂_inl_inl`: on vectors tangent to a slice, `σ` is the
  pull-back of `τ t`.
* `SymplecticGeometry.IsCouplingForm.isNondegenerate` and `isSymplectic`: a coupling form for a
  family of nondegenerate forms is nondegenerate, hence symplectic, at every point of
  `P × [a, b]`, the boundary included.

## Implementation notes

The product is taken in the order `P × [a, b]`, total space first, as in McDuff–Salamon: the
Hamiltonian is then the second coordinate `x.2`, and the slice at `t` is `p ↦ (p, t)`. The
constructions on families of forms over a parameter manifold (`TauCeti.verticalForm`,
`SymplecticGeometry.moserField`, `TauCeti.SmoothForm.timeExtend`,
`SymplecticGeometry.IsSmoothFamily.exists_extend`) put the parameter first,
on `N × M`; results stated in that order are reached from this one through `Prod.swap`.
The interval `Set.Icc a b` carries Mathlib's structure of a manifold with boundary, modelled on
`𝓡∂ 1`, and its tangent spaces are all of `EuclideanSpace ℝ (Fin 1)`, endpoints included.

The circle of McDuff–Salamon has period one, so its generator is
`SymplecticGeometry.circlePeriodOneGenerator`, that is `2π • circleLieGenerator`. The connection
forms of this library (`SymplecticGeometry.IsCircleConnectionForm`) are normalized on
`circleLieGenerator` instead, so a connection form that takes the value `1` on `X` is `(2π)⁻¹`
times one of them; part 39 of `DESIGN.md` records this choice.

The Hamiltonian condition is written out with `TauCeti.RoughForm.interior` rather than with Tau
Ceti's moment maps, which are stated for left actions, while the action here is the right action
of a principal bundle.

Nondegeneracy is proved at each point `(p, t)` with
`LinearMap.BilinForm.IsRefl.nondegenerate_of_ker_restrict_eq_span_singleton`. The hyperplane is
the `σ`-orthogonal of `(X, 0)`, which is the kernel of `dt` by the Hamiltonian identity. On it `σ`
is `π^* (τ t)`, whose radical is the vertical line spanned by `X`
(`SymplecticGeometry.exists_eq_smul_rightFundamentalVectorField_of_mfderiv_proj_eq_zero`), and
`σ((X, 0), ∂_t) = -1`. Since the tangent spaces of `Set.Icc a b` are the whole model space at the
endpoints too, the argument is the same on the boundary.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Proposition 5.1.9 (coupling forms) and §2.7 (connection forms of circle bundles).
-/

public section

noncomputable section

open Bundle Manifold MulOpposite TauCeti
open scoped Manifold ContDiff

namespace SymplecticGeometry

variable {EB HB B : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  {P : B → Type*} [TopologicalSpace (TotalSpace Circle P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle Circle P] [∀ b, MulAction Circleᵐᵒᵖ (P b)]
  {a b : ℝ} [Fact (a < b)]

/-! ### The fundamental vector field on the product -/

variable (IB P a b) in
/-- The vector field `(X, 0)` on `P × [a, b]`, where
`X = rightFundamentalVectorField (IB.prod (𝓡 1)) circlePeriodOneGenerator` is the fundamental
vector field of the circle action of period one on the total space of `P`. -/
def couplingField (x : ManifoldTotalSpace Circle P × Set.Icc a b) :
    TangentSpace ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) x :=
  (rightFundamentalVectorField (IB.prod (𝓡 1)) circlePeriodOneGenerator x.1,
    (0 : EuclideanSpace ℝ (Fin 1)))

theorem couplingField_def (x : ManifoldTotalSpace Circle P × Set.Icc a b) :
    couplingField IB P a b x =
      (rightFundamentalVectorField (IB.prod (𝓡 1)) circlePeriodOneGenerator x.1,
        (0 : EuclideanSpace ℝ (Fin 1))) :=
  (rfl)

/-- The first component of `couplingField` is the period-one fundamental vector field. -/
@[simp]
theorem couplingField_fst (x : ManifoldTotalSpace Circle P × Set.Icc a b) :
    (couplingField IB P a b x).1 =
      rightFundamentalVectorField (IB.prod (𝓡 1)) circlePeriodOneGenerator x.1 :=
  (rfl)

/-- The component of `couplingField` along the interval vanishes. -/
@[simp]
theorem couplingField_snd (x : ManifoldTotalSpace Circle P × Set.Icc a b) :
    (couplingField IB P a b x).2 = 0 :=
  (rfl)

/-! ### Coupling forms -/

variable [IsManifold IB ∞ B] [PrincipalBundle Circle P] [ContMDiffFiberBundle ∞ Circle P IB (𝓡 1)]

/-- A **coupling form** for a family `τ` of two-forms on `B`, indexed by `t ∈ [a, b]`: a closed
two-form `σ` on `P × [a, b]` that is invariant under the circle action on the first factor, whose
contraction with the period-one fundamental field `(X, 0)` is `-dt`, the differential of minus the
coordinate of the interval, and whose slice at each `t` is the pull-back of `τ t` along the
projection of `P`. The sign `ι_{(X, 0)} σ = -dt` is the library's Hamiltonian sign
`ι_{X_H} ω = -dH`. -/
structure IsCouplingForm
    (σ : SmoothTwoForm ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) (ManifoldTotalSpace Circle P × Set.Icc a b))
    (τ : Set.Icc a b → SmoothTwoForm IB B) : Prop where
  /-- A coupling form is closed. -/
  isClosed : σ.IsClosed
  /-- A coupling form is invariant under the circle action on the total space. -/
  mpullback_smul (z : Circle) :
    SmoothForm.mpullback (fun x : ManifoldTotalSpace Circle P × Set.Icc a b ↦ (op z • x.1, x.2))
      (((contMDiff_const_smul (op z)).comp contMDiff_fst).prodMk contMDiff_snd) σ = σ
  /-- The contraction of a coupling form with `(X, 0)` is `-dt`. -/
  interior_eq : RoughForm.interior (couplingField IB P a b) σ.val =
    -mextDeriv (RoughForm.ofFunction ((IB.prod (𝓡 1)).prod (𝓡∂ 1))
      fun x : ManifoldTotalSpace Circle P × Set.Icc a b ↦ (x.2 : ℝ))
  /-- The slice of a coupling form at `t` is the pull-back of `τ t` along the projection. -/
  mpullback_slice (t : Set.Icc a b) :
    SmoothForm.mpullback (fun p : ManifoldTotalSpace Circle P ↦ (p, t))
      (contMDiff_id.prodMk contMDiff_const) σ =
    SmoothForm.mpullback (fun y : ManifoldTotalSpace Circle P ↦
        ((ManifoldTotalSpace.homeomorph Circle P).symm y).proj)
      (ManifoldTotalSpace.contMDiff_proj ∞ Circle P IB (𝓡 1)) (τ t)

namespace IsCouplingForm

variable {σ σ₀ σ₁ :
    SmoothTwoForm ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) (ManifoldTotalSpace Circle P × Set.Icc a b)}
  {τ : Set.Icc a b → SmoothTwoForm IB B}

/-- The Hamiltonian identity of a coupling form at a point: `σ((X, 0), v) = -dt(v)`. -/
theorem apply_couplingField (h : IsCouplingForm σ τ)
    (x : ManifoldTotalSpace Circle P × Set.Icc a b)
    (v : TangentSpace ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) x) :
    σ.val x ![couplingField IB P a b x, v] =
      -mfderiv ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) 𝓘(ℝ)
        (fun y : ManifoldTotalSpace Circle P × Set.Icc a b ↦ (y.2 : ℝ)) x v := by
  have := congrArg (fun β ↦ β x ![v]) h.interior_eq
  simp only [RoughForm.interior_apply, Pi.neg_apply, ContinuousAlternatingMap.neg_apply,
    mextDeriv_ofFunction_apply] at this
  -- `this` states the same equation in the fibre `Bundle.Trivial _ ℝ x`, which is `ℝ`.
  exact this

/-- Each form `τ t` of a coupling form is closed: its pull-back along the projection is the slice
of the closed form `σ` at `t`, and pull-back along the submersion `π` detects closedness. -/
theorem isClosed_apply (h : IsCouplingForm σ τ) (t : Set.Icc a b) : (τ t).IsClosed := by
  rw [← (ManifoldTotalSpace.isSubmersion_proj ∞ Circle P IB (𝓡 1)).isClosed_mpullback_iff
    ((FiberBundle.surjective_proj Circle P).comp
      (ManifoldTotalSpace.homeomorph Circle P).symm.surjective),
    ← h.mpullback_slice t]
  exact h.isClosed.mpullback _ _

/-- **Coupling forms are an affine space.** For two coupling forms `σ₀` and `σ₁` for the same
family `τ` and every real `s`, the form `σ₀ + s • (σ₁ - σ₀)` is a coupling form for `τ`. -/
theorem lineMap (h₀ : IsCouplingForm σ₀ τ) (h₁ : IsCouplingForm σ₁ τ) (s : ℝ) :
    IsCouplingForm (σ₀ + s • (σ₁ - σ₀)) τ where
  isClosed := h₀.isClosed.add ((h₁.isClosed.sub h₀.isClosed).smul s)
  mpullback_smul z := by
    rw [map_add, map_smul, map_sub, h₀.mpullback_smul, h₁.mpullback_smul]
  interior_eq := by
    have e : σ₀ + s • (σ₁ - σ₀) = (1 - s) • σ₀ + s • σ₁ := by module
    rw [e]
    simp [h₀.interior_eq, h₁.interior_eq]
    module
  mpullback_slice t := by
    rw [map_add, map_smul, map_sub, h₀.mpullback_slice, h₁.mpullback_slice, sub_self, smul_zero,
      add_zero]

/-- On vectors tangent to the slice at `t`, a coupling form is the pull-back of `τ t` along the
projection: `σ((v, 0), (w, 0)) = τ t (dπ v, dπ w)`. -/
theorem eval₂_inl_inl (h : IsCouplingForm σ τ) (p : ManifoldTotalSpace Circle P)
    (t : Set.Icc a b) (v w : TangentSpace (IB.prod (𝓡 1)) p) :
    SmoothBundleForm.eval₂ σ (p, t)
        ((v, 0) : TangentSpace ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) (p, t)) (w, 0) =
      SmoothBundleForm.eval₂ (τ t) ((ManifoldTotalSpace.homeomorph Circle P).symm p).proj
        (mfderiv (IB.prod (𝓡 1)) IB (fun y : ManifoldTotalSpace Circle P ↦
          ((ManifoldTotalSpace.homeomorph Circle P).symm y).proj) p v)
        (mfderiv (IB.prod (𝓡 1)) IB (fun y : ManifoldTotalSpace Circle P ↦
          ((ManifoldTotalSpace.homeomorph Circle P).symm y).proj) p w) := by
  have := congrArg (fun φ ↦ SmoothBundleForm.eval₂ φ p v w) (h.mpullback_slice t)
  simp only [SmoothForm.eval₂_mpullback, mfderiv_prod_left] at this
  -- `ContinuousLinearMap.inl _ _ _ v` is `(v, 0)`, and `(p, t).1` is `p`, by definition
  exact this

/-- The Hamiltonian identity of a coupling form in terms of the second component:
`σ((X, 0), v) = -v₂`, where `v₂` is the component of `v` along the interval, read in `ℝ` through
the inclusion `[a, b] → ℝ`. -/
theorem apply_couplingField_eq_neg_mfderiv_snd (h : IsCouplingForm σ τ)
    (x : ManifoldTotalSpace Circle P × Set.Icc a b)
    (v : TangentSpace ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) x) :
    σ.val x ![couplingField IB P a b x, v] =
      -mfderiv (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : Set.Icc a b → ℝ) x.2 v.2 := by
  rw [h.apply_couplingField]
  -- `fun y ↦ (y.2 : ℝ)` is `Subtype.val ∘ Prod.snd` by definition of composition
  exact congrArg (fun c ↦ -c) (DFunLike.congr_fun
    (mfderiv_comp_snd (I := IB.prod (𝓡 1)) (I'' := 𝓘(ℝ)) Subtype.val x) v)

/-- At a point `(p, t)`, the radical of a coupling form over a nondegenerate `τ t`, restricted to
the `σ`-orthogonal of `(X, 0)` (the kernel of `dt`), is the line spanned by `(X, 0)`. -/
private theorem ker_restrict_eq_span_couplingField (h : IsCouplingForm σ τ) {t : Set.Icc a b}
    (hτ : (τ t).IsNondegenerate) (p : ManifoldTotalSpace Circle P) :
    LinearMap.ker ((σ.bilinFormAt (p, t)).restrict
      (LinearMap.ker (σ.bilinFormAt (p, t) (couplingField IB P a b (p, t))))) =
      ℝ ∙ ⟨couplingField IB P a b (p, t),
        LinearMap.mem_ker.mpr (SmoothForm.isAlt_bilinFormAt σ (p, t) _)⟩ := by
  ext ⟨w, hw⟩
  rw [LinearMap.mem_ker, Submodule.mem_span_singleton]
  constructor
  · intro hk
    -- `w` has no component along the interval, since the inclusion `[a, b] → ℝ` has injective
    -- derivative
    have hw0 : w.2 = 0 := by
      have hw' := LinearMap.mem_ker.mp hw
      rw [SmoothForm.bilinFormAt_apply, SmoothBundleForm.eval₂_apply,
        h.apply_couplingField_eq_neg_mfderiv_snd] at hw'
      exact (isImmersionOfComplement_subtypeVal_Icc (n := 1)).mfderiv_injective one_ne_zero _
        (((neg_eq_zero (α := ℝ)).mp hw').trans (map_zero _).symm)
    have hwe : ((w.1, 0) : TangentSpace ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) (p, t)) = w :=
      Prod.ext rfl hw0.symm
    have hd : mfderiv (IB.prod (𝓡 1)) IB (fun y : ManifoldTotalSpace Circle P ↦
        ((ManifoldTotalSpace.homeomorph Circle P).symm y).proj) p w.1 = 0 := by
      refine (SmoothTwoForm.isNondegenerate_iff_separatingLeft.mp hτ) _ _ fun z ↦ ?_
      obtain ⟨u, rfl⟩ :=
        (ManifoldTotalSpace.isSubmersion_proj ∞ Circle P IB (𝓡 1)).surjective_mfderiv (by simp) p z
      let u₀ : TangentSpace ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) (p, t) := (u, 0)
      have hu0 : u₀ ∈ LinearMap.ker (σ.bilinFormAt (p, t) (couplingField IB P a b (p, t))) := by
        refine LinearMap.mem_ker.mpr ?_
        rw [SmoothForm.bilinFormAt_apply, SmoothBundleForm.eval₂_apply,
          h.apply_couplingField_eq_neg_mfderiv_snd]
        -- the second component of `u₀` is `0`, by definition of the product tangent space
        exact neg_eq_zero.mpr (map_zero _)
      refine (h.eval₂_inl_inl p t w.1 u).symm.trans ?_
      rw [hwe]
      exact (SmoothForm.bilinFormAt_apply σ (p, t) w _).symm.trans
        (LinearMap.congr_fun hk ⟨u₀, hu0⟩)
    obtain ⟨c, hc⟩ := exists_eq_smul_rightFundamentalVectorField_of_mfderiv_proj_eq_zero
      circlePeriodOneGenerator_ne_zero hd
    refine ⟨c, Subtype.ext ?_⟩
    refine Eq.trans ?_ hwe
    simp only [Submodule.coe_smul]
    rw [hc, couplingField_def]
    -- the tangent space of the product is the product of the tangent spaces, by definition
    exact Prod.ext rfl (smul_zero _)
  · rintro ⟨c, hc⟩
    refine LinearMap.ext fun u ↦ ?_
    simp only [← hc, LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply,
      map_smul, LinearMap.smul_apply, LinearMap.mem_ker.mp u.property, smul_zero,
      LinearMap.zero_apply]

/-- **Coupling forms over nondegenerate forms are nondegenerate.** If every `τ t` is
nondegenerate, then so is a coupling form for `τ`, at every point of `P × [a, b]`, the two
boundary levels included. -/
theorem isNondegenerate (h : IsCouplingForm σ τ) (hτ : ∀ t, (τ t).IsNondegenerate) :
    σ.IsNondegenerate := by
  refine SmoothTwoForm.isNondegenerate_iff_forall_ker_bilinFormAt_eq_bot.mpr fun ⟨p, t⟩ ↦
    LinearMap.BilinForm.Nondegenerate.ker_eq_bot ?_
  -- `ℓ = σ((X, 0), ·)`, which is `-dt`
  set ℓ := σ.bilinFormAt (p, t) (couplingField IB P a b (p, t))
  -- the vector `∂_t`, on which `ℓ` is `-1`
  let e : TangentSpace ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) (p, t) :=
    LinearMap.inr ℝ (TangentSpace (IB.prod (𝓡 1)) p) (TangentSpace (𝓡∂ 1) t) 1
  have he : ℓ e = -1 := by
    rw [SmoothForm.bilinFormAt_apply, SmoothBundleForm.eval₂_apply,
      h.apply_couplingField_eq_neg_mfderiv_snd]
    -- the second component of `e` is `1`, and the value lies in `Bundle.Trivial _ ℝ (p, t)`,
    -- which is `ℝ`
    exact congrArg (fun c ↦ -c) (mfderiv_subtypeVal_Icc_one t)
  have hℓe : ℓ e ≠ 0 := by rw [he]; exact neg_ne_zero.mpr one_ne_zero
  refine LinearMap.BilinForm.IsRefl.nondegenerate_of_ker_restrict_eq_span_singleton
    (SmoothForm.isAlt_bilinFormAt σ (p, t)).isRefl
    (h.ker_restrict_eq_span_couplingField (hτ t) p) (e := e) ?_ hℓe
  rw [sup_comm]
  exact LinearMap.span_singleton_sup_ker_eq_top ℓ hℓe

/-- **Coupling forms over nondegenerate forms are symplectic.** -/
theorem isSymplectic (h : IsCouplingForm σ τ) (hτ : ∀ t, (τ t).IsNondegenerate) :
    σ.IsSymplectic :=
  ⟨h.isClosed, h.isNondegenerate hτ⟩

end IsCouplingForm

end SymplecticGeometry

end
