/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Icc
public import SymplecticGeometry.Geometry.Manifold.FiberBundle.Principal.CircleConnection
public import SymplecticGeometry.Geometry.Manifold.DeRham.Basic
public import SymplecticGeometry.Geometry.Manifold.FiberBundle.Principal.RealChernClass
public import SymplecticGeometry.Geometry.Manifold.GroupAction.Circle
public import TauCeti.Geometry.Manifold.DifferentialForm.Closed
public import TauCeti.Geometry.Manifold.DifferentialForm.Interior
public import TauCeti.Geometry.Manifold.TwoForm.Basic
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
import Mathlib.Tactic.Module
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.HomotopyOperator
import SymplecticGeometry.Geometry.Manifold.Instances.Icc
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
* `SymplecticGeometry.IsCouplingForm.mk_sub_mk_eq_neg_smul_realFirstChernClass`: the de Rham
  classes of the forms `τ t` satisfy `[τ t] - [τ s] = -(t - s) c₁(P)`, where `c₁(P)` is the real
  first Chern class `SymplecticGeometry.realFirstChernClass`. This needs the base to be a
  finite-dimensional, boundaryless, Hausdorff, σ-compact manifold, where that class is defined.

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

The cohomological condition is proved with the homotopy operator
`TauCeti.SmoothForm.homotopyOperator`. Pull `σ` back along `Φ (p, u) = (p, s + u (t - s))`,
from `P × [0, 1]`; the homotopy formula makes `β = h (Φ^* σ)` a primitive of
`π^* (τ t - τ s)`, the difference of the end slices. The form `β` is invariant, by naturality of
the homotopy operator (`TauCeti.homotopyOperator_mpullback_prodMap_id_of_isSmoothForm`), and by
the Hamiltonian identity it takes the value `(2π)⁻¹ (t - s)` on the fundamental field of
`circleLieGenerator`. So for a connection form `α`, the form `β - (2π)⁻¹ (t - s) α` is the
pull-back `π^* γ` of a form on `B`
(`SymplecticGeometry.IsCircleConnectionForm.existsUnique_eq_add_mpullback`), and
`τ t - τ s = (2π)⁻¹ (t - s) F_α + d γ`, as pull-back along `π` is injective.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Proposition 5.1.9 (coupling forms and their cohomological condition) and §2.7 (connection forms
  of circle bundles).
* [R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §4 (the
  homotopy operator).
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
    obtain ⟨c, hc⟩ := exists_eq_smul_rightFundamentalVectorField_of_mfderiv_proj_eq_zero hd
    have hX : ((2 * Real.pi)⁻¹ * c) •
        rightFundamentalVectorField (IB.prod (𝓡 1)) circlePeriodOneGenerator p =
          c • rightFundamentalVectorField (IB.prod (𝓡 1)) circleLieGenerator p := by
      rw [circlePeriodOneGenerator_def, rightFundamentalVectorField_smul, Pi.smul_apply, smul_smul]
      congr 1
      field_simp
    refine ⟨(2 * Real.pi)⁻¹ * c, Subtype.ext ?_⟩
    refine Eq.trans ?_ hwe
    simp only [Submodule.coe_smul]
    rw [hc, couplingField_def]
    -- the tangent space of the product is the product of the tangent spaces, by definition
    exact Prod.ext hX (smul_zero _)
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

/-! ### The cohomological condition -/

section Cohomology

variable (P) in
/-- The map `(p, u) ↦ (p, s + u (t - s))` from `P × [0, 1]` to `P × [a, b]`. -/
private def segmentMap (s t : Set.Icc a b) :
    ManifoldTotalSpace Circle P × Set.Icc (0 : ℝ) 1 → ManifoldTotalSpace Circle P × Set.Icc a b :=
  Prod.map id (Set.Icc.lineMap s t)

omit [∀ b, MulAction Circleᵐᵒᵖ (P b)] [IsManifold IB ∞ B] [PrincipalBundle Circle P]
  [ContMDiffFiberBundle ∞ Circle P IB (𝓡 1)] in
variable (P) in
private theorem contMDiff_segmentMap (s t : Set.Icc a b) :
    ContMDiff ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) ∞
      (segmentMap P s t) :=
  contMDiff_id.prodMap (Set.Icc.contMDiff_lineMap s t)

/-- The primitive `h (Φ^* σ)` of `π^* (τ t - τ s)`, for `Φ` the map `(p, u) ↦ (p, s + u (t - s))`
and `h` the homotopy operator. -/
private def primitive
    (σ : SmoothTwoForm ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) (ManifoldTotalSpace Circle P × Set.Icc a b))
    (s t : Set.Icc a b) : SmoothForm (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) ℝ 1 :=
  SmoothForm.homotopyOperator
    (SmoothForm.mpullback (segmentMap P s t) (contMDiff_segmentMap P s t) σ)

/-- The homotopy formula along the segment: `d (h (Φ^* σ)) = π^* (τ t - τ s)`, since the slices
of `σ` at the two ends are `π^* (τ t)` and `π^* (τ s)`. -/
private theorem mextDerivₗ_primitive (h : IsCouplingForm σ τ) (s t : Set.Icc a b) :
    mextDerivₗ (IB.prod (𝓡 1)) 1 (primitive σ s t) =
      SmoothForm.mpullback (fun y : ManifoldTotalSpace Circle P ↦
          ((ManifoldTotalSpace.homeomorph Circle P).symm y).proj)
        (ManifoldTotalSpace.contMDiff_proj ∞ Circle P IB (𝓡 1)) (τ t - τ s) := by
  have hcl : mextDerivₗ ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) 2
      (SmoothForm.mpullback (segmentMap P s t) (contMDiff_segmentMap P s t) σ) = 0 := by
    rw [SmoothForm.mextDerivₗ_mpullback,
      (SmoothForm.isClosed_iff_mextDerivₗ_eq_zero σ).mp h.isClosed, map_zero]
  have h₁ : segmentMap P s t ∘ (fun x ↦ (x, (1 : Set.Icc (0 : ℝ) 1))) = fun p ↦ (p, t) :=
    funext fun p ↦ by simp [segmentMap, Set.Icc.lineMap_one]
  have h₀ : segmentMap P s t ∘ (fun x ↦ (x, (0 : Set.Icc (0 : ℝ) 1))) = fun p ↦ (p, s) :=
    funext fun p ↦ by simp [segmentMap, Set.Icc.lineMap_zero]
  rw [primitive, SmoothForm.mextDerivₗ_homotopyOperator hcl, SmoothForm.mpullback_mpullback,
    SmoothForm.mpullback_mpullback, map_sub, ← h.mpullback_slice, ← h.mpullback_slice]
  simp only [h₁, h₀]

/-- The primitive is invariant under the circle action, since `σ` is and `Φ` commutes with the
action. -/
private theorem mpullback_smul_primitive (h : IsCouplingForm σ τ) (s t : Set.Icc a b)
    (z : Circle) :
    SmoothForm.mpullback (fun x : ManifoldTotalSpace Circle P ↦ op z • x)
      (contMDiff_const_smul (op z)) (primitive σ s t) = primitive σ s t := by
  have hz : ContMDiff (IB.prod (𝓡 1)) (IB.prod (𝓡 1)) ∞
      (fun x : ManifoldTotalSpace Circle P ↦ op z • x) := contMDiff_const_smul (op z)
  have hzc : ContMDiff ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) ∞
      (Prod.map (fun x : ManifoldTotalSpace Circle P ↦ op z • x)
        (id : Set.Icc (0 : ℝ) 1 → Set.Icc (0 : ℝ) 1)) := hz.prodMap contMDiff_id
  refine Subtype.ext ?_
  rw [primitive, SmoothForm.coe_mpullback, SmoothForm.coe_homotopyOperator,
    ← homotopyOperator_mpullback_prodMap_id_of_isSmoothForm (hz.mdifferentiable (by simp))
      ((SmoothForm.mpullback (segmentMap P s t) (contMDiff_segmentMap P s t) σ).isSmoothForm.of_le
        (by simp)),
    ← SmoothForm.coe_mpullback _ hzc, ← SmoothForm.coe_homotopyOperator]
  have hcomp : segmentMap P s t ∘ Prod.map (fun x ↦ op z • x) id =
      (fun x : ManifoldTotalSpace Circle P × Set.Icc a b ↦ (op z • x.1, x.2)) ∘
        segmentMap P s t :=
    funext fun _ ↦ rfl
  rw [SmoothForm.mpullback_mpullback]
  conv_rhs => rw [← h.mpullback_smul z, SmoothForm.mpullback_mpullback]
  rw [SmoothForm.coe_homotopyOperator]
  simp only [hcomp]

/-- The primitive takes the value `(2π)⁻¹ (t - s)` on the fundamental vector field of `1`. -/
private theorem primitive_apply_rightFundamentalVectorField (h : IsCouplingForm σ τ)
    (s t : Set.Icc a b) (p : ManifoldTotalSpace Circle P) :
    (primitive σ s t).val p ![rightFundamentalVectorField (IB.prod (𝓡 1)) circleLieGenerator p] =
      (2 * Real.pi)⁻¹ * ((t : ℝ) - s) := by
  set X := rightFundamentalVectorField (IB.prod (𝓡 1)) circleLieGenerator p
  have hX : X = (2 * Real.pi)⁻¹ •
      rightFundamentalVectorField (IB.prod (𝓡 1)) circlePeriodOneGenerator p := by
    rw [circlePeriodOneGenerator_def, rightFundamentalVectorField_smul, Pi.smul_apply,
      smul_smul, inv_mul_cancel₀ (by positivity), one_smul]
  rw [primitive, SmoothForm.coe_homotopyOperator]
  refine (homotopyOperator_apply_apply (k := 1) ((SmoothForm.mpullback (segmentMap P s t)
      (contMDiff_segmentMap P s t) σ).isSmoothForm.of_le (by simp)) p ![X]).trans ?_
  refine (intervalIntegral.integral_congr (g := fun _ ↦ (2 * Real.pi)⁻¹ * ((t : ℝ) - s))
    fun r _ ↦ ?_).trans (by simp)
  dsimp only
  generalize Set.projIcc (0 : ℝ) 1 zero_le_one r = u
  have hD : mfderiv ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) ((IB.prod (𝓡 1)).prod (𝓡∂ 1))
      (segmentMap P s t) (p, u) =
      (mfderiv (IB.prod (𝓡 1)) (IB.prod (𝓡 1)) id p).prodMap
        (mfderiv (𝓡∂ 1) (𝓡∂ 1) (Set.Icc.lineMap s t) u) :=
    mfderiv_prodMap mdifferentiableAt_id
      ((Set.Icc.contMDiff_lineMap (n := 1) s t).mdifferentiable one_ne_zero u)
  rw [SmoothForm.mpullback_apply, hD]
  let w₀ : TangentSpace ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) (p, Set.Icc.lineMap s t u) :=
    (0, mfderiv (𝓡∂ 1) (𝓡∂ 1) (Set.Icc.lineMap s t) u 1)
  have hw₀ := h.apply_couplingField_eq_neg_mfderiv_snd (p, Set.Icc.lineMap s t u) w₀
  have hd : mfderiv (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : Set.Icc a b → ℝ) (Set.Icc.lineMap s t u)
      (mfderiv (𝓡∂ 1) (𝓡∂ 1) (Set.Icc.lineMap s t) u 1) = (t : ℝ) - (s : ℝ) := by
    rw [Set.Icc.mfderiv_lineMap_one, map_smul, mfderiv_subtypeVal_Icc_one]
    -- the tangent spaces of `ℝ` are `ℝ` itself
    exact mul_one ((t : ℝ) - s)
  -- the second component of `w₀` is `d(lineMap) 1`, by definition
  rw [show w₀.2 = mfderiv (𝓡∂ 1) (𝓡∂ 1) (Set.Icc.lineMap s t) u 1 from rfl, hd] at hw₀
  convert congrArg (fun c ↦ (2 * Real.pi)⁻¹ * c) (neg_eq_iff_eq_neg.mpr hw₀) using 1
  rw [mul_neg, ← smul_eq_mul, ← ContinuousAlternatingMap.vecCons_smul,
    ← ContinuousAlternatingMap.apply_vecCons_swap]
  congr 1
  funext i
  fin_cases i
  · -- `(id, d(lineMap)) (0, 1) = (0, d(lineMap) 1)`, by definition of `prodMap`
    simp [w₀]
    rfl
  · simp only [id_eq, mfderiv_id, Fin.mk_one, Fin.isValue, Matrix.cons_val,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    -- the components of `prodMap` are the two maps, by definition
    exact Prod.ext hX ((map_zero (mfderiv (𝓡∂ 1) (𝓡∂ 1) (Set.Icc.lineMap s t) u)).trans
      (smul_zero ((2 * Real.pi)⁻¹ : ℝ)).symm)

variable [IB.Boundaryless] [FiniteDimensional ℝ EB] [T2Space B] [SigmaCompactSpace B]

/-- **The cohomological condition on a coupling form.** If `σ` is a coupling form for `τ`, then
the de Rham classes of the forms `τ t` move linearly with `t`, with slope minus the real first
Chern class of `P`: `[τ t] - [τ s] = -(t - s) c₁(P)`. -/
theorem mk_sub_mk_eq_neg_smul_realFirstChernClass (h : IsCouplingForm σ τ) (t s : Set.Icc a b) :
    deRhamCohomology.mk IB 2 ⟨τ t, (h.isClosed_apply t).mem_closedForms⟩ -
        deRhamCohomology.mk IB 2 ⟨τ s, (h.isClosed_apply s).mem_closedForms⟩ =
      -((t : ℝ) - s) • realFirstChernClass IB P := by
  obtain ⟨α, hα⟩ := exists_isCircleConnectionForm (IB := IB) (P := P)
  set c : ℝ := (2 * Real.pi)⁻¹ * ((t : ℝ) - s)
  set β := primitive σ s t
  -- `α + (β - c α)` is a connection form, so `β - c α` is the pull-back of a form `γ` on `B`
  have hα' : IsCircleConnectionForm (α + (β - c • α)) := by
    refine ⟨fun z ↦ ?_, fun x ↦ ?_⟩
    · rw [map_add, map_sub, map_smul, hα.mpullback_op_smul, mpullback_smul_primitive h]
    · simp only [Submodule.coe_add, Submodule.coe_sub, Submodule.coe_smul, Pi.add_apply,
        Pi.sub_apply, Pi.smul_apply, ContinuousAlternatingMap.add_apply,
        ContinuousAlternatingMap.sub_apply, ContinuousAlternatingMap.smul_apply,
        hα.apply_rightFundamentalVectorField]
      simp [β, c, primitive_apply_rightFundamentalVectorField h]
  obtain ⟨γ, hγ, -⟩ := hα.existsUnique_eq_add_mpullback hα'
  have hβ := add_left_cancel hγ
  -- so `τ t - τ s = c F + d γ`, by injectivity of the pull-back along `π`
  have hτ : τ t - τ s = c • hα.curvature + mextDerivₗ IB 1 γ := by
    refine SmoothForm.mpullback_injective_of_surjective
      (ManifoldTotalSpace.contMDiff_proj ∞ Circle P IB (𝓡 1))
      ((FiberBundle.surjective_proj Circle P).comp
        (ManifoldTotalSpace.homeomorph Circle P).symm.surjective)
      ((ManifoldTotalSpace.isSubmersion_proj ∞ Circle P IB (𝓡 1)).surjective_mfderiv (by simp))
      ?_
    rw [← mextDerivₗ_primitive h, map_add, map_smul, hα.mpullback_curvature,
      ← SmoothForm.mextDerivₗ_mpullback, ← hβ]
    simp [β, map_sub, map_smul]
  rw [← map_sub, hα.realFirstChernClass_eq, smul_smul,
    show -((t : ℝ) - s) * -(2 * Real.pi)⁻¹ = c by ring, ← map_smul,
    deRhamCohomology.mk_eq_mk_iff]
  simp only [Submodule.coe_sub, Submodule.coe_smul, hτ, add_sub_cancel_left, exactForms_succ]
  exact LinearMap.mem_range_self _ γ

end Cohomology

end IsCouplingForm

end SymplecticGeometry

end
