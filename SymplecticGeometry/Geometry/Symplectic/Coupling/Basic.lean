/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Icc
public import SymplecticGeometry.Geometry.Manifold.FiberBundle.Principal.CircleConnection
public import TauCeti.Geometry.Manifold.DifferentialForm.Closed
public import TauCeti.Geometry.Manifold.DifferentialForm.Interior
public import TauCeti.Geometry.Manifold.TwoForm.Basic

/-!
# Coupling forms

Let `P` be a smooth principal `Circle`-bundle over `B`, with charted total space
`TauCeti.ManifoldTotalSpace Circle P` and projection `π`, and let `a < b`. A **coupling form**
for a family `τ : Set.Icc a b → SmoothTwoForm IB B` of two-forms on the base is a closed two-form
`σ` on `ManifoldTotalSpace Circle P × Set.Icc a b` which

* is invariant under the circle action `(p, t) ↦ (p • z, t)`;
* has the coordinate `t ↦ t` of the interval as Hamiltonian for the period-one circle action, in
  the sign `ι_{(X, 0)} σ = -dt`, where `X` is the fundamental vector field of the period-one
  action;
* has slice `π^* (τ t)` at each level `t`: its pull-back along `p ↦ (p, t)` is the pull-back of
  `τ t` along `π`.

These are the forms of McDuff–Salamon, Proposition 5.1.9. There, a compact band `H⁻¹([a, b])` of
a Hamiltonian circle action that is free on it is identified with `P × [a, b]`, the levels of `H`
becoming the slices `t = const`, and the reduced form at level `t` becoming `τ t` on `B`.

## Main definitions

* `SymplecticGeometry.couplingField IB P a b`: the field `(X, 0)` on the product, where
  `X = 2π • rightFundamentalVectorField (IB.prod (𝓡 1)) circleLieGenerator` is the fundamental
  vector field of the period-one circle action.
* `SymplecticGeometry.IsCouplingForm σ τ`: `σ` is a coupling form for `τ`.

## Main results

* `SymplecticGeometry.IsCouplingForm.apply_couplingField`: pointwise, `σ((X, 0), v) = -dt(v)`.
* `SymplecticGeometry.IsCouplingForm.isClosed_apply`: each `τ t` is closed, since its pull-back
  along the submersion `π` is the closed slice of `σ`; so it has a de Rham class.
* `SymplecticGeometry.IsCouplingForm.lineMap`: coupling forms for the same `τ` form an affine
  space: `σ₀ + s • (σ₁ - σ₀)` is one for every real `s`.

## Implementation notes

The product is taken in the order `P × [a, b]`, total space first, as in McDuff–Salamon: the
Hamiltonian is then the second coordinate `x.2`, and the slice at `t` is `p ↦ (p, t)`. The
constructions on families of forms over a parameter manifold (`TauCeti.verticalForm`,
`SymplecticGeometry.moserField`, `TauCeti.SmoothForm.timeExtend`,
`SymplecticGeometry.IsSmoothFamily.exists_extend`) put the parameter first,
on `N × M`; results stated in that order are reached from this one through `Prod.swap`.
The interval `Set.Icc a b` carries Mathlib's structure of a manifold with boundary, modelled on
`𝓡∂ 1`, and its tangent spaces are all of `EuclideanSpace ℝ (Fin 1)`, endpoints included.

The circle of McDuff–Salamon has period one, so its generator is `2π • circleLieGenerator`. The
connection forms of this library (`SymplecticGeometry.IsCircleConnectionForm`) are normalized on
`circleLieGenerator` instead, so a connection form that takes the value `1` on `X` is `(2π)⁻¹`
times one of them; part 39 of `DESIGN.md` records this choice.

The Hamiltonian condition is written out with `TauCeti.RoughForm.interior` rather than with Tau
Ceti's moment maps, which are stated for left actions, while the action here is the right action
of a principal bundle.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Proposition 5.1.9 (coupling forms) and §2.7 (connection forms of circle bundles).
-/

public section

noncomputable section

open Bundle Manifold MulOpposite TauCeti Real
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
`X = 2π • rightFundamentalVectorField (IB.prod (𝓡 1)) circleLieGenerator` is the fundamental
vector field of the circle action of period one on the total space of `P`. -/
def couplingField (x : ManifoldTotalSpace Circle P × Set.Icc a b) :
    TangentSpace ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) x :=
  ((2 * π) • rightFundamentalVectorField (IB.prod (𝓡 1)) circleLieGenerator x.1,
    (0 : EuclideanSpace ℝ (Fin 1)))

theorem couplingField_def (x : ManifoldTotalSpace Circle P × Set.Icc a b) :
    couplingField IB P a b x =
      ((2 * π) • rightFundamentalVectorField (IB.prod (𝓡 1)) circleLieGenerator x.1,
        (0 : EuclideanSpace ℝ (Fin 1))) :=
  (rfl)

/-- The first component of `couplingField` is the period-one fundamental vector field. -/
@[simp]
theorem couplingField_fst (x : ManifoldTotalSpace Circle P × Set.Icc a b) :
    (couplingField IB P a b x).1 =
      (2 * π) • rightFundamentalVectorField (IB.prod (𝓡 1)) circleLieGenerator x.1 :=
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
projection of `P`. -/
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
  rw [← SmoothForm.isClosed_mpullback_iff_of_surjective
    (ManifoldTotalSpace.contMDiff_proj ∞ Circle P IB (𝓡 1))
    ((FiberBundle.surjective_proj Circle P).comp
      (ManifoldTotalSpace.homeomorph Circle P).symm.surjective)
    ((ManifoldTotalSpace.isSubmersion_proj ∞ Circle P IB (𝓡 1)).surjective_mfderiv (by simp)),
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
    funext x
    refine ContinuousAlternatingMap.ext fun v ↦ ?_
    have e₀ := congrArg (fun β ↦ β x v) h₀.interior_eq
    have e₁ := congrArg (fun β ↦ β x v) h₁.interior_eq
    simp only [RoughForm.interior_apply] at e₀ e₁ ⊢
    simp only [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_sub, Pi.add_apply,
      Pi.smul_apply, Pi.sub_apply, ContinuousAlternatingMap.add_apply,
      ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.sub_apply, e₀, e₁, sub_self,
      smul_zero, add_zero]
  mpullback_slice t := by
    rw [map_add, map_smul, map_sub, h₀.mpullback_slice, h₁.mpullback_slice, sub_self, smul_zero,
      add_zero]

end IsCouplingForm

end SymplecticGeometry

end
