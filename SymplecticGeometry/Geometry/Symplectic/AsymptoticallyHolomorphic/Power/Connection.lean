/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.FiberBundle.Principal.CircleConnection
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.CovariantDerivative.OfLocal
public import SymplecticGeometry.Geometry.Symplectic.AsymptoticallyHolomorphic.Power.Basic
public import SymplecticGeometry.Geometry.Manifold.FiberBundle.Principal.LocalSection
public import SymplecticGeometry.Topology.FiberBundle.Associated.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LocalFrame
public import TauCeti.Geometry.Manifold.FiberBundle.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Smooth
import SymplecticGeometry.Geometry.Manifold.DeRham.Circle

/-!
# The connection on the powers of a principal circle bundle

Let `P → B` be a smooth principal `Circle`-bundle and `α` a real `1`-form on its total space, in
practice a connection form (`SymplecticGeometry.IsCircleConnectionForm α`, which takes the value
`1` on the fundamental field of `circleLieGenerator`). For an integer `k`, this file defines the
connection `D_k = d + i k α` on the complex line bundle `PowerBundle P k = P ×_{Circle} ℂ` of
weight `k` (`Power/Basic.lean`), as a Mathlib `CovariantDerivative` on its underlying real vector
bundle.

For a point `b` of the base, write `σ_b = TauCeti.PrincipalBundle.localSection Circle P b` for the
preferred local section of `P` at `b`: `σ_b y` is the point of `P y` with fibre coordinate `1` in
the preferred trivialization of `P` at `b`. Forms are pulled back along it read in the charted
total space, as `TauCeti.PrincipalBundle.manifoldLocalSection Circle P b`. By
`TauCeti.AssociatedBundle.trivializationAt_mk_localSection` the preferred trivialization of
`PowerBundle P k` at `b` reads `[σ_b y, z]` as `z`. Over its base set,
`SymplecticGeometry.powerConnectionAt α k b` is Tau Ceti's flat derivative of that frame
(`TauCeti.Manifold.frameCovariantDerivative`, for a real basis of the model fibre) plus the
endomorphism-valued one-form `SymplecticGeometry.powerConnectionForm`,
`v ↦ (i k (σ_b^* α) v) • ·` (Mathlib's `IsCovariantDerivativeOn.add_one_form`). The connection
`D_k` takes at `x` the value of the operator for `b = x`. Both conditions of a covariant
derivative are conditions at one point, so this is a covariant derivative on all of `B`
(`CovariantDerivative.ofIsCovariantDerivativeOnOfMem`), and no comparison of frames is needed
to define it. On a section that reads `[σ_x, f]` near `x`, with
`f` differentiable at `x`, `D_k` is given at `x` by the local formula in the preferred frame
(`SymplecticGeometry.powerConnection_apply_trivializationAt`). The definition uses no property
of `α`; that the formula holds in every local section of `P` uses that `α` is a connection form
(`SymplecticGeometry.powerConnection_apply_frame`). To prove it for a local section `σ`, write
the preferred section `σ_x` as `σ · g`; a section `[σ, f]` is then `[σ_x, g ^ (-k) f]`, and the
change-of-section formula `σ_x^* α = σ^* α + g^* dθ`
(`SymplecticGeometry.IsCircleConnectionForm.mpullback_apply_eq_mpullback_division_add`) cancels
the derivative of `g ^ (-k)`, which is `-i k g ^ (-k) g^* dθ` (`TauCeti.mvfderiv_coe_circle_apply`,
Tau Ceti's `TauCeti.mpullback_zpow_circleAngularForm_apply`).

The statements take `[∀ b, Nonempty (P b)]`, since `localSection`, through Mathlib's
`Bundle.Trivialization.symm`, asks for it; a caller supplies it with
`FiberBundle.nonempty_fiber Circle P`, as `Circle` is nonempty.

## Main definitions

* `SymplecticGeometry.powerConnectionForm α k b`: the one-form `v ↦ (i k (σ_b^* α) v) • ·`.
* `SymplecticGeometry.powerConnectionAt α k b`: the connection `d + i k σ_b^* α` in the preferred
  frame at `b`, a covariant derivative over the base set of the preferred trivialization at `b`
  (`SymplecticGeometry.isCovariantDerivativeOn_powerConnectionAt`).
* `SymplecticGeometry.powerConnection α k`: a covariant derivative on `PowerBundle P k`, the
  connection `D_k` when `α` is a connection form.

## Main results

* `SymplecticGeometry.powerConnection_apply_trivializationAt`: if a section reads `[σ_x, f]` near
  `x`, with `f` differentiable at `x`, its derivative at `x` is
  `[σ_x x, df_x + i k (σ_x^* α)_x f(x)]`.
* `SymplecticGeometry.powerConnection_apply_frame`: for a connection form `α` and a local section
  `σ` of `P`, smooth on an open set `U`, the derivative of a section reading `[σ, f]` on `U` is
  `[σ x, df_x + i k (σ^* α)_x f(x)]` at a point `x ∈ U` where `f` is differentiable.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §7.4
  (the connections on the powers of the prequantum line bundle).
* [S. K. Donaldson, *Symplectic submanifolds and almost-complex geometry*][Donaldson1996].
* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, volume I, Chapter II, §7
  (covariant differentiation in associated vector bundles).
-/

public section

noncomputable section

open Bundle Manifold TauCeti TauCeti.Manifold TauCeti.PrincipalBundle
open scoped Manifold ContDiff Topology

namespace SymplecticGeometry

variable {EB HB B : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B]
  {P : B → Type*} [TopologicalSpace (TotalSpace Circle P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle Circle P] [∀ b, Nonempty (P b)] [∀ b, MulAction Circleᵐᵒᵖ (P b)]
  [PrincipalBundle Circle P] [ContMDiffFiberBundle ∞ Circle P IB (𝓡 1)]

variable (α : SmoothForm (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) ℝ 1) (k : ℤ)

/-- The one-form `v ↦ (i k (σ_b^* α)_x v) • ·` with values in the endomorphisms of the fibre
of `PowerBundle P k` at `x`, where `σ_b = localSection Circle P b` is the preferred local section
of `P` at `b`, the point of fibre coordinate `1` in the preferred trivialization of `P` at `b`. -/
def powerConnectionForm (b x : B) :
    PowerBundle P k x →L[ℝ] TangentSpace IB x →L[ℝ] PowerBundle P k x :=
  ContinuousLinearMap.smulRightL ℝ ℝ ℂ (TangentSpace IB x) (PowerBundle P k x)
    ((Complex.I * k) • Complex.ofRealCLM.comp
      ((ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace IB x) ℝ (0 : Fin 1)).symm
        (TauCeti.mpullback IB (IB.prod (𝓡 1)) (manifoldLocalSection Circle P b) α.val x)))

/-- `powerConnectionForm α k b x w` sends `v` to `(i k (σ_b^* α)_x v) • w`. -/
@[simp]
theorem powerConnectionForm_apply (b x : B) (w : PowerBundle P k x) (v : TangentSpace IB x) :
    powerConnectionForm α k b x w v =
      (Complex.I * k * (TauCeti.mpullback IB (IB.prod (𝓡 1))
        (manifoldLocalSection Circle P b) α.val x ![v] : ℝ)) • w := by
  simp [powerConnectionForm]

/-- The connection `d + i k σ_b^* α` of `PowerBundle P k` over the base set of the preferred
trivialization of `P` at `b`, read in the preferred frame at `b`. -/
def powerConnectionAt (b : B) (s : Π x, PowerBundle P k x) (x : B) :
    TangentSpace IB x →L[ℝ] PowerBundle P k x :=
  frameCovariantDerivative IB (Module.finBasis ℝ (PowerModel k))
      (trivializationAt (PowerModel k) (PowerBundle P k) b) s x +
    powerConnectionForm α k b x (s x)

/-- `powerConnectionAt α k b` is the flat derivative of the preferred frame of `PowerBundle P k`
at `b` plus `powerConnectionForm α k b`. -/
theorem powerConnectionAt_def (b : B) (s : Π x, PowerBundle P k x) (x : B) :
    powerConnectionAt α k b s x =
      frameCovariantDerivative IB (Module.finBasis ℝ (PowerModel k))
          (trivializationAt (PowerModel k) (PowerBundle P k) b) s x +
        powerConnectionForm α k b x (s x) :=
  (rfl)

/-- `powerConnectionAt α k b` is a covariant derivative over the base set of the preferred
trivialization of `P` at `b`. -/
theorem isCovariantDerivativeOn_powerConnectionAt (b : B) :
    IsCovariantDerivativeOn (PowerModel k) (powerConnectionAt α k b)
      (trivializationAt Circle P b).baseSet := by
  have h := (isCovariantDerivativeOn_frameCovariantDerivative (I := IB)
    (Module.finBasis ℝ (PowerModel k))
    (e := trivializationAt (PowerModel k) (PowerBundle P k) b)).add_one_form
      (powerConnectionForm α k b)
  rwa [AssociatedBundle.baseSet_trivializationAt] at h

/-- The covariant derivative on `PowerBundle P k` defined by a real `1`-form `α`: at each point
`x`, the operator `d + i k σ_x^* α` read in the preferred frame at `x`, where `σ_x` is the
preferred local section of `P` at `x` (`SymplecticGeometry.powerConnection_apply_trivializationAt`).
It is a covariant derivative for every `α`. When `α` is a connection form, it is the connection
`D_k`, which has this form in every local section of `P`
(`SymplecticGeometry.powerConnection_apply_frame`). -/
def powerConnection : CovariantDerivative IB (PowerModel k) (PowerBundle P k) :=
  .ofIsCovariantDerivativeOnOfMem (isCovariantDerivativeOn_powerConnectionAt α k)
    (mem_baseSet_trivializationAt Circle P)

/-- At `x`, `D_k` is the connection `powerConnectionAt α k x` of the preferred frame at `x`. -/
theorem powerConnection_apply (s : Π x, PowerBundle P k x) (x : B) :
    powerConnection α k s x = powerConnectionAt α k x s x :=
  CovariantDerivative.ofIsCovariantDerivativeOnOfMem_apply _ _ s x

/-- **The connection in the preferred frame.** If a section `s` of `PowerBundle P k` reads
`[σ_x, f]` near `x`, where `σ_x` is the preferred local section of `P` at `x`, and `f` is
differentiable at `x`, then `D_k s` at `x` is `[σ_x x, df_x + i k (σ_x^* α)_x f(x)]`. -/
theorem powerConnection_apply_trivializationAt {s : Π x, PowerBundle P k x}
    {f : B → PowerModel k} {x : B} (hf : MDifferentiableAt IB 𝓘(ℝ, PowerModel k) f x)
    (hs : ∀ᶠ y in 𝓝 x, s y = AssociatedBundle.mk Circle (localSection Circle P x y) (f y))
    (v : TangentSpace IB x) :
    powerConnection α k s x v =
      AssociatedBundle.mk Circle (localSection Circle P x x)
        (mvfderiv IB f x v +
          (Complex.I * k * (TauCeti.mpullback IB (IB.prod (𝓡 1))
            (manifoldLocalSection Circle P x) α.val x ![v] : ℝ)) • f x) := by
  have hx := mem_baseSet_trivializationAt Circle P x
  have hxe : x ∈ (trivializationAt (PowerModel k) (PowerBundle P k) x).baseSet := by
    rwa [AssociatedBundle.baseSet_trivializationAt]
  -- `mvfderiv` is `mfderiv` read in the model space `PowerModel k`.
  have hframe : frameCovariantDerivative IB (Module.finBasis ℝ (PowerModel k))
      (trivializationAt (PowerModel k) (PowerBundle P k) x) s x =
      ((trivializationAt (PowerModel k) (PowerBundle P k) x).symmL ℝ x).comp
        (mvfderiv IB f x) := by
    refine frameCovariantDerivative_eq_symmL_comp _ hf.hasMFDerivAt (fun i ↦ ?_) hxe
    filter_upwards [hs, (trivializationAt Circle P x).open_baseSet.mem_nhds hx] with y hy hyU
    rw [Trivialization.localFrameCoeff_eq_coeff _
      (hxe := by rwa [AssociatedBundle.baseSet_trivializationAt])]
    simp only [hy, AssociatedBundle.trivializationAt_mk_localSection hyU, Module.Basis.coord_apply]
  rw [powerConnection_apply, powerConnectionAt_def, add_apply, hframe,
    ContinuousLinearMap.comp_apply, Trivialization.symmL_apply _ hxe,
    AssociatedBundle.trivializationAt_symm_eq_mk hx, powerConnectionForm_apply, hs.self_of_nhds,
    ← AssociatedBundle.mk_smul_scalar, AssociatedBundle.mk_add]

attribute [local instance] finrank_real_complex_fact'

/-- **The connection in a local section.** Let `α` be a connection form and `σ` a section of `P`
that is smooth on an open set `U` of the base. If a section `s` of `PowerBundle P k` reads
`[σ, f]` on `U`, and `f` is differentiable at `x ∈ U`, then `D_k s` at `x` is
`[σ x, df_x + i k (σ^* α)_x f(x)]`. -/
theorem powerConnection_apply_frame (hα : IsCircleConnectionForm α) {σ : ∀ b, P b} {U : Set B}
    (hU : IsOpen U)
    (hσ : ContMDiffOn IB (IB.prod (𝓡 1)) ∞
      (fun b ↦ ManifoldTotalSpace.homeomorph Circle P ⟨b, σ b⟩) U)
    {s : Π x, PowerBundle P k x} {f : B → PowerModel k} {x : B} (hx : x ∈ U)
    (hf : MDifferentiableAt IB 𝓘(ℝ, PowerModel k) f x)
    (hs : ∀ y ∈ U, s y = AssociatedBundle.mk Circle (σ y) (f y)) (v : TangentSpace IB x) :
    powerConnection α k s x v =
      AssociatedBundle.mk Circle (σ x)
        (mvfderiv IB f x v +
          (Complex.I * k * (TauCeti.mpullback IB (IB.prod (𝓡 1))
            (fun y ↦ ManifoldTotalSpace.homeomorph Circle P ⟨y, σ y⟩) α.val x ![v] : ℝ)) •
            f x) := by
  -- Compare with the preferred section `τ` at `x`, through the transition `g` with `τ = σ · g`.
  set τ : ∀ y, P y := localSection Circle P x
  set g : B → Circle := fun y ↦ PrincipalBundle.division Circle (σ y) (τ y)
  -- In the frame `τ`, the section `s` reads `[τ, c • f]`, with `c = g ^ (-k)`.
  set c : B → ℂ := fun y ↦ ((g y ^ (-k) : Circle) : ℂ) with hcdef
  have hτ' : ContMDiffAt IB (IB.prod (𝓡 1)) ∞
      (fun y ↦ ManifoldTotalSpace.homeomorph Circle P ⟨y, τ y⟩) x := by
    rw [← funext (PrincipalBundle.manifoldLocalSection_def Circle P x)]
    exact PrincipalBundle.contMDiffAt_manifoldLocalSection (IB := IB) (IG := 𝓡 1) (n := ∞) x
  have hτ : MDifferentiableAt IB (IB.prod (𝓡 1))
      (fun y ↦ ManifoldTotalSpace.homeomorph Circle P ⟨y, τ y⟩) x :=
    hτ'.mdifferentiableAt (by simp)
  have hg : MDifferentiableAt IB (𝓡 1) g x :=
    ((hσ.contMDiffAt (hU.mem_nhds hx)).division hτ').mdifferentiableAt (by simp)
  have hgk : MDifferentiableAt IB (𝓡 1) (fun y ↦ g y ^ (-k)) x :=
    ((contMDiff_zpow (I := 𝓡 1) (G := Circle) (-k)).mdifferentiableAt (n := 1) one_ne_zero).comp
      x hg
  have hc : MDifferentiableAt IB 𝓘(ℝ, ℂ) c x :=
    ((contMDiff_coe_sphere (m := 1)).mdifferentiableAt one_ne_zero).comp x hgk
  have hcf : MDifferentiableAt IB 𝓘(ℝ, PowerModel k) (c • f) x :=
    (mdifferentiableAt_iff _ _).2 ⟨hc.continuousAt.smul hf.continuousAt,
      hc.differentiableWithinAt_writtenInExtChartAt.smul
        hf.differentiableWithinAt_writtenInExtChartAt⟩
  have hgc (y : B) : ((g y : ℂ) ^ k) * c y = 1 := by
    simp only [hcdef]
    rw [Circle.coe_zpow, zpow_neg, mul_inv_cancel₀ (zpow_ne_zero _ (Circle.coe_ne_zero _))]
  have hmk (y : B) (w : PowerModel k) :
      (AssociatedBundle.mk Circle (τ y) w : PowerBundle P k y) =
        AssociatedBundle.mk Circle (σ y) (((g y : ℂ) ^ k) • w) := by
    rw [← PrincipalBundle.smul_division (G := Circle) (σ y) (τ y), PowerBundle.mk_op_smul,
      AssociatedBundle.mk_smul_scalar]
  have hs' : ∀ᶠ y in 𝓝 x, s y = AssociatedBundle.mk Circle (τ y) ((c • f) y) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    rw [hs y hy, hmk, Pi.smul_apply', smul_smul, hgc, one_smul]
  -- The pull-backs of `α` along `τ` and `σ` differ by the pull-back of `dθ` along `g`.
  have hA := congrArg (· ![v]) (hα.mpullback_apply_eq_mpullback_division_add hU hσ hx hτ)
  simp only [ContinuousAlternatingMap.add_apply] at hA
  -- The derivative of `c • f`, where `dc = c · (-i k g^* dθ)`.
  have hdc : mvfderiv IB c x v = c x * (Complex.I *
      (TauCeti.mpullback IB (𝓡 1) (fun y ↦ g y ^ (-k)) circleAngularForm x ![v] : ℝ)) :=
    mvfderiv_coe_circle_apply hgk v
  rw [mpullback_fun_zpow_circleAngularForm_apply hg (-k)] at hdc
  have hd := congrArg (· v) (mvfderiv_smul_algebra hc hf)
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, hdc] at hd
  rw [powerConnection_apply_trivializationAt α k hcf hs' v, hd, hmk,
    funext (PrincipalBundle.manifoldLocalSection_def Circle P x), hA, Pi.smul_apply']
  congr 1
  simp only [smul_add, smul_smul, hgc, one_smul]
  match_scalars
  · simp
  · simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    push_cast
    linear_combination (Complex.I * k * TauCeti.mpullback IB (IB.prod (𝓡 1))
      (fun b ↦ ManifoldTotalSpace.homeomorph Circle P ⟨b, σ b⟩) α.val x ![v]) * hgc x

end SymplecticGeometry

end
