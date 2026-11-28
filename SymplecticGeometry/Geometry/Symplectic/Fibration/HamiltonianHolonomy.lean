/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Fibration.Holonomy
public import SymplecticGeometry.Geometry.Symplectic.Fibration.Curvature
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Smooth
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Analysis.Calculus.Deriv.Prod
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.ModelSpace
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension
import SymplecticGeometry.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import SymplecticGeometry.Geometry.Manifold.DeRham.Basic
import SymplecticGeometry.Geometry.Symplectic.Flux.Family
import SymplecticGeometry.Geometry.Symplectic.Flux.Hamiltonian

/-!
# Hamiltonian holonomy and Hamiltonian curvature

Let `D` be a smooth Ehresmann connection on a proper smooth map `proj : M → B`, whose horizontal
spaces are the `τ`-orthogonals of the vertical spaces for a two-form `τ` on `M`. For a smooth
family of curves `Δ : ℝ × ℝ → B`, a trivialization `e` of `proj` and a loop `c` in its fibre `F`,
let `C = hD.transportedCylinder e Δ c`, so that `C (s, t, θ)` is the transport along
`t ↦ Δ (s, t)` of the point with coordinates `(Δ (s, 0), c θ)`. For the velocity `X_s` of the
holonomy diffeotopy of a disc `Δ`, the period of `ι(X_s)σ` along `c` is minus the integral of
`dτ(∂ₛC, ∂ₜC, ∂_θC)` over `[0, 1]²`
(`TauCeti.IsEhresmannConnection.period_interior_velocity_holonomyDiffeotopy`). This file rewrites
that integrand through the curvature of `D`.

Fix `p = (s, t, θ)` and smooth vector fields `v₁ v₂` on `B` with values `∂ₛΔ (s, t)` and
`∂ₜΔ (s, t)` at `Δ (s, t)`; write `v♯` for the horizontal lift of `v` and `Ω` for the curvature
`[v₁♯, v₂♯] - [v₁, v₂]♯` of `D` at `C p`. Since `proj ∘ C` is `(s, t, θ) ↦ Δ (s, t)`, the
derivative `∂ₜC` is horizontal over `∂ₜΔ`, hence equal to `v₂♯`; `∂_θC` is vertical; and `∂ₛC`
differs from `v₁♯` by a vertical vector. When `τ` is vertically closed, `dτ` vanishes on two
vertical vectors, so `dτ(∂ₛC, ∂ₜC, ∂_θC) = dτ(v₁♯, v₂♯, ∂_θC)`. The curvature identity
`TauCeti.IsEhresmannConnection.apply_curvature_eq_mvfderiv_sub_mextDeriv` then gives

`dτ(∂ₛC, ∂ₜC, ∂_θC) = ∂_θ (τ(v₁♯, v₂♯) ∘ C) - τ(Ω, ∂_θC)`

at `p`, the derivative of `τ(v₁♯, v₂♯)` along `∂_θC` being the `θ`-derivative along the
cylinder by the chain rule. The function `θ ↦ τ(v₁♯, v₂♯)(C (s, t, θ))` is smooth, and
`1`-periodic for a `1`-periodic `c`, so its derivative integrates to zero over a period.

Since the curvature at `C (s, t, θ)` of smooth fields depends only on their values at `Δ (s, t)`,
it is the curvature tensor `Ω` of `D` there on `∂ₛΔ` and `∂ₜΔ`. Integrating over `θ ∈ [0, 1]`
and then over `t ∈ [0, 1]`, the period of `ι(X_s)σ` along `c` becomes

`∫₀¹ ∫₀¹ τ(Ω(∂ₛΔ, ∂ₜΔ), ∂_θC) dθ dt`,

with a plus sign: the minus sign of the curvature term cancels that of
`period_interior_velocity_holonomyDiffeotopy`. The integrand of the inner integral is continuous
in `θ` because `C` is smooth near each `(s, t, θ)` with `Δ (s, 0)` in the base set of `e`
(Tau Ceti's `TauCeti.SmoothForm.contDiffOn_mpullback`).

When `D` has Hamiltonian curvature for an atlas `A` on whose fibres `τ` restricts to `σ`, the
inner integral vanishes. Fix `s, t`, a chart `e'` of `A` at `Δ (s, t)` and a Hamiltonian `f` of
the curvature read in `e'`. Since `∂_θC` is vertical,
`TauCeti.IsEhresmannConnection.apply_curvature_eq_mvfderiv_of_isHamiltonianVectorField` turns
`τ(Ω, ∂_θC)` into the `θ`-derivative of `f ((e' (C (s, t, θ))).2)`, a `1`-periodic function, whose
derivative integrates to zero over a period (`Function.Periodic.intervalIntegral_deriv_eq_zero`).
No relation between `τ` and `D` is needed for this step.

This is the computation behind the equivalence of Hamiltonian holonomy around discs and
Hamiltonian curvature for symplectic connections of McDuff–Salamon [McDuffSalamon2017],
Lemma 6.4.8 and Exercise 6.4.9 (see also [McDuffSalamon2019Errata]), and of
Guillemin–Lerman–Sternberg [GuilleminLermanSternberg1996], §1.4. The bracket, and so the
curvature, is Mathlib's `VectorField.mlieBracket`, as in [GuilleminLermanSternberg1996]; the
curvature of [McDuffSalamon2017] is its negative.

## Main results

* `TauCeti.IsEhresmannConnection.mextDeriv_mfderiv_transportedCylinder_eq`: for a vertically
  closed `τ`, `dτ(∂ₛC, ∂ₜC, ∂_θC) = dτ(v₁♯, v₂♯, ∂_θC)`.
* `TauCeti.IsEhresmannConnection.mpullback_mextDeriv_transportedCylinder_eq_deriv_sub`: the
  integrand of the variation of holonomy through the curvature.
* `TauCeti.IsEhresmannConnection.contDiff_val_horizontalLiftField_transportedCylinder`: the
  function `θ ↦ τ(v₁♯, v₂♯)(C (s, t, θ))` is smooth; for a `1`-periodic `c` it is `1`-periodic
  by `TauCeti.IsEhresmannConnection.transportedCylinder_add_one`.
* `TauCeti.IsEhresmannConnection.integral_mpullback_mextDeriv_transportedCylinder_eq_neg`: at
  fixed `s` and `t`, the integral over `θ ∈ [0, 1]` of `dτ(∂ₛC, ∂ₜC, ∂_θC)` is minus that of
  `τ(Ω(∂ₛΔ, ∂ₜΔ), ∂_θC)`.
* `period_interior_velocity_holonomyDiffeotopy_eq_integral_curvatureTensor`, in the namespace
  `TauCeti.IsEhresmannConnection`:
  the variation of holonomy through the curvature, the period of `ι(X_s)σ` along `c` as the
  integral of `τ(Ω(∂ₛΔ, ∂ₜΔ), ∂_θC)` over `[0, 1]²`.
* `TauCeti.IsEhresmannConnection.integral_val_curvatureTensor_transportedCylinder_eq_zero`: for
  Hamiltonian curvature, the integral over `θ ∈ [0, 1]` of `τ(Ω(∂ₛΔ, ∂ₜΔ), ∂_θC)` is zero.
* `HasHamiltonianDiscHolonomy.isHamiltonian_holonomyDiffeotopy`, in the namespace
  `TauCeti.IsEhresmannConnection`: when the holonomy around discs is Hamiltonian for a closed `σ`
  on a compact fibre, the holonomy diffeotopy is Hamiltonian, since each of its slices is the
  holonomy of a loop that bounds a disc; so each `ι(X_s)σ` is exact and its periods vanish
  (`HasHamiltonianDiscHolonomy.pathIntegral_interiorₗ_velocity_holonomyDiffeotopy_eq_zero`).

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §6.4, Lemma 6.4.8 and Exercise 6.4.9.
* [D. McDuff and D. Salamon, *Errata*][McDuffSalamon2019Errata]
* [V. Guillemin, E. Lerman, S. Sternberg, *Symplectic Fibrations and Multiplicity
  Diagrams*][GuilleminLermanSternberg1996], §1.3–1.4.
-/

public section

noncomputable section

open Bundle Function Set
open scoped Manifold ContDiff Topology

namespace TauCeti

namespace IsEhresmannConnection

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [FiniteDimensional ℝ EM]
  {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M] [IsManifold IM ∞ M] [IM.Boundaryless]
  [T2Space M]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B] [IB.Boundaryless]
  [T2Space B]
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace ℝ EF]
  {HF : Type*} [TopologicalSpace HF] {IF : ModelWithCorners ℝ EF HF}
  {F : Type*} [TopologicalSpace F] [ChartedSpace HF F]
  {proj : M → B} {D : Π x : M, Submodule ℝ (TangentSpace IM x)}
  {hD : IsEhresmannConnection IM IB ∞ proj D} {e : Trivialization F proj} {Δ : ℝ × ℝ → B}
  {c : ℝ → F}

/-- **The vertical part of `∂ₛC` drops out.** Let `τ` be a vertically closed two-form on `M`,
in the setting of `mfderiv_proj_transportedCylinder`. For fields `v₁ v₂` on `B` whose values at
`Δ (s, t)` are the derivatives of `Δ` in `s` and in `t`, the exterior derivative of `τ` at
`C (s, t, θ)` takes the same value on the derivatives `(∂ₛC, ∂ₜC, ∂_θC)` of the transported
cylinder `C` as on `(v₁♯, v₂♯, ∂_θC)`. The connection need not be that of `τ`. -/
theorem mextDeriv_mfderiv_transportedCylinder_eq {τ : SmoothTwoForm IM M}
    (hτ : SmoothTwoForm.IsVerticallyClosed IB proj τ)
    (hf : ContMDiff IM IB ∞ proj) (hfp : IsProperMap proj)
    (he_symm : ContMDiffOn (IB.prod IF) IM ∞ e.toOpenPartialHomeomorph.symm e.target)
    (hΔ : ContMDiff 𝓘(ℝ, ℝ × ℝ) IB ∞ Δ) (hc : ContMDiff 𝓘(ℝ, ℝ) IF ∞ c) {s t θ : ℝ}
    (hs : Δ (s, 0) ∈ e.baseSet) {v₁ v₂ : Π b : B, TangentSpace IB b}
    (h₁ : v₁ (Δ (s, t)) = mfderiv 𝓘(ℝ, ℝ × ℝ) IB Δ (s, t) (1, 0))
    (h₂ : v₂ (Δ (s, t)) = mfderiv 𝓘(ℝ, ℝ × ℝ) IB Δ (s, t) (0, 1)) :
    mextDeriv τ.val (hD.transportedCylinder e Δ c (s, t, θ))
        ![mfderiv 𝓘(ℝ, ℝ × ℝ × ℝ) IM (hD.transportedCylinder e Δ c) (s, t, θ) (1, 0, 0),
          mfderiv 𝓘(ℝ, ℝ × ℝ × ℝ) IM (hD.transportedCylinder e Δ c) (s, t, θ) (0, 1, 0),
          mfderiv 𝓘(ℝ, ℝ × ℝ × ℝ) IM (hD.transportedCylinder e Δ c) (s, t, θ) (0, 0, 1)] =
      mextDeriv τ.val (hD.transportedCylinder e Δ c (s, t, θ))
        ![hD.horizontalLiftField v₁ (hD.transportedCylinder e Δ c (s, t, θ)),
          hD.horizontalLiftField v₂ (hD.transportedCylinder e Δ c (s, t, θ)),
          mfderiv 𝓘(ℝ, ℝ × ℝ × ℝ) IM (hD.transportedCylinder e Δ c) (s, t, θ) (0, 0, 1)] := by
  set C := hD.transportedCylinder e Δ c
  set x := C (s, t, θ)
  set S := mfderiv 𝓘(ℝ, ℝ × ℝ × ℝ) IM C (s, t, θ) (1, 0, 0)
  set T := mfderiv 𝓘(ℝ, ℝ × ℝ × ℝ) IM C (s, t, θ) (0, 1, 0)
  set Θ := mfderiv 𝓘(ℝ, ℝ × ℝ × ℝ) IM C (s, t, θ) (0, 0, 1)
  have hΘ : Θ ∈ (mfderiv IM IB proj x).ker :=
    hD.mfderiv_transportedCylinder_apply_mem_ker (by simp) (hf.of_le (by simp)) hfp
      (hΔ.of_le (by simp)) hs
  -- `S - v₁♯` is vertical: both project to the derivative of `Δ` in `s`.
  have hS : S - hD.horizontalLiftField v₁ x ∈ (mfderiv IM IB proj x).ker := by
    have hx : proj x = Δ (s, t) :=
      hD.proj_transportedCylinder (by simp) (hf.of_le (by simp)) hfp (hΔ.of_le (by simp)) hs _ _
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero, ContinuousLinearMap.coe_coe,
      mfderiv_horizontalLiftField,
      hD.mfderiv_proj_transportedCylinder hf hfp he_symm hΔ hc hs (1, 0, 0)]
    exact h₁.symm.trans (congrArg (fun b ↦ (v₁ b : EB)) hx).symm
  -- `dτ` vanishes on two vertical vectors, here in the first and the last slot.
  have hV : mextDeriv τ.val x ![S - hD.horizontalLiftField v₁ x, T, Θ] = 0 := by
    have h0 := SmoothTwoForm.isVerticallyClosed_iff.1 hτ x _ hS _ hΘ T
    have hsw := (mextDeriv τ.val x).toAlternatingMap.map_swap
      ![S - hD.horizontalLiftField v₁ x, Θ, T] (i := 1) (j := 2) (by decide)
    have hv : ![S - hD.horizontalLiftField v₁ x, Θ, T] ∘ Equiv.swap 1 2 =
        ![S - hD.horizontalLiftField v₁ x, T, Θ] := by
      ext i
      fin_cases i <;> rfl
    rw [hv] at hsw
    exact hsw.trans (neg_eq_zero.2 h0)
  rw [← add_sub_cancel (hD.horizontalLiftField v₁ x) S, ContinuousAlternatingMap.vecCons_add, hV,
    add_zero, show T = _ from
      hD.mfderiv_transportedCylinder_eq_horizontalLiftField hf hfp he_symm hΔ hc hs h₂]

/-- **Derivatives along the loops of the transported cylinder.** In the setting of
`mfderiv_proj_transportedCylinder`, let `Δ (s, 0)` be in the base set of `e` and `Φ : M → ℝ` be
differentiable at `C (s, t, θ)`, for the transported cylinder `C`. Then the derivative of
`θ' ↦ Φ (C (s, t, θ'))` at `θ` is the derivative of `Φ` along `∂_θC (s, t, θ)`. -/
theorem deriv_comp_transportedCylinder (hf : ContMDiff IM IB ∞ proj) (hfp : IsProperMap proj)
    (he_symm : ContMDiffOn (IB.prod IF) IM ∞ e.toOpenPartialHomeomorph.symm e.target)
    (hΔ : ContMDiff 𝓘(ℝ, ℝ × ℝ) IB ∞ Δ) (hc : ContMDiff 𝓘(ℝ, ℝ) IF ∞ c) {s t θ : ℝ}
    (hs : Δ (s, 0) ∈ e.baseSet) {Φ : M → ℝ}
    (hΦ : MDifferentiableAt IM 𝓘(ℝ) Φ (hD.transportedCylinder e Δ c (s, t, θ))) :
    deriv (fun θ' ↦ Φ (hD.transportedCylinder e Δ c (s, t, θ'))) θ =
      mvfderiv IM Φ (hD.transportedCylinder e Δ c (s, t, θ))
        (mfderiv 𝓘(ℝ, ℝ × ℝ × ℝ) IM (hD.transportedCylinder e Δ c) (s, t, θ) (0, 0, 1)) := by
  set C := hD.transportedCylinder e Δ c
  have hC : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ × ℝ) IM C (s, t, θ) :=
    (hD.contMDiffAt_transportedCylinder hf hfp he_symm hΔ hc hs).mdifferentiableAt (by simp)
  have hℓ : HasDerivAt (fun θ' : ℝ ↦ (s, t, θ')) ((0, 0, 1) : ℝ × ℝ × ℝ) θ :=
    (hasDerivAt_const θ s).prodMk ((hasDerivAt_const θ t).prodMk (hasDerivAt_id θ))
  -- The velocity of the loop `θ' ↦ C (s, t, θ')` at `θ` is `∂_θC (s, t, θ)`.
  have hv := Manifold.hasMFDerivAt_curveVelocity (I := IM)
    (hC.comp θ hℓ.differentiableAt.mdifferentiableAt)
  rw [hC.curveVelocity_comp_mfderiv hℓ] at hv
  exact (Manifold.hasDerivAt_comp_curve hΦ hv).deriv

/-- **The integrand of the variation of holonomy, through the curvature.** Let `D` be the
connection of a vertically closed two-form `τ` on a proper smooth map `proj`, `Δ` a smooth
family of curves, `e` a trivialization with a smooth inverse, `c` smooth, and `C` the
transported cylinder. Let `(s, t, θ)` be a parameter with `Δ (s, 0)` in the base set of `e`, and
`v₁ v₂` fields on `B`, `C^1` at `Δ (s, t)`, whose values there are the derivatives of `Δ` in `s`
and in `t`. Then the integrand `dτ(∂ₛC, ∂ₜC, ∂_θC)` of
`period_interior_velocity_holonomyDiffeotopy` at `(s, t, θ)` is the derivative in `θ` of
`τ(v₁♯, v₂♯)` along the cylinder minus `τ(Ω, ∂_θC)`, with `Ω = [v₁♯, v₂♯] - [v₁, v₂]♯` the
curvature of `D` at `C (s, t, θ)`. -/
theorem mpullback_mextDeriv_transportedCylinder_eq_deriv_sub {τ : SmoothTwoForm IM M}
    (hτD : SmoothTwoForm.horizontalDistribution IB proj τ = D)
    (hτ : SmoothTwoForm.IsVerticallyClosed IB proj τ)
    (hf : ContMDiff IM IB ∞ proj) (hfp : IsProperMap proj)
    (he_symm : ContMDiffOn (IB.prod IF) IM ∞ e.toOpenPartialHomeomorph.symm e.target)
    (hΔ : ContMDiff 𝓘(ℝ, ℝ × ℝ) IB ∞ Δ) (hc : ContMDiff 𝓘(ℝ, ℝ) IF ∞ c) {s t θ : ℝ}
    (hs : Δ (s, 0) ∈ e.baseSet) {v₁ v₂ : Π b : B, TangentSpace IB b}
    (hv₁ : ContMDiffAt IB IB.tangent 1 (T% v₁) (Δ (s, t)))
    (hv₂ : ContMDiffAt IB IB.tangent 1 (T% v₂) (Δ (s, t)))
    (h₁ : v₁ (Δ (s, t)) = mfderiv 𝓘(ℝ, ℝ × ℝ) IB Δ (s, t) (1, 0))
    (h₂ : v₂ (Δ (s, t)) = mfderiv 𝓘(ℝ, ℝ × ℝ) IB Δ (s, t) (0, 1)) :
    mpullback 𝓘(ℝ, ℝ × ℝ × ℝ) IM (hD.transportedCylinder e Δ c) (mextDeriv τ.val) (s, t, θ)
        ![(1, 0, 0), (0, 1, 0), (0, 0, 1)] =
      deriv (fun θ' ↦ τ.val (hD.transportedCylinder e Δ c (s, t, θ'))
        ![hD.horizontalLiftField v₁ (hD.transportedCylinder e Δ c (s, t, θ')),
          hD.horizontalLiftField v₂ (hD.transportedCylinder e Δ c (s, t, θ'))]) θ -
      τ.val (hD.transportedCylinder e Δ c (s, t, θ))
        ![hD.curvature v₁ v₂ (hD.transportedCylinder e Δ c (s, t, θ)),
          mfderiv 𝓘(ℝ, ℝ × ℝ × ℝ) IM (hD.transportedCylinder e Δ c) (s, t, θ) (0, 0, 1)] := by
  have hsplit := mextDeriv_mfderiv_transportedCylinder_eq (hD := hD) hτ hf hfp he_symm hΔ hc
    hs h₁ h₂ (θ := θ)
  subst hτD
  set C := hD.transportedCylinder e Δ c
  have hx : proj (C (s, t, θ)) = Δ (s, t) :=
    hD.proj_transportedCylinder (by simp) (hf.of_le (by simp)) hfp (hΔ.of_le (by simp)) hs _ _
  rw [← hx] at hv₁ hv₂
  -- The curvature identity at `C (s, t, θ)`, along the vertical vector `∂_θC`.
  have hid := apply_curvature_eq_mvfderiv_sub_mextDeriv hD (by simp) (hf.of_le (by simp)) hv₁
    hv₂ (hD.mfderiv_transportedCylinder_apply_mem_ker (by simp) (hf.of_le (by simp)) hfp
      (hΔ.of_le (by simp)) (p := (s, t, θ)) hs)
  have hg : MDifferentiableAt IM 𝓘(ℝ)
      (fun y ↦ τ.val y ![hD.horizontalLiftField v₁ y, hD.horizontalLiftField v₂ y])
      (C (s, t, θ)) :=
    SmoothForm.mdifferentiableAt_apply_two τ
      (hD.mdifferentiableAt_horizontalLiftField (by simp) ((hf _).of_le (by simp)) hv₁)
      (hD.mdifferentiableAt_horizontalLiftField (by simp) ((hf _).of_le (by simp)) hv₂)
  have hpb : mpullback 𝓘(ℝ, ℝ × ℝ × ℝ) IM C (mextDeriv τ.val) (s, t, θ)
      ![(1, 0, 0), (0, 1, 0), (0, 0, 1)] =
        mextDeriv τ.val (C (s, t, θ)) ![mfderiv 𝓘(ℝ, ℝ × ℝ × ℝ) IM C (s, t, θ) (1, 0, 0),
          mfderiv 𝓘(ℝ, ℝ × ℝ × ℝ) IM C (s, t, θ) (0, 1, 0),
          mfderiv 𝓘(ℝ, ℝ × ℝ × ℝ) IM C (s, t, θ) (0, 0, 1)] :=
    mpullback_apply_triple _ _ _ _ _ _
  -- The derivative of `τ(v₁♯, v₂♯)` along `∂_θC` is its derivative in `θ` along the cylinder.
  have hderiv := hD.deriv_comp_transportedCylinder hf hfp he_symm hΔ hc hs hg
  rw [hpb, hsplit, hderiv]
  linear_combination hid

/-- **The function `τ(v₁♯, v₂♯)` along the transported cylinder is smooth.** For a smooth
connection on a proper smooth map, a two-form `τ`, smooth fields `v₁ v₂` on `B`, a smooth family
`Δ`, a trivialization `e` with a smooth inverse and a smooth `c`, the function
`θ ↦ τ(v₁♯, v₂♯)(C (s, t, θ))` is smooth when `Δ (s, 0)` is in the base set of `e`. -/
theorem contDiff_val_horizontalLiftField_transportedCylinder (τ : SmoothTwoForm IM M)
    (hf : ContMDiff IM IB ∞ proj) (hfp : IsProperMap proj)
    (he_symm : ContMDiffOn (IB.prod IF) IM ∞ e.toOpenPartialHomeomorph.symm e.target)
    (hΔ : ContMDiff 𝓘(ℝ, ℝ × ℝ) IB ∞ Δ) (hc : ContMDiff 𝓘(ℝ, ℝ) IF ∞ c)
    {v₁ v₂ : Π b : B, TangentSpace IB b} (hv₁ : CMDiff ∞ (T% v₁)) (hv₂ : CMDiff ∞ (T% v₂))
    {s t : ℝ} (hs : Δ (s, 0) ∈ e.baseSet) :
    ContDiff ℝ ∞ fun θ ↦ τ.val (hD.transportedCylinder e Δ c (s, t, θ))
      ![hD.horizontalLiftField v₁ (hD.transportedCylinder e Δ c (s, t, θ)),
        hD.horizontalLiftField v₂ (hD.transportedCylinder e Δ c (s, t, θ))] := by
  have hL {v : Π b : B, TangentSpace IB b} (hv : CMDiff ∞ (T% v)) :
      ContMDiff IM IM.tangent ∞ (T% (hD.horizontalLiftField v)) :=
    hD.contMDiff_horizontalLiftField (hf.of_le (by simp)) hv
  have hg : ContMDiff IM 𝓘(ℝ) ∞
      (fun y ↦ τ.val y ![hD.horizontalLiftField v₁ y, hD.horizontalLiftField v₂ y]) := by
    simpa using SmoothForm.contMDiff_apply τ (b := id) (hL hv₁) (hL hv₂)
  have hℓ : ContMDiff 𝓘(ℝ) IM ∞ fun θ ↦ hD.transportedCylinder e Δ c (s, t, θ) :=
    (hD.contMDiffOn_transportedCylinder hf hfp he_symm hΔ hc).comp_contMDiff
      (by fun_prop : ContDiff ℝ ∞ fun θ : ℝ ↦ (s, t, θ)).contMDiff fun _ ↦ hs
  exact contMDiff_iff_contDiff.1 (hg.comp hℓ)

/-- **The variation of holonomy through the curvature, at fixed `t`.** Let `D` be the connection
of a vertically closed two-form `τ` on a proper smooth map `proj`, `Δ` a smooth family of curves,
`e` a trivialization with a smooth inverse, `c` a smooth `1`-periodic map and `C` the transported
cylinder. If `Δ (s, 0)` is in the base set of `e`, the integral over `θ ∈ [0, 1]` of
`dτ(∂ₛC, ∂ₜC, ∂_θC)` at `(s, t, θ)` is minus that of `τ(Ω(∂ₛΔ, ∂ₜΔ), ∂_θC)`, with `Ω` the
curvature tensor of `D` at `C (s, t, θ)`. -/
theorem integral_mpullback_mextDeriv_transportedCylinder_eq_neg {τ : SmoothTwoForm IM M}
    (hτD : SmoothTwoForm.horizontalDistribution IB proj τ = D)
    (hτ : SmoothTwoForm.IsVerticallyClosed IB proj τ)
    (hf : ContMDiff IM IB ∞ proj) (hfp : IsProperMap proj)
    (he_symm : ContMDiffOn (IB.prod IF) IM ∞ e.toOpenPartialHomeomorph.symm e.target)
    (hΔ : ContMDiff 𝓘(ℝ, ℝ × ℝ) IB ∞ Δ) (hc : ContMDiff 𝓘(ℝ, ℝ) IF ∞ c) (hcp : Periodic c 1)
    {s t : ℝ} (hs : Δ (s, 0) ∈ e.baseSet) :
    ∫ θ in 0..1, mpullback 𝓘(ℝ, ℝ × ℝ × ℝ) IM (hD.transportedCylinder e Δ c) (mextDeriv τ.val)
        (s, t, θ) ![(1, 0, 0), (0, 1, 0), (0, 0, 1)] =
      -∫ θ in 0..1, τ.val (hD.transportedCylinder e Δ c (s, t, θ))
        ![hD.curvatureTensor (by simp) ((hf _).of_le (by simp))
            (mfderiv 𝓘(ℝ, ℝ × ℝ) IB Δ (s, t) (1, 0)) (mfderiv 𝓘(ℝ, ℝ × ℝ) IB Δ (s, t) (0, 1)),
          mfderiv 𝓘(ℝ, ℝ × ℝ × ℝ) IM (hD.transportedCylinder e Δ c) (s, t, θ) (0, 0, 1)] := by
  set C := hD.transportedCylinder e Δ c
  set u₁ := mfderiv 𝓘(ℝ, ℝ × ℝ) IB Δ (s, t) (1, 0)
  set u₂ := mfderiv 𝓘(ℝ, ℝ × ℝ) IB Δ (s, t) (0, 1)
  -- Smooth fields on `B` through `∂ₛΔ` and `∂ₜΔ`.
  set v₁ := FiberBundle.contMDiffExtend IB EB u₁
  set v₂ := FiberBundle.contMDiffExtend IB EB u₂
  have hv₁ : CMDiff ∞ (T% v₁) := FiberBundle.contMDiff_contMDiffExtend IB EB u₁
  have hv₂ : CMDiff ∞ (T% v₂) := FiberBundle.contMDiff_contMDiffExtend IB EB u₂
  set g := fun θ ↦ τ.val (C (s, t, θ))
    ![hD.horizontalLiftField v₁ (C (s, t, θ)), hD.horizontalLiftField v₂ (C (s, t, θ))]
  have hg : ContDiff ℝ ∞ g :=
    contDiff_val_horizontalLiftField_transportedCylinder τ hf hfp he_symm hΔ hc hv₁ hv₂ hs
  -- The pointwise identity, with the curvature tensor.
  have hpt (θ : ℝ) : τ.val (C (s, t, θ))
      ![hD.curvatureTensor (by simp) ((hf _).of_le (by simp)) u₁ u₂,
        mfderiv 𝓘(ℝ, ℝ × ℝ × ℝ) IM C (s, t, θ) (0, 0, 1)] =
      deriv g θ - mpullback 𝓘(ℝ, ℝ × ℝ × ℝ) IM C (mextDeriv τ.val) (s, t, θ)
        ![(1, 0, 0), (0, 1, 0), (0, 0, 1)] := by
    rw [← hD.curvature_contMDiffExtend (by simp) ((hf _).of_le (by simp))
        (hD.proj_transportedCylinder (by simp) (hf.of_le (by simp)) hfp (hΔ.of_le (by simp)) hs
          t θ) u₁ u₂,
      mpullback_mextDeriv_transportedCylinder_eq_deriv_sub (hD := hD) hτD hτ hf hfp
      he_symm hΔ hc hs ((hv₁ _).of_le (by simp)) ((hv₂ _).of_le (by simp))
      (FiberBundle.contMDiffExtend_apply_self IB EB u₁)
      (FiberBundle.contMDiffExtend_apply_self IB EB u₂)]
    ring
  -- The integrand of the left side is continuous in `θ`, since `C` is smooth near `(s, t, θ)`.
  have hint : IntervalIntegrable (fun θ ↦ mpullback 𝓘(ℝ, ℝ × ℝ × ℝ) IM C (mextDeriv τ.val)
      (s, t, θ) ![(1, 0, 0), (0, 1, 0), (0, 0, 1)]) MeasureTheory.volume 0 1 := by
    have hU : IsOpen {p : ℝ × ℝ × ℝ | Δ (p.1, 0) ∈ e.baseSet} :=
      e.open_baseSet.preimage (hΔ.continuous.comp (by fun_prop))
    have hl : Continuous fun θ : ℝ ↦ (s, t, θ) := by fun_prop
    -- The pullback of the smooth form `dτ` along `C` is smooth on the open set `U`.
    have hd := (mextDerivₗ IM 2 τ).contDiffOn_mpullback hU
      (hD.contMDiffOn_transportedCylinder hf hfp he_symm hΔ hc)
    rw [mextDerivₗ_apply] at hd
    exact (((ContinuousAlternatingMap.apply ℝ (ℝ × ℝ × ℝ) ℝ
      ![(1, 0, 0), (0, 1, 0), (0, 0, 1)]).continuous.comp_continuousOn
      hd.continuousOn).comp_continuous hl fun _ ↦ hs).intervalIntegrable _ _
  -- The derivative of the `1`-periodic function `g` integrates to zero over a period.
  have hgp : Periodic g 1 := fun θ ↦
    congrArg (fun y ↦ τ.val y ![hD.horizontalLiftField v₁ y, hD.horizontalLiftField v₂ y])
      (hD.transportedCylinder_add_one hcp s t θ)
  have hderiv : ∫ θ in 0..1, deriv g θ = 0 := by
    simpa using hgp.intervalIntegral_deriv_eq_zero (a := 0)
      (fun θ _ ↦ hg.differentiable (by simp) θ)
      ((hg.continuous_deriv (by simp)).intervalIntegrable _ _)
  rw [intervalIntegral.integral_congr fun θ _ ↦ hpt θ,
    intervalIntegral.integral_sub ((hg.continuous_deriv (by simp)).intervalIntegrable _ _) hint,
    hderiv, zero_sub, neg_neg]

end IsEhresmannConnection

end TauCeti

namespace TauCeti

namespace IsEhresmannConnection

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [FiniteDimensional ℝ EM]
  {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M] [IsManifold IM ∞ M] [IM.Boundaryless]
  [T2Space M]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B] [IB.Boundaryless]
  [T2Space B]
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace ℝ EF] [FiniteDimensional ℝ EF]
  {HF : Type*} [TopologicalSpace HF] {IF : ModelWithCorners ℝ EF HF} [IF.Boundaryless]
  {F : Type} [TopologicalSpace F] [ChartedSpace HF F] [IsManifold IF ∞ F] [T2Space F]
  {proj : M → B} {D : Π x : M, Submodule ℝ (TangentSpace IM x)}
  {hD : IsEhresmannConnection IM IB ∞ proj D} {A : MapFiber.Atlas F proj} {b x : B}
  {γ : Path x x} {Δ : ℝ × ℝ → B} {c : ℝ → F}

/-- **The variation of holonomy through the curvature.** Let `τ` be a vertically closed two-form
on `M` that restricts to a closed form `σ` on the fibres of a smooth atlas `A` of a proper map,
and whose horizontal spaces form the smooth connection `D`. Let `Δ` be a smooth disc with centre
`x` in the base set of a chart `e = A.trivAt b`, `Φ` its holonomy diffeotopy read in `e`, all of
whose slices preserve `σ`, and `X_s` the velocity of `Φ` at time `s`. For a smooth `1`-periodic
loop `c` in `F` with transported cylinder `C`, the line integral of `ι_{X_s} σ` along `c` from `0`
to `1` is the integral over `(t, θ) ∈ [0, 1] × [0, 1]` of `τ(Ω(∂ₛΔ, ∂ₜΔ), ∂_θC)`, with `Ω` the
curvature tensor of `D` at `C (s, t, θ)`. -/
theorem period_interior_velocity_holonomyDiffeotopy_eq_integral_curvatureTensor
    {σ : SmoothTwoForm IF F} {τ : SmoothTwoForm IM M}
    (hτD : SmoothTwoForm.horizontalDistribution IB proj τ = D) (hτ : A.RestrictsTo σ τ)
    (hσ : σ.IsClosed) (hτv : SmoothTwoForm.IsVerticallyClosed IB proj τ) (hfp : IsProperMap proj)
    (hA : A.IsContMDiff ∞ IB IF IM) (hΔ : IsSmoothDisc IB γ Δ) (hx : x ∈ (A.trivAt b).baseSet)
    (hΦ : ∀ s, (hD.holonomyDiffeotopy hA.contMDiff_proj hfp (hA.contMDiffOn_trivAt b)
        (hA.contMDiffOn_trivAt_symm b) hΔ hx).timeSlice s ∈ SmoothForm.diffeomorphStabilizer σ)
    (hc : ContMDiff 𝓘(ℝ, ℝ) IF ∞ c) (hcp : Periodic c 1) (s : unitInterval) :
    pathIntegral (σ.interiorₗ ((hD.holonomyDiffeotopy hA.contMDiff_proj hfp
        (hA.contMDiffOn_trivAt b) (hA.contMDiffOn_trivAt_symm b) hΔ hx).smoothVelocity s)).val
        c 0 1 =
      ∫ t in 0..1, ∫ θ in 0..1, τ.val (hD.transportedCylinder (A.trivAt b) Δ c ((s : ℝ), t, θ))
        ![hD.curvatureTensor (by simp) ((hA.contMDiff_proj _).of_le (by simp))
            (mfderiv 𝓘(ℝ, ℝ × ℝ) IB Δ ((s : ℝ), t) (1, 0))
            (mfderiv 𝓘(ℝ, ℝ × ℝ) IB Δ ((s : ℝ), t) (0, 1)),
          mfderiv 𝓘(ℝ, ℝ × ℝ × ℝ) IM (hD.transportedCylinder (A.trivAt b) Δ c) ((s : ℝ), t, θ)
            (0, 0, 1)] := by
  rw [period_interior_velocity_holonomyDiffeotopy hτD hτ hσ hfp hA hΔ hx hΦ hc hcp s,
    ← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun t _ ↦ ?_
  rw [integral_mpullback_mextDeriv_transportedCylinder_eq_neg hτD hτv hA.contMDiff_proj hfp
    (hA.contMDiffOn_trivAt_symm b) hΔ.contMDiff hc hcp
    ((congrArg (· ∈ (A.trivAt b).baseSet) (hΔ.apply_seam s)).mpr hx), neg_neg]

omit [FiniteDimensional ℝ EF] [IF.Boundaryless] [T2Space F] in
/-- **Hamiltonian curvature kills the curvature term.** Let `τ` restrict to `σ` on the fibres
of a smooth atlas `A` of a proper map `proj`, and let the smooth connection `D` have
Hamiltonian curvature for `A` and `σ`. Let `Δ` be a smooth family of curves, `e` a
trivialization with a smooth inverse, `c` a smooth `1`-periodic loop in `F` and `C` the
transported cylinder. If `Δ (s, 0)` is in the base set of `e`, the integral over
`θ ∈ [0, 1]` of `τ(Ω(∂ₛΔ, ∂ₜΔ), ∂_θC)` at `(s, t, θ)` vanishes, with `Ω` the curvature tensor
of `D` at `C (s, t, θ)`: in a chart `e'` at `Δ (s, t)`, the integrand is the derivative in `θ`
of `f ((e' (C (s, t, θ))).2)`, for a Hamiltonian `f` of the curvature read in `e'`. No relation
between `τ` and `D` is needed. -/
theorem integral_val_curvatureTensor_transportedCylinder_eq_zero {σ : SmoothTwoForm IF F}
    {τ : SmoothTwoForm IM M} (hτ : A.RestrictsTo σ τ) (hA : A.IsContMDiff ∞ IB IF IM)
    (hH : hD.HasHamiltonianCurvature A σ) (hfp : IsProperMap proj) {e : Trivialization F proj}
    (he_symm : ContMDiffOn (IB.prod IF) IM ∞ e.toOpenPartialHomeomorph.symm e.target)
    (hΔ : ContMDiff 𝓘(ℝ, ℝ × ℝ) IB ∞ Δ) (hc : ContMDiff 𝓘(ℝ, ℝ) IF ∞ c) (hcp : Periodic c 1)
    {s t : ℝ} (hs : Δ (s, 0) ∈ e.baseSet) :
    ∫ θ in 0..1, τ.val (hD.transportedCylinder e Δ c (s, t, θ))
        ![hD.curvatureTensor (by simp) ((hA.contMDiff_proj _).of_le (by simp))
            (mfderiv 𝓘(ℝ, ℝ × ℝ) IB Δ (s, t) (1, 0)) (mfderiv 𝓘(ℝ, ℝ × ℝ) IB Δ (s, t) (0, 1)),
          mfderiv 𝓘(ℝ, ℝ × ℝ × ℝ) IM (hD.transportedCylinder e Δ c) (s, t, θ) (0, 0, 1)] =
      0 := by
  have hf : ContMDiff IM IB ∞ proj := hA.contMDiff_proj
  set C := hD.transportedCylinder e Δ c
  set u₁ := mfderiv 𝓘(ℝ, ℝ × ℝ) IB Δ (s, t) (1, 0)
  set u₂ := mfderiv 𝓘(ℝ, ℝ × ℝ) IB Δ (s, t) (0, 1)
  -- Smooth fields on `B` through `∂ₛΔ` and `∂ₜΔ`, and a Hamiltonian of their curvature read in
  -- the chart `e'` at `Δ (s, t)`.
  set v₁ := FiberBundle.contMDiffExtend IB EB u₁
  set v₂ := FiberBundle.contMDiffExtend IB EB u₂
  have hv₁ : CMDiff ∞ (T% v₁) := FiberBundle.contMDiff_contMDiffExtend IB EB u₁
  have hv₂ : CMDiff ∞ (T% v₂) := FiberBundle.contMDiff_contMDiffExtend IB EB u₂
  set e' := A.trivAt (Δ (s, t))
  have hy : Δ (s, t) ∈ e'.baseSet := A.mem_baseSet_trivAt _
  obtain ⟨f, hfs, hX⟩ := (hD.hasHamiltonianCurvature_def A σ).1 hH _ _ hy v₁ v₂ hv₁ hv₂
  have hp (θ : ℝ) : proj (C (s, t, θ)) = Δ (s, t) :=
    hD.proj_transportedCylinder (by simp) (hf.of_le (by simp)) hfp (hΔ.of_le (by simp)) hs _ _
  have hsrc (θ : ℝ) : C (s, t, θ) ∈ e'.source := e'.mem_source.2 ((hp θ).symm ▸ hy)
  -- The function `f` read along the loops of the cylinder through the fibre coordinate of `e'`.
  have hΦ : ContMDiffOn IM 𝓘(ℝ) ∞ (fun y ↦ f (e' y).2) e'.source :=
    hfs.comp_contMDiffOn (hA.contMDiffOn_snd_trivAt _)
  have hℓ : ContMDiff 𝓘(ℝ) IM ∞ fun θ ↦ C (s, t, θ) :=
    (hD.contMDiffOn_transportedCylinder hf hfp he_symm hΔ hc).comp_contMDiff
      (by fun_prop : ContDiff ℝ ∞ fun θ : ℝ ↦ (s, t, θ)).contMDiff fun _ ↦ hs
  have hg : ContDiff ℝ ∞ fun θ ↦ f (e' (C (s, t, θ))).2 :=
    contMDiff_iff_contDiff.1 (hΦ.comp_contMDiff hℓ hsrc)
  -- The integrand is the derivative in `θ` of `f ((e' (C (s, t, θ))).2)`.
  have hpt (θ : ℝ) : τ.val (C (s, t, θ))
      ![hD.curvatureTensor (by simp) ((hf _).of_le (by simp)) u₁ u₂,
        mfderiv 𝓘(ℝ, ℝ × ℝ × ℝ) IM C (s, t, θ) (0, 0, 1)] =
      deriv (fun θ' ↦ f (e' (C (s, t, θ'))).2) θ := by
    have hsnd : MDifferentiableAt IM IF (fun y ↦ (e' y).2) (C (s, t, θ)) :=
      ((hA.contMDiffOn_snd_trivAt _).contMDiffAt
        (e'.open_source.mem_nhds (hsrc θ))).mdifferentiableAt (by simp)
    have hfd : MDifferentiableAt IM 𝓘(ℝ) (fun y ↦ f (e' y).2) (C (s, t, θ)) :=
      ((hfs _).mdifferentiableAt (by simp)).comp _ hsnd
    rw [← hD.curvature_contMDiffExtend (by simp) ((hf _).of_le (by simp)) (hp θ) u₁ u₂,
      hD.apply_curvature_eq_mvfderiv_of_isHamiltonianVectorField (by simp) hA hτ hy
        ((hv₁ _).of_le (by simp)) ((hv₂ _).of_le (by simp)) hX (hp θ)
        (hD.mfderiv_transportedCylinder_apply_mem_ker (by simp) (hf.of_le (by simp)) hfp
          (hΔ.of_le (by simp)) hs),
      hD.deriv_comp_transportedCylinder hf hfp he_symm hΔ hc hs hfd]
    exact (mvfderiv_comp_apply _ ((hfs _).mdifferentiableAt (by simp)) hsnd _).symm
  have hgp : Periodic (fun θ ↦ f (e' (C (s, t, θ))).2) 1 := fun θ ↦ by
    simp only [C, hD.transportedCylinder_add_one hcp]
  rw [intervalIntegral.integral_congr fun θ _ ↦ hpt θ]
  simpa using hgp.intervalIntegral_deriv_eq_zero (a := 0)
    (fun θ _ ↦ hg.differentiable (by simp) θ)
    ((hg.continuous_deriv (by simp)).intervalIntegrable _ _)

/-- **Hamiltonian disc holonomy makes the holonomy diffeotopy Hamiltonian.** Let `D` be a smooth
Ehresmann connection on a proper map with a smooth atlas `A` and a compact model fibre `F`, whose
holonomy around discs is Hamiltonian for a closed two-form `σ` on `F`. Then the holonomy
diffeotopy of a smooth disc `Δ` with centre `x` in the base set of a chart `A.trivAt b`, read in
that chart, is a Hamiltonian diffeotopy of `σ`. -/
theorem HasHamiltonianDiscHolonomy.isHamiltonian_holonomyDiffeotopy [CompactSpace F]
    {σ : SmoothTwoForm IF F} (hH : hD.HasHamiltonianDiscHolonomy A σ) (hσ : σ.IsClosed)
    (hfp : IsProperMap proj) (hA : A.IsContMDiff ∞ IB IF IM) (hΔ : IsSmoothDisc IB γ Δ)
    (hx : x ∈ (A.trivAt b).baseSet) :
    (hD.holonomyDiffeotopy hA.contMDiff_proj hfp (hA.contMDiffOn_trivAt b)
      (hA.contMDiffOn_trivAt_symm b) hΔ hx).IsHamiltonian σ := by
  refine Diffeotopy.isHamiltonian_of_forall_timeSlice_mem_hamiltonianGroup
    (σ := ⟨σ, hσ.mem_closedForms⟩) fun s ↦ ?_
  -- Each slice is the holonomy of the loop `t ↦ Δ (s, t)`, which bounds a smooth disc.
  rw [timeSlice_holonomyDiffeotopy]
  exact (hasHamiltonianDiscHolonomy_iff hfp hA).1 hH _
    (SymplecticGeometry.BoundsSmoothDisc.of_isSmoothDisc_slice hΔ s) b
    ((hΔ.apply_seam s).symm ▸ hx)

/-- **Hamiltonian disc holonomy kills the periods of the holonomy velocity.** In the setting of
`HasHamiltonianDiscHolonomy.isHamiltonian_holonomyDiffeotopy`, for every time `s` and every `C¹`
curve `c` in `F` with `c 0 = c 1`, the line integral from `0` to `1` along `c` of the contraction
`ι_{X_s} σ` of `σ` with the velocity `X_s` of the holonomy diffeotopy vanishes. -/
theorem HasHamiltonianDiscHolonomy.pathIntegral_interiorₗ_velocity_holonomyDiffeotopy_eq_zero
    [CompactSpace F] {σ : SmoothTwoForm IF F} (hH : hD.HasHamiltonianDiscHolonomy A σ)
    (hσ : σ.IsClosed) (hfp : IsProperMap proj) (hA : A.IsContMDiff ∞ IB IF IM)
    (hΔ : IsSmoothDisc IB γ Δ) (hx : x ∈ (A.trivAt b).baseSet) (s : unitInterval)
    (hc : ContMDiff 𝓘(ℝ, ℝ) IF 1 c) (hc₀₁ : c 0 = c 1) :
    pathIntegral (σ.interiorₗ ((hD.holonomyDiffeotopy hA.contMDiff_proj hfp
        (hA.contMDiffOn_trivAt b) (hA.contMDiffOn_trivAt_symm b) hΔ hx).smoothVelocity s)).val
        c 0 1 = 0 :=
  (hH.isHamiltonian_holonomyDiffeotopy hσ hfp hA hΔ hx).pathIntegral_interiorₗ_velocity_eq_zero s
    hc hc₀₁

end IsEhresmannConnection

end TauCeti

end
