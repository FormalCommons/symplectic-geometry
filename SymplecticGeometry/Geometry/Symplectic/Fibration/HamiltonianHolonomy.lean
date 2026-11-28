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
  have hC : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ × ℝ) IM C (s, t, θ) :=
    (hD.contMDiffAt_transportedCylinder hf hfp he_symm hΔ hc hs).mdifferentiableAt (by simp)
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
  have hℓ : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) (fun θ' : ℝ ↦ (s, t, θ')) θ
      ((1 : ℝ →L[ℝ] ℝ).smulRight ((0, 0, 1) : ℝ × ℝ × ℝ)) :=
    hasMFDerivAt_iff_hasFDerivAt.2 (HasDerivAt.prodMk (hasDerivAt_const θ s)
      ((hasDerivAt_const θ t).prodMk (hasDerivAt_id θ))).hasFDerivAt
  have hCℓ := hC.hasMFDerivAt.comp θ hℓ
  have hderiv : deriv (fun θ' ↦ τ.val (C (s, t, θ'))
      ![hD.horizontalLiftField v₁ (C (s, t, θ')), hD.horizontalLiftField v₂ (C (s, t, θ'))]) θ =
        mfderiv IM 𝓘(ℝ)
          (fun y ↦ τ.val y ![hD.horizontalLiftField v₁ y, hD.horizontalLiftField v₂ y])
          (C (s, t, θ)) (mfderiv 𝓘(ℝ, ℝ × ℝ × ℝ) IM C (s, t, θ) (0, 0, 1)) := by
    rw [← fderiv_apply_one_eq_deriv]
    refine (fderiv_comp_apply_eq_mfderiv (f := C ∘ fun θ' : ℝ ↦ (s, t, θ')) hg
      hCℓ.mdifferentiableAt 1).trans (congrArg _ ?_)
    rw [hCℓ.mfderiv]
    -- The vectors are typed as tangent vectors of `ℝ × ℝ × ℝ`, so `smulRight_apply` does not
    -- rewrite; the value of `smulRight 1 v` at `1` is `1 • v` by definition.
    exact congrArg (mfderiv 𝓘(ℝ, ℝ × ℝ × ℝ) IM C (s, t, θ)) (one_smul ℝ ((0, 0, 1) : ℝ × ℝ × ℝ))
  rw [hpb, hsplit, hderiv, ← mvfderiv_apply_eq_mfderiv_apply]
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

end IsEhresmannConnection

end TauCeti

end
