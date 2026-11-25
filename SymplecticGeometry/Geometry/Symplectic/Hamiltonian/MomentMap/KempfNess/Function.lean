/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import SymplecticGeometry.Geometry.Lie.Complexification
public import TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Basic
import SymplecticGeometry.Geometry.Manifold.ContMDiff.Dual
import TauCeti.Analysis.Calculus.IntervalIntegral.ParametricPrimitive

/-!
# The Kempf–Ness function

Let `C : LieComplexification I G IC Gc` be a complexification of a real Lie group `G`, let `Gc`
act on `M`, and let `μ : M → 𝔤*` be a map. In the applications `μ` is a moment map for the action
of `G` with the opposite of Tau Ceti's sign: `-μ` is the moment map in Tau Ceti's sense, that is
`σ.IsEquivariantMomentMap (fun x ↦ -μ x)`. With this sign `Φ_p` is convex along the curves
`t ↦ g * C.expI (t • ξ)`; a moment map in Tau Ceti's sense passed as `μ` gives `-Φ_p` instead,
which is concave along them.

For `p : M`, the *Kempf–Ness function* `Φ_p : Gc → ℝ` is defined through the polar decomposition
`Gc = exp(i𝔤) G` of `C.polar`: for `ξ ∈ 𝔤` and `u ∈ G`,

  `Φ_p (exp(iξ) u) = ∫ t in 0..1, ⟨μ (exp(-itξ) p), ξ⟩`,

where `exp(iξ)` is `C.expI ξ`. This file defines `Φ_p`, shows that it vanishes on `G` and that it
is invariant under right multiplication by `G`, so that it descends to the space `Gc ⧸ G` of
cosets `gG`, and shows that it is smooth when the action and the components of `μ` are.

## Main definitions

* `SymplecticGeometry.kempfNessFunction C μ p`: the Kempf–Ness function `Φ_p : Gc → ℝ`.
* `SymplecticGeometry.kempfNessFunctionQuotient C μ p`: the function that `Φ_p` induces on
  `Gc ⧸ C.toHom.range`.

## Main results

* `SymplecticGeometry.kempfNessFunction_polar`,
  `SymplecticGeometry.kempfNessFunction_expI_mul_toHom`: the value of `Φ_p` at
  `C.polar (ξ, u) = C.expI ξ * C.toHom u`.
* `SymplecticGeometry.kempfNessFunction_toHom`: `Φ_p` vanishes on `G`.
* `SymplecticGeometry.kempfNessFunction_mul_toHom`: `Φ_p (g * C.toHom u) = Φ_p g`.
* `SymplecticGeometry.kempfNessFunctionQuotient_mk`: the induced function on cosets agrees with
  `Φ_p` on representatives.
* `SymplecticGeometry.contMDiff_kempfNessFunction`: `Φ_p` is smooth.
* `SymplecticGeometry.moment_inv_smul_im_mfderiv_polar_smul`: on the velocity of the radial curve
  `τ ↦ C.polar (τ • ξ, u)` at `t`, the one-form `ĝ ↦ μ (g⁻¹ • p) (C.im (g⁻¹ ĝ))` takes the value
  `μ (C.expI (-(t • ξ)) • p) ξ` of the integrand of `Φ_p (C.polar (ξ, u))`.

The smoothness reads `Φ_p` through the diffeomorphism `C.polar` as the integral over `[0, 1]` of a
smooth function on `𝔤 × ℝ`, and applies Tau Ceti's
`intervalIntegral.contDiff_parametric_primitive_of_contDiff` to it.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §5.7.
* [V. Georgoulas, J. W. Robbin and D. A. Salamon, *The Moment-Weight Inequality and the
  Hilbert–Mumford Criterion*][GeorgoulasRobbinSalamon2021], §2.
-/

public section

noncomputable section

open scoped Manifold ContDiff

namespace SymplecticGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {EC : Type*} [NormedAddCommGroup EC] [NormedSpace ℝ EC] [CompleteSpace EC]
  {HC : Type*} [TopologicalSpace HC] {IC : ModelWithCorners ℝ EC HC}
  {Gc : Type*} [TopologicalSpace Gc] [ChartedSpace HC Gc] [Group Gc] [LieGroup IC ∞ Gc]
  [T2Space Gc] [BoundarylessManifold IC Gc]
  {M : Type*} [MulAction Gc M]

/-- The *Kempf–Ness function* `Φ_p : Gc → ℝ` of `p : M` for the map `μ : M → 𝔤*`: writing
`g = C.expI ξ * C.toHom u` through the polar decomposition `C.polar`, its value at `g` is
`∫ t in 0..1, μ (C.expI (-(t • ξ)) • p) ξ`.

The intended `μ` has the opposite of Tau Ceti's sign, `σ.IsEquivariantMomentMap (fun x ↦ -μ x)`;
with that sign `Φ_p` is convex along the curves `t ↦ g * C.expI (t • ξ)`. -/
def kempfNessFunction (C : LieComplexification I G IC Gc)
    (μ : M → Module.Dual ℝ (GroupLieAlgebra I G)) (p : M) (g : Gc) : ℝ :=
  let ξ : GroupLieAlgebra I G := (C.polar.symm g).1
  ∫ t in (0 : ℝ)..1, μ (C.expI (-(t • ξ)) • p) ξ

variable (C : LieComplexification I G IC Gc) (μ : M → Module.Dual ℝ (GroupLieAlgebra I G))
  (p : M)

theorem kempfNessFunction_def (g : Gc) :
    kempfNessFunction C μ p g =
      let ξ : GroupLieAlgebra I G := (C.polar.symm g).1
      ∫ t in (0 : ℝ)..1, μ (C.expI (-(t • ξ)) • p) ξ :=
  (rfl)

/-- The defining property of the Kempf–Ness function, at the point `C.polar (ξ, u)` of the polar
decomposition. -/
theorem kempfNessFunction_polar (ξ : GroupLieAlgebra I G) (u : G) :
    kempfNessFunction C μ p (C.polar (ξ, u)) =
      ∫ t in (0 : ℝ)..1, μ (C.expI (-(t • ξ)) • p) ξ := by
  rw [kempfNessFunction_def, C.polar_apply, C.polar_symm_expI_mul_toHom]

/-- `Φ_p (C.expI ξ * C.toHom u) = ∫ t in 0..1, μ (C.expI (-(t • ξ)) • p) ξ`. -/
theorem kempfNessFunction_expI_mul_toHom (ξ : GroupLieAlgebra I G) (u : G) :
    kempfNessFunction C μ p (C.expI ξ * C.toHom u) =
      ∫ t in (0 : ℝ)..1, μ (C.expI (-(t • ξ)) • p) ξ := by
  rw [← C.polar_apply, kempfNessFunction_polar]

/-- `Φ_p (C.expI ξ) = ∫ t in 0..1, μ (C.expI (-(t • ξ)) • p) ξ`. -/
theorem kempfNessFunction_expI (ξ : GroupLieAlgebra I G) :
    kempfNessFunction C μ p (C.expI ξ) = ∫ t in (0 : ℝ)..1, μ (C.expI (-(t • ξ)) • p) ξ := by
  simpa using kempfNessFunction_expI_mul_toHom C μ p ξ 1

/-- The Kempf–Ness function vanishes on `G`. -/
@[simp]
theorem kempfNessFunction_toHom (u : G) : kempfNessFunction C μ p (C.toHom u) = 0 := by
  simpa [C.expI_zero] using kempfNessFunction_expI_mul_toHom C μ p 0 u

@[simp]
theorem kempfNessFunction_one : kempfNessFunction C μ p 1 = 0 := by
  simpa using kempfNessFunction_toHom C μ p 1

/-- The Kempf–Ness function is invariant under right multiplication by `G`:
`Φ_p (g * C.toHom u) = Φ_p g`. -/
@[simp]
theorem kempfNessFunction_mul_toHom (g : Gc) (u : G) :
    kempfNessFunction C μ p (g * C.toHom u) = kempfNessFunction C μ p g := by
  obtain ⟨ξ, v, rfl⟩ : ∃ (ξ : GroupLieAlgebra I G) (v : G), C.expI ξ * C.toHom v = g :=
    ⟨_, _, C.expI_mul_toHom_polar_symm g⟩
  rw [mul_assoc, ← map_mul, kempfNessFunction_expI_mul_toHom,
    kempfNessFunction_expI_mul_toHom]

/-- The function that the Kempf–Ness function induces on the space `Gc ⧸ C.toHom.range` of cosets
`g G`, well defined by `kempfNessFunction_mul_toHom`. -/
def kempfNessFunctionQuotient : Gc ⧸ C.toHom.range → ℝ :=
  Quotient.lift (kempfNessFunction C μ p) fun g g' h ↦ by
    obtain ⟨u, hu⟩ := QuotientGroup.leftRel_apply.1 h
    rw [ContMDiffMonoidMorphism.coe_toMonoidHom] at hu
    rw [← mul_inv_cancel_left g g', ← hu, kempfNessFunction_mul_toHom]

@[simp]
theorem kempfNessFunctionQuotient_mk (g : Gc) :
    kempfNessFunctionQuotient C μ p (g : Gc ⧸ C.toHom.range) = kempfNessFunction C μ p g :=
  (rfl)

section OneForm

open TauCeti

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ EC] [ConnectedSpace G]

/-- Along the radial curve `τ ↦ C.polar (τ • ξ, u)` of the polar decomposition, the one-form
`ĝ ↦ μ (g⁻¹ • p) (C.im (g⁻¹ ĝ))` on `Gc` takes on the velocity at `t` the value
`μ (C.expI (-(t • ξ)) • p) ξ`, the integrand that defines `kempfNessFunction` at
`C.polar (ξ, u)`. Here `g⁻¹ ĝ` is the left translate `mfderiv IC IC (g⁻¹ * ·) g ĝ` of `ĝ` to the
identity, and `μ` is assumed equivariant along `C.toHom` for the coadjoint action of `G`, as
`IsComplexifiedAction.moment_toHom_smul` shows for the intended `μ`. -/
theorem moment_inv_smul_im_mfderiv_polar_smul
    (hμ : ∀ (u : G) (x : M), μ (C.toHom u • x) = Lie.coadjointRepresentation ℝ I G u (μ x))
    (ξ : GroupLieAlgebra I G) (u : G) (t : ℝ) :
    μ ((C.polar (t • ξ, u))⁻¹ • p)
        (C.im (mfderiv IC IC ((C.polar (t • ξ, u))⁻¹ * ·) (C.polar (t • ξ, u))
          (mfderiv 𝓘(ℝ) IC (fun τ : ℝ ↦ C.polar (τ • ξ, u)) t (1 : ℝ)))) =
      μ (C.expI (-(t • ξ)) • p) ξ := by
  rw [funext fun τ : ℝ ↦ C.polar_apply (τ • ξ) u, C.polar_apply,
    C.mfderiv_inv_mul_mfderiv_expI_smul_mul_toHom, C.im_cplx_lieMap, mul_inv_rev, ← map_inv,
    ← C.expI_neg, mul_smul, hμ, Lie.coadjointRepresentation_apply, inv_inv,
    ← Lie.tangentAd_apply, Lie.tangentAd_inv, LieEquiv.apply_symm_apply]

end OneForm

section Smooth

variable [FiniteDimensional ℝ E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  [TopologicalSpace M] [ChartedSpace H' M] [ContMDiffSMul IC I' ∞ Gc M]

/-- The Kempf–Ness function is smooth on `Gc` when `Gc` acts smoothly on `M` and each component
`x ↦ μ x ξ` of `μ` is smooth, as for a moment map (Tau Ceti's `IsMomentMap.contMDiff`). -/
theorem contMDiff_kempfNessFunction (hμ : ∀ ξ, ContMDiff I' 𝓘(ℝ) ∞ fun x ↦ μ x ξ) :
    ContMDiff IC 𝓘(ℝ) ∞ (kempfNessFunction C μ p) := by
  -- The integrand `(ξ, t) ↦ μ (C.expI (-(t • ξ)) • p) ξ`, on the model space `E × ℝ`.
  have hx : ContMDiff 𝓘(ℝ, E × ℝ) I' ∞ fun q : E × ℝ ↦ C.expI (-(q.2 • q.1)) • p :=
    (C.contMDiff_expI.comp (contDiff_snd.smul contDiff_fst).neg.contMDiff).smul contMDiff_const
  have hF : ContDiff ℝ ∞ (Function.uncurry fun (ξ : E) (t : ℝ) ↦
      μ (C.expI (-(t • ξ)) • p) ξ) :=
    contMDiff_iff_contDiff.1 <|
      ((contMDiff_toContinuousLinearMap_of_contMDiff_apply (E := E) hμ).comp hx).clm_apply
        contDiff_fst.contMDiff
  -- Its integral over `[0, 1]`, a smooth function of `ξ`, composed with `g ↦ (C.polar.symm g).1`.
  have hΦ := (intervalIntegral.contDiff_parametric_primitive_of_contDiff hF 0).comp
    (contDiff_id.prodMk (contDiff_const (c := (1 : ℝ))))
  refine (hΦ.contMDiff.comp (contMDiff_fst.comp C.polar.symm.contMDiff)).congr fun g ↦ ?_
  rw [kempfNessFunction_def]
  -- The sides differ only in the type of `(C.polar.symm g).1`: the model space `E` on the left,
  -- the Lie algebra `GroupLieAlgebra I G` on the right, which is `E` by definition.
  rfl

end Smooth

end SymplecticGeometry

end
