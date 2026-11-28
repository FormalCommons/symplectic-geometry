/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import SymplecticGeometry.Geometry.Lie.LeftTrivializedCurve.Deriv
public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.KempfNess.Basic
public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.NormSq
public import TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Basic
public import TauCeti.Algebra.GroupAction.OrbitRelQuotient
public import TauCeti.Geometry.Symplectic.Hamiltonian.EquivariantMomentMap.LevelAction
import SymplecticGeometry.Geometry.Lie.Adjoint.Differential
import SymplecticGeometry.Geometry.Lie.Complexification
import Mathlib.Analysis.Convex.Deriv
import SymplecticGeometry.Analysis.Calculus.ParametricIntervalIntegral
import SymplecticGeometry.Geometry.Lie.Exponential.Derivative
import SymplecticGeometry.Geometry.Manifold.ContMDiff.Dual
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Arith
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Constancy
import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.ContMDiff
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
cosets `gG`, shows that it is smooth when the action and the components of `μ` are, and computes
its differential: for a complexified action and an equivariant moment map `-μ`, the differential
of `Φ_p` at `g` is the one-form `ĝ ↦ μ (g⁻¹ • p) (C.im (g⁻¹ ĝ))`. Since `Gc` is connected, these two
properties determine `Φ_p`; its critical points are the `g` with `μ (g⁻¹ • p) = 0`, so `Φ_p` has a
critical point exactly when `p` is polystable. Along the curves `t ↦ g * C.expI (t • ξ)` its second
derivative is a squared norm, so `Φ_p` is convex along them. Finally, the zeros of `μ` in one
`Gc`-orbit form a single `G`-orbit, so the `G`-orbits of the zero level correspond bijectively to
the polystable `Gc`-orbits.

## Main definitions

* `SymplecticGeometry.kempfNessFunction C μ p`: the Kempf–Ness function `Φ_p : Gc → ℝ`.
* `SymplecticGeometry.kempfNessFunctionQuotient C μ p`: the function that `Φ_p` induces on
  `Gc ⧸ C.toHom.range`.
* `SymplecticGeometry.zeroLevelToPolystable C h hμ`: the inclusion of the zero level of `μ` into
  the polystable locus, equivariant along `C.toHom`.

## Main results

* `SymplecticGeometry.kempfNessFunction_polar`,
  `SymplecticGeometry.kempfNessFunction_expI_mul_toHom`: the value of `Φ_p` at
  `C.polar (ξ, u) = C.expI ξ * C.toHom u`.
* `SymplecticGeometry.kempfNessFunction_toHom`: `Φ_p` vanishes on `G`.
* `SymplecticGeometry.kempfNessFunction_mul_toHom`: `Φ_p (g * C.toHom u) = Φ_p g`.
* `SymplecticGeometry.kempfNessFunctionQuotient_mk`: the induced function on cosets agrees with
  `Φ_p` on representatives.
* `SymplecticGeometry.contDiff_moment_expI_neg_smul_smul_apply`: the integrand
  `(ξ, t) ↦ μ (C.expI (-(t • ξ)) • p) ξ` is smooth.
* `SymplecticGeometry.contMDiff_kempfNessFunction`: `Φ_p` is smooth.
* `SymplecticGeometry.moment_inv_smul_im_mfderiv_inv_mul_curveVelocity_polar_smul`: on the
  velocity of the radial curve `τ ↦ C.polar (τ • ξ, u)` at `t`, translated to the identity, the
  one-form `ĝ ↦ μ (g⁻¹ • p) (C.im (g⁻¹ ĝ))` takes the value `μ (C.expI (-(t • ξ)) • p) ξ` of the
  integrand of `Φ_p (C.polar (ξ, u))`.
* `SymplecticGeometry.mfderiv_kempfNessFunction`: the differential of `Φ_p` at `g` is
  `ĝ ↦ μ (g⁻¹ • p) (C.im (g⁻¹ ĝ))`.
* `SymplecticGeometry.hasDerivAt_kempfNessFunction_comp`: along a curve `c` differentiable at
  `s₀`, the derivative of `Φ_p ∘ c` at `s₀` is the one-form evaluated on the velocity of `c`.
* `SymplecticGeometry.HasLeftTrivializedDerivOn.hasDerivAt_kempfNessFunction`: the same, for a
  curve `c` with left-trivialized derivative `ξ` near `t`: the derivative is
  `μ ((c t)⁻¹ • p) (C.im (ξ t))`.
* `SymplecticGeometry.hasDerivAt_kempfNessFunction_geodesic`,
  `SymplecticGeometry.hasDerivAt_deriv_kempfNessFunction_geodesic`: along the curve
  `t ↦ g * C.expI (t • ξ)`, the first derivative of `Φ_p` is `μ (C.expI (-(t • ξ)) • g⁻¹ • p) ξ`
  and the second is the squared norm of the fundamental vector field of `ξ` at
  `C.expI (-(t • ξ)) • g⁻¹ • p`.
* `SymplecticGeometry.hasDerivAt_kempfNessFunction_expI_neg_smul`: the case `g = 1`, direction
  `-ξ`: along `t ↦ C.expI (-(t • ξ))` the derivative of `Φ_p` is `-μ (C.expI (t • ξ) • p) ξ`.
* `SymplecticGeometry.convexOn_kempfNessFunction_geodesic`: `Φ_p` is convex along these curves.
* `SymplecticGeometry.kempfNessFunction_add_moment_le`,
  `SymplecticGeometry.kempfNessFunction_sub_sqrt_momentNormSq_mul_sqrt_le`: the tangent line at
  `t = 0` bounds `Φ_p (g * C.expI η * C.toHom u)` below by `Φ_p g + μ (g⁻¹ • p) η`, and by
  Cauchy–Schwarz below by `Φ_p g - √(‖μ (g⁻¹ • p)‖²) * √(B η η)` for a symmetric nonnegative `B`.
* `SymplecticGeometry.kempfNessFunction_nonneg_of_moment_eq_zero`,
  `SymplecticGeometry.exists_pos_le_moment_expI_neg_smul_apply`,
  `SymplecticGeometry.mul_norm_sub_one_le_kempfNessFunction`: at a zero `p` of `μ`, `Φ_p ≥ 0`;
  if moreover the stabilizer of `p` in the Lie algebra is trivial, the slope
  `μ (C.expI (-ξ) • p) ξ` is at least some `c > 0` on unit vectors `ξ`, and then
  `Φ_p (C.expI η * C.toHom u) ≥ c (‖η‖ - 1)`.
* `SymplecticGeometry.eq_kempfNessFunction_of_mfderiv_eq`,
  `SymplecticGeometry.existsUnique_kempfNessFunction`: `Φ_p` is the only smooth function with this
  differential that vanishes on `G`; a differentiable one with this differential that vanishes at
  `1` is already `Φ_p`.
* `SymplecticGeometry.kempfNessFunction_mul`: the cocycle identity
  `Φ_p (a * g) = Φ_p a + Φ_{a⁻¹ • p} g`; by `SymplecticGeometry.kempfNessFunction_mul_of_smul_eq`,
  `Φ_p` is additive on the stabilizer of `p`.
* `SymplecticGeometry.mfderiv_kempfNessFunction_eq_zero_iff`: `g` is a critical point of `Φ_p`
  exactly when `μ (g⁻¹ • p) = 0`.
* `SymplecticGeometry.isPolystable_iff_exists_mfderiv_kempfNessFunction_eq_zero`: `p` is
  polystable exactly when `Φ_p` has a critical point.
* `SymplecticGeometry.exists_smul_eq_of_moment_eq_zero`: two zeros of `μ` in one `Gc`-orbit
  differ by an element of `G`.
* `SymplecticGeometry.bijective_zeroLevelOrbit_polystableOrbit`: the map from the `G`-orbits of
  the zero level to the `Gc`-orbits of polystable points, induced by the inclusion, is bijective.

The smoothness reads `Φ_p` through the diffeomorphism `C.polar` as the integral over `[0, 1]` of a
smooth function on `𝔤 × ℝ`, and applies Tau Ceti's
`intervalIntegral.contDiff_parametric_primitive_of_contDiff` to it.

The derivative follows [GeorgoulasRobbinSalamon2021], §2. Along a smooth curve `c`, write
`c s = C.polar (ξ s, u s)` and deform the curve `s ↦ C.toHom (u s)` in `G` to `c` through
`γ (s, t) = C.polar (t • ξ s, u s)`. Along `t` the one-form takes the value of the integrand
(`moment_inv_smul_im_mfderiv_inv_mul_curveVelocity_polar_smul`), so
`Φ_p (c s) = ∫ t in 0..1, A (s, t)` with `A` the one-form on `∂_t γ`. The closedness of the
one-form (`fderiv_moment_inv_smul_im_comm`) turns `∂_s A` into `∂_t B`, with `B` the one-form
on `∂_s γ`, so differentiating under the integral sign and integrating along `t`
(`intervalIntegral.hasDerivAt_integral_of_hasDerivAt_snd`) leaves
`B (s, 1) - B (s, 0)`. Here `B (s, 0) = 0` since
`γ (·, 0)` stays in `G` (`LieComplexification.im_mfderiv_inv_mul_mfderiv_toHom_comp`), and
`B (s, 1)` is the one-form on the velocity of `c`. The differential at `g` is read along the curve
`s ↦ g * exp (s • g⁻¹ ĝ)` with Tau Ceti's
`HasMFDerivAt.hasDerivAt_comp_mul_mulInvariantExp_smul_zero`, and the derivative along any curve
differentiable at a point then follows by the chain rule.

Along `t ↦ g * C.expI (t • ξ)`, a left translate of a one-parameter subgroup whose
left-trivialized velocity is `C.cplx (C.lieMap ξ)`, the derivative of `Φ_p` is read off
`hasDerivAt_kempfNessFunction_comp`; its derivative in turn is `hasDerivAt_moment_expI` at
`g⁻¹ • p` and time `-t`, and convexity follows from the monotonicity of the first derivative
(`antitone_moment_expI`). The slope of this convex function at `t = 0` is `μ (g⁻¹ • p) η`, and
Mathlib's `ConvexOn.le_slope_of_hasDerivAt` bounds it by the slope of the secant from `0` to `1`;
the Cauchy–Schwarz inequality `abs_apply_le_sqrt_momentNormSq_mul_sqrt` gives the form with
norms.

For the cocycle identity, `g ↦ Φ_p (a * g) - Φ_p a` vanishes at `1`, and since left translation
commutes with the left-trivialized derivative (`TauCeti.Lie.mfderiv_inv_mul_mfderiv_mul_left`) it
has the differential of `Φ_{a⁻¹ • p}`, so `eq_kempfNessFunction_of_mfderiv_eq` identifies the
two.

For two zeros `x` and `y = C.expI ξ • C.toHom u • x` of `μ` in one orbit, `μ` vanishes at
`C.toHom u • x` by equivariance, and `expI_smul_eq_self_of_moment_apply_le` shows that
`C.expI ξ` fixes it: the antitone function `t ↦ μ (C.expI (t • ξ) • x) ξ` does not drop from
`0` to `1`, so it is constant on `[0, 1]`, `X_ξ` vanishes along the curve and the curve is
constant. The map of orbit sets is Tau Ceti's `MulActionHom.orbitRelQuotientMap` of
`zeroLevelToPolystable`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §5.7.
* [V. Georgoulas, J. W. Robbin and D. A. Salamon, *The Moment-Weight Inequality and the
  Hilbert–Mumford Criterion*][GeorgoulasRobbinSalamon2021], §2.
-/

public section

noncomputable section

open scoped Manifold ContDiff Topology

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

variable [FiniteDimensional ℝ E] [ConnectedSpace G]

/-- Along the radial curve `τ ↦ C.polar (τ • ξ, u)` of the polar decomposition, the one-form
`ĝ ↦ μ (g⁻¹ • p) (C.im (g⁻¹ ĝ))` on `Gc` takes on the velocity at `t` the value
`μ (C.expI (-(t • ξ)) • p) ξ`, the integrand that defines `kempfNessFunction` at
`C.polar (ξ, u)`. Here `g⁻¹ ĝ` is the left translate `mfderiv IC IC (g⁻¹ * ·) g ĝ` of `ĝ` to the
identity, and `μ` is assumed equivariant along `C.toHom` for the coadjoint action of `G`, as
`IsComplexifiedAction.moment_toHom_smul` shows for the intended `μ`. -/
theorem moment_inv_smul_im_mfderiv_inv_mul_curveVelocity_polar_smul
    (hμ : ∀ (u : G) (x : M), μ (C.toHom u • x) = Lie.coadjointRepresentation ℝ I G u (μ x))
    (ξ : GroupLieAlgebra I G) (u : G) (t : ℝ) :
    μ ((C.polar (t • ξ, u))⁻¹ • p)
        (C.im (mfderiv IC IC ((C.polar (t • ξ, u))⁻¹ * ·) (C.polar (t • ξ, u))
          (Manifold.curveVelocity IC (fun τ : ℝ ↦ C.polar (τ • ξ, u)) t))) =
      μ (C.expI (-(t • ξ)) • p) ξ := by
  have := C.finiteDimensional
  rw [funext fun τ : ℝ ↦ C.polar_apply (τ • ξ) u, C.polar_apply,
    C.mfderiv_inv_mul_curveVelocity_expI_smul_mul_toHom, C.im_cplx_lieMap, mul_inv_rev, ← map_inv,
    ← C.expI_neg, mul_smul, hμ, Lie.coadjointRepresentation_apply, inv_inv,
    ← Lie.tangentAd_apply, Lie.tangentAd_inv, LieEquiv.apply_symm_apply]

end OneForm

section Smooth

variable [FiniteDimensional ℝ E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  [TopologicalSpace M] [ChartedSpace H' M] [ContMDiffSMul IC I' ∞ Gc M]

/-- The integrand `(ξ, t) ↦ μ (C.expI (-(t • ξ)) • p) ξ` of the Kempf–Ness function, read on the
model space `E × ℝ`, is smooth when `Gc` acts smoothly on `M` and each component `x ↦ μ x ξ` of
`μ` is smooth. -/
theorem contDiff_moment_expI_neg_smul_smul_apply (hμ : ∀ ξ, ContMDiff I' 𝓘(ℝ) ∞ fun x ↦ μ x ξ) :
    ContDiff ℝ ∞ fun q : E × ℝ ↦ μ (C.expI (-(q.2 • q.1)) • p) q.1 := by
  have hx : ContMDiff 𝓘(ℝ, E × ℝ) I' ∞ fun q : E × ℝ ↦ C.expI (-(q.2 • q.1)) • p :=
    (C.contMDiff_expI.comp (contDiff_snd.smul contDiff_fst).neg.contMDiff).smul contMDiff_const
  exact contMDiff_iff_contDiff.1 <| contMDiff_dual_comp_apply (X := E) hμ hx contDiff_fst.contMDiff

/-- The Kempf–Ness function is smooth on `Gc` when `Gc` acts smoothly on `M` and each component
`x ↦ μ x ξ` of `μ` is smooth, as for a moment map (Tau Ceti's `IsMomentMap.contMDiff`). -/
theorem contMDiff_kempfNessFunction (hμ : ∀ ξ, ContMDiff I' 𝓘(ℝ) ∞ fun x ↦ μ x ξ) :
    ContMDiff IC 𝓘(ℝ) ∞ (kempfNessFunction C μ p) := by
  have hF : ContDiff ℝ ∞ (Function.uncurry fun (ξ : E) (t : ℝ) ↦
      μ (C.expI (-(t • ξ)) • p) ξ) :=
    contDiff_moment_expI_neg_smul_smul_apply C μ p hμ
  -- Its integral over `[0, 1]`, a smooth function of `ξ`, composed with `g ↦ (C.polar.symm g).1`.
  have hΦ := (intervalIntegral.contDiff_parametric_primitive_of_contDiff hF 0).comp
    (contDiff_id.prodMk (contDiff_const (c := (1 : ℝ))))
  refine (hΦ.contMDiff.comp (contMDiff_fst.comp C.polar.symm.contMDiff)).congr fun g ↦ ?_
  rw [kempfNessFunction_def]
  -- The sides differ only in the type of `(C.polar.symm g).1`: the model space `E` on the left,
  -- the Lie algebra `GroupLieAlgebra I G` on the right, which is `E` by definition.
  rfl

end Smooth

section Derivative

open _root_.Bundle TauCeti TauCeti.Manifold
open scoped RealInnerProductSpace GroupLieAlgebra

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable [FiniteDimensional ℝ E] [ConnectedSpace G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [MulAction G M]
  [ContMDiffSMul I I' ∞ G M] [ContMDiffSMul IC I' ∞ Gc M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I' x)]
  {σ : SmoothTwoForm I' M} {J : SmoothAlmostComplexStructure I' M}

/-- Along a smooth curve `c` in `Gc`, `s ↦ Φ_p (c s)` has at `s₀` the derivative
`μ ((c s₀)⁻¹ • p) (C.im ((c s₀)⁻¹ ċ))`. This is the step of `mfderiv_kempfNessFunction` that
deforms `c` to a curve in `G` through the polar decomposition. -/
private theorem hasDerivAt_kempfNessFunction_comp_of_contMDiff (h : IsComplexifiedAction C J)
    (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w))
    {c : ℝ → Gc} (hc : ContMDiff 𝓘(ℝ) IC ∞ c) (s₀ : ℝ) :
    HasDerivAt (kempfNessFunction C μ p ∘ c)
      (μ ((c s₀)⁻¹ • p)
        (C.im (mfderiv IC IC ((c s₀)⁻¹ * ·) (c s₀) (curveVelocity IC c s₀)))) s₀ := by
  have hμc : ∀ ξ, ContMDiff I' 𝓘(ℝ) ∞ fun x ↦ μ x ξ := hμ.toIsMomentMap.contMDiff_of_neg
  -- The polar components of `c`, and the homotopy `γ (s, t) = C.polar (t • ξ s, u s)` from the
  -- curve `s ↦ C.toHom (u s)` in `G` to `c`.
  set ξ : ℝ → GroupLieAlgebra I G := fun s ↦ (C.polar.symm (c s)).1
  set u : ℝ → G := fun s ↦ (C.polar.symm (c s)).2
  set γ : ℝ × ℝ → Gc := fun z ↦ C.polar (z.2 • ξ z.1, u z.1)
  have hpc : ContMDiff 𝓘(ℝ) (𝓘(ℝ, E).prod I) ∞ fun s ↦ C.polar.symm (c s) :=
    C.polar.symm.contMDiff.comp hc
  have hξ : ContDiff ℝ ∞ fun s ↦ (C.polar.symm (c s)).1 :=
    contMDiff_iff_contDiff.1 (contMDiff_fst.comp hpc)
  have hu : ContMDiff 𝓘(ℝ) I ∞ u := contMDiff_snd.comp hpc
  have hγ : ContMDiff 𝓘(ℝ, ℝ × ℝ) IC ∞ γ :=
    C.polar.contMDiff.comp ((contDiff_snd.smul (hξ.comp contDiff_fst)).contMDiff.prodMk
      (hu.comp contDiff_fst.contMDiff))
  have hγd (z : ℝ × ℝ) : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) IC γ z := hγ.mdifferentiableAt (by simp)
  -- The one-form along `γ` in the direction `v`, and the integrand `A` of `Φ_p (c s)`.
  set α : ℝ × ℝ → ℝ × ℝ → ℝ := fun v z ↦ μ ((γ z)⁻¹ • p)
    (C.im (mfderiv IC IC ((γ z)⁻¹ * ·) (γ z) (mfderiv 𝓘(ℝ, ℝ × ℝ) IC γ z v)))
  set A : ℝ × ℝ → ℝ := fun z ↦ μ (C.expI (-(z.2 • ξ z.1)) • p) (ξ z.1)
  have hAs : ContDiff ℝ ∞ A :=
    (contDiff_moment_expI_neg_smul_smul_apply C μ p hμc).comp
      ((hξ.comp contDiff_fst).prodMk contDiff_snd)
  -- The curve `q ↦ γ (q, t)` has velocity `∂_s γ`.
  have hfst (s t : ℝ) : mfderiv 𝓘(ℝ, ℝ × ℝ) IC γ (s, t) (1, 0) =
      curveVelocity IC (fun q ↦ γ (q, t)) s :=
    (curveVelocity_eq_mfderiv_fst (f := fun a b ↦ γ (a, b)) (hγd (s, t))).symm
  -- Along `t`, the one-form is the integrand
  -- (`moment_inv_smul_im_mfderiv_inv_mul_curveVelocity_polar_smul`).
  have hA : α (0, 1) = A := by
    funext ⟨s, t⟩
    have hv : mfderiv 𝓘(ℝ, ℝ × ℝ) IC γ (s, t) (0, 1) =
        curveVelocity IC (fun τ ↦ γ (s, τ)) t :=
      (curveVelocity_eq_mfderiv_snd (f := fun a b ↦ γ (a, b)) (hγd (s, t))).symm
    -- `change` unfolds the local definition `α` to expose the velocity that `hv` rewrites.
    change μ ((γ (s, t))⁻¹ • p) (C.im (mfderiv IC IC ((γ (s, t))⁻¹ * ·) (γ (s, t))
      (mfderiv 𝓘(ℝ, ℝ × ℝ) IC γ (s, t) (0, 1)))) = A (s, t)
    rw [hv]
    exact moment_inv_smul_im_mfderiv_inv_mul_curveVelocity_polar_smul C μ p
      (h.moment_toHom_smul hμ) (ξ s) (u s) t
  -- Differentiating under the integral sign, the closedness of the one-form trades `∂_s A` for
  -- `∂_t (α (1, 0))`, and the fundamental theorem of calculus evaluates the integral.
  have hD : HasDerivAt (kempfNessFunction C μ p ∘ c)
      (α (1, 0) (s₀, 1) - α (1, 0) (s₀, 0)) s₀ := by
    refine (intervalIntegral.hasDerivAt_integral_of_hasDerivAt_snd (B := α (1, 0))
      isOpen_univ (hAs.of_le (by simp)).contDiffOn (Set.subset_univ _)
      fun t _ ↦ ?_).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun s ↦ by simp [kempfNessFunction_def, A, ξ])
    rw [← hA, fderiv_moment_inv_smul_im_comm h hμ hg p hγ (s₀, t) (1, 0) (0, 1)]
    exact ((differentiable_moment_inv_smul_im_mfderiv hμc p hγ (1, 0) (s₀, t)).hasFDerivAt.comp t
      (hasFDerivAt_prodMk_right s₀ t)).hasDerivAt
  -- At `t = 0` the homotopy stays in `G`, where `C.im` vanishes on left-trivialized velocities.
  have hB0 : α (1, 0) (s₀, 0) = 0 := by
    have hγ0 : (fun q ↦ γ (q, 0)) = C.toHom ∘ u := by
      funext q
      simp [γ]
    have hγ00 : γ (s₀, 0) = C.toHom (u s₀) := congrFun hγ0 s₀
    -- `change` unfolds the local definition `α` to expose `γ (s₀, 0)` and the velocity.
    change μ ((γ (s₀, 0))⁻¹ • p) (C.im (mfderiv IC IC ((γ (s₀, 0))⁻¹ * ·) (γ (s₀, 0))
      (mfderiv 𝓘(ℝ, ℝ × ℝ) IC γ (s₀, 0) (1, 0)))) = 0
    rw [hfst, hγ0, hγ00, curveVelocity_apply,
      C.im_mfderiv_inv_mul_mfderiv_toHom_comp (hu.mdifferentiableAt (by simp)) (1 : ℝ), map_zero]
  -- At `t = 1` the homotopy is the curve `c`.
  have hγ1 : (fun q ↦ γ (q, 1)) = c := by
    funext q
    have hq : (((1 : ℝ) • ξ q : E), u q) = C.polar.symm (c q) := Prod.ext (one_smul ℝ _) rfl
    exact (congrArg C.polar hq).trans (C.polar.apply_symm_apply (c q))
  have hB1 : α (1, 0) (s₀, 1) = μ ((c s₀)⁻¹ • p)
      (C.im (mfderiv IC IC ((c s₀)⁻¹ * ·) (c s₀) (curveVelocity IC c s₀))) := by
    -- `change` unfolds the local definition `α` to expose `γ (s₀, 1)` and the velocity.
    change μ ((γ (s₀, 1))⁻¹ • p) (C.im (mfderiv IC IC ((γ (s₀, 1))⁻¹ * ·) (γ (s₀, 1))
      (mfderiv 𝓘(ℝ, ℝ × ℝ) IC γ (s₀, 1) (1, 0)))) = _
    rw [hfst, hγ1, congrFun hγ1 s₀]
  rwa [hB1, hB0, sub_zero] at hD

/-- **The derivative of the Kempf–Ness function.** Let the action of `Gc` be a complexified
action, let `-μ` be an equivariant moment map for `σ`, and let the metric be
`g(u, w) = σ(u, J w)`. Then the differential of `Φ_p` at `g` is the one-form
`ĝ ↦ μ (g⁻¹ • p) (C.im (g⁻¹ ĝ))`, where `g⁻¹ ĝ` is the left translate
`mfderiv IC IC (g⁻¹ * ·) g ĝ` of `ĝ` to the identity. -/
theorem mfderiv_kempfNessFunction (h : IsComplexifiedAction C J)
    (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w))
    (g : Gc) (ĝ : TangentSpace IC g) :
    mfderiv IC 𝓘(ℝ) (kempfNessFunction C μ p) g ĝ =
      μ (g⁻¹ • p) (C.im (mfderiv IC IC (g⁻¹ * ·) g ĝ)) := by
  -- Along the curve `s ↦ g * exp (s • g⁻¹ ĝ)`, which passes through `g` with velocity `ĝ`.
  set ζ : GroupLieAlgebra IC Gc := mfderiv IC IC (g⁻¹ * ·) g ĝ
  have hΦ := ((contMDiff_kempfNessFunction C μ p hμ.toIsMomentMap.contMDiff_of_neg)
    |>.mdifferentiableAt (x := g) (by simp)).hasMFDerivAt
    |>.hasDerivAt_comp_mul_mulInvariantExp_smul_zero ζ
  rw [mulInvariantVectorField_mfderiv_inv_mul] at hΦ
  have h' := hΦ.unique (hasDerivAt_kempfNessFunction_comp_of_contMDiff C μ p h hμ hg
    (c := fun s ↦ g * mulInvariantExp (s • ζ))
    (contMDiff_const.mul (contMDiff_mulInvariantExp_smul ζ)) 0)
  rwa [mfderiv_inv_mul_curveVelocity_mul_mulInvariantExp_smul, zero_smul, mulInvariantExp_zero,
    mul_one] at h'

/-- **The derivative of the Kempf–Ness function along a curve.** Let the action of `Gc` be a
complexified action, let `-μ` be an equivariant moment map for `σ`, and let the metric be
`g(u, w) = σ(u, J w)`. If a curve `c` in `Gc` is differentiable at `s₀`, then `s ↦ Φ_p (c s)` has
at `s₀` the derivative `μ ((c s₀)⁻¹ • p) (C.im ((c s₀)⁻¹ ċ))`, where `(c s₀)⁻¹ ċ` is the velocity
of `c` at `s₀` translated to the identity. -/
theorem hasDerivAt_kempfNessFunction_comp (h : IsComplexifiedAction C J)
    (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w))
    {c : ℝ → Gc} {s₀ : ℝ} (hc : MDifferentiableAt 𝓘(ℝ) IC c s₀) :
    HasDerivAt (kempfNessFunction C μ p ∘ c)
      (μ ((c s₀)⁻¹ • p)
        (C.im (mfderiv IC IC ((c s₀)⁻¹ * ·) (c s₀) (curveVelocity IC c s₀)))) s₀ := by
  have hΦ := hasDerivAt_comp_curve
    ((contMDiff_kempfNessFunction C μ p hμ.toIsMomentMap.contMDiff_of_neg).mdifferentiableAt
      (x := c s₀) (by simp)) (hasMFDerivAt_curveVelocity hc)
  rwa [mvfderiv, ContinuousLinearMap.comp_apply, mfderiv_kempfNessFunction C μ p h hμ hg] at hΦ

/-- **The derivative of the Kempf–Ness function along a curve with left-trivialized derivative.**
Let the action of `Gc` be a complexified action, let `-μ` be an equivariant moment map for `σ`,
and let the metric be `g(u, w) = σ(u, J w)`. If a curve `c` in `Gc` has left-trivialized
derivative `ξ` on a neighbourhood `s` of `t`, then `u ↦ Φ_p (c u)` has at `t` the derivative
`μ ((c t)⁻¹ • p) (C.im (ξ t))`. -/
theorem HasLeftTrivializedDerivOn.hasDerivAt_kempfNessFunction {c : ℝ → Gc}
    {ξ : ℝ → GroupLieAlgebra IC Gc} {s : Set ℝ} (hc : HasLeftTrivializedDerivOn c ξ s)
    (h : IsComplexifiedAction C J) (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w)) {t : ℝ}
    (hs : s ∈ 𝓝 t) :
    HasDerivAt (fun u ↦ kempfNessFunction C μ p (c u)) (μ ((c t)⁻¹ • p) (C.im (ξ t))) t := by
  have hΦ := hasDerivAt_kempfNessFunction_comp C μ p h hμ hg (hc.mdifferentiableAt hs)
  rwa [hc.mfderiv_inv_mul_curveVelocity hs] at hΦ

/-- **The derivative of the Kempf–Ness function along a geodesic.** Let the action of `Gc` be a
complexified action, let `-μ` be an equivariant moment map for `σ`, and let the metric be
`g(u, w) = σ(u, J w)`. Then `t ↦ Φ_p (g * C.expI (t • ξ))` has at `t` the derivative
`μ (C.expI (-(t • ξ)) • g⁻¹ • p) ξ`. -/
theorem hasDerivAt_kempfNessFunction_geodesic (h : IsComplexifiedAction C J)
    (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w))
    (g : Gc) (ξ : GroupLieAlgebra I G) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ kempfNessFunction C μ p (g * C.expI (s • ξ)))
      (μ (C.expI (-(t • ξ)) • g⁻¹ • p) ξ) t := by
  -- The curve is `s ↦ g * exp (s • ζ)` for the invariant direction `ζ = C.cplx (C.lieMap ξ)`.
  set ζ : GroupLieAlgebra IC Gc := C.cplx (C.lieMap ξ)
  have hexp (s : ℝ) : C.expI (s • ξ) = mulInvariantExp (s • ζ) := C.expI_smul s ξ
  have hc : MDifferentiableAt 𝓘(ℝ) IC (fun s ↦ g * mulInvariantExp (s • ζ)) t :=
    (contMDiff_const.mul (contMDiff_mulInvariantExp_smul ζ)).mdifferentiableAt (by simp)
  have hD := hasDerivAt_kempfNessFunction_comp C μ p h hμ hg hc
  rw [mfderiv_inv_mul_curveVelocity_mul_mulInvariantExp_smul, C.im_cplx_lieMap, mul_inv_rev,
    mul_smul, ← hexp, ← C.expI_neg] at hD
  simpa only [Function.comp_def, hexp] using hD

/-- The derivative of `t ↦ Φ_p (C.expI (-(t • ξ)))` at `t` is `-μ (C.expI (t • ξ) • p) ξ`, for a
complexified action, with `-μ` an equivariant moment map for `σ` and the metric
`g(u, w) = σ(u, J w)`. -/
theorem hasDerivAt_kempfNessFunction_expI_neg_smul (h : IsComplexifiedAction C J)
    (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w))
    (ξ : GroupLieAlgebra I G) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ kempfNessFunction C μ p (C.expI (-(s • ξ))))
      (-μ (C.expI (t • ξ) • p) ξ) t := by
  simpa [smul_neg] using hasDerivAt_kempfNessFunction_geodesic C μ p h hμ hg 1 (-ξ) t

/-- **The second derivative of the Kempf–Ness function along a geodesic.** Let the action of
`Gc` be a complexified action, let `-μ` be an equivariant moment map for `σ`, and let the metric
be `g(u, w) = σ(u, J w)`. Then the derivative of `t ↦ Φ_p (g * C.expI (t • ξ))` has at `t` the
derivative `‖X_ξ‖²`, the squared length of the fundamental vector field of `ξ` at the point
`C.expI (-(t • ξ)) • g⁻¹ • p`. -/
theorem hasDerivAt_deriv_kempfNessFunction_geodesic [FiniteDimensional ℝ E']
    (h : IsComplexifiedAction C J)
    (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w))
    (g : Gc) (ξ : GroupLieAlgebra I G) (t : ℝ) :
    HasDerivAt (deriv fun s : ℝ ↦ kempfNessFunction C μ p (g * C.expI (s • ξ)))
      (‖fundamentalVectorField I' ξ (C.expI (-(t • ξ)) • g⁻¹ • p)‖ ^ 2) t := by
  have hd : (deriv fun s : ℝ ↦ kempfNessFunction C μ p (g * C.expI (s • ξ))) =
      fun s ↦ μ (C.expI ((-s) • ξ) • g⁻¹ • p) ξ :=
    funext fun s ↦ (hasDerivAt_kempfNessFunction_geodesic C μ p h hμ hg g ξ s).deriv.trans
      (by rw [neg_smul])
  -- `simp` cannot rewrite the base point of `fundamentalVectorField`, which its type depends on.
  have hx : C.expI ((-t) • ξ) • g⁻¹ • p = C.expI (-(t • ξ)) • g⁻¹ • p := by rw [neg_smul]
  rw [hd, ← hx]
  convert (hasDerivAt_moment_expI h hμ.toIsMomentMap hg ξ (g⁻¹ • p) (-t)).comp t
    (hasDerivAt_neg t) using 1
  · rw [Function.comp_def]
  · rw [neg_mul_neg, mul_one]

/-- **Convexity of the Kempf–Ness function along geodesics.** Let the action of `Gc` be a
complexified action, let `-μ` be an equivariant moment map for `σ`, and let the metric be
`g(u, w) = σ(u, J w)`. Then `t ↦ Φ_p (g * C.expI (t • ξ))` is convex on `ℝ` for every `g` and
`ξ`. -/
theorem convexOn_kempfNessFunction_geodesic [FiniteDimensional ℝ E']
    (h : IsComplexifiedAction C J)
    (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w))
    (g : Gc) (ξ : GroupLieAlgebra I G) :
    ConvexOn ℝ Set.univ fun t : ℝ ↦ kempfNessFunction C μ p (g * C.expI (t • ξ)) := by
  have hD := hasDerivAt_kempfNessFunction_geodesic C μ p h hμ hg g ξ
  refine Monotone.convexOn_univ_of_deriv (fun t ↦ (hD t).differentiableAt) fun a b hab ↦ ?_
  -- The derivative is `μ (C.expI ((-t) • ξ) • g⁻¹ • p) ξ`, antitone in `-t`.
  rw [(hD a).deriv, (hD b).deriv, ← neg_smul, ← neg_smul]
  exact antitone_moment_expI h hμ.toIsMomentMap hg ξ (g⁻¹ • p) (neg_le_neg hab)

/-- **The lower bound from convexity.** Let the action of `Gc` be a complexified action, let `-μ`
be an equivariant moment map for `σ`, and let the metric be `g(u, w) = σ(u, J w)`. Then
`Φ_p g + μ (g⁻¹ • p) η ≤ Φ_p (g * C.expI η * C.toHom u)` for all `g`, `η` and `u`: the convex
function `t ↦ Φ_p (g * C.expI (t • η))` lies above its tangent line at `t = 0`. -/
theorem kempfNessFunction_add_moment_le [FiniteDimensional ℝ E']
    (h : IsComplexifiedAction C J)
    (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w))
    (g : Gc) (η : GroupLieAlgebra I G) (u : G) :
    kempfNessFunction C μ p g + μ (g⁻¹ • p) η ≤
      kempfNessFunction C μ p (g * C.expI η * C.toHom u) := by
  have hD := hasDerivAt_kempfNessFunction_geodesic C μ p h hμ hg g η 0
  rw [zero_smul, neg_zero, C.expI_zero, one_smul] at hD
  have hle := (convexOn_kempfNessFunction_geodesic C μ p h hμ hg g η).le_slope_of_hasDerivAt
    (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one hD
  rw [slope_def_field, sub_zero, div_one, zero_smul, C.expI_zero, mul_one, one_smul] at hle
  rw [kempfNessFunction_mul_toHom]
  linarith

/-- **The lower bound from convexity, with norms.** In the setting of
`kempfNessFunction_add_moment_le`, for a symmetric nonnegative form `B` on the Lie algebra,
`Φ_p g - √(‖μ (g⁻¹ • p)‖²) * √(B η η) ≤ Φ_p (g * C.expI η * C.toHom u)`, where `‖μ x‖²` is
`momentNormSq B hB μ x`. -/
theorem kempfNessFunction_sub_sqrt_momentNormSq_mul_sqrt_le [FiniteDimensional ℝ E']
    (h : IsComplexifiedAction C J)
    (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w))
    {B : LinearMap.BilinForm ℝ (GroupLieAlgebra I G)} {hB : B.Nondegenerate} (hBs : B.IsSymm)
    (hpos : B.IsNonneg) (g : Gc) (η : GroupLieAlgebra I G) (u : G) :
    kempfNessFunction C μ p g - √(momentNormSq B hB μ (g⁻¹ • p)) * √(B η η) ≤
      kempfNessFunction C μ p (g * C.expI η * C.toHom u) := by
  have hCS := neg_abs_le (μ (g⁻¹ • p) η) |>.trans' <| neg_le_neg <|
    abs_apply_le_sqrt_momentNormSq_mul_sqrt (hB := hB) hBs hpos η
  linarith [kempfNessFunction_add_moment_le C μ p h hμ hg g η u]

/-- **The Kempf–Ness function at a zero of the moment map is nonnegative.** In the setting of
`kempfNessFunction_add_moment_le`, if `μ p = 0` then `0 ≤ Φ_p g` for every `g`: the function `Φ_p`
attains its minimum `0` at `1`. -/
theorem kempfNessFunction_nonneg_of_moment_eq_zero [FiniteDimensional ℝ E']
    (h : IsComplexifiedAction C J)
    (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w)) (hp : μ p = 0)
    (g : Gc) : 0 ≤ kempfNessFunction C μ p g := by
  have hle := kempfNessFunction_add_moment_le C μ p h hμ hg 1 (C.polar.symm g).1
    (C.polar.symm g).2
  have h0 : μ ((1 : Gc)⁻¹ • p) (C.polar.symm g).1 = 0 := by
    rw [inv_one, one_smul, hp]
    exact LinearMap.zero_apply _
  rwa [one_mul, C.expI_mul_toHom_polar_symm, kempfNessFunction_one, h0, add_zero] at hle

omit [ConnectedSpace G] in
/-- **A uniform positive slope at a zero of the moment map.** For a complexified action, with `-μ`
a moment map for `σ` and the metric `g(u, w) = σ(u, J w)`, let `μ p = 0` and let `0` be the only
`ξ` whose fundamental vector field vanishes at `p`. Then there is `c > 0` with
`c ≤ μ (C.expI (-ξ) • p) ξ` for every unit vector `ξ` of the Lie algebra. For an equivariant moment
map, this value is the derivative of `t ↦ Φ_p (C.expI (t • ξ))` at `t = 1`
(`hasDerivAt_kempfNessFunction_geodesic`). -/
theorem exists_pos_le_moment_expI_neg_smul_apply [FiniteDimensional ℝ E']
    (h : IsComplexifiedAction C J)
    (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w)) (hp : μ p = 0)
    (hξ : ∀ ξ : GroupLieAlgebra I G, fundamentalVectorField I' ξ p = 0 → ξ = 0) :
    ∃ c > 0, ∀ ξ : E, ‖ξ‖ = 1 → c ≤ μ (C.expI (-ξ) • p) ξ := by
  have hcont : Continuous fun ξ : E ↦ μ (C.expI (-ξ) • p) ξ := by
    have := (contDiff_moment_expI_neg_smul_smul_apply C μ p hμ.contMDiff_of_neg).continuous.comp
      (show Continuous fun ξ : E ↦ (ξ, (1 : ℝ)) by fun_prop)
    simpa only [Function.comp_def, one_smul] using this
  have hpos (ξ : E) (h1 : ‖ξ‖ = 1) : 0 < μ (C.expI (-ξ) • p) ξ :=
    moment_expI_neg_smul_apply_pos h hμ hg hp fun h0 ↦ by
      have h00 : ξ = (0 : E) := hξ ξ h0
      simp [h00] at h1
  obtain ⟨c, hc, hle⟩ := (isCompact_sphere (0 : E) 1).exists_forall_le' hcont.continuousOn
    fun ξ h1 ↦ hpos ξ (mem_sphere_zero_iff_norm.1 h1)
  exact ⟨c, hc, fun ξ h1 ↦ hle ξ (mem_sphere_zero_iff_norm.2 h1)⟩

/-- **Linear growth of the Kempf–Ness function at a zero of the moment map.** In the setting of
`kempfNessFunction_add_moment_le`, let `μ p = 0` and let `0 ≤ c ≤ μ (C.expI (-ξ) • p) ξ` for every
unit vector `ξ`. Then `c * (‖η‖ - 1) ≤ Φ_p (C.expI η * C.toHom u)` for all `η` and `u`. -/
theorem mul_norm_sub_one_le_kempfNessFunction [FiniteDimensional ℝ E']
    (h : IsComplexifiedAction C J)
    (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w)) (hp : μ p = 0)
    {c : ℝ} (hc0 : 0 ≤ c) (hc : ∀ ξ : E, ‖ξ‖ = 1 → c ≤ μ (C.expI (-ξ) • p) ξ) (η : E) (u : G) :
    c * (‖η‖ - 1) ≤ kempfNessFunction C μ p (C.expI η * C.toHom u) := by
  rw [kempfNessFunction_mul_toHom]
  rcases le_or_gt ‖η‖ 1 with hη | hη
  · exact (mul_nonpos_of_nonneg_of_nonpos hc0 (by linarith)).trans
      (kempfNessFunction_nonneg_of_moment_eq_zero C μ p h hμ hg hp _)
  -- Write `η = ‖η‖ • ξ` with `‖ξ‖ = 1`, and use convexity along `t ↦ C.expI (t • ξ)` at `t = 1`.
  set ξ : E := ‖η‖⁻¹ • η
  have hξ : ‖ξ‖ = 1 := norm_smul_inv_norm (norm_ne_zero_iff.1 (zero_lt_one.trans hη).ne')
  have hηξ : η = ‖η‖ • ξ := (smul_inv_smul₀ (zero_lt_one.trans hη).ne' η).symm
  have hD := hasDerivAt_kempfNessFunction_geodesic C μ p h hμ hg 1 ξ 1
  have hle := (convexOn_kempfNessFunction_geodesic C μ p h hμ hg 1 ξ).le_slope_of_hasDerivAt
    (Set.mem_univ 1) (Set.mem_univ ‖η‖) hη hD
  simp only [one_smul, inv_one, one_mul, slope_def_field] at hle
  -- `1 • ξ` carries the scalar action of the Lie algebra, which `rw [one_smul]` does not see
  -- through `TangentSpace`.
  erw [one_smul] at hle
  rw [le_div_iff₀ (by linarith)] at hle
  have h1 := kempfNessFunction_nonneg_of_moment_eq_zero C μ p h hμ hg hp (C.expI ξ)
  have := mul_le_mul_of_nonneg_right (hc ξ hξ) (show 0 ≤ ‖η‖ - 1 by linarith)
  conv_rhs => rw [hηξ]
  exact this.trans (hle.trans (sub_le_self _ h1))

/-- **Uniqueness of the Kempf–Ness function.** Let the action of `Gc` be a complexified action,
let `-μ` be an equivariant moment map for `σ`, and let the metric be `g(u, w) = σ(u, J w)`. A
differentiable function on `Gc` whose differential at every `g` is the one-form
`ĝ ↦ μ (g⁻¹ • p) (C.im (g⁻¹ ĝ))` and which vanishes at `1` is `Φ_p`. -/
theorem eq_kempfNessFunction_of_mfderiv_eq (h : IsComplexifiedAction C J)
    (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w))
    {f : Gc → ℝ} (hf : MDifferentiable IC 𝓘(ℝ) f)
    (hdf : ∀ (g : Gc) (ĝ : TangentSpace IC g),
      mfderiv IC 𝓘(ℝ) f g ĝ = μ (g⁻¹ • p) (C.im (mfderiv IC IC (g⁻¹ * ·) g ĝ)))
    (hf1 : f 1 = 0) : f = kempfNessFunction C μ p := by
  have := C.connectedSpace
  refine hf.eq_of_mfderiv_eq
    ((contMDiff_kempfNessFunction C μ p hμ.toIsMomentMap.contMDiff_of_neg).mdifferentiable
      (by simp)) (fun x ↦ ?_) 1 (by rw [hf1, kempfNessFunction_one])
  ext ĝ
  exact (hdf x ĝ).trans (mfderiv_kempfNessFunction C μ p h hμ hg x ĝ).symm

/-- **Existence and uniqueness of the Kempf–Ness function.** Let the action of `Gc` be a
complexified action, let `-μ` be an equivariant moment map for `σ`, and let the metric be
`g(u, w) = σ(u, J w)`. Then `Φ_p` is the only smooth function on `Gc` whose differential at
every `g` is the one-form `ĝ ↦ μ (g⁻¹ • p) (C.im (g⁻¹ ĝ))` and which vanishes on `G`. -/
theorem existsUnique_kempfNessFunction (h : IsComplexifiedAction C J)
    (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w)) :
    ∃! f : Gc → ℝ, ContMDiff IC 𝓘(ℝ) ∞ f ∧
      (∀ (g : Gc) (ĝ : TangentSpace IC g),
        mfderiv IC 𝓘(ℝ) f g ĝ = μ (g⁻¹ • p) (C.im (mfderiv IC IC (g⁻¹ * ·) g ĝ))) ∧
      ∀ u : G, f (C.toHom u) = 0 :=
  ⟨kempfNessFunction C μ p,
    ⟨contMDiff_kempfNessFunction C μ p hμ.toIsMomentMap.contMDiff_of_neg,
      mfderiv_kempfNessFunction C μ p h hμ hg, kempfNessFunction_toHom C μ p⟩,
    fun _ ⟨hf, hdf, hf0⟩ ↦ eq_kempfNessFunction_of_mfderiv_eq C μ p h hμ hg
      (hf.mdifferentiable (by simp)) hdf (by simpa using hf0 1)⟩

/-- **The cocycle identity for the Kempf–Ness function.** Let the action of `Gc` be a
complexified action, let `-μ` be an equivariant moment map for `σ`, and let the metric be
`g(u, w) = σ(u, J w)`. Then `Φ_p (a * g) = Φ_p a + Φ_{a⁻¹ • p} g` for all `a g : Gc`. -/
theorem kempfNessFunction_mul (h : IsComplexifiedAction C J)
    (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w)) (a g : Gc) :
    kempfNessFunction C μ p (a * g) =
      kempfNessFunction C μ p a + kempfNessFunction C μ (a⁻¹ • p) g := by
  -- `g ↦ Φ_p (a * g) - Φ_p a` vanishes at `1` and has the differential of `Φ_{a⁻¹ • p}`.
  have hΦ := contMDiff_kempfNessFunction C μ p hμ.toIsMomentMap.contMDiff_of_neg
  have hmul : ContMDiff IC IC ∞ (a * · : Gc → Gc) := contMDiff_const.mul contMDiff_id
  have hf := eq_kempfNessFunction_of_mfderiv_eq C μ (a⁻¹ • p) h hμ hg
    (f := fun g ↦ kempfNessFunction C μ p (a * g) - kempfNessFunction C μ p a)
    (((hΦ.comp hmul).sub contMDiff_const).mdifferentiable (by simp)) (fun x ĝ ↦ ?_) (by simp)
  · rw [← congrFun hf g]
    ring
  rw [mfderiv_sub_const]
  refine (mfderiv_comp_apply (g := kempfNessFunction C μ p) x (hΦ.mdifferentiableAt (by simp))
    (hmul.mdifferentiableAt (by simp)) ĝ).trans ?_
  refine (mfderiv_kempfNessFunction C μ p h hμ hg (a * x) _).trans ?_
  rw [Lie.mfderiv_inv_mul_mfderiv_mul_left, mul_inv_rev, mul_smul]

/-- The Kempf–Ness function is additive on the stabilizer of `p` in `Gc`, in the setting of
`kempfNessFunction_mul`: `Φ_p (a * g) = Φ_p a + Φ_p g` when `a • p = p`. -/
theorem kempfNessFunction_mul_of_smul_eq (h : IsComplexifiedAction C J)
    (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w)) {a : Gc}
    (ha : a • p = p) (g : Gc) :
    kempfNessFunction C μ p (a * g) = kempfNessFunction C μ p a + kempfNessFunction C μ p g := by
  rw [kempfNessFunction_mul C μ p h hμ hg, inv_smul_eq_iff.2 ha.symm]

/-- **Critical points of the Kempf–Ness function.** Let the action of `Gc` be a complexified
action, let `-μ` be an equivariant moment map for `σ`, and let the metric be
`g(u, w) = σ(u, J w)`. Then the differential of `Φ_p` vanishes at `g` exactly when `μ` vanishes
at `g⁻¹ • p`. -/
theorem mfderiv_kempfNessFunction_eq_zero_iff (h : IsComplexifiedAction C J)
    (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w)) (g : Gc) :
    mfderiv IC 𝓘(ℝ) (kempfNessFunction C μ p) g = 0 ↔ μ (g⁻¹ • p) = 0 := by
  refine ⟨fun h0 ↦ ?_, fun h0 ↦ ?_⟩
  · ext ξ
    -- The value at `g` of the invariant vector field of `C.cplx (C.lieMap ξ)` translates back to
    -- `C.cplx (C.lieMap ξ)`, whose imaginary part is `ξ`.
    have h1 := congrArg (· (mulInvariantVectorField (C.cplx (C.lieMap ξ)) g)) h0
    simp only [mfderiv_kempfNessFunction C μ p h hμ hg, mfderiv_inv_mul_mulInvariantVectorField,
      C.im_cplx_lieMap, zero_apply] at h1
    -- `h1` is stated in `TangentSpace 𝓘(ℝ) _`, which is `ℝ` by definition.
    exact h1
  · ext ĝ
    rw [mfderiv_kempfNessFunction C μ p h hμ hg, h0, LinearMap.zero_apply, zero_apply]
    -- The zeros of `ℝ` and of `TangentSpace 𝓘(ℝ) _`, which is `ℝ` by definition.
    rfl

/-- **Polystability and critical points.** Let the action of `Gc` be a complexified action, let
`-μ` be an equivariant moment map for `σ`, and let the metric be `g(u, w) = σ(u, J w)`. Then `p`
is polystable exactly when its Kempf–Ness function `Φ_p` has a critical point. -/
theorem isPolystable_iff_exists_mfderiv_kempfNessFunction_eq_zero (h : IsComplexifiedAction C J)
    (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w)) :
    IsPolystable C μ p ↔ ∃ g : Gc, mfderiv IC 𝓘(ℝ) (kempfNessFunction C μ p) g = 0 := by
  simp_rw [mfderiv_kempfNessFunction_eq_zero_iff C μ p h hμ hg, isPolystable_iff_exists_smul]
  exact ⟨fun ⟨g, hg⟩ ↦ ⟨g⁻¹, by rwa [inv_inv]⟩, fun ⟨g, hg⟩ ↦ ⟨g⁻¹, hg⟩⟩

end Derivative

/-! ### Zeros of `μ` in a polystable orbit -/

section Polystable

open _root_.Bundle TauCeti
open scoped RealInnerProductSpace

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [MulAction G M]
  [ContMDiffSMul I I' ∞ G M]
  {σ : SmoothTwoForm I' M} {J : SmoothAlmostComplexStructure I' M} {C μ p}

/-- **The zeros of `μ` in a `Gc`-orbit form one `G`-orbit.** Let the action of `Gc` be a
complexified action, let `-μ` be an equivariant moment map for `σ`, and let the metric be
`g(u, w) = σ(u, J w)`. If `x` and `y` lie in the `Gc`-orbit of `p` and `μ` vanishes at both, then
`y = u • x` for some `u ∈ G`. -/
theorem exists_smul_eq_of_moment_eq_zero [FiniteDimensional ℝ E'] [ContMDiffSMul IC I' ∞ Gc M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I' x)] (h : IsComplexifiedAction C J)
    (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w)) {x y : M}
    (hx : x ∈ MulAction.orbit Gc p) (hy : y ∈ MulAction.orbit Gc p) (hx0 : μ x = 0)
    (hy0 : μ y = 0) : ∃ u : G, u • x = y := by
  rw [← MulAction.orbit_eq_iff.2 hx] at hy
  obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.1 hy
  -- Write `g = C.expI ξ * C.toHom u` by the polar decomposition; `μ` vanishes at
  -- `C.toHom u • x` by equivariance, and `C.expI ξ` then fixes that point.
  obtain ⟨ξ, u, rfl⟩ : ∃ ξ u, C.expI ξ * C.toHom u = g := ⟨_, _, C.expI_mul_toHom_polar_symm g⟩
  have hux : μ (C.toHom u • x) = 0 := by rw [h.moment_toHom_smul hμ, hx0, map_zero]
  rw [mul_smul] at hy0 ⊢
  have hle : μ (C.toHom u • x) ξ ≤ μ (C.expI ξ • C.toHom u • x) ξ := by rw [hux, hy0]
  exact ⟨u, by rw [expI_smul_eq_self_of_moment_apply_le h hμ.toIsMomentMap hg hle,
    h.toHom_smul]⟩

variable (C) in
/-- The inclusion of the zero level of `μ` into the polystable locus, equivariant along
`C.toHom` from the coadjoint stabilizer of `0` (all of `G`) to `Gc`. The zero level is Tau Ceti's
`levelSubMulAction` of the moment map `-μ` at `0`. -/
def zeroLevelToPolystable (h : IsComplexifiedAction C J)
    (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x) :
    hμ.levelSubMulAction 0 →ₑ[fun u : (Lie.coadjointRepresentation ℝ I G).stabilizer 0 ↦
      C.toHom u] polystableLocus C μ where
  toFun z := ⟨z, mem_polystableLocus.2 <|
    isPolystable_of_moment_eq_zero (neg_eq_zero.1 (hμ.mem_levelSubMulAction.1 z.property))⟩
  map_smul' u z := Subtype.ext <| by
    rw [SetLike.val_smul, SetLike.val_smul, h.toHom_smul, Subgroup.smul_def]

@[simp]
theorem coe_zeroLevelToPolystable_apply (h : IsComplexifiedAction C J)
    (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x) (z : hμ.levelSubMulAction 0) :
    (zeroLevelToPolystable C h hμ z : M) = z :=
  (rfl)

/-- **Polystable orbits and the zero level.** Let the action of `Gc` be a complexified action,
let `-μ` be an equivariant moment map for `σ`, and let the metric be `g(u, w) = σ(u, J w)`. Then
the map from the `G`-orbits of the zero level of `μ` to the `Gc`-orbits of polystable points,
induced by the inclusion, is bijective: every polystable `Gc`-orbit meets the zero level, and
it meets it in a single `G`-orbit. -/
theorem bijective_zeroLevelOrbit_polystableOrbit [FiniteDimensional ℝ E']
    [ContMDiffSMul IC I' ∞ Gc M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I' x)] (h : IsComplexifiedAction C J)
    (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w)) :
    Function.Bijective (zeroLevelToPolystable C h hμ).orbitRelQuotientMap := by
  have hzero {x : M} : x ∈ hμ.levelSubMulAction 0 ↔ μ x = 0 := by
    rw [hμ.mem_levelSubMulAction, neg_eq_zero]
  constructor
  · intro a b hzz'
    induction a, b using Quotient.inductionOn₂ with | h z z' => ?_
    rw [MulActionHom.orbitRelQuotientMap_mk, MulActionHom.orbitRelQuotientMap_mk] at hzz'
    have hz : (z : M) ∈ MulAction.orbit Gc (z' : M) := by
      obtain ⟨g, hgz⟩ :=
        MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 (Quotient.exact hzz'))
      exact ⟨g, congrArg Subtype.val hgz⟩
    obtain ⟨u, hu⟩ := exists_smul_eq_of_moment_eq_zero h hμ hg (MulAction.mem_orbit_self _) hz
      (hzero.1 z'.property) (hzero.1 z.property)
    exact Quotient.sound ((hμ.orbitRel_levelSubMulAction_iff).2 ⟨u, hu⟩)
  · intro a
    induction a using Quotient.inductionOn with | h z => ?_
    obtain ⟨g, hg0⟩ := isPolystable_iff_exists_smul.1 (mem_polystableLocus.1 z.property)
    refine ⟨⟦⟨g • (z : M), hzero.2 hg0⟩⟧, ?_⟩
    rw [MulActionHom.orbitRelQuotientMap_mk]
    exact Quotient.sound (MulAction.orbitRel_apply.2
      ⟨g, Subtype.ext (by rw [SetLike.val_smul, coe_zeroLevelToPolystable_apply])⟩)

end Polystable

end SymplecticGeometry

end
