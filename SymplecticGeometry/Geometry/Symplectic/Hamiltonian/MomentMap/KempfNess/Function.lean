/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import SymplecticGeometry.Geometry.Lie.Complexification
public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.KempfNess.Basic
public import TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Basic
import SymplecticGeometry.Analysis.Calculus.ParametricIntervalIntegral
import SymplecticGeometry.Geometry.Lie.Exponential.Derivative
import SymplecticGeometry.Geometry.Manifold.ContMDiff.Dual
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
of `Φ_p` at `g` is the one-form `ĝ ↦ μ (g⁻¹ • p) (C.im (g⁻¹ ĝ))`.

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
* `SymplecticGeometry.contDiff_moment_expI_neg_smul_smul_apply`: the integrand
  `(ξ, t) ↦ μ (C.expI (-(t • ξ)) • p) ξ` is smooth.
* `SymplecticGeometry.contMDiff_kempfNessFunction`: `Φ_p` is smooth.
* `SymplecticGeometry.moment_inv_smul_im_mfderiv_polar_smul`: on the velocity of the radial curve
  `τ ↦ C.polar (τ • ξ, u)` at `t`, the one-form `ĝ ↦ μ (g⁻¹ • p) (C.im (g⁻¹ ĝ))` takes the value
  `μ (C.expI (-(t • ξ)) • p) ξ` of the integrand of `Φ_p (C.polar (ξ, u))`.
* `SymplecticGeometry.mfderiv_kempfNessFunction`: the differential of `Φ_p` at `g` is
  `ĝ ↦ μ (g⁻¹ • p) (C.im (g⁻¹ ĝ))`.
* `SymplecticGeometry.hasDerivAt_kempfNessFunction_comp`: along a curve `c` differentiable at
  `s₀`, the derivative of `Φ_p ∘ c` at `s₀` is the one-form evaluated on the velocity of `c`.

The smoothness reads `Φ_p` through the diffeomorphism `C.polar` as the integral over `[0, 1]` of a
smooth function on `𝔤 × ℝ`, and applies Tau Ceti's
`intervalIntegral.contDiff_parametric_primitive_of_contDiff` to it.

The derivative follows [GeorgoulasRobbinSalamon2021], §2. Along a smooth curve `c`, write
`c s = C.polar (ξ s, u s)` and deform the curve `s ↦ C.toHom (u s)` in `G` to `c` through
`γ (s, t) = C.polar (t • ξ s, u s)`. Along `t` the one-form takes the value of the integrand
(`moment_inv_smul_im_mfderiv_polar_smul`), so `Φ_p (c s) = ∫ t in 0..1, A (s, t)` with `A` the
one-form on `∂_t γ`. The closedness of the one-form (`fderiv_moment_inv_smul_im_comm`) turns
`∂_s A` into `∂_t B`, with `B` the one-form on `∂_s γ`, so differentiating under the integral sign
and integrating along `t` (`intervalIntegral.hasDerivAt_integral_of_hasDerivAt_snd`) leaves
`B (s, 1) - B (s, 0)`. Here `B (s, 0) = 0` since
`γ (·, 0)` stays in `G` (`LieComplexification.im_mfderiv_inv_mul_mfderiv_toHom_comp`), and
`B (s, 1)` is the one-form on the velocity of `c`. The differential at `g` is read along the curve
`s ↦ g * exp (s • g⁻¹ ĝ)` with Tau Ceti's
`HasMFDerivAt.hasDerivAt_comp_mul_mulInvariantExp_smul_zero`, and the derivative along any curve
differentiable at a point then follows by the chain rule.

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

/-- The integrand `(ξ, t) ↦ μ (C.expI (-(t • ξ)) • p) ξ` of the Kempf–Ness function, read on the
model space `E × ℝ`, is smooth when `Gc` acts smoothly on `M` and each component `x ↦ μ x ξ` of
`μ` is smooth. -/
theorem contDiff_moment_expI_neg_smul_smul_apply (hμ : ∀ ξ, ContMDiff I' 𝓘(ℝ) ∞ fun x ↦ μ x ξ) :
    ContDiff ℝ ∞ fun q : E × ℝ ↦ μ (C.expI (-(q.2 • q.1)) • p) q.1 := by
  have hx : ContMDiff 𝓘(ℝ, E × ℝ) I' ∞ fun q : E × ℝ ↦ C.expI (-(q.2 • q.1)) • p :=
    (C.contMDiff_expI.comp (contDiff_snd.smul contDiff_fst).neg.contMDiff).smul contMDiff_const
  exact contMDiff_iff_contDiff.1 <|
    ((contMDiff_toContinuousLinearMap_of_contMDiff_apply (E := E) hμ).comp hx).clm_apply
      contDiff_fst.contMDiff

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

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ EC] [ConnectedSpace G]
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
        (C.im (mfderiv IC IC ((c s₀)⁻¹ * ·) (c s₀) (mfderiv 𝓘(ℝ) IC c s₀ (1 : ℝ))))) s₀ := by
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
      mfderiv 𝓘(ℝ) IC (fun q ↦ γ (q, t)) s (1 : ℝ) :=
    (curveVelocity_eq_mfderiv_fst (f := fun a b ↦ γ (a, b)) (hγd (s, t))).symm.trans
      curveVelocity_apply
  -- Along `t`, the one-form is the integrand (`moment_inv_smul_im_mfderiv_polar_smul`).
  have hA : α (0, 1) = A := by
    funext ⟨s, t⟩
    have hv : mfderiv 𝓘(ℝ, ℝ × ℝ) IC γ (s, t) (0, 1) =
        mfderiv 𝓘(ℝ) IC (fun τ ↦ γ (s, τ)) t (1 : ℝ) :=
      (curveVelocity_eq_mfderiv_snd (f := fun a b ↦ γ (a, b)) (hγd (s, t))).symm.trans
        curveVelocity_apply
    -- `change` unfolds the local definition `α` to expose the velocity that `hv` rewrites.
    change μ ((γ (s, t))⁻¹ • p) (C.im (mfderiv IC IC ((γ (s, t))⁻¹ * ·) (γ (s, t))
      (mfderiv 𝓘(ℝ, ℝ × ℝ) IC γ (s, t) (0, 1)))) = A (s, t)
    rw [hv]
    exact moment_inv_smul_im_mfderiv_polar_smul C μ p (h.moment_toHom_smul hμ) (ξ s) (u s) t
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
    rw [hfst, hγ0, hγ00,
      C.im_mfderiv_inv_mul_mfderiv_toHom_comp (hu.mdifferentiableAt (by simp)) (1 : ℝ), map_zero]
  -- At `t = 1` the homotopy is the curve `c`.
  have hγ1 : (fun q ↦ γ (q, 1)) = c := by
    funext q
    have hq : (((1 : ℝ) • ξ q : E), u q) = C.polar.symm (c q) := Prod.ext (one_smul ℝ _) rfl
    exact (congrArg C.polar hq).trans (C.polar.apply_symm_apply (c q))
  have hB1 : α (1, 0) (s₀, 1) = μ ((c s₀)⁻¹ • p)
      (C.im (mfderiv IC IC ((c s₀)⁻¹ * ·) (c s₀) (mfderiv 𝓘(ℝ) IC c s₀ (1 : ℝ)))) := by
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
  rwa [mfderiv_inv_mul_mfderiv_mul_mulInvariantExp_smul, zero_smul, mulInvariantExp_zero,
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
        (C.im (mfderiv IC IC ((c s₀)⁻¹ * ·) (c s₀) (mfderiv 𝓘(ℝ) IC c s₀ (1 : ℝ))))) s₀ := by
  have hΦ := hasDerivAt_comp_curve
    ((contMDiff_kempfNessFunction C μ p hμ.toIsMomentMap.contMDiff_of_neg).mdifferentiableAt
      (x := c s₀) (by simp)) (hasMFDerivAt_curveVelocity hc)
  rwa [mvfderiv, ContinuousLinearMap.comp_apply, mfderiv_kempfNessFunction C μ p h hμ hg,
    curveVelocity_apply] at hΦ

end Derivative

end SymplecticGeometry

end
