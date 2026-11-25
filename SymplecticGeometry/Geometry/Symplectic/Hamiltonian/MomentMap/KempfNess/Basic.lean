/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Lie.Complexification
public import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.Metric
public import SymplecticGeometry.Topology.Algebra.GroupAction.Stabilizer
public import TauCeti.Geometry.Lie.FundamentalVectorField
public import TauCeti.Geometry.Manifold.Algebra.ComplexSmoothFunctions
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import TauCeti.Geometry.Manifold.MFDeriv.Curve
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.Basic
public import TauCeti.Geometry.Symplectic.Hamiltonian.EquivariantMomentMap.Basic
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Metric
import SymplecticGeometry.Geometry.Lie.FundamentalVectorField
import SymplecticGeometry.Geometry.Lie.MaurerCartan
import SymplecticGeometry.Geometry.Manifold.ContMDiff.Dual
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Constancy
import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.ContMDiff

/-!
# Complexified actions, stability and the gradient of the moment map

Let `C : LieComplexification I G IC Gc` be a complexification of a real Lie group `G`, and suppose
that `G` and `Gc` both act on `M`, which carries the almost complex structure `J`. The action of
`Gc` is a *complexified action* of that of `G` if it extends it along the inclusion `C.toHom`, and
if, for every `ξ` in the Lie algebra of `G`, the fundamental vector field of the imaginary
direction `C.cplx (C.lieMap ξ)` is `J` applied to that of `ξ`: `X_{iξ} = J X_ξ`. This is the
infinitesimal form of the holomorphicity of the action of `Gc`, the only form in which the
Kempf–Ness theory uses it.

For an action of `Gc` on `M`, a point `p` is *polystable* for `μ` if its `Gc`-orbit meets the
zero set of `μ`, *semistable* if the closure of that orbit does, and *stable* if it is
polystable with a discrete stabilizer in `Gc`, following [McDuffSalamon2017], §5.7, and
[GeorgoulasRobbinSalamon2021]. Later files characterize them through the Kempf–Ness function
and the moment weights.

## Main definitions

* `SymplecticGeometry.IsComplexifiedAction C J`: the action of `Gc` on `M` is a complexified
  action of that of `G`, for `C` and `J`.
* `SymplecticGeometry.IsSemistable C μ p`, `SymplecticGeometry.IsPolystable C μ p`,
  `SymplecticGeometry.IsStable C μ p`: the stability predicates.
* `SymplecticGeometry.polystableLocus C μ`: the polystable points, as a sub-action of `Gc`.

## Main results

* `SymplecticGeometry.IsComplexifiedAction.fundamentalVectorField_lieMap`: the fundamental vector
  field of `C.lieMap ξ` for the action of `Gc` is that of `ξ` for the action of `G`.
* `SymplecticGeometry.IsComplexifiedAction.fundamentalVectorField_eq_re_add_im`: the fundamental
  vector field of any `ζ` for the action of `Gc` is `X_{C.re ζ} + J X_{C.im ζ}`.
* `SymplecticGeometry.IsComplexifiedAction.isMIntegralCurve_expI_smul`: the curve
  `t ↦ C.expI (t • ξ) • p` is an integral curve of `x ↦ J x (X_ξ x)`.
* `SymplecticGeometry.isComplexifiedAction_circle`: the action of `ℂˣ` on `ℂ` by multiplication,
  with `J` multiplication by `i`, is a complexified action of the rotation action of `Circle`, for
  the complexification `LieComplexification.circle`.
* `SymplecticGeometry.IsComplexifiedAction.moment_toHom_smul`: if `-μ` is an equivariant moment
  map, then `μ (C.toHom u • x) = Ad*_u (μ x)`.
* `SymplecticGeometry.IsStable.isPolystable`, `SymplecticGeometry.IsPolystable.isSemistable`:
  stable points are polystable, and polystable points semistable.
* `SymplecticGeometry.isSemistable_smul_iff`, `SymplecticGeometry.isPolystable_smul_iff`,
  `SymplecticGeometry.isStable_smul_iff`: each predicate holds at `g • p` exactly when it holds
  at `p`.
* `SymplecticGeometry.isPolystable_of_moment_eq_zero`: a zero of `μ` is polystable.
* `SymplecticGeometry.isSemistable_of_moment_eq_zero`: a zero of `μ` is semistable.
* `SymplecticGeometry.isStable_of_moment_eq_zero`: a zero of `μ` whose stabilizer in `Gc` is
  discrete is stable.
* `SymplecticGeometry.mgradient_moment_apply`: if `-μ` is a moment map for `σ` and the metric is
  `g(u, w) = σ(u, J w)`, the gradient of `x ↦ μ x ξ` is `-J X_ξ`.
* `SymplecticGeometry.hasDerivAt_moment_expI`, `SymplecticGeometry.antitone_moment_expI`: for a
  complexified action, `t ↦ μ (C.expI (t • ξ) • p) ξ` has derivative `-‖X_ξ‖²` at the moving
  point, so it is antitone.
* `SymplecticGeometry.expI_smul_eq_self_of_moment_eq_zero`: for a complexified action, if `μ`
  vanishes at `x` and at `C.expI ξ • x`, then `C.expI ξ` fixes `x`.
* `SymplecticGeometry.differentiable_moment_inv_smul_im_mfderiv`: along a smooth map `γ` from a
  normed space to `Gc`, the function `z ↦ μ ((γ z)⁻¹ • p) (C.im (a_v z))` is differentiable.
* `SymplecticGeometry.fderiv_moment_inv_smul_im_comm`: for a smooth map `γ` from a normed space
  to `Gc`, with left-trivialized derivatives `a_u`, the functions
  `z ↦ μ ((γ z)⁻¹ • p) (C.im (a_u z))` satisfy `∂_v A_w = ∂_w A_v`. This is the closedness of the
  one-form `ĝ ↦ μ (g⁻¹ • p) (C.im (g⁻¹ ĝ))` on `Gc`, stated along maps so that no form on `Gc`
  is built.

The integral curve is Tau Ceti's `TauCeti.isMIntegralCurve_mulInvariantExp_smul_smul` for the
action of `Gc` and the direction `C.cplx (C.lieMap ξ)`. In the example, the orbit maps of `ℂˣ` are
holomorphic, so their real differentials commute with multiplication by `i`
(`MDifferentiableAt.mfderiv_ofComplexManifold_apply`). The smoothness of the action of `ℂˣ` on `ℂ`
for the real structures, which the results on complexified actions assume, is found by instance
search: Mathlib's `Units.contMDiffSMul` and `ContMDiffMul.contMDiffSMul` from Tau Ceti's
`TauCeti.realComplexContMDiffRing`.

The gradient of `x ↦ μ x ξ` is computed as in Tau Ceti's
`TauCeti.SmoothTwoForm.IsNondegenerate.apply_hamiltonianVectorField_eq_mgradient`, read for the
component `-μ_ξ` with Hamiltonian vector field `X_ξ`; no nondegeneracy is needed, since the
gradient is tested directly against the moment map identity, through
`TauCeti.SmoothAlmostComplexStructure.apply_eq_mgradient_of_eval₂_eq`. The derivative along
`exp(itξ)` follows Tau Ceti's `TauCeti.hasDerivAt_comp_maximalIntegralCurve_neg_mgradient`: the
chain rule along the integral curve `isMIntegralCurve_expI_smul` of `J X_ξ`, and `J` is
orthogonal for `g` (`TauCeti.SmoothAlmostComplexStructure.inner_apply_apply_of_inner_eq`).
These results take any metric with `g(u, w) = σ(u, J w)`; for a compatible pair, Tau Ceti's
`TauCeti.SmoothTwoForm.Compatible.inner_eq_eval₂` says that `Compatible.metric` is one.

The closedness follows [GeorgoulasRobbinSalamon2021], Lemma 2.1. The moving point
`(γ z)⁻¹ • p` has derivative `-(X_{re a} + J X_{im a})`, by `mfderiv_inv_smul_comp_apply` and the
complexified action; the moment map equation turns the derivatives of `μ` into values of `σ`;
the terms with `J` are inner products, which are symmetric; infinitesimal equivariance
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.momentCocycle_eq_zero`) turns the other terms into
values of `μ` on brackets, and these cancel against the structure equation
`fderiv_leftMaurerCartanForm_mfderiv_sub`, read through `C.im` (`LieComplexification.im_lie`).

## References

* [V. Georgoulas, J. W. Robbin and D. A. Salamon, *The Moment-Weight Inequality and the
  Hilbert–Mumford Criterion*][GeorgoulasRobbinSalamon2021], §2.
* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §5.7.
-/

public section

noncomputable section

open Function Manifold TauCeti
open scoped Manifold ContDiff

namespace SymplecticGeometry

/-! ### The stability predicates -/

section Stability

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {EC : Type*} [NormedAddCommGroup EC] [NormedSpace ℝ EC] [CompleteSpace EC]
  {HC : Type*} [TopologicalSpace HC] {IC : ModelWithCorners ℝ EC HC}
  {Gc : Type*} [TopologicalSpace Gc] [ChartedSpace HC Gc] [Group Gc] [LieGroup IC ∞ Gc]
  [T2Space Gc] [BoundarylessManifold IC Gc]
  {M : Type*} [MulAction Gc M]

/-- A point `p` is *polystable* for `μ` if its orbit under the complexification `Gc` meets the
zero level set of `μ`. -/
def IsPolystable (_C : LieComplexification I G IC Gc)
    (μ : M → Module.Dual ℝ (GroupLieAlgebra I G)) (p : M) : Prop :=
  ∃ x ∈ MulAction.orbit Gc p, μ x = 0

/-- A point `p` is *stable* for `μ` if it is polystable and its stabilizer in the
complexification `Gc` is discrete. -/
def IsStable (C : LieComplexification I G IC Gc)
    (μ : M → Module.Dual ℝ (GroupLieAlgebra I G)) (p : M) : Prop :=
  IsPolystable C μ p ∧ DiscreteTopology (MulAction.stabilizer Gc p)

/-- A point `p` is *semistable* for `μ` if the closure of its orbit under the complexification
`Gc` meets the zero level set of `μ`. -/
def IsSemistable [TopologicalSpace M] (_C : LieComplexification I G IC Gc)
    (μ : M → Module.Dual ℝ (GroupLieAlgebra I G)) (p : M) : Prop :=
  ∃ x ∈ closure (MulAction.orbit Gc p), μ x = 0

variable {C : LieComplexification I G IC Gc} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}
  {p : M}

theorem isPolystable_iff : IsPolystable C μ p ↔ ∃ x ∈ MulAction.orbit Gc p, μ x = 0 :=
  Iff.rfl

/-- `p` is polystable exactly when `μ` vanishes at `g • p` for some `g` in `Gc`. -/
theorem isPolystable_iff_exists_smul : IsPolystable C μ p ↔ ∃ g : Gc, μ (g • p) = 0 := by
  simp [isPolystable_iff, MulAction.mem_orbit_iff]

theorem isStable_iff :
    IsStable C μ p ↔ IsPolystable C μ p ∧ DiscreteTopology (MulAction.stabilizer Gc p) :=
  Iff.rfl

/-- A stable point is polystable. -/
theorem IsStable.isPolystable (h : IsStable C μ p) : IsPolystable C μ p :=
  h.1

theorem IsStable.discreteTopology_stabilizer (h : IsStable C μ p) :
    DiscreteTopology (MulAction.stabilizer Gc p) :=
  h.2

/-- A zero of `μ` is polystable. -/
theorem isPolystable_of_moment_eq_zero (h : μ p = 0) : IsPolystable C μ p :=
  ⟨p, MulAction.mem_orbit_self p, h⟩

/-- A zero of `μ` with a discrete stabilizer in `Gc` is stable. -/
theorem isStable_of_moment_eq_zero (h : μ p = 0) [DiscreteTopology (MulAction.stabilizer Gc p)] :
    IsStable C μ p :=
  ⟨isPolystable_of_moment_eq_zero h, ‹_›⟩

/-- Polystability is invariant along the orbits of `Gc`. -/
@[simp]
theorem isPolystable_smul_iff (g : Gc) : IsPolystable C μ (g • p) ↔ IsPolystable C μ p := by
  simp only [isPolystable_iff, MulAction.orbit_smul]

/-- Stability is invariant along the orbits of `Gc`. -/
@[simp]
theorem isStable_smul_iff (g : Gc) : IsStable C μ (g • p) ↔ IsStable C μ p := by
  have := continuousMul_of_contMDiffMul IC ∞ (G := Gc)
  rw [isStable_iff, isStable_iff, isPolystable_smul_iff,
    MulAction.discreteTopology_stabilizer_smul_iff]

/-- The *polystable locus*: the set of polystable points, as a sub-action of `Gc`. -/
def polystableLocus (C : LieComplexification I G IC Gc)
    (μ : M → Module.Dual ℝ (GroupLieAlgebra I G)) : SubMulAction Gc M where
  carrier := {p | IsPolystable C μ p}
  smul_mem' g _ hp := (isPolystable_smul_iff (C := C) g).2 hp

@[simp]
theorem mem_polystableLocus : p ∈ polystableLocus C μ ↔ IsPolystable C μ p :=
  Iff.rfl

@[simp]
theorem coe_polystableLocus : (polystableLocus C μ : Set M) = {p | IsPolystable C μ p} :=
  (rfl)

/-- The zero level set of `μ` lies in the polystable locus. -/
theorem setOf_moment_eq_zero_subset_polystableLocus :
    {x | μ x = 0} ⊆ (polystableLocus C μ : Set M) :=
  fun _ hx ↦ isPolystable_of_moment_eq_zero (C := C) hx

variable [TopologicalSpace M]

theorem isSemistable_iff : IsSemistable C μ p ↔ ∃ x ∈ closure (MulAction.orbit Gc p), μ x = 0 :=
  Iff.rfl

/-- A polystable point is semistable. -/
theorem IsPolystable.isSemistable (h : IsPolystable C μ p) : IsSemistable C μ p :=
  let ⟨x, hx, hμ⟩ := h
  ⟨x, subset_closure hx, hμ⟩

theorem IsStable.isSemistable (h : IsStable C μ p) : IsSemistable C μ p :=
  h.isPolystable.isSemistable

/-- A zero of `μ` is semistable. -/
theorem isSemistable_of_moment_eq_zero (h : μ p = 0) : IsSemistable C μ p :=
  (isPolystable_of_moment_eq_zero h).isSemistable

/-- Semistability is invariant along the orbits of `Gc`. -/
@[simp]
theorem isSemistable_smul_iff (g : Gc) : IsSemistable C μ (g • p) ↔ IsSemistable C μ p := by
  simp only [isSemistable_iff, MulAction.orbit_smul]

end Stability

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {EC : Type*} [NormedAddCommGroup EC] [NormedSpace ℝ EC] [CompleteSpace EC]
  {HC : Type*} [TopologicalSpace HC] {IC : ModelWithCorners ℝ EC HC}
  {Gc : Type*} [TopologicalSpace Gc] [ChartedSpace HC Gc] [Group Gc] [LieGroup IC ∞ Gc]
  [T2Space Gc] [BoundarylessManifold IC Gc]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M]
  [MulAction G M] [MulAction Gc M]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-- The action of the complexification `Gc` on `M` is a *complexified action* of that of `G`,
for the complexification `C` and the almost complex structure `J` of `M`: it extends the action of
`G` along `C.toHom`, and for every `ξ` in the Lie algebra of `G` the fundamental vector field of
`C.cplx (C.lieMap ξ)` is `J` applied to that of `C.lieMap ξ`, at every point. -/
structure IsComplexifiedAction (C : LieComplexification I G IC Gc)
    (J : SmoothAlmostComplexStructure I' M) : Prop where
  /-- The action of `Gc` extends that of `G` along `C.toHom`. -/
  toHom_smul (u : G) (x : M) : C.toHom u • x = u • x
  /-- The fundamental vector field of an imaginary direction is `J` applied to that of the real
  direction: `X_{iξ} = J X_ξ`. -/
  fundamentalVectorField_cplx (ξ : GroupLieAlgebra I G) (x : M) :
    fundamentalVectorField I' (C.cplx (C.lieMap ξ)) x =
      J x (fundamentalVectorField I' (C.lieMap ξ) x)

namespace IsComplexifiedAction

variable [ContMDiffSMul IC I' ∞ Gc M] {C : LieComplexification I G IC Gc}
  {J : SmoothAlmostComplexStructure I' M}

/-- For a complexified action, the fundamental vector field of `C.lieMap ξ` for the action of
`Gc` is that of `ξ` for the action of `G`. -/
theorem fundamentalVectorField_lieMap (h : IsComplexifiedAction C J) (ξ : GroupLieAlgebra I G) :
    fundamentalVectorField I' (C.lieMap ξ) =
      (fundamentalVectorField I' ξ : ∀ x : M, TangentSpace I' x) := by
  rw [LieComplexification.lieMap_def, ContMDiffMonoidMorphism.coe_groupLieAlgebraLieHom]
  exact C.toHom.toMonoidHom.fundamentalVectorField_groupLieAlgebraMap
    (C.toHom.contMDiff_toFun.mdifferentiableAt (by simp)) (fun u x ↦ (h.toHom_smul u x).symm) ξ

/-- For a complexified action, the fundamental vector field of any `ζ` in the Lie algebra of `Gc`
is `X_{C.re ζ} + J X_{C.im ζ}`, where `X_{C.re ζ}` and `X_{C.im ζ}` are fundamental vector fields
for the action of `G`. -/
theorem fundamentalVectorField_eq_re_add_im [FiniteDimensional ℝ E] [FiniteDimensional ℝ EC]
    (h : IsComplexifiedAction C J) (ζ : GroupLieAlgebra IC Gc) (x : M) :
    fundamentalVectorField I' ζ x =
      fundamentalVectorField I' (C.re ζ) x + J x (fundamentalVectorField I' (C.im ζ) x) := by
  conv_lhs => rw [← C.lieMap_re_add_cplx_lieMap_im ζ]
  rw [fundamentalVectorField_add, Pi.add_apply, h.fundamentalVectorField_cplx,
    h.fundamentalVectorField_lieMap, h.fundamentalVectorField_lieMap]

/-- **The imaginary one-parameter subgroups move points along `J X_ξ`.** For a complexified
action, the curve `t ↦ C.expI (t • ξ) • p` is an integral curve of the vector field
`x ↦ J x (X_ξ x)`, where `X_ξ` is the fundamental vector field of `ξ` for the action of `G`. -/
theorem isMIntegralCurve_expI_smul (h : IsComplexifiedAction C J) (ξ : GroupLieAlgebra I G)
    (p : M) :
    IsMIntegralCurve (fun t : ℝ ↦ C.expI (t • ξ) • p)
      (fun x ↦ J x (fundamentalVectorField I' ξ x)) := by
  have hγ : (fun t : ℝ ↦ C.expI (t • ξ) • p) =
      fun t : ℝ ↦ mulInvariantExp (t • C.cplx (C.lieMap ξ)) • p := by
    funext t
    rw [LieComplexification.expI_def, map_smul, AlmostComplexStructure.apply_smul]
  have hv : fundamentalVectorField I' (C.cplx (C.lieMap ξ)) =
      fun x ↦ J x (fundamentalVectorField I' ξ x) :=
    funext fun x ↦ by rw [h.fundamentalVectorField_cplx, h.fundamentalVectorField_lieMap]
  rw [hγ, ← hv]
  exact isMIntegralCurve_mulInvariantExp_smul_smul (I' := I') (C.cplx (C.lieMap ξ)) p

omit [ContMDiffSMul IC I' ∞ Gc M] in
/-- For a complexified action and a map `μ` whose negative is an equivariant moment map, `μ` is
equivariant along `C.toHom`: `μ (C.toHom u • x) = Ad*_u (μ x)`. -/
theorem moment_toHom_smul [CompleteSpace E'] [ContMDiffSMul I I' ∞ G M] {σ : SmoothTwoForm I' M}
    {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)} (h : IsComplexifiedAction C J)
    (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x) (u : G) (x : M) :
    μ (C.toHom u • x) = Lie.coadjointRepresentation ℝ I G u (μ x) := by
  rw [h.toHom_smul]
  exact neg_injective ((hμ.apply_smul u x).trans (map_neg _ _))

end IsComplexifiedAction

/-! ### The gradient of a component of the moment map -/

section Gradient

open _root_.Bundle
open scoped RealInnerProductSpace

variable [FiniteDimensional ℝ E'] [ContMDiffSMul I I' ∞ G M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I' x)]
  {σ : SmoothTwoForm I' M} {J : SmoothAlmostComplexStructure I' M}
  {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}

/-- **The gradient of a component of the moment map.** Let `-μ` be a moment map for `σ` of the
action of `G` by fundamental vector fields, and let the metric be `g(u, w) = σ(u, J w)`. Then the
gradient of `x ↦ μ x ξ` is `-J X_ξ`, where `X_ξ` is the fundamental vector field of `ξ`. -/
theorem mgradient_moment_apply
    (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w))
    (ξ : GroupLieAlgebra I G) (x : M) :
    Manifold.mgradient I' (fun y ↦ μ y ξ) x = -J x (fundamentalVectorField I' ξ x) := by
  -- `J X_ξ` is the gradient of the component `x ↦ (-μ x) ξ` of the moment map `-μ`.
  have h := J.apply_eq_mgradient_of_eval₂_eq hg (hμ.eval₂_apply ξ x)
  rw [InfinitesimalAction.fundamental_apply] at h
  rw [show (fun y ↦ μ y ξ) = -fun y ↦ (-μ y) ξ by ext; simp, Manifold.mgradient_neg, ← h]

/-- **The derivative of `⟨μ, ξ⟩` along `exp(itξ)`.** For a complexified action, with `-μ` a
moment map for `σ` and the metric `g(u, w) = σ(u, J w)`, the function
`t ↦ μ (C.expI (t • ξ) • p) ξ` has derivative `-‖X_ξ‖²` at the point `C.expI (t • ξ) • p`. -/
theorem hasDerivAt_moment_expI [ContMDiffSMul IC I' ∞ Gc M] {C : LieComplexification I G IC Gc}
    (h : IsComplexifiedAction C J)
    (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w))
    (ξ : GroupLieAlgebra I G) (p : M) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ μ (C.expI (s • ξ) • p) ξ)
      (-‖fundamentalVectorField I' ξ (C.expI (t • ξ) • p)‖ ^ 2) t := by
  have hd : MDifferentiableAt I' 𝓘(ℝ) (fun y ↦ μ y ξ) (C.expI (t • ξ) • p) := by
    convert (hμ.mdifferentiableAt ξ (C.expI (t • ξ) • p)).neg using 1
    funext y
    simp
  have hD := Manifold.hasDerivAt_comp_curve hd (h.isMIntegralCurve_expI_smul ξ p t)
  rwa [← Manifold.inner_mgradient, mgradient_moment_apply hμ hg, inner_neg_left,
    SmoothAlmostComplexStructure.inner_apply_apply_of_inner_eq hg,
    real_inner_self_eq_norm_sq] at hD

/-- **`⟨μ, ξ⟩` decreases along `exp(itξ)`.** For a complexified action, with `-μ` a moment map
for `σ` and the metric `g(u, w) = σ(u, J w)`, the function `t ↦ μ (C.expI (t • ξ) • p) ξ` is
antitone. -/
theorem antitone_moment_expI [ContMDiffSMul IC I' ∞ Gc M] {C : LieComplexification I G IC Gc}
    (h : IsComplexifiedAction C J)
    (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w))
    (ξ : GroupLieAlgebra I G) (p : M) :
    Antitone fun t : ℝ ↦ μ (C.expI (t • ξ) • p) ξ :=
  antitone_of_hasDerivAt_nonpos (hasDerivAt_moment_expI h hμ hg ξ p)
    fun _ ↦ neg_nonpos.2 (sq_nonneg _)

/-- **Zeros of `μ` joined by an imaginary direction coincide.** For a complexified action, with
`-μ` a moment map for `σ` and the metric `g(u, w) = σ(u, J w)`: if `μ` vanishes at `x` and at
`C.expI ξ • x`, then `C.expI ξ` fixes `x`. -/
theorem expI_smul_eq_self_of_moment_eq_zero [ContMDiffSMul IC I' ∞ Gc M]
    {C : LieComplexification I G IC Gc} (h : IsComplexifiedAction C J)
    (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w))
    {ξ : GroupLieAlgebra I G} {x : M} (hx : μ x = 0) (hξx : μ (C.expI ξ • x) = 0) :
    C.expI ξ • x = x := by
  -- `t ↦ μ (C.expI (t • ξ) • x) ξ` is antitone and vanishes at `0` and `1`, so it vanishes on
  -- `[0, 1]` with its derivative `-‖X_ξ‖²`; the curve, of velocity `J X_ξ`, is then constant.
  have hanti := antitone_moment_expI h hμ hg ξ x
  have hf0 : μ (C.expI ((0 : ℝ) • ξ) • x) ξ = 0 := by
    rw [zero_smul, C.expI_zero, one_smul, hx, LinearMap.zero_apply]
  have hf1 : μ (C.expI ((1 : ℝ) • ξ) • x) ξ = 0 := by
    rw [one_smul, hξx, LinearMap.zero_apply]
  -- The fundamental vector field of `ξ` vanishes along the curve on `[0, 1]`.
  have hX (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      fundamentalVectorField I' ξ (C.expI (t • ξ) • x) = 0 := by
    have hD := hasDerivAt_moment_expI h hμ hg ξ x t
    have hft : μ (C.expI (t • ξ) • x) ξ = 0 :=
      le_antisymm (hf0 ▸ hanti ht.1) (hf1 ▸ hanti ht.2)
    have h0 : -‖fundamentalVectorField I' ξ (C.expI (t • ξ) • x)‖ ^ 2 = 0 := by
      rcases ht.2.lt_or_eq with ht1 | rfl
      · -- Left of `1` the function stays above its value `0` at `t`.
        refine IsLocalMin.hasDerivAt_eq_zero ?_ hD
        filter_upwards [Iio_mem_nhds ht1] with s hs
        exact (hft.trans hf1.symm).trans_le (hanti (Set.mem_Iio.1 hs).le)
      · -- Right of `0` the function stays below its value `0` at `1`.
        refine IsLocalMax.hasDerivAt_eq_zero ?_ hD
        filter_upwards [Ioi_mem_nhds zero_lt_one] with s hs
        exact (hanti (Set.mem_Ioi.1 hs).le).trans_eq (hf0.trans hft.symm)
    simpa using h0
  have hconst := (convex_Icc (0 : ℝ) 1).apply_eq_of_hasMFDerivWithinAt_zero (J := I')
    (g := fun t : ℝ ↦ C.expI (t • ξ) • x) (fun t ht ↦ ?_) (Set.left_mem_Icc.2 zero_le_one)
    (Set.right_mem_Icc.2 zero_le_one)
  · simpa only [zero_smul, C.expI_zero, one_smul] using hconst.symm
  · have hγ := (h.isMIntegralCurve_expI_smul ξ x t).hasMFDerivWithinAt (s := Set.Icc 0 1)
    beta_reduce at hγ
    rwa [hX t ht, map_zero, ContinuousLinearMap.smulRight_zero] at hγ

end Gradient

/-! ### The Kempf–Ness one-form is closed -/

section Closed

open _root_.Bundle
open scoped RealInnerProductSpace GroupLieAlgebra

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ EC] [CompleteSpace E']
  [ContMDiffSMul I I' ∞ G M] [ContMDiffSMul IC I' ∞ Gc M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I' x)]
  {σ : SmoothTwoForm I' M} {J : SmoothAlmostComplexStructure I' M}
  {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)} {C : LieComplexification I G IC Gc}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [IsManifold I' ∞ M] [MulAction G M] [CompleteSpace E'] [ContMDiffSMul I I' ∞ G M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I' x)] in
/-- The Kempf–Ness one-form along a map into `Gc` is differentiable: for a smooth map
`γ : F → Gc` from a normed space and a direction `v`, the function
`z ↦ μ ((γ z)⁻¹ • p) (C.im (d(L_{(γ z)⁻¹})(dγ_z v)))` is differentiable when `Gc` acts smoothly
and each component `x ↦ μ x ξ` of `μ` is smooth. -/
theorem differentiable_moment_inv_smul_im_mfderiv
    (hμ : ∀ ξ, ContMDiff I' 𝓘(ℝ) ∞ fun x ↦ μ x ξ) (p : M) {γ : F → Gc}
    (hγ : ContMDiff 𝓘(ℝ, F) IC ∞ γ) (v : F) :
    Differentiable ℝ fun z ↦ μ ((γ z)⁻¹ • p)
      (C.im (mfderiv IC IC ((γ z)⁻¹ * ·) (γ z) (mfderiv 𝓘(ℝ, F) IC γ z v))) := by
  -- The function pairs a smooth family of covectors with `C.im` of the left-trivialized
  -- derivative of `γ`.
  have hx : ContMDiff 𝓘(ℝ, F) I' ∞ fun z ↦ (γ z)⁻¹ • p :=
    ((contMDiff_inv IC ∞).comp hγ).smul contMDiff_const
  refine differentiable_dual_comp_apply (fun ξ ↦ (hμ ξ).mdifferentiable (by simp))
    (hx.mdifferentiable (by simp))
    ((LinearMap.toContinuousLinearMap C.im).differentiable.comp
      (differentiable_mfderiv_inv_mul_mfderiv hγ v))

/-- **The Kempf–Ness one-form is closed along maps into `Gc`.** Let the action of `Gc` be a
complexified action, let `-μ` be an equivariant moment map for `σ`, and let the metric be
`g(u, w) = σ(u, J w)`. For a smooth map `γ : F → Gc` from a normed space, write
`a_u z = d(L_{(γ z)⁻¹})(dγ_z u)` for the left-trivialized derivative of `γ` in the direction `u`,
and `A_u z = μ ((γ z)⁻¹ • p) (C.im (a_u z))`. Then `∂_v A_w = ∂_w A_v`: the one-form
`ĝ ↦ μ (g⁻¹ • p) (C.im (g⁻¹ ĝ))` on `Gc` pulls back along `γ` to a closed form. For
`F = ℝ × ℝ` and the coordinate directions this is `∂_s A = ∂_t B`, with `A` built from the
derivative in `t` and `B` from that in `s`. -/
theorem fderiv_moment_inv_smul_im_comm (h : IsComplexifiedAction C J)
    (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w))
    (p : M) {γ : F → Gc} (hγ : ContMDiff 𝓘(ℝ, F) IC ∞ γ) (y v w : F) :
    fderiv ℝ (fun z ↦ μ ((γ z)⁻¹ • p)
        (C.im (mfderiv IC IC ((γ z)⁻¹ * ·) (γ z) (mfderiv 𝓘(ℝ, F) IC γ z w)))) y v =
      fderiv ℝ (fun z ↦ μ ((γ z)⁻¹ • p)
        (C.im (mfderiv IC IC ((γ z)⁻¹ * ·) (γ z) (mfderiv 𝓘(ℝ, F) IC γ z v)))) y w := by
  -- The left trivializations of the derivatives of `γ` are the left Maurer–Cartan form along `γ`.
  set θ := leftMaurerCartanForm IC Gc
  set a : F → F → GroupLieAlgebra IC Gc := fun u z ↦ θ.val (γ z) ![mfderiv 𝓘(ℝ, F) IC γ z u]
  have ha (u z : F) : mfderiv IC IC ((γ z)⁻¹ * ·) (γ z) (mfderiv 𝓘(ℝ, F) IC γ z u) = a u z := by
    simp [a, θ, leftMaurerCartanForm_apply]
  simp only [ha]
  have hμc := hμ.toIsMomentMap.contMDiff_of_neg
  have hx : ContMDiff 𝓘(ℝ, F) I' ∞ fun z ↦ (γ z)⁻¹ • p :=
    ((contMDiff_inv IC ∞).comp hγ).smul contMDiff_const
  have hda (u : F) : Differentiable ℝ (a u) := by
    simpa only [ha] using differentiable_mfderiv_inv_mul_mfderiv hγ u
  set imL := LinearMap.toContinuousLinearMap C.im
  have hdim (u : F) (r : F) : fderiv ℝ (fun z ↦ C.im (a u z)) y r = C.im (fderiv ℝ (a u) y r) :=
    congr($(imL.fderiv_comp_left (hda u y)) r)
  -- The derivative of the moving point is minus the fundamental vector field of `a u`.
  have hdx (u : F) : mfderiv 𝓘(ℝ, F) I' (fun z ↦ (γ z)⁻¹ • p) y u =
      -(fundamentalVectorField I' (C.re (a u y)) ((γ y)⁻¹ • p) +
        J ((γ y)⁻¹ • p) (fundamentalVectorField I' (C.im (a u y)) ((γ y)⁻¹ • p))) := by
    rw [mfderiv_inv_smul_comp_apply (hγ.mdifferentiableAt (by simp))
      (((ContMDiffSMul.contMDiff_smul_const (n := ∞) p).comp (contMDiff_inv IC ∞)
        ).mdifferentiableAt (by simp)) u, ha, h.fundamentalVectorField_eq_re_add_im]
  set x₀ := (γ y)⁻¹ • p
  have hside (u u' : F) : fderiv ℝ (fun z ↦ μ ((γ z)⁻¹ • p) (C.im (a u' z))) y u =
      μ x₀ (C.im (fderiv ℝ (a u') y u)) +
        σ.eval₂ x₀ (fundamentalVectorField I' (C.im (a u' y)) x₀)
          (fundamentalVectorField I' (C.re (a u y)) x₀) +
        ⟪fundamentalVectorField I' (C.im (a u' y)) x₀,
          fundamentalVectorField I' (C.im (a u y)) x₀⟫ := by
    have hc : DifferentiableAt ℝ (fun z ↦ C.im (a u' z)) y := by
      simpa [imL, Function.comp_def] using imL.differentiableAt.comp y (hda u' y)
    rw [fderiv_dual_comp_apply (fun ξ ↦ (hμc ξ).mdifferentiableAt (by simp))
        (hx.mdifferentiableAt (by simp)) hc u, hdim, hμ.toIsMomentMap.mvfderiv_apply_of_neg,
      InfinitesimalAction.fundamental_apply, hdx, SmoothBundleForm.eval₂_neg_right,
      SmoothBundleForm.eval₂_add_right, hg]
    ring
  have hcoc := SmoothTwoForm.momentCocycle_eq_zero_iff.1 (hμ.momentCocycle_eq_zero x₀)
  simp only [InfinitesimalAction.fundamental_apply] at hcoc
  -- The structure equation, read through `C.im` and `μ x₀`.
  have hs0 : fderiv ℝ (a w) y v - fderiv ℝ (a v) y w = -⁅a v y, a w y⁆ :=
    fderiv_leftMaurerCartanForm_mfderiv_sub hγ y v w
  have hs := congrArg (fun ξ ↦ μ x₀ (C.im ξ)) hs0
  simp only [map_sub, map_neg, LieComplexification.im_lie, map_add] at hs
  rw [hside, hside, hcoc, hcoc, real_inner_comm, ← lie_skew (C.im (a w y))]
  simp only [LinearMap.neg_apply, map_neg]
  linarith

end Closed

/-! ### The example: `ℂˣ` acting on `ℂ` -/

section Circle

open Complex

/-- **`ℂˣ` acting on `ℂ` is a complexified action.** The action of `ℂˣ` on `ℂ` by multiplication,
with the almost complex structure of `ℂ` given by multiplication by `i`
(`SmoothAlmostComplexStructure.ofComplexManifold`), is a complexified action of the rotation
action of `Circle`, for the complexification `LieComplexification.circle`. -/
theorem isComplexifiedAction_circle :
    IsComplexifiedAction LieComplexification.circle
      (SmoothAlmostComplexStructure.ofComplexManifold ℂ ℂ) where
  toHom_smul u z := by
    rw [Units.smul_def, LieComplexification.circle_toHom, Circle.coe_contMDiffToUnits_apply,
      Circle.smul_def]
  fundamentalVectorField_cplx ξ z := by
    -- The orbit map of `z` is holomorphic, so its real differential commutes with `i`.
    have hf : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (fun g : ℂˣ ↦ g • z) 1 :=
      (ContMDiffSMul.contMDiff_smul_const (I := 𝓘(ℂ, ℂ)) (I' := 𝓘(ℂ, ℂ)) (n := 1)
        z).mdifferentiableAt one_ne_zero
    rw [fundamentalVectorField_apply, fundamentalVectorField_apply,
      LieComplexification.circle_cplx, SmoothAlmostComplexStructure.almostComplexStructureAt_apply]
    -- The two sides are `i` times the same vector, at the points `1 • z` and `z`.
    exact (hf.mfderiv_ofComplexManifold_apply _).trans
      ((SmoothAlmostComplexStructure.ofComplexManifold_apply _ _).trans
        (SmoothAlmostComplexStructure.ofComplexManifold_apply _ _).symm)

end Circle

end SymplecticGeometry
