/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DeRham.Hodge.L2
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Smooth
public import TauCeti.Geometry.Manifold.Riemannian.Codifferential
public import SymplecticGeometry.Geometry.Manifold.DeRham.Hodge.Regularity
public import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.Tempered
public import TauCeti.Analysis.Sobolev.BesselPotential.Distribution
public import TauCeti.MeasureTheory.Function.Lp.Precomposition
public import TauCeti.Geometry.Manifold.Riemannian.Sobolev.H1
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Friedrichs.Basic
import SymplecticGeometry.Analysis.Distribution.Support
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.Basic
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.ChartCover
import TauCeti.Analysis.Normed.Operator.Compact.Domination
import TauCeti.Analysis.Distribution.SchwartzSpace.Cutoff
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Sobolev.BesselPotential.Inclusion
import TauCeti.Analysis.Sobolev.BesselPotential.Rellich
import TauCeti.MeasureTheory.Function.Lp.FiniteDimensional
import TauCeti.MeasureTheory.Measure.Haar.Unique

/-!
# The Hodge `H¹` space of differential forms

Let `M` be a closed oriented Riemannian manifold, `Δ = dδ + δd` its Hodge Laplacian on real
`k`-forms and `⟪α, β⟫ = ∫_M ⟨α, β⟩ dV` the `L²` inner product of smooth forms
(`TauCeti.SmoothForm.l2Inner`). Since `Δ` is symmetric and nonnegative for this inner product,
`⟪α, β⟫ + ⟪Δα, β⟫ = ⟪α, β⟫ + ⟪dα, dβ⟫ + ⟪δα, δβ⟫` is again an inner product on the smooth forms,
and it is definite because the `L²` part is. The Hilbert space `SymplecticGeometry.H1Form o hkl`
is the completion of the smooth `k`-forms for it.

Its norm dominates the `L²` norm, so the identity of smooth forms extends to a continuous linear
map `H1Form.toL2 : H1Form o hkl →L[ℝ] L2Form I M k` of norm at most one. The
**Dirichlet form** `H1Form.dirichlet u v = ⟪u, v⟫ - ⟪toL2 u, toL2 v⟫` is a continuous bilinear
form on `H1Form o hkl` that extends `⟪Δα, β⟫`, so that `‖u‖ ^ 2 = dirichlet u u + ‖toL2 u‖ ^ 2`
(Gårding's identity) holds by definition. Against a smooth form it is the weak Laplacian:
`dirichlet u (ofSmooth φ) = ⟪toL2 u, Δφ⟫`, which gives Green's identity
`⟪u, ofSmooth φ⟫ = ⟪toL2 u, φ + Δφ⟫`. Hence an element `u` with `toL2 u = 0` is orthogonal to
every smooth form, and `toL2` is injective. The Dirichlet form is nonnegative, so it satisfies
the Cauchy–Schwarz inequality, which bounds `|⟪toL2 u, Δφ⟫|` by `‖u‖` times the `H¹` norm
`√(‖φ‖ ^ 2 + ⟪Δφ, φ⟫)` of `φ`.

By `SymplecticGeometry.L2Form.isLocallySobolev_one_of_forall_inner`, that bound makes every
element of `H1Form o hkl` locally `H¹` in each chart. Fix a chart `ψ`, a smooth cutoff `χ`
supported in its source, a basis `bΛ` of the forms on `E`, an index `p` and coordinates
`e : E ≃L[ℝ] CoordinateSpace n`. The complexified `p`-th coordinate of the localization of an
`L²` form `u`, read through `e⁻¹`, is an `L²` function on `CoordinateSpace n`
(`SymplecticGeometry.L2Form.localizeCoord`). Its distribution is, up to a nonzero constant, the
coordinate distribution `Distribution.coordOfFun` of the localization, and it vanishes outside
the compact image of the support of `χ`. So, for `u = toL2 v` with `v` in `H1Form o hkl`, Tau
Ceti's `TemperedDistribution.memSobolev_of_isCompact_dsupport_of_forall_isLocallySobolevAt` puts
it in the Bessel-potential space `H^1` of `CoordinateSpace n`. This defines a linear map
`H1Form.localizeSobolev` from `H1Form o hkl` to `H^1`. Its graph is closed, because `H1Form o hkl`
and `H^1` both map continuously into the tempered distributions, the second one injectively, so
the map is bounded by the closed graph theorem `LinearMap.continuous_of_isClosed_graph`.

The inclusion `H1Form.toL2` is a compact operator (`H1Form.isCompactOperator_toL2`). In a chart,
take a Schwartz function `φ` equal to `1` near the compact set outside which the coordinate
`L2Form.localizeCoord` of `toL2 u` vanishes. Multiplying by `φ` leaves that coordinate unchanged,
so it is the image of `H1Form.localizeSobolev u` under multiplication by `φ` followed by the
inclusion of `H^1` into `L²`, which is compact by Tau Ceti's Rellich theorem
`BesselPotentialSpace.isCompactOperator_inclusion_comp_smulLeftCLM`
(`H1Form.isCompactOperator_localizeCoord_comp_toL2`). For a finite atlas and a subordinate
partition of unity, the `L²` norm of a form is bounded by the norms of its localizations
(`L2Form.exists_norm_le_sum_norm_localize`), and each localization by the norms of its
coordinates (`L2Form.exists_norm_localize_le_mul_sum_norm_localizeCoord`). So `toL2` is
dominated by finitely many compact operators, and is compact by
Tau Ceti's `IsCompactOperator.of_norm_le_mul_sum`.

In degree zero, `H1Form o hl` for `hl : 0 + l = m` is Tau Ceti's Sobolev space
`TauCeti.Manifold.SobolevH1 I M`, the completion of the smooth functions for
`∫ a b dV + ∫ ⟪∇a, ∇b⟫ dV`. A smooth `0`-form `α` is the smooth function `a = (x ↦ α x 0)`, the
`L²` inner product of two `0`-forms is `∫ a b dV`, and `⟪Δα, β⟫ = ∫ ⟪∇a, ∇b⟫ dV`, since the Hodge
Laplacian of a function is minus its Laplace–Beltrami operator and by Green's first identity
(`TauCeti.SmoothForm.l2Inner_hodgeLaplacian_zero_eq_integral_inner_mgradient`). So the two inner
products agree on smooth functions, and the identification extends to a linear isometric
equivalence `H1Form.sobolevH1Equiv o hl : H1Form o hl ≃ₗᵢ[ℝ] SobolevH1 I M`, which carries
`H1Form.dirichlet` to `SobolevH1.dirichletForm`, and so the `L²` inner product of the images
under `toL2` to that of the images under `SobolevH1.toLp`. Tau Ceti's Green identity asks for a
model without boundary, `I.Boundaryless`, and so does this equivalence.

## Main definitions and results

* `SymplecticGeometry.H1Form o hkl`: the Hilbert space, with `H1Form.ofSmooth`,
  `H1Form.inner_ofSmooth`, `H1Form.norm_ofSmooth_sq`, `H1Form.ofSmooth_injective`,
  `H1Form.denseRange_ofSmooth` and `H1Form.induction_on`.
* `SymplecticGeometry.H1Form.toL2`: the inclusion into `L2Form I M k`, with `toL2_ofSmooth`,
  `norm_toL2_le`, `inner_ofSmooth_right` and `toL2_injective`.
* `SymplecticGeometry.H1Form.dirichlet`: the Dirichlet form, with `dirichlet_ofSmooth`,
  `dirichlet_comm`, `dirichlet_self_nonneg`, `norm_sq_eq_dirichlet_add`,
  `dirichlet_ofSmooth_right` and `abs_dirichlet_le`.
* `SymplecticGeometry.H1Form.abs_inner_toL2_ofSmooth_hodgeLaplacian_le`: the bound
  `|⟪toL2 u, Δφ⟫| ≤ ‖u‖ * √(‖φ‖ ^ 2 + ⟪Δφ, φ⟫)`, the hypothesis of
  `SymplecticGeometry.L2Form.isLocallySobolev_one_of_forall_inner`.
* `SymplecticGeometry.H1Form.sobolevH1Equiv`: in degree zero, the linear isometric equivalence
  with `TauCeti.Manifold.SobolevH1 I M`, with `sobolevH1Equiv_ofSmooth`,
  `sobolevH1Equiv_symm_ofSmooth`, `dirichletForm_sobolevH1Equiv` and
  `inner_toLp_sobolevH1Equiv`.
* `SymplecticGeometry.L2Form.localizeCoord`: a coordinate of the localization of an `L²` form,
  as an `L²` function on `CoordinateSpace n`, with `L2Form.coeFn_localizeCoord`,
  `L2Form.coordOfFun_localize_eq_smul` and `L2Form.memSobolev_localizeCoord_of_forall_inner`.
* `SymplecticGeometry.H1Form.localizeSobolev`: the localization of `H1Form o hkl` to the
  Bessel-potential space `H^1` of `CoordinateSpace n`, a continuous linear map, with
  `H1Form.toDistr_localizeSobolev`.
* `SymplecticGeometry.L2Form.localizeCoord_ae_eq_zero_of_notMem` and
  `SymplecticGeometry.L2Form.exists_norm_localize_le_mul_sum_norm_localizeCoord`: the
  coordinates vanish outside the image of the support of the cutoff, and they control the
  localization.
* `SymplecticGeometry.H1Form.isCompactOperator_localizeCoord_comp_toL2`: Rellich's theorem in a
  chart.
* `SymplecticGeometry.H1Form.isCompactOperator_toL2`: the inclusion of `H1Form o hkl` into
  `L2Form I M k` is compact.

## Implementation notes

The construction of `H1Form` through the type synonym `SymplecticGeometry.PreH1Form`, and the
names and proofs of `ofSmooth`, `inner_ofSmooth`, `denseRange_ofSmooth`, `induction_on`,
`dirichlet`, `dirichlet_comm`, `dirichlet_self_nonneg`, `norm_sq_eq_dirichlet_add`,
`dirichlet_ofSmooth_right`, `inner_ofSmooth_right` and `toL2_injective`, adapt those of Tau
Ceti's `TauCeti.Manifold.SobolevH1` (`TauCeti/Geometry/Manifold/Riemannian/Sobolev/H1.lean`,
itself after Mathlib's `PreGNS`: `SobolevH1.ofSmooth`, `SobolevH1.dirichletForm`,
`SobolevH1.dirichletForm_comm`, `SobolevH1.dirichletForm_self_nonneg`,
`SobolevH1.norm_sq_eq_dirichletForm_add`, `SobolevH1.dirichletForm_ofSmooth_right`,
`SobolevH1.inner_ofSmooth_right` and `SobolevH1.toLp_injective`), with smooth `k`-forms and the
Hodge Laplacian in place of smooth functions and the gradient, and `L2Form` in place of
`Lp ℝ 2`. Since the `L²` part of the inner product is definite, the type synonym carries an
`InnerProductSpace.Core` rather than a `PreInnerProductSpace.Core`, as in `L2.lean`. As
`L2Form.localize` does, `toL2` is Mathlib's extension `LinearMap.extendOfNorm` of the
inclusion of smooth forms into `L2Form I M k`, which is bounded by `norm_l2FormOfSmooth_le`.

The Bessel-potential space `H^1` is a complex space; `H1Form.localizeSobolev` is linear over `ℝ`
for its real structure. The change of variables along `e⁻¹` in `L2Form.localizeCoord` is Tau
Ceti's `MeasureTheory.Lp.compOfMapLeSmul`, since the image of the volume of `CoordinateSpace n`
is a multiple of the volume of `E`.

The proof of `H1Form.isCompactOperator_localizeCoord_comp_toL2` follows that of Tau Ceti's
`TauCeti.Symbol.isCompactOperator_inclusion_comp_quantizeSobolev`: a Schwartz cutoff equal to `1`
near a common compact support (`IsCompact.exists_schwartzMap_cutoff`), multiplication by which
is the identity, reduces compactness to
`BesselPotentialSpace.isCompactOperator_inclusion_comp_smulLeftCLM`.

As Tau Ceti's `TauCeti.Manifold.SobolevH1.compRiemannianIsometry`
(`TauCeti/Geometry/Manifold/Riemannian/Sobolev/Isometry.lean`) does for pullback along a
Riemannian isometry, `sobolevH1Equiv` is Mathlib's `LinearEquiv.extendOfIsometry` of a linear
equivalence of the dense smooth parts, here `TauCeti.SmoothForm.ofFunctionEquiv`.

## References

* F. W. Warner, *Foundations of Differentiable Manifolds and Lie Groups*, Graduate Texts in
  Mathematics 94, Springer, 1983, Chapter 6.
* [P. Griffiths, J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978],
  Chapter 0, §6.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §2.2 (support of a
  distribution) and §7.1 (tempered distributions).
* G. B. Folland, *Introduction to Partial Differential Equations*, 2nd ed., Princeton University
  Press, 1995, Chapter 6 (Rellich's theorem).
-/

public section

open Bundle MeasureTheory
open scoped Manifold ContDiff InnerProductSpace

noncomputable section

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {m k l : ℕ}

namespace SymplecticGeometry

open TauCeti TauCeti.SmoothForm

variable [IsManifold I ∞ M]

variable [CompactSpace M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

namespace L2Form

variable (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m)

/-- The **Hodge Laplacian** `Δ = dδ + δd` as a partial operator on `L2Form I M k`, whose domain
is the image of the smooth `k`-forms. -/
def hodgeLaplacian : L2Form I M k →ₗ.[ℝ] L2Form I M k where
  domain := LinearMap.range (ofSmooth : SmoothForm I M ℝ k →ₗ[ℝ] L2Form I M k)
  toFun := ofSmooth ∘ₗ SmoothForm.hodgeLaplacian o hkl ∘ₗ
    (LinearEquiv.ofInjective _ ofSmooth_injective).symm.toLinearMap

/-- The domain of the Hodge Laplacian on `L2Form I M k` is the image of the smooth forms. -/
theorem domain_hodgeLaplacian :
    (hodgeLaplacian o hkl).domain =
      LinearMap.range (ofSmooth : SmoothForm I M ℝ k →ₗ[ℝ] L2Form I M k) :=
  (rfl)

/-- The linear equivalence of the smooth forms with the domain of the Hodge Laplacian on
`L2Form I M k`. -/
def toDomainHodgeLaplacian : SmoothForm I M ℝ k ≃ₗ[ℝ] (hodgeLaplacian o hkl).domain :=
  LinearEquiv.ofInjective _ ofSmooth_injective

/-- The vector of the domain of the Hodge Laplacian given by a smooth form `α` is `α` in
`L2Form I M k`. -/
@[simp]
theorem coe_toDomainHodgeLaplacian (α : SmoothForm I M ℝ k) :
    (toDomainHodgeLaplacian o hkl α : L2Form I M k) = ofSmooth α :=
  (rfl)

/-- The Hodge Laplacian on `L2Form I M k` applies `TauCeti.SmoothForm.hodgeLaplacian` to the smooth
form of a vector of its domain. -/
theorem hodgeLaplacian_apply (x : (hodgeLaplacian o hkl).domain) :
    hodgeLaplacian o hkl x =
      ofSmooth (SmoothForm.hodgeLaplacian o hkl ((toDomainHodgeLaplacian o hkl).symm x)) :=
  (rfl)

/-- On a smooth form, the Hodge Laplacian on `L2Form I M k` is that of `TauCeti.SmoothForm`. -/
@[simp]
theorem hodgeLaplacian_toDomainHodgeLaplacian (α : SmoothForm I M ℝ k) :
    hodgeLaplacian o hkl (toDomainHodgeLaplacian o hkl α) =
      ofSmooth (SmoothForm.hodgeLaplacian o hkl α) := by
  rw [hodgeLaplacian_apply, LinearEquiv.symm_apply_apply]

variable [BoundarylessManifold I M] [T2Space M]

/-- The Hodge Laplacian on `L2Form I M k` is symmetric and nonnegative. -/
theorem isSymmetricBoundedBelow_hodgeLaplacian :
    (hodgeLaplacian o hkl).IsSymmetricBoundedBelow 0 where
  isFormalAdjoint x y := by
    obtain ⟨α, rfl⟩ := (toDomainHodgeLaplacian o hkl).surjective x
    obtain ⟨β, rfl⟩ := (toDomainHodgeLaplacian o hkl).surjective y
    rw [hodgeLaplacian_toDomainHodgeLaplacian, hodgeLaplacian_toDomainHodgeLaplacian,
      coe_toDomainHodgeLaplacian, coe_toDomainHodgeLaplacian, inner_ofSmooth o, inner_ofSmooth o,
      l2Inner_hodgeLaplacian_eq_l2Inner_hodgeLaplacian]
  mul_norm_sq_le_re_inner x := by
    obtain ⟨α, rfl⟩ := (toDomainHodgeLaplacian o hkl).surjective x
    rw [zero_mul, hodgeLaplacian_toDomainHodgeLaplacian, coe_toDomainHodgeLaplacian,
      inner_ofSmooth o, RCLike.re_to_real]
    exact l2Inner_hodgeLaplacian_self_nonneg o hkl α

end L2Form

variable [BoundarylessManifold I M] [T2Space M]
  {o : Manifold.Orientation I M (Fin m)} {hkl : k + l = m}

open LinearPMap

/-- The proof that the Hodge Laplacian is symmetric and nonnegative, inferred from the context. -/
local notation "hΔ" => L2Form.isSymmetricBoundedBelow_hodgeLaplacian _ _

/-- The **Hodge `H¹` space** of `k`-forms on a closed oriented Riemannian manifold of dimension
`m = k + l`: the completion of the smooth real `k`-forms for the inner product
`⟪Δα, β⟫ + ⟪α, β⟫`, where `⟪·, ·⟫` is the `L²` inner product and `Δ` the Hodge Laplacian. It is
the form domain `LinearPMap.FriedrichsSpace` of the Hodge Laplacian on `L2Form I M k`, with lower
bound `0`. -/
abbrev H1Form (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m) :=
  FriedrichsSpace (L2Form.hodgeLaplacian o hkl) 0
    (L2Form.isSymmetricBoundedBelow_hodgeLaplacian o hkl)

namespace H1Form


/-- The inclusion of the smooth forms into `H1Form o hkl`. -/
def ofSmooth : SmoothForm I M ℝ k →ₗ[ℝ] H1Form o hkl :=
  toFriedrichsSpace hΔ ∘ₗ L2Form.toDomainHodgeLaplacian o hkl

/-- A smooth form in `H1Form o hkl` is the image of its vector in the domain of the Hodge
Laplacian. -/
theorem ofSmooth_apply (α : SmoothForm I M ℝ k) :
    (ofSmooth α : H1Form o hkl) = toFriedrichsSpace hΔ (L2Form.toDomainHodgeLaplacian o hkl α) :=
  (rfl)

/-- The inner product of two smooth forms in `H1Form o hkl` is `⟪α, β⟫ + ⟪Δα, β⟫`. -/
@[simp]
theorem inner_ofSmooth (α β : SmoothForm I M ℝ k) :
    ⟪(ofSmooth α : H1Form o hkl), ofSmooth β⟫_ℝ =
      l2Inner o α β + l2Inner o (hodgeLaplacian o hkl α) β := by
  rw [ofSmooth_apply, ofSmooth_apply, inner_toFriedrichsSpace,
    L2Form.hodgeLaplacian_toDomainHodgeLaplacian, L2Form.coe_toDomainHodgeLaplacian,
    L2Form.coe_toDomainHodgeLaplacian, L2Form.inner_ofSmooth o, L2Form.inner_ofSmooth o]
  simp [add_comm]

/-- The squared norm of a smooth form in `H1Form o hkl` is `⟪α, α⟫ + ⟪Δα, α⟫`. -/
theorem norm_ofSmooth_sq (α : SmoothForm I M ℝ k) :
    ‖(ofSmooth α : H1Form o hkl)‖ ^ 2 = l2Inner o α α + l2Inner o (hodgeLaplacian o hkl α) α := by
  rw [← real_inner_self_eq_norm_sq, inner_ofSmooth]

/-- The inclusion of the smooth forms into `H1Form o hkl` is injective. -/
theorem ofSmooth_injective :
    Function.Injective (ofSmooth : SmoothForm I M ℝ k → H1Form o hkl) :=
  (toFriedrichsSpace_injective hΔ).comp (L2Form.toDomainHodgeLaplacian o hkl).injective

/-- The smooth forms are dense in `H1Form o hkl`. -/
theorem denseRange_ofSmooth : DenseRange (ofSmooth : SmoothForm I M ℝ k → H1Form o hkl) := by
  have h : (ofSmooth : SmoothForm I M ℝ k → H1Form o hkl) =
      toFriedrichsSpace hΔ ∘ L2Form.toDomainHodgeLaplacian o hkl := funext ofSmooth_apply
  rw [DenseRange, h, (L2Form.toDomainHodgeLaplacian o hkl).surjective.range_comp]
  exact denseRange_toFriedrichsSpace hΔ

/-- **Induction principle for `H1Form o hkl`.** A closed property of elements of `H1Form o hkl`
that holds for all smooth forms holds everywhere. -/
@[elab_as_elim]
theorem induction_on {p : H1Form o hkl → Prop} (u : H1Form o hkl) (hp : IsClosed {u | p u})
    (h : ∀ α : SmoothForm I M ℝ k, p (ofSmooth α)) : p u :=
  denseRange_ofSmooth.induction_on u hp h

/-! ### The inclusion into `L2Form` and the Dirichlet form

The inclusion of `H1Form o hkl` into `L2Form I M k` is `LinearPMap.friedrichsInclusion`, and the
Dirichlet form, which extends `⟪Δα, β⟫`, is `LinearPMap.friedrichsForm`. -/

/-- On a smooth form, the inclusion of `H1Form o hkl` into `L2Form I M k` is the inclusion of
smooth forms. -/
@[simp]
theorem friedrichsInclusion_ofSmooth (α : SmoothForm I M ℝ k) :
    friedrichsInclusion hΔ (ofSmooth α : H1Form o hkl) = L2Form.ofSmooth α := by
  rw [ofSmooth_apply, friedrichsInclusion_toFriedrichsSpace, L2Form.coe_toDomainHodgeLaplacian]

/-- The Dirichlet form of two smooth forms is `⟪Δα, β⟫`. -/
@[simp]
theorem friedrichsForm_ofSmooth (α β : SmoothForm I M ℝ k) :
    friedrichsForm hΔ (ofSmooth α : H1Form o hkl) (ofSmooth β) =
      l2Inner o (hodgeLaplacian o hkl α) β := by
  rw [ofSmooth_apply α, friedrichsForm_toFriedrichsSpace_left, friedrichsInclusion_ofSmooth,
    L2Form.hodgeLaplacian_toDomainHodgeLaplacian, L2Form.inner_ofSmooth o]

/-- **The Dirichlet form against a smooth form** is the weak Laplacian:
`D(u, φ) = ⟪u, Δφ⟫` in `L2Form I M k`. -/
theorem friedrichsForm_ofSmooth_right (u : H1Form o hkl) (φ : SmoothForm I M ℝ k) :
    friedrichsForm hΔ u (ofSmooth φ) =
      ⟪friedrichsInclusion hΔ u, L2Form.ofSmooth (hodgeLaplacian o hkl φ)⟫_ℝ := by
  rw [ofSmooth_apply, friedrichsForm_toFriedrichsSpace_right,
    L2Form.hodgeLaplacian_toDomainHodgeLaplacian]

/-- **Gårding's identity**: the squared `H¹` norm is the Dirichlet energy plus the squared `L²`
norm. -/
theorem norm_sq_eq_friedrichsForm_add (u : H1Form o hkl) :
    ‖u‖ ^ 2 = friedrichsForm hΔ u u + ‖friedrichsInclusion hΔ u‖ ^ 2 := by
  have h := re_friedrichsForm_self hΔ u
  rw [RCLike.re_to_real] at h
  linarith

/-- **Cauchy–Schwarz inequality for the Dirichlet form**: `|D(u, v)| ≤ ‖u‖ * ‖v‖`. -/
theorem abs_friedrichsForm_le (u v : H1Form o hkl) :
    |friedrichsForm hΔ u v| ≤ ‖u‖ * ‖v‖ := by
  let B : H1Form o hkl →L[ℝ] H1Form o hkl →L[ℝ] ℝ := friedrichsForm hΔ
  have h0 (w : H1Form o hkl) : 0 ≤ B w w := by
    simpa using mul_norm_sq_le_re_friedrichsForm hΔ w
  have hD (w : H1Form o hkl) : B w w ≤ ‖w‖ ^ 2 := by
    rw [norm_sq_eq_friedrichsForm_add w]
    exact le_add_of_nonneg_right (sq_nonneg _)
  have hcs : B u v * B v u ≤ B u u * B v v :=
    LinearMap.BilinForm.apply_mul_apply_le_of_forall_zero_le B.toLinearMap₁₂ h0 u v
  have hcomm : B v u = B u v := by
    simpa using (friedrichsForm_eq_star hΔ v u)
  rw [hcomm] at hcs
  refine abs_le_of_sq_le_sq ?_ (by positivity)
  rw [mul_pow]
  calc B u v ^ 2 ≤ B u u * B v v := by rwa [sq]
    _ ≤ ‖u‖ ^ 2 * ‖v‖ ^ 2 := mul_le_mul (hD u) (hD v) (h0 v) (sq_nonneg _)

/-- The pairing of an element of `H1Form o hkl` with the Laplacian of a smooth form `φ` is
bounded by its norm times the Hodge `H¹` norm `√(‖φ‖ ^ 2 + ⟪Δφ, φ⟫)` of `φ`, computed in
`L2Form I M k`. This is the hypothesis of `L2Form.isLocallySobolev_one_of_forall_inner` for
the image of `u` in `L2Form I M k`. -/
theorem abs_inner_friedrichsInclusion_ofSmooth_hodgeLaplacian_le (u : H1Form o hkl)
    (φ : SmoothForm I M ℝ k) :
    |⟪friedrichsInclusion hΔ u, L2Form.ofSmooth (hodgeLaplacian o hkl φ)⟫_ℝ| ≤
      ‖u‖ * √(‖(L2Form.ofSmooth φ : L2Form I M k)‖ ^ 2 +
        ⟪(L2Form.ofSmooth (hodgeLaplacian o hkl φ) : L2Form I M k), L2Form.ofSmooth φ⟫_ℝ) := by
  rw [← friedrichsForm_ofSmooth_right, L2Form.norm_ofSmooth_sq o, L2Form.inner_ofSmooth o,
    ← norm_ofSmooth_sq (hkl := hkl), Real.sqrt_sq (norm_nonneg _)]
  exact abs_friedrichsForm_le u (ofSmooth φ)

/-! ### Degree zero: Tau Ceti's Sobolev space of functions -/

section DegreeZero

/-- Tau Ceti's Riemannian volume measure and Sobolev space `H¹(M)` ask for a continuous metric. -/
local instance : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
  IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle
    (IB := I) (n := ∞) (F := E) (V := fun x : M ↦ TangentSpace I x)

variable [I.Boundaryless] [MeasurableSpace M] [BorelSpace M] {hl : 0 + l = m}

/-- On smooth `0`-forms, the Hodge `H¹` inner product `⟪α, β⟫ + ⟪Δα, β⟫` is Tau Ceti's `H¹`
inner product `∫ a b dV + ∫ ⟪∇a, ∇b⟫ dV` of the underlying functions. -/
private theorem inner_sobolevH1_ofSmooth_ofFunctionEquiv_symm (α β : SmoothForm I M ℝ 0) :
    ⟪Manifold.SobolevH1.ofSmooth (SmoothForm.ofFunctionEquiv.symm α),
        Manifold.SobolevH1.ofSmooth (SmoothForm.ofFunctionEquiv.symm β)⟫_ℝ =
      ⟪(ofSmooth α : H1Form o hl), ofSmooth β⟫_ℝ := by
  rw [Manifold.SobolevH1.inner_ofSmooth, inner_ofSmooth, l2Inner_zero_eq_integral,
    l2Inner_hodgeLaplacian_zero_eq_integral_inner_mgradient, SmoothForm.coe_ofFunctionEquiv_symm,
    SmoothForm.coe_ofFunctionEquiv_symm]

variable (o hl) in
/-- **In degree zero, the Hodge `H¹` space is Tau Ceti's Sobolev space `H¹(M)`.** On a closed
oriented Riemannian manifold whose model has no boundary, reading a smooth `0`-form `α` as the
smooth function `x ↦ α x 0` extends to a linear isometric equivalence of `H1Form o hl` with
`TauCeti.Manifold.SobolevH1 I M` (`H1Form.sobolevH1Equiv_ofSmooth`). -/
def sobolevH1Equiv : H1Form o hl ≃ₗᵢ[ℝ] Manifold.SobolevH1 I M :=
  SmoothForm.ofFunctionEquiv.symm.extendOfIsometry ofSmooth Manifold.SobolevH1.ofSmooth
    denseRange_ofSmooth Manifold.SobolevH1.denseRange_ofSmooth fun α ↦ by
      rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner (ofSmooth α : H1Form o hl),
        inner_sobolevH1_ofSmooth_ofFunctionEquiv_symm]

/-- `sobolevH1Equiv` sends a smooth `0`-form `α` to the smooth function `x ↦ α x 0`. -/
@[simp]
theorem sobolevH1Equiv_ofSmooth (α : SmoothForm I M ℝ 0) :
    sobolevH1Equiv o hl (ofSmooth α) =
      Manifold.SobolevH1.ofSmooth (SmoothForm.ofFunctionEquiv.symm α) :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ α

/-- The inverse of `sobolevH1Equiv` sends a smooth function `f` to its `0`-form. -/
@[simp]
theorem sobolevH1Equiv_symm_ofSmooth (f : C^∞⟮I, M; ℝ⟯) :
    (sobolevH1Equiv o hl).symm (Manifold.SobolevH1.ofSmooth f) =
      ofSmooth (SmoothForm.ofFunction f) := by
  rw [LinearIsometryEquiv.symm_apply_eq, sobolevH1Equiv_ofSmooth,
    SmoothForm.ofFunctionEquiv_symm_ofFunction]

/-- `sobolevH1Equiv` carries the Dirichlet form of `H1Form o hl` to Tau Ceti's Dirichlet form
`TauCeti.Manifold.SobolevH1.dirichletForm`. -/
@[simp]
theorem dirichletForm_sobolevH1Equiv (u v : H1Form o hl) :
    Manifold.SobolevH1.dirichletForm (sobolevH1Equiv o hl u) (sobolevH1Equiv o hl v) =
      friedrichsForm hΔ u v := by
  induction u using induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | h α =>
    induction v using induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | h β =>
      rw [sobolevH1Equiv_ofSmooth, sobolevH1Equiv_ofSmooth,
        Manifold.SobolevH1.dirichletForm_ofSmooth, friedrichsForm_ofSmooth,
        l2Inner_hodgeLaplacian_zero_eq_integral_inner_mgradient,
        SmoothForm.coe_ofFunctionEquiv_symm, SmoothForm.coe_ofFunctionEquiv_symm]

/-- `sobolevH1Equiv` carries the `L²` inner product of the images in `L2Form I M 0` to that of
the images under Tau Ceti's `TauCeti.Manifold.SobolevH1.toLp`. -/
theorem inner_toLp_sobolevH1Equiv (u v : H1Form o hl) :
    ⟪Manifold.SobolevH1.toLp (sobolevH1Equiv o hl u),
        Manifold.SobolevH1.toLp (sobolevH1Equiv o hl v)⟫_ℝ =
      ⟪friedrichsInclusion hΔ u, friedrichsInclusion hΔ v⟫_ℝ := by
  have h := Manifold.SobolevH1.dirichletForm_apply (sobolevH1Equiv o hl u) (sobolevH1Equiv o hl v)
  rw [dirichletForm_sobolevH1Equiv, friedrichsForm_apply, LinearIsometryEquiv.inner_map_map] at h
  norm_num at h
  linarith

end DegreeZero

end H1Form

/-! ### Localizations in `H¹` of a chart -/

section Localize

open scoped Distributions SchwartzMap BesselPotentialSpace
open TemperedDistribution

variable [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]
  (ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞) (χ : C^∞⟮I, M; ℝ⟯) (hχ : tsupport χ ⊆ ψ.source)
  {κ : Type*} (bΛ : Module.Basis κ ℝ (E [⋀^Fin k]→L[ℝ] ℝ)) (p : κ) {n : ℕ}
  (e : E ≃L[ℝ] CoordinateSpace n)

omit [BoundarylessManifold I M] [T2Space M] in
/-- The `p`-th coordinate in the basis `bΛ`, complexified, of the localization
`L2Form.localize ψ χ hχ` of an `L²` form, read in the coordinates `e : E ≃L[ℝ] CoordinateSpace n`:
the `L²` function `x ↦ (bΛ.repr (localize ψ χ hχ u (e⁻¹ x)) p : ℂ)` on `CoordinateSpace n`
(`L2Form.coeFn_localizeCoord`). -/
def L2Form.localizeCoord : L2Form I M k →L[ℝ] Lp ℂ 2 (volume : Measure (CoordinateSpace n)) :=
  Lp.compOfMapLeSmul ℝ e.symm.continuous.aemeasurable ENNReal.coe_ne_top
    (C := (((volume : Measure (CoordinateSpace n)).map e.symm).addHaarScalarFactor volume :
      ENNReal))
    (by rw [← ENNReal.smul_def, ← Measure.isAddLeftInvariant_eq_smul]) ∘L
    (Complex.ofRealCLM ∘L LinearMap.toContinuousLinearMap (bΛ.coord p)).compLpL 2 volume ∘L
      L2Form.localize ψ χ hχ

omit [BoundarylessManifold I M] [T2Space M] in
/-- `L2Form.localizeCoord ψ χ hχ bΛ p e u` is almost everywhere the complexified `p`-th
coordinate in `bΛ` of the localization of `u`, read through `e⁻¹`. -/
theorem L2Form.coeFn_localizeCoord (u : L2Form I M k) :
    L2Form.localizeCoord ψ χ hχ bΛ p e u =ᵐ[volume]
      fun x ↦ (bΛ.repr (L2Form.localize ψ χ hχ u (e.symm x)) p : ℂ) := by
  have hq : QuasiMeasurePreserving e.symm volume volume :=
    e.symm.toContinuousAddEquiv.quasiMeasurePreserving_addHaar _ _
  rw [L2Form.localizeCoord, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  refine (Lp.coeFn_compOfMapLeSmul _ _ _ _).trans ?_
  filter_upwards [hq.ae
    ((Complex.ofRealCLM ∘L LinearMap.toContinuousLinearMap (bΛ.coord p)).coeFn_compLpL
      (L2Form.localize ψ χ hχ u))] with x h
  rw [Function.comp_apply, h]
  simp

omit [BoundarylessManifold I M] [T2Space M] in
/-- `L2Form.localizeCoord ψ χ hχ bΛ p e u` vanishes almost everywhere outside the image under `e`
of the image under `ψ` of the support of `χ`. -/
theorem L2Form.localizeCoord_ae_eq_zero_of_notMem (u : L2Form I M k) :
    ∀ᵐ x ∂volume, x ∉ e '' (ψ '' tsupport χ) → L2Form.localizeCoord ψ χ hχ bΛ p e u x = 0 := by
  have hq : QuasiMeasurePreserving e.symm volume volume :=
    e.symm.toContinuousAddEquiv.quasiMeasurePreserving_addHaar _ _
  filter_upwards [L2Form.coeFn_localizeCoord ψ χ hχ bΛ p e u,
    hq.ae (L2Form.localize_ae_eq_zero_of_notMem ψ χ hχ u)] with x h₁ h₂ hx
  rw [h₁, h₂ fun h ↦ hx ⟨_, h, e.apply_symm_apply x⟩]
  simp

omit [BoundarylessManifold I M] [T2Space M] in
/-- **The localization is controlled by its coordinates.** There is a constant `C` such that the
`L²` norm of the localization `L2Form.localize ψ χ hχ u` is at most `C` times the sum over `p` of
the `L²` norms of its coordinates `L2Form.localizeCoord ψ χ hχ bΛ p e u`. -/
theorem L2Form.exists_norm_localize_le_mul_sum_norm_localizeCoord [Fintype κ] :
    ∃ C, ∀ u : L2Form I M k, ‖L2Form.localize ψ χ hχ u‖ ≤
      C * ∑ p, ‖L2Form.localizeCoord ψ χ hχ bΛ p e u‖ := by
  -- Reading a coordinate back through `e` and taking its real part.
  have hmap : (volume : Measure E).map e ≤
      ((((volume : Measure E).map e).addHaarScalarFactor volume : NNReal) : ENNReal) • volume := by
    rw [← ENNReal.smul_def, ← Measure.isAddLeftInvariant_eq_smul]
  have hq : QuasiMeasurePreserving e volume volume :=
    e.toContinuousAddEquiv.quasiMeasurePreserving_addHaar _ _
  let R : Lp ℂ 2 (volume : Measure (CoordinateSpace n)) →L[ℝ] Lp ℝ 2 (volume : Measure E) :=
    (Complex.reCLM : ℂ →L[ℝ] ℝ).compLpL 2 volume ∘L
      Lp.compOfMapLeSmul ℝ e.continuous.aemeasurable ENNReal.coe_ne_top hmap
  have hR (q : κ) (u : L2Form I M k) : R (L2Form.localizeCoord ψ χ hχ bΛ q e u) =
      (bΛ.coord q).toContinuousLinearMap.compLpL 2 volume (L2Form.localize ψ χ hχ u) := by
    refine Lp.ext ?_
    filter_upwards [(Complex.reCLM : ℂ →L[ℝ] ℝ).coeFn_compLpL (p := 2) (μ := volume)
        (Lp.compOfMapLeSmul ℝ e.continuous.aemeasurable ENNReal.coe_ne_top hmap
          (L2Form.localizeCoord ψ χ hχ bΛ q e u)),
      Lp.coeFn_compOfMapLeSmul (𝕜 := ℝ) e.continuous.aemeasurable ENNReal.coe_ne_top hmap
        (L2Form.localizeCoord ψ χ hχ bΛ q e u),
      hq.ae (L2Form.coeFn_localizeCoord ψ χ hχ bΛ q e u),
      (bΛ.coord q).toContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volume)
        (L2Form.localize ψ χ hχ u)] with y h₁ h₂ h₃ h₄
    rw [ContinuousLinearMap.comp_apply, h₁, h₂, Function.comp_apply, h₃, h₄]
    simp
  let Q : κ → Lp ℂ 2 (volume : Measure (CoordinateSpace n)) →L[ℝ]
      Lp (E [⋀^Fin k]→L[ℝ] ℝ) 2 (volume : Measure E) := fun q ↦
    (ContinuousLinearMap.toSpanSingleton ℝ (bΛ q)).compLpL 2 volume ∘L R
  have hQ (u : L2Form I M k) :
      L2Form.localize ψ χ hχ u = ∑ q, Q q (L2Form.localizeCoord ψ χ hχ bΛ q e u) := by
    conv_lhs => rw [TauCeti.eq_sum_basis_compLpL bΛ (L2Form.localize ψ χ hχ u)]
    simp only [Q, ContinuousLinearMap.comp_apply, hR]
  refine ⟨∑ q, ‖Q q‖, fun u ↦ ?_⟩
  rw [hQ u, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ ↦ ?_)
  exact ((Q q).le_opNorm _).trans (mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun i _ ↦ norm_nonneg (Q i)) (Finset.mem_univ q)) (norm_nonneg _))

omit [BoundarylessManifold I M] [T2Space M] in
/-- **The coordinate distribution as a tempered distribution.** On all of `CoordinateSpace n`,
the coordinate distribution `Distribution.coordOfFun` of the localization of `u` is the
distribution of the `L²` function `L2Form.localizeCoord ψ χ hχ bΛ p e u`, multiplied by the factor
relating the image of the volume of `E` under `e` to the volume of `CoordinateSpace n`. -/
theorem L2Form.coordOfFun_localize_eq_smul (u : L2Form I M k) :
    Distribution.coordOfFun (U := ⊤) (Ω := ⊤) e (Set.mapsTo_univ _ _) bΛ
        (L2Form.localize ψ χ hχ u) volume p =
      (((volume : Measure E).map e).addHaarScalarFactor volume : ℝ) •
        toDistribution ⊤ (L2Form.localizeCoord ψ χ hχ bΛ p e u : 𝓢'(CoordinateSpace n, ℂ)) := by
  have hloc : LocallyIntegrableOn (L2Form.localize ψ χ hχ u) (⊤ : TopologicalSpace.Opens E)
      volume :=
    ((Lp.memLp _).locallyIntegrable one_le_two).locallyIntegrableOn _
  rw [Distribution.coordOfFun_def, Distribution.transportCLM_ofFun_of_isAddHaarMeasure _ _ volume
    volume (hloc.ofReal_basis_repr bΛ p), toDistribution_toTemperedDistribution,
    ContinuousLinearEquiv.symm_symm,
    Distribution.ofFun_congr_ae (ae_restrict_of_ae (L2Form.coeFn_localizeCoord ψ χ hχ bΛ p e u))]

omit [BoundarylessManifold I M] in
/-- **Localizations of `H¹` forms are in `H¹`.** Let `u` be an `L²` form whose pairing with
Laplacians is bounded in the Hodge `H¹` norm, as in `L2Form.isLocallySobolev_one_of_forall_inner`.
Then the `p`-th coordinate of its localization to a chart, read in coordinates
(`L2Form.localizeCoord`), lies in the Bessel-potential space `H^1` of `CoordinateSpace n`. -/
theorem L2Form.memSobolev_localizeCoord_of_forall_inner [Finite κ] {u : L2Form I M k} {C : ℝ}
    (hu : ∀ φ : SmoothForm I M ℝ k,
      |⟪u, L2Form.ofSmooth (SmoothForm.hodgeLaplacian o hkl φ)⟫_ℝ| ≤
        C * √(‖(L2Form.ofSmooth φ : L2Form I M k)‖ ^ 2 +
          ⟪(L2Form.ofSmooth (SmoothForm.hodgeLaplacian o hkl φ) : L2Form I M k),
            L2Form.ofSmooth φ⟫_ℝ)) :
    MemSobolev 1 2 (L2Form.localizeCoord ψ χ hχ bΛ p e u : 𝓢'(CoordinateSpace n, ℂ)) := by
  set K := e '' (ψ '' tsupport χ)
  have hK : IsCompact K :=
    (ψ.isCompact_image_of_subset_source (isClosed_tsupport _).isCompact hχ).image e.continuous
  -- The localization vanishes outside the compact set `K`, and so does its distribution.
  have hsupp : Distribution.dsupport
      (L2Form.localizeCoord ψ χ hχ bΛ p e u : 𝓢'(CoordinateSpace n, ℂ)) ⊆ K :=
    Lp.dsupport_toTemperedDistribution_subset hK.isClosed
      (L2Form.localizeCoord_ae_eq_zero_of_notMem ψ χ hχ bΛ p e u)
  refine memSobolev_of_isCompact_dsupport_of_forall_isLocallySobolevAt
    (hK.of_isClosed_subset Distribution.isClosed_dsupport hsupp) fun x _ ↦ ?_
  -- Near every point, it is a nonzero multiple of a coordinate distribution, which is `H¹`.
  set c : ℝ := (((volume : Measure E).map e).addHaarScalarFactor volume : ℝ)
  have hc : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2
    (NNReal.coe_ne_zero.2 (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne')
  have h := (L2Form.isLocallySobolev_one_of_forall_inner hu ψ χ hχ e
    (U := ⊤) (Ω := ⊤) (Set.mapsTo_univ _ _) bΛ p (z := x) (Set.mem_univ x)).smul (c : ℂ)⁻¹
  rwa [L2Form.coordOfFun_localize_eq_smul, ← Complex.coe_smul, smul_smul, inv_mul_cancel₀ hc,
    one_smul] at h

namespace H1Form

variable [Finite κ]

/-- The `p`-th coordinate of the localization of an element of `H1Form o hkl` to a chart, read in
coordinates, lies in the Bessel-potential space `H^1` of `CoordinateSpace n`. -/
theorem memSobolev_localizeCoord_friedrichsInclusion (u : H1Form o hkl) :
    MemSobolev 1 2
      (L2Form.localizeCoord ψ χ hχ bΛ p e (friedrichsInclusion hΔ u) : 𝓢'(CoordinateSpace n, ℂ)) :=
  L2Form.memSobolev_localizeCoord_of_forall_inner ψ χ hχ bΛ p e
    (abs_inner_friedrichsInclusion_ofSmooth_hodgeLaplacian_le u)

/-- The localization of `H1Form o hkl` to `H^1` of a chart, as a linear map. -/
private def localizeSobolevₗ : H1Form o hkl →ₗ[ℝ] H^{1}(CoordinateSpace n) where
  toFun u :=
    (memSobolev_localizeCoord_friedrichsInclusion ψ χ hχ bΛ p e u).toBesselPotentialSpace
  map_add' u v := BesselPotentialSpace.ext (by simp [← Lp.toTemperedDistributionCLM_apply])
  map_smul' r u := BesselPotentialSpace.ext (by
    rw [RingHom.id_apply, ← Complex.coe_smul, BesselPotentialSpace.toDistr_smul]
    simp [← Lp.toTemperedDistributionCLM_apply, ← Complex.coe_smul])

/-- The graph of the localization is closed: both `H1Form o hkl` and `H^1` map continuously to
the tempered distributions, and `H^1` injectively. -/
private theorem isClosed_graph_localizeSobolevₗ :
    IsClosed ((localizeSobolevₗ (o := o) (hkl := hkl) ψ χ hχ bΛ p e).graph :
      Set (H1Form o hkl × H^{1}(CoordinateSpace n))) := by
  have h : ((localizeSobolevₗ (o := o) (hkl := hkl) ψ χ hχ bΛ p e).graph :
      Set (H1Form o hkl × H^{1}(CoordinateSpace n))) =
      {x | BesselPotentialSpace.toDistrCLM _ ℂ 1 2 x.2 =
        Lp.toTemperedDistributionCLM ℂ volume 2
          (L2Form.localizeCoord ψ χ hχ bΛ p e (friedrichsInclusion hΔ x.1))} := by
    ext x
    rw [SetLike.mem_coe, LinearMap.mem_graph_iff, Set.mem_ofPred_eq,
      ← (BesselPotentialSpace.toDistrCLM_injective (E := CoordinateSpace n) (F := ℂ)).eq_iff]
    simp [localizeSobolevₗ]
  rw [h]
  exact isClosed_eq (by fun_prop) (by fun_prop)

/-- **The localization of `H1Form o hkl` to `H^1` of a chart.** For a chart `ψ`, a smooth cutoff
`χ` supported in its source, a basis `bΛ` of the forms on `E`, an index `p` and coordinates
`e : E ≃L[ℝ] CoordinateSpace n`, the continuous linear map to the Bessel-potential space `H^1` of
`CoordinateSpace n` that sends `u` to the `p`-th coordinate in `bΛ`, complexified, of the
localization of the image of `u` in `L2Form I M k`, read through `e⁻¹`
(`H1Form.toDistr_localizeSobolev`). It is
everywhere defined by `memSobolev_localizeCoord_friedrichsInclusion`, and continuous by the closed
graph
theorem. -/
def localizeSobolev : H1Form o hkl →L[ℝ] H^{1}(CoordinateSpace n) :=
  .ofIsClosedGraph (isClosed_graph_localizeSobolevₗ ψ χ hχ bΛ p e)

/-- The tempered distribution of `localizeSobolev ψ χ hχ bΛ p e u` is that of the `L²` function
`L2Form.localizeCoord ψ χ hχ bΛ p e (friedrichsInclusion _ u)`, the complexified `p`-th coordinate
of the
localization of the image of `u` in `L2Form I M k` read through `e⁻¹`
(`L2Form.coeFn_localizeCoord`). -/
@[simp]
theorem toDistr_localizeSobolev (u : H1Form o hkl) :
    (localizeSobolev (o := o) (hkl := hkl) ψ χ hχ bΛ p e u).toDistr =
      (L2Form.localizeCoord ψ χ hχ bΛ p e (friedrichsInclusion hΔ u) :
        𝓢'(CoordinateSpace n, ℂ)) := by
  rw [localizeSobolev, ContinuousLinearMap.coeFn_ofIsClosedGraph, localizeSobolevₗ,
    LinearMap.coe_mk, AddHom.coe_mk, MemSobolev.toBesselPotentialSpace_toDistr]

/-- **Rellich's theorem in a chart.** The map sending `u` in `H1Form o hkl` to the `p`-th
coordinate of the localization of its image in `L2Form I M k`, read in coordinates
(`L2Form.localizeCoord ψ χ hχ bΛ p e`), is a compact operator into `L²` of `CoordinateSpace n`. -/
theorem isCompactOperator_localizeCoord_comp_friedrichsInclusion :
    IsCompactOperator
      (L2Form.localizeCoord ψ χ hχ bΛ p e ∘L friedrichsInclusion hΔ : H1Form o hkl →L[ℝ] _) := by
  have hK : IsCompact (e '' (ψ '' tsupport χ)) :=
    (ψ.isCompact_image_of_subset_source (isClosed_tsupport _).isCompact hχ).image e.continuous
  obtain ⟨φ, -, -, hφ⟩ := hK.exists_schwartzMap_cutoff isOpen_univ (Set.subset_univ _)
  -- Multiplication by `φ` does not change the coordinate, which vanishes outside that compact set;
  -- followed by the inclusion of `H^1` into `L²`, it is compact by Rellich's theorem.
  have h :
      ⇑(L2Form.localizeCoord ψ χ hχ bΛ p e ∘L friedrichsInclusion hΔ : H1Form o hkl →L[ℝ] _) =
      ⇑(BesselPotentialSpace.inclusionLp (E := CoordinateSpace n) (G := ℂ) (p := 2) le_rfl) ∘
        ⇑(BesselPotentialSpace.inclusion zero_le_one ∘L BesselPotentialSpace.smulLeftCLM 1 φ) ∘
        localizeSobolev ψ χ hχ bΛ p e := by
    funext u
    refine ((BesselPotentialSpace.inclusionLp_eq_iff le_rfl).2 ?_).symm
    simp only [Function.comp_apply, ContinuousLinearMap.comp_apply,
      BesselPotentialSpace.toDistr_inclusion, BesselPotentialSpace.toDistr_smulLeftCLM,
      toDistr_localizeSobolev]
    -- The coordinate vanishes almost everywhere off the set where `φ = 1`.
    refine (Lp.toTemperedDistribution_eq_smulLeftCLM_iff φ.hasTemperateGrowth
      (L2Form.localizeCoord ψ χ hχ bΛ p e (friedrichsInclusion hΔ u)) _).2
      ((L2Form.localizeCoord_ae_eq_zero_of_notMem ψ χ hχ bΛ p e (friedrichsInclusion hΔ u)).mono
        fun x hx ↦ ?_)
    by_cases hxK : x ∈ e '' (ψ '' tsupport χ)
    · simp [hφ.self_of_nhdsSet x hxK]
    · simp [hx hxK]
  rw [h]
  exact ((BesselPotentialSpace.isCompactOperator_inclusion_comp_smulLeftCLM φ
    zero_lt_one).clm_comp _).comp_clm _

end H1Form

end Localize

/-! ### Compactness of the inclusion into `L2Form` -/

/-- **Rellich's theorem for `H1Form`.** On a closed oriented Riemannian manifold, the inclusion
`LinearPMap.friedrichsInclusion _ : H1Form o hkl →L[ℝ] L2Form I M k` is a compact operator. -/
theorem H1Form.isCompactOperator_friedrichsInclusion :
    IsCompactOperator (friedrichsInclusion hΔ : H1Form o hkl →L[ℝ] L2Form I M k) := by
  -- The localizations are taken in `L²` for a Haar measure on `E`.
  borelize E
  let _ : MeasureSpace E := ⟨Measure.addHaar⟩
  have : (volume : Measure E).IsAddHaarMeasure :=
    inferInstanceAs (Measure.addHaar : Measure E).IsAddHaarMeasure
  obtain ⟨N, c, ρ, hρ⟩ := exists_finite_partialDiffeomorph_cover (I := I) (M := M)
  let bΛ := Module.finBasis ℝ (E [⋀^Fin k]→L[ℝ] ℝ)
  let e : E ≃L[ℝ] CoordinateSpace (Module.finrank ℝ E) := .ofFinrankEq (by simp)
  obtain ⟨C, hC0, hC⟩ := L2Form.exists_norm_le_sum_norm_localize (k := k)
    (fun i ↦ extChartPartialDiffeomorph I ∞ (c i)) ρ hρ
  choose D hD using fun i ↦ L2Form.exists_norm_localize_le_mul_sum_norm_localizeCoord
    (extChartPartialDiffeomorph I ∞ (c i)) (ρ i) (hρ i) bΛ e
  -- The inclusion is dominated by the coordinates of its localizations, which are compact.
  refine IsCompactOperator.of_norm_le_mul_sum
    (friedrichsInclusion hΔ : H1Form o hkl →L[ℝ] L2Form I M k).toLinearMap
    (fun ip : Fin N × Fin (Module.finrank ℝ (E [⋀^Fin k]→L[ℝ] ℝ)) ↦
      (L2Form.localizeCoord (extChartPartialDiffeomorph I ∞ (c ip.1)) (ρ ip.1) (hρ ip.1) bΛ ip.2
        e ∘L friedrichsInclusion hΔ : H1Form o hkl →L[ℝ] _))
    (fun ip ↦ isCompactOperator_localizeCoord_comp_friedrichsInclusion _ _ (hρ ip.1) bΛ ip.2 e)
    (C := ∑ i, C i * max (D i) 0) fun u ↦ ?_
  refine (hC (friedrichsInclusion hΔ u)).trans ?_
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  simp only [ContinuousLinearMap.comp_apply]
  have hs : 0 ≤ ∑ p, ‖L2Form.localizeCoord (extChartPartialDiffeomorph I ∞ (c i)) (ρ i) (hρ i)
      bΛ p e (friedrichsInclusion hΔ u)‖ := by positivity
  refine (mul_le_mul_of_nonneg_left ((hD i (friedrichsInclusion hΔ u)).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ 0) hs)) (hC0 i)).trans ?_
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (Finset.single_le_sum (f := fun j ↦ C j * max (D j) 0)
    (fun j _ ↦ mul_nonneg (hC0 j) (le_max_right _ _)) (Finset.mem_univ i)) hs

end SymplecticGeometry

end
