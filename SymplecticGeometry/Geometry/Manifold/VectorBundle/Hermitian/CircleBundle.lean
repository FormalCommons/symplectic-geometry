/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.VectorBundle.FiniteDimensional
public import TauCeti.Topology.VectorBundle.OrthonormalFrame.Principal
public import TauCeti.Topology.VectorBundle.Smul
public import SymplecticGeometry.Analysis.CStarAlgebra.Unitary.ContinuousLinearMap
public import SymplecticGeometry.Analysis.Normed.Operator.SpanSingleton
public import SymplecticGeometry.Topology.FiberBundle.Principal.ChangeGroup
public import SymplecticGeometry.Geometry.Manifold.Instances.Sphere
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Riemannian.Hermitian
public import TauCeti.Geometry.Manifold.FiberBundle.Principal
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Sphere
import TauCeti.Geometry.Manifold.ContMDiff.Sqrt
import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Scalar

/-!
# The circle bundle of a Hermitian line bundle

Let `E → B` be a complex vector bundle of rank one whose fibres are complex inner product spaces
with a continuous norm (`TauCeti.ContinuousFiberNorm`), for instance a Hermitian line bundle given
by an `i`-invariant smooth metric `g` with the inner products `g.complexInnerProductSpace hI`. Its
unit vectors form the subtype `{p : TotalSpace F E // ‖p.snd‖ = 1}`, the set
`TauCeti.sphereBundle F E` of Tau Ceti, on which Tau Ceti's `isManifold_sphereBundle` puts a smooth
structure under smoothness hypotheses. This file proves the topological facts, which hold over any
base:

* `Circle` acts on the unit vectors by scalar multiplication in the fibres, continuously, freely
  (`SymplecticGeometry.Bundle.circleBundle_smul_eq_iff`) and with the fibres as orbits
  (`SymplecticGeometry.Bundle.exists_circleBundle_smul_eq_iff`);
* a unitary frame `φ : ℂ ≃ₗᵢ[ℂ] E x` of a fibre is multiplication by the unit vector `φ 1`, which
  identifies the total space of Tau Ceti's unitary frame bundle
  `TauCeti.OrthonormalFrameBundle.Fiber ℂ F E ℂ` with the unit vectors
  (`SymplecticGeometry.Bundle.circleBundleHomeomorph`); the right action of
  `unitary (ℂ →L[ℂ] ℂ)` on frames becomes the action of `Circle` along the isomorphism
  `Unitary.continuousLinearMapCircleEquiv`, which sends `u` to `u 1`, and the right action of
  `Circle` on frames becomes its action on unit vectors
  (`SymplecticGeometry.Bundle.circleBundleHomeomorph_op_circle_smul`);
* the unitary frame bundle is a principal `Circle`-bundle
  (`SymplecticGeometry.Bundle.instPrincipalBundleCircleFiber`), obtained from Tau Ceti's principal
  `unitary (ℂ →L[ℂ] ℂ)`-bundle structure (`TauCeti.OrthonormalFrameBundle.instPrincipalBundleFiber`)
  by changing the structure group along that isomorphism
  (`TauCeti.PrincipalBundle.changeGroup`); its trivializations are those of Tau Ceti's bundle
  followed by the isomorphism on the fibre coordinate
  (`Bundle.Trivialization.changeModelFiber`). Such a trivialization reads a frame `φ` as the
  inner product `⟪σ 1, φ 1⟫` with the unit vector of the local frame `σ`
  (`Bundle.Trivialization.coe_snd_changeModelFiber_orthonormalFrameBundleFiber`), so its
  transition functions are the inner products `⟪σ' 1, σ 1⟫`
  (`Bundle.Trivialization.coe_coordChange_changeModelFiber_orthonormalFrameBundleFiber`).

The rank-one condition is the instance `Fact (Module.finrank ℂ F = 1)`.

The last section adds the smooth structure, for a Hermitian line bundle `(g, hI)` over a manifold:
a smooth complex line bundle `V` with a smooth `i`-invariant real metric `g`, whose fibres get
their norms and Hermitian products from `g` through three local instances (written with `letI` in
the statements). The unit vector `σ 1` of a local unitary frame is then a smooth local section
(`Bundle.Trivialization.contMDiffOn_orthonormalFrameAt_one`; its normalization follows the proof
of `Bundle.ContMDiffRiemannianMetric.contMDiff_and_orthonormal_vecCons_of_mem_orthogonalSpanFamily`
in `Hermitian/Frame.lean`), so the transition functions above are smooth. By Tau Ceti's
`TauCeti.PrincipalBundle.contMDiffFiberBundle_iff`, the unitary frames thus form a smooth
principal `Circle`-bundle (`SymplecticGeometry.Bundle.contMDiffFiberBundle_circleFiber`), charted
through the fibre as `TauCeti.ManifoldTotalSpace Circle (Fiber ℂ F V ℂ)`; Tau Ceti's
`TauCeti.ManifoldTotalSpace.isSubmersion_proj` applies to its projection. For a
finite-dimensional base without boundary, `circleBundleHomeomorph` is a diffeomorphism onto the
unit vectors with the smooth structure of a regular level set that Tau Ceti's
`sphereBundleChartedSpace` gives them (`SymplecticGeometry.Bundle.circleBundleDiffeomorph`),
equivariant fibre by fibre (`SymplecticGeometry.Bundle.circleBundleDiffeomorph_op_smul`).

## Main definitions

* `SymplecticGeometry.Bundle.circleBundleHomeomorph`: the total space of the unitary frame bundle
  is homeomorphic to the unit vectors, by `φ ↦ φ 1`.
* `SymplecticGeometry.Bundle.instFiberBundleCircleFiber`,
  `SymplecticGeometry.Bundle.instPrincipalBundleCircleFiber`: the unitary frame bundle as a
  principal `Circle`-bundle.
* `SymplecticGeometry.Bundle.contMDiffFiberBundle_circleFiber`: for a smooth Hermitian line
  bundle, it is a smooth principal `Circle`-bundle.
* `SymplecticGeometry.Bundle.circleBundleDiffeomorph`: `circleBundleHomeomorph` as a
  diffeomorphism onto the unit vectors with their regular-level smooth structure.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.7
  (the unit circle bundle of a Hermitian line bundle as a principal circle bundle).
* D. Husemoller, *Fibre Bundles*, third edition, Graduate Texts in Mathematics 20, Springer
  (1994), Chapter 4 (principal bundles) and Chapter 5, §§4–5 (the bundle of unitary frames).
-/

public section

noncomputable section

open Bundle MulOpposite Module TauCeti TauCeti.OrthonormalFrameBundle
open scoped Manifold ContDiff InnerProductSpace

namespace SymplecticGeometry.Bundle

/-! ### The action of `Circle` on unit vectors -/

section Action

variable {B F : Type*} {E : B → Type*} [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)]

/-- `Circle` acts on the unit vectors of a bundle with complex normed fibres by scalar
multiplication in the fibres. -/
instance instMulActionCircleBundle : MulAction Circle {p : TotalSpace F E // ‖p.snd‖ = 1} where
  smul z p := ⟨⟨p.val.proj, (z : ℂ) • p.val.snd⟩, by
    rw [norm_smul, Circle.norm_coe, p.property, one_mul]⟩
  one_smul p := Subtype.ext <| congrArg (TotalSpace.mk p.val.proj) (one_smul ℂ p.val.snd)
  mul_smul z w p := Subtype.ext <|
    congrArg (TotalSpace.mk p.val.proj) (mul_smul (z : ℂ) w p.val.snd)

/-- The action of `z : Circle` multiplies a unit vector by `z` in its fibre. -/
@[simp]
theorem circleBundle_smul_apply (z : Circle) (p : {p : TotalSpace F E // ‖p.snd‖ = 1}) :
    ((z • p : {p : TotalSpace F E // ‖p.snd‖ = 1}) : TotalSpace F E) =
      ⟨p.val.proj, (z : ℂ) • p.val.snd⟩ :=
  (rfl)

/-- **The action of `Circle` on unit vectors is free.** -/
@[simp]
theorem circleBundle_smul_eq_iff {z w : Circle} {p : {p : TotalSpace F E // ‖p.snd‖ = 1}} :
    z • p = w • p ↔ z = w := by
  refine ⟨fun h ↦ Circle.ext ?_, fun h ↦ h ▸ rfl⟩
  have hp : p.val.snd ≠ 0 := norm_ne_zero_iff.1 (p.property.symm ▸ one_ne_zero)
  exact smul_left_injective ℂ hp (TotalSpace.mk_inj.1 (congrArg Subtype.val h))

variable [NormedAddCommGroup F] [NormedSpace ℂ F] [TopologicalSpace B]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℂ F E]

/-- The action of `Circle` on unit vectors is continuous. -/
instance instContinuousSMulCircleBundle :
    ContinuousSMul Circle {p : TotalSpace F E // ‖p.snd‖ = 1} where
  continuous_smul := Continuous.subtype_mk
    ((Continuous.smul_totalSpace (continuous_subtypeVal.comp continuous_fst)
      (continuous_subtypeVal.comp continuous_snd))) _

variable [Fact (finrank ℂ F = 1)]

/-- **The orbits of `Circle` on unit vectors are the fibres**, for a bundle of complex rank one. -/
theorem exists_circleBundle_smul_eq_iff {p q : {p : TotalSpace F E // ‖p.snd‖ = 1}} :
    (∃ z : Circle, z • p = q) ↔ p.val.proj = q.val.proj := by
  refine ⟨fun ⟨_, h⟩ ↦ h ▸ rfl, ?_⟩
  obtain ⟨⟨x, u⟩, hu⟩ := p
  obtain ⟨⟨y, w⟩, hw⟩ := q
  rintro (rfl : x = y)
  have hu0 : u ≠ 0 := norm_ne_zero_iff.1 (hu.symm ▸ one_ne_zero)
  obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_ne_zero' u hu0).1
    ((VectorBundle.finrank_eq ℂ F E x).trans Fact.out) w
  have hc : ‖c‖ = 1 := by simpa [norm_smul, show ‖u‖ = 1 from hu] using hw
  exact ⟨⟨c, mem_sphere_zero_iff_norm.2 hc⟩, rfl⟩

end Action

/-! ### Unitary frames of a line bundle as unit vectors -/

section Homeomorph

variable {B F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [TopologicalSpace B]
  {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℂ F E]
  [Fact (finrank ℂ F = 1)]

omit [TopologicalSpace B] [TopologicalSpace (TotalSpace F E)] [FiberBundle F E]
  [VectorBundle ℂ F E] [Fact (finrank ℂ F = 1)] in
/-- A unitary frame `φ` of a fibre is multiplication by `φ 1`. -/
private theorem frame_apply_eq_smul {x : B} (φ : ℂ ≃ₗᵢ[ℂ] E x) (z : ℂ) : φ z = z • φ 1 := by
  rw [← map_smul, smul_eq_mul, mul_one]

/-- The total space of the unitary frame bundle of a complex line bundle is homeomorphic to its
unit vectors: a frame `φ : ℂ ≃ₗᵢ[ℂ] E x` goes to the unit vector `φ 1`. -/
def circleBundleHomeomorph :
    TotalSpace (unitary (ℂ →L[ℂ] ℂ)) (Fiber ℂ F E ℂ) ≃ₜ {p : TotalSpace F E // ‖p.snd‖ = 1} where
  toFun φ := ⟨⟨φ.proj, φ.snd.frame 1⟩, by simp⟩
  invFun p := ⟨p.val.proj, .ofFrame (LinearIsometryEquiv.toSpanSingleton ℂ _
    ((VectorBundle.finrank_eq ℂ F E _).trans Fact.out) p.property)⟩
  left_inv φ := by
    refine TotalSpace.ext rfl (heq_of_eq (Fiber.ext (LinearIsometryEquiv.ext fun z ↦ ?_)))
    rw [Fiber.frame_ofFrame, LinearIsometryEquiv.toSpanSingleton_apply, ← frame_apply_eq_smul]
  right_inv p := Subtype.ext <| congrArg (TotalSpace.mk p.val.proj) <| by
    rw [Fiber.frame_ofFrame, LinearIsometryEquiv.toSpanSingleton_one]
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    have h := (continuous_totalSpaceMk_frame (𝕜 := ℂ) (F := F) (E := E) (1 : ℂ)).comp
      (totalSpaceHomeomorph (V := ℂ)).continuous
    refine h.congr fun φ ↦ ?_
    rw [Function.comp_apply, coe_totalSpaceHomeomorph]
    exact congrArg (fun q : OrthonormalFrameBundle ℂ F E ℂ ↦
      (⟨q.proj, q.frame 1⟩ : TotalSpace F E)) (totalSpaceEquiv_apply φ)
  continuous_invFun := by
    have h : Continuous fun p : {p : TotalSpace F E // ‖p.snd‖ = 1} ↦
        (⟨p.val.proj, LinearIsometryEquiv.toSpanSingleton ℂ _
          ((VectorBundle.finrank_eq ℂ F E _).trans Fact.out) p.property⟩ :
          OrthonormalFrameBundle ℂ F E ℂ) :=
      continuous_iff.2 fun z ↦ by
        simpa only [LinearIsometryEquiv.toSpanSingleton_apply] using
          Continuous.smul_totalSpace (continuous_const (y := z)) continuous_subtypeVal
    have h' := (totalSpaceHomeomorph (𝕜 := ℂ) (F := F) (E := E) (V := ℂ)).symm.continuous.comp h
    refine h'.congr fun p ↦ ?_
    rw [Function.comp_apply, coe_totalSpaceHomeomorph_symm]
    exact totalSpaceEquiv_symm_apply _

/-- `circleBundleHomeomorph` sends a frame `φ` of `E x` to the unit vector `φ 1`. -/
@[simp]
theorem circleBundleHomeomorph_apply (φ : TotalSpace (unitary (ℂ →L[ℂ] ℂ)) (Fiber ℂ F E ℂ)) :
    (circleBundleHomeomorph φ : TotalSpace F E) = ⟨φ.proj, φ.snd.frame 1⟩ :=
  (rfl)

theorem proj_circleBundleHomeomorph_symm (p : {p : TotalSpace F E // ‖p.snd‖ = 1}) :
    ((circleBundleHomeomorph (F := F)).symm p).proj = p.val.proj :=
  (rfl)

/-- The inverse of `circleBundleHomeomorph` sends a unit vector `v` to the frame `z ↦ z • v`. -/
@[simp]
theorem circleBundleHomeomorph_symm_apply_frame (p : {p : TotalSpace F E // ‖p.snd‖ = 1})
    (z : ℂ) :
    (⟨_, ((circleBundleHomeomorph (F := F)).symm p).snd.frame z⟩ : TotalSpace F E) =
      ⟨p.val.proj, z • p.val.snd⟩ :=
  TotalSpace.mk_inj.2 (LinearIsometryEquiv.toSpanSingleton_apply _ p.property z)

/-- `circleBundleHomeomorph` turns the right action of `unitary (ℂ →L[ℂ] ℂ)` on frames into the
action of `Circle` on unit vectors, along `Unitary.continuousLinearMapCircleEquiv`. -/
theorem circleBundleHomeomorph_smul (u : unitary (ℂ →L[ℂ] ℂ)) {x : B} (φ : Fiber ℂ F E ℂ x) :
    circleBundleHomeomorph (⟨x, op u • φ⟩ : TotalSpace (unitary (ℂ →L[ℂ] ℂ)) (Fiber ℂ F E ℂ)) =
      Unitary.continuousLinearMapCircleEquiv u • circleBundleHomeomorph ⟨x, φ⟩ := by
  rw [Subtype.ext_iff, circleBundle_smul_apply, circleBundleHomeomorph_apply,
    circleBundleHomeomorph_apply, Fiber.frame_smul_apply, unop_op,
    Unitary.coe_continuousLinearMapCircleEquiv_apply, frame_apply_eq_smul]

end Homeomorph

/-! ### The right action of `Circle` on unitary frames -/

/-- `Circle` acts on the right on the unitary frames of a fibre, through
`Unitary.continuousLinearMapCircleEquiv`: `z` precomposes a frame with multiplication by `z`. -/
instance instMulActionCircleFiber {B F : Type*} {E : B → Type*} [∀ x, NormedAddCommGroup (E x)]
    [∀ x, InnerProductSpace ℂ (E x)] (x : B) : MulAction Circleᵐᵒᵖ (Fiber ℂ F E ℂ x) :=
  MulAction.compHom _
    (MulEquiv.op Unitary.continuousLinearMapCircleEquiv.symm.toMulEquiv).toMonoidHom

end SymplecticGeometry.Bundle

namespace TauCeti.OrthonormalFrameBundle.Fiber

variable {B F : Type*} {E : B → Type*} [∀ x, NormedAddCommGroup (E x)]
  [∀ x, InnerProductSpace ℂ (E x)]

theorem op_circle_smul_eq {x : B} (z : Circle) (φ : Fiber ℂ F E ℂ x) :
    op z • φ = op (Unitary.continuousLinearMapCircleEquiv.symm z) • φ :=
  (rfl)

/-- The action of `z : Circle` precomposes a frame with multiplication by `z`. -/
@[simp]
theorem frame_op_circle_smul_apply {x : B} (z : Circle) (φ : Fiber ℂ F E ℂ x) (v : ℂ) :
    (op z • φ).frame v = φ.frame ((z : ℂ) * v) := by
  rw [op_circle_smul_eq, Fiber.frame_smul_apply, unop_op,
    Unitary.continuousLinearMapCircleEquiv_symm_apply]

end TauCeti.OrthonormalFrameBundle.Fiber

namespace SymplecticGeometry.Bundle

section Equivariance

variable {B F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [TopologicalSpace B]
  {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℂ F E]
  [Fact (finrank ℂ F = 1)]

/-- **`circleBundleHomeomorph` is `Circle`-equivariant**: it turns the right action of `Circle`
on frames into its action on unit vectors. -/
theorem circleBundleHomeomorph_op_circle_smul (z : Circle) {x : B} (φ : Fiber ℂ F E ℂ x) :
    circleBundleHomeomorph (⟨x, op z • φ⟩ : TotalSpace (unitary (ℂ →L[ℂ] ℂ)) (Fiber ℂ F E ℂ)) =
      z • circleBundleHomeomorph ⟨x, φ⟩ := by
  simp [Fiber.op_circle_smul_eq, circleBundleHomeomorph_smul]

end Equivariance

/-! ### The unitary frame bundle as a principal `Circle`-bundle -/

section Principal

variable {B F : Type*} {E : B → Type*} [∀ x, NormedAddCommGroup (E x)]
  [∀ x, InnerProductSpace ℂ (E x)] [TopologicalSpace (TotalSpace F E)]

/-- The topology on the total space of the unitary frame bundle with model fibre `Circle`,
induced from the one with model fibre `unitary (ℂ →L[ℂ] ℂ)` along
`Bundle.TotalSpace.modelFiberEquiv`, as `FiberBundle.changeModelFiber` and
`TauCeti.PrincipalBundle.changeGroup` ask. -/
instance instTopologicalSpaceTotalSpaceCircleFiber :
    TopologicalSpace (TotalSpace Circle (Fiber ℂ F E ℂ)) :=
  .induced (TotalSpace.modelFiberEquiv (unitary (ℂ →L[ℂ] ℂ)) Circle (Fiber ℂ F E ℂ))
    inferInstance

variable [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace ℂ F] [FiberBundle F E]
  [VectorBundle ℂ F E] [ContinuousFiberNorm F E] [Fact (finrank ℂ F = 1)]

local instance : FiniteDimensional ℂ F := .of_fact_finrank_eq_succ 0

local instance : Fact (finrank ℂ ℂ = finrank ℂ F) :=
  ⟨by rw [finrank_self, Fact.out (p := finrank ℂ F = 1)]⟩

/-- The unitary frames of a complex line bundle form a fibre bundle with fibre `Circle`: Tau Ceti's
frame bundle with its model fibre `unitary (ℂ →L[ℂ] ℂ)` replaced by `Circle` along
`Unitary.continuousLinearMapCircleEquiv` (`FiberBundle.changeModelFiber`). -/
instance instFiberBundleCircleFiber : FiberBundle Circle (Fiber ℂ F E ℂ) :=
  FiberBundle.changeModelFiber (Unitary.continuousLinearMapCircleEquiv : _ ≃ₜ Circle) ⟨rfl⟩

/-- **The unitary frames of a complex line bundle form a principal `Circle`-bundle**, `Circle`
acting on the right by precomposition with multiplication: the change of structure group of
Tau Ceti's principal `unitary (ℂ →L[ℂ] ℂ)`-bundle along
`Unitary.continuousLinearMapCircleEquiv`. -/
instance instPrincipalBundleCircleFiber : PrincipalBundle Circle (Fiber ℂ F E ℂ) :=
  PrincipalBundle.changeGroup Unitary.continuousLinearMapCircleEquiv ⟨rfl⟩ fun _ _ _ ↦ rfl

end Principal

end SymplecticGeometry.Bundle

/-! ### The trivializations of the principal `Circle`-bundle -/

namespace Bundle.Trivialization

open SymplecticGeometry.Bundle

variable {B F : Type*} {E : B → Type*} [∀ x, NormedAddCommGroup (E x)]
  [∀ x, InnerProductSpace ℂ (E x)] [TopologicalSpace (TotalSpace F E)] [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiberBundle F E] [VectorBundle ℂ F E]
  [ContinuousFiberNorm F E] (e : Trivialization F (π F E)) [e.IsLinear ℂ]
  {ι : Type*} [Fintype ι] [LinearOrder ι] [LocallyFiniteOrderBot ι] (c : Basis ι ℂ F)
  (b : OrthonormalBasis ι ℂ ℂ)

/-- The trivialization of the principal `Circle`-bundle given by the Gram–Schmidt trivialization of
the unitary frame bundle over `e` reads a frame `φ` over the base set of `e` as the inner product
`⟪σ 1, φ 1⟫` of the unit vectors given by `φ` and by the local frame `σ = e.orthonormalFrameAt c b`.
-/
theorem coe_snd_changeModelFiber_orthonormalFrameBundleFiber
    (p : TotalSpace Circle (Fiber ℂ F E ℂ)) (hp : p.proj ∈ e.baseSet) :
    (((e.orthonormalFrameBundle c b).orthonormalFrameBundleFiber.changeModelFiber
      (Unitary.continuousLinearMapCircleEquiv : _ ≃ₜ Circle) ⟨rfl⟩ p).2 : ℂ) =
      ⟪e.orthonormalFrameAt c b p.proj 1, p.snd.frame 1⟫_ℂ := by
  rw [changeModelFiber_apply, orthonormalFrameBundleFiber_apply, totalSpaceEquiv_apply,
    orthonormalFrameBundle_apply_mk e c b ⟨_, hp⟩]
  simp only [e.orthonormalFrameAt_of_mem c b hp]
  rw [LinearIsometryEquiv.inner_map_eq_flip]
  simp

/-- The inverse of the trivialization of `coe_snd_changeModelFiber_orthonormalFrameBundleFiber`
sends `(y, z)`, for `y` in the base set of `e`, to a frame over `y` whose unit vector is `z • σ 1`,
for the local frame `σ = e.orthonormalFrameAt c b` at `y`. -/
theorem frame_changeModelFiber_orthonormalFrameBundleFiber_symm_one {y : B} (hy : y ∈ e.baseSet)
    (z : Circle) :
    (⟨_, (((e.orthonormalFrameBundle c b).orthonormalFrameBundleFiber.changeModelFiber
      (Unitary.continuousLinearMapCircleEquiv : _ ≃ₜ Circle) ⟨rfl⟩).toOpenPartialHomeomorph.symm
        (y, z)).snd.frame 1⟩ : TotalSpace F E) = ⟨y, (z : ℂ) • e.orthonormalFrameAt c b y 1⟩ := by
  rw [changeModelFiber_symm_apply, orthonormalFrameBundleFiber_symm_apply,
    e.orthonormalFrameBundle_symm_apply c b ⟨y, hy⟩, TotalSpace.modelFiberEquiv_symm_apply,
    totalSpaceEquiv_symm_apply]
  simp only [OrthonormalFrameBundle.proj_smul, OrthonormalFrameBundle.frame_smul_apply,
    unop_op, ContinuousMulEquiv.coe_toHomeomorph_symm, e.orthonormalFrameAt_of_mem c b hy]
  have hz : (((Unitary.continuousLinearMapCircleEquiv.symm : Circle ≃ₜ _) z :
      unitary (ℂ →L[ℂ] ℂ)) : ℂ →L[ℂ] ℂ) 1 = z :=
    (Unitary.continuousLinearMapCircleEquiv_symm_apply z 1).trans (mul_one _)
  rw [hz]
  exact congrArg (TotalSpace.mk y)
    (by simpa using (e.orthonormalFrame c b ⟨y, hy⟩).map_smul (z : ℂ) 1)

/-- The transition function between two of the trivializations of
`coe_snd_changeModelFiber_orthonormalFrameBundleFiber` is the inner product `⟪σ' 1, σ 1⟫` of the
unit vectors of their local frames. -/
theorem coe_coordChange_changeModelFiber_orthonormalFrameBundleFiber
    (e' : Trivialization F (π F E)) [e'.IsLinear ℂ] (c' : Basis ι ℂ F)
    (b' : OrthonormalBasis ι ℂ ℂ) {y : B} (hy : y ∈ e.baseSet) (hy' : y ∈ e'.baseSet) :
    (((e.orthonormalFrameBundle c b).orthonormalFrameBundleFiber.changeModelFiber
      (Unitary.continuousLinearMapCircleEquiv : _ ≃ₜ Circle) ⟨rfl⟩).coordChange
        ((e'.orthonormalFrameBundle c' b').orthonormalFrameBundleFiber.changeModelFiber
          (Unitary.continuousLinearMapCircleEquiv : _ ≃ₜ Circle) ⟨rfl⟩) y 1 : ℂ) =
      ⟪e'.orthonormalFrameAt c' b' y 1, e.orthonormalFrameAt c b y 1⟫_ℂ := by
  have key (q : TotalSpace F E) (hq : q = ⟨y, ((1 : Circle) : ℂ) • e.orthonormalFrameAt c b y 1⟩) :
      ⟪e'.orthonormalFrameAt c' b' q.proj 1, q.snd⟫_ℂ =
        ⟪e'.orthonormalFrameAt c' b' y 1, e.orthonormalFrameAt c b y 1⟫_ℂ := by
    subst hq
    rw [Circle.coe_one, one_smul]
  rw [coordChange]
  refine (e'.coe_snd_changeModelFiber_orthonormalFrameBundleFiber c' b' _ ?_).trans
    (key _ (e.frame_changeModelFiber_orthonormalFrameBundleFiber_symm_one c b hy 1))
  convert hy'
  exact proj_symm_apply' _ (by simpa using hy)

end Bundle.Trivialization

/-! ### The smooth structure -/

section Smooth

variable {EB HB B F : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  {I : ModelWithCorners ℝ EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  {V : B → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)]
  [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℂ F V]
  {n : ℕ∞ω}

local instance instVectorBundleRealCircleBundle : VectorBundle ℝ F V :=
  VectorBundle.restrictScalars ℝ ℂ F V

variable [ContMDiffVectorBundle n F V I] (g : ContMDiffRiemannianMetric I n F V)
  (hI : ∀ x (v w : V x), g.inner x (Complex.I • v) (Complex.I • w) = g.inner x v w)

/-- For a smooth Hermitian metric on a complex line bundle, the unit vector `σ 1` of the local
unitary frame `σ = e.orthonormalFrameAt c b` of a trivialization `e` of the atlas is a smooth
section over the base set of `e`. -/
theorem Bundle.Trivialization.contMDiffOn_orthonormalFrameAt_one
    (e : Trivialization F (π F V)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [LinearOrder ι] [LocallyFiniteOrderBot ι] (c : Basis ι ℂ F)
    (b : OrthonormalBasis ι ℂ ℂ) :
    letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
    letI : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
    ContMDiffOn I (I.prod 𝓘(ℝ, F)) n
      (fun y ↦ (⟨y, e.orthonormalFrameAt c b y 1⟩ : TotalSpace F V)) e.baseSet := by
  let : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
  let : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
  -- In rank one, `σ 1` is a multiple of the normalized vector `u / ‖u‖`, for `u = e⁻¹ (c i)`.
  obtain ⟨i, hi⟩ := Fintype.card_eq_one_iff.1 <| by
    rw [← finrank_eq_card_basis b.toBasis, finrank_self]
  set u : ∀ y, V y := fun y ↦ e.symm y (c i)
  have hu : ContMDiffOn I (I.prod 𝓘(ℝ, F)) n (fun y ↦ (⟨y, u y⟩ : TotalSpace F V)) e.baseSet :=
    (e.contMDiffOn_symm.comp (contMDiffOn_id.prodMk (contMDiffOn_const (c := c i)))
      fun y hy ↦ e.mem_target.2 hy).congr fun y hy ↦ e.mk_symm hy (c i)
  have hu₀ (y : B) (hy : y ∈ e.baseSet) : u y ≠ 0 := by
    have h : u y = (e.continuousLinearEquivAt ℂ y hy).symm (c i) := by
      rw [e.symm_continuousLinearEquivAt_eq hy, e.symmL_apply (R := ℂ) hy]
    rw [h, ne_eq, map_eq_zero_iff _ (e.continuousLinearEquivAt ℂ y hy).symm.injective]
    exact c.ne_zero i
  have hne (y : B) (hy : y ∈ e.baseSet) : Inner.inner ℝ (u y) (u y) ≠ 0 :=
    inner_self_ne_zero.mpr (hu₀ y hy)
  have hc : ContMDiffOn I 𝓘(ℝ, ℂ) n (fun y ↦ ((‖u y‖⁻¹ : ℝ) : ℂ)) e.baseSet := by
    refine Complex.ofRealCLM.contMDiff.comp_contMDiffOn
      ((((hu.inner_bundle hu).sqrt hne).inv₀ fun y hy ↦ ?_).congr fun y _ ↦ ?_)
    · exact Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne real_inner_self_nonneg (hne y hy).symm)
    · simp [Real.sqrt_sq (norm_nonneg _)]
      rfl
  have hIio : Finset.Iio i = ∅ := by ext j; simp [hi j]
  refine ((contMDiffOn_const (c := ⟪b i, 1⟫_ℂ)).smul_totalSpace
    (hc.smul_totalSpace hu)).congr fun y hy ↦ ?_
  rw [orthonormalFrameAt_of_mem e c b hy, orthonormalFrame_apply,
    Fintype.sum_eq_single i fun j hj ↦ (hj (hi j)).elim, orthonormalBasis_apply,
    InnerProductSpace.gramSchmidtNormed, InnerProductSpace.gramSchmidt_def, hIio,
    Finset.sum_empty, sub_zero, e.symmL_apply (R := ℂ) hy, Complex.ofReal_inv]
  rfl

namespace SymplecticGeometry.Bundle

variable [Fact (finrank ℂ F = 1)]

local instance : FiniteDimensional ℂ F := .of_fact_finrank_eq_succ 0

local instance : Fact (finrank ℂ ℂ = finrank ℂ F) :=
  ⟨by rw [finrank_self, Fact.out (p := finrank ℂ F = 1)]⟩

local instance : FiniteDimensional ℝ F := Module.Finite.trans ℂ F

/-- **The unitary frames of a smooth Hermitian line bundle form a smooth principal
`Circle`-bundle.** For a smooth `i`-invariant metric `g` on a smooth complex line bundle `V`, the
principal `Circle`-bundle `instPrincipalBundleCircleFiber` of its unitary frames is a `C^n` fibre
bundle: its transition functions, the inner products `⟪σ' 1, σ 1⟫` of the unit vectors of two
local unitary frames, are `C^n`. So `TauCeti.ManifoldTotalSpace Circle (Fiber ℂ F V ℂ)` is a
`C^n` manifold on which Tau Ceti's smooth principal-bundle API applies. -/
theorem contMDiffFiberBundle_circleFiber [IsManifold I n B] :
    letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
    letI : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
    letI : IsContinuousRiemannianBundle F V :=
      instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
    ContMDiffFiberBundle n Circle (Fiber ℂ F V ℂ) I (𝓡 1) := by
  let : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
  let : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
  let : IsContinuousRiemannianBundle F V :=
    instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
  refine (PrincipalBundle.contMDiffFiberBundle_iff (n := n) (G := Circle)
    (P := Fiber ℂ F V ℂ) (IB := I) (IG := 𝓡 1)).2 fun t₁ t₂ h₁ h₂ ↦ ?_
  obtain ⟨s₁, hs₁, rfl⟩ :=
    FiberBundle.exists_eq_changeModelFiber_of_memTrivializationAtlas _ _ t₁ h₁
  obtain ⟨s₂, hs₂, rfl⟩ :=
    FiberBundle.exists_eq_changeModelFiber_of_memTrivializationAtlas _ _ t₂ h₂
  obtain ⟨e₁, he₁, c₁, b₁, rfl⟩ :=
    (Trivialization.memTrivializationAtlas_orthonormalFrameBundleFiber_iff s₁).1 hs₁
  obtain ⟨e₂, he₂, c₂, b₂, rfl⟩ :=
    (Trivialization.memTrivializationAtlas_orthonormalFrameBundleFiber_iff s₂).1 hs₂
  simp only [Trivialization.baseSet_changeModelFiber,
    Trivialization.baseSet_orthonormalFrameBundleFiber,
    Trivialization.baseSet_orthonormalFrameBundle]
  refine ContMDiffOn.of_coe_circle (e₁.open_baseSet.inter e₂.open_baseSet) ?_
  exact (g.contMDiffOn_hermitianPairing hI (b := id)
    ((e₂.contMDiffOn_orthonormalFrameAt_one g hI c₂ b₂).mono Set.inter_subset_right)
    ((e₁.contMDiffOn_orthonormalFrameAt_one g hI c₁ b₁).mono Set.inter_subset_left)).congr
    fun y hy ↦ e₁.coe_coordChange_changeModelFiber_orthonormalFrameBundleFiber c₁ b₁ e₂ c₂ b₂
      hy.1 hy.2

variable [IsManifold I n B]

/-- The map `φ ↦ ⟨x, φ 1⟩` from the unitary frames to the total space is `C^n`. -/
private theorem contMDiff_frame_one :
    letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
    letI : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
    letI : IsContinuousRiemannianBundle F V :=
      instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
    ContMDiff (I.prod (𝓡 1)) (I.prod 𝓘(ℝ, F)) n fun x : ManifoldTotalSpace Circle (Fiber ℂ F V ℂ) ↦
      (⟨((ManifoldTotalSpace.homeomorph _ _).symm x).proj,
        ((ManifoldTotalSpace.homeomorph _ _).symm x).snd.frame 1⟩ : TotalSpace F V) := by
  let : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
  let : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
  let : IsContinuousRiemannianBundle F V :=
    instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
  have := contMDiffFiberBundle_circleFiber g hI
  intro x₀
  set h := ManifoldTotalSpace.homeomorph Circle (Fiber ℂ F V ℂ)
  have ht := trivialization_mem_atlas Circle (Fiber ℂ F V ℂ) (h.symm x₀).proj
  obtain ⟨s, hs, hst⟩ :=
    FiberBundle.exists_eq_changeModelFiber_of_memTrivializationAtlas _ _ _ ⟨ht⟩
  obtain ⟨e, he, c, b, rfl⟩ :=
    (Trivialization.memTrivializationAtlas_orthonormalFrameBundleFiber_iff s).1 hs
  set t := trivializationAt Circle (Fiber ℂ F V ℂ) (h.symm x₀).proj
  have hx₀ : x₀ ∈ h.symm ⁻¹' t.source :=
    t.mem_source.2 (mem_baseSet_trivializationAt Circle (Fiber ℂ F V ℂ) _)
  have hU : IsOpen (h.symm ⁻¹' t.source) := t.open_source.preimage h.symm.continuous
  -- In the trivialization `t`, the map is `(y, z) ↦ ⟨y, z • σ 1⟩`.
  have hG : ContMDiffOn (I.prod (𝓡 1)) (I.prod 𝓘(ℝ, F)) n
      (fun q : B × Circle ↦ (⟨q.1, (q.2 : ℂ) • e.orthonormalFrameAt c b q.1 1⟩ : TotalSpace F V))
      (e.baseSet ×ˢ Set.univ) :=
    (contMDiff_coe_circle.comp contMDiff_snd).contMDiffOn.smul_totalSpace
      ((e.contMDiffOn_orthonormalFrameAt_one g hI c b).comp contMDiff_fst.contMDiffOn
        fun q (hq : q ∈ e.baseSet ×ˢ Set.univ) ↦ hq.1)
  have hb : t.baseSet = e.baseSet := by rw [hst]; simp
  refine ((hG.comp (ManifoldTotalSpace.contMDiffOn_trivialization t) fun x hx ↦ ?_).contMDiffAt
    (hU.mem_nhds hx₀)).congr_of_eventuallyEq ?_
  · rw [← hb, ← t.target_eq]
    exact t.map_source hx
  · filter_upwards [hU.mem_nhds hx₀] with x hx
    have hq : (t (h.symm x)).1 ∈ e.baseSet := by
      have h' := t.map_source hx
      rw [t.target_eq, hb] at h'
      exact h'.1
    rw [Set.mem_preimage, hst] at hx
    rw [hst] at hq
    simp only [Function.comp_apply, hst]
    conv_lhs => rw [← (Trivialization.toOpenPartialHomeomorph _).left_inv hx]
    exact e.frame_changeModelFiber_orthonormalFrameBundleFiber_symm_one c b hq _
variable [I.Boundaryless] [FiniteDimensional ℝ EB]

/-- The inverse of `circleBundleHomeomorph`, from the unit vectors with the regular-level charts
of Tau Ceti's `sphereBundleChartedSpace` to the unitary frames, is `C^n`. -/
private theorem contMDiff_circleBundleHomeomorph_symm (hn : 1 ≤ n) :
    letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
    letI : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
    letI : IsContinuousRiemannianBundle F V :=
      instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
    letI : IsContMDiffRiemannianBundle I n F V := ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
    letI := sphereBundleChartedSpace (F := F) (V := V) (contMDiff_const (I := I) (c := (1 : ℝ)))
      hn fun _ ↦ one_pos
    ContMDiff 𝓘(ℝ, Fin (finrank ℝ (EB × F) - 1) → ℝ) (I.prod (𝓡 1)) n
      fun p : {p : TotalSpace F V // ‖p.snd‖ = 1} ↦ ManifoldTotalSpace.homeomorph _ _
        (⟨(circleBundleHomeomorph.symm p).proj, (circleBundleHomeomorph.symm p).snd⟩ :
          TotalSpace Circle (Fiber ℂ F V ℂ)) := by
  let : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
  let : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
  let : IsContinuousRiemannianBundle F V :=
    instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
  let : IsContMDiffRiemannianBundle I n F V := ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
  let := sphereBundleChartedSpace (F := F) (V := V) (contMDiff_const (I := I) (c := (1 : ℝ)))
    hn fun _ ↦ one_pos
  have := isManifold_sphereBundle (F := F) (V := V) (contMDiff_const (I := I) (c := (1 : ℝ)))
    hn fun _ ↦ one_pos
  have hval := (isSmoothEmbedding_coe_sphereBundle (F := F) (V := V)
    (contMDiff_const (I := I) (c := (1 : ℝ))) hn fun _ ↦ one_pos).contMDiff
  have hproj : ContMDiff 𝓘(ℝ, Fin (finrank ℝ (EB × F) - 1) → ℝ) I n
      fun p : {p : TotalSpace F V // ‖p.snd‖ = 1} ↦ p.val.proj :=
    (Bundle.contMDiff_proj V).comp hval
  intro p₀
  refine ManifoldTotalSpace.contMDiffAt_iff.2 ⟨hproj p₀, ?_⟩
  have ht := trivialization_mem_atlas Circle (Fiber ℂ F V ℂ) p₀.val.proj
  obtain ⟨s, hs, hst⟩ :=
    FiberBundle.exists_eq_changeModelFiber_of_memTrivializationAtlas _ _ _ ⟨ht⟩
  obtain ⟨e, he, c, b, rfl⟩ :=
    (Trivialization.memTrivializationAtlas_orthonormalFrameBundleFiber_iff s).1 hs
  have hb : (trivializationAt Circle (Fiber ℂ F V ℂ) p₀.val.proj).baseSet = e.baseSet := by
    rw [hst]; simp
  have hW : IsOpen {p : {p : TotalSpace F V // ‖p.snd‖ = 1} | p.val.proj ∈ e.baseSet} :=
    e.open_baseSet.preimage hproj.continuous
  have hp₀ : p₀.val.proj ∈ e.baseSet :=
    hb ▸ mem_baseSet_trivializationAt Circle (Fiber ℂ F V ℂ) p₀.val.proj
  -- Over the base set of `e`, the fibre coordinate of the frame of `v` is `⟪σ 1, v⟫`.
  refine (ContMDiffOn.of_coe_circle hW ((g.contMDiffOn_hermitianPairing hI
    (b := fun p : {p : TotalSpace F V // ‖p.snd‖ = 1} ↦ p.val.proj)
    ((e.contMDiffOn_orthonormalFrameAt_one g hI c b).comp hproj.contMDiffOn fun p hp ↦ hp)
    hval.contMDiffOn).congr fun p hp ↦ ?_)).contMDiffAt (hW.mem_nhds hp₀)
  have key := e.coe_snd_changeModelFiber_orthonormalFrameBundleFiber c b
    (⟨(circleBundleHomeomorph.symm p).proj, (circleBundleHomeomorph.symm p).snd⟩ :
          TotalSpace Circle (Fiber ℂ F V ℂ)) hp
  rw [← hst] at key
  have h1 := circleBundleHomeomorph_symm_apply_frame (F := F) p 1
  rw [one_smul] at h1
  exact key.trans (congrArg _ (TotalSpace.mk_inj.1 h1))

/-- **The unitary frames of a smooth Hermitian line bundle are diffeomorphic to its unit
vectors.** For `n ≥ 1`, `circleBundleHomeomorph`, `φ ↦ φ 1`, is a `C^n` diffeomorphism from the
smooth principal `Circle`-bundle of `contMDiffFiberBundle_circleFiber` onto the unit vectors with
the smooth structure of a regular level set, Tau Ceti's `sphereBundleChartedSpace` of radius `1`.
-/
def circleBundleDiffeomorph (hn : 1 ≤ n) :
    letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
    letI : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
    letI : IsContinuousRiemannianBundle F V :=
      instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
    letI : IsContMDiffRiemannianBundle I n F V := ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
    letI := sphereBundleChartedSpace (F := F) (V := V) (contMDiff_const (I := I) (c := (1 : ℝ)))
      hn fun _ ↦ one_pos
    ManifoldTotalSpace Circle (Fiber ℂ F V ℂ) ≃ₘ^n⟮I.prod (𝓡 1),
      𝓘(ℝ, Fin (finrank ℝ (EB × F) - 1) → ℝ)⟯ {p : TotalSpace F V // ‖p.snd‖ = 1} :=
  letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
  letI : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
  letI : IsContinuousRiemannianBundle F V :=
    instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
  letI : IsContMDiffRiemannianBundle I n F V := ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
  letI := sphereBundleChartedSpace (F := F) (V := V) (contMDiff_const (I := I) (c := (1 : ℝ)))
    hn fun _ ↦ one_pos
  { toEquiv := (((ManifoldTotalSpace.homeomorph Circle (Fiber ℂ F V ℂ)).symm.trans
      (TotalSpace.modelFiberHomeomorph ⟨rfl⟩)).trans circleBundleHomeomorph).toEquiv
    contMDiff_toFun := (isSmoothEmbedding_coe_sphereBundle (F := F) (V := V)
      (contMDiff_const (I := I) (c := (1 : ℝ))) hn fun _ ↦ one_pos).contMDiff_iff_comp.2
        ((contMDiff_frame_one g hI).congr fun x ↦ by
          simp [TotalSpace.coe_modelFiberHomeomorph, TotalSpace.modelFiberEquiv_apply])
    contMDiff_invFun := (contMDiff_circleBundleHomeomorph_symm g hI hn).congr fun p ↦ by
      simp [TotalSpace.coe_modelFiberHomeomorph_symm, TotalSpace.modelFiberEquiv_symm_apply] }

/-- `circleBundleDiffeomorph` sends a frame `φ` of `V x` to the unit vector `φ 1`. -/
theorem coe_circleBundleDiffeomorph_homeomorph (hn : 1 ≤ n) :
    letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
    letI : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
    letI : IsContinuousRiemannianBundle F V :=
      instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
    ∀ p : TotalSpace Circle (Fiber ℂ F V ℂ),
      (circleBundleDiffeomorph g hI hn (ManifoldTotalSpace.homeomorph _ _ p) : TotalSpace F V) =
        ⟨p.proj, p.snd.frame 1⟩ := by
  let : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
  let : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
  let : IsContinuousRiemannianBundle F V :=
    instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
  intro p
  -- `circleBundleDiffeomorph` is `circleBundleHomeomorph` after the change of model fibre.
  change (circleBundleHomeomorph (TotalSpace.modelFiberHomeomorph ⟨rfl⟩
    ((ManifoldTotalSpace.homeomorph _ _).symm (ManifoldTotalSpace.homeomorph _ _ p))) :
      TotalSpace F V) = _
  rw [Homeomorph.symm_apply_apply, TotalSpace.coe_modelFiberHomeomorph,
    TotalSpace.modelFiberEquiv_apply, circleBundleHomeomorph_apply]

/-- **`circleBundleDiffeomorph` is `Circle`-equivariant**, fibre by fibre: it turns the right action
of `Circle` on the frames of `V x` into its action on unit vectors. -/
theorem circleBundleDiffeomorph_op_smul (hn : 1 ≤ n) :
    letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
    letI : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
    letI : IsContinuousRiemannianBundle F V :=
      instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
    ∀ (z : Circle) {x : B} (φ : Fiber ℂ F V ℂ x),
      circleBundleDiffeomorph g hI hn (ManifoldTotalSpace.homeomorph _ _ ⟨x, op z • φ⟩) =
        z • circleBundleDiffeomorph g hI hn (ManifoldTotalSpace.homeomorph _ _ ⟨x, φ⟩) := by
  let : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
  let : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
  let : IsContinuousRiemannianBundle F V :=
    instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
  intro z x φ
  refine Subtype.ext ?_
  rw [circleBundle_smul_apply, coe_circleBundleDiffeomorph_homeomorph,
    coe_circleBundleDiffeomorph_homeomorph, Fiber.frame_op_circle_smul_apply, mul_one,
    frame_apply_eq_smul]

end SymplecticGeometry.Bundle

end Smooth

end
