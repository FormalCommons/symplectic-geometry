/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.VectorBundle.FiniteDimensional
public import TauCeti.Topology.VectorBundle.OrthonormalFrame.Associated
public import TauCeti.Topology.VectorBundle.Smul
public import SymplecticGeometry.Analysis.CStarAlgebra.Unitary.ContinuousLinearMap
public import SymplecticGeometry.Analysis.Normed.Operator.SpanSingleton
public import SymplecticGeometry.Topology.FiberBundle.Principal.ChangeGroup
public import SymplecticGeometry.Geometry.Manifold.Instances.Sphere
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Riemannian.Hermitian
public import TauCeti.Geometry.Manifold.FiberBundle.Principal
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Sphere
public import SymplecticGeometry.Topology.VectorBundle.Complex.RestrictScalars
public import SymplecticGeometry.LinearAlgebra.Complex.FiniteDimensional
import SymplecticGeometry.GroupTheory.GroupAction.Hom
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Hermitian.Frame
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Riemannian.Norm
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

The rank-one condition is the instance `Fact (Module.finrank ℂ F = 1)`. The instances
`FiniteDimensional.of_fact_finrank_eq_one` and
`Module.fact_finrank_self_eq_of_fact_finrank_eq_one` derive from it that `F` is
finite-dimensional and has the rank of `ℂ`. The topology on the frames with model fibre `Circle`
is induced from Tau Ceti's along `Bundle.TotalSpace.modelFiberEquiv`
(`SymplecticGeometry.Bundle.isInducing_modelFiberEquiv_circleFiber`).

The last section adds the smooth structure, for a Hermitian line bundle `(g, hI)` over a manifold:
a smooth complex line bundle `V` with a smooth `i`-invariant real metric `g`, whose fibres get
their norms and Hermitian products from `g` through three local instances (written with `letI` in
the statements). The unit vector `σ 1` of a local unitary frame is then a smooth local section
(`Bundle.Trivialization.contMDiffOn_orthonormalFrameAt_one`, a case of the smoothness of local
unitary frames in any rank,
`Bundle.Trivialization.contMDiffOn_totalSpaceMk_orthonormalFrameAt_complex`), so the transition
functions above are smooth. By Tau Ceti's
`TauCeti.PrincipalBundle.contMDiffFiberBundle_iff`, the unitary frames thus form a smooth
principal `Circle`-bundle (`SymplecticGeometry.Bundle.contMDiffFiberBundle_circleFiber`), charted
through the fibre as `TauCeti.ManifoldTotalSpace Circle (Fiber ℂ F V ℂ)`; Tau Ceti's
`TauCeti.ManifoldTotalSpace.isSubmersion_proj` applies to its projection. A family of unitary
frames over an open set is smooth into this bundle exactly when its unit vectors are smooth into
the total space of `V` (`SymplecticGeometry.Bundle.contMDiffOn_circleFiber_iff`). Hence the
normalization `s / ‖s‖` of a smooth section `s` with no zero on an open set, as the family of
frames `SymplecticGeometry.Bundle.normalizedFrame (s x)`, is smooth there
(`SymplecticGeometry.Bundle.contMDiffOn_normalizedFrame`), and every point of the base has a
smooth local section of the circle bundle
(`SymplecticGeometry.Bundle.exists_contMDiffOn_circleFiber`). For a
finite-dimensional base without boundary, `circleBundleHomeomorph` is a diffeomorphism onto the
unit vectors with the smooth structure of a regular level set that Tau Ceti's
`sphereBundleChartedSpace` gives them (`SymplecticGeometry.Bundle.circleBundleDiffeomorph`),
equivariant fibre by fibre (`SymplecticGeometry.Bundle.circleBundleDiffeomorph_op_smul`). It
and its inverse are computed by `SymplecticGeometry.Bundle.circleBundleDiffeomorph_homeomorph`,
`SymplecticGeometry.Bundle.coe_circleBundleDiffeomorph_homeomorph` and
`SymplecticGeometry.Bundle.circleBundleDiffeomorph_symm_apply`.

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
* `SymplecticGeometry.Bundle.normalizedFrame`: the unitary frame `z ↦ (z / ‖v‖) • v` of a nonzero
  vector `v` of a fibre.

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

/-! ### The rank-one convention

The model fibre `F` of a complex line bundle here comes with `Fact (finrank ℂ F = 1)`. The two
instances below derive from such a fact, over any division ring, that `F` is finite-dimensional
and that it has the rank of the model fibre `ℂ` of the unitary frames, which Tau Ceti's frame
bundle asks for. Mathlib's `FiniteDimensional.of_fact_finrank_eq_succ` is not an instance, since
its `n` cannot be inferred; for rank one there is no `n`. -/

/-- A module of rank one, the rank given by a `Fact`, is finite-dimensional. -/
instance FiniteDimensional.of_fact_finrank_eq_one {K V : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] [Fact (finrank K V = 1)] : FiniteDimensional K V :=
  .of_fact_finrank_eq_succ 0

/-- A module of rank one, the rank given by a `Fact`, has the rank of the ring itself. -/
instance Module.fact_finrank_self_eq_of_fact_finrank_eq_one {K V : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] [Fact (finrank K V = 1)] : Fact (finrank K K = finrank K V) :=
  ⟨by rw [finrank_self, Fact.out (p := finrank K V = 1)]⟩

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

/-- The total space of the unitary frame bundle of a complex line bundle is homeomorphic to its
unit vectors: a frame `φ : ℂ ≃ₗᵢ[ℂ] E x` goes to the unit vector `φ 1`. -/
def circleBundleHomeomorph :
    TotalSpace (unitary (ℂ →L[ℂ] ℂ)) (Fiber ℂ F E ℂ) ≃ₜ {p : TotalSpace F E // ‖p.snd‖ = 1} where
  toFun φ := ⟨⟨φ.proj, φ.snd.frame 1⟩, by simp⟩
  invFun p := ⟨p.val.proj, .ofFrame (LinearIsometryEquiv.toSpanSingleton ℂ _
    ((VectorBundle.finrank_eq ℂ F E _).trans Fact.out) p.property)⟩
  left_inv φ := by
    refine TotalSpace.ext rfl (heq_of_eq (Fiber.ext (LinearIsometryEquiv.ext fun z ↦ ?_)))
    rw [Fiber.frame_ofFrame, LinearIsometryEquiv.toSpanSingleton_apply, ← map_eq_smul_map_one]
  right_inv p := Subtype.ext <| congrArg (TotalSpace.mk p.val.proj) <| by
    rw [Fiber.frame_ofFrame, LinearIsometryEquiv.toSpanSingleton_one]
  continuous_toFun := (continuous_totalSpace_iff.1 continuous_id 1).subtype_mk fun _ ↦ by simp
  continuous_invFun := by
    refine continuous_totalSpace_iff.2 fun z ↦ ?_
    simpa only [Fiber.frame_ofFrame, LinearIsometryEquiv.toSpanSingleton_apply] using
      Continuous.smul_totalSpace (continuous_const (y := z)) continuous_subtypeVal

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

open scoped Classical in
/-- The **normalization** of a vector `v` of a fibre of a complex line bundle, as a unitary frame:
for `v ≠ 0`, the frame `z ↦ (z / ‖v‖) • v`, whose unit vector is `v / ‖v‖`
(`SymplecticGeometry.Bundle.frame_normalizedFrame_apply`). For `v = 0` it is some unitary frame
of the fibre. -/
def normalizedFrame {x : B} (v : E x) : Fiber ℂ F E ℂ x :=
  haveI : Nontrivial (E x) :=
    Module.nontrivial_of_finrank_eq_succ (n := 0) ((VectorBundle.finrank_eq ℂ F E x).trans Fact.out)
  let w : E x := if v = 0 then (exists_ne (0 : E x)).choose else v
  have hw : ‖w‖ ≠ 0 := norm_ne_zero_iff.2 <| by
    dsimp only [w]
    split_ifs with h
    exacts [(exists_ne _).choose_spec, h]
  .ofFrame (LinearIsometryEquiv.toSpanSingleton ℂ _
    ((VectorBundle.finrank_eq ℂ F E x).trans Fact.out) (v := (‖w‖ : ℂ)⁻¹ • w) (by
      rw [norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_cancel₀ hw]))

/-- The normalization of a nonzero vector `v` is the frame `z ↦ (z / ‖v‖) • v`. -/
@[simp]
theorem frame_normalizedFrame_apply {x : B} {v : E x} (hv : v ≠ 0) (z : ℂ) :
    (normalizedFrame (F := F) v).frame z = (z / ‖v‖) • v := by
  simp only [normalizedFrame, Fiber.frame_ofFrame, LinearIsometryEquiv.toSpanSingleton_apply, hv,
    ↓reduceIte]
  rw [smul_smul, div_eq_mul_inv]

/-- The unit vector of the normalization of a nonzero vector `v` is `v / ‖v‖`. -/
theorem frame_normalizedFrame_one {x : B} {v : E x} (hv : v ≠ 0) :
    (normalizedFrame (F := F) v).frame 1 = (‖v‖ : ℂ)⁻¹ • v := by
  rw [frame_normalizedFrame_apply hv, one_div]

/-- `circleBundleHomeomorph` turns the right action of `unitary (ℂ →L[ℂ] ℂ)` on frames into the
action of `Circle` on unit vectors, along `Unitary.continuousLinearMapCircleEquiv`. -/
theorem circleBundleHomeomorph_smul (u : unitary (ℂ →L[ℂ] ℂ)) {x : B} (φ : Fiber ℂ F E ℂ x) :
    circleBundleHomeomorph (⟨x, op u • φ⟩ : TotalSpace (unitary (ℂ →L[ℂ] ℂ)) (Fiber ℂ F E ℂ)) =
      Unitary.continuousLinearMapCircleEquiv u • circleBundleHomeomorph ⟨x, φ⟩ := by
  rw [Subtype.ext_iff, circleBundle_smul_apply, circleBundleHomeomorph_apply,
    circleBundleHomeomorph_apply, Fiber.frame_smul_apply, unop_op,
    Unitary.coe_continuousLinearMapCircleEquiv_apply, map_eq_smul_map_one]

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

/-- `Bundle.TotalSpace.modelFiberEquiv`, from the unitary frames with model fibre `Circle` to
those with model fibre `unitary (ℂ →L[ℂ] ℂ)`, is inducing: the topology
`instTopologicalSpaceTotalSpaceCircleFiber` is induced along it. -/
theorem isInducing_modelFiberEquiv_circleFiber :
    Topology.IsInducing
      (TotalSpace.modelFiberEquiv (unitary (ℂ →L[ℂ] ℂ)) Circle (Fiber ℂ F E ℂ)) :=
  ⟨rfl⟩

variable [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace ℂ F] [FiberBundle F E]
  [VectorBundle ℂ F E] [ContinuousFiberNorm F E] [Fact (finrank ℂ F = 1)]

/-- The unitary frames of a complex line bundle form a fibre bundle with fibre `Circle`: Tau Ceti's
frame bundle with its model fibre `unitary (ℂ →L[ℂ] ℂ)` replaced by `Circle` along
`Unitary.continuousLinearMapCircleEquiv` (`FiberBundle.changeModelFiber`). -/
instance instFiberBundleCircleFiber : FiberBundle Circle (Fiber ℂ F E ℂ) :=
  FiberBundle.changeModelFiber (Unitary.continuousLinearMapCircleEquiv : _ ≃ₜ Circle)
      isInducing_modelFiberEquiv_circleFiber

/-- **The unitary frames of a complex line bundle form a principal `Circle`-bundle**, `Circle`
acting on the right by precomposition with multiplication: the change of structure group of
Tau Ceti's principal `unitary (ℂ →L[ℂ] ℂ)`-bundle along
`Unitary.continuousLinearMapCircleEquiv`. -/
instance instPrincipalBundleCircleFiber : PrincipalBundle Circle (Fiber ℂ F E ℂ) :=
  PrincipalBundle.changeGroup Unitary.continuousLinearMapCircleEquiv
    isInducing_modelFiberEquiv_circleFiber fun _ _ _ ↦ rfl

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
      (Unitary.continuousLinearMapCircleEquiv : _ ≃ₜ Circle)
      isInducing_modelFiberEquiv_circleFiber p).2 : ℂ) =
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
      (Unitary.continuousLinearMapCircleEquiv : _ ≃ₜ Circle)
      isInducing_modelFiberEquiv_circleFiber).toOpenPartialHomeomorph.symm
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
      (Unitary.continuousLinearMapCircleEquiv : _ ≃ₜ Circle)
      isInducing_modelFiberEquiv_circleFiber).coordChange
        ((e'.orthonormalFrameBundle c' b').orthonormalFrameBundleFiber.changeModelFiber
          (Unitary.continuousLinearMapCircleEquiv : _ ≃ₜ Circle)
          isInducing_modelFiberEquiv_circleFiber) y 1 : ℂ) =
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

attribute [local instance] finrank_real_complex_fact'

open scoped VectorBundle.ComplexToReal Module.ComplexToReal

variable [ContMDiffVectorBundle n F V I] (g : ContMDiffRiemannianMetric I n F V)
  (hI : ∀ x (v w : V x), g.inner x (Complex.I • v) (Complex.I • w) = g.inner x v w)

/-- For a smooth Hermitian metric on a complex line bundle, the unit vector `σ 1` of the local
unitary frame `σ = e.orthonormalFrameAt c b` of a trivialization `e` of the atlas is a smooth
section over the base set of `e`: the case `w = 1` of
`Bundle.Trivialization.contMDiffOn_totalSpaceMk_orthonormalFrameAt_complex`. -/
theorem Bundle.Trivialization.contMDiffOn_orthonormalFrameAt_one
    (e : Trivialization F (π F V)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [LinearOrder ι] [LocallyFiniteOrderBot ι] (c : Basis ι ℂ F)
    (b : OrthonormalBasis ι ℂ ℂ) :
    letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
    letI : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
    ContMDiffOn I (I.prod 𝓘(ℝ, F)) n
      (fun y ↦ (⟨y, e.orthonormalFrameAt c b y 1⟩ : TotalSpace F V)) e.baseSet :=
  e.contMDiffOn_totalSpaceMk_orthonormalFrameAt_complex g hI
    (e.mem_maximalAtlas_of_memTrivializationAtlas I n) c b 1

namespace SymplecticGeometry.Bundle

variable [Fact (finrank ℂ F = 1)]

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
  refine ContMDiffOn.of_coe_sphere (E := ℂ) ?_
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
    (contMDiff_coe_sphere.comp contMDiff_snd).contMDiffOn.smul_totalSpace
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

section Sections

variable {EM HM M : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [TopologicalSpace HM]
  {IM : ModelWithCorners ℝ EM HM} [TopologicalSpace M] [ChartedSpace HM M]

/-- **Smooth families of unitary frames are smooth families of unit vectors.** On an open set `U`,
a family `σ m` of unitary frames of `V (b m)` is `C^n` as a map into the smooth principal
`Circle`-bundle of `contMDiffFiberBundle_circleFiber` if and only if its family of unit vectors
`σ m 1` is `C^n` as a map into the total space of `V`. -/
theorem contMDiffOn_circleFiber_iff {b : M → B} {U : Set M} (hU : IsOpen U) :
    letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
    letI : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
    letI : IsContinuousRiemannianBundle F V :=
      instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
    ∀ σ : ∀ m, Fiber ℂ F V ℂ (b m),
      ContMDiffOn IM (I.prod (𝓡 1)) n
          (fun m ↦ ManifoldTotalSpace.homeomorph Circle (Fiber ℂ F V ℂ) ⟨b m, σ m⟩) U ↔
        ContMDiffOn IM (I.prod 𝓘(ℝ, F)) n
          (fun m ↦ (⟨b m, (σ m).frame 1⟩ : TotalSpace F V)) U := by
  let : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
  let : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
  let : IsContinuousRiemannianBundle F V :=
    instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
  have := contMDiffFiberBundle_circleFiber g hI
  intro σ
  refine ⟨fun h ↦ ((contMDiff_frame_one g hI).comp_contMDiffOn h).congr fun m _ ↦ ?_,
    fun h m₀ hm₀ ↦ ?_⟩
  · exact congrArg (fun p : TotalSpace Circle (Fiber ℂ F V ℂ) ↦ (⟨p.proj, p.snd.frame 1⟩ :
      TotalSpace F V))
      ((ManifoldTotalSpace.homeomorph Circle (Fiber ℂ F V ℂ)).symm_apply_apply ⟨b m, σ m⟩).symm
  have hb : ContMDiffOn IM I n b U := (Bundle.contMDiff_proj V).comp_contMDiffOn h
  refine (ManifoldTotalSpace.contMDiffAt_iff.2
    ⟨hb.contMDiffAt (hU.mem_nhds hm₀), ?_⟩).contMDiffWithinAt
  have ht := trivialization_mem_atlas Circle (Fiber ℂ F V ℂ) (b m₀)
  obtain ⟨s, hs, hst⟩ :=
    FiberBundle.exists_eq_changeModelFiber_of_memTrivializationAtlas _ _ _ ⟨ht⟩
  obtain ⟨e, he, c, b', rfl⟩ :=
    (Trivialization.memTrivializationAtlas_orthonormalFrameBundleFiber_iff s).1 hs
  have hbase : (trivializationAt Circle (Fiber ℂ F V ℂ) (b m₀)).baseSet = e.baseSet := by
    rw [hst]; simp
  have hW : IsOpen (U ∩ b ⁻¹' e.baseSet) := hb.continuousOn.isOpen_inter_preimage hU e.open_baseSet
  have hm : m₀ ∈ U ∩ b ⁻¹' e.baseSet :=
    ⟨hm₀, hbase ▸ mem_baseSet_trivializationAt Circle (Fiber ℂ F V ℂ) (b m₀)⟩
  -- Over the base set of `e`, the fibre coordinate of `σ m` is `⟪τ 1, σ m 1⟫` for the local
  -- unitary frame `τ` of `e`.
  refine ContMDiffAt.of_coe_sphere (E := ℂ) (((g.contMDiffOn_hermitianPairing hI (b := b)
    ((e.contMDiffOn_orthonormalFrameAt_one g hI c b').comp (hb.mono Set.inter_subset_left)
      fun m hm ↦ hm.2) (h.mono Set.inter_subset_left)).congr fun m hm ↦ ?_).contMDiffAt
    (hW.mem_nhds hm))
  have key := e.coe_snd_changeModelFiber_orthonormalFrameBundleFiber c b'
    (⟨b m, σ m⟩ : TotalSpace Circle (Fiber ℂ F V ℂ)) hm.2
  rw [← hst] at key
  exact key

/-- **The normalization of a smooth nonvanishing section is a smooth section of the circle
bundle.** If `s` is a `C^n` family of vectors of `V (b m)` with no zero on an open set `U`, the
family of unitary frames `normalizedFrame (s m)`, with unit vectors `s m / ‖s m‖`, is `C^n` on
`U` as a map into the smooth principal `Circle`-bundle of `contMDiffFiberBundle_circleFiber`. -/
theorem contMDiffOn_normalizedFrame {b : M → B} {s : ∀ m, V (b m)} {U : Set M} (hU : IsOpen U)
    (hs : ContMDiffOn IM (I.prod 𝓘(ℝ, F)) n (fun m ↦ (⟨b m, s m⟩ : TotalSpace F V)) U)
    (h0 : ∀ m ∈ U, s m ≠ 0) :
    letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
    letI : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
    letI : IsContinuousRiemannianBundle F V :=
      instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
    ContMDiffOn IM (I.prod (𝓡 1)) n (fun m ↦ ManifoldTotalSpace.homeomorph Circle
      (Fiber ℂ F V ℂ) ⟨b m, normalizedFrame (F := F) (s m)⟩) U := by
  let : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
  let : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
  let : IsContinuousRiemannianBundle F V :=
    instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
  let : IsContMDiffRiemannianBundle I n F V := ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
  have hnorm : ContMDiffOn IM 𝓘(ℝ, ℂ) n (fun m ↦ ((‖s m‖⁻¹ : ℝ) : ℂ)) U :=
    Complex.ofRealCLM.contMDiff.comp_contMDiffOn
      ((hs.norm_bundle h0).inv₀ fun m hm ↦ norm_ne_zero_iff.2 (h0 m hm))
  refine (contMDiffOn_circleFiber_iff g hI hU _).2 ((hnorm.smul_totalSpace hs).congr fun m hm ↦ ?_)
  rw [frame_normalizedFrame_one (h0 m hm), Complex.ofReal_inv]

/-- **Every point has a smooth local section of the circle bundle.** Every point `x₀` of the base
has an open neighbourhood `U` with a family `σ` of unitary frames, `C^n` on `U` as a map into the
smooth principal `Circle`-bundle of `contMDiffFiberBundle_circleFiber`: the local unitary frame
of a trivialization of `V` at `x₀`. -/
theorem exists_contMDiffOn_circleFiber (x₀ : B) :
    letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
    letI : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
    letI : IsContinuousRiemannianBundle F V :=
      instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
    ∃ U : Set B, IsOpen U ∧ x₀ ∈ U ∧ ∃ σ : ∀ x, Fiber ℂ F V ℂ x,
      ContMDiffOn I (I.prod (𝓡 1)) n
        (fun x ↦ ManifoldTotalSpace.homeomorph Circle (Fiber ℂ F V ℂ) ⟨x, σ x⟩) U := by
  let : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
  let : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
  let : IsContinuousRiemannianBundle F V :=
    instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
  let e := trivializationAt F V x₀
  let c : Basis (Fin 1) ℂ F := Module.finBasisOfFinrankEq ℂ F Fact.out
  let b := OrthonormalBasis.singleton (Fin 1) ℂ
  refine ⟨e.baseSet, e.open_baseSet, mem_baseSet_trivializationAt F V x₀,
    fun x ↦ .ofFrame (e.orthonormalFrameAt c b x), ?_⟩
  exact (contMDiffOn_circleFiber_iff g hI (b := id) e.open_baseSet _).2
    (e.contMDiffOn_orthonormalFrameAt_one g hI c b)

end Sections

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
  rw [← contMDiffOn_univ]
  refine (contMDiffOn_circleFiber_iff g hI
    (b := fun p : {p : TotalSpace F V // ‖p.snd‖ = 1} ↦ p.val.proj) isOpen_univ
    fun p ↦ (circleBundleHomeomorph.symm p).snd).2 (hval.contMDiffOn.congr fun p _ ↦ ?_)
  have h1 := circleBundleHomeomorph_symm_apply_frame (F := F) p 1
  rw [one_smul] at h1
  exact h1

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
      (TotalSpace.modelFiberHomeomorph isInducing_modelFiberEquiv_circleFiber)).trans
        circleBundleHomeomorph).toEquiv
    contMDiff_toFun := (isSmoothEmbedding_coe_sphereBundle (F := F) (V := V)
      (contMDiff_const (I := I) (c := (1 : ℝ))) hn fun _ ↦ one_pos).contMDiff_iff_comp.2
        ((contMDiff_frame_one g hI).congr fun x ↦ by
          simp [TotalSpace.coe_modelFiberHomeomorph, TotalSpace.modelFiberEquiv_apply])
    contMDiff_invFun := (contMDiff_circleBundleHomeomorph_symm g hI hn).congr fun p ↦ by
      simp [TotalSpace.coe_modelFiberHomeomorph_symm, TotalSpace.modelFiberEquiv_symm_apply] }

/-- `circleBundleDiffeomorph` is `circleBundleHomeomorph`, read through the identification of the
total space of the unitary frame bundle with model fibre `Circle` with
`TauCeti.ManifoldTotalSpace Circle (Fiber ℂ F V ℂ)`. -/
theorem circleBundleDiffeomorph_homeomorph (hn : 1 ≤ n) :
    letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
    letI : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
    letI : IsContinuousRiemannianBundle F V :=
      instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
    ∀ p : TotalSpace Circle (Fiber ℂ F V ℂ),
      circleBundleDiffeomorph g hI hn (ManifoldTotalSpace.homeomorph _ _ p) =
        circleBundleHomeomorph ⟨p.proj, p.snd⟩ := by
  let : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
  let : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
  let : IsContinuousRiemannianBundle F V :=
    instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
  intro p
  -- `circleBundleDiffeomorph` is defined as `circleBundleHomeomorph` after the change of model
  -- fibre, and this is the statement of that definition.
  change circleBundleHomeomorph (TotalSpace.modelFiberHomeomorph
    isInducing_modelFiberEquiv_circleFiber
    ((ManifoldTotalSpace.homeomorph _ _).symm (ManifoldTotalSpace.homeomorph _ _ p))) = _
  rw [Homeomorph.symm_apply_apply, TotalSpace.coe_modelFiberHomeomorph,
    TotalSpace.modelFiberEquiv_apply]

/-- `circleBundleDiffeomorph` sends a frame `φ` of `V x` to the unit vector `φ 1`. -/
@[simp]
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
  rw [circleBundleDiffeomorph_homeomorph, circleBundleHomeomorph_apply]

/-- The inverse of `circleBundleDiffeomorph` sends a unit vector `p` to the frame
`circleBundleHomeomorph.symm p`, read in `TauCeti.ManifoldTotalSpace Circle (Fiber ℂ F V ℂ)`. -/
@[simp]
theorem circleBundleDiffeomorph_symm_apply (hn : 1 ≤ n) :
    letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
    letI : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
    letI : IsContinuousRiemannianBundle F V :=
      instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
    letI : IsContMDiffRiemannianBundle I n F V := ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
    letI := sphereBundleChartedSpace (F := F) (V := V) (contMDiff_const (I := I) (c := (1 : ℝ)))
      hn fun _ ↦ one_pos
    ∀ p : {p : TotalSpace F V // ‖p.snd‖ = 1},
      (circleBundleDiffeomorph g hI hn).symm p = ManifoldTotalSpace.homeomorph _ _
        ⟨(circleBundleHomeomorph.symm p).proj, (circleBundleHomeomorph.symm p).snd⟩ := by
  let : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
  let : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
  let : IsContinuousRiemannianBundle F V :=
    instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
  let : IsContMDiffRiemannianBundle I n F V := ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
  let := sphereBundleChartedSpace (F := F) (V := V) (contMDiff_const (I := I) (c := (1 : ℝ)))
    hn fun _ ↦ one_pos
  intro p
  rw [← (circleBundleDiffeomorph g hI hn).symm_apply_apply (ManifoldTotalSpace.homeomorph _ _ _),
    circleBundleDiffeomorph_homeomorph]
  exact congrArg _ (circleBundleHomeomorph.apply_symm_apply p).symm

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
  rw [circleBundleDiffeomorph_homeomorph, circleBundleDiffeomorph_homeomorph]
  exact circleBundleHomeomorph_op_circle_smul z φ

end SymplecticGeometry.Bundle

end Smooth

end
