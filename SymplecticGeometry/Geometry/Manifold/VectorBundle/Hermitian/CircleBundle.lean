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
  (`Bundle.Trivialization.changeModelFiber`).

The rank-one condition is the instance `Fact (Module.finrank ℂ F = 1)`.

## Main definitions

* `SymplecticGeometry.Bundle.circleBundleHomeomorph`: the total space of the unitary frame bundle
  is homeomorphic to the unit vectors, by `φ ↦ φ 1`.
* `SymplecticGeometry.Bundle.instFiberBundleCircleFiber`,
  `SymplecticGeometry.Bundle.instPrincipalBundleCircleFiber`: the unitary frame bundle as a
  principal `Circle`-bundle.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.7
  (the unit circle bundle of a Hermitian line bundle as a principal circle bundle).
* D. Husemoller, *Fibre Bundles*, third edition, Graduate Texts in Mathematics 20, Springer
  (1994), Chapter 4 (principal bundles) and Chapter 5, §§4–5 (the bundle of unitary frames).
-/

public section

noncomputable section

open Bundle MulOpposite Module TauCeti TauCeti.OrthonormalFrameBundle

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
`Bundle.TotalSpace.modelFiberEquiv`, as `TauCeti.PrincipalBundle.changeGroup` asks. -/
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

end
