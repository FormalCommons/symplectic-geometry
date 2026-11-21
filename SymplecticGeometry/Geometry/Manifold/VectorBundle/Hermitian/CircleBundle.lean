/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Complex.Circle
public import TauCeti.Topology.VectorBundle.OrthonormalFrame.Principal
public import TauCeti.Topology.VectorBundle.Smul
public import SymplecticGeometry.Analysis.CStarAlgebra.Unitary.ContinuousLinearMap

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
  `SymplecticGeometry.Bundle.unitaryCircleEquiv`, which sends `u` to `u 1`;
* the unitary frame bundle is a principal `Circle`-bundle
  (`SymplecticGeometry.Bundle.instPrincipalBundleCircleFiber`): its trivializations are those of
  Tau Ceti's principal `unitary (ℂ →L[ℂ] ℂ)`-bundle structure
  (`TauCeti.OrthonormalFrameBundle.instPrincipalBundleFiber`) followed by that isomorphism
  (`SymplecticGeometry.Bundle.circleTrivialization`).

The rank-one condition is the instance `Fact (Module.finrank ℂ F = 1)`.

## Main definitions

* `SymplecticGeometry.Bundle.unitaryCircleEquiv : unitary (ℂ →L[ℂ] ℂ) ≃ₜ* Circle`.
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

/-- A fibre of a complex vector bundle has the dimension of the model fibre. -/
private theorem finrank_fiber (x : B) : finrank ℂ (E x) = finrank ℂ F :=
  ((trivializationAt F E x).continuousLinearEquivAt ℂ x
    (mem_baseSet_trivializationAt F E x)).toLinearEquiv.finrank_eq

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
    ((finrank_fiber (F := F) (E := E) x).trans Fact.out) w
  have hc : ‖c‖ = 1 := by simpa [norm_smul, show ‖u‖ = 1 from hu] using hw
  exact ⟨⟨c, mem_sphere_zero_iff_norm.2 hc⟩, rfl⟩

end Action

/-! ### The structure groups -/

/-- The unitary group of `ℂ →L[ℂ] ℂ`, with the operator-norm topology, is isomorphic as a
topological group to `Circle`: a unitary `u` goes to `u 1`. -/
def unitaryCircleEquiv : unitary (ℂ →L[ℂ] ℂ) ≃ₜ* Circle :=
  (Unitary.continuousLinearMapSelfEquiv ℂ).trans circleEquivUnitary.symm

theorem unitaryCircleEquiv_def :
    unitaryCircleEquiv = (Unitary.continuousLinearMapSelfEquiv ℂ).trans circleEquivUnitary.symm :=
  (rfl)

@[simp]
theorem coe_unitaryCircleEquiv_apply (u : unitary (ℂ →L[ℂ] ℂ)) :
    (unitaryCircleEquiv u : ℂ) = (u : ℂ →L[ℂ] ℂ) 1 := by
  rw [unitaryCircleEquiv_def, ContinuousMulEquiv.trans_apply, coe_circleEquivUnitary_symm,
    Unitary.coe_continuousLinearMapSelfEquiv_apply]

@[simp]
theorem unitaryCircleEquiv_symm_apply (z : Circle) (v : ℂ) :
    ((unitaryCircleEquiv.symm z : unitary (ℂ →L[ℂ] ℂ)) : ℂ →L[ℂ] ℂ) v = (z : ℂ) * v := by
  rw [unitaryCircleEquiv_def, ContinuousMulEquiv.symm_trans_apply,
    Unitary.continuousLinearMapSelfEquiv_symm_apply, ContinuousMulEquiv.symm_symm,
    coe_circleEquivUnitary]

/-! ### Unitary frames of a line bundle as unit vectors -/

section Homeomorph

variable {B F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [TopologicalSpace B]
  {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℂ F E]
  [Fact (finrank ℂ F = 1)]

/-- The unitary frame `z ↦ z • v` of a complex inner product space `W` of dimension one, for a
unit vector `v`. -/
private def frameOfUnit {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (h : finrank ℂ W = 1) {v : W} (hv : ‖v‖ = 1) : ℂ ≃ₗᵢ[ℂ] W :=
  haveI : FiniteDimensional ℂ W := Module.finite_of_finrank_eq_succ h
  (LinearIsometry.toSpanSingleton ℂ W hv).toLinearIsometryEquiv (by rw [finrank_self, h])

private theorem frameOfUnit_apply {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (h : finrank ℂ W = 1) {v : W} (hv : ‖v‖ = 1) (z : ℂ) : frameOfUnit h hv z = z • v :=
  LinearIsometry.toSpanSingleton_apply hv z

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
  invFun p := ⟨p.val.proj, .ofFrame
    (frameOfUnit ((finrank_fiber (F := F) _).trans Fact.out) p.property)⟩
  left_inv φ := by
    refine TotalSpace.ext rfl (heq_of_eq (Fiber.ext (LinearIsometryEquiv.ext fun z ↦ ?_)))
    rw [Fiber.frame_ofFrame, frameOfUnit_apply, ← frame_apply_eq_smul]
  right_inv p := Subtype.ext <| congrArg (TotalSpace.mk p.val.proj) <| by
    rw [Fiber.frame_ofFrame, frameOfUnit_apply, one_smul]
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
        (⟨p.val.proj, frameOfUnit ((finrank_fiber (F := F) _).trans Fact.out) p.property⟩ :
          OrthonormalFrameBundle ℂ F E ℂ) :=
      continuous_iff.2 fun z ↦ by
        simpa only [frameOfUnit_apply] using
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
  TotalSpace.mk_inj.2 (frameOfUnit_apply ((finrank_fiber (F := F) _).trans Fact.out) p.property z)

/-- `circleBundleHomeomorph` turns the right action of `unitary (ℂ →L[ℂ] ℂ)` on frames into the
action of `Circle` on unit vectors, along `unitaryCircleEquiv`. -/
theorem circleBundleHomeomorph_smul (u : unitary (ℂ →L[ℂ] ℂ)) {x : B} (φ : Fiber ℂ F E ℂ x) :
    circleBundleHomeomorph (⟨x, op u • φ⟩ : TotalSpace (unitary (ℂ →L[ℂ] ℂ)) (Fiber ℂ F E ℂ)) =
      unitaryCircleEquiv u • circleBundleHomeomorph ⟨x, φ⟩ := by
  refine Subtype.ext (congrArg (TotalSpace.mk x) ?_)
  change φ.frame ((u : ℂ →L[ℂ] ℂ) 1) = (unitaryCircleEquiv u : ℂ) • φ.frame 1
  rw [coe_unitaryCircleEquiv_apply, frame_apply_eq_smul]

end Homeomorph

/-! ### The unitary frame bundle as a principal `Circle`-bundle -/

section Principal

variable {B F : Type*} {E : B → Type*} [∀ x, NormedAddCommGroup (E x)]
  [∀ x, InnerProductSpace ℂ (E x)]

/-- `Circle` acts on the right on the unitary frames of a fibre, through `unitaryCircleEquiv`:
`z` precomposes a frame with multiplication by `z`. -/
instance instMulActionCircleFiber (x : B) : MulAction Circleᵐᵒᵖ (Fiber ℂ F E ℂ x) :=
  MulAction.compHom _ (MulEquiv.op unitaryCircleEquiv.symm.toMulEquiv).toMonoidHom

theorem op_circle_smul_eq {x : B} (z : Circle) (φ : Fiber ℂ F E ℂ x) :
    op z • φ = op (unitaryCircleEquiv.symm z) • φ :=
  (rfl)

/-- The action of `z : Circle` precomposes a frame with multiplication by `z`. -/
@[simp]
theorem frame_op_circle_smul_apply {x : B} (z : Circle) (φ : Fiber ℂ F E ℂ x) (v : ℂ) :
    (op z • φ).frame v = φ.frame ((z : ℂ) * v) := by
  rw [op_circle_smul_eq, Fiber.frame_smul_apply, unop_op, unitaryCircleEquiv_symm_apply]

/-- The total space of the unitary frame bundle, as a bundle with fibre `Circle`, is the total
space with fibre `unitary (ℂ →L[ℂ] ℂ)`: both are the pairs of a point and a frame. -/
def totalSpaceCircleEquiv :
    TotalSpace Circle (Fiber ℂ F E ℂ) ≃ TotalSpace (unitary (ℂ →L[ℂ] ℂ)) (Fiber ℂ F E ℂ) where
  toFun p := ⟨p.proj, p.snd⟩
  invFun p := ⟨p.proj, p.snd⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem totalSpaceCircleEquiv_apply (p : TotalSpace Circle (Fiber ℂ F E ℂ)) :
    totalSpaceCircleEquiv p = ⟨p.proj, p.snd⟩ :=
  (rfl)

@[simp]
theorem totalSpaceCircleEquiv_symm_apply
    (p : TotalSpace (unitary (ℂ →L[ℂ] ℂ)) (Fiber ℂ F E ℂ)) :
    totalSpaceCircleEquiv.symm p = (⟨p.proj, p.snd⟩ : TotalSpace Circle (Fiber ℂ F E ℂ)) :=
  (rfl)

variable [TopologicalSpace (TotalSpace F E)]

/-- The topology on the total space of the unitary frame bundle with fibre `Circle` that makes
`totalSpaceCircleEquiv` a homeomorphism. -/
instance instTopologicalSpaceTotalSpaceCircleFiber :
    TopologicalSpace (TotalSpace Circle (Fiber ℂ F E ℂ)) :=
  .induced totalSpaceCircleEquiv inferInstance

/-- `totalSpaceCircleEquiv` as a homeomorphism. -/
def totalSpaceCircleHomeomorph :
    TotalSpace Circle (Fiber ℂ F E ℂ) ≃ₜ TotalSpace (unitary (ℂ →L[ℂ] ℂ)) (Fiber ℂ F E ℂ) :=
  totalSpaceCircleEquiv.toHomeomorphOfIsInducing ⟨rfl⟩

@[simp]
theorem coe_totalSpaceCircleHomeomorph :
    ⇑(totalSpaceCircleHomeomorph (F := F) (E := E)) = totalSpaceCircleEquiv :=
  (rfl)

@[simp]
theorem coe_totalSpaceCircleHomeomorph_symm :
    ⇑(totalSpaceCircleHomeomorph (F := F) (E := E)).symm = totalSpaceCircleEquiv.symm :=
  (rfl)

variable [TopologicalSpace B]

/-- A trivialization of the unitary frame bundle of a line bundle, read with fibre `Circle`
through `unitaryCircleEquiv`. -/
def circleTrivialization
    (t : Trivialization (unitary (ℂ →L[ℂ] ℂ)) (π (unitary (ℂ →L[ℂ] ℂ)) (Fiber ℂ F E ℂ))) :
    Trivialization Circle (π Circle (Fiber ℂ F E ℂ)) :=
  (t.compHomeomorph totalSpaceCircleHomeomorph).transFiberHomeomorph
    unitaryCircleEquiv.toHomeomorph

variable
  (t : Trivialization (unitary (ℂ →L[ℂ] ℂ)) (π (unitary (ℂ →L[ℂ] ℂ)) (Fiber ℂ F E ℂ)))

@[simp]
theorem circleTrivialization_apply (p : TotalSpace Circle (Fiber ℂ F E ℂ)) :
    circleTrivialization t p =
      ((t ⟨p.proj, p.snd⟩).1, unitaryCircleEquiv (t ⟨p.proj, p.snd⟩).2) :=
  (rfl)

@[simp]
theorem circleTrivialization_symm_apply (q : B × Circle) :
    (circleTrivialization t).toOpenPartialHomeomorph.symm q =
      totalSpaceCircleEquiv.symm
        (t.toOpenPartialHomeomorph.symm (q.1, unitaryCircleEquiv.symm q.2)) :=
  (rfl)

@[simp]
theorem baseSet_circleTrivialization : (circleTrivialization t).baseSet = t.baseSet :=
  (rfl)

/-- An equivariant trivialization of the unitary frame bundle stays equivariant when read with
fibre `Circle`. -/
instance isEquivariant_circleTrivialization [t.IsEquivariant] :
    (circleTrivialization t).IsEquivariant :=
  ⟨fun b hb φ z ↦ by
    simp only [circleTrivialization_apply, op_circle_smul_eq, t.snd_apply_smul hb, map_mul,
      ContinuousMulEquiv.apply_symm_apply]⟩

variable [NormedAddCommGroup F] [NormedSpace ℂ F] [FiberBundle F E] [VectorBundle ℂ F E]
  [ContinuousFiberNorm F E] [Fact (finrank ℂ F = 1)]

local instance : FiniteDimensional ℂ F :=
  Module.finite_of_finrank_eq_succ (Fact.out (p := finrank ℂ F = 1))

local instance : Fact (finrank ℂ ℂ = finrank ℂ F) :=
  ⟨by rw [finrank_self, Fact.out (p := finrank ℂ F = 1)]⟩

/-- The unitary frames of a complex line bundle form a fibre bundle with fibre `Circle`, whose
atlas consists of the trivializations of the atlas of Tau Ceti's frame bundle, read through
`unitaryCircleEquiv`. -/
instance instFiberBundleCircleFiber : FiberBundle Circle (Fiber ℂ F E ℂ) where
  totalSpaceMk_isInducing' b := by
    have h := totalSpaceCircleHomeomorph.symm.isInducing.comp
      (FiberBundle.totalSpaceMk_isInducing (unitary (ℂ →L[ℂ] ℂ)) (Fiber ℂ F E ℂ) b)
    rwa [coe_totalSpaceCircleHomeomorph_symm] at h
  trivializationAtlas' :=
    {t | ∃ (e : Trivialization (unitary (ℂ →L[ℂ] ℂ)) (π (unitary (ℂ →L[ℂ] ℂ)) (Fiber ℂ F E ℂ)))
      (_ : MemTrivializationAtlas e), t = circleTrivialization e}
  trivializationAt' x := circleTrivialization (trivializationAt _ (Fiber ℂ F E ℂ) x)
  mem_baseSet_trivializationAt' x := by
    rw [baseSet_circleTrivialization]
    exact mem_baseSet_trivializationAt (unitary (ℂ →L[ℂ] ℂ)) (Fiber ℂ F E ℂ) x
  trivialization_mem_atlas' x := ⟨_, inferInstance, rfl⟩

theorem trivializationAt_circleFiber (x : B) :
    trivializationAt Circle (Fiber ℂ F E ℂ) x =
      circleTrivialization (trivializationAt (unitary (ℂ →L[ℂ] ℂ)) (Fiber ℂ F E ℂ) x) :=
  rfl

instance memTrivializationAtlas_circleTrivialization [MemTrivializationAtlas t] :
    MemTrivializationAtlas (circleTrivialization t) :=
  ⟨⟨t, inferInstance, rfl⟩⟩

/-- **The unitary frames of a complex line bundle form a principal `Circle`-bundle**, `Circle`
acting on the right by precomposition with multiplication. -/
instance instPrincipalBundleCircleFiber : PrincipalBundle Circle (Fiber ℂ F E ℂ) where
  isEquivariant_trivialization' _ ht := by
    obtain ⟨e, _, rfl⟩ := ht.out
    infer_instance

end Principal

end SymplecticGeometry.Bundle

end
