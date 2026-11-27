/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.Geometry.Manifold.VectorBundle.Associated.Metric
public import SymplecticGeometry.Topology.VectorBundle.Associated.Basic
public import TauCeti.Topology.VectorBundle.TensorProduct.Basic
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Hermitian.CircleBundle
public import TauCeti.Topology.VectorBundle.Orientation.Complex.EulerClass
import SymplecticGeometry.Topology.VectorBundle.Orientation.Complex.Tensor

/-!
# Powers of a principal circle bundle

For an integer `k`, the circle acts on `ℂ` with weight `k`, by `g • z = g ^ k * z`. This file
gives this action a type of its own, `SymplecticGeometry.PowerModel k`, a copy of `ℂ` with its
normed, inner product and module structures, and for a principal `Circle`-bundle `P → B` it
defines the complex line bundle `SymplecticGeometry.PowerBundle P k`, Tau Ceti's associated bundle
`TauCeti.AssociatedBundle Circle P (PowerModel k)`. Its point `[p, z]` satisfies
`[p · g, z] = [p, g ^ k z]` (`SymplecticGeometry.PowerBundle.mk_op_smul`).

When `P` is the bundle of unitary frames of a Hermitian line bundle `L` (the principal
`Circle`-bundle of `Geometry/Manifold/VectorBundle/Hermitian/CircleBundle.lean`), `PowerBundle P k`
stands for the `k`-th tensor power of `L` (of its dual when `k < 0`). For `k = 1` the file
identifies it with `L`: `SymplecticGeometry.PowerBundle.powerOneEquiv` sends the class `[φ, z]` of
a unitary frame `φ` to `φ z`, fibre by fibre, and it and its inverse are continuous on total
spaces, in the form that Tau Ceti's `TauCeti.complexEulerClass_eq_of_fiberwise` takes.
`PowerBundle P k` is built as an associated bundle, and not as an iterated tensor product, so
that its model fibre is `ℂ` for every `k`.

A separate type for each `k` is needed because the instance arguments of Tau Ceti's construction
fix the action of `Circle` on the model fibre. Through its `ℂ`-module structure the type also has
Mathlib's action of weight one (`Circle.instSMul`, `Circle.instMulAction`,
`Circle.instDistribMulAction`); the instances of weight `k` here have higher priority, and
`PowerModel.smul_def` rewrites them as multiplication by `(g : ℂ) ^ k`. The model instances
follow those of Tau Ceti's `TauCeti.SpinCStructure.DeterminantModel`, with the action built by
`DistribMulAction.compHom` as there, and the proof of
`SymplecticGeometry.PowerModel.instContMDiffSMul` follows that of Tau Ceti's
`Circle.instContMDiffSMul`. The bundle declarations adapt Tau Ceti's declarations for the
determinant line of a `Spinᶜ` structure: `SymplecticGeometry.PowerBundle` adapts
`TauCeti.SpinCStructure.determinantLine`, `SymplecticGeometry.PowerBundle.finrank_eq_one` adapts
`TauCeti.SpinCStructure.finrank_determinantLine`, and `SymplecticGeometry.PowerBundle.mk_op_smul`
adapts `TauCeti.SpinCStructure.mk_ofCircle_smul_determinantLine`.
`SymplecticGeometry.PowerBundle.powerOneEquiv`, `SymplecticGeometry.PowerBundle.powerOneEquiv_mk`
and `SymplecticGeometry.PowerBundle.powerOneEquiv_symm_apply` adapt Tau Ceti's
`TauCeti.OrthonormalFrameBundle.associatedLinearIsometryEquiv`,
`TauCeti.OrthonormalFrameBundle.associatedLinearIsometryEquiv_mk` and
`TauCeti.OrthonormalFrameBundle.associatedLinearIsometryEquiv_symm_apply`, from the group
`unitary (ℂ →L[ℂ] ℂ)` to `Circle`, and `SymplecticGeometry.PowerBundle.continuous_powerOneEquiv`
follows the continuity proof of `TauCeti.OrthonormalFrameBundle.associatedBundleHomeomorph`; the
continuity of the inverse comes from Tau Ceti's `TauCeti.continuous_bundle_symm`.

The structures of `PowerBundle P k` come from Tau Ceti, except the compatibility of the real and
complex scalars on the fibres, `TauCeti.AssociatedBundle.instIsScalarTower` of
`SymplecticGeometry/Topology/VectorBundle/Associated/Basic.lean`:

* complex (and real) vector bundle, from `Topology/VectorBundle/Associated/Basic.lean`;
* fibrewise norms, real and Hermitian inner products and the continuity of the norm, from
  `Topology/VectorBundle/Associated/Metric.lean`, since the action is isometric;
* for a smooth principal bundle over a real manifold, the smooth vector bundle structure
  (`SymplecticGeometry.PowerBundle.contMDiffVectorBundle`) and the smoothness of the metric, from
  `Geometry/Manifold/VectorBundle/Associated/` (`Basic.lean` and `Metric.lean`), since the action
  is smooth (`SymplecticGeometry.PowerModel.instContMDiffSMul`).

The weights add under tensor products: `SymplecticGeometry.powerAddEquiv` identifies each fibre
of `PowerBundle P (k + l)` with the tensor product of the fibres of `PowerBundle P k` and
`PowerBundle P l`, by `[p, z * w] ↦ [p, z] ⊗ [p, w]`, and is continuous on total spaces into Tau
Ceti's tensor product bundle (`Topology/VectorBundle/TensorProduct/Basic.lean`). The continuity
is checked on `P × ℂ`, of which the total space is a quotient
(`TauCeti.AssociatedBundle.isOpenQuotientMap_totalSpaceMk_mk`). The statement has the form that
`TauCeti.complexEulerClass_eq_of_fiberwise` asks for; the tensor product fibres carry their module
topology, and the real structure that instance search finds on them is the one of
`TauCeti.complexEulerClass_tensorProduct`.

Over a compact normal base, the two identifications compute the Euler classes
(`TauCeti.complexEulerClass`). Through `powerAddEquiv`, Tau Ceti's
`TauCeti.complexEulerClass_eq_of_fiberwise` and the library's
`TauCeti.complexEulerClass_tensorProduct` (with finite trivializing covers from compactness), the
class of `PowerBundle P k` is additive in `k`, so it is `k` times the class of `PowerBundle P 1`;
through `powerOneEquiv`, for the unitary frames of a Hermitian line bundle `V`, that is `k` times
the class of `V` (`SymplecticGeometry.PowerBundle.complexEulerClass_power`).

The file states the instances that Tau Ceti's files ask of the model fibre, and checks the
structures of the bundle by `example`s.

## Main definitions

* `SymplecticGeometry.PowerModel k`: `ℂ` with the circle acting by `g • z = g ^ k * z`.
* `SymplecticGeometry.PowerBundle P k`: the complex line bundle `P ×_{Circle} ℂ` of weight `k`.
* `SymplecticGeometry.powerAddEquiv k l`: the fibrewise isomorphism from
  `PowerBundle P (k + l)` to `PowerBundle P k ⊗ PowerBundle P l`.
* `SymplecticGeometry.PowerBundle.powerOneEquiv`: for the unitary frames of a Hermitian line bundle
  `V`, the fibrewise identification of the bundle of weight one with `V`.

## Main results

* `SymplecticGeometry.PowerBundle.mk_op_smul`: `[p · g, z] = (g : ℂ) ^ k • [p, z]`.
* `SymplecticGeometry.PowerBundle.mk_eq_smul_mk`: `[p, x] = (g ^ k * x) • [p₀, 1]` for `p = p₀ · g`.
* `SymplecticGeometry.PowerBundle.finrank_eq_one`: the fibres are complex lines.
* `SymplecticGeometry.PowerBundle.contMDiffVectorBundle`: for a smooth principal bundle, a smooth
  vector bundle.
* `SymplecticGeometry.powerAddEquiv_mk`: `[p, z * w] ↦ [p, z] ⊗ [p, w]`.
* `SymplecticGeometry.continuous_powerAddEquiv`: `powerAddEquiv` is continuous on total spaces.
* `SymplecticGeometry.PowerBundle.continuous_powerOneEquiv`,
  `SymplecticGeometry.PowerBundle.continuous_powerOneEquiv_symm`: `powerOneEquiv` and its inverse
  are continuous on total spaces.
* `SymplecticGeometry.PowerBundle.complexEulerClass_add`,
  `SymplecticGeometry.PowerBundle.complexEulerClass_eq_zsmul`: over a compact normal base,
  `e(PowerBundle P (k + l)) = e(PowerBundle P k) + e(PowerBundle P l)`, and
  `e(PowerBundle P k) = k • e(PowerBundle P 1)`.
* `SymplecticGeometry.PowerBundle.complexEulerClass_power`: for the unitary frames of a Hermitian
  line bundle `V` over a compact normal base, the Euler class of the bundle of weight `k` is
  `k • e(V)`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §7.4
  (the powers of the prequantum line bundle).
* [S. K. Donaldson, *Symplectic submanifolds and almost-complex geometry*][Donaldson1996].
* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, volume I, Chapter I, §5
  (associated bundles).
-/

public section

noncomputable section

open Bundle MulOpposite Module TauCeti
open scoped Manifold ContDiff InnerProductSpace

namespace SymplecticGeometry

/-! ### The model fibre -/

/-- The **model fibre of weight `k`**: a copy of `ℂ`, on which the circle acts by
`g • z = g ^ k * z`. -/
@[expose] def PowerModel (_k : ℤ) : Type := ℂ

namespace PowerModel

variable {k : ℤ}

instance instNormedAddCommGroup : NormedAddCommGroup (PowerModel k) :=
  inferInstanceAs (NormedAddCommGroup ℂ)

instance instInnerProductSpace : InnerProductSpace ℂ (PowerModel k) :=
  inferInstanceAs (InnerProductSpace ℂ ℂ)

instance instInnerProductSpaceReal : InnerProductSpace ℝ (PowerModel k) :=
  inferInstanceAs (InnerProductSpace ℝ ℂ)

instance instIsScalarTower : IsScalarTower ℝ ℂ (PowerModel k) :=
  inferInstanceAs (IsScalarTower ℝ ℂ ℂ)

instance instFiniteDimensional : FiniteDimensional ℂ (PowerModel k) :=
  inferInstanceAs (FiniteDimensional ℂ ℂ)

instance instFiniteDimensionalReal : FiniteDimensional ℝ (PowerModel k) :=
  inferInstanceAs (FiniteDimensional ℝ ℂ)

/-- The model fibre of weight `k` as `ℂ`. -/
def toComplex : PowerModel k ≃ₗᵢ[ℂ] ℂ := LinearIsometryEquiv.refl ℂ ℂ

variable (k) in
/-- The model fibre has complex dimension one. -/
theorem finrank_eq_one : finrank ℂ (PowerModel k) = 1 :=
  (toComplex (k := k)).finrank_eq.trans (finrank_self ℂ)

/-- The circle acts on the model fibre of weight `k` by multiplication by `g ^ k`, through the
homomorphism `g ↦ (g : ℂ) ^ k` and the `ℂ`-module structure. -/
instance (priority := high) instDistribMulAction : DistribMulAction Circle (PowerModel k) :=
  DistribMulAction.compHom (PowerModel k) (Circle.coeHom.comp (zpowGroupHom k))

/-- The action of weight `k`, rather than the action through the `ℂ`-module structure. -/
instance (priority := high) instSMul : SMul Circle (PowerModel k) :=
  instDistribMulAction.toSMul

/-- The action of weight `k`, rather than the action through the `ℂ`-module structure. -/
instance (priority := high) instMulAction : MulAction Circle (PowerModel k) :=
  instDistribMulAction.toMulAction

/-- The action of `g` on the model fibre of weight `k` is scalar multiplication by `g ^ k`. -/
theorem smul_def (g : Circle) (w : PowerModel k) : g • w = ((g : ℂ) ^ k) • w :=
  (rfl)

/-- `g` acts on the model fibre of weight `k` by multiplication by `g ^ k`. -/
@[simp]
theorem toComplex_smul (g : Circle) (w : PowerModel k) :
    toComplex (g • w) = (g : ℂ) ^ k * toComplex w := by
  rw [smul_def, map_smul, smul_eq_mul]

/-- The real inner product of the model fibre is the real part of its Hermitian inner product. -/
theorem real_inner_eq_re_inner (u w : PowerModel k) : inner ℝ u w = (inner ℂ u w).re :=
  _root_.real_inner_eq_re_inner ℂ u w

instance instSMulCommClass : SMulCommClass Circle ℂ (PowerModel k) where
  smul_comm g c w := smul_comm ((g : ℂ) ^ k) c w

instance instSMulCommClassReal : SMulCommClass Circle ℝ (PowerModel k) where
  smul_comm g c w := smul_comm ((g : ℂ) ^ k) c w

instance instContinuousSMul : ContinuousSMul Circle (PowerModel k) where
  continuous_smul := by
    have h : Continuous fun p : Circle × PowerModel k ↦ ((p.1 ^ k : Circle) : ℂ) • p.2 :=
      (continuous_subtypeVal.comp ((continuous_zpow (G := Circle) k).comp continuous_fst)).smul
        continuous_snd
    exact h.congr fun p ↦ by rw [Circle.coe_zpow, smul_def]

instance instIsIsometricSMul : IsIsometricSMul Circle (PowerModel k) where
  isometry_smul g := AddMonoidHomClass.isometry_of_norm (DistribSMul.toAddMonoidHom _ g)
    fun w ↦ by
      rw [DistribSMul.toAddMonoidHom_apply, smul_def, norm_smul, norm_zpow, Circle.norm_coe,
        one_zpow, one_mul]

attribute [local instance] finrank_real_complex_fact'

/-- The circle acts smoothly on the model fibre of weight `k`. -/
instance instContMDiffSMul {n : ℕ∞ω} :
    ContMDiffSMul (𝓡 1) 𝓘(ℝ, PowerModel k) n Circle (PowerModel k) where
  contMDiff_smul := by
    -- The action is multiplication by the image of `g ^ k` in `ℂ`.
    have hsmul : ContDiff ℝ n fun p : ℂ × PowerModel k ↦ p.1 • p.2 :=
      contDiff_fst.smul contDiff_snd
    exact (hsmul.comp_contMDiff (((contMDiff_coe_sphere.comp
      (contMDiff_zpow (I := 𝓡 1) (G := Circle) k)).comp contMDiff_fst).prodMk_space
        contMDiff_snd)).congr
      fun p ↦ by
        rw [Function.comp_apply, smul_def]
        exact congrArg (· • p.2) (Circle.coe_zpow p.1 k).symm
end PowerModel

/-! ### The bundle of weight `k` -/

variable {B : Type*} [TopologicalSpace B] (P : B → Type*) [TopologicalSpace (TotalSpace Circle P)]
  [∀ b, TopologicalSpace (P b)] [FiberBundle Circle P] [∀ b, MulAction Circleᵐᵒᵖ (P b)]
  [PrincipalBundle Circle P]

/-- The **complex line bundle of weight `k`** of a principal `Circle`-bundle `P`: the associated
bundle `P ×_{Circle} ℂ` for the action `g • z = g ^ k * z`. -/
abbrev PowerBundle (k : ℤ) : B → Type _ :=
  AssociatedBundle Circle P (PowerModel k)

namespace PowerBundle

variable {P} {k : ℤ}

/-- **The circle acts with weight `k`**: `[p · g, z] = g ^ k • [p, z]`. -/
theorem mk_op_smul {b : B} (p : P b) (g : Circle) (z : PowerModel k) :
    AssociatedBundle.mk Circle (op g • p) z =
      ((g : ℂ) ^ k) • (AssociatedBundle.mk Circle p z : PowerBundle P k b) := by
  rw [AssociatedBundle.mk_smul, PowerModel.smul_def, AssociatedBundle.mk_smul_scalar]

/-- Every point `[p, x]` of a fibre of `PowerBundle P k` is a multiple of `[p₀, 1]`, for any point
`p₀` of the same fibre of `P`: the factor is `g ^ k * x`, where `g` is the division of `p`
by `p₀`, so that `p = p₀ · g`. -/
theorem mk_eq_smul_mk {b : B} (p₀ p : P b) (x : PowerModel k) :
    AssociatedBundle.mk Circle p x =
      (((PrincipalBundle.division Circle p₀ p : ℂ) ^ k * PowerModel.toComplex x) •
        AssociatedBundle.mk Circle p₀ (PowerModel.toComplex.symm 1) : PowerBundle P k b) := by
  conv_lhs => rw [← PrincipalBundle.smul_division (G := Circle) p₀ p]
  rw [mk_op_smul, mul_smul, ← AssociatedBundle.mk_smul_scalar p₀ (PowerModel.toComplex x)]
  congr 2
  apply PowerModel.toComplex.injective
  simp

variable (P k) in
/-- The fibres of `PowerBundle P k` are complex lines. -/
theorem finrank_eq_one (b : B) : finrank ℂ (PowerBundle P k b) = 1 := by
  rw [AssociatedBundle.finrank_eq ℂ Circle _ P b, PowerModel.finrank_eq_one]

/-! The vector bundle and metric structures of Tau Ceti apply. -/

example : VectorBundle ℂ (PowerModel k) (PowerBundle P k) := inferInstance

example : VectorBundle ℝ (PowerModel k) (PowerBundle P k) := inferInstance

example (b : B) : InnerProductSpace ℂ (PowerBundle P k b) := inferInstance

example (b : B) : InnerProductSpace ℝ (PowerBundle P k b) := inferInstance

example (b : B) : IsScalarTower ℝ ℂ (PowerBundle P k b) := inferInstance

example : ContinuousFiberNorm (PowerModel k) (PowerBundle P k) := inferInstance

example {b : B} (p : P b) (z w : PowerModel k) :
    ⟪(AssociatedBundle.mk Circle p z : PowerBundle P k b), AssociatedBundle.mk Circle p w⟫_ℂ =
      ⟪z, w⟫_ℂ :=
  AssociatedBundle.inner_mk p z w

example {b : B} (p : P b) (z : PowerModel k) :
    ‖(AssociatedBundle.mk Circle p z : PowerBundle P k b)‖ = ‖z‖ :=
  AssociatedBundle.norm_mk p z

/-! ### Smooth structure -/

section Smooth

attribute [local instance] finrank_real_complex_fact'

variable {n : ℕ∞ω} {EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} [ChartedSpace HB B]
  [ContMDiffFiberBundle n Circle P IB (𝓡 1)]

/-- For a smooth principal `Circle`-bundle, `PowerBundle P k` is a smooth real vector bundle. -/
instance contMDiffVectorBundle :
    ContMDiffVectorBundle n (PowerModel k) (PowerBundle P k) IB :=
  AssociatedBundle.contMDiffVectorBundle (𝓡 1)

example : IsContMDiffRiemannianBundle IB n (PowerModel k) (PowerBundle P k) := inferInstance

end Smooth

/-! ### The bundle of weight one of a Hermitian line bundle -/

section PowerOne

open OrthonormalFrameBundle

variable {B F : Type*} [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace ℂ F]
  [Fact (finrank ℂ F = 1)] {V : B → Type*} [∀ b, NormedAddCommGroup (V b)]
  [∀ b, InnerProductSpace ℂ (V b)] [TopologicalSpace (TotalSpace F V)] [FiberBundle F V]
  [VectorBundle ℂ F V] [ContinuousFiberNorm F V]

variable (F V) in
/-- For a Hermitian line bundle `V` with its principal `Circle`-bundle of unitary frames, the
fibre at `b` of the bundle of weight one is identified with `V b`, complex linearly and
isometrically, by sending the class `[φ, z]` of a unitary frame `φ` to `φ z`
(`SymplecticGeometry.PowerBundle.powerOneEquiv_mk`). -/
def powerOneEquiv (b : B) : PowerBundle (Fiber ℂ F V ℂ) 1 b ≃ₗᵢ[ℂ] V b :=
  let p₀ := (FiberBundle.homeomorphAt Circle (Fiber ℂ F V ℂ) b).symm 1
  (AssociatedBundle.mkLinearIsometryEquiv ℂ Circle p₀).symm.trans
    (PowerModel.toComplex.trans p₀.frame)

/-- `powerOneEquiv` sends the class `[φ, z]` to `φ z`. -/
@[simp]
theorem powerOneEquiv_mk {b : B} (φ : Fiber ℂ F V ℂ b) (z : PowerModel 1) :
    powerOneEquiv F V b (AssociatedBundle.mk Circle φ z) = φ.frame (PowerModel.toComplex z) := by
  rw [powerOneEquiv, LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.trans_apply,
    AssociatedBundle.mkLinearIsometryEquiv_symm_apply_mk, PowerModel.toComplex_smul, zpow_one,
    ← Fiber.frame_op_circle_smul_apply, PrincipalBundle.smul_division]

/-- The inverse of `powerOneEquiv` writes `w : V b` in a unitary frame `φ` as `[φ, φ⁻¹ w]`. -/
theorem powerOneEquiv_symm_apply {b : B} (φ : Fiber ℂ F V ℂ b) (w : V b) :
    (powerOneEquiv F V b).symm w =
      AssociatedBundle.mk Circle φ (PowerModel.toComplex.symm (φ.frame.symm w)) :=
  (powerOneEquiv F V b).injective <| by simp

/-- The map of total spaces induced by `powerOneEquiv` is continuous. -/
theorem continuous_powerOneEquiv :
    Continuous fun v : TotalSpace (PowerModel 1) (PowerBundle (Fiber ℂ F V ℂ) 1) ↦
      TotalSpace.mk' F v.proj (powerOneEquiv F V v.proj v.snd) := by
  rw [(AssociatedBundle.isOpenQuotientMap_totalSpaceMk_mk Circle (Fiber ℂ F V ℂ)
    (PowerModel 1)).isQuotientMap.continuous_iff]
  refine (continuous_totalSpace_frame_apply.comp
    (Bundle.isInducing_totalSpaceMk'_circleFiber.continuous.prodMap
      PowerModel.toComplex.continuous)).congr fun ⟨⟨b, φ⟩, z⟩ ↦ ?_
  rw [Function.comp_apply, Prod.map_apply]
  simp

/-- The map of total spaces induced by the inverse of `powerOneEquiv` is continuous. -/
theorem continuous_powerOneEquiv_symm :
    Continuous fun v : TotalSpace F V ↦
      TotalSpace.mk' (PowerModel 1) (E := PowerBundle (Fiber ℂ F V ℂ) 1) v.proj
        ((powerOneEquiv F V v.proj).symm v.snd) :=
  continuous_bundle_symm (fun b ↦ (powerOneEquiv F V b).toContinuousLinearEquiv)
    continuous_powerOneEquiv

end PowerOne

end PowerBundle

/-! ### Tensor products of the bundles of weight `k` -/

open scoped TensorProduct TauCeti.ModuleTopology

/-- **The bundle of weight `k + l` is the tensor product of those of weights `k` and `l`.** Over
each point `b`, the complex linear isomorphism from `PowerBundle P (k + l) b` to
`PowerBundle P k b ⊗[ℂ] PowerBundle P l b` that sends `[p, z * w]` to `[p, z] ⊗ [p, w]`
(`SymplecticGeometry.powerAddEquiv_mk`). The tensor product carries the topology of Tau Ceti's
tensor product bundle, its module topology. -/
def powerAddEquiv (k l : ℤ) (b : B) :
    PowerBundle P (k + l) b ≃L[ℂ] PowerBundle P k b ⊗[ℂ] PowerBundle P l b :=
  -- A point of the fibre of `P` over `b`, through which both sides are identified with `ℂ`.
  let p := (FiberBundle.homeomorphAt Circle P b).symm 1
  haveI := VectorBundle.finiteDimensional ℂ (PowerModel (k + l)) (PowerBundle P (k + l)) b
  haveI := FiberBundle.t2Space (PowerModel (k + l)) (PowerBundle P (k + l)) b
  letI : IsModuleTopology ℂ (PowerBundle P (k + l) b) := isModuleTopologyOfFiniteDimensional
  LinearEquiv.toContinuousLinearEquivOfIsModuleTopology <|
    (AssociatedBundle.mkContinuousLinearEquiv ℂ Circle p).symm.toLinearEquiv ≪≫ₗ
      PowerModel.toComplex.toLinearEquiv ≪≫ₗ (TensorProduct.lid ℂ ℂ).symm ≪≫ₗ
      TensorProduct.congr
        (PowerModel.toComplex.symm.toLinearEquiv ≪≫ₗ
          (AssociatedBundle.mkContinuousLinearEquiv ℂ Circle p).toLinearEquiv)
        (PowerModel.toComplex.symm.toLinearEquiv ≪≫ₗ
          (AssociatedBundle.mkContinuousLinearEquiv ℂ Circle p).toLinearEquiv)

variable {P} in
/-- `powerAddEquiv` sends `[p, z * w]` to `[p, z] ⊗ [p, w]`, for every point `p` of the fibre
of `P`. -/
@[simp]
theorem powerAddEquiv_mk {k l : ℤ} {b : B} (p : P b) (z : PowerModel k) (w : PowerModel l) :
    powerAddEquiv P k l b (AssociatedBundle.mk Circle p
        (PowerModel.toComplex.symm (PowerModel.toComplex z * PowerModel.toComplex w))) =
      AssociatedBundle.mk Circle p z ⊗ₜ[ℂ] AssociatedBundle.mk Circle p w := by
  -- Write each class as a multiple of the class of the point that defines `powerAddEquiv`.
  simp only [PowerBundle.mk_eq_smul_mk ((FiberBundle.homeomorphAt Circle P b).symm 1) p]
  rw [TensorProduct.smul_tmul_smul, map_smul]
  congr 1
  · rw [LinearIsometryEquiv.apply_symm_apply, zpow_add₀ (Circle.coe_ne_zero _)]
    ring
  · simp [powerAddEquiv]

/-- **`powerAddEquiv` is continuous on total spaces**: as a map from the total space of
`PowerBundle P (k + l)` to that of Tau Ceti's tensor product bundle of `PowerBundle P k` and
`PowerBundle P l`, with model fibre `TauCeti.ProjectiveTensor ℂ (PowerModel k) (PowerModel l)`.
This is the hypothesis of `TauCeti.complexEulerClass_eq_of_fiberwise`. -/
theorem continuous_powerAddEquiv (k l : ℤ) :
    Continuous fun v : TotalSpace (PowerModel (k + l)) (PowerBundle P (k + l)) ↦
      TotalSpace.mk' (ProjectiveTensor ℂ (PowerModel k) (PowerModel l))
        (E := fun b ↦ PowerBundle P k b ⊗[ℂ] PowerBundle P l b) v.proj
        (powerAddEquiv P k l v.proj v.snd) := by
  -- The total space of `PowerBundle P (k + l)` is a quotient of `P × ℂ`, on which the map is
  -- `(p, z) ↦ [p, z] ⊗ [p, 1]`.
  refine (AssociatedBundle.isOpenQuotientMap_totalSpaceMk_mk Circle P
    (PowerModel (k + l))).isQuotientMap.continuous_iff.2 ?_
  have hp : Continuous fun x : TotalSpace Circle P × PowerModel (k + l) ↦
      TotalSpace.mk' Circle x.1.proj x.1.snd := continuous_fst
  refine (Continuous.tmul_section (hp.totalSpaceMk_associatedBundleMk
    ((PowerModel.toComplex.symm.continuous.comp PowerModel.toComplex.continuous).comp
      continuous_snd))
    (hp.totalSpaceMk_associatedBundleMk
      (continuous_const (y := (PowerModel.toComplex.symm 1 : PowerModel l))))).congr fun x ↦ ?_
  rw [Function.comp_apply, Function.comp_apply, ← powerAddEquiv_mk]
  simp

/-! ### The Euler classes of the bundles of weight `k` -/

namespace PowerBundle

section EulerClass

variable {B : Type} [TopologicalSpace B] [NormalSpace B] [CompactSpace B]
  (P : B → Type) [TopologicalSpace (TotalSpace Circle P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle Circle P] [∀ b, MulAction Circleᵐᵒᵖ (P b)] [PrincipalBundle Circle P]

/-- **The Euler class is additive in the weight**: over a compact normal base, the Euler class of
`PowerBundle P (k + l)` is the sum of those of `PowerBundle P k` and `PowerBundle P l`. -/
theorem complexEulerClass_add (k l : ℤ) :
    complexEulerClass (r := 0) (PowerModel (k + l)) (PowerBundle P (k + l))
        (PowerModel.finrank_eq_one _) =
      complexEulerClass (r := 0) (PowerModel k) (PowerBundle P k) (PowerModel.finrank_eq_one _) +
        complexEulerClass (r := 0) (PowerModel l) (PowerBundle P l)
          (PowerModel.finrank_eq_one _) :=
  (complexEulerClass_eq_of_fiberwise _ _ (continuous_powerAddEquiv P k l)).trans
    (complexEulerClass_tensorProduct (PowerModel.finrank_eq_one k) (PowerModel.finrank_eq_one l)
      (.of_compactSpace ..) (.of_compactSpace ..))

/-- Over a compact normal base, the Euler class of `PowerBundle P k` is `k` times that of
`PowerBundle P 1`. -/
theorem complexEulerClass_eq_zsmul (k : ℤ) :
    complexEulerClass (r := 0) (PowerModel k) (PowerBundle P k) (PowerModel.finrank_eq_one _) =
      k • complexEulerClass (r := 0) (PowerModel 1) (PowerBundle P 1)
        (PowerModel.finrank_eq_one _) := by
  -- The Euler class, as a function of the weight, is an additive map from `ℤ`.
  let f : ℤ →+ _ := AddMonoidHom.mk' (fun k ↦ complexEulerClass (r := 0) (PowerModel k)
    (PowerBundle P k) (PowerModel.finrank_eq_one _)) (complexEulerClass_add P)
  simpa [f] using map_zsmul f k 1

end EulerClass

section PowerOneEulerClass

open OrthonormalFrameBundle

variable {B F : Type} [TopologicalSpace B] [NormalSpace B] [CompactSpace B]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [Fact (finrank ℂ F = 1)] {V : B → Type}
  [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℂ (V b)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℂ F V]
  [ContinuousFiberNorm F V]

/-- **The Euler class of a power of a Hermitian line bundle**: over a compact normal base, for
the principal `Circle`-bundle of unitary frames of a Hermitian line bundle `V`, the Euler class of
the bundle of weight `k` is `k` times that of `V`. -/
theorem complexEulerClass_power (k : ℤ) :
    complexEulerClass (r := 0) (PowerModel k) (PowerBundle (Fiber ℂ F V ℂ) k)
        (PowerModel.finrank_eq_one _) =
      k • complexEulerClass (r := 0) F V Fact.out := by
  rw [complexEulerClass_eq_zsmul, complexEulerClass_eq_of_fiberwise _ _
    (φ := fun b ↦ (powerOneEquiv F V b).toContinuousLinearEquiv) continuous_powerOneEquiv]

end PowerOneEulerClass

end PowerBundle

end SymplecticGeometry

end
