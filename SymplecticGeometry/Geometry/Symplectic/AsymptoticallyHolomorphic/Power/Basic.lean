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
stands for the `k`-th tensor power of `L` (of its dual when `k < 0`); this file does not compare
the two. It is built as an associated bundle, and not as an iterated tensor product, so that its
model fibre is `ℂ` for every `k`.

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

The file states the instances that Tau Ceti's files ask of the model fibre, and checks the
structures of the bundle by `example`s.

## Main definitions

* `SymplecticGeometry.PowerModel k`: `ℂ` with the circle acting by `g • z = g ^ k * z`.
* `SymplecticGeometry.PowerBundle P k`: the complex line bundle `P ×_{Circle} ℂ` of weight `k`.

## Main results

* `SymplecticGeometry.PowerBundle.mk_op_smul`: `[p · g, z] = (g : ℂ) ^ k • [p, z]`.
* `SymplecticGeometry.PowerBundle.finrank_eq_one`: the fibres are complex lines.
* `SymplecticGeometry.PowerBundle.contMDiffVectorBundle`: for a smooth principal bundle, a smooth
  vector bundle.

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

variable (P k) in
/-- The fibres of `PowerBundle P k` are complex lines. -/
theorem finrank_eq_one (b : B) : finrank ℂ (PowerBundle P k b) = 1 := by
  obtain ⟨p, -, -⟩ := AssociatedBundle.exists_mk (0 : PowerBundle P k b)
  rw [AssociatedBundle.finrank_eq ℂ Circle p, PowerModel.finrank_eq_one]

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

end PowerBundle

end SymplecticGeometry

end
