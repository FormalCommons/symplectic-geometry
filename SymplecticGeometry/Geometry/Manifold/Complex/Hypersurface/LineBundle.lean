/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Core.Section
public import TauCeti.Topology.VectorBundle.Hom
public import TauCeti.Topology.VectorBundle.TensorProduct.Basic

import TauCeti.Analysis.Calculus.ContDiffZPow

/-!
# The line bundle of a hypersurface

A hypersurface `D` of a complex manifold `X` is given here by local defining functions: an open
cover `U i` of `X` and holomorphic functions `f i` on `U i`, together with holomorphic, nowhere
vanishing functions `g i j` on `U i ∩ U j` with `f i = g i j * f j` there, satisfying the cocycle
identity `g i j * g j k = g i k`. This is the data `SymplecticGeometry.HypersurfaceData I X ι`.
The cocycle identity is part of the data because `g i j` is not determined by the `f` where they
vanish.

* `SymplecticGeometry.HypersurfaceData.support`: the hypersurface itself, the common zero set of
  the `f i` (`HypersurfaceData.mem_support_iff_of_mem`), a closed set.
* `SymplecticGeometry.HypersurfaceData.lineBundleCore D k`, for `k : ℤ`: the line bundle
  `𝒪(kD)`, as a Mathlib vector bundle core with model fibre `ℂ`, whose coordinate change from the
  chart `i` to the chart `j` is multiplication by `(g j i) ^ k`
  (`HypersurfaceData.lineBundleCore_coordChange`). It is a holomorphic line bundle
  (`HypersurfaceData.isContMDiff_lineBundleCore`, which gives `ContMDiffVectorBundle ω`).
* `SymplecticGeometry.HypersurfaceData.canonicalSection`: the section of `𝒪(D)` that is `f i` in
  the chart `i` (`HypersurfaceData.localTriv_canonicalSection`). It is holomorphic
  (`HypersurfaceData.contMDiff_canonicalSection`) and vanishes exactly on the support
  (`HypersurfaceData.canonicalSection_eq_zero_iff`). At a point of the support, the differentials
  of its local expressions differ by the nonzero factor `g i j`
  (`HypersurfaceData.mfderiv_f_apply_of_mem_support`), so whether it vanishes to first order
  does not depend on the chart.
* `SymplecticGeometry.HypersurfaceData.lineBundleCoreTensorEquiv D k l x`: the isomorphism
  `𝒪((k + l)D) ≅ 𝒪(kD) ⊗ 𝒪(lD)` onto Tau Ceti's tensor product bundle, `a ↦ a ⊗ 1` in every chart
  (`HypersurfaceData.tensorProduct_localTriv_lineBundleCoreTensorEquiv`), continuous on total
  spaces in both directions.

## Implementation notes

The core follows Tau Ceti's `TauCeti.signedPointTwistCore` and `Projectivization.twistCore`:
scalar coordinate changes `ContinuousLinearMap.lsmul ℂ ℂ` of a scalar cocycle. The three cores
`lineBundleCore (k + l)`, `lineBundleCore k` and `lineBundleCore l` share their charts and their
preferred chart at each point, so the tensor isomorphism needs no scalar factor, unlike the
library's `Projectivization.twistCoreTensorEquiv`. The proof of
`continuous_lineBundleCoreTensorEquiv` follows that of
`Projectivization.continuous_twistCoreTensorEquiv`.

## References

* [P. Griffiths, J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978], Chapter 1,
  §1 (divisors and their line bundles).
-/

public noncomputable section

open Bundle Set Topology
open scoped Manifold ContDiff TensorProduct TauCeti.ModuleTopology

namespace SymplecticGeometry

variable {F H : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [TopologicalSpace H]

/-- Local defining functions of a hypersurface in a complex manifold `X` with model `I`: an open
cover `U` of `X` indexed by `ι`, holomorphic functions `f i` on `U i`, and holomorphic, nowhere
vanishing functions `g i j` on `U i ∩ U j` with `f i = g i j * f j` there, which form a cocycle.
The hypersurface is the common zero set `HypersurfaceData.support`, and the `g` are the
transition functions of its line bundle. -/
structure HypersurfaceData (I : ModelWithCorners ℂ F H) (X : Type*) [TopologicalSpace X]
    [ChartedSpace H X] (ι : Type*) where
  /-- The open sets of the cover. -/
  U : ι → Set X
  isOpen_U (i : ι) : IsOpen (U i)
  iUnion_U : ⋃ i, U i = univ
  /-- The local defining function on `U i`. -/
  f : ι → X → ℂ
  contMDiffOn_f (i : ι) : ContMDiffOn I 𝓘(ℂ) ω (f i) (U i)
  /-- The transition functions: `f i = g i j * f j` on `U i ∩ U j`. -/
  g : ι → ι → X → ℂ
  contMDiffOn_g (i j : ι) : ContMDiffOn I 𝓘(ℂ) ω (g i j) (U i ∩ U j)
  g_ne_zero {i j : ι} {x : X} : x ∈ U i → x ∈ U j → g i j x ≠ 0
  f_eq_g_mul {i j : ι} {x : X} : x ∈ U i → x ∈ U j → f i x = g i j x * f j x
  g_mul_g {i j k : ι} {x : X} : x ∈ U i → x ∈ U j → x ∈ U k → g i j x * g j k x = g i k x

namespace HypersurfaceData

variable {I : ModelWithCorners ℂ F H} {X : Type*} [TopologicalSpace X] [ChartedSpace H X]
  {ι : Type*} (D : HypersurfaceData I X ι)

/-! ### The cover and the support -/

theorem exists_mem_U (x : X) : ∃ i, x ∈ D.U i :=
  mem_iUnion.1 (D.iUnion_U ▸ mem_univ x)

/-- A chart of the cover containing `x`. -/
def indexAt (x : X) : ι := (D.exists_mem_U x).choose

theorem mem_U_indexAt (x : X) : x ∈ D.U (D.indexAt x) := (D.exists_mem_U x).choose_spec

theorem g_self {i : ι} {x : X} (hi : x ∈ D.U i) : D.g i i x = 1 := by
  have h := D.g_mul_g hi hi hi
  exact (mul_eq_right₀ (D.g_ne_zero hi hi)).1 h

/-- The hypersurface: the points where the local defining functions vanish. -/
def support : Set X := {x | ∃ i, x ∈ D.U i ∧ D.f i x = 0}

theorem mem_support_iff {x : X} : x ∈ D.support ↔ ∃ i, x ∈ D.U i ∧ D.f i x = 0 := Iff.rfl

/-- In any chart containing `x`, the point `x` lies on the hypersurface exactly when the local
defining function of that chart vanishes at `x`. -/
theorem mem_support_iff_of_mem {i : ι} {x : X} (hi : x ∈ D.U i) :
    x ∈ D.support ↔ D.f i x = 0 := by
  refine ⟨fun ⟨j, hj, h⟩ ↦ ?_, fun h ↦ ⟨i, hi, h⟩⟩
  rw [D.f_eq_g_mul hi hj, h, mul_zero]

theorem isClosed_support : IsClosed D.support := by
  have : D.supportᶜ = ⋃ i, D.U i ∩ D.f i ⁻¹' {0}ᶜ := by
    ext x
    simp only [mem_compl_iff, mem_iUnion, mem_inter_iff, mem_preimage, mem_singleton_iff]
    refine ⟨fun h ↦ ⟨D.indexAt x, D.mem_U_indexAt x, ?_⟩, fun ⟨i, hi, h⟩ ↦ ?_⟩
    · rwa [← D.mem_support_iff_of_mem (D.mem_U_indexAt x)]
    · rwa [D.mem_support_iff_of_mem hi]
  rw [← isOpen_compl_iff, this]
  exact isOpen_iUnion fun i ↦
    ((D.contMDiffOn_f i).continuousOn.isOpen_inter_preimage (D.isOpen_U i) isOpen_compl_singleton)

/-- The powers of the transition functions are holomorphic on the overlaps. -/
theorem contMDiffOn_g_zpow (i j : ι) (k : ℤ) :
    ContMDiffOn I 𝓘(ℂ) ω (fun x ↦ D.g i j x ^ k) (D.U i ∩ D.U j) := by
  intro x hx
  have hpow : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (fun u : ℂ ↦ u ^ k) (D.g i j x) :=
    (contDiffAt_id.zpow (Or.inl (D.g_ne_zero hx.1 hx.2))).contMDiffAt
  exact hpow.comp_contMDiffWithinAt x (D.contMDiffOn_g i j x hx)

/-! ### The line bundle `𝒪(kD)` -/

/-- The line bundle `𝒪(kD)` of the hypersurface, for `k : ℤ`, as a vector bundle core with model
fibre `ℂ`. The chart `i` is trivial over `U i`, and the coordinate change from the chart `i` to
the chart `j` is multiplication by `(g j i) ^ k`, so that the local sections that are `f i ^ k`
in the chart `i` glue. -/
def lineBundleCore (k : ℤ) : VectorBundleCore ℂ X ℂ ι where
  baseSet := D.U
  isOpen_baseSet := D.isOpen_U
  indexAt := D.indexAt
  mem_baseSet_at := D.mem_U_indexAt
  coordChange i j x := ContinuousLinearMap.lsmul ℂ ℂ (D.g j i x ^ k)
  coordChange_self i x hx v := by simp [D.g_self hx]
  continuousOn_coordChange i j :=
    (ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] ℂ →L[ℂ] ℂ).continuous.comp_continuousOn
      ((D.contMDiffOn_g_zpow j i k).continuousOn.mono fun _ hx ↦ ⟨hx.2, hx.1⟩)
  coordChange_comp i j l x hx v := by
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, ← mul_assoc, ← mul_zpow]
    rw [D.g_mul_g hx.2 hx.1.2 hx.1.1]

theorem lineBundleCore_baseSet (k : ℤ) (i : ι) : (D.lineBundleCore k).baseSet i = D.U i := (rfl)

@[simp]
theorem lineBundleCore_localTriv_baseSet (k : ℤ) (i : ι) :
    ((D.lineBundleCore k).localTriv i).baseSet = D.U i := (rfl)

@[simp]
theorem lineBundleCore_indexAt (k : ℤ) (x : X) : (D.lineBundleCore k).indexAt x = D.indexAt x :=
  (rfl)

/-- The preferred trivialization of `𝒪(kD)` at `x` is its chart `D.indexAt x`. -/
theorem lineBundleCore_trivializationAt (k : ℤ) (x : X) :
    trivializationAt ℂ (D.lineBundleCore k).Fiber x =
      (D.lineBundleCore k).localTriv (D.indexAt x) :=
  (rfl)

/-- The coordinate change of `𝒪(kD)` from the chart `i` to the chart `j` is multiplication by
`(g j i) ^ k`. -/
theorem lineBundleCore_coordChange (k : ℤ) (i j : ι) (x : X) :
    (D.lineBundleCore k).coordChange i j x = ContinuousLinearMap.lsmul ℂ ℂ (D.g j i x ^ k) :=
  (rfl)

@[simp]
theorem lineBundleCore_coordChange_apply (k : ℤ) (i j : ι) (x : X) (v : ℂ) :
    (D.lineBundleCore k).coordChange i j x v = D.g j i x ^ k * v :=
  (rfl)

/-- **`𝒪(kD)` is a holomorphic line bundle**: its coordinate changes are holomorphic. With
Mathlib's `VectorBundleCore.instContMDiffVectorBundle` this makes it a `ContMDiffVectorBundle ω`. -/
instance isContMDiff_lineBundleCore (k : ℤ) : (D.lineBundleCore k).IsContMDiff I ω where
  contMDiffOn_coordChange i j :=
    (ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] ℂ →L[ℂ] ℂ).contMDiff.comp_contMDiffOn
      ((D.contMDiffOn_g_zpow j i k).mono fun _ hx ↦ ⟨hx.2, hx.1⟩)

/-! ### The canonical section of `𝒪(D)` -/

/-- The canonical section of `𝒪(D)`: the local defining function `f i` in the chart `i`
(`localTriv_canonicalSection`). -/
def canonicalSection (x : X) : (D.lineBundleCore 1).Fiber x := D.f (D.indexAt x) x

theorem canonicalSection_def (x : X) : D.canonicalSection x = D.f (D.indexAt x) x := (rfl)

/-- In the chart `i`, the canonical section of `𝒪(D)` is the defining function `f i`. -/
theorem localTriv_canonicalSection {i : ι} {x : X} (hi : x ∈ D.U i) :
    ((D.lineBundleCore 1).localTriv i ⟨x, D.canonicalSection x⟩).2 = D.f i x := by
  rw [VectorBundleCore.localTriv_apply]
  refine (D.lineBundleCore_coordChange_apply 1 _ i x (D.canonicalSection x)).trans ?_
  rw [zpow_one, canonicalSection_def, lineBundleCore_indexAt,
    ← D.f_eq_g_mul hi (D.mem_U_indexAt x)]

/-- The canonical section of `𝒪(D)` is holomorphic. -/
theorem contMDiff_canonicalSection :
    ContMDiff I (I.prod 𝓘(ℂ)) ω fun x ↦ TotalSpace.mk' ℂ x (D.canonicalSection x) := by
  refine ((D.lineBundleCore 1).contMDiff_section_iff _).2 fun i ↦ ?_
  refine (D.contMDiffOn_f i).congr fun x hx ↦ ?_
  rw [← D.localTriv_canonicalSection hx, VectorBundleCore.localTriv_apply]

/-- The canonical section of `𝒪(D)` vanishes exactly on the hypersurface. -/
theorem canonicalSection_eq_zero_iff {x : X} : D.canonicalSection x = 0 ↔ x ∈ D.support :=
  (D.mem_support_iff_of_mem (D.mem_U_indexAt x)).symm

/-- At a point of the hypersurface, the differentials of the defining functions of two charts
differ by the nonzero factor `g i j`. So the canonical section vanishes to first order there in
one chart exactly when it does in every chart (`mfderiv_f_eq_zero_iff`). -/
theorem mfderiv_f_apply_of_mem_support {i j : ι} {x : X} (hi : x ∈ D.U i) (hj : x ∈ D.U j)
    (hx : x ∈ D.support) (v : TangentSpace I x) :
    mfderiv I 𝓘(ℂ) (D.f i) x v = D.g i j x • mfderiv I 𝓘(ℂ) (D.f j) x v := by
  have hU : D.U i ∩ D.U j ∈ 𝓝 x := ((D.isOpen_U i).inter (D.isOpen_U j)).mem_nhds ⟨hi, hj⟩
  have hg : MDifferentiableAt I 𝓘(ℂ) (D.g i j) x :=
    ((D.contMDiffOn_g i j).contMDiffAt hU).mdifferentiableAt (by simp)
  have hf : MDifferentiableAt I 𝓘(ℂ) (D.f j) x :=
    ((D.contMDiffOn_f j).contMDiffAt ((D.isOpen_U j).mem_nhds hj)).mdifferentiableAt (by simp)
  have heq : D.f i =ᶠ[𝓝 x] D.g i j * D.f j :=
    Filter.eventually_of_mem hU fun y hy ↦ D.f_eq_g_mul hy.1 hy.2
  rw [((hg.hasMFDerivAt.mul hf.hasMFDerivAt).congr_of_eventuallyEq_abuse heq).mfderiv]
  -- The derivative of the product has values in the tangent space of `ℂ` at
  -- `(D.g i j * D.f j) x`, which is `ℂ` but not syntactically that at `D.f i x`.
  change D.g i j x * (show ℂ from mfderiv I 𝓘(ℂ) (D.f j) x v) +
    D.f j x * (show ℂ from mfderiv I 𝓘(ℂ) (D.g i j) x v) = _
  rw [(D.mem_support_iff_of_mem hj).1 hx, zero_mul, add_zero]
  rfl

/-- At a point of the hypersurface, the differential of the defining function of one chart
vanishes exactly when that of any other chart does. -/
theorem mfderiv_f_eq_zero_iff {i j : ι} {x : X} (hi : x ∈ D.U i) (hj : x ∈ D.U j)
    (hx : x ∈ D.support) :
    mfderiv I 𝓘(ℂ) (D.f i) x = 0 ↔ mfderiv I 𝓘(ℂ) (D.f j) x = 0 := by
  simp only [ContinuousLinearMap.ext_iff, D.mfderiv_f_apply_of_mem_support hi hj hx]
  exact forall_congr' fun _ ↦ smul_eq_zero_iff_right (D.g_ne_zero hi hj)

/-! ### Tensor products -/

section Tensor

variable (k l : ℤ)

/-- The isomorphism `v ↦ v ⊗ 1` from `ℂ` to `ℂ ⊗[ℂ] ℂ`, the model of
`lineBundleCoreTensorEquiv` on the model fibres. -/
private def tensorEquivModel : ℂ ≃L[ℂ] ℂ ⊗[ℂ] ℂ :=
  LinearEquiv.toContinuousLinearEquivOfIsModuleTopology (TensorProduct.rid ℂ ℂ).symm

private theorem tensorEquivModel_apply (v : ℂ) : tensorEquivModel v = v ⊗ₜ[ℂ] (1 : ℂ) := by
  rw [tensorEquivModel, LinearEquiv.coe_toContinuousLinearEquivOfIsModuleTopology,
    TensorProduct.rid_symm_apply]

private theorem tensorEquivModel_symm_apply (a b : ℂ) :
    tensorEquivModel.symm (a ⊗ₜ[ℂ] b) = a * b := by
  rw [ContinuousLinearEquiv.symm_apply_eq, tensorEquivModel_apply]
  apply (TensorProduct.rid ℂ ℂ).injective
  simp [mul_comm]

/-- The fibrewise isomorphism `𝒪((k + l)D) ≅ 𝒪(kD) ⊗ 𝒪(lD)`, `a ↦ a ⊗ 1` in every chart
(`tensorProduct_localTriv_lineBundleCoreTensorEquiv`). It is continuous on total spaces in both
directions (`continuous_lineBundleCoreTensorEquiv` and
`continuous_lineBundleCoreTensorEquiv_symm`). -/
def lineBundleCoreTensorEquiv (x : X) :
    (D.lineBundleCore (k + l)).Fiber x ≃L[ℂ]
      (D.lineBundleCore k).Fiber x ⊗[ℂ] (D.lineBundleCore l).Fiber x :=
  -- The fibres of `lineBundleCore` are `ℂ`, and their tensor product is `ℂ ⊗[ℂ] ℂ`.
  tensorEquivModel

theorem lineBundleCoreTensorEquiv_apply (x : X) (v : ℂ) :
    D.lineBundleCoreTensorEquiv k l x v =
      TensorProduct.tmul ℂ (M := (D.lineBundleCore k).Fiber x)
        (N := (D.lineBundleCore l).Fiber x) v (1 : ℂ) :=
  tensorEquivModel_apply v

theorem lineBundleCoreTensorEquiv_symm_apply (x : X) (a b : ℂ) :
    (D.lineBundleCoreTensorEquiv k l x).symm
        (TensorProduct.tmul ℂ (M := (D.lineBundleCore k).Fiber x)
          (N := (D.lineBundleCore l).Fiber x) a b) = a * b :=
  tensorEquivModel_symm_apply a b

/-- **`lineBundleCoreTensorEquiv` in a chart.** Over `U i`, read through the charts `i` of
`𝒪((k + l)D)`, `𝒪(kD)` and `𝒪(lD)`, `lineBundleCoreTensorEquiv` is `a ↦ a ⊗ 1`. -/
theorem tensorProduct_localTriv_lineBundleCoreTensorEquiv {i : ι} {x : X} (hi : x ∈ D.U i)
    (v : ℂ) :
    (Pretrivialization.tensorProduct ℂ ((D.lineBundleCore k).localTriv i)
        ((D.lineBundleCore l).localTriv i) ⟨x, D.lineBundleCoreTensorEquiv k l x v⟩).2 =
      TauCeti.ProjectiveTensor.tmulL ℂ ℂ ℂ ((D.lineBundleCore (k + l)).localTriv i ⟨x, v⟩).2 1 := by
  rw [lineBundleCoreTensorEquiv_apply, Pretrivialization.tensorProduct_apply]
  dsimp only
  -- The factors of the pure tensor are elements of `ℂ` read as elements of the fibres, so `rw`
  -- does not match `TensorProduct.map_tmul` against them.
  refine (congrArg (fun t ↦ ({ toTensorProduct := t } : TauCeti.ProjectiveTensor ℂ ℂ ℂ))
    (TensorProduct.map_tmul _ _ _ _)).trans ?_
  rw [Trivialization.coe_linearMapAt_of_mem _ hi, Trivialization.coe_linearMapAt_of_mem _ hi]
  simp only [VectorBundleCore.localTriv_apply, lineBundleCore_coordChange_apply,
    lineBundleCore_indexAt, TauCeti.ProjectiveTensor.tmulL_apply, mul_one]
  rw [zpow_add₀ (D.g_ne_zero hi (D.mem_U_indexAt x))]
  congr 1
  apply (TensorProduct.rid ℂ ℂ).injective
  simp only [TensorProduct.rid_tmul, smul_eq_mul]
  ring

/-- In the trivialization of `𝒪(kD) ⊗ 𝒪(lD)` at `x₀`, `lineBundleCoreTensorEquiv` sends a vector
to its coordinate in the preferred chart at `x₀` of `𝒪((k + l)D)`, tensored with `1`. -/
private theorem trivializationAt_lineBundleCoreTensorEquiv (x₀ : X) {x : X}
    (hx : x ∈ D.U (D.indexAt x₀)) (v : ℂ) :
    (trivializationAt (TauCeti.ProjectiveTensor ℂ ℂ ℂ)
        (fun x ↦ (D.lineBundleCore k).Fiber x ⊗[ℂ] (D.lineBundleCore l).Fiber x) x₀
        ⟨x, D.lineBundleCoreTensorEquiv k l x v⟩).2 =
      TauCeti.ProjectiveTensor.tmulL ℂ ℂ ℂ
        ((D.lineBundleCore (k + l)).localTriv (D.indexAt x₀) ⟨x, v⟩).2 1 := by
  rw [TauCeti.tensorProduct_trivializationAt, Bundle.Trivialization.tensorProduct_apply]
  simp only [lineBundleCore_trivializationAt]
  rw [← D.tensorProduct_localTriv_lineBundleCoreTensorEquiv k l hx v,
    Pretrivialization.tensorProduct_apply]

/-- `lineBundleCoreTensorEquiv` is continuous on total spaces. -/
theorem continuous_lineBundleCoreTensorEquiv :
    Continuous fun p : TotalSpace ℂ (D.lineBundleCore (k + l)).Fiber ↦
      TotalSpace.mk' (TauCeti.ProjectiveTensor ℂ ℂ ℂ)
        (E := fun x ↦ (D.lineBundleCore k).Fiber x ⊗[ℂ] (D.lineBundleCore l).Fiber x)
        p.proj (D.lineBundleCoreTensorEquiv k l p.proj p.snd) := by
  refine continuous_iff_continuousAt.2 fun p₀ ↦ ?_
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨(FiberBundle.continuous_proj _ _).continuousAt, ?_⟩
  set i := D.indexAt p₀.proj
  have hi₀ : p₀.proj ∈ D.U i := D.mem_U_indexAt p₀.proj
  have hU : ∀ᶠ p in 𝓝 p₀, p.proj ∈ D.U i :=
    (FiberBundle.continuous_proj _ _).continuousAt.preimage_mem_nhds
      ((D.isOpen_U i).mem_nhds hi₀)
  have h₁ : ContinuousAt (fun p ↦ ((D.lineBundleCore (k + l)).localTriv i p).2) p₀ :=
    continuous_snd.continuousAt.comp (((D.lineBundleCore (k + l)).localTriv i).continuousAt
      (((D.lineBundleCore (k + l)).mem_localTriv_source (i := i) p₀).2 hi₀))
  refine ContinuousAt.congr
    (((TauCeti.ProjectiveTensor.tmulL ℂ ℂ ℂ).continuous.continuousAt.comp h₁).clm_apply
      (continuousAt_const : ContinuousAt (fun _ ↦ (1 : ℂ)) p₀))
    (hU.mono fun p hp ↦ ?_)
  exact (D.trivializationAt_lineBundleCoreTensorEquiv k l p₀.proj hp p.snd).symm

/-- The inverse of `lineBundleCoreTensorEquiv` is continuous on total spaces. -/
theorem continuous_lineBundleCoreTensorEquiv_symm :
    Continuous fun q : TotalSpace (TauCeti.ProjectiveTensor ℂ ℂ ℂ)
        (fun x ↦ (D.lineBundleCore k).Fiber x ⊗[ℂ] (D.lineBundleCore l).Fiber x) ↦
      TotalSpace.mk' ℂ (E := (D.lineBundleCore (k + l)).Fiber) q.proj
        ((D.lineBundleCoreTensorEquiv k l q.proj).symm q.snd) :=
  TauCeti.continuous_bundle_symm _ (D.continuous_lineBundleCoreTensorEquiv k l)

end Tensor

end HypersurfaceData

end SymplecticGeometry

end
