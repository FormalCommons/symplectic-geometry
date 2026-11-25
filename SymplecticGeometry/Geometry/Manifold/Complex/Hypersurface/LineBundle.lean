/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Core.Section
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Core.ScalarCocycle

/-!
# The line bundle of a divisor given by local equations

The data `SymplecticGeometry.HypersurfaceData I X ι` are local equations of an effective divisor
`D` on a complex manifold `X`: an open cover `U i` of `X`, with a preferred chart at each
point, and holomorphic functions `f i` on `U i`, together with holomorphic, nowhere vanishing
functions `g i j` on `U i ∩ U j` with `f i = g i j * f j` there, satisfying the cocycle identity
`g i j * g j k = g i k`. The cocycle identity is part of the data because `g i j` is not
determined by the `f` where they vanish.

The structure asks nothing more: an `f i` may vanish identically, and its zeros may be singular.
The common zero set is a smooth hypersurface when moreover no `f i` vanishes identically and
`mfderiv (f i) x ≠ 0` at each of its points `x` in `U i`. By
`HypersurfaceData.mfderiv_f_eq_zero_iff`, the second condition does not depend on the chart. The
line bundle and its canonical section need neither condition.

* `SymplecticGeometry.HypersurfaceData.support`: the common zero set of the `f i`
  (`HypersurfaceData.mem_support_iff_of_mem`), a closed set.
* `D.lineBundleCore k`, for `k : ℤ`: the line bundle `𝒪(kD)`, as a Mathlib vector bundle core
  with model fibre `ℂ`, whose coordinate change from the chart `i` to the chart `j` is
  multiplication by `(g j i) ^ k` (`ScalarCocycle.lineBundleCore_coordChange`). It is a
  holomorphic line bundle (`HypersurfaceData.isContMDiff_lineBundleCore`, which gives
  `ContMDiffVectorBundle ω`).
* `SymplecticGeometry.HypersurfaceData.canonicalSection`: the section of `𝒪(D)` that is `f i` in
  the chart `i` (`HypersurfaceData.localTriv_canonicalSection`). It is holomorphic
  (`HypersurfaceData.contMDiff_canonicalSection`) and vanishes exactly on the support
  (`HypersurfaceData.canonicalSection_eq_zero_iff`). At a point of the support, the differentials
  of its local expressions differ by the nonzero factor `g i j`
  (`HypersurfaceData.mfderiv_f_apply_of_mem_support`), so whether it vanishes to first order
  does not depend on the chart.
* `D.lineBundleCoreTensorEquiv k l x`: the isomorphism `𝒪((k + l)D) ≅ 𝒪(kD) ⊗ 𝒪(lD)` onto
  Tau Ceti's tensor product bundle, `a ↦ a ⊗ 1` in every chart
  (`ScalarCocycle.tensorProduct_localTriv_lineBundleCoreTensorEquiv`), continuous on total
  spaces in both directions.

## Implementation notes

`HypersurfaceData` extends `SymplecticGeometry.ScalarCocycle`: the cover, its preferred charts and
the transition functions form a scalar cocycle. So `D.lineBundleCore k`, `D.indexAt`,
`D.mem_U_indexAt`, `D.g_self` and `D.lineBundleCoreTensorEquiv k l` are, by dot notation, the
declarations `ScalarCocycle.lineBundleCore` and so on of `D.toScalarCocycle`
(`SymplecticGeometry/Topology/VectorBundle/Core/ScalarCocycle.lean`). Of the line bundle, this
file adds only the smoothness instance, from `ScalarCocycle.isContMDiff_lineBundleCore`.

## References

* [P. Griffiths, J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978], Chapter 1,
  §1 (divisors and their line bundles).
-/

public noncomputable section

open Bundle Set Topology
open scoped Manifold ContDiff

namespace SymplecticGeometry

variable {F H : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [TopologicalSpace H]

/-- Local equations of an effective divisor on a complex manifold `X` with model `I`: an open
cover `U` of `X` indexed by `ι` with a preferred chart `indexAt x` containing each point `x`,
holomorphic functions `f i` on `U i`, and holomorphic, nowhere vanishing functions `g i j` on
`U i ∩ U j` with `f i = g i j * f j` there, which form a cocycle.
The `g` are the transition functions of the line bundle of the divisor. The common zero set
`HypersurfaceData.support` is a smooth hypersurface if no `f i` vanishes identically and the
differential of each `f i` is nonzero on it, which the structure does not require. -/
@[ext]
structure HypersurfaceData (I : ModelWithCorners ℂ F H) (X : Type*) [TopologicalSpace X]
    [ChartedSpace H X] (ι : Type*) extends ScalarCocycle ℂ X ι where
  /-- The local equation on `U i`. -/
  f : ι → X → ℂ
  contMDiffOn_f (i : ι) : ContMDiffOn I 𝓘(ℂ) ω (f i) (U i)
  contMDiffOn_g (i j : ι) : ContMDiffOn I 𝓘(ℂ) ω (g i j) (U i ∩ U j)
  continuousOn_g i j := (contMDiffOn_g i j).continuousOn
  /-- The transition functions `g` relate the local equations: `f i = g i j * f j` on
  `U i ∩ U j`. -/
  f_eq_g_mul {i j : ι} {x : X} : x ∈ U i → x ∈ U j → f i x = g i j x * f j x

namespace HypersurfaceData

variable {I : ModelWithCorners ℂ F H} {X : Type*} [TopologicalSpace X] [ChartedSpace H X]
  {ι : Type*} (D : HypersurfaceData I X ι)

/-! ### The support -/

/-- The common zero set of the local equations: the points where they vanish. -/
def support : Set X := {x | ∃ i, x ∈ D.U i ∧ D.f i x = 0}

theorem mem_support_iff {x : X} : x ∈ D.support ↔ ∃ i, x ∈ D.U i ∧ D.f i x = 0 := Iff.rfl

/-- In any chart containing `x`, the point `x` lies in the support exactly when the local
equation of that chart vanishes at `x`. -/
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

/-! ### The line bundle `𝒪(kD)` -/

/-- **`𝒪(kD)` is a holomorphic line bundle**: the coordinate changes of
`ScalarCocycle.lineBundleCore D.toScalarCocycle k` are holomorphic. With Mathlib's
`VectorBundleCore.instContMDiffVectorBundle` this makes it a `ContMDiffVectorBundle ω`. -/
instance isContMDiff_lineBundleCore (k : ℤ) : (D.lineBundleCore k).IsContMDiff I ω :=
  D.toScalarCocycle.isContMDiff_lineBundleCore D.contMDiffOn_g k

/-! ### The canonical section of `𝒪(D)` -/

/-- The canonical section of `𝒪(D)`: the local equation `f i` in the chart `i`
(`localTriv_canonicalSection`). -/
def canonicalSection (x : X) : (D.lineBundleCore 1).Fiber x := D.f (D.indexAt x) x

theorem canonicalSection_def (x : X) : D.canonicalSection x = D.f (D.indexAt x) x := (rfl)

/-- In the chart `i`, the canonical section of `𝒪(D)` is the local equation `f i`. -/
theorem localTriv_canonicalSection {i : ι} {x : X} (hi : x ∈ D.U i) :
    ((D.lineBundleCore 1).localTriv i ⟨x, D.canonicalSection x⟩).2 = D.f i x := by
  rw [VectorBundleCore.localTriv_apply]
  refine (D.lineBundleCore_coordChange_apply 1 _ i x (D.canonicalSection x)).trans ?_
  rw [zpow_one, canonicalSection_def, D.lineBundleCore_indexAt,
    ← D.f_eq_g_mul hi (D.mem_U_indexAt x)]

/-- The canonical section of `𝒪(D)` is holomorphic. -/
theorem contMDiff_canonicalSection :
    ContMDiff I (I.prod 𝓘(ℂ)) ω fun x ↦ TotalSpace.mk' ℂ x (D.canonicalSection x) := by
  refine ((D.lineBundleCore 1).contMDiff_section_iff _).2 fun i ↦ ?_
  rw [D.lineBundleCore_baseSet]
  refine (D.contMDiffOn_f i).congr fun x hx ↦ ?_
  rw [← D.localTriv_canonicalSection hx, VectorBundleCore.localTriv_apply]

/-- The canonical section of `𝒪(D)` vanishes exactly on the support. -/
theorem canonicalSection_eq_zero_iff {x : X} : D.canonicalSection x = 0 ↔ x ∈ D.support :=
  (D.mem_support_iff_of_mem (D.mem_U_indexAt x)).symm

/-- At a point of the support, the differentials of the local equations of two charts
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

/-- At a point of the support, the differential of the local equation of one chart
vanishes exactly when that of any other chart does. -/
theorem mfderiv_f_eq_zero_iff {i j : ι} {x : X} (hi : x ∈ D.U i) (hj : x ∈ D.U j)
    (hx : x ∈ D.support) :
    mfderiv I 𝓘(ℂ) (D.f i) x = 0 ↔ mfderiv I 𝓘(ℂ) (D.f j) x = 0 := by
  simp only [ContinuousLinearMap.ext_iff, D.mfderiv_f_apply_of_mem_support hi hj hx]
  exact forall_congr' fun _ ↦ smul_eq_zero_iff_right (D.g_ne_zero hi hj)

end HypersurfaceData

end SymplecticGeometry

end
