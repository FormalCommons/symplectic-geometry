/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.VectorBundle.Hom
public import TauCeti.Topology.VectorBundle.TensorProduct.Basic

/-!
# The line bundles of a scalar cocycle

A `SymplecticGeometry.ScalarCocycle 𝕜 X ι` is an open cover `U i` of a topological space `X`
with continuous, nowhere vanishing functions `g i j : X → 𝕜` on the overlaps `U i ∩ U j` that
satisfy the cocycle identity `g i j * g j k = g i k`. For every `k : ℤ`, the powers `g j i ^ k`
glue trivial lines over the `U i` into a line bundle.

* `SymplecticGeometry.ScalarCocycle.lineBundleCore c k`: that line bundle, as a vector bundle
  core with model fibre `𝕜`, whose coordinate change from the chart `i` to the chart `j` is
  multiplication by `g j i ^ k` (`ScalarCocycle.lineBundleCore_coordChange`). The preferred chart
  at `x` is `c.indexAt x` for every `k`.
* `SymplecticGeometry.ScalarCocycle.lineBundleCoreTensorEquiv c k l x`: the isomorphism
  from the line bundle of `k + l` to the tensor product of those of `k` and `l` (Tau Ceti's
  tensor product bundle), `a ↦ a ⊗ 1` in every chart
  (`ScalarCocycle.tensorProduct_localTriv_lineBundleCoreTensorEquiv`), continuous on total
  spaces in both directions.

The smoothness of the line bundle over a manifold,
`SymplecticGeometry.ScalarCocycle.isContMDiff_lineBundleCore`, is in
`SymplecticGeometry/Geometry/Manifold/VectorBundle/Core/ScalarCocycle.lean`.

## Implementation notes

The core follows Tau Ceti's `TauCeti.signedPointTwistCore` and `Projectivization.twistCore`:
scalar coordinate changes `ContinuousLinearMap.lsmul 𝕜 𝕜` of a scalar cocycle. The cores for
`k + l`, `k` and `l` share their charts and their preferred chart at each point, so the tensor
isomorphism needs no scalar factor. Apart from that factor, the tensor section adapts the
library's `Projectivization.twistCoreTensorEquiv`,
`Projectivization.tensorProduct_localTriv_twistCoreTensorEquiv` and
`Projectivization.continuous_twistCoreTensorEquiv`
(`SymplecticGeometry/Geometry/Manifold/Projectivization/TwistCore.lean`).

## References

* [P. Griffiths, J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978], Chapter 0,
  §5 (line bundles given by transition functions).
-/

public noncomputable section

open Bundle Set Topology
open scoped TensorProduct TauCeti.ModuleTopology

namespace SymplecticGeometry

/-- A scalar cocycle on a topological space `X`: an open cover `U` of `X` indexed by `ι` and
continuous, nowhere vanishing functions `g i j` on the overlaps `U i ∩ U j` with
`g i j * g j k = g i k` on triple overlaps. -/
@[ext]
structure ScalarCocycle (𝕜 X ι : Type*) [NontriviallyNormedField 𝕜] [TopologicalSpace X] where
  /-- The open sets of the cover. -/
  U : ι → Set X
  isOpen_U (i : ι) : IsOpen (U i)
  iUnion_U : ⋃ i, U i = univ
  /-- The cocycle. -/
  g : ι → ι → X → 𝕜
  continuousOn_g (i j : ι) : ContinuousOn (g i j) (U i ∩ U j)
  g_ne_zero {i j : ι} {x : X} : x ∈ U i → x ∈ U j → g i j x ≠ 0
  g_mul_g {i j k : ι} {x : X} : x ∈ U i → x ∈ U j → x ∈ U k → g i j x * g j k x = g i k x

namespace ScalarCocycle

variable {𝕜 X ι : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace X]
  (c : ScalarCocycle 𝕜 X ι)

theorem exists_mem_U (x : X) : ∃ i, x ∈ c.U i :=
  mem_iUnion.1 (c.iUnion_U ▸ mem_univ x)

/-- A chart of the cover containing `x`. -/
def indexAt (x : X) : ι := (c.exists_mem_U x).choose

theorem mem_U_indexAt (x : X) : x ∈ c.U (c.indexAt x) := (c.exists_mem_U x).choose_spec

theorem g_self {i : ι} {x : X} (hi : x ∈ c.U i) : c.g i i x = 1 :=
  (mul_eq_right₀ (c.g_ne_zero hi hi)).1 (c.g_mul_g hi hi hi)

/-- The line bundle of the scalar cocycle and `k : ℤ`, as a vector bundle core with model fibre
`𝕜`: the chart `i` is trivial over `U i`, and the coordinate change from the chart `i` to the
chart `j` is multiplication by `g j i ^ k`. -/
def lineBundleCore (k : ℤ) : VectorBundleCore 𝕜 X 𝕜 ι where
  baseSet := c.U
  isOpen_baseSet := c.isOpen_U
  indexAt := c.indexAt
  mem_baseSet_at := c.mem_U_indexAt
  coordChange i j x := ContinuousLinearMap.lsmul 𝕜 𝕜 (c.g j i x ^ k)
  coordChange_self i x hx v := by simp [c.g_self hx]
  continuousOn_coordChange i j :=
    (ContinuousLinearMap.lsmul 𝕜 𝕜 : 𝕜 →L[𝕜] 𝕜 →L[𝕜] 𝕜).continuous.comp_continuousOn
      (((c.continuousOn_g j i).zpow₀ k fun _ hx ↦ Or.inl (c.g_ne_zero hx.1 hx.2)).mono
        fun _ hx ↦ ⟨hx.2, hx.1⟩)
  coordChange_comp i j l x hx v := by
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, ← mul_assoc, ← mul_zpow]
    rw [c.g_mul_g hx.2 hx.1.2 hx.1.1]

theorem lineBundleCore_baseSet (k : ℤ) (i : ι) : (c.lineBundleCore k).baseSet i = c.U i := (rfl)

@[simp]
theorem lineBundleCore_localTriv_baseSet (k : ℤ) (i : ι) :
    ((c.lineBundleCore k).localTriv i).baseSet = c.U i := (rfl)

@[simp]
theorem lineBundleCore_indexAt (k : ℤ) (x : X) : (c.lineBundleCore k).indexAt x = c.indexAt x :=
  (rfl)

/-- The preferred trivialization of the line bundle at `x` is its chart `c.indexAt x`. -/
theorem lineBundleCore_trivializationAt (k : ℤ) (x : X) :
    trivializationAt 𝕜 (c.lineBundleCore k).Fiber x =
      (c.lineBundleCore k).localTriv (c.indexAt x) :=
  (rfl)

/-- The coordinate change of the line bundle from the chart `i` to the chart `j` is
multiplication by `g j i ^ k`. -/
theorem lineBundleCore_coordChange (k : ℤ) (i j : ι) (x : X) :
    (c.lineBundleCore k).coordChange i j x = ContinuousLinearMap.lsmul 𝕜 𝕜 (c.g j i x ^ k) :=
  (rfl)

@[simp]
theorem lineBundleCore_coordChange_apply (k : ℤ) (i j : ι) (x : X) (v : 𝕜) :
    (c.lineBundleCore k).coordChange i j x v = c.g j i x ^ k * v :=
  (rfl)

/-! ### Tensor products -/

section Tensor

variable (k l : ℤ)

/-- The isomorphism `v ↦ v ⊗ 1` from `𝕜` to `𝕜 ⊗[𝕜] 𝕜`, the model of
`lineBundleCoreTensorEquiv` on the model fibres. -/
private def tensorEquivModel : 𝕜 ≃L[𝕜] 𝕜 ⊗[𝕜] 𝕜 :=
  LinearEquiv.toContinuousLinearEquivOfIsModuleTopology (TensorProduct.rid 𝕜 𝕜).symm

private theorem tensorEquivModel_apply (v : 𝕜) :
    (tensorEquivModel (𝕜 := 𝕜)) v = v ⊗ₜ[𝕜] (1 : 𝕜) := by
  rw [tensorEquivModel, LinearEquiv.coe_toContinuousLinearEquivOfIsModuleTopology,
    TensorProduct.rid_symm_apply]

private theorem tensorEquivModel_symm_apply (a b : 𝕜) :
    (tensorEquivModel (𝕜 := 𝕜)).symm (a ⊗ₜ[𝕜] b) = a * b := by
  rw [ContinuousLinearEquiv.symm_apply_eq, tensorEquivModel_apply]
  apply (TensorProduct.rid 𝕜 𝕜).injective
  simp [mul_comm]

/-- The fibrewise isomorphism from the line bundle of `k + l` to the tensor product of those of
`k` and `l`, `a ↦ a ⊗ 1` in every chart (`tensorProduct_localTriv_lineBundleCoreTensorEquiv`).
It is continuous on total spaces in both directions (`continuous_lineBundleCoreTensorEquiv` and
`continuous_lineBundleCoreTensorEquiv_symm`). -/
def lineBundleCoreTensorEquiv (x : X) :
    (c.lineBundleCore (k + l)).Fiber x ≃L[𝕜]
      (c.lineBundleCore k).Fiber x ⊗[𝕜] (c.lineBundleCore l).Fiber x :=
  -- The fibres of `lineBundleCore` are `𝕜`, and their tensor product is `𝕜 ⊗[𝕜] 𝕜`.
  tensorEquivModel

theorem lineBundleCoreTensorEquiv_apply (x : X) (v : 𝕜) :
    c.lineBundleCoreTensorEquiv k l x v =
      TensorProduct.tmul 𝕜 (M := (c.lineBundleCore k).Fiber x)
        (N := (c.lineBundleCore l).Fiber x) v (1 : 𝕜) :=
  tensorEquivModel_apply v

theorem lineBundleCoreTensorEquiv_symm_apply (x : X) (a b : 𝕜) :
    (c.lineBundleCoreTensorEquiv k l x).symm
        (TensorProduct.tmul 𝕜 (M := (c.lineBundleCore k).Fiber x)
          (N := (c.lineBundleCore l).Fiber x) a b) = a * b :=
  tensorEquivModel_symm_apply a b

/-- **`lineBundleCoreTensorEquiv` in a chart.** Over `U i`, read through the charts `i` of the
line bundles of `k + l`, `k` and `l`, `lineBundleCoreTensorEquiv` is `a ↦ a ⊗ 1`. -/
theorem tensorProduct_localTriv_lineBundleCoreTensorEquiv {i : ι} {x : X} (hi : x ∈ c.U i)
    (v : 𝕜) :
    (Pretrivialization.tensorProduct 𝕜 ((c.lineBundleCore k).localTriv i)
        ((c.lineBundleCore l).localTriv i) ⟨x, c.lineBundleCoreTensorEquiv k l x v⟩).2 =
      TauCeti.ProjectiveTensor.tmulL 𝕜 𝕜 𝕜 ((c.lineBundleCore (k + l)).localTriv i ⟨x, v⟩).2 1 := by
  rw [lineBundleCoreTensorEquiv_apply, Pretrivialization.tensorProduct_apply]
  dsimp only
  -- The factors of the pure tensor are elements of `𝕜` read as elements of the fibres, so `rw`
  -- does not match `TensorProduct.map_tmul` against them.
  refine (congrArg (fun t ↦ ({ toTensorProduct := t } : TauCeti.ProjectiveTensor 𝕜 𝕜 𝕜))
    (TensorProduct.map_tmul _ _ _ _)).trans ?_
  rw [Trivialization.coe_linearMapAt_of_mem _ hi, Trivialization.coe_linearMapAt_of_mem _ hi]
  simp only [VectorBundleCore.localTriv_apply, lineBundleCore_coordChange_apply,
    lineBundleCore_indexAt, TauCeti.ProjectiveTensor.tmulL_apply, mul_one]
  rw [zpow_add₀ (c.g_ne_zero hi (c.mem_U_indexAt x))]
  congr 1
  apply (TensorProduct.rid 𝕜 𝕜).injective
  simp only [TensorProduct.rid_tmul, smul_eq_mul]
  ring

variable [CompleteSpace 𝕜]

/-- In the trivialization of the tensor product at `x₀`, `lineBundleCoreTensorEquiv` sends a
vector to its coordinate in the preferred chart at `x₀` of the line bundle of `k + l`, tensored
with `1`. -/
private theorem trivializationAt_lineBundleCoreTensorEquiv (x₀ : X)
    {x : X} (hx : x ∈ c.U (c.indexAt x₀)) (v : 𝕜) :
    (trivializationAt (TauCeti.ProjectiveTensor 𝕜 𝕜 𝕜)
        (fun x ↦ (c.lineBundleCore k).Fiber x ⊗[𝕜] (c.lineBundleCore l).Fiber x) x₀
        ⟨x, c.lineBundleCoreTensorEquiv k l x v⟩).2 =
      TauCeti.ProjectiveTensor.tmulL 𝕜 𝕜 𝕜
        ((c.lineBundleCore (k + l)).localTriv (c.indexAt x₀) ⟨x, v⟩).2 1 := by
  rw [TauCeti.tensorProduct_trivializationAt, Bundle.Trivialization.tensorProduct_apply]
  simp only [lineBundleCore_trivializationAt]
  rw [← c.tensorProduct_localTriv_lineBundleCoreTensorEquiv k l hx v,
    Pretrivialization.tensorProduct_apply]

/-- `lineBundleCoreTensorEquiv` is continuous on total spaces. -/
theorem continuous_lineBundleCoreTensorEquiv :
    Continuous fun p : TotalSpace 𝕜 (c.lineBundleCore (k + l)).Fiber ↦
      TotalSpace.mk' (TauCeti.ProjectiveTensor 𝕜 𝕜 𝕜)
        (E := fun x ↦ (c.lineBundleCore k).Fiber x ⊗[𝕜] (c.lineBundleCore l).Fiber x)
        p.proj (c.lineBundleCoreTensorEquiv k l p.proj p.snd) := by
  refine continuous_iff_continuousAt.2 fun p₀ ↦ ?_
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨(FiberBundle.continuous_proj _ _).continuousAt, ?_⟩
  set i := c.indexAt p₀.proj
  have hi₀ : p₀.proj ∈ c.U i := c.mem_U_indexAt p₀.proj
  have hU : ∀ᶠ p in 𝓝 p₀, p.proj ∈ c.U i :=
    (FiberBundle.continuous_proj _ _).continuousAt.preimage_mem_nhds
      ((c.isOpen_U i).mem_nhds hi₀)
  have h₁ : ContinuousAt (fun p ↦ ((c.lineBundleCore (k + l)).localTriv i p).2) p₀ :=
    continuous_snd.continuousAt.comp (((c.lineBundleCore (k + l)).localTriv i).continuousAt
      (((c.lineBundleCore (k + l)).mem_localTriv_source (i := i) p₀).2 hi₀))
  refine ContinuousAt.congr
    (((TauCeti.ProjectiveTensor.tmulL 𝕜 𝕜 𝕜).continuous.continuousAt.comp h₁).clm_apply
      (continuousAt_const : ContinuousAt (fun _ ↦ (1 : 𝕜)) p₀))
    (hU.mono fun p hp ↦ ?_)
  exact (c.trivializationAt_lineBundleCoreTensorEquiv k l p₀.proj hp p.snd).symm

/-- The inverse of `lineBundleCoreTensorEquiv` is continuous on total spaces. -/
theorem continuous_lineBundleCoreTensorEquiv_symm :
    Continuous fun q : TotalSpace (TauCeti.ProjectiveTensor 𝕜 𝕜 𝕜)
        (fun x ↦ (c.lineBundleCore k).Fiber x ⊗[𝕜] (c.lineBundleCore l).Fiber x) ↦
      TotalSpace.mk' 𝕜 (E := (c.lineBundleCore (k + l)).Fiber) q.proj
        ((c.lineBundleCoreTensorEquiv k l q.proj).symm q.snd) :=
  TauCeti.continuous_bundle_symm _ (c.continuous_lineBundleCoreTensorEquiv k l)

end Tensor

end ScalarCocycle

end SymplecticGeometry

end
