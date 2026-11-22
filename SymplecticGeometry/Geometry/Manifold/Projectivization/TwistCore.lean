/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.Topology.VectorBundle.Constructions
public import SymplecticGeometry.Topology.Algebra.Module.Equiv.Pi
public import TauCeti.Geometry.Manifold.Projectivization.LineBundle
public import TauCeti.Topology.VectorBundle.Core.Trivial
public import TauCeti.Topology.VectorBundle.Hom
public import TauCeti.Topology.VectorBundle.TensorProduct.Basic

/-!
# Sums and tensor products of the line bundles `𝒪(k)`

On projective space `ℙ 𝕜 (Fin (n + 1) → 𝕜)`, Tau Ceti's `Projectivization.twistCore k` is the
line bundle `𝒪(k)`, glued from trivial lines over the standard affine opens along the transition
functions `twistTransition k`. This file adds the bundles built from it that the computation of
Chern classes of projective space uses.

* `Projectivization.twistPiCore k ι`: the bundle `𝒪(k) ⊗ 𝕜^ι`, the direct sum of `ι` copies of
  `𝒪(k)`, as a vector bundle core with model fibre `ι → 𝕜`, with the charts of `𝒪(k)` and
  transitions `twistTransition k i j • id`. It is analytic
  (`Projectivization.isContMDiff_twistPiCore`).
* `Projectivization.twistPiCoreOptionEquiv k ι x`: the splitting
  `𝒪(k) ⊗ 𝕜^{Option ι} ≅ 𝒪(k) ⊕ (𝒪(k) ⊗ 𝕜^ι)` into Mathlib's direct sum `×ᵇ` of bundles,
  continuous on total spaces in both directions. By induction on `r` it writes `𝒪(k)^{⊕ r}` as an
  iterated direct sum.
* `Projectivization.twistPiCoreTrivializationOfIsEmpty`: for empty `ι`, `𝒪(k) ⊗ 𝕜^ι` has rank
  zero and is trivial.
* `Projectivization.twistCoreTensorEquiv k l x`: the isomorphism `𝒪(k + l) ≅ 𝒪(k) ⊗ 𝒪(l)` onto
  Tau Ceti's tensor product bundle, `a ↦ a ⊗ 1` in every chart, continuous on total spaces in
  both directions. It rests on `Projectivization.twistTransition_add`.
* `Projectivization.twistCoreZeroTrivialization`: `𝒪(0)` is trivial, by
  `Projectivization.twistTransition_zero` and Tau Ceti's
  `VectorBundleCore.globalTrivializationOfCoordChangeEqId`.

## Implementation notes

The core `twistPiCore`, its base sets and its smoothness instance follow Tau Ceti's
`Projectivization.twistCore` and `Projectivization.isContMDiff_twistCore`, with the scalar
multiplication `lsmul` replaced by a scalar multiple of the identity of `ι → 𝕜`.

The fibres of a vector bundle core are its model fibre under the name `VectorBundleCore.Fiber`,
and the body of `twistCore` is not visible here. The fibrewise maps are therefore built on the
model fibres `𝕜`, `𝕜 × (ι → 𝕜)` and `𝕜 ⊗[𝕜] 𝕜`, and their continuity on total spaces is checked in
the preferred trivializations of the target bundles. The continuity of the inverse of
`twistCoreTensorEquiv` is Tau Ceti's `TauCeti.continuous_bundle_symm`; that of the inverse of
`twistPiCoreOptionEquiv` is proved directly, so that it needs no completeness of `𝕜`.

## References

* [P. Griffiths, J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978], Chapter 1,
  §1 (the line bundles `𝒪(k)` on projective space and their tensor products).
-/

public noncomputable section

open Bundle Set Topology
open scoped Manifold ContDiff LinearAlgebra.Projectivization TensorProduct TauCeti.ModuleTopology

namespace Projectivization

section Transition

variable {K ι : Type*} [Field K]

/-- On the overlap of two standard charts, the transition function of `𝒪(k)` does not
vanish. -/
theorem twistTransition_ne_zero (k : ℤ) {i j : ι} {x : ℙ K (ι → K)} (hi : x ∈ affineOpen i)
    (hj : x ∈ affineOpen j) : twistTransition k i j x ≠ 0 := by
  rw [twistTransition_def]
  exact zpow_ne_zero _
    (div_ne_zero ((mem_affineOpen_iff i x).1 hi) ((mem_affineOpen_iff j x).1 hj))

end Transition

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ}

/-- A point of projective space lies in the standard affine open of the preferred chart of
`𝒪(k)` at that point. -/
theorem mem_affineOpen_twistCore_indexAt (k : ℤ) (x : ℙ 𝕜 (Fin (n + 1) → 𝕜)) :
    x ∈ affineOpen ((twistCore k).indexAt x) :=
  twistCore_baseSet (𝕜 := 𝕜) k _ ▸ (twistCore k).mem_baseSet_at x

/-! ### The bundles `𝒪(k) ⊗ 𝕜^ι` -/

section Pi

/-- The vector bundle `𝒪(k) ⊗ 𝕜^ι`, that is, the direct sum of `ι` copies of `𝒪(k)`, on
projective space `ℙ 𝕜 (Fin (n + 1) → 𝕜)`, as a vector bundle core with model fibre `ι → 𝕜`. It
has the charts of `𝒪(k)`, and its coordinate change from the chart `i` to the chart `j` is
multiplication of every coordinate by `twistTransition k i j`. -/
def twistPiCore (k : ℤ) (ι : Type*) [Fintype ι] :
    VectorBundleCore 𝕜 (ℙ 𝕜 (Fin (n + 1) → 𝕜)) (ι → 𝕜) (Fin (n + 1)) where
  baseSet i := affineOpen i
  isOpen_baseSet i := isOpen_affineOpen i
  indexAt x := (twistCore (𝕜 := 𝕜) k).indexAt x
  mem_baseSet_at x := mem_affineOpen_twistCore_indexAt k x
  coordChange i j x := twistTransition k i j x • ContinuousLinearMap.id 𝕜 (ι → 𝕜)
  coordChange_self i x hx v := by simp [twistTransition_self k hx]
  continuousOn_coordChange i j :=
    (contMDiffOn_twistTransition k i j 0).continuousOn.smul continuousOn_const
  coordChange_comp i j l x hx v := by
    simp [smul_smul, mul_comm (twistTransition k i j x),
      twistTransition_mul_twistTransition k i l hx.1.2]

variable (k : ℤ) (ι : Type*) [Fintype ι]

/-- The chart `i` of `𝒪(k) ⊗ 𝕜^ι` is defined over the standard affine open `U_i`. -/
theorem twistPiCore_baseSet (i : Fin (n + 1)) :
    (twistPiCore (𝕜 := 𝕜) k ι).baseSet i = affineOpen i :=
  (rfl)

/-- The chart `i` of `𝒪(k) ⊗ 𝕜^ι` is trivial over the standard affine open `U_i`. -/
@[simp]
theorem twistPiCore_localTriv_baseSet (i : Fin (n + 1)) :
    ((twistPiCore (𝕜 := 𝕜) k ι).localTriv i).baseSet = affineOpen i :=
  (rfl)

/-- The preferred chart of `𝒪(k) ⊗ 𝕜^ι` at a point is that of `𝒪(k)`. -/
theorem twistPiCore_indexAt (x : ℙ 𝕜 (Fin (n + 1) → 𝕜)) :
    (twistPiCore k ι).indexAt x = (twistCore k).indexAt x :=
  (rfl)

/-- The coordinate change of `𝒪(k) ⊗ 𝕜^ι` from the chart `i` to the chart `j` multiplies by the
transition function of `𝒪(k)`. -/
@[simp]
theorem twistPiCore_coordChange_apply (i j : Fin (n + 1)) (x : ℙ 𝕜 (Fin (n + 1) → 𝕜))
    (v : ι → 𝕜) : (twistPiCore k ι).coordChange i j x v = twistTransition k i j x • v :=
  (rfl)

/-- **`𝒪(k) ⊗ 𝕜^ι` is an analytic vector bundle**, as its transition functions are
analytic. -/
instance isContMDiff_twistPiCore :
    (twistPiCore (𝕜 := 𝕜) (n := n) k ι).IsContMDiff 𝓘(𝕜, Fin n → 𝕜) ω where
  contMDiffOn_coordChange i j :=
    ContMDiffOn.smul (contMDiffOn_twistTransition k i j ω) contMDiffOn_const

/-- The fibrewise splitting `𝒪(k) ⊗ 𝕜^{Option ι} ≅ 𝒪(k) ⊕ (𝒪(k) ⊗ 𝕜^ι)`, which takes the
`none` coordinate to the first summand and the others to the second. It is continuous on total
spaces in both directions (`continuous_twistPiCoreOptionEquiv` and
`continuous_twistPiCoreOptionEquiv_symm`). -/
def twistPiCoreOptionEquiv (x : ℙ 𝕜 (Fin (n + 1) → 𝕜)) :
    (twistPiCore k (Option ι)).Fiber x ≃L[𝕜]
      ((twistCore k).Fiber ×ᵇ (twistPiCore k ι).Fiber) x :=
  ContinuousLinearEquiv.piOptionEquivProd 𝕜 fun _ ↦ 𝕜

/-- `twistPiCoreOptionEquiv` splits off the `none` coordinate. -/
@[simp]
theorem twistPiCoreOptionEquiv_apply (x : ℙ 𝕜 (Fin (n + 1) → 𝕜))
    (v : (twistPiCore k (Option ι)).Fiber x) :
    twistPiCoreOptionEquiv k ι x v = (v none, fun i ↦ v (some i)) :=
  ContinuousLinearEquiv.piOptionEquivProd_apply v

/-- The inverse of `twistPiCoreOptionEquiv` has the first summand as its `none` coordinate. -/
@[simp]
theorem twistPiCoreOptionEquiv_symm_apply_none (x : ℙ 𝕜 (Fin (n + 1) → 𝕜))
    (v : ((twistCore k).Fiber ×ᵇ (twistPiCore k ι).Fiber) x) :
    (twistPiCoreOptionEquiv k ι x).symm v none = v.1 :=
  ContinuousLinearEquiv.piOptionEquivProd_symm_apply_none (R := 𝕜) (M := fun _ ↦ 𝕜) v

/-- The inverse of `twistPiCoreOptionEquiv` has the second summand as its `some` coordinates. -/
@[simp]
theorem twistPiCoreOptionEquiv_symm_apply_some (x : ℙ 𝕜 (Fin (n + 1) → 𝕜))
    (v : ((twistCore k).Fiber ×ᵇ (twistPiCore k ι).Fiber) x) (i : ι) :
    (twistPiCoreOptionEquiv k ι x).symm v (some i) = v.2 i :=
  ContinuousLinearEquiv.piOptionEquivProd_symm_apply_some (R := 𝕜) (M := fun _ ↦ 𝕜) v i

/-- In the chart `i` of all three bundles, `twistPiCoreOptionEquiv` is
`ContinuousLinearEquiv.piOptionEquivProd`. -/
private theorem prod_localTriv_twistPiCoreOptionEquiv (i : Fin (n + 1))
    (p : TotalSpace (Option ι → 𝕜) (twistPiCore (𝕜 := 𝕜) (n := n) k (Option ι)).Fiber) :
    ((twistCore k).localTriv i).prod ((twistPiCore k ι).localTriv i)
        (TotalSpace.mk' (𝕜 × (ι → 𝕜)) (E := (twistCore k).Fiber ×ᵇ (twistPiCore k ι).Fiber)
          p.proj (twistPiCoreOptionEquiv k ι p.proj p.snd)) =
      (p.proj, ContinuousLinearEquiv.piOptionEquivProd 𝕜 (fun _ ↦ 𝕜)
        ((twistPiCore k (Option ι)).localTriv i p).2) := by
  -- After the coordinates of `twistCore` are computed, both sides are the coordinate changes of
  -- `twistPiCore`, which are the scalar multiplications by `twistTransition`.
  ext
  · rfl
  · simp [Trivialization.Prod.toFun', twistPiCoreOptionEquiv_apply, twistPiCore_indexAt]
    rfl
  · simp [Trivialization.Prod.toFun', twistPiCoreOptionEquiv_apply, twistPiCore_indexAt]
    rfl

/-- `twistPiCoreOptionEquiv` is continuous on total spaces. -/
theorem continuous_twistPiCoreOptionEquiv :
    Continuous fun p : TotalSpace (Option ι → 𝕜)
        (twistPiCore (𝕜 := 𝕜) (n := n) k (Option ι)).Fiber ↦
      TotalSpace.mk' (𝕜 × (ι → 𝕜)) (E := (twistCore k).Fiber ×ᵇ (twistPiCore k ι).Fiber) p.proj
        (twistPiCoreOptionEquiv k ι p.proj p.snd) := by
  refine continuous_iff_continuousAt.2 fun p₀ ↦ ?_
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨(FiberBundle.continuous_proj _ _).continuousAt, ?_⟩
  set i := (twistCore (𝕜 := 𝕜) (n := n) k).indexAt p₀.proj
  simp only [FiberBundle.prod_trivializationAt', VectorBundleCore.trivializationAt,
    ← VectorBundleCore.localTrivAt_def, twistPiCore_indexAt]
  simp only [prod_localTriv_twistPiCoreOptionEquiv]
  exact (ContinuousLinearEquiv.continuous _).continuousAt.comp
    (continuous_snd.continuousAt.comp
      (((twistPiCore k (Option ι)).localTriv i).continuousAt
        (((twistPiCore k (Option ι)).mem_localTriv_source (i := i) p₀).2
          (mem_affineOpen_twistCore_indexAt k p₀.proj))))

/-- In the chart `i` of all three bundles, the inverse of `twistPiCoreOptionEquiv` is the inverse
of `ContinuousLinearEquiv.piOptionEquivProd`. -/
private theorem localTriv_twistPiCoreOptionEquiv_symm (i : Fin (n + 1))
    (q : TotalSpace (𝕜 × (ι → 𝕜))
      ((twistCore (𝕜 := 𝕜) (n := n) k).Fiber ×ᵇ (twistPiCore k ι).Fiber)) :
    (twistPiCore k (Option ι)).localTriv i
        (TotalSpace.mk' (Option ι → 𝕜) (E := (twistPiCore k (Option ι)).Fiber) q.proj
          ((twistPiCoreOptionEquiv k ι q.proj).symm q.snd)) =
      (q.proj, (ContinuousLinearEquiv.piOptionEquivProd 𝕜 (fun _ ↦ 𝕜)).symm
        (((twistCore k).localTriv i).prod ((twistPiCore k ι).localTriv i) q).2) := by
  -- As in `prod_localTriv_twistPiCoreOptionEquiv`, both sides are scalar multiplications by
  -- `twistTransition` once the coordinates of `twistCore` are computed.
  ext j
  · rfl
  · cases j
    · simp only [Trivialization.Prod.toFun', Trivialization.prod_apply,
        VectorBundleCore.localTriv_apply, ContinuousLinearEquiv.piOptionEquivProd_symm_apply_none]
      exact (congrArg (twistTransition k ((twistCore k).indexAt q.proj) i q.proj * ·)
        (twistPiCoreOptionEquiv_symm_apply_none k ι q.proj q.snd)).trans
          (twistCore_coordChange_apply k _ i q.proj q.snd.1).symm
    · simp only [Trivialization.Prod.toFun', Trivialization.prod_apply,
        VectorBundleCore.localTriv_apply, ContinuousLinearEquiv.piOptionEquivProd_symm_apply_some]
      exact congrArg (twistTransition k ((twistCore k).indexAt q.proj) i q.proj * ·)
        (twistPiCoreOptionEquiv_symm_apply_some k ι q.proj q.snd _)

/-- The inverse of `twistPiCoreOptionEquiv` is continuous on total spaces. -/
theorem continuous_twistPiCoreOptionEquiv_symm :
    Continuous fun q : TotalSpace (𝕜 × (ι → 𝕜))
        ((twistCore (𝕜 := 𝕜) (n := n) k).Fiber ×ᵇ (twistPiCore k ι).Fiber) ↦
      TotalSpace.mk' (Option ι → 𝕜) (E := (twistPiCore k (Option ι)).Fiber) q.proj
        ((twistPiCoreOptionEquiv k ι q.proj).symm q.snd) := by
  refine continuous_iff_continuousAt.2 fun q₀ ↦ ?_
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨(FiberBundle.continuous_proj _ _).continuousAt, ?_⟩
  set i := (twistCore (𝕜 := 𝕜) (n := n) k).indexAt q₀.proj
  simp only [VectorBundleCore.trivializationAt, ← VectorBundleCore.localTrivAt_def,
    twistPiCore_indexAt]
  simp only [localTriv_twistPiCoreOptionEquiv_symm]
  have hq₀ : q₀ ∈ (((twistCore (𝕜 := 𝕜) (n := n) k).localTriv i).prod
      ((twistPiCore k ι).localTriv i)).source := by
    simp [mem_affineOpen_twistCore_indexAt k q₀.proj, i]
  exact (ContinuousLinearEquiv.continuous _).continuousAt.comp
    (continuous_snd.continuousAt.comp
      ((((twistCore k).localTriv i).prod ((twistPiCore k ι).localTriv i)).continuousAt hq₀))

/-- For empty `ι`, the rank-zero bundle `𝒪(k) ⊗ 𝕜^ι` is trivial: its total space is the product
of the base with the zero-dimensional space `ι → 𝕜`. -/
def twistPiCoreTrivializationOfIsEmpty [IsEmpty ι] :
    Trivialization (ι → 𝕜) (π (ι → 𝕜) (twistPiCore (𝕜 := 𝕜) (n := n) k ι).Fiber) :=
  (twistPiCore k ι).globalTrivializationOfCoordChangeEqId fun _ _ _ _ _ ↦ Subsingleton.elim _ _

/-- The trivialization `twistPiCoreTrivializationOfIsEmpty` is defined over the whole base. -/
@[simp]
theorem twistPiCoreTrivializationOfIsEmpty_baseSet [IsEmpty ι] :
    (twistPiCoreTrivializationOfIsEmpty (𝕜 := 𝕜) (n := n) k ι).baseSet = univ :=
  VectorBundleCore.globalTrivializationOfCoordChangeEqId_baseSet _ _

/-- The trivialization `twistPiCoreTrivializationOfIsEmpty` is linear on fibres. -/
instance [IsEmpty ι] : (twistPiCoreTrivializationOfIsEmpty (𝕜 := 𝕜) (n := n) k ι).IsLinear 𝕜 :=
  VectorBundleCore.globalTrivializationOfCoordChangeEqId_isLinear _ _

end Pi

/-! ### `𝒪(0)` is trivial -/

/-- The bundle `𝒪(0)` is trivial: its transition functions are `1`, so its total space is the
product of projective space with `𝕜`. -/
def twistCoreZeroTrivialization :
    Trivialization 𝕜 (π 𝕜 (twistCore (𝕜 := 𝕜) (n := n) 0).Fiber) :=
  (twistCore 0).globalTrivializationOfCoordChangeEqId fun _ _ _ _ _ ↦ by simp

/-- The trivialization `twistCoreZeroTrivialization` is defined over the whole base. -/
@[simp]
theorem twistCoreZeroTrivialization_baseSet :
    (twistCoreZeroTrivialization (𝕜 := 𝕜) (n := n)).baseSet = univ :=
  VectorBundleCore.globalTrivializationOfCoordChangeEqId_baseSet _ _

/-- The trivialization `twistCoreZeroTrivialization` keeps the base point and the coordinate in
the preferred chart. -/
@[simp]
theorem twistCoreZeroTrivialization_apply
    (p : TotalSpace 𝕜 (twistCore (𝕜 := 𝕜) (n := n) 0).Fiber) :
    twistCoreZeroTrivialization p = (p.proj, p.snd) :=
  VectorBundleCore.globalTrivializationOfCoordChangeEqId_apply _ _ p

/-- The trivialization `twistCoreZeroTrivialization` is linear on fibres. -/
instance : (twistCoreZeroTrivialization (𝕜 := 𝕜) (n := n)).IsLinear 𝕜 :=
  VectorBundleCore.globalTrivializationOfCoordChangeEqId_isLinear _ _

/-! ### Tensor products -/

section Tensor

variable (k l : ℤ)

/-- The scalar by which `twistCoreTensorEquiv` multiplies in preferred coordinates is not
zero. -/
private theorem twistTransition_mul_twistTransition_indexAt_ne_zero (x : ℙ 𝕜 (Fin (n + 1) → 𝕜)) :
    twistTransition k ((twistCore (k + l)).indexAt x) ((twistCore k).indexAt x) x *
      twistTransition l ((twistCore (k + l)).indexAt x) ((twistCore l).indexAt x) x ≠ 0 :=
  mul_ne_zero
    (twistTransition_ne_zero k (mem_affineOpen_twistCore_indexAt _ x)
      (mem_affineOpen_twistCore_indexAt _ x))
    (twistTransition_ne_zero l (mem_affineOpen_twistCore_indexAt _ x)
      (mem_affineOpen_twistCore_indexAt _ x))

/-- `twistCoreTensorEquiv` on the model fibres `𝕜` and `𝕜 ⊗[𝕜] 𝕜`. -/
private def twistCoreTensorEquivModel (x : ℙ 𝕜 (Fin (n + 1) → 𝕜)) : 𝕜 ≃L[𝕜] 𝕜 ⊗[𝕜] 𝕜 :=
  LinearEquiv.toContinuousLinearEquivOfIsModuleTopology
    ((LinearEquiv.smulOfNeZero 𝕜 𝕜 _
      (twistTransition_mul_twistTransition_indexAt_ne_zero (n := n) k l x)).trans
        (TensorProduct.lid 𝕜 𝕜).symm)

private theorem twistCoreTensorEquivModel_apply (x : ℙ 𝕜 (Fin (n + 1) → 𝕜)) (v : 𝕜) :
    twistCoreTensorEquivModel k l x v =
      (twistTransition k ((twistCore (k + l)).indexAt x) ((twistCore k).indexAt x) x * v) ⊗ₜ[𝕜]
        twistTransition l ((twistCore (k + l)).indexAt x) ((twistCore l).indexAt x) x := by
  rw [twistCoreTensorEquivModel, LinearEquiv.coe_toContinuousLinearEquivOfIsModuleTopology]
  apply (TensorProduct.lid 𝕜 𝕜).injective
  simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, LinearEquiv.smulOfNeZero_apply,
    TensorProduct.lid_tmul, smul_eq_mul]
  ring

/-- The fibrewise isomorphism `𝒪(k + l) ≅ 𝒪(k) ⊗ 𝒪(l)`, which is `a ↦ a ⊗ 1` in every chart
(`twistCoreTensorEquiv_apply`). It is continuous on total spaces in both directions
(`continuous_twistCoreTensorEquiv` and `continuous_twistCoreTensorEquiv_symm`). -/
def twistCoreTensorEquiv (x : ℙ 𝕜 (Fin (n + 1) → 𝕜)) :
    (twistCore (k + l)).Fiber x ≃L[𝕜] (twistCore k).Fiber x ⊗[𝕜] (twistCore l).Fiber x :=
  -- The fibres of `twistCore` are `𝕜`, and their tensor product is `𝕜 ⊗[𝕜] 𝕜`.
  twistCoreTensorEquivModel k l x

/-- In preferred coordinates at `x`, `twistCoreTensorEquiv` sends `v` to `(g * v) ⊗ h`, where
`g` and `h` are the transitions of `𝒪(k)` and `𝒪(l)` from the preferred chart of `𝒪(k + l)` to
their own preferred charts. Where the three preferred charts agree, this is `v ⊗ 1`. -/
theorem twistCoreTensorEquiv_apply (x : ℙ 𝕜 (Fin (n + 1) → 𝕜)) (v : 𝕜) :
    twistCoreTensorEquiv k l x v =
      TensorProduct.tmul 𝕜 (M := (twistCore k).Fiber x) (N := (twistCore l).Fiber x)
        (twistTransition k ((twistCore (k + l)).indexAt x) ((twistCore k).indexAt x) x * v)
        (twistTransition (𝕜 := 𝕜) l ((twistCore (k + l)).indexAt x)
          ((twistCore l).indexAt x) x) :=
  twistCoreTensorEquivModel_apply k l x v

variable [CompleteSpace 𝕜]

/-- In the trivialization of `𝒪(k) ⊗ 𝒪(l)` at `x₀`, `twistCoreTensorEquiv` sends a vector to its
coordinate in the chart `(twistCore k).indexAt x₀` of `𝒪(k + l)`, tensored with a transition
function of `𝒪(l)`. -/
private theorem trivializationAt_twistCoreTensorEquiv (x₀ : ℙ 𝕜 (Fin (n + 1) → 𝕜))
    {x : ℙ 𝕜 (Fin (n + 1) → 𝕜)} (hb : x ∈ affineOpen ((twistCore k).indexAt x₀))
    (hc : x ∈ affineOpen ((twistCore l).indexAt x₀)) (v : 𝕜) :
    (trivializationAt (TauCeti.ProjectiveTensor 𝕜 𝕜 𝕜)
        (fun x ↦ (twistCore (𝕜 := 𝕜) (n := n) k).Fiber x ⊗[𝕜] (twistCore l).Fiber x) x₀
        ⟨x, twistCoreTensorEquiv k l x v⟩).2 =
      TauCeti.ProjectiveTensor.tmulL 𝕜 𝕜 𝕜
        ((twistCore (k + l)).localTriv ((twistCore k).indexAt x₀) ⟨x, v⟩).2
        (twistTransition l ((twistCore k).indexAt x₀) ((twistCore l).indexAt x₀) x) := by
  have hb' : x ∈ (trivializationAt 𝕜 (twistCore (𝕜 := 𝕜) (n := n) k).Fiber x₀).baseSet := by
    simpa [VectorBundleCore.trivializationAt, ← VectorBundleCore.localTrivAt_def] using hb
  have hc' : x ∈ (trivializationAt 𝕜 (twistCore (𝕜 := 𝕜) (n := n) l).Fiber x₀).baseSet := by
    simpa [VectorBundleCore.trivializationAt, ← VectorBundleCore.localTrivAt_def] using hc
  rw [TauCeti.tensorProduct_trivializationAt, twistCoreTensorEquiv_apply]
  -- The factors of the pure tensor are elements of `𝕜`, read as elements of the fibres.
  refine (congrArg Prod.snd (Bundle.Trivialization.tensorProduct_apply_mk_tmul ⟨hb', hc'⟩
    (twistTransition k ((twistCore (k + l)).indexAt x) ((twistCore k).indexAt x) x * v)
    (twistTransition (𝕜 := 𝕜) l ((twistCore (k + l)).indexAt x) ((twistCore l).indexAt x) x))).trans
    ?_
  simp only [VectorBundleCore.trivializationAt, ← VectorBundleCore.localTrivAt_def,
    VectorBundleCore.localTriv_apply, twistCore_coordChange_apply,
    TauCeti.ProjectiveTensor.tmulL_apply]
  have h₁ := twistTransition_mul_twistTransition k ((twistCore (k + l)).indexAt x)
    ((twistCore k).indexAt x₀) (mem_affineOpen_twistCore_indexAt k x)
  have h₂ := twistTransition_mul_twistTransition l ((twistCore (k + l)).indexAt x)
    ((twistCore l).indexAt x₀) (mem_affineOpen_twistCore_indexAt l x)
  have h₃ := twistTransition_mul_twistTransition l ((twistCore (k + l)).indexAt x)
    ((twistCore l).indexAt x₀) hb
  rw [twistTransition_add k l (mem_affineOpen_twistCore_indexAt (k + l) x) hb]
  congr 1
  apply (TensorProduct.lid 𝕜 𝕜).injective
  simp only [TensorProduct.lid_tmul, smul_eq_mul]
  linear_combination
    (v * (twistTransition l ((twistCore l).indexAt x) ((twistCore l).indexAt x₀) x *
      twistTransition l ((twistCore (k + l)).indexAt x) ((twistCore l).indexAt x) x)) * h₁ +
    (twistTransition k ((twistCore (k + l)).indexAt x) ((twistCore k).indexAt x₀) x * v) * h₂ -
    (twistTransition k ((twistCore (k + l)).indexAt x) ((twistCore k).indexAt x₀) x * v) * h₃

/-- `twistCoreTensorEquiv` is continuous on total spaces. -/
theorem continuous_twistCoreTensorEquiv :
    Continuous fun p : TotalSpace 𝕜 (twistCore (𝕜 := 𝕜) (n := n) (k + l)).Fiber ↦
      TotalSpace.mk' (TauCeti.ProjectiveTensor 𝕜 𝕜 𝕜)
        (E := fun x ↦ (twistCore (𝕜 := 𝕜) (n := n) k).Fiber x ⊗[𝕜] (twistCore l).Fiber x)
        p.proj (twistCoreTensorEquiv k l p.proj p.snd) := by
  refine continuous_iff_continuousAt.2 fun p₀ ↦ ?_
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨(FiberBundle.continuous_proj _ _).continuousAt, ?_⟩
  set b := (twistCore (𝕜 := 𝕜) (n := n) k).indexAt p₀.proj
  set c := (twistCore (𝕜 := 𝕜) (n := n) l).indexAt p₀.proj
  have hb₀ : p₀.proj ∈ affineOpen b := mem_affineOpen_twistCore_indexAt k p₀.proj
  have hc₀ : p₀.proj ∈ affineOpen c := mem_affineOpen_twistCore_indexAt l p₀.proj
  have hU : ∀ᶠ p in 𝓝 p₀, p.proj ∈ affineOpen b ∩ affineOpen c :=
    (FiberBundle.continuous_proj _ _).continuousAt.preimage_mem_nhds
      (((isOpen_affineOpen b).inter (isOpen_affineOpen c)).mem_nhds ⟨hb₀, hc₀⟩)
  refine ContinuousAt.congr ?_
    (hU.mono fun p hp ↦ (trivializationAt_twistCoreTensorEquiv k l p₀.proj hp.1 hp.2 p.snd).symm)
  have h₁ : ContinuousAt (fun p ↦ ((twistCore (k + l)).localTriv b p).2) p₀ :=
    continuous_snd.continuousAt.comp (((twistCore (k + l)).localTriv b).continuousAt
      (((twistCore (k + l)).mem_localTriv_source (i := b) p₀).2
        (by simpa [twistCore_baseSet] using hb₀)))
  have h₂ : ContinuousAt (fun p : TotalSpace 𝕜 (twistCore (𝕜 := 𝕜) (n := n) (k + l)).Fiber ↦
      twistTransition l b c p.proj) p₀ :=
    ((contMDiffOn_twistTransition l b c 0).continuousOn.continuousAt
      (((isOpen_affineOpen b).inter (isOpen_affineOpen c)).mem_nhds ⟨hb₀, hc₀⟩)).comp
        (FiberBundle.continuous_proj _ _).continuousAt
  exact (((TauCeti.ProjectiveTensor.tmulL 𝕜 𝕜 𝕜).continuous.continuousAt.comp h₁).clm_apply h₂)

/-- The inverse of `twistCoreTensorEquiv` is continuous on total spaces. -/
theorem continuous_twistCoreTensorEquiv_symm :
    Continuous fun q : TotalSpace (TauCeti.ProjectiveTensor 𝕜 𝕜 𝕜)
        (fun x ↦ (twistCore (𝕜 := 𝕜) (n := n) k).Fiber x ⊗[𝕜] (twistCore l).Fiber x) ↦
      TotalSpace.mk' 𝕜 (E := (twistCore (k + l)).Fiber) q.proj
        ((twistCoreTensorEquiv k l q.proj).symm q.snd) :=
  TauCeti.continuous_bundle_symm _ (continuous_twistCoreTensorEquiv k l)

end Tensor

end Projectivization

end
