/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Flow.Basic
public import SymplecticGeometry.Geometry.Symplectic.Cotangent.Bundle.Liouville
public import SymplecticGeometry.Geometry.Symplectic.Cotangent.Bundle.ZeroSection
public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.Manifold
public import TauCeti.Geometry.Manifold.IntegralCurve.GlobalFlow
public import TauCeti.Geometry.Manifold.DifferentialForm.Flow
public import TauCeti.Geometry.Manifold.Flow.Related
public import TauCeti.Geometry.Manifold.VectorBundle.Bilinear.SmulRight
public import TauCeti.Geometry.Manifold.VectorBundle.Submersion
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Classification
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Lift
public import TauCeti.Geometry.Symplectic.Hamiltonian.Manifold
public import TauCeti.Topology.FiberBundle.Separation

/-!
# Cotangent lifts of local flows

Let `Y` be a smooth vector field on a manifold `L`, with maximal flow `φ` (`TauCeti.flowOf`), and
let `H(q, p) = p(Y_q)` be its momentum function on the cotangent bundle `T*L`
(`TauCeti.CotangentBundle.momentumFunction`). The local flow of `Y` lifts to `T*L`:

`(q, p) ↦ (φ_t q, p ∘ (dφ_t)_q⁻¹)` (`TauCeti.CotangentBundle.liftFlow`),

for `t` in the maximal interval of existence of `Y` at `q`, the inverse of `(dφ_t)_q` being the
differential of `φ_{-t}` at `φ_t q`, as in Tau Ceti's cotangent lift `Diffeomorph.cotangent`.
This file proves that the lifted flow is the Hamiltonian flow of `H` for the canonical symplectic
form `ω = -dλ`, with the convention `ι_{X_H} ω = dH` of
`TauCeti.SmoothTwoForm.IsHamiltonianVectorField`:
for every covector `z = (q, p)`, the curve `t ↦ (φ_t q, p ∘ (dφ_t)_q⁻¹)` is an integral curve of
`X_H` on the whole maximal interval of existence of `Y` at `q`
(`TauCeti.CotangentBundle.isMIntegralCurveOn_liftFlow`), that interval is the maximal interval of
existence of `X_H` at `z`
(`TauCeti.CotangentBundle.maximalIntegralCurveInterval_eq_of_isHamiltonianVectorField`),
and so `X_H` is complete exactly when `Y` is
(`TauCeti.CotangentBundle.isCompleteVectorField_iff_of_isHamiltonianVectorField`).
When `Y` is complete, the lifted flow at time `t` is the cotangent lift `Diffeomorph.cotangent` of
the time-`t` diffeomorphism `TauCeti.globalFlowDiffeomorph`
(`TauCeti.CotangentBundle.liftFlow_eq_cotangent_globalFlowDiffeomorph`), so that Tau Ceti's
results on cotangent lifts, such as `Diffeomorph.mpullback_cotangent_liouvilleForm`, apply to it.

The proof is intrinsic. A Hamiltonian vector field `X` of `H` covers `Y`, `dπ (X z) = Y z.proj`,
since `ω` pairs `X` with a vertical vector `(0, β)` to `β (dπ X)` and `dH (0, β) = β (Y q)`
(`TauCeti.CotangentBundle.mfderiv_proj_of_isHamiltonianVectorField`). Hence `λ(X) = H`, and
Cartan's formula gives `L_X λ = ι_X dλ + d(λ(X)) = -dH + dH = 0`
(`TauCeti.CotangentBundle.mlieDerivForm_liouvilleForm_of_isHamiltonianVectorField`); this step
follows the proof of Tau Ceti's `TauCeti.CotangentBundle.isEquivariantMomentMap_momentMap`, run
backwards. So the flow of `X` preserves `λ` (`TauCeti.mpullback_flowOf_apply_eq_exp_integral_smul`)
and covers the flow of `Y` (`MDifferentiable.apply_flowOf`), and these two facts force it to be the
lifted flow wherever it is defined
(`TauCeti.CotangentBundle.flowOf_eq_liftFlow_of_isHamiltonianVectorField`). Finally the lifted
flow satisfies the flow law (`TauCeti.CotangentBundle.liftFlow_liftFlow`), so near each time of the
maximal interval of `Y` the lifted curve is a restarted trajectory of `X`, which makes it an
integral curve of `X` on that whole interval.

The flow API needs a finite-dimensional model, a Hausdorff base and no boundary.

The file ends with the theorem
`TauCeti.CotangentBundle.liouvilleForm_symplecticForm_and_cotangent_lifts`,
which collects the canonical structure of `T*L`: the intrinsic and coordinate formulas for `λ` and
`ω`, nondegeneracy, the characterization of `λ` by `σ^* λ = σ`
(`TauCeti.CotangentBundle.eq_liouvilleForm_of_forall_mpullback_eq`), the splitting along the zero
section (`TauCeti.CotangentBundle.eval₂_symplecticForm_zeroSectionTangentEquiv_symm`), cotangent
lifts of diffeomorphisms and their characterization by `F^* λ = λ`, and the lifted flows above.

## Main definitions

* `TauCeti.CotangentBundle.momentumFunction Y`: the function `H(q, p) = p(Y_q)` on `T*L`.
* `TauCeti.CotangentBundle.liftFlow Y t`: the cotangent lift of the time-`t` map of `Y`.

## Main results

* `TauCeti.CotangentBundle.isMIntegralCurveOn_liftFlow`: lifted trajectories are integral curves
  of `X_H` on the maximal interval of `Y`.
* `TauCeti.CotangentBundle.flowOf_eq_liftFlow_of_isHamiltonianVectorField`: the flow of `X_H` is
  the lifted flow.
* `TauCeti.CotangentBundle.maximalIntegralCurveInterval_eq_of_isHamiltonianVectorField` and
  `TauCeti.CotangentBundle.isCompleteVectorField_iff_of_isHamiltonianVectorField`: the maximal
  intervals of `X_H` and `Y` agree, and `X_H` is complete exactly when `Y` is.
* `TauCeti.CotangentBundle.liftFlow_eq_cotangent_globalFlowDiffeomorph`: for a complete `Y`, the
  lifted flow is the cotangent lift of the flow.
* `TauCeti.CotangentBundle.liouvilleForm_symplecticForm_and_cotangent_lifts`: the canonical
  structure of the cotangent bundle and cotangent lifts.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §3.1,
  Proposition 3.1.18 and Exercises 3.1.19 and 3.1.21.
-/

public section

noncomputable section

open Bundle Filter Set
open scoped Manifold Topology ContDiff

namespace TauCeti.CotangentBundle

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {L : Type*} [TopologicalSpace L] [ChartedSpace H L]
  {Y : (x : L) → TangentSpace I x}

variable (Y) in
/-- The **momentum function** of a vector field `Y` on `L`: the function `H(q, p) = p(Y_q)` on the
cotangent bundle, pairing each covector with the value of `Y` at its base point. -/
def momentumFunction (z : CotangentBundle I L) : ℝ :=
  z.snd (Y z.proj)

/-- The momentum function pairs a covector with the vector field at its base point. -/
@[simp]
theorem momentumFunction_apply (z : CotangentBundle I L) :
    momentumFunction Y z = z.snd (Y z.proj) :=
  (rfl)

section Smooth

variable [IsManifold I 1 L]

/-- The momentum function of a `C^n` vector field is `C^n`. -/
theorem contMDiff_momentumFunction {n : WithTop ℕ∞}
    (hY : ContMDiff I I.tangent n (fun x ↦ (⟨x, Y x⟩ : TangentBundle I L))) :
    ContMDiff (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 𝓘(ℝ) n (momentumFunction Y) := fun z ↦
  ContMDiffAt.clm_bundle_apply_scalar (b := fun z : CotangentBundle I L ↦ z.proj)
    (α := fun z ↦ z.snd) contMDiffAt_id ((hY.comp (contMDiff_proj _)) z)

/-- **The vertical derivative of the momentum function.** If `H` is differentiable at `z`, then,
read in the chart of `T*L` at `z`, the vertical tangent vector `(0, β)` is sent by `dH` to
`β (Y z.proj)`: along the fibre over `z.proj`, the momentum function is the linear map
`p ↦ p (Y z.proj)`. -/
theorem mvfderiv_momentumFunction_zero_prod {z : CotangentBundle I L}
    (hH : MDifferentiableAt (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 𝓘(ℝ) (momentumFunction Y) z)
    (β : E →L[ℝ] ℝ) :
    mvfderiv (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (momentumFunction Y) z ((0 : E), β) = β (Y z.proj) := by
  set p : E →L[ℝ] ℝ := z.snd
  set v : E := Y z.proj
  -- Along the fibre over `z.proj`, the momentum function is the evaluation at `Y z.proj`.
  have h₁ := hH.hasMFDerivAt.comp p (hasMFDerivAt_mk (I := I) (M := L) z.proj (c := id) (y := p)
    (hasMFDerivAt_id _))
  have h₂ : HasMFDerivAt 𝓘(ℝ, E →L[ℝ] ℝ) 𝓘(ℝ)
      (momentumFunction Y ∘ fun ξ : E →L[ℝ] ℝ ↦ TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun x : L ↦ TangentSpace I x →L[ℝ] ℝ) z.proj (id ξ)) p
      (ContinuousLinearMap.apply ℝ ℝ v) :=
    (ContinuousLinearMap.apply ℝ ℝ v).hasMFDerivAt
  -- For a real-valued function, `mvfderiv` is `mfderiv` read in `ℝ`.
  exact congrArg (fun A : (E →L[ℝ] ℝ) →L[ℝ] ℝ ↦ A β) (h₁.mfderiv.symm.trans h₂.mfderiv)

end Smooth

section Hamiltonian

variable [IsManifold I ∞ L]
  {X : (z : CotangentBundle I L) → TangentSpace (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) z}

/-- **A Hamiltonian vector field of the momentum function covers the vector field.** If `Y` is a
`C¹` vector field and `X` a Hamiltonian vector field of `H(q, p) = p(Y_q)` for the canonical
symplectic form, then `dπ (X z) = Y z.proj` at every covector `z`. -/
theorem mfderiv_proj_of_isHamiltonianVectorField
    (hY : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, Y x⟩ : TangentBundle I L)))
    (hX : (symplecticForm I L).IsHamiltonianVectorField (momentumFunction Y) X)
    (z : CotangentBundle I L) :
    mfderiv (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) I (π (E →L[ℝ] ℝ) (fun x : L ↦ TangentSpace I x →L[ℝ] ℝ)) z
      (X z) = Y z.proj := by
  rw [Bundle.mfderiv_proj]
  refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ) (V := E)).2 fun β ↦ ?_
  -- Pair `X z` with the vertical vector `(0, β)`.
  have h := ((eval₂_symplecticForm z (X z) ((0 : E), β)).trans
    (strongDualCotangentSymplecticForm_apply _ _)).symm.trans
    (SmoothTwoForm.isHamiltonianVectorField_iff.1 hX z ((0 : E), β))
  rw [mvfderiv_momentumFunction_zero_prod
    ((contMDiff_momentumFunction hY z).mdifferentiableAt one_ne_zero)] at h
  simp only [map_zero, sub_zero] at h
  exact h

/-- For a `C¹` vector field `Y`, the Liouville form takes the value `H` on a Hamiltonian vector
field of the momentum function `H(q, p) = p(Y_q)`. -/
theorem liouvilleForm_apply_of_isHamiltonianVectorField
    (hY : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, Y x⟩ : TangentBundle I L)))
    (hX : (symplecticForm I L).IsHamiltonianVectorField (momentumFunction Y) X)
    (z : CotangentBundle I L) :
    (liouvilleForm I L).val z ![X z] = momentumFunction Y z := by
  rw [liouvilleForm_apply, Matrix.cons_val_zero, mfderiv_proj_of_isHamiltonianVectorField hY hX,
    momentumFunction_apply]

/-- **A Hamiltonian vector field of the momentum function preserves the Liouville form**: for a
`C¹` vector field `Y` and a differentiable Hamiltonian vector field `X` of `H(q, p) = p(Y_q)`,
`L_X λ = 0`, by Cartan's formula `L_X λ = ι_X dλ + d(λ(X)) = -ι_X ω + dH`. -/
theorem mlieDerivForm_liouvilleForm_of_isHamiltonianVectorField
    (hY : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, Y x⟩ : TangentBundle I L)))
    (hX : (symplecticForm I L).IsHamiltonianVectorField (momentumFunction Y) X)
    (hXd : MDifferentiable (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).tangent
      fun z ↦ (⟨z, X z⟩ : TangentBundle (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (CotangentBundle I L))) :
    mlieDerivForm X (liouvilleForm I L).val = 0 := by
  rw [SmoothForm.mlieDerivForm_eq_interior_mextDeriv_add hXd]
  have hlam : RoughForm.interior X (liouvilleForm I L).val =
      RoughForm.ofFunction _ (momentumFunction Y) := by
    funext z
    ext v
    rw [RoughForm.interior_apply, Subsingleton.elim v ![], RoughForm.ofFunction_apply]
    exact liouvilleForm_apply_of_isHamiltonianVectorField hY hX z
  have hω := SmoothTwoForm.isHamiltonianVectorField_iff_interior_eq.1 hX
  rw [symplecticForm_eq_neg_mextDeriv] at hω
  rw [hlam, ← hω]
  funext z
  ext v
  simp [RoughForm.interior_apply]

end Hamiltonian

section Flow

variable (Y) in
/-- The **cotangent lift of the local flow** of `Y`: at time `t`, the covector `p` at `q` goes to
the covector `p ∘ (dφ_t)_q⁻¹` at `φ_t q`, where `φ` is the maximal flow of `Y`
(`TauCeti.flowOf`), the inverse of `(dφ_t)_q` being the differential of `φ_{-t}` at `φ_t q`. It
is meaningful for `t` in the maximal interval of existence of `Y` at `q`. -/
def liftFlow (t : ℝ) (z : CotangentBundle I L) : CotangentBundle I L :=
  TotalSpace.mk' (E →L[ℝ] ℝ) (flowOf Y t z.proj)
    (z.snd ∘L mfderiv I I (flowOf Y (-t)) (flowOf Y t z.proj))

/-- The lifted flow at time `t` sends the covector `p` at `q` to `p ∘ (dφ_{-t})_{φ_t q}` at
`φ_t q`. -/
theorem liftFlow_def (t : ℝ) (z : CotangentBundle I L) :
    liftFlow Y t z = TotalSpace.mk' (E →L[ℝ] ℝ) (flowOf Y t z.proj)
      (z.snd ∘L mfderiv I I (flowOf Y (-t)) (flowOf Y t z.proj)) :=
  (rfl)

/-- The lifted flow covers the flow of `Y`. -/
@[simp]
theorem proj_liftFlow (t : ℝ) (z : CotangentBundle I L) :
    (liftFlow Y t z).proj = flowOf Y t z.proj :=
  (rfl)

/-- The lifted covector evaluates a tangent vector `w` at `φ_t q` as the original covector
evaluates `(dφ_{-t}) w`. -/
theorem liftFlow_snd_apply (t : ℝ) (z : CotangentBundle I L)
    (w : TangentSpace I (flowOf Y t z.proj)) :
    (liftFlow Y t z).snd w = z.snd (mfderiv I I (flowOf Y (-t)) (flowOf Y t z.proj) w) :=
  (rfl)

/-- At time `0` the lifted flow is the identity. -/
theorem liftFlow_zero (z : CotangentBundle I L) : liftFlow Y 0 z = z :=
  CotangentBundle.ext (flowOf_zero Y z.proj) fun w ↦ congrArg z.snd
    ((congrArg (fun A : E →L[ℝ] E ↦ A w) (mfderiv_congr (congrArg (flowOf Y) neg_zero))).trans
      (mfderiv_flowOf_zero_apply_eq_self Y _ w))

variable [CompleteSpace E] [BoundarylessManifold I L] [T2Space L] [IsManifold I 1 L]
  (hY : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, Y x⟩ : TangentBundle I L)))
include hY

/-- The lifted covector evaluated on `(dφ_t)_q v` is the original covector evaluated on `v`. -/
theorem liftFlow_snd_apply_mfderiv {t : ℝ} {z : CotangentBundle I L}
    (ht : (t, z.proj) ∈ flowDomain Y) (v : TangentSpace I z.proj) :
    (liftFlow Y t z).snd (mfderiv I I (flowOf Y t) z.proj v) = z.snd v :=
  congrArg z.snd (mfderiv_flowOf_neg_apply_mfderiv_flowOf hY ht v)

/-- **The flow law for the lifted flow**: lifting for time `t` and then for time `s` is lifting
for time `t + s`, wherever the flow of `Y` is defined. -/
theorem liftFlow_liftFlow {s t : ℝ} {z : CotangentBundle I L} (ht : (t, z.proj) ∈ flowDomain Y)
    (hs : (s, flowOf Y t z.proj) ∈ flowDomain Y) :
    liftFlow Y s (liftFlow Y t z) = liftFlow Y (t + s) z := by
  have hadd := flowOf_add hY ht hs
  have h (w : TangentSpace I (flowOf Y s (flowOf Y t z.proj))) :
      @Eq E (mfderiv I I (flowOf Y (-t)) (flowOf Y t z.proj)
        (mfderiv I I (flowOf Y (-s)) (flowOf Y s (flowOf Y t z.proj)) w))
        (mfderiv I I (flowOf Y (-(t + s))) (flowOf Y (t + s) z.proj) w) := by
    rw [mfderiv_flowOf_add_apply hY (neg_mem_flowDomain_flowOf hY hs)
      (flowOf_neg_flowOf hY hs) (neg_mem_flowDomain_flowOf hY ht), neg_add_rev]
    exact congrArg (fun A : E →L[ℝ] E ↦ A w) (mfderiv_congr_point hadd.2)
  exact CotangentBundle.ext hadd.2 fun w ↦ congrArg z.snd (h w)

end Flow

section Complete

variable [CompleteSpace E] [BoundarylessManifold I L] [T2Space L] [IsManifold I ∞ L]

/-- **Lifted flows of complete fields are cotangent lifts.** For a complete smooth vector field
`Y`, the lifted flow at time `t` is the cotangent lift `Diffeomorph.cotangent` of the time-`t`
diffeomorphism of the flow of `Y` (`TauCeti.globalFlowDiffeomorph`). -/
theorem liftFlow_eq_cotangent_globalFlowDiffeomorph (hcomplete : IsCompleteVectorField Y)
    (hY : ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, Y x⟩ : TangentBundle I L))) (t : ℝ) :
    liftFlow Y t = (globalFlowDiffeomorph hcomplete le_top hY t).cotangent := by
  have hflow := flowOf_eq_globalFlow (hY.of_le (by exact_mod_cast le_top)) hcomplete
  have h₁ : ⇑(globalFlowDiffeomorph hcomplete le_top hY t) = flowOf Y t := by
    rw [coe_globalFlowDiffeomorph, hflow]
  have h₂ : ⇑(globalFlowDiffeomorph hcomplete le_top hY t).symm = flowOf Y (-t) := by
    funext x
    rw [globalFlowDiffeomorph_symm_apply, hflow]
  funext z
  rw [Diffeomorph.cotangent_apply, h₁, h₂, liftFlow_def]

end Complete

section HamiltonianFlow

variable [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space L] [IsManifold I ∞ L]
  {X : (z : CotangentBundle I L) → TangentSpace (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) z}
  (hY : ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, Y x⟩ : TangentBundle I L)))
  (hX : (symplecticForm I L).IsHamiltonianVectorField (momentumFunction Y) X)
include hY hX

omit [I.Boundaryless] [T2Space L] in
/-- A Hamiltonian vector field of the momentum function of a smooth vector field is smooth. -/
theorem contMDiff_of_isHamiltonianVectorField_momentumFunction :
    ContMDiff (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).tangent ∞
      fun z ↦ (⟨z, X z⟩ : TangentBundle (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (CotangentBundle I L)) :=
  isSymplectic_symplecticForm.isNondegenerate.contMDiff_of_isHamiltonianVectorField le_rfl
    (by simpa using contMDiff_momentumFunction hY) hX

/-- **The Hamiltonian flow is the lifted flow.** Wherever the flow of a Hamiltonian vector field
`X` of the momentum function `H(q, p) = p(Y_q)` is defined, it is the cotangent lift of the flow
of `Y`. -/
theorem flowOf_eq_liftFlow_of_isHamiltonianVectorField {t : ℝ} {z : CotangentBundle I L}
    (ht : (t, z) ∈ flowDomain X) : flowOf X t z = liftFlow Y t z := by
  have hY1 : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, Y x⟩ : TangentBundle I L)) :=
    hY.of_le (by simp)
  have hXs := contMDiff_of_isHamiltonianVectorField_momentumFunction hY hX
  have hX1 : ContMDiff (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).tangent 1
      fun z ↦ (⟨z, X z⟩ : TangentBundle (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (CotangentBundle I L)) :=
    hXs.of_le (by simp)
  have hπ : MDifferentiable (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) I
      (π (E →L[ℝ] ℝ) (fun x : L ↦ TangentSpace I x →L[ℝ] ℝ)) :=
    (contMDiff_proj _).mdifferentiable one_ne_zero
  have hXY := mfderiv_proj_of_isHamiltonianVectorField hY1 hX
  have htY : (t, z.proj) ∈ flowDomain Y :=
    mem_flowDomain.2 (hπ.maximalIntegralCurveInterval_subset hXY z (mem_flowDomain.1 ht))
  -- The flow of `X` covers the flow of `Y` near `z`.
  have hev : π (E →L[ℝ] ℝ) (fun x : L ↦ TangentSpace I x →L[ℝ] ℝ) ∘ flowOf X t =ᶠ[𝓝 z]
      flowOf Y t ∘ π (E →L[ℝ] ℝ) (fun x : L ↦ TangentSpace I x →L[ℝ] ℝ) := by
    filter_upwards [(isOpen_setOf_mem_flowDomain hX1 continuous_const continuous_id).mem_nhds ht]
      with z' hz'
    exact hπ.apply_flowOf hY1 hXY hz'
  have hΦ : MDifferentiableAt (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (flowOf X t) z :=
    (contMDiffAt_flowOf_comp le_rfl hX1 contMDiffAt_const contMDiffAt_id ht).mdifferentiableAt
      one_ne_zero
  have hφ : MDifferentiableAt I I (flowOf Y t) z.proj :=
    (contMDiffAt_flowOf_comp le_rfl hY1 contMDiffAt_const contMDiffAt_id htY).mdifferentiableAt
      one_ne_zero
  -- The flow of `X` preserves the Liouville form, since `L_X λ = 0`.
  have hL : mlieDerivForm X (liouvilleForm I L).val =
      fun y ↦ (fun _ ↦ (0 : ℝ)) y • (liouvilleForm I L).val y := by
    rw [mlieDerivForm_liouvilleForm_of_isHamiltonianVectorField hY1 hX
      (hX1.mdifferentiable one_ne_zero)]
    funext y
    simp
  have hpres := mpullback_flowOf_apply_eq_exp_integral_smul (hXs.of_le (by simp))
    continuous_const (liouvilleForm I L).mdifferentiable hL ht
  simp only [intervalIntegral.integral_zero, Real.exp_zero, one_smul] at hpres
  -- Hence the covector `flowOf X t z` pulls back along `dφ_t` to `z`.
  have hkey (u : TangentSpace I z.proj) :
      (flowOf X t z).snd (mfderiv I I (flowOf Y t) z.proj u) = z.snd u := by
    obtain ⟨v, rfl⟩ := Bundle.mfderiv_proj_surjective z u
    have h := congrArg (fun α ↦ α ![v]) hpres
    simp only [mpullback_apply_one, liouvilleForm_apply, Matrix.cons_val_zero] at h
    rw [← mfderiv_comp_apply z (hπ _) hΦ, hev.mfderiv_eq, ContinuousLinearMap.comp_apply,
      mfderiv_comp_apply z hφ (hπ z)] at h
    -- `tangentSpaceCast` is the identity of the model space.
    exact h
  refine CotangentBundle.ext (hev.self_of_nhds) fun w ↦ ?_
  exact (congrArg (flowOf X t z).snd (mfderiv_flowOf_apply_mfderiv_flowOf_neg hY1 htY w)).symm.trans
    (hkey _)

/-- **Cotangent lifts of flows are Hamiltonian.** For a smooth vector field `Y` on `L` and a
Hamiltonian vector field `X` of the momentum function `H(q, p) = p(Y_q)` for the canonical
symplectic form, the lifted curve `t ↦ (φ_t q, p ∘ (dφ_t)_q⁻¹)` through a covector `z = (q, p)`
is an integral curve of `X` on the whole maximal interval of existence of `Y` at `q`. -/
theorem isMIntegralCurveOn_liftFlow (z : CotangentBundle I L) :
    IsMIntegralCurveOn (fun t ↦ liftFlow Y t z) X (maximalIntegralCurveInterval Y z.proj) := by
  have hY1 : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, Y x⟩ : TangentBundle I L)) :=
    hY.of_le (by simp)
  have hX1 : ContMDiff (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).tangent 1
      fun z ↦ (⟨z, X z⟩ : TangentBundle (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (CotangentBundle I L)) :=
    (contMDiff_of_isHamiltonianVectorField_momentumFunction hY hX).of_le (by simp)
  intro t ht
  have hD : (t, z.proj) ∈ flowDomain Y := mem_flowDomain.2 ht
  set w := liftFlow Y t z
  -- Near time `t`, the lifted curve is the flow of `X` through `w`, restarted at time `t`.
  have h₁ : ∀ᶠ s in 𝓝 (0 : ℝ), (s, flowOf Y t z.proj) ∈ flowDomain Y :=
    (isOpen_setOf_mem_flowDomain hY1 continuous_id continuous_const).mem_nhds
      (mem_flowDomain_zero hY1 _)
  have h₂ : ∀ᶠ s in 𝓝 (0 : ℝ), (s, w) ∈ flowDomain X :=
    (isOpen_setOf_mem_flowDomain hX1 continuous_id continuous_const).mem_nhds
      (mem_flowDomain_zero hX1 _)
  have hsub : Tendsto (fun r ↦ r - t) (𝓝 t) (𝓝 0) := by
    simpa using (continuous_sub_right t).tendsto t
  have heq : (fun r ↦ liftFlow Y r z) =ᶠ[𝓝 t] (fun s ↦ flowOf X s w) ∘ (· + -t) := by
    filter_upwards [hsub.eventually (h₁.and h₂)] with r hr
    rw [Function.comp_apply, ← sub_eq_add_neg,
      flowOf_eq_liftFlow_of_isHamiltonianVectorField hY hX hr.2,
      liftFlow_liftFlow hY1 hD hr.1, add_sub_cancel]
  have hd :=
    ((isMIntegralCurveAt_flowOf hX1 (mem_flowDomain_zero hX1 w)).comp_add (-t)).hasMFDerivAt
  have hval : ((fun s ↦ flowOf X s w) ∘ (· + -t)) (0 - -t) = w := by
    simp
  rw [hval, zero_sub, neg_neg] at hd
  exact (hd.congr_of_eventuallyEq heq).hasMFDerivWithinAt

/-- **The maximal intervals agree.** The maximal interval of existence of `X` at a covector
`z = (q, p)` is the maximal interval of existence of `Y` at `q`. -/
theorem maximalIntegralCurveInterval_eq_of_isHamiltonianVectorField (z : CotangentBundle I L) :
    maximalIntegralCurveInterval X z = maximalIntegralCurveInterval Y z.proj := by
  refine subset_antisymm (MDifferentiable.maximalIntegralCurveInterval_subset
    ((contMDiff_proj _).mdifferentiable one_ne_zero)
    (mfderiv_proj_of_isHamiltonianVectorField (hY.of_le (by simp)) hX) z) ?_
  intro t ht
  obtain ⟨γ, a, b, hγ, hx, h0, ht, -⟩ := exists_isMIntegralCurveOn_maximalIntegralCurve_eq ht
  exact ((isMIntegralCurveOn_liftFlow hY hX z).mono
    (hγ.subset_maximalIntegralCurveInterval h0 hx)).subset_maximalIntegralCurveInterval h0
    (liftFlow_zero z) ht

/-- The flow of `X` is defined at `(t, z)` exactly when the flow of `Y` is defined at
`(t, z.proj)`. -/
theorem mem_flowDomain_iff_of_isHamiltonianVectorField {t : ℝ} {z : CotangentBundle I L} :
    (t, z) ∈ flowDomain X ↔ (t, z.proj) ∈ flowDomain Y := by
  rw [mem_flowDomain, mem_flowDomain,
    maximalIntegralCurveInterval_eq_of_isHamiltonianVectorField hY hX]

/-- **Completeness.** A Hamiltonian vector field of the momentum function of `Y` is complete
exactly when `Y` is. -/
theorem isCompleteVectorField_iff_of_isHamiltonianVectorField :
    IsCompleteVectorField X ↔ IsCompleteVectorField Y := by
  simp only [isCompleteVectorField_iff_maximalIntegralCurveInterval,
    maximalIntegralCurveInterval_eq_of_isHamiltonianVectorField hY hX]
  exact ⟨fun h q ↦ h (zeroSection (E →L[ℝ] ℝ) (fun x : L ↦ TangentSpace I x →L[ℝ] ℝ) q),
    fun h z ↦ h z.proj⟩

end HamiltonianFlow

section Milestone

variable [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space L] [IsManifold I ∞ L]

/-- **The canonical structure of a cotangent bundle and cotangent lifts.** Here `L` is a Hausdorff
smooth manifold without boundary, modelled on a finite-dimensional space; its cotangent bundle
`π : T*L → L` carries the Liouville form `λ` and the canonical symplectic form `ω`.

1. `λ_(q, p)(v) = p(dπ v)` and `ω = -dλ`.
2. In every bundle chart, with coordinates `(q, p)`, `λ` is the linear form `Σ pᵢ dqᵢ`
   (`TauCeti.cotangentLiouvilleForm`) and `ω((δq, δp), (δq', δp')) = δp'(δq) - δp(δq')`, that is
   `Σ dqᵢ ∧ dpᵢ`.
3. `ω` is symplectic.
4. A one-form `μ` on `T*L` satisfies `σ^* μ = σ` for every one-form `σ` on `L`, read as a section
   of `T*L`, if and only if `μ = λ`.
5. At the zero covector over `q`, in the splitting `T_q L × T*_q L` of the tangent space given by
   `TauCeti.Bundle.zeroSectionTangentEquiv`, `ω((v, a), (w, b)) = b(v) - a(w)`.
6. The cotangent lift `(q, p) ↦ (χ q, p ∘ (dχ_q)⁻¹)` of a diffeomorphism `χ` of `L` preserves `λ`
   and `ω`. Conversely, for every diffeomorphism `F` of `T*L` with `F^* λ = λ` there is exactly
   one diffeomorphism `χ` of `L` whose lift is `F`.
7. For a smooth vector field `Y` on `L`, the function `H(q, p) = p(Y_q)` is smooth, and its
   Hamiltonian vector field `X_H`, with `ι_{X_H} ω = dH`, generates the cotangent lift of the local
   flow `φ` of `Y`: for every covector `z = (q, p)`, the curve
   `t ↦ (φ_t q, p ∘ (dφ_t)_q⁻¹)` is an integral curve of `X_H` on the whole maximal interval of
   existence of `Y` at `q`, this interval is the maximal interval of existence of `X_H` at `z`, and
   the flow of `X_H` is this curve there. In particular `X_H` is complete if `Y` is.

Milestone: *Canonical cotangent structure and cotangent lifts*. -/
theorem liouvilleForm_symplecticForm_and_cotangent_lifts :
    -- 1. The intrinsic formulas.
    (∀ (z : CotangentBundle I L) (v : Fin 1 → TangentSpace (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) z),
      (liouvilleForm I L).val z v =
        z.snd (mfderiv (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) I
          (π (E →L[ℝ] ℝ) (fun x : L ↦ TangentSpace I x →L[ℝ] ℝ)) z (v 0))) ∧
    (symplecticForm I L).val = -mextDeriv (liouvilleForm I L).val ∧
    -- 2. The coordinate formulas.
    (∀ (z₀ : CotangentBundle I L) {w : E × (E →L[ℝ] ℝ)},
      w ∈ (extChartAt (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) z₀).target →
        RoughForm.inChartAt (liouvilleForm I L).val z₀ w = cotangentLiouvilleForm w) ∧
    (∀ (z₀ : CotangentBundle I L) {w : E × (E →L[ℝ] ℝ)},
      w ∈ (extChartAt (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) z₀).target →
        ∀ v : Fin 2 → E × (E →L[ℝ] ℝ), RoughForm.inChartAt (symplecticForm I L).val z₀ w v =
          strongDualCotangentSymplecticForm (v 0) (v 1)) ∧
    -- 3. Nondegeneracy.
    (symplecticForm I L).IsSymplectic ∧
    -- 4. The tautological property characterizes the Liouville form.
    (∀ μ : SmoothForm (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (CotangentBundle I L) ℝ 1,
      (∀ σ : SmoothForm I L ℝ 1,
        SmoothForm.mpullback
          (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) x (SmoothForm.degreeOneEquiv σ x))
          (SmoothForm.degreeOneEquiv σ).contMDiff μ = σ) ↔ μ = liouvilleForm I L) ∧
    -- 5. The canonical splitting along the zero section.
    (∀ (q : L) (v w : TangentSpace I q) (a b : TangentSpace I q →L[ℝ] ℝ),
      SmoothBundleForm.eval₂ (symplecticForm I L)
          (zeroSection (E →L[ℝ] ℝ) (fun x : L ↦ TangentSpace I x →L[ℝ] ℝ) q)
          ((Bundle.zeroSectionTangentEquiv (I := I) q).symm (v, a))
          ((Bundle.zeroSectionTangentEquiv (I := I) q).symm (w, b)) =
        b v - a w) ∧
    -- 6. Cotangent lifts of diffeomorphisms, and their characterization.
    (∀ (χ : L ≃ₘ⟮I, I⟯ L) (z : CotangentBundle I L),
      χ.cotangent z =
        TotalSpace.mk' (E →L[ℝ] ℝ) (χ z.proj) (z.snd ∘L mfderiv I I χ.symm (χ z.proj))) ∧
    (∀ χ : L ≃ₘ⟮I, I⟯ L,
      SmoothForm.mpullback χ.cotangent χ.cotangent.contMDiff (liouvilleForm I L) =
          liouvilleForm I L ∧
        SmoothForm.mpullback χ.cotangent χ.cotangent.contMDiff (symplecticForm I L) =
          symplecticForm I L) ∧
    (∀ F : CotangentBundle I L ≃ₘ⟮I.prod 𝓘(ℝ, E →L[ℝ] ℝ), I.prod 𝓘(ℝ, E →L[ℝ] ℝ)⟯
        CotangentBundle I L,
      SmoothForm.mpullback F F.contMDiff (liouvilleForm I L) = liouvilleForm I L →
        ∃! χ : L ≃ₘ⟮I, I⟯ L, χ.cotangent = F) ∧
    -- 7. Cotangent lifts of local flows are Hamiltonian.
    (∀ Y : (x : L) → TangentSpace I x,
      ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, Y x⟩ : TangentBundle I L)) →
        ContMDiff (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 𝓘(ℝ) ∞ (momentumFunction Y) ∧
        (symplecticForm I L).IsHamiltonianVectorField (momentumFunction Y)
          ((symplecticForm I L).hamiltonianVectorField (momentumFunction Y)) ∧
        (∀ z : CotangentBundle I L,
          IsMIntegralCurveOn (fun t ↦ liftFlow Y t z)
              ((symplecticForm I L).hamiltonianVectorField (momentumFunction Y))
              (maximalIntegralCurveInterval Y z.proj) ∧
            maximalIntegralCurveInterval
                ((symplecticForm I L).hamiltonianVectorField (momentumFunction Y)) z =
              maximalIntegralCurveInterval Y z.proj ∧
            ∀ t ∈ maximalIntegralCurveInterval Y z.proj,
              flowOf ((symplecticForm I L).hamiltonianVectorField (momentumFunction Y)) t z =
                liftFlow Y t z) ∧
        (IsCompleteVectorField Y →
          IsCompleteVectorField
            ((symplecticForm I L).hamiltonianVectorField (momentumFunction Y)))) := by
  refine ⟨liouvilleForm_apply, symplecticForm_eq_neg_mextDeriv, fun z₀ _ hw ↦
    inChartAt_liouvilleForm z₀ hw, fun z₀ _ hw ↦ inChartAt_symplecticForm_apply z₀ hw,
    isSymplectic_symplecticForm, fun μ ↦ ⟨eq_liouvilleForm_of_forall_mpullback_eq,
      fun h ↦ h ▸ mpullback_liouvilleForm⟩,
    eval₂_symplecticForm_zeroSectionTangentEquiv_symm, Diffeomorph.cotangent_apply,
    fun χ ↦ ⟨χ.mpullback_cotangent_liouvilleForm, χ.mpullback_cotangent_symplecticForm⟩,
    Diffeomorph.existsUnique_cotangent_eq_of_mpullback_liouvilleForm, fun Y hY ↦ ?_⟩
  have hX := isSymplectic_symplecticForm.isNondegenerate
    |>.isHamiltonianVectorField_hamiltonianVectorField (I := I.prod 𝓘(ℝ, E →L[ℝ] ℝ))
      (momentumFunction Y)
  refine ⟨contMDiff_momentumFunction hY, hX, fun z ↦ ⟨isMIntegralCurveOn_liftFlow hY hX z,
    maximalIntegralCurveInterval_eq_of_isHamiltonianVectorField hY hX z, fun t ht ↦
    flowOf_eq_liftFlow_of_isHamiltonianVectorField hY hX ?_⟩,
    (isCompleteVectorField_iff_of_isHamiltonianVectorField hY hX).2⟩
  exact (mem_flowDomain_iff_of_isHamiltonianVectorField hY hX).2 (mem_flowDomain.2 ht)

end Milestone

end TauCeti.CotangentBundle
