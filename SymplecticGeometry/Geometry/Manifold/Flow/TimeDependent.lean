/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Flow
public import TauCeti.Geometry.Manifold.Flow.TimeDependent
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Tangent.Opens
import Mathlib.Geometry.Manifold.Instances.Icc
import TauCeti.Geometry.Manifold.IntegralCurve.Interval

/-!
# Time-dependent flows: joint smoothness, uniqueness on intervals, open subsets

Let `X` be a `C^n` time-dependent vector field, `1 ≤ n`, on a finite-dimensional boundaryless
manifold `M`, whose suspension on `ℝ × M` is complete. Tau Ceti's
`TauCeti.timeDependentFlowDiffeomorph hc hn hX s t` is the flow of `X` from time `s` to time `t`,
as a `C^n` diffeomorphism of `M`. For a fixed initial time `s`, these diffeomorphisms form a
jointly `C^n` family in `(t, x)`.

The restriction of a `C¹` time-dependent field `X` to an open subset `U` has, as its flow, the flow
of `X`, wherever the flow of the restriction is defined: a trajectory of the restriction is a
trajectory of `X`, and Tau Ceti's uniqueness theorem
`TauCeti.timeDependentFlowOf_eq_of_hasMFDerivAt` applies. The two flows then agree near the
initial point, so their differentials agree too. The restriction is `C¹` by
`TauCeti.Manifold.contMDiff_tangentSpaceOpenEquiv_symm`.

The proofs of `TauCeti.timeDependentFlowOf_restrict_eq` and
`TauCeti.tangentSpaceOpenEquiv_mfderiv_timeDependentFlowOf_restrict` adapt those of
`TauCeti.timeDependentFlowOf_restrict_opens` and
`TauCeti.mfderiv_timeDependentFlowOf_restrict_opens_apply`, in Tau Ceti's file
`TauCeti/Geometry/Manifold/Flow/TimeDependent/Opens.lean` at commit
526c5263b3fcb0f8fc7ea15aff46134de6919d86 (Tau Ceti pull request #2176), which the pinned version
of Tau Ceti does not have.

Tau Ceti proves that solutions of the time-dependent equation are unique on open intervals
(`TauCeti.timeDependentFlowOf_eq_of_hasMFDerivAt`).
`TauCeti.timeDependentFlowOf_eq_of_hasMFDerivWithinAt` is the same statement on any
preconnected set of times, such as a closed interval, with derivatives within that set. Its proof
follows Tau Ceti's: both curves are lifted through their clocks to integral curves of the
suspension, and these agree by Tau Ceti's uniqueness theorem for integral curves on preconnected
sets, `IsMIntegralCurveOn.eqOn_of_isPreconnected`.
So the curves of the diffeotopy `TauCeti.timeDependentFlowDiffeotopy` of `X` are the solutions on
`[0, 1]` (`TauCeti.timeDependentFlowDiffeotopy_apply_eq_of_mfderiv_eq`).

## Main results

* `TauCeti.contMDiff_timeDependentFlowDiffeomorph`: the map
  `(t, x) ↦ timeDependentFlowDiffeomorph hc hn hX s t x` is `C^n` on `ℝ × M`. It is Tau Ceti's
  `TauCeti.contMDiff_timeDependentFlowOf` restricted to a fixed initial time.
* `TauCeti.timeDependentFlowOf_restrict_eq`: the flow of the restriction of `X` to `U` is defined
  only where the flow of `X` is, and agrees with it there.
* `TauCeti.tangentSpaceOpenEquiv_mfderiv_timeDependentFlowOf_restrict`: so do their differentials,
  the tangent spaces of `U` and `M` being identified.
* `TauCeti.timeDependentFlowOf_eq_of_hasMFDerivWithinAt`: uniqueness of solutions on a
  preconnected set of times.
* `TauCeti.timeDependentFlowDiffeotopy_apply_eq_of_mfderiv_eq`: a curve on `[0, 1]` whose
  velocity is `X` is a trajectory of `TauCeti.timeDependentFlowDiffeotopy`.
-/

public section

open scoped Manifold ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-- The time-dependent flow from a fixed time `s` of a `C^n` time-dependent vector field, `1 ≤ n`,
with complete suspension is jointly `C^n` in the final time and the initial point. -/
theorem contMDiff_timeDependentFlowDiffeomorph [FiniteDimensional ℝ E] [T2Space M]
    [BoundarylessManifold I M] [IsManifold I 1 M] {n : ℕ∞} (hn : 1 ≤ n) [IsManifold I n M]
    {X : ℝ → (x : M) → TangentSpace I x}
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent n
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    (hc : IsCompleteVectorField (timeDependentSuspensionField X)) (s : ℝ) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) I n
      (fun p : ℝ × M ↦ timeDependentFlowDiffeomorph hc hn hX s p.1 p.2) :=
  (contMDiff_timeDependentFlowOf hc hn hX).comp
    ((contMDiff_const.prodMk contMDiff_fst).prodMk contMDiff_snd) |>.congr fun p ↦
      timeDependentFlowDiffeomorph_apply hc hn hX s p.1 p.2

/-! ### Uniqueness of solutions on preconnected sets of times -/

section Icc

open Set

variable [T2Space M] [IsManifold I 1 M] [BoundarylessManifold I M]
  {X : ℝ → (x : M) → TangentSpace I x} {s t : ℝ}

/-- **Uniqueness of solutions on a preconnected set of times.** Let `X` be a `C¹` time-dependent
vector field whose suspension is complete. A curve `γ` that solves `γ' u = X u (γ u)` on a
preconnected `S ⊆ ℝ`, with derivatives within `S`, such as one-sided derivatives at the ends of a
closed interval, is the curve of the time-dependent flow through `γ s` at time `s`, for all
`s, t ∈ S`. -/
theorem timeDependentFlowOf_eq_of_hasMFDerivWithinAt
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 1
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    (hc : IsCompleteVectorField (timeDependentSuspensionField X)) {γ : ℝ → M} {S : Set ℝ}
    (hS : IsPreconnected S)
    (hγ : ∀ u ∈ S, HasMFDerivWithinAt 𝓘(ℝ, ℝ) I γ S u ((1 : ℝ →L[ℝ] ℝ).smulRight (X u (γ u))))
    (hs : s ∈ S) (ht : t ∈ S) :
    timeDependentFlowOf X s t (γ s) = γ t := by
  -- A solution, lifted through its clock, is an integral curve of the suspension.
  have hlift {c : ℝ → M} {u : ℝ} {S : Set ℝ}
      (h : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I c S u ((1 : ℝ →L[ℝ] ℝ).smulRight (X u (c u)))) :
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) (fun r ↦ (r, c r)) S u
        ((1 : ℝ →L[ℝ] ℝ).smulRight (timeDependentSuspensionField X (u, c u))) := by
    have hs : timeDependentSuspensionField X (u, c u) = ((1 : ℝ), X u (c u)) :=
      Prod.ext (timeDependentSuspensionField_fst _ _) (timeDependentSuspensionField_snd _ _)
    rw [hs]
    -- Both derivatives send `r` to `(r, r • X u (c u))`; the clock component on the right is
    -- `r • 1 = r * 1`.
    exact ((hasMFDerivWithinAt_id S u).prodMk h).congr_mfderiv
      (ContinuousLinearMap.ext fun r ↦ Prod.ext (mul_one (M := ℝ) r).symm rfl)
  have h₁ : IsMIntegralCurveOn (fun r ↦ (r, γ r)) (timeDependentSuspensionField X) S :=
    fun u hu ↦ hlift (hγ u hu)
  have h₂ : IsMIntegralCurveOn (fun r ↦ (r, timeDependentFlowOf X s r (γ s)))
      (timeDependentSuspensionField X) S := fun u _ ↦
    hlift (hasMFDerivAt_timeDependentFlowOf hX
      ((timeDependentFlowDomain_eq_univ hc).symm ▸ mem_univ _)).hasMFDerivWithinAt
  have heq := h₂.eqOn_of_isPreconnected h₁ hS hs
    (fun _ _ ↦ BoundarylessManifold.isInteriorPoint)
    (fun _ _ ↦ (contMDiff_timeDependentSuspensionField hX).contMDiffAt)
    (by simp [timeDependentFlowOf_self]) ht
  exact congrArg Prod.snd heq

/-- **The curves of the diffeotopy of a time-dependent field.** A differentiable curve `γ` on
`[0, 1]` whose velocity at every time `t` is `X t (γ t)`, one-sided at the ends, is the trajectory
of its initial point under the diffeotopy `TauCeti.timeDependentFlowDiffeotopy` of `X`. -/
theorem timeDependentFlowDiffeotopy_apply_eq_of_mfderiv_eq [FiniteDimensional ℝ E]
    [IsManifold I ∞ M]
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent ∞
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    (hc : IsCompleteVectorField (timeDependentSuspensionField X)) {γ : unitInterval → M}
    (hγ : MDifferentiable (𝓡∂ 1) I γ) (hγX : ∀ t, mfderiv (𝓡∂ 1) I γ t 1 = X t (γ t))
    (t : unitInterval) : timeDependentFlowDiffeotopy le_top hX hc (t, γ 0) = γ t := by
  -- The curve `γ ∘ projIcc` on `ℝ` solves the time-dependent equation on `[0, 1]`.
  have hsol (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (γ ∘ projIcc 0 1 zero_le_one) (Icc 0 1) u
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X u ((γ ∘ projIcc 0 1 zero_le_one) u))) := by
    set w : unitInterval := ⟨u, hu⟩
    have hw : projIcc 0 1 zero_le_one u = w := projIcc_of_mem _ hu
    refine (mdifferentiableWithinAt_comp_projIcc_iff (w := w).2 (hγ w)).hasMFDerivWithinAt
      |>.congr_mfderiv (ContinuousLinearMap.ext_ring ?_)
    refine (mfderivWithin_comp_projIcc_one (w := w)).trans ?_
    rw [Function.comp_apply, hw, hγX w]
    exact (one_smul ℝ _).symm
  have h := timeDependentFlowOf_eq_of_hasMFDerivWithinAt (hX.of_le (by simp)) hc
    isPreconnected_Icc hsol (s := 0) ⟨le_rfl, zero_le_one⟩ t.property
  have h0 : projIcc (0 : ℝ) 1 zero_le_one 0 = 0 := projIcc_left _
  rw [Function.comp_apply, Function.comp_apply, h0, projIcc_val] at h
  rw [timeDependentFlowDiffeotopy_apply]
  exact h

end Icc

/-! ### Restriction to an open subset -/

section Opens

open Filter Set TopologicalSpace
open scoped Topology

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [T2Space M] [BoundarylessManifold I M] {X : ℝ → (x : M) → TangentSpace I x}
  {U : Opens M} {s t : ℝ} {z : U}
  (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 1
    (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
include hX

/-- **The flow of a restricted field is the restricted flow.** Let `X` be a `C¹` time-dependent
vector field on `M` and `U` an open subset. Wherever the flow of the restriction of `X` to `U`
is defined, so is the flow of `X`, and the two agree: a trajectory in `U` is a trajectory in `M`.
-/
theorem timeDependentFlowOf_restrict_eq
    (h : ((s, t), z) ∈ timeDependentFlowDomain (M := U)
      fun u y ↦ (Manifold.tangentSpaceOpenEquiv y).symm (X u y)) :
    ((s, t), (z : M)) ∈ timeDependentFlowDomain X ∧
      (timeDependentFlowOf (M := U) (fun u y ↦ (Manifold.tangentSpaceOpenEquiv y).symm (X u y))
        s t z : M) = timeDependentFlowOf X s t z := by
  set XU : ℝ → (y : U) → TangentSpace I y :=
    fun u y ↦ (Manifold.tangentSpaceOpenEquiv y).symm (X u y)
  have hXU : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 1
      (fun p : ℝ × U ↦ (⟨p.2, XU p.1 p.2⟩ : TangentBundle I U)) :=
    Manifold.contMDiff_tangentSpaceOpenEquiv_symm (f := Prod.snd)
      (hX.comp (contMDiff_fst.prodMk (contMDiff_subtypeVal.comp contMDiff_snd)))
  obtain ⟨a, b, hs, ht, hab⟩ := exists_Ioo_of_mem_timeDependentFlowDomain h
  -- The trajectory of `XU`, read in `M`, solves the equation of `X`.
  have hγ : ∀ u ∈ Ioo a b, HasMFDerivAt 𝓘(ℝ, ℝ) I
      (fun u ↦ (timeDependentFlowOf (M := U) XU s u z : M)) u
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X u (timeDependentFlowOf (M := U) XU s u z))) := by
    intro u hu
    have h₁ := hasMFDerivAt_timeDependentFlowOf hXU (hab u hu)
    have h₂ := ((contMDiff_subtypeVal (I := I) (U := U) (n := 1)).mdifferentiableAt
      one_ne_zero (x := timeDependentFlowOf XU s u z)).hasMFDerivAt
    refine (h₂.comp u h₁).congr_mfderiv ?_
    ext
    simp only [Manifold.mfderiv_subtype_val, XU, Manifold.tangentSpaceOpenEquiv_symm_apply]
    exact Manifold.tangentSpaceOpenEquiv_apply _ _
  have hz : (timeDependentFlowOf (M := U) XU s s z : M) = z := by rw [timeDependentFlowOf_self]
  refine ⟨hz ▸ mem_timeDependentFlowDomain_of_hasMFDerivAt hγ hs ht, ?_⟩
  rw [← timeDependentFlowOf_eq_of_hasMFDerivAt hX hγ hs ht, hz]

/-- The differential of the flow of a restricted field is the differential of the flow, the
tangent spaces of `U` and `M` being identified, wherever the flow of the restriction is
defined. -/
theorem tangentSpaceOpenEquiv_mfderiv_timeDependentFlowOf_restrict [CompleteSpace E]
    (h : ((s, t), z) ∈ timeDependentFlowDomain (M := U)
      fun u y ↦ (Manifold.tangentSpaceOpenEquiv y).symm (X u y)) (v : TangentSpace I z) :
    Manifold.tangentSpaceOpenEquiv _ (mfderiv I I (timeDependentFlowOf (M := U)
      (fun u y ↦ (Manifold.tangentSpaceOpenEquiv y).symm (X u y)) s t) z v) =
      mfderiv I I (timeDependentFlowOf X s t) z (Manifold.tangentSpaceOpenEquiv z v) := by
  set XU : ℝ → (y : U) → TangentSpace I y :=
    fun u y ↦ (Manifold.tangentSpaceOpenEquiv y).symm (X u y)
  have hXU : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 1
      (fun p : ℝ × U ↦ (⟨p.2, XU p.1 p.2⟩ : TangentBundle I U)) :=
    Manifold.contMDiff_tangentSpaceOpenEquiv_symm (f := Prod.snd)
      (hX.comp (contMDiff_fst.prodMk (contMDiff_subtypeVal.comp contMDiff_snd)))
  -- Near `z`, the flow of `XU`, read in `M`, is the flow of `X`.
  have heq : Subtype.val ∘ timeDependentFlowOf XU s t =ᶠ[𝓝 z]
      timeDependentFlowOf X s t ∘ Subtype.val := by
    filter_upwards [((isOpen_timeDependentFlowDomain hXU).preimage (by fun_prop)).mem_nhds h]
      with y hy
    exact (timeDependentFlowOf_restrict_eq hX hy).2
  rw [Manifold.tangentSpaceOpenEquiv_apply, Manifold.tangentSpaceOpenEquiv_apply,
    ← Manifold.mfderiv_subtype_val_comp_apply]
  exact (congrArg (fun L ↦ L v) (heq.mfderiv_eq (I := I) (I' := I))).trans
    (Manifold.mfderiv_comp_subtype_val_apply (f := timeDependentFlowOf X s t) v)

end Opens

end TauCeti

end
