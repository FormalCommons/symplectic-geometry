/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.TimeDependent
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Tangent.Opens

/-!
# Joint smoothness of time-dependent flows, and flows on open subsets

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

## Main results

* `TauCeti.contMDiff_timeDependentFlowDiffeomorph`: the map
  `(t, x) ↦ timeDependentFlowDiffeomorph hc hn hX s t x` is `C^n` on `ℝ × M`. It is Tau Ceti's
  `TauCeti.contMDiff_timeDependentFlowOf` restricted to a fixed initial time.
* `TauCeti.timeDependentFlowOf_restrict_eq`: the flow of the restriction of `X` to `U` is defined
  only where the flow of `X` is, and agrees with it there.
* `TauCeti.tangentSpaceOpenEquiv_mfderiv_timeDependentFlowOf_restrict`: so do their differentials,
  the tangent spaces of `U` and `M` being identified.
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
