/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.TimeDependent
import TauCeti.Geometry.Manifold.Flow.Parametric
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Tangent.Opens
import TauCeti.Geometry.Manifold.IntegralCurve.Interval
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Opens
import TauCeti.Geometry.Manifold.Flow.Diffeomorph
import SymplecticGeometry.Geometry.Manifold.Diffeomorph.Prod

/-!
# Time-dependent flows: joint smoothness, uniqueness on intervals, open subsets, naturality

Let `X` be a `C^n` time-dependent vector field, `1 ≤ n`, on a finite-dimensional boundaryless
manifold `M`, whose suspension on `ℝ × M` is complete. Tau Ceti's
`TauCeti.timeDependentFlowDiffeomorph hc hn hX s t` is the flow of `X` from time `s` to time `t`,
as a `C^n` diffeomorphism of `M`. For a fixed initial time `s`, these diffeomorphisms form a
jointly `C^n` family in `(t, x)`.

For a family `X a` of time-dependent fields indexed by the points of a boundaryless manifold `N`,
jointly `C^n` in `(a, t, x)` and with complete suspensions, the flows are `C^n` in the parameter
`a` as well. The flow of `X a` from `s` to `t` is read off the flow of its suspension for time
`t - s`, and the suspensions form a jointly `C^n` family of autonomous fields on `ℝ × M`, whose
flows Tau Ceti's `TauCeti.contMDiffAt_flowOf_param` shows to be smooth in the parameter.
The proof of `TauCeti.contMDiff_timeDependentFlowOf_param` adapts that of Tau Ceti's
`TauCeti.contMDiffOn_timeDependentFlowOf` (`TauCeti/Geometry/Manifold/Flow/TimeDependent.lean`),
with `TauCeti.contMDiffAt_flowOf_param` in place of `TauCeti.contMDiffOn_flowOf`.

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
The lift of a solution through its clock is
`TauCeti.hasMFDerivWithinAt_prodMk_timeDependentSuspensionField`, and
`TauCeti.contMDiffAt_timeDependentSuspensionField` is the pointwise form of Tau Ceti's
`TauCeti.contMDiff_timeDependentSuspensionField`, whose proof, through
`TauCeti.contMDiff_const_prod_field`, it follows.

A diffeomorphism `ψ` that carries one time-dependent field to another at every time carries the
suspension of the first to that of the second through `id × ψ`
(`TauCeti.mfderiv_prodMap_id_timeDependentSuspensionField`), so Tau Ceti's naturality of
flows, `Diffeomorph.apply_flowOf` (`TauCeti/Geometry/Manifold/Flow/Diffeomorph.lean`), gives
`Diffeomorph.apply_timeDependentFlowOf`. Tau Ceti's `Diffeomorph.mem_flowDomain_apply_iff`, from
the same file, applied to the diffeomorphism `Diffeomorph.reflProdCongr ℝ ψ` of `ℝ × M` onto
`ℝ × M'`, shows that the flow domains correspond
(`Diffeomorph.mem_timeDependentFlowDomain_apply_iff`).

## Main results

* `TauCeti.contMDiff_timeDependentFlowDiffeomorph`: the map
  `(t, x) ↦ timeDependentFlowDiffeomorph hc hn hX s t x` is `C^n` on `ℝ × M`. It is Tau Ceti's
  `TauCeti.contMDiff_timeDependentFlowOf` restricted to a fixed initial time.
* `TauCeti.contMDiff_timeDependentFlowOf_param`: the time-dependent flows of a jointly `C^n`
  family of fields with complete suspensions are `C^n` in the parameter, both times and the
  initial point.
* `TauCeti.timeDependentFlowOf_restrict_eq`: the flow of the restriction of `X` to `U` is defined
  only where the flow of `X` is, and agrees with it there.
* `TauCeti.tangentSpaceOpenEquiv_mfderiv_timeDependentFlowOf_restrict`: so do their differentials,
  the tangent spaces of `U` and `M` being identified.
* `TauCeti.hasMFDerivWithinAt_prodMk_timeDependentSuspensionField` and
  `TauCeti.contMDiffAt_timeDependentSuspensionField`: a solution lifted through its clock is an
  integral curve of the suspension, and the suspension of a field `C^n` at a point is `C^n` there.
* `TauCeti.timeDependentFlowOf_eq_of_hasMFDerivWithinAt`: uniqueness of solutions on a
  preconnected set of times.
* `Diffeomorph.apply_timeDependentFlowOf`: a diffeomorphism relating two time-dependent fields
  conjugates their flows.
* `Diffeomorph.mem_timeDependentFlowDomain_apply_iff`: it maps the domain of one flow onto that of
  the other.
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

/-! ### Families of time-dependent fields -/

section Param

variable {EN HN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [CompleteSpace EN]
  [TopologicalSpace HN] {J : ModelWithCorners ℝ EN HN} [TopologicalSpace N] [ChartedSpace HN N]
  [T2Space N] [BoundarylessManifold J N]

/-- **The time-dependent flow of a family is smooth in the parameter.** Let `X a` be a family of
time-dependent vector fields on a finite-dimensional boundaryless manifold `M`, indexed by the
points `a` of a Hausdorff boundaryless manifold `N` modelled on a complete normed space, and
jointly `C^n` in `(a, t, x)`, `1 ≤ n`, such that the suspension of every `X a` is complete. Then
`(a, s, t, x) ↦ timeDependentFlowOf (X a) s t x` is `C^n`. -/
theorem contMDiff_timeDependentFlowOf_param [FiniteDimensional ℝ E] [T2Space M]
    [BoundarylessManifold I M] [IsManifold I 1 M] [IsManifold J 1 N] {n : ℕ∞} (hn : 1 ≤ n)
    [IsManifold I n M] [IsManifold J n N] {X : N → ℝ → (x : M) → TangentSpace I x}
    (hX : ContMDiff ((J.prod 𝓘(ℝ, ℝ)).prod I) I.tangent n
      (fun p : (N × ℝ) × M ↦ (⟨p.2, X p.1.1 p.1.2 p.2⟩ : TangentBundle I M)))
    (hc : ∀ a, IsCompleteVectorField (timeDependentSuspensionField (X a))) :
    ContMDiff ((J.prod (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))).prod I) I n
      (fun p : (N × ℝ × ℝ) × M ↦ timeDependentFlowOf (X p.1.1) p.1.2.1 p.1.2.2 p.2) := by
  -- The suspensions `(t, x) ↦ (1, X a t x)` form a jointly `C^n` family over `N`.
  have hclock : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ).tangent n
      (fun s : ℝ ↦ (⟨s, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
    contMDiff_vectorSpace_iff_contDiff.2 contDiff_const
  have hS (z : N × ℝ × M) :
      timeDependentSuspensionField (X z.1) z.2 = ((1 : ℝ), X z.1 z.2.1 z.2.2) :=
    Prod.ext (timeDependentSuspensionField_fst _ _) (timeDependentSuspensionField_snd _ _)
  have hv : ContMDiff (J.prod (𝓘(ℝ, ℝ).prod I)) (𝓘(ℝ, ℝ).prod I).tangent n
      (fun z : N × ℝ × M ↦ (⟨z.2, timeDependentSuspensionField (X z.1) z.2⟩ :
        TangentBundle (𝓘(ℝ, ℝ).prod I) (ℝ × M))) := by
    simp only [hS]
    exact (contMDiff_equivTangentBundleProd_symm (I := 𝓘(ℝ, ℝ)) (M := ℝ) (I' := I)
      (M' := M)).comp ((hclock.comp contMDiff_snd.fst).prodMk
        (hX.comp ((contMDiff_fst.prodMk contMDiff_snd.fst).prodMk contMDiff_snd.snd)))
  have hmap : ContMDiff ((J.prod (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))).prod I)
      (J.prod (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod I))) n
      (fun p : (N × ℝ × ℝ) × M ↦ (p.1.1, p.1.2.2 - p.1.2.1, (p.1.2.1, p.2))) :=
    contMDiff_fst.fst.prodMk ((contMDiff_fst.snd.snd.sub contMDiff_fst.snd.fst).prodMk
      (contMDiff_fst.snd.fst.prodMk contMDiff_snd))
  intro p
  -- The flow from `s` to `t` is read off the flow of the suspension for time `t - s`.
  refine (contMDiffAt_snd.comp _ ((contMDiffAt_flowOf_param
    (v := fun a ↦ timeDependentSuspensionField (X a)) hn hv
    ((hc p.1.1).mem_flowDomain (p.1.2.2 - p.1.2.1) (p.1.2.1, p.2))).comp p
      (hmap p))).congr_of_eventuallyEq (Filter.Eventually.of_forall fun q ↦ ?_)
  simp only [Function.comp_apply]
  rw [flowOf_timeDependentSuspensionField
    ((timeDependentFlowDomain_eq_univ (hc q.1.1)).symm ▸ Set.mem_univ _)]

end Param

/-! ### The suspension at a point -/

section Suspension

variable {X : ℝ → (x : M) → TangentSpace I x}

/-- **A solution lifted through its clock.** If a curve `c` solves `c' u = X u (c u)` at `u`,
with derivative within `S`, then `r ↦ (r, c r)` has at `u` the velocity of the suspension of `X`
within `S`. -/
theorem hasMFDerivWithinAt_prodMk_timeDependentSuspensionField {c : ℝ → M} {S : Set ℝ} {u : ℝ}
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

/-- The suspension of a time-dependent vector field that is jointly `C^n` at a point `p` of
`ℝ × M` is a vector field on `ℝ × M` that is `C^n` at `p`. -/
theorem contMDiffAt_timeDependentSuspensionField [IsManifold I 1 M] {n : ℕ∞ω} {p : ℝ × M}
    (hX : ContMDiffAt (𝓘(ℝ, ℝ).prod I) I.tangent n
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)) p) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I).tangent n
      (fun p : ℝ × M ↦ (⟨p, timeDependentSuspensionField X p⟩ :
        TangentBundle (𝓘(ℝ, ℝ).prod I) (ℝ × M))) p := by
  have hs : (fun p : ℝ × M ↦ (⟨p, timeDependentSuspensionField X p⟩ :
        TangentBundle (𝓘(ℝ, ℝ).prod I) (ℝ × M))) =
      fun p ↦ ⟨p, ((1 : ℝ), X p.1 p.2)⟩ :=
    funext fun p ↦ congrArg (Bundle.TotalSpace.mk p)
      (Prod.ext (timeDependentSuspensionField_fst _ _) (timeDependentSuspensionField_snd _ _))
  have hclock : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ).tangent n
      (fun s : ℝ ↦ (⟨s, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
    contMDiff_vectorSpace_iff_contDiff.2 contDiff_const
  rw [hs]
  exact (contMDiff_equivTangentBundleProd_symm (I := 𝓘(ℝ, ℝ)) (M := ℝ) (I' := I)
    (M' := M)).contMDiffAt.comp p ((hclock.comp contMDiff_fst).contMDiffAt.prodMk hX)

end Suspension

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
  have h₁ : IsMIntegralCurveOn (fun r ↦ (r, γ r)) (timeDependentSuspensionField X) S :=
    fun u hu ↦ hasMFDerivWithinAt_prodMk_timeDependentSuspensionField (hγ u hu)
  have h₂ : IsMIntegralCurveOn (fun r ↦ (r, timeDependentFlowOf X s r (γ s)))
      (timeDependentSuspensionField X) S := fun u _ ↦
    hasMFDerivWithinAt_prodMk_timeDependentSuspensionField (hasMFDerivAt_timeDependentFlowOf hX
      ((timeDependentFlowDomain_eq_univ hc).symm ▸ mem_univ _)).hasMFDerivWithinAt
  have heq := h₂.eqOn_of_isPreconnected h₁ hS hs
    (fun _ _ ↦ (contMDiff_timeDependentSuspensionField hX).contMDiffAt)
    (by simp [timeDependentFlowOf_self]) ht
  exact congrArg Prod.snd heq

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
  rw [Manifold.tangentSpaceOpenEquiv_apply, Manifold.tangentSpaceOpenEquiv_apply]
  exact Manifold.mfderiv_apply_of_subtype_val_comp_eventuallyEq heq v

end Opens

end TauCeti

/-! ### Naturality under diffeomorphisms -/

namespace Diffeomorph

open TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M'] [ChartedSpace H' M']
  {n : ℕ∞ω} {X : ℝ → (x : M) → TangentSpace I x} {Y : ℝ → (y : M') → TangentSpace I' y}

/-- If a differentiable map `ψ` carries the time-dependent vector field `X` to `Y` at every time,
then `id × ψ` carries the suspension of `X` on `ℝ × M` to that of `Y` on `ℝ × M'`. -/
theorem _root_.TauCeti.mfderiv_prodMap_id_timeDependentSuspensionField {ψ : M → M'}
    (hψ : MDifferentiable I I' ψ) (hXY : ∀ t x, mfderiv I I' ψ x (X t x) = Y t (ψ x))
    (p : ℝ × M) :
    mfderiv (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I') (Prod.map id ψ) p
      (timeDependentSuspensionField X p) = timeDependentSuspensionField Y (Prod.map id ψ p) := by
  obtain ⟨u, y⟩ := p
  have h := Manifold.mfderiv_prodMap_apply (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ)) (p := (u, y))
    mdifferentiableAt_id (hψ y) ((1 : ℝ), X u y)
  rw [Manifold.tangentSpaceProdEquiv_symm_apply, Manifold.tangentSpaceProdEquiv_symm_apply,
    mfderiv_id, hXY] at h
  exact (congrArg _ (Prod.ext (timeDependentSuspensionField_fst X (u, y))
    (timeDependentSuspensionField_snd X (u, y)))).trans (h.trans (Prod.ext
      (timeDependentSuspensionField_fst Y _).symm
      (timeDependentSuspensionField_snd Y (u, ψ y)).symm))

/-- A diffeomorphism `ψ` that carries the time-dependent vector field `X` to `Y` at every time
carries the domain of the time-dependent flow of `X` onto that of `Y`: the flow of `Y` from `s`
to `t` is defined at `ψ x` exactly when the flow of `X` from `s` to `t` is defined at `x`. -/
theorem mem_timeDependentFlowDomain_apply_iff (ψ : M ≃ₘ^n⟮I, I'⟯ M') (hn : n ≠ 0)
    (hXY : ∀ t x, mfderiv I I' ψ x (X t x) = Y t (ψ x)) {s t : ℝ} {x : M} :
    ((s, t), ψ x) ∈ timeDependentFlowDomain Y ↔ ((s, t), x) ∈ timeDependentFlowDomain X := by
  -- The diffeomorphism `id × ψ` relates the suspensions, whose flow domains give the
  -- time-dependent ones.
  have h := (ψ.reflProdCongr ℝ (J := 𝓘(ℝ, ℝ))).mem_flowDomain_apply_iff hn (t := t - s)
    (x := (s, x)) (by
      rw [coe_reflProdCongr]
      exact mfderiv_prodMap_id_timeDependentSuspensionField (ψ.mdifferentiable hn) hXY)
  rw [coe_reflProdCongr, Prod.map_apply, id_eq] at h
  rw [mem_timeDependentFlowDomain, mem_timeDependentFlowDomain, h]

variable [T2Space M'] [IsManifold I' 1 M'] [BoundarylessManifold I' M']

/-- **Naturality of time-dependent flows.** A diffeomorphism `ψ` that carries the time-dependent
vector field `X` to a `C¹` time-dependent field `Y` at every time conjugates their flows:
`ψ (φˣ_{s, t} x) = φʸ_{s, t} (ψ x)`. Outside the flow domains both sides are the junk value
`ψ x`. -/
theorem apply_timeDependentFlowOf (ψ : M ≃ₘ^n⟮I, I'⟯ M') (hn : n ≠ 0)
    (hY : ContMDiff (𝓘(ℝ, ℝ).prod I') I'.tangent 1
      (fun p : ℝ × M' ↦ (⟨p.2, Y p.1 p.2⟩ : TangentBundle I' M')))
    (hXY : ∀ t x, mfderiv I I' ψ x (X t x) = Y t (ψ x)) (s t : ℝ) (x : M) :
    ψ (timeDependentFlowOf X s t x) = timeDependentFlowOf Y s t (ψ x) := by
  -- The diffeomorphism `id × ψ` of the extended phase spaces carries one suspension to the other.
  -- The time-dependent flows are read off the flows of the suspensions.
  have h := (ψ.reflProdCongr ℝ (J := 𝓘(ℝ, ℝ))).apply_flowOf hn
    (contMDiff_timeDependentSuspensionField hY) (by
      rw [coe_reflProdCongr]
      exact mfderiv_prodMap_id_timeDependentSuspensionField (ψ.mdifferentiable hn) hXY)
    (t - s) (s, x)
  rw [coe_reflProdCongr] at h
  rw [timeDependentFlowOf_def, timeDependentFlowOf_def]
  simpa using congrArg Prod.snd h

end Diffeomorph

end
