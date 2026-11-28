/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.TimeDependent
import TauCeti.Geometry.Manifold.Flow.TimeDependent.Related
import TauCeti.Geometry.Manifold.Flow.Parametric
import TauCeti.Geometry.Manifold.ContMDiffMap.Extension
import TauCeti.Geometry.Manifold.PartitionOfUnity.Compact
public import TauCeti.Geometry.Manifold.MFDeriv.Curve
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
import TauCeti.Geometry.Manifold.IntegralCurve.Interval
import TauCeti.Geometry.Manifold.Flow.Diffeomorph
import TauCeti.Geometry.Manifold.VectorField.ModelChart
import TauCeti.Geometry.Manifold.ContMDiff.MFDeriv
import TauCeti.Geometry.Manifold.Diffeomorph.Prod
import SymplecticGeometry.Topology.VectorBundle.Basic

/-!
# Time-dependent flows: joint smoothness, uniqueness on intervals, naturality

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

Tau Ceti proves that solutions of the time-dependent equation are unique on open intervals
(`TauCeti.timeDependentFlowOf_eq_of_hasMFDerivAt`).
`TauCeti.timeDependentFlowOf_eq_of_hasMFDerivWithinAt` is the same statement on any
preconnected set of times, such as a closed interval, with derivatives within that set. Its proof
follows Tau Ceti's: both curves are lifted through their clocks to integral curves of the
suspension, and these agree by Tau Ceti's uniqueness theorem for integral curves on preconnected
sets, `IsMIntegralCurveOn.eqOn_of_isPreconnected`.
The lift of a solution through its clock is
`TauCeti.hasMFDerivWithinAt_prodMk_timeDependentSuspensionField`, at one time, and
`TauCeti.isMIntegralCurveOn_prodMk_timeDependentSuspensionField_iff`, on a set of times, where
the lift is an integral curve exactly when the curve is a solution; and
`TauCeti.contMDiffAt_timeDependentSuspensionField` is the pointwise form of Tau Ceti's
`TauCeti.contMDiff_timeDependentSuspensionField`, whose proof, through
`TauCeti.contMDiff_const_prod_field`, it follows.

A time-dependent field on `M × N` that vanishes outside a compact set and has no component along
`N` on a level `M × {y}` induces a field on `M`, to which the inclusion `x ↦ (x, y)` relates it;
by Tau Ceti's `MDifferentiable.apply_timeDependentFlowOf` the inclusion intertwines the two
flows, so the flow keeps the level (`TauCeti.timeDependentFlowOf_snd_eq_of_forall_snd_eq_zero`).

A diffeomorphism `ψ` that carries one time-dependent field to another at every time carries the
suspension of the first to that of the second through `id × ψ`
(`TauCeti.mfderiv_prodMap_id_timeDependentSuspensionField`), so Tau Ceti's naturality of
flows, `Diffeomorph.apply_flowOf` (`TauCeti/Geometry/Manifold/Flow/Diffeomorph.lean`), gives
`Diffeomorph.apply_timeDependentFlowOf`. Tau Ceti's `Diffeomorph.mem_flowDomain_apply_iff`, from
the same file, applied to the diffeomorphism
`(Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ n).prodCongrOfModels ψ` of `ℝ × M` onto
`ℝ × M'`, shows that the flow domains correspond
(`Diffeomorph.mem_timeDependentFlowDomain_apply_iff`).

A `C^(n+1)` curve `γ` that maps a closed interval into the base set of a trivialization `e` of
the tangent bundle is a trajectory, on that interval, of a jointly `C^n` time-dependent field that
vanishes outside a compact set (`Bundle.Trivialization.exists_timeDependentField_eq_curveVelocity`).
More generally, for a `C^(n+1)` family `Γ : N × ℝ → B` of curves whose curve at `a₀` maps the
interval into the base set, one family of fields, jointly `C^n` in the parameter as well, serves
for all parameters near `a₀`
(`Bundle.Trivialization.exists_timeDependentField_param_eq_curveVelocity`); a single curve is a
constant family. The velocities of the curves, read in `e`, are the tangent maps of the curves
applied to the unit vector in time, which are jointly smooth by Tau Ceti's
`ContMDiff.contMDiff_tangentMap_family`. They are multiplied by smooth cutoffs, in parameter and
time and in space, from Tau Ceti's `IsCompact.exists_contMDiff_one_nhds_tsupport_subset`, equal
to `1` near `{a₀} × [a, b]` and near its image, and mapped back by `e.symmL`, which vanishes off
the base set. Since the interval is compact, both cutoffs are `1` on the product of a
neighbourhood of `a₀` with the interval.

## Main results

* `TauCeti.contMDiff_timeDependentFlowDiffeomorph`: the map
  `(t, x) ↦ timeDependentFlowDiffeomorph hc hn hX s t x` is `C^n` on `ℝ × M`. It is Tau Ceti's
  `TauCeti.contMDiff_timeDependentFlowOf` restricted to a fixed initial time.
* `TauCeti.contMDiff_timeDependentFlowOf_param`: the time-dependent flows of a jointly `C^n`
  family of fields with complete suspensions are `C^n` in the parameter, both times and the
  initial point.
* `TauCeti.contMDiff_timeDependentFlowDiffeomorph_param`: for a fixed initial time, the flow
  diffeomorphisms of such a family are jointly `C^n` in the parameter, the final time and the
  point.
* `TauCeti.hasMFDerivWithinAt_prodMk_timeDependentSuspensionField` and
  `TauCeti.contMDiffAt_timeDependentSuspensionField`: a solution lifted through its clock is an
  integral curve of the suspension, and the suspension of a field `C^n` at a point is `C^n` there.
* `TauCeti.isMIntegralCurveOn_prodMk_timeDependentSuspensionField_iff`: a curve solves the
  equation on a set of times if and only if its lift is an integral curve of the suspension there.
* `TauCeti.timeDependentFlowOf_eq_of_hasMFDerivWithinAt`: uniqueness of solutions on a
  preconnected set of times.
* `TauCeti.timeDependentFlowOf_snd_eq_of_forall_snd_eq_zero`: a flow tangent to a level
  `M × {y}` of a product keeps it.
* `Diffeomorph.apply_timeDependentFlowOf`: a diffeomorphism relating two time-dependent fields
  conjugates their flows.
* `Diffeomorph.mem_timeDependentFlowDomain_apply_iff`: it maps the domain of one flow onto that of
  the other.
* `Bundle.Trivialization.exists_timeDependentField_eq_curveVelocity`: a compactly supported
  time-dependent field whose value along a curve, on a closed interval, is its velocity.
* `Bundle.Trivialization.exists_timeDependentField_param_eq_curveVelocity`: the same for the
  curves of a family near a given parameter, with fields that depend smoothly on the parameter.
-/

public section

open scoped Manifold ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-- The suspension of `X` at `(t, x)` is `(1, X t x)`. -/
theorem timeDependentSuspensionField_apply (X : ℝ → (x : M) → TangentSpace I x) (p : ℝ × M) :
    timeDependentSuspensionField X p = ((1 : ℝ), X p.1 p.2) :=
  Prod.ext (timeDependentSuspensionField_fst X p) (timeDependentSuspensionField_snd X p)

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
  have hv : ContMDiff (J.prod (𝓘(ℝ, ℝ).prod I)) (𝓘(ℝ, ℝ).prod I).tangent n
      (fun z : N × ℝ × M ↦ (⟨z.2, timeDependentSuspensionField (X z.1) z.2⟩ :
        TangentBundle (𝓘(ℝ, ℝ).prod I) (ℝ × M))) := by
    simp only [timeDependentSuspensionField_apply]
    exact (contMDiff_equivTangentBundleProd_symm (I := 𝓘(ℝ, ℝ)) (M := ℝ) (I' := I)
      (M' := M)).comp (((contMDiff_tangentBundle_mk_const (1 : ℝ)).comp contMDiff_snd.fst).prodMk
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
    (mem_timeDependentFlowDomain.2 ((hc q.1.1).mem_flowDomain _ _))]

/-- **The flow diffeomorphisms of a family are jointly smooth.** For a family `X a` of
time-dependent vector fields as in `TauCeti.contMDiff_timeDependentFlowOf_param`, jointly `C^n`
in `(a, t, x)`, `1 ≤ n`, with complete suspensions, and an initial time `s`, the map
`(a, t, x) ↦ timeDependentFlowDiffeomorph … s t x`, the flow of `X a` from `s` to `t` applied
to `x`, is `C^n`. -/
theorem contMDiff_timeDependentFlowDiffeomorph_param [FiniteDimensional ℝ E] [T2Space M]
    [BoundarylessManifold I M] [IsManifold I 1 M] [IsManifold J 1 N] {n : ℕ∞} (hn : 1 ≤ n)
    [IsManifold I n M] [IsManifold J n N] {X : N → ℝ → (x : M) → TangentSpace I x}
    (hX : ContMDiff ((J.prod 𝓘(ℝ, ℝ)).prod I) I.tangent n
      (fun p : (N × ℝ) × M ↦ (⟨p.2, X p.1.1 p.1.2 p.2⟩ : TangentBundle I M)))
    (hc : ∀ a, IsCompleteVectorField (timeDependentSuspensionField (X a))) (s : ℝ) :
    ContMDiff (J.prod (𝓘(ℝ, ℝ).prod I)) I n (fun p : N × ℝ × M ↦
      timeDependentFlowDiffeomorph (hc p.1) hn
        (hX.comp ((contMDiff_const (c := p.1).prodMk contMDiff_fst).prodMk contMDiff_snd))
        s p.2.1 p.2.2) :=
  (contMDiff_timeDependentFlowOf_param hn hX hc).comp
    ((contMDiff_fst.prodMk ((contMDiff_const (c := s)).prodMk contMDiff_snd.fst)).prodMk
      contMDiff_snd.snd) |>.congr fun _ ↦ timeDependentFlowDiffeomorph_apply ..

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
  rw [timeDependentSuspensionField_apply]
  -- Both derivatives send `r` to `(r, r • X u (c u))`; the clock component on the right is
  -- `r • 1 = r * 1`.
  exact ((hasMFDerivWithinAt_id S u).prodMk h).congr_mfderiv
    (ContinuousLinearMap.ext fun r ↦ Prod.ext (mul_one (M := ℝ) r).symm rfl)

/-- **Solutions on a set are integral curves of the suspension.** A curve `c` solves
`c' u = X u (c u)` at every `u ∈ S`, with derivatives within `S`, if and only if
`r ↦ (r, c r)` is an integral curve on `S` of the suspension of `X`. -/
theorem isMIntegralCurveOn_prodMk_timeDependentSuspensionField_iff {c : ℝ → M} {S : Set ℝ} :
    IsMIntegralCurveOn (fun r ↦ (r, c r)) (timeDependentSuspensionField X) S ↔
      ∀ u ∈ S, HasMFDerivWithinAt 𝓘(ℝ, ℝ) I c S u ((1 : ℝ →L[ℝ] ℝ).smulRight (X u (c u))) := by
  refine ⟨fun h u hu ↦ ?_, fun h u hu ↦
    hasMFDerivWithinAt_prodMk_timeDependentSuspensionField (h u hu)⟩
  -- The second component of the lift is `c`, and that of the suspension is `X`.
  exact ((hasMFDerivAt_snd (u, c u)).comp_hasMFDerivWithinAt u (h u hu)).congr_mfderiv
    (ContinuousLinearMap.ext fun r : ℝ ↦ congrArg (r • ·) (timeDependentSuspensionField_snd X _))

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
      (timeDependentSuspensionField_apply X p)
  rw [hs]
  exact (contMDiff_equivTangentBundleProd_symm (I := 𝓘(ℝ, ℝ)) (M := ℝ) (I' := I)
    (M' := M)).contMDiffAt.comp p
      (((contMDiff_tangentBundle_mk_const (1 : ℝ)).comp contMDiff_fst).contMDiffAt.prodMk hX)

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
    isMIntegralCurveOn_prodMk_timeDependentSuspensionField_iff.2 hγ
  have h₂ : IsMIntegralCurveOn (fun r ↦ (r, timeDependentFlowOf X s r (γ s)))
      (timeDependentSuspensionField X) S := fun u _ ↦
    hasMFDerivWithinAt_prodMk_timeDependentSuspensionField (hasMFDerivAt_timeDependentFlowOf hX
      (mem_timeDependentFlowDomain.2 (hc.mem_flowDomain _ _))).hasMFDerivWithinAt
  have heq := h₂.eqOn_of_isPreconnected h₁ hS hs
    (fun _ _ ↦ (contMDiff_timeDependentSuspensionField hX).contMDiffAt)
    (by simp [timeDependentFlowOf_self]) ht
  exact congrArg Prod.snd heq

end Icc

/-! ### Flows that keep a level of a product -/

section Level

variable {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  [CompleteSpace E] [T2Space M] [T2Space N] [IsManifold I 1 M] [IsManifold J 1 N]
  [BoundarylessManifold I M] [BoundarylessManifold J N]

/-- **A flow tangent to a level of a product keeps it.** Let `X` be a `C¹` time-dependent vector
field on `M × N` that vanishes, at every time, outside a fixed compact set. If at every time `X`
has no component along `N` at the points of the level `M × {y}`, then the time-dependent flow of
`X` between any two times keeps `M × {y}`. -/
theorem timeDependentFlowOf_snd_eq_of_forall_snd_eq_zero
    {X : ℝ → (p : M × N) → TangentSpace (I.prod J) p}
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod (I.prod J)) (I.prod J).tangent 1
      (fun p : ℝ × (M × N) ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle (I.prod J) (M × N))))
    {K : Set (M × N)} (hK : IsCompact K) (hXK : ∀ u, ∀ p ∉ K, X u p = 0) {y : N}
    (hy : ∀ u x, (X u (x, y)).2 = 0) (s t : ℝ) (x : M) :
    (timeDependentFlowOf X s t (x, y)).2 = y := by
  -- The field on `M` that `X` induces on the level `M × {y}`.
  set Z : ℝ → (x : M) → TangentSpace I x := fun u x ↦ (X u (x, y)).1
  have hZ : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 1
      (fun p : ℝ × M ↦ (⟨p.2, Z p.1 p.2⟩ : TangentBundle I M)) :=
    contMDiff_fst.comp ((contMDiff_equivTangentBundleProd (I := I) (M := M) (I' := J)
      (M' := N)).comp (hX.comp (contMDiff_fst.prodMk (contMDiff_snd.prodMk contMDiff_const))))
  have hcZ : IsCompleteVectorField (timeDependentSuspensionField Z) :=
    isCompleteVectorField_timeDependentSuspensionField hZ (hK.image continuous_fst)
      fun u x hx ↦ by
        simp only [Z, hXK u (x, y) fun h ↦ hx ⟨_, h, rfl⟩]
        exact Prod.fst_zero
  -- `x ↦ (x, y)` carries `Z` to `X`, so it intertwines their flows.
  have h := MDifferentiable.apply_timeDependentFlowOf (f := fun x : M ↦ (x, y))
    (mdifferentiable_id.prodMk mdifferentiable_const) hZ hX
    (fun u x ↦ by rw [mfderiv_prod_left]; exact Prod.ext rfl (hy u x).symm)
    (mem_timeDependentFlowDomain.2 (hcZ.mem_flowDomain _ _)) (s := s) (t := t) (x := x)
  rw [← h]

end Level

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
  exact (congrArg _ (timeDependentSuspensionField_apply X (u, y))).trans
    (h.trans (timeDependentSuspensionField_apply Y (u, ψ y)).symm)

/-- A diffeomorphism `ψ` that carries the time-dependent vector field `X` to `Y` at every time
carries the domain of the time-dependent flow of `X` onto that of `Y`: the flow of `Y` from `s`
to `t` is defined at `ψ x` exactly when the flow of `X` from `s` to `t` is defined at `x`. -/
theorem mem_timeDependentFlowDomain_apply_iff (ψ : M ≃ₘ^n⟮I, I'⟯ M') (hn : n ≠ 0)
    (hXY : ∀ t x, mfderiv I I' ψ x (X t x) = Y t (ψ x)) {s t : ℝ} {x : M} :
    ((s, t), ψ x) ∈ timeDependentFlowDomain Y ↔ ((s, t), x) ∈ timeDependentFlowDomain X := by
  -- The diffeomorphism `id × ψ` relates the suspensions, whose flow domains give the
  -- time-dependent ones.
  have h := ((Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ n).prodCongrOfModels ψ).mem_flowDomain_apply_iff hn
    (t := t - s) (x := (s, x)) (by
      rw [coe_prodCongrOfModels, coe_refl]
      exact mfderiv_prodMap_id_timeDependentSuspensionField (ψ.mdifferentiable hn) hXY)
  rw [coe_prodCongrOfModels, coe_refl, Prod.map_apply, id_eq] at h
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
  have h := ((Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ n).prodCongrOfModels ψ).apply_flowOf hn
    (contMDiff_timeDependentSuspensionField hY) (by
      rw [coe_prodCongrOfModels, coe_refl]
      exact mfderiv_prodMap_id_timeDependentSuspensionField (ψ.mdifferentiable hn) hXY)
    (t - s) (s, x)
  rw [coe_prodCongrOfModels, coe_refl] at h
  rw [timeDependentFlowOf_def, timeDependentFlowOf_def]
  simpa using congrArg Prod.snd h

end Diffeomorph

namespace Bundle.Trivialization

open Function Set Filter TauCeti TauCeti.Manifold
open scoped Topology

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {B : Type*} [TopologicalSpace B] [ChartedSpace G B] [IsManifold J ∞ B] [T2Space B]
  {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [FiniteDimensional ℝ EN]
  {HN : Type*} [TopologicalSpace HN] {IN : ModelWithCorners ℝ EN HN}
  {N : Type*} [TopologicalSpace N] [ChartedSpace HN N] [IsManifold IN ∞ N] [T2Space N]

/-- **A compactly supported field through the velocities of a family of curves.** Let
`Γ : N × ℝ → B` be a `C^(n+1)` family of curves in `B`, with parameters in a
finite-dimensional Hausdorff manifold `N`, whose curve at `a₀` maps `Set.Icc a b` into the base
set of a trivialization `e` of the tangent bundle of `B`. There are a neighbourhood `U` of `a₀`
and a family `V c` of time-dependent vector fields on `B`, jointly `C^n` in parameter, time
and point, vanishing outside one compact set `K`, such that for `c ∈ U` and `u ∈ Set.Icc a b`
the value of `V c u` at `Γ (c, u)` is the velocity at `u` of the curve `r ↦ Γ (c, r)`. -/
theorem exists_timeDependentField_param_eq_curveVelocity {n : ℕ∞} {Γ : N × ℝ → B}
    (e : Trivialization F (π F (TangentSpace J))) [MemTrivializationAtlas e]
    (hΓ : ContMDiff (IN.prod 𝓘(ℝ, ℝ)) J (n + 1) Γ) {a₀ : N} {a b : ℝ}
    (hΓe : MapsTo (fun u ↦ Γ (a₀, u)) (Icc a b) e.baseSet) :
    ∃ U ∈ 𝓝 a₀, ∃ (V : N → ℝ → Π y : B, TangentSpace J y) (K : Set B), IsCompact K ∧
      ContMDiff ((IN.prod 𝓘(ℝ, ℝ)).prod J) J.tangent n
        (fun p : (N × ℝ) × B ↦ (⟨p.2, V p.1.1 p.1.2 p.2⟩ : TangentBundle J B)) ∧
      (∀ c u, ∀ y ∉ K, V c u y = 0) ∧
      ∀ c ∈ U, ∀ u ∈ Icc a b, V c u (Γ (c, u)) = curveVelocity J (fun r ↦ Γ (c, r)) u := by
  have hC : IsCompact ({a₀} ×ˢ Icc a b) := isCompact_singleton.prod isCompact_Icc
  have hCO : {a₀} ×ˢ Icc a b ⊆ Γ ⁻¹' e.baseSet := by
    rintro ⟨c, u⟩ ⟨hc, hu⟩
    obtain rfl : c = a₀ := mem_singleton_iff.1 hc
    exact hΓe hu
  -- Cut-offs in the parameters and time, and in space.
  obtain ⟨χ, hχ, hχ1, -, hχO, -⟩ := hC.exists_contMDiff_one_nhds_tsupport_subset
    (IN.prod 𝓘(ℝ, ℝ)) (e.open_baseSet.preimage hΓ.continuous) hCO
  obtain ⟨ψ, hψ, hψ1, hψc, hψU, -⟩ := (hC.image hΓ.continuous
    ).exists_contMDiff_one_nhds_tsupport_subset J e.open_baseSet (image_subset_iff.2 hCO)
  -- Both are `1` on a tube around `{a₀} × Icc a b`.
  obtain ⟨U, hU, T, hT, hUT⟩ := mem_prod_iff.1 (by
    rw [← isCompact_singleton.nhdsSet_prod_eq isCompact_Icc]
    exact hχ1.and ((hΓ.continuous.tendsto_nhdsSet (mapsTo_image Γ _)).eventually hψ1) :
      {p : N × ℝ | χ p = 1 ∧ ψ (Γ p) = 1} ∈ 𝓝ˢ {a₀} ×ˢ 𝓝ˢ (Icc a b))
  -- The velocities of the curves of the family, as a map to the tangent bundle.
  have hvel : ContMDiff (IN.prod 𝓘(ℝ, ℝ)) J.tangent n
      (fun p : N × ℝ ↦ (⟨Γ p, curveVelocity J (fun r ↦ Γ (p.1, r)) p.2⟩ : TangentBundle J B)) :=
    have : IsManifold IN (n + 1) N := .of_le (n := ∞) (by exact_mod_cast le_top)
    (ContMDiff.contMDiff_tangentMap_family (f := fun c r ↦ Γ (c, r)) hΓ le_rfl).comp
      (contMDiff_fst.prodMk ((contMDiff_tangentBundle_mk_const (1 : ℝ)).comp contMDiff_snd))
      |>.congr fun p ↦ by simp [tangentMap, curveVelocity_apply]
  -- The velocities read in `e`, cut off in the parameter and time.
  let v : N × ℝ → F := fun p ↦ (e ⟨Γ p, curveVelocity J (fun r ↦ Γ (p.1, r)) p.2⟩).2
  have hv {p : N × ℝ} (hp : Γ p ∈ e.baseSet) :
      ContMDiffAt (IN.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F) n v p :=
    ((e.contMDiffAt_iff (e.mem_source.2 hp)).1 (hvel p)).2
  let w : N × ℝ → F := fun p ↦ χ p • v p
  have hw : ContMDiff (IN.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F) n w :=
    ContMDiffOn.contMDiff_smul_of_tsupport_subset (fun p hp ↦ (hv hp).contMDiffWithinAt)
      (e.open_baseSet.preimage hΓ.continuous)
      (hχ.of_le (by exact_mod_cast le_top)).contMDiffOn hχO
  -- The field read in `e` as `ψ y • w (c, u)`, which `ψ` cuts off in space.
  let V : N → ℝ → Π y : B, TangentSpace J y := fun c u y ↦ e.symmL ℝ y (ψ y • w (c, u))
  have hV0 {c : N} {u : ℝ} {y : B} (hy : y ∉ tsupport ψ) : V c u y = 0 := by
    simp only [V, image_eq_zero_of_notMem_tsupport hy, zero_smul, map_zero]
  refine ⟨U, nhdsSet_singleton (x := a₀) ▸ hU, V, tsupport ψ, hψc, ?_, fun c u y hy ↦ hV0 hy,
    fun c hc u hu ↦ ?_⟩
  · rintro ⟨q₀, y₀⟩
    by_cases hy₀ : y₀ ∈ e.baseSet
    · have hsm : ContMDiffAt ((IN.prod 𝓘(ℝ, ℝ)).prod J) 𝓘(ℝ, F) n
          (fun p : (N × ℝ) × B ↦ (e (⟨p.2, V p.1.1 p.1.2 p.2⟩ : TangentBundle J B)).2)
          (q₀, y₀) := by
        refine ((((hψ.of_le (by exact_mod_cast le_top)) y₀).comp (q₀, y₀) contMDiffAt_snd).smul
          ((hw q₀).comp (q₀, y₀) contMDiffAt_fst)).congr_of_eventuallyEq ?_
        filter_upwards [continuousAt_snd.preimage_mem_nhds (e.open_baseSet.mem_nhds hy₀)]
          with p hp
        simp only [V, e.symmL_apply hp, e.apply_mk_symm hp, Pi.smul_apply', comp_apply]
      exact (e.contMDiffAt_iff (e.mem_source.2 hy₀)).2 ⟨contMDiffAt_snd, hsm⟩
    · -- Off the base set, `ψ` vanishes nearby and so does the field.
      have hy : y₀ ∉ tsupport ψ := fun h ↦ hy₀ (hψU h)
      refine (((contMDiff_zeroSection _ _).contMDiffAt).comp (q₀, y₀)
        contMDiffAt_snd).congr_of_eventuallyEq ?_
      filter_upwards [continuousAt_snd.preimage_mem_nhds
        ((isClosed_tsupport ψ).isOpen_compl.mem_nhds hy)] with p hp
      simp [zeroSection_def, hV0 hp]
  · obtain ⟨hχ1, hψ1⟩ := hUT (mk_mem_prod hc (subset_of_mem_nhdsSet hT hu))
    have hb : Γ (c, u) ∈ e.baseSet :=
      hχO (subset_tsupport _ (by simp [hχ1] : χ (c, u) ≠ 0))
    simp only [V, w, v, hψ1, hχ1, one_smul, e.symmL_apply hb]
    exact e.symm_apply_apply_mk hb _

/-- **A compactly supported field through the velocities of a curve.** Let `γ` be a `C^(n+1)`
curve in `B` that maps `Set.Icc a b` into the base set of a trivialization `e` of the tangent
bundle of `B`. There is a time-dependent vector field `V` on `B`, jointly `C^n` in time and point,
that vanishes outside a compact set `K` at all times and whose value at `γ u` at time `u` is the
velocity of `γ` at `u`, for every `u ∈ Set.Icc a b`. -/
theorem exists_timeDependentField_eq_curveVelocity {n : ℕ∞} {γ : ℝ → B}
    (e : Trivialization F (π F (TangentSpace J))) [MemTrivializationAtlas e]
    (hγ : ContMDiff 𝓘(ℝ, ℝ) J (n + 1) γ) {a b : ℝ} (hγe : MapsTo γ (Icc a b) e.baseSet) :
    ∃ (V : ℝ → Π y : B, TangentSpace J y) (K : Set B), IsCompact K ∧
      ContMDiff (𝓘(ℝ, ℝ).prod J) J.tangent n
        (fun p : ℝ × B ↦ (⟨p.2, V p.1 p.2⟩ : TangentBundle J B)) ∧
      (∀ u, ∀ y ∉ K, V u y = 0) ∧ ∀ u ∈ Icc a b, V u (γ u) = curveVelocity J γ u := by
  -- The constant family of curves `(c, u) ↦ γ u`, with parameters in `ℝ`.
  obtain ⟨U, hU, V, K, hK, hV, hV0, hVγ⟩ := e.exists_timeDependentField_param_eq_curveVelocity
    (IN := 𝓘(ℝ, ℝ)) (Γ := fun p : ℝ × ℝ ↦ γ p.2) (hγ.comp contMDiff_snd) (a₀ := 0) hγe
  exact ⟨V 0, K, hK, hV.comp ((contMDiff_const.prodMk contMDiff_fst).prodMk contMDiff_snd),
    hV0 0, hVγ 0 (mem_of_mem_nhds hU)⟩

end Bundle.Trivialization

end
