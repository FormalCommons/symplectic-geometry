/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Collar.Local
public import TauCeti.Geometry.Manifold.Boundary.Derivative
public import TauCeti.Geometry.Manifold.Boundary.InwardFlow
public import TauCeti.Geometry.Manifold.Boundary.Orientation
public import TauCeti.Geometry.Manifold.MFDeriv.Curve
public import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
public import TauCeti.Geometry.Manifold.VectorField.Regularity
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Boundary
import SymplecticGeometry.Analysis.Calculus.FDeriv.Uncurry
import SymplecticGeometry.Geometry.Manifold.Boundary.Charts
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.Basic
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Chart

/-!
# The flow of an outward field near a boundary point

Let `W` be a manifold modelled on the half-space `𝓡∂ (n + 1)` and `Y` a smooth vector field on
`W` that points out of `W` along its boundary (`TauCeti.IsOutwardPointingField`). Integral curves
of `Y` cannot start at a boundary point and go forward, but they can go backward, into the
interior. This file constructs them near a boundary point `p`.

In the extended chart `φ` at `p`, the field `Y` reads as a smooth map `f` on the chart target, a
relatively open part of the half-space `{y | 0 ≤ y 0}`, and its zeroth coordinate is negative at
`φ p`. Tau Ceti's `TauCeti.exists_contDiffOn_localFlow_euclideanHalfSpace`, applied to the inward
field `-f`, gives a smooth local flow `Ψ` near `φ p`, with `Ψ x 0 = x`, whose zeroth coordinate
strictly increases in time and whose forward curves from the half-space are integral curves of
`-f` in the chart target. So a curve `t ↦ Ψ x t` from a point `x` of the boundary hyperplane is in
the open half-space exactly at positive times, and `s ↦ φ⁻¹ (Ψ x (-s))` is an integral curve of
`Y` on `(-η, 0]`, in the interior of `W` at negative times. Tau Ceti's manifold form,
`TauCeti.exists_contMDiffOn_localFlow_of_isOutwardPointing_neg`, gives these curves too, but not
their chart expression, which the local diffeomorphism below needs.

Written in the boundary chart at `p`, the flow from the boundary is the map
`G (z, τ) = Ψ (z inserted as a point with zeroth coordinate 0) (τ 0)` between open subsets of
`ℝⁿ × ℝ¹` and `ℝⁿ⁺¹`. At `(z₀, 0)`, `z₀` the boundary chart reading of `p`, its derivative sends
`(u, σ)` to `σ 0 • v` plus `u` inserted with zeroth coordinate `0`, where `v = -f (φ p)` is the
velocity of `t ↦ Ψ (φ p) t` at `0`, since `Ψ x 0 = x`
(`DifferentiableAt.hasFDerivAt_uncurry_zero`). It is invertible since `v` is transverse
to the boundary hyperplane, so by the inverse function theorem in the boundaryless spaces `G` is
a local diffeomorphism there
(`TauCeti.isLocalDiffeomorphAt_euclideanHalfSpaceBoundaryParam_of_hasDerivAt`). This adapts the
proof of Tau Ceti's flow-out theorem `TauCeti.isLocalDiffeomorph_globalFlow_comp` (with its
differential `TauCeti.mfderiv_globalFlow_comp_apply`) at time zero, with the linear inclusion of
the hyperplane in place of an immersion; see also Lee, Theorem 9.20. Near that point `G` sends
`ℝⁿ × [0, ∞)` exactly into the half-space, by the monotonicity of the zeroth coordinate, so it
restricts to a local diffeomorphism of the half-space models (Tau Ceti's
`TauCeti.PartialDiffeomorph.ofOpenPartialHomeomorphOfMemRangeIff`), and in the charts of
`∂W × [0, ∞)` and `W` this is the map `(x, t) ↦ γ (-t, x)`.

These curves need no uniqueness result here: Tau Ceti's
`IsMIntegralCurveOn.eqOn_of_isPreconnected` holds for curves that may meet the boundary, so two
integral curves of a smooth field on `(-η, 0]` that agree at time `0` agree.
An integral curve of an outward field stays in the interior at times from which it is defined for
a while forward, since its velocity there within `[t, ∞)` would be outward, which Tau Ceti's
`TauCeti.not_isOutwardPointing_curveVelocityWithin_Ici` rules out
(`IsMIntegralCurveOn.mem_interior_of_isOutwardPointing`).

## Main results

* `TauCeti.isLocalDiffeomorphAt_euclideanHalfSpaceBoundaryParam_of_hasDerivAt`: a smooth family
  `Ψ x t` with `Ψ x 0 = x` whose velocity at time `0` is transverse to the boundary hyperplane is,
  out of that hyperplane, a local diffeomorphism.
* `TauCeti.exists_isMIntegralCurveOn_of_isOutwardPointing`: integral curves of an outward field
  entering from the boundary near `p`, forming a local diffeomorphism `∂W × [0, η) → W`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218, 2013,
  Chapter 9 (flows; the flow-out theorem 9.20, and the collar theorem 9.25 that this file
  prepares).
* M. Hirsch, *Differential Topology*, Springer GTM 33, 1976, Chapter 4, Theorem 6.1.
-/

public section

open Set Filter Function Topology VectorField SymplecticGeometry
open scoped Manifold ContDiff

namespace TauCeti

variable {n : ℕ} {W : Type*} [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
  {Y : (x : W) → TangentSpace (𝓡∂ (n + 1)) x}

/-- An integral curve of a vector field that points outward along the boundary is in the interior
at every time `t` of its domain `s` from which it is defined for a while forward, that is with
`s ∈ 𝓝[≥] t`. -/
theorem _root_.IsMIntegralCurveOn.mem_interior_of_isOutwardPointing
    (hY : ∀ x ∈ (𝓡∂ (n + 1)).boundary W, IsOutwardPointing x (Y x)) {γ : ℝ → W} {s : Set ℝ}
    (hγ : IsMIntegralCurveOn γ Y s) {t : ℝ} (hs : s ∈ 𝓝[≥] t) :
    γ t ∈ (𝓡∂ (n + 1)).interior W := by
  rw [← ModelWithCorners.compl_boundary]
  intro hb
  -- The velocity of `γ` at `t` within `[t, ∞)` is `Y (γ t)`, which is outward, but no curve
  -- running forward from `t` has an outward velocity there.
  apply not_isOutwardPointing_curveVelocityWithin_Ici (n := n) γ t
  rw [Manifold.curveVelocityWithin_eq_of_hasMFDerivWithinAt
    ((hγ t (mem_of_mem_nhdsWithin self_mem_Ici hs)).mono_of_mem_nhdsWithin hs)
    (uniqueDiffOn_Ici t t self_mem_Ici)]
  exact hY _ hb

variable [IsManifold (𝓡∂ (n + 1)) ∞ W]

section Param

variable {Ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ → EuclideanSpace ℝ (Fin (n + 1))}

/-- Let `Ψ x t` be a family of points of `ℝⁿ⁺¹` with `Ψ x 0 = x`, smooth on a neighbourhood of
`(y₀, 0)`, where `y₀` is the point `z₀ ∈ ℝⁿ` of the boundary hyperplane, such that the curve
`t ↦ Ψ y₀ t` has at time `0` a velocity `v` with `v 0 ≠ 0`. Then
`(z, τ) ↦ Ψ (z in the hyperplane) (τ 0)` on `ℝⁿ × ℝ¹` is a local diffeomorphism at `(z₀, 0)`. -/
theorem isLocalDiffeomorphAt_euclideanHalfSpaceBoundaryParam_of_hasDerivAt
    {z₀ : EuclideanSpace ℝ (Fin n)}
    {S : Set (EuclideanSpace ℝ (Fin (n + 1)) × ℝ)}
    (hS : S ∈ 𝓝 (euclideanHalfSpaceBoundaryParam n z₀, 0))
    (hΨ : ContDiffOn ℝ ∞ (fun p : EuclideanSpace ℝ (Fin (n + 1)) × ℝ ↦ Ψ p.1 p.2) S)
    (hΨ0 : ∀ x, Ψ x 0 = x) {v : EuclideanSpace ℝ (Fin (n + 1))}
    (hv : HasDerivAt (Ψ (euclideanHalfSpaceBoundaryParam n z₀)) v 0) (hv0 : v 0 ≠ 0) :
    IsLocalDiffeomorphAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞
      (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1) ↦
        Ψ (euclideanHalfSpaceBoundaryParam n q.1) (q.2 0)) (z₀, 0) := by
  set ι := euclideanHalfSpaceBoundaryParam n
  set F := fun p : EuclideanSpace ℝ (Fin (n + 1)) × ℝ ↦ Ψ p.1 p.2
  set L : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1) →L[ℝ]
      EuclideanSpace ℝ (Fin (n + 1)) × ℝ :=
    (ι.comp (ContinuousLinearMap.fst ℝ _ _)).prod
      ((PiLp.proj 2 (fun _ : Fin 1 ↦ ℝ) 0).comp (ContinuousLinearMap.snd ℝ _ _))
  have hLz₀ : L (z₀, 0) = (ι z₀, 0) := by
    simp [L]
  -- The derivative `D` of `F` at `(ι z₀, 0)` is the identity in space and `v` in time.
  set D : EuclideanSpace ℝ (Fin (n + 1)) × ℝ →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
    ContinuousLinearMap.fst ℝ _ ℝ + (ContinuousLinearMap.snd ℝ _ ℝ).smulRight v
  have hD : HasFDerivAt F D (ι z₀, 0) :=
    ((hΨ.contDiffAt hS).differentiableAt (by simp)).hasFDerivAt_uncurry_zero
      (Eventually.of_forall hΨ0) hv
  have hDapply (u : EuclideanSpace ℝ (Fin (n + 1))) (σ : ℝ) : D (u, σ) = u + σ • v := by
    simp [D]
  -- So the derivative of `F ∘ L` at `(z₀, 0)` is injective, since `v` leaves the hyperplane.
  have hinj : Injective (D.comp L) := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨dz, dτ⟩ h
    simp only [L, ContinuousLinearMap.coe_comp, comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', PiLp.proj_apply, hDapply] at h
    have h0 := congrArg (fun y : EuclideanSpace ℝ (Fin (n + 1)) ↦ y 0) h
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, ι,
      euclideanHalfSpaceBoundaryParam_apply_zero, zero_add, PiLp.zero_apply, mul_eq_zero, hv0,
      or_false] at h0
    have hτ : dτ = 0 := by
      ext i
      fin_cases i
      simpa using h0
    rw [h0, zero_smul, add_zero] at h
    have hz : dz = 0 := euclideanHalfSpaceBoundaryParam_injective n (by simpa [ι] using h)
    simp [hz, hτ]
  set D' := L ⁻¹' interior S
  have hD' : IsOpen D' := isOpen_interior.preimage L.continuous
  have hz₀D' : (z₀, (0 : EuclideanSpace ℝ (Fin 1))) ∈ D' := by
    simp only [D', mem_preimage, hLz₀]
    exact mem_interior_iff_mem_nhds.2 hS
  have hGs : ContDiffOn ℝ ∞ (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1) ↦
      Ψ (ι q.1) (q.2 0)) D' :=
    (hΨ.mono interior_subset).comp L.contDiff.contDiffOn fun _ hq ↦ hq
  have hGd : HasFDerivAt (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1) ↦
      Ψ (ι q.1) (q.2 0)) (D.comp L) (z₀, 0) := by
    rw [← hLz₀] at hD
    exact hD.comp (z₀, 0) L.hasFDerivAt
  exact isLocalDiffeomorphAt_of_injective_mfderiv (contMDiffOn_iff_contDiffOn.2 hGs) hD' hz₀D'
      BoundarylessManifold.isInteriorPoint (by simp)
      (by rwa [mfderiv_eq_fderiv, hGd.fderiv]) (by simp)

/-- Under the hypotheses of `isLocalDiffeomorphAt_euclideanHalfSpaceBoundaryParam_of_hasDerivAt`,
the map `(z, τ) ↦ Ψ z τ` from the boundary hyperplane agrees near `(z₀, 0)`, and inside a given
open set `R`, with a partial diffeomorphism `Θ` that sends a point of its source into the
half-space exactly when the point lies in `ℝⁿ × [0, ∞)`, provided that this holds for the map
on `R`. -/
private theorem exists_partialDiffeomorph_boundaryParam {z₀ : EuclideanSpace ℝ (Fin n)}
    {S : Set (EuclideanSpace ℝ (Fin (n + 1)) × ℝ)}
    (hS : S ∈ 𝓝 (euclideanHalfSpaceBoundaryParam n z₀, 0))
    (hΨ : ContDiffOn ℝ ∞ (fun p : EuclideanSpace ℝ (Fin (n + 1)) × ℝ ↦ Ψ p.1 p.2) S)
    (hΨ0 : ∀ x, Ψ x 0 = x) {v : EuclideanSpace ℝ (Fin (n + 1))}
    (hv : HasDerivAt (Ψ (euclideanHalfSpaceBoundaryParam n z₀)) v 0) (hv0 : v 0 ≠ 0)
    {R : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1))} (hR : IsOpen R)
    (hz₀R : (z₀, 0) ∈ R)
    (hsign : ∀ q ∈ R, 0 ≤ Ψ (euclideanHalfSpaceBoundaryParam n q.1) (q.2 0) 0 ↔ 0 ≤ q.2 0) :
    ∃ Θ : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1))
        𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1))
        (EuclideanSpace ℝ (Fin (n + 1))) ∞,
      (z₀, 0) ∈ Θ.source ∧ Θ.source ⊆ R ∧
      (∀ q ∈ Θ.source, Θ q = Ψ (euclideanHalfSpaceBoundaryParam n q.1) (q.2 0)) ∧
      ∀ q ∈ Θ.source, Θ q ∈ range (𝓡∂ (n + 1)) ↔ q ∈ range ((𝓡 n).prod (𝓡∂ 1)) := by
  obtain ⟨Θ, hΘ0, hΘR, hGΘ⟩ := IsLocalDiffeomorphAt.exists_partialDiffeomorph_eqOn
    (isLocalDiffeomorphAt_euclideanHalfSpaceBoundaryParam_of_hasDerivAt hS hΨ hΨ0 hv hv0) hR hz₀R
  refine ⟨Θ, hΘ0, hΘR, fun q hq ↦ (hGΘ hq).symm, ?_⟩
  rintro ⟨z, τ⟩ hq
  rw [← hGΘ hq, ModelWithCorners.range_prod, range_modelWithCornersEuclideanHalfSpace,
    range_modelWithCornersEuclideanHalfSpace]
  simp only [mem_ofPred_eq, mem_prod, modelWithCornersSelf_coe, range_id, mem_univ, true_and]
  exact hsign _ (hΘR hq)

end Param

/-- Let `Θ` be a partial diffeomorphism of `ℝⁿ × ℝ¹` into `ℝⁿ⁺¹` that sends a point of its source
into the half-space exactly when the point lies in `ℝⁿ × [0, ∞)`. A map on an open set `S` of
`∂W × [0, ∞)` which, read in the boundary chart at `p` and in the extended chart at `p`, is the
restriction of `Θ`, is a local diffeomorphism on `S`. -/
private theorem isLocalDiffeomorphOn_extChartAt_symm_comp {p : (𝓡∂ (n + 1)).boundary W}
    (Θ : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1))
      (EuclideanSpace ℝ (Fin (n + 1))) ∞)
    (hΘ : ∀ q ∈ Θ.source, Θ q ∈ range (𝓡∂ (n + 1)) ↔ q ∈ range ((𝓡 n).prod (𝓡∂ 1)))
    {f : (𝓡∂ (n + 1)).boundary W × EuclideanHalfSpace 1 → EuclideanSpace ℝ (Fin (n + 1))}
    {S : Set ((𝓡∂ (n + 1)).boundary W × EuclideanHalfSpace 1)} (hS : IsOpen S)
    (hf : ∀ q ∈ S, q.1 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source ∧
      (chartAt (EuclideanSpace ℝ (Fin n)) p q.1, q.2.val) ∈ Θ.source ∧
      Θ (chartAt (EuclideanSpace ℝ (Fin n)) p q.1, q.2.val) = f q ∧
      f q ∈ (extChartAt (𝓡∂ (n + 1)) (p : W)).target) :
    IsLocalDiffeomorphOn ((𝓡 n).prod (𝓡∂ 1)) (𝓡∂ (n + 1)) ∞
      (fun q ↦ (extChartAt (𝓡∂ (n + 1)) (p : W)).symm (f q)) S := by
  set β := chartAt (EuclideanSpace ℝ (Fin n)) p
  set C := chartAt (ModelProd (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace 1))
    ((p, 0) : (𝓡∂ (n + 1)).boundary W × EuclideanHalfSpace 1)
  -- The product chart at `(p, 0)` is `β` times the identity, and the product model is the
  -- inclusion of `ℝⁿ × [0, ∞)`.
  have hCapply (q : (𝓡∂ (n + 1)).boundary W × EuclideanHalfSpace 1) : C q = (β q.1, q.2) := by
    simp only [C, β, prodChartedSpace_chartAt, chartAt_self_eq]
    rw [OpenPartialHomeomorph.prod_apply, OpenPartialHomeomorph.refl_apply]
    simp only [id_eq]
  have hCsrc (q : (𝓡∂ (n + 1)).boundary W × EuclideanHalfSpace 1) (hq : q.1 ∈ β.source) :
      q ∈ C.source := by
    simp only [C, prodChartedSpace_chartAt, OpenPartialHomeomorph.prod_source, chartAt_self_eq,
      OpenPartialHomeomorph.refl_source]
    exact ⟨hq, mem_univ _⟩
  have hI (q : EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1) :
      ((𝓡 n).prod (𝓡∂ 1)) q = (q.1, q.2.val) := by
    rw [modelWithCorners_prod_coe, Prod.map_apply, modelWithCornersSelf_coe, id_eq,
      modelWithCornersEuclideanHalfSpace_apply]
  have hCI (q : (𝓡∂ (n + 1)).boundary W × EuclideanHalfSpace 1) :
      ((𝓡 n).prod (𝓡∂ 1)) (C q) = (β q.1, q.2.val) := by
    rw [hCapply, hI]
  rintro ⟨q, hq⟩
  obtain ⟨hq1, hsrc, hval, htgt⟩ := hf q hq
  -- `Θ` read in the half-space models, as a partial diffeomorphism by Tau Ceti.
  have hl : IsLocalDiffeomorphAt ((𝓡 n).prod (𝓡∂ 1)) (𝓡∂ (n + 1)) ∞
      ((𝓡∂ (n + 1)).symm ∘ Θ ∘ ((𝓡 n).prod (𝓡∂ 1))) (C q) := by
    have hΘ' : ∀ y ∈ Θ.toOpenPartialHomeomorph.source, Θ.toOpenPartialHomeomorph y ∈
        range (𝓡∂ (n + 1)) ↔ y ∈ range ((𝓡 n).prod (𝓡∂ 1)) := by
      simpa only [Θ.toOpenPartialHomeomorph_source,
        PartialDiffeomorph.toFun'_toOpenPartialHomeomorph] using hΘ
    have h := (PartialDiffeomorph.ofOpenPartialHomeomorphOfMemRangeIff
      Θ.toOpenPartialHomeomorph
      (by
        rw [Θ.toOpenPartialHomeomorph_source, PartialDiffeomorph.toFun'_toOpenPartialHomeomorph]
        exact contMDiffOn_iff_contDiffOn.1 Θ.contMDiffOn)
      (by
        rw [Θ.toOpenPartialHomeomorph_target, PartialDiffeomorph.coe_toOpenPartialHomeomorph_symm]
        exact contMDiffOn_iff_contDiffOn.1 Θ.symm.contMDiffOn) hΘ').isLocalDiffeomorphAt _ _ _
      (by
        rw [PartialDiffeomorph.ofOpenPartialHomeomorphOfMemRangeIff_source, mem_preimage,
          Θ.toOpenPartialHomeomorph_source, hCI]
        exact hsrc)
    rwa [PartialDiffeomorph.coe_ofOpenPartialHomeomorphOfMemRangeIff,
      PartialDiffeomorph.toFun'_toOpenPartialHomeomorph] at h
  have hχ : (𝓡∂ (n + 1)).symm (Θ (((𝓡 n).prod (𝓡∂ 1)) (C q))) ∈
      (chartAt (EuclideanHalfSpace (n + 1)) (p : W)).target := by
    rw [extChartAt_target] at htgt
    rw [hCI, hval]
    exact htgt.1
  have hc := (C.isLocalDiffeomorphAt_of_mem_maximalAtlas (n := ∞)
    (IsManifold.chart_mem_maximalAtlas _) (hCsrc q hq1)).comp (hg := hl.comp (hg :=
      (OpenPartialHomeomorph.isLocalDiffeomorphAt_symm_of_mem_maximalAtlas
        (chartAt (EuclideanHalfSpace (n + 1)) (p : W))
        (IsManifold.chart_mem_maximalAtlas _) hχ)))
  refine hc.congr_of_eventuallyEq ?_
  filter_upwards [hS.mem_nhds hq] with q' hq'
  simp only [comp_apply, hCI, (hf q' hq').2.2.1, extChartAt_coe_symm]

/-- **Integral curves entering from the boundary.** Let `Y` be a smooth vector field pointing out
of `W` along its boundary, and `p` a boundary point. There are an open set `B ∋ p` of the
boundary, a time `η > 0` and a map `γ` such that for each `x ∈ B` the curve `s ↦ γ (s, x)` starts
at `x`, runs in the interior of `W` for `s ∈ (-η, 0)`, and is an integral curve of `Y` on
`(-η, 0]`. Moreover `(x, t) ↦ γ (-t, x)` is a local diffeomorphism on `B × [0, η)`, the time
interval being read as part of the one-dimensional half-space. -/
theorem exists_isMIntegralCurveOn_of_isOutwardPointing (hY : IsOutwardPointingField Y)
    (p : (𝓡∂ (n + 1)).boundary W) :
    ∃ (B : Set ((𝓡∂ (n + 1)).boundary W)) (η : ℝ)
      (γ : ℝ × (𝓡∂ (n + 1)).boundary W → W),
      IsOpen B ∧ p ∈ B ∧ 0 < η ∧ (∀ x ∈ B, γ (0, x) = x) ∧
      (∀ x ∈ B, ∀ s ∈ Ioo (-η) 0, γ (s, x) ∈ (𝓡∂ (n + 1)).interior W) ∧
      (∀ x ∈ B, IsMIntegralCurveOn (fun s ↦ γ (s, x)) Y (Ioc (-η) 0)) ∧
      IsLocalDiffeomorphOn ((𝓡 n).prod (𝓡∂ 1)) (𝓡∂ (n + 1)) ∞
        (fun q : (𝓡∂ (n + 1)).boundary W × EuclideanHalfSpace 1 ↦ γ (-q.2.val 0, q.1))
        (B ×ˢ EuclideanHalfSpace.normalIio η) := by
  obtain ⟨hYs, hYb⟩ := isOutwardPointingField_iff.1 hY
  set φ := extChartAt (𝓡∂ (n + 1)) (p : W)
  set f : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) :=
    mpullbackWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) (𝓡∂ (n + 1)) φ.symm Y
      (range (𝓡∂ (n + 1)))
  have hrange (y : EuclideanSpace ℝ (Fin (n + 1))) : y ∈ range (𝓡∂ (n + 1)) ↔ 0 ≤ y 0 := by
    simp [range_modelWithCornersEuclideanHalfSpace]
  -- The coordinate field `f` of `Y` is smooth on the chart target, which is the part in the
  -- half-space of an open set `O`; it points out of the half-space at `φ p`.
  obtain ⟨O, hO, hpO, hOt⟩ :=
    mem_nhdsWithin.1 (extChartAt_target_mem_nhdsWithin (I := 𝓡∂ (n + 1)) (p : W))
  have hOt' : O ∩ {y | 0 ≤ y 0} ⊆ φ.target := fun y hy ↦ hOt ⟨hy.1, (hrange y).2 hy.2⟩
  have hf : ContDiffOn ℝ ∞ (-f) (O ∩ {y | 0 ≤ y 0}) :=
    ((hYs.contDiffOn_mpullbackWithin_extChartAt_symm (n := ∞) (by simp) (p : W)).mono hOt').neg
  have hw₀ : f (φ p) 0 < 0 := by
    have h := (isOutwardPointing_iff_proj p.property).1 (hYb p p.property)
    rwa [← mpullbackWithin_extChartAt_symm_self Y (p : W)] at h
  have hp0 : φ p 0 = 0 := extChartAt_self_apply_zero p.property
  -- Tau Ceti's local flow `Ψ` of the inward field `-f` on the half-space.
  obtain ⟨Ψ, U, hU, ε, hε, hΨ, hΨ0, -, hmono, hcurve⟩ :=
    exists_contDiffOn_localFlow_euclideanHalfSpace (k := ⊤) (by simpa using hf)
      (hO.mem_nhds hpO) hp0.ge
      (by simp only [Pi.neg_apply, PiLp.neg_apply]; exact neg_pos.2 hw₀)
  have hcurve' : ∀ x ∈ U, x 0 = 0 → ∀ t ∈ Ico 0 ε,
      Ψ x t ∈ φ.target ∧ HasDerivAt (Ψ x) (-f (Ψ x t)) t := fun x hx hx0 t ht ↦ by
    obtain ⟨hs, hd⟩ := hcurve x ⟨hx, hx0.ge⟩ t ht
    exact ⟨hOt' hs, hd⟩
  -- Along a curve from the boundary hyperplane, the zeroth coordinate has the sign of the time.
  have hsign : ∀ x ∈ U, x 0 = 0 → ∀ t ∈ Ioo (-ε) ε, (0 ≤ Ψ x t 0 ↔ 0 ≤ t) ∧
      (0 < Ψ x t 0 ↔ 0 < t) := fun x hx hx0 t ht ↦ by
    have hm : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨neg_lt_zero.2 hε, hε⟩
    have h1 := (hmono x hx).le_iff_le hm ht
    have h2 := (hmono x hx).lt_iff_lt hm ht
    simp only [hΨ0, hx0] at h1 h2
    exact ⟨h1, h2⟩
  -- The boundary chart `β` at `p`, read in `φ` through the hyperplane parametrization `ι`.
  set ι := euclideanHalfSpaceBoundaryParam n
  set β := chartAt (EuclideanSpace ℝ (Fin n)) p
  have hι (x : (𝓡∂ (n + 1)).boundary W) (hx : (x : W) ∈ φ.source) : ι (β x) = φ x := by
    have h := boundaryParam_extChartAt (α := p) (x := x)
      (by simpa [φ, extChartAt_source, boundaryChartedSpace_chartAt_source] using hx)
    rwa [extChartAt_coe, modelWithCornersSelf_coe, id_comp] at h
  have hz₀ : ι (β p) = φ p := hι p (mem_extChartAt_source _)
  have hU' : interior U ∈ 𝓝 (φ p) := isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.2 hU)
  obtain ⟨Θ, hΘ0, hΘR, hΘG, hcond⟩ := exists_partialDiffeomorph_boundaryParam (z₀ := β p)
    (S := U ×ˢ Ioo (-ε) ε) (by rw [hz₀]; exact prod_mem_nhds hU (Ioo_mem_nhds (by simpa) hε))
    (by simpa using hΨ) hΨ0 (v := -f (φ p))
    (by
      have h := (hcurve' _ (mem_of_mem_nhds hU) hp0 0 ⟨le_rfl, hε⟩).2
      rw [hΨ0] at h
      rwa [hz₀])
    (by simpa using hw₀.ne)
    (R := {q | q.2 0 ∈ Ioo (-ε) ε ∧ ι q.1 ∈ interior U})
    ((isOpen_Ioo.preimage (by fun_prop)).inter (isOpen_interior.preimage (by fun_prop)))
    ⟨by simp [hε], by rw [hz₀]; exact mem_of_mem_nhds hU'⟩ fun q hq ↦
      (hsign _ (interior_subset hq.2) (euclideanHalfSpaceBoundaryParam_apply_zero _) _ hq.1).1
  -- A product box in the source of `Θ`, and the corresponding set `B` of boundary points.
  obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.1 Θ.open_source _ hΘ0
  set B : Set ((𝓡∂ (n + 1)).boundary W) := β.source ∩ β ⁻¹' Metric.ball (β p) δ
  have hB : IsOpen B := β.isOpen_inter_preimage Metric.isOpen_ball
  have hBsrc : ∀ x ∈ B, (x : W) ∈ φ.source := fun x hx ↦ by
    simpa [boundaryChartedSpace_chartAt_source, β, φ] using hx.1
  have hBΘ : ∀ x ∈ B, ∀ τ : EuclideanSpace ℝ (Fin 1), ‖τ‖ < δ → (β x, τ) ∈ Θ.source :=
    fun x hx τ hτ ↦ hδsub (by
      rw [Metric.mem_ball, Prod.dist_eq]
      exact max_lt hx.2 (by simpa using hτ))
  have hBU : ∀ x ∈ B, φ x ∈ U := fun x hx ↦ by
    rw [← hι x (hBsrc x hx)]
    exact interior_subset (hΘR (hBΘ x hx 0 (by simpa using hδ))).2
  have hB0 : ∀ x ∈ B, φ x 0 = 0 := fun x hx ↦ by
    rw [← hι x (hBsrc x hx)]
    exact euclideanHalfSpaceBoundaryParam_apply_zero _
  have hη (s : ℝ) (hs : s ∈ Ioc (-min ε δ) 0) : -s ∈ Ico 0 ε :=
    ⟨neg_nonneg.2 hs.2, by linarith [hs.1, min_le_left ε δ]⟩
  refine ⟨B, min ε δ, fun q ↦ φ.symm (Ψ (φ q.2) (-q.1)), hB,
    ⟨mem_chart_source _ p, Metric.mem_ball_self hδ⟩, lt_min hε hδ, fun x hx ↦ ?_,
    fun x hx s hs ↦ ?_, fun x hx s hs ↦ ?_, ?_⟩
  · -- The curves start on the boundary.
    simp only [neg_zero, hΨ0]
    exact φ.left_inv (hBsrc x hx)
  · -- They run in the interior at negative times.
    have ht := hη s ⟨hs.1, hs.2.le⟩
    exact extChartAt_symm_mem_interior (hcurve' _ (hBU x hx) (hB0 x hx) _ ht).1
      ((hsign _ (hBU x hx) (hB0 x hx) _ ⟨by linarith [ht.1, hε], ht.2⟩).2.2 (by linarith [hs.2]))
  · -- They are integral curves of `Y`: in the chart they solve `y' = f y`, and `f` is the
    -- coordinate field of `Y`.
    have hmem : ∀ r ∈ Ioc (-min ε δ) 0, Ψ (φ x) (-r) ∈ φ.target := fun r hr ↦
      (hcurve' _ (hBU x hx) (hB0 x hx) _ (hη r hr)).1
    have hd : HasDerivWithinAt (fun r ↦ Ψ (φ x) (-r)) (f (Ψ (φ x) (-s))) (Ioc (-min ε δ) 0) s := by
      have h := (hcurve' _ (hBU x hx) (hB0 x hx) _ (hη s hs)).2.scomp s (hasDerivAt_neg s)
      simp only [neg_smul, one_smul, neg_neg] at h
      exact h.hasDerivWithinAt
    have h := Manifold.hasMFDerivWithinAt_extChartAt_symm_comp (γ := fun r ↦ Ψ (φ x) (-r))
      (hmem s hs)
      (eventually_nhdsWithin_of_forall fun r hr ↦ extChartAt_target_subset_range _ (hmem r hr)) hd
    rwa [mfderivWithin_extChartAt_symm_mpullbackWithin (hmem s hs)] at h
  · -- Read in charts, `(x, t) ↦ γ (-t, x)` is the restriction of `Θ` to the half-spaces.
    simp only [neg_neg]
    refine isLocalDiffeomorphOn_extChartAt_symm_comp Θ hcond
      (hB.prod (EuclideanHalfSpace.isOpen_normalIio _)) fun q ⟨hq1, hq2⟩ ↦ ?_
    rw [EuclideanHalfSpace.mem_normalIio] at hq2
    have h0 : 0 ≤ q.2.val 0 := q.2.property
    have hnorm : ‖q.2.val‖ < δ := by
      have h : ‖q.2.val‖ = |q.2.val 0| := by
        simp [EuclideanSpace.norm_eq, Real.sqrt_sq_eq_abs]
      rw [h, abs_of_nonneg h0]
      exact lt_of_lt_of_le hq2 (min_le_right _ _)
    have hsrc := hBΘ _ hq1 _ hnorm
    refine ⟨hq1.1, hsrc, by rw [hΘG _ hsrc, hι _ (hBsrc _ hq1)],
      (hcurve' _ (hBU _ hq1) (hB0 _ hq1) _ ⟨h0, lt_of_lt_of_le hq2 (min_le_left _ _)⟩).1⟩

end TauCeti

end
