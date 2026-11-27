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

Written in the charts of `∂W × [0, ∞)` at `(p, 0)` and of `W` at `p`, the flow from the boundary
`(x, t) ↦ γ (-t, x)` is the map
`G (z, τ) = Ψ (z inserted as a point with zeroth coordinate 0) (τ 0)` between open subsets of
`ℝⁿ × ℝ¹` and `ℝⁿ⁺¹`, also defined at negative times. At `(z₀, 0)`, `z₀` the boundary chart
reading of `p`, its derivative sends `(u, σ)` to `σ 0 • v` plus `u` inserted with zeroth
coordinate `0`, where `v = -f (φ p)` is the velocity of `t ↦ Ψ (φ p) t` at `0`, since
`Ψ x 0 = x` (`DifferentiableAt.hasFDerivAt_uncurry_zero`). It is injective since `v` is
transverse to the boundary hyperplane
(`TauCeti.injective_fderiv_euclideanHalfSpaceBoundaryParam_of_hasDerivAt`). Near that point `G`
sends exactly the points of `ℝⁿ × [0, ∞)` into the half-space, by the monotonicity of the zeroth
coordinate, so Tau Ceti's inverse function theorem at boundary points,
`TauCeti.isLocalDiffeomorphAt_of_injective_fderiv_of_mem_range_iff`, makes the flow from the
boundary a local diffeomorphism at `(p, 0)`, hence on a box `B × [0, η)` inside the source of a
partial diffeomorphism that agrees with it. This follows the proof of Tau Ceti's
`TauCeti.isLocalDiffeomorphAt_flowOut_boundary`, for a field defined near `p` in the chart rather
than a flow given on the manifold, which here needs no Hausdorff hypothesis on `W`; see also Lee,
Theorem 9.20, and Tau Ceti's boundaryless flow-out theorem
`TauCeti.isLocalDiffeomorph_globalFlow_comp`.

These curves need no uniqueness result here: Tau Ceti's
`IsMIntegralCurveOn.eqOn_of_isPreconnected` holds for curves that may meet the boundary, so two
integral curves of a smooth field on `(-η, 0]` that agree at time `0` agree.
An integral curve of an outward field stays in the interior at times from which it is defined for
a while forward, since its velocity there within `[t, ∞)` would be outward, which Tau Ceti's
`TauCeti.not_isOutwardPointing_curveVelocityWithin_Ici` rules out
(`IsMIntegralCurveOn.mem_interior_of_isOutwardPointing`).

## Main results

* `TauCeti.injective_fderiv_euclideanHalfSpaceBoundaryParam_of_hasDerivAt`: a family `Ψ x t`
  with `Ψ x 0 = x` whose velocity at time `0` is transverse to the boundary hyperplane has, out of
  that hyperplane, injective derivative.
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

/-- Let `Ψ x t` be a family of points of `ℝⁿ⁺¹` with `Ψ x 0 = x`, differentiable at `(y₀, 0)`,
where `y₀` is the point `z₀ ∈ ℝⁿ` of the boundary hyperplane, such that the curve `t ↦ Ψ y₀ t`
has at time `0` a velocity `v` with `v 0 ≠ 0`. Then `(z, τ) ↦ Ψ (z in the hyperplane) (τ 0)` on
`ℝⁿ × ℝ¹` has injective derivative at `(z₀, 0)`. -/
theorem injective_fderiv_euclideanHalfSpaceBoundaryParam_of_hasDerivAt
    {z₀ : EuclideanSpace ℝ (Fin n)}
    (hΨ : DifferentiableAt ℝ (fun p : EuclideanSpace ℝ (Fin (n + 1)) × ℝ ↦ Ψ p.1 p.2)
      (euclideanHalfSpaceBoundaryParam n z₀, 0))
    (hΨ0 : ∀ x, Ψ x 0 = x) {v : EuclideanSpace ℝ (Fin (n + 1))}
    (hv : HasDerivAt (Ψ (euclideanHalfSpaceBoundaryParam n z₀)) v 0) (hv0 : v 0 ≠ 0) :
    Injective (fderiv ℝ (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1) ↦
      Ψ (euclideanHalfSpaceBoundaryParam n q.1) (q.2 0)) (z₀, 0)) := by
  set ι := euclideanHalfSpaceBoundaryParam n
  set L : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1) →L[ℝ]
      EuclideanSpace ℝ (Fin (n + 1)) × ℝ :=
    (ι.comp (ContinuousLinearMap.fst ℝ _ _)).prod
      ((PiLp.proj 2 (fun _ : Fin 1 ↦ ℝ) 0).comp (ContinuousLinearMap.snd ℝ _ _))
  have hLz₀ : L (z₀, 0) = (ι z₀, 0) := by
    simp [L]
  -- The derivative `D` of `Ψ` at `(ι z₀, 0)` is the identity in space and `v` in time.
  set D : EuclideanSpace ℝ (Fin (n + 1)) × ℝ →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
    ContinuousLinearMap.fst ℝ _ ℝ + (ContinuousLinearMap.snd ℝ _ ℝ).smulRight v
  have hD : HasFDerivAt (fun p : EuclideanSpace ℝ (Fin (n + 1)) × ℝ ↦ Ψ p.1 p.2) D (ι z₀, 0) :=
    hΨ.hasFDerivAt_uncurry_zero (Eventually.of_forall hΨ0) hv
  have hDapply (u : EuclideanSpace ℝ (Fin (n + 1))) (σ : ℝ) : D (u, σ) = u + σ • v := by
    simp [D]
  have hGd : HasFDerivAt (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1) ↦
      Ψ (ι q.1) (q.2 0)) (D.comp L) (z₀, 0) := by
    rw [← hLz₀] at hD
    exact hD.comp (z₀, 0) L.hasFDerivAt
  -- So that derivative is injective, since `v` leaves the hyperplane.
  rw [hGd.fderiv, injective_iff_map_eq_zero]
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

end Param

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
  have hβφ (x : (𝓡∂ (n + 1)).boundary W) (hx : x ∈ β.source) : (x : W) ∈ φ.source := by
    simpa [boundaryChartedSpace_chartAt_source, β, φ] using hx
  have hΨ' : ContDiffOn ℝ ∞ (fun p : EuclideanSpace ℝ (Fin (n + 1)) × ℝ ↦ Ψ p.1 p.2)
      (U ×ˢ Ioo (-ε) ε) := by
    simpa using hΨ
  -- The flow from the boundary `F (x, t) = φ⁻¹ (Ψ (φ x) t)` reads, in the charts at `(p, 0)` and
  -- at `p`, as `g (z, τ) = Ψ (ι z) (τ 0)`, which is smooth on the open set `t`.
  set F : (𝓡∂ (n + 1)).boundary W × EuclideanHalfSpace 1 → W :=
    fun q ↦ φ.symm (Ψ (φ q.1) (q.2.val 0))
  set g : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin (n + 1)) :=
    fun q ↦ Ψ (ι q.1) (q.2 0)
  set t : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1)) :=
    {q | q.2 0 ∈ Ioo (-ε) ε ∧ ι q.1 ∈ interior U}
  have ht : IsOpen t :=
    (isOpen_Ioo.preimage (by fun_prop)).inter (isOpen_interior.preimage (by fun_prop))
  have hg : ContDiffOn ℝ ∞ g t := by
    set L : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1) →L[ℝ]
        EuclideanSpace ℝ (Fin (n + 1)) × ℝ :=
      (ι.comp (ContinuousLinearMap.fst ℝ _ _)).prod
        ((PiLp.proj 2 (fun _ : Fin 1 ↦ ℝ) 0).comp (ContinuousLinearMap.snd ℝ _ _))
    exact hΨ'.comp L.contDiff.contDiffOn fun q hq ↦ ⟨interior_subset hq.2, hq.1⟩
  have hval0 : (0 : EuclideanHalfSpace 1).val = 0 := by
    ext i
    rw [Subsingleton.elim i 0]
    exact EuclideanHalfSpace.val_zero_apply
  have hext (q : (𝓡∂ (n + 1)).boundary W × EuclideanHalfSpace 1) :
      extChartAt ((𝓡 n).prod (𝓡∂ 1)) (p, 0) q = (β q.1, q.2.val) := by
    simp [β]
  have hF0 : F (p, 0) = p := by
    simp only [F, EuclideanHalfSpace.val_zero_apply, hΨ0]
    exact φ.left_inv (mem_extChartAt_source _)
  -- By the inverse function theorem at boundary points, `F` is a local diffeomorphism at `(p, 0)`.
  have hloc : IsLocalDiffeomorphAt ((𝓡 n).prod (𝓡∂ 1)) (𝓡∂ (n + 1)) ∞ F (p, 0) := by
    refine isLocalDiffeomorphAt_of_injective_fderiv_of_mem_range_iff hg ht ?_ (by simp) ?_
      (by simp) (fun q hq ↦ ?_) ?_ ?_
    · rw [hext]
      exact ⟨by simp [EuclideanHalfSpace.val_zero_apply, hε], by
        rw [hz₀]; exact mem_of_mem_nhds hU'⟩
    · rw [hext, hval0]
      refine injective_fderiv_euclideanHalfSpaceBoundaryParam_of_hasDerivAt ?_ hΨ0
        (v := -f (φ p)) ?_ (by simpa using hw₀.ne)
      · rw [hz₀]
        exact (hΨ'.contDiffAt (prod_mem_nhds hU (Ioo_mem_nhds (by simpa) hε))).differentiableAt
          (by simp)
      · have h := (hcurve' _ (mem_of_mem_nhds hU) hp0 0 ⟨le_rfl, hε⟩).2
        rw [hΨ0] at h
        rwa [hz₀]
    · -- Along a curve from the boundary hyperplane, the zeroth coordinate has the sign of the
      -- time.
      rw [ModelWithCorners.range_prod, range_modelWithCornersEuclideanHalfSpace,
        range_modelWithCornersEuclideanHalfSpace]
      simp only [mem_ofPred_eq, mem_prod, modelWithCornersSelf_coe, range_id, mem_univ, true_and]
      exact (hsign _ (interior_subset hq.2) (euclideanHalfSpaceBoundaryParam_apply_zero _) _
        hq.1).1
    · rw [hF0, hext, hval0]
      simp only [g, PiLp.zero_apply, hΨ0, hz₀, φ]
    · rw [hF0]
      filter_upwards [(β.open_source.preimage continuous_fst).mem_nhds
        (show ((p, 0) : (𝓡∂ (n + 1)).boundary W × EuclideanHalfSpace 1).1 ∈ β.source from
          mem_chart_source _ p)] with q hq
      simp only [F, g, hext, hι q.1 (hβφ q.1 hq), φ]
  -- A partial diffeomorphism `Φ` agreeing with `F`, with source in the chart domain at `p`, and a
  -- product box in its source.
  set B₀ : Set ((𝓡∂ (n + 1)).boundary W) := β.source ∩ β ⁻¹' (ι ⁻¹' interior U)
  have hB₀ : IsOpen B₀ := β.isOpen_inter_preimage (isOpen_interior.preimage (by fun_prop))
  have hpB₀ : p ∈ B₀ := ⟨mem_chart_source _ p, by
    rw [mem_preimage, mem_preimage, hz₀]; exact mem_of_mem_nhds hU'⟩
  obtain ⟨Φ, hΦ0, hΦB₀, hFΦ⟩ :=
    hloc.exists_partialDiffeomorph_eqOn (hB₀.preimage continuous_fst) hpB₀
  obtain ⟨B, V, hB, hpB, hV, h0V, hBV⟩ := mem_nhds_prod_iff'.1 (Φ.open_source.mem_nhds hΦ0)
  obtain ⟨δ, hδ, hδV⟩ := EuclideanHalfSpace.exists_normalIio_subset hV h0V
  have hBB₀ : ∀ x ∈ B, x ∈ B₀ := fun x hx ↦
    mem_preimage.1 (hΦB₀ (hBV (mk_mem_prod hx h0V)))
  have hBsrc : ∀ x ∈ B, (x : W) ∈ φ.source := fun x hx ↦ hβφ x (hBB₀ x hx).1
  have hBU : ∀ x ∈ B, φ x ∈ U := fun x hx ↦ by
    rw [← hι x (hBsrc x hx)]
    exact interior_subset (hBB₀ x hx).2
  have hB0 : ∀ x ∈ B, φ x 0 = 0 := fun x hx ↦ by
    rw [← hι x (hBsrc x hx)]
    exact euclideanHalfSpaceBoundaryParam_apply_zero _
  have hη (s : ℝ) (hs : s ∈ Ioc (-min ε δ) 0) : -s ∈ Ico 0 ε :=
    ⟨neg_nonneg.2 hs.2, by linarith [hs.1, min_le_left ε δ]⟩
  refine ⟨B, min ε δ, fun q ↦ φ.symm (Ψ (φ q.2) (-q.1)), hB, hpB, lt_min hε hδ, fun x hx ↦ ?_,
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
  · -- `(x, t) ↦ γ (-t, x)` is `F`, which agrees with `Φ` on the source of `Φ`.
    simp only [neg_neg]
    rintro ⟨q, hq1, hq2⟩
    refine isLocalDiffeomorphAt_of_eqOn (hBV ⟨hq1, hδV ?_⟩) hFΦ
    rw [EuclideanHalfSpace.mem_normalIio] at hq2 ⊢
    exact lt_of_lt_of_le hq2 (min_le_right _ _)

end TauCeti

end
