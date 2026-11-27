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
import Mathlib.Geometry.Manifold.IntegralCurve.Transform
import TauCeti.Geometry.Manifold.Boundary.BoundaryFlow.LocalDiffeomorph
import SymplecticGeometry.Analysis.Calculus.FDeriv.Uncurry
import SymplecticGeometry.Geometry.Manifold.Boundary.Charts
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Chart

/-!
# The flow of an outward field near a boundary point

Let `W` be a manifold modelled on the half-space `𝓡∂ (n + 1)` and `Y` a smooth vector field on
`W` that points out of `W` along its boundary (`TauCeti.IsOutwardPointingField`). Integral curves
of `Y` cannot start at a boundary point and go forward, but they can go backward, into the
interior. This file constructs them near a boundary point `p`.

Tau Ceti's `TauCeti.exists_contDiffOn_chartFlow_of_isOutwardPointing_neg`, applied to the
inward field `-Y`, gives the flow of `-Y` read in the extended chart `φ` at `p`: a smooth family
`Ψ x t` near `φ p`, with `Ψ x 0 = x`, whose zeroth coordinate strictly increases in time, and
whose forward curves from the half-space stay in the chart target and are, read back by `φ⁻¹`,
integral curves of `-Y`. So a curve `t ↦ Ψ x t` from a point `x` of the boundary hyperplane is in
the open half-space exactly at positive times, and `s ↦ φ⁻¹ (Ψ x (-s))` is an integral curve of
`Y` on `(-η, 0]` (Mathlib's `IsMIntegralCurveOn.comp_mul`), in the interior of `W` at negative
times.

On a Hausdorff manifold, Tau Ceti's flow-out theorem
`TauCeti.isLocalDiffeomorphAt_flowOut_boundary`
makes the flow from the boundary `(x, t) ↦ φ⁻¹ (Ψ (φ x) t)` a local diffeomorphism at `(p, 0)`,
hence on a box `B × [0, η)` inside the source of a partial diffeomorphism that agrees with it.
See also Lee, Theorem 9.20.

These curves need no uniqueness result here: Tau Ceti's
`IsMIntegralCurveOn.eqOn_of_isPreconnected` holds for curves that may meet the boundary, so two
integral curves of a smooth field on `(-η, 0]` that agree at time `0` agree.
An integral curve of an outward field stays in the interior at times from which it is defined for
a while forward, since its velocity there within `[t, ∞)` would be outward, which Tau Ceti's
`TauCeti.not_isOutwardPointing_curveVelocityWithin_Ici` rules out
(`IsMIntegralCurveOn.mem_interior_of_isOutwardPointing`).

## Main results

* `TauCeti.injective_fderiv_flowOut_euclideanHalfSpaceBoundaryParam`: a family `Ψ x t`
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

variable {Ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ → EuclideanSpace ℝ (Fin (n + 1))}

/-- Let `Ψ x t` be a family of points of `ℝⁿ⁺¹` with `Ψ x 0 = x` for `x` near `y₀`,
differentiable at `(y₀, 0)`, where `y₀` is the point `z₀ ∈ ℝⁿ` of the boundary hyperplane, such
that the curve `t ↦ Ψ y₀ t` has at time `0` a velocity `v` with `v 0 ≠ 0`. Then the flow-out map
`(z, τ) ↦ Ψ (z in the hyperplane) (τ 0)` on `ℝⁿ × ℝ¹` has injective derivative at `(z₀, 0)`. -/
theorem injective_fderiv_flowOut_euclideanHalfSpaceBoundaryParam
    {z₀ : EuclideanSpace ℝ (Fin n)}
    (hΨ : DifferentiableAt ℝ (fun p : EuclideanSpace ℝ (Fin (n + 1)) × ℝ ↦ Ψ p.1 p.2)
      (euclideanHalfSpaceBoundaryParam n z₀, 0))
    (hΨ0 : ∀ᶠ x in 𝓝 (euclideanHalfSpaceBoundaryParam n z₀), Ψ x 0 = x)
    {v : EuclideanSpace ℝ (Fin (n + 1))}
    (hv : HasDerivAt (Ψ (euclideanHalfSpaceBoundaryParam n z₀)) v 0) (hv0 : v 0 ≠ 0) :
    Injective (fderiv ℝ (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1) ↦
      Ψ (euclideanHalfSpaceBoundaryParam n q.1) (q.2 0)) (z₀, 0)) := by
  set ι := euclideanHalfSpaceBoundaryParam n
  set L := ι.prodMap (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1))
  have hLz₀ : L (z₀, 0) = (ι z₀, 0) := by
    simp [L]
  -- The derivative `D` of `Ψ` at `(ι z₀, 0)` is the identity in space and `v` in time.
  set D : EuclideanSpace ℝ (Fin (n + 1)) × ℝ →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
    ContinuousLinearMap.fst ℝ _ ℝ + (ContinuousLinearMap.snd ℝ _ ℝ).smulRight v
  have hD : HasFDerivAt (fun p : EuclideanSpace ℝ (Fin (n + 1)) × ℝ ↦ Ψ p.1 p.2) D (ι z₀, 0) :=
    hΨ.hasFDerivAt_uncurry_zero hΨ0 hv
  have hDapply (u : EuclideanSpace ℝ (Fin (n + 1))) (σ : ℝ) : D (u, σ) = u + σ • v := by
    simp [D]
  have hGd : HasFDerivAt (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1) ↦
      Ψ (ι q.1) (q.2 0)) (D.comp L) (z₀, 0) := by
    rw [← hLz₀] at hD
    exact hD.comp (z₀, 0) L.hasFDerivAt
  -- So that derivative is injective, since `v` leaves the hyperplane.
  rw [hGd.fderiv, injective_iff_map_eq_zero]
  rintro ⟨dz, dτ⟩ h
  simp only [L, ContinuousLinearMap.coe_comp, comp_apply, ContinuousLinearMap.coe_prodMap',
    Prod.map_apply, PiLp.proj_apply, hDapply] at h
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

/-- **Integral curves entering from the boundary.** Let `Y` be a smooth vector field pointing out
of a Hausdorff manifold `W` along its boundary, and `p` a boundary point. There are an open set
`B ∋ p` of the boundary, a time `η > 0` and a map `γ` such that for each `x ∈ B` the curve
`s ↦ γ (s, x)` starts at `x`, runs in the interior of `W` for `s ∈ (-η, 0)`, and is an integral
curve of `Y` on `(-η, 0]`. Moreover `(x, t) ↦ γ (-t, x)` is a local diffeomorphism on
`B × [0, η)`, the time interval being read as part of the one-dimensional half-space. -/
theorem exists_isMIntegralCurveOn_of_isOutwardPointing [T2Space W]
    (hY : IsOutwardPointingField Y) (p : (𝓡∂ (n + 1)).boundary W) :
    ∃ (B : Set ((𝓡∂ (n + 1)).boundary W)) (η : ℝ)
      (γ : ℝ × (𝓡∂ (n + 1)).boundary W → W),
      IsOpen B ∧ p ∈ B ∧ 0 < η ∧ (∀ x ∈ B, γ (0, x) = x) ∧
      (∀ x ∈ B, ∀ s ∈ Ioo (-η) 0, γ (s, x) ∈ (𝓡∂ (n + 1)).interior W) ∧
      (∀ x ∈ B, IsMIntegralCurveOn (fun s ↦ γ (s, x)) Y (Ioc (-η) 0)) ∧
      IsLocalDiffeomorphOn ((𝓡 n).prod (𝓡∂ 1)) (𝓡∂ (n + 1)) ∞
        (fun q : (𝓡∂ (n + 1)).boundary W × EuclideanHalfSpace 1 ↦ γ (-q.2.val 0, q.1))
        (B ×ˢ EuclideanHalfSpace.normalIio η) := by
  set φ := extChartAt (𝓡∂ (n + 1)) (p : W)
  have hYneg : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞
      (fun x ↦ (⟨x, (-Y) x⟩ : TangentBundle (𝓡∂ (n + 1)) W)) :=
    fun x ↦ (hY.contMDiff x).neg_section
  have hpY : IsOutwardPointing (p : W) (-(-Y) (p : W)) := by
    simpa using hY.isOutwardPointing p.property
  -- Tau Ceti's flow `Ψ` of the inward field `-Y`, read in the chart `φ` at `p`.
  obtain ⟨Ψ, U, hU, ε, hε, -, hΨ0, hmono, hdom, hcurve, -⟩ :=
    exists_contDiffOn_chartFlow_of_isOutwardPointing_neg (-Y) hYneg.contMDiffOn univ_mem hpY
  have hφ0 : ∀ x ∈ φ.source, 0 ≤ φ x 0 := fun x hx ↦ by
    have h := extChartAt_target_subset_range (I := 𝓡∂ (n + 1)) (p : W) (φ.map_source hx)
    rwa [range_modelWithCornersEuclideanHalfSpace] at h
  -- Along a curve from the boundary hyperplane, the zeroth coordinate has the sign of the time.
  have hsign : ∀ x ∈ U, x 0 = 0 → ∀ t ∈ Ioo (-ε) ε, (0 < Ψ x t 0 ↔ 0 < t) := fun x hx hx0 t ht ↦ by
    have h := (hmono x hx).lt_iff_lt ⟨neg_lt_zero.2 hε, hε⟩ ht
    simpa only [hΨ0, hx0] using h
  -- The flow from the boundary `F (x, t) = φ⁻¹ (Ψ (φ x) t)` is a local diffeomorphism at `(p, 0)`,
  -- by Tau Ceti's flow-out theorem.
  set F : (𝓡∂ (n + 1)).boundary W × EuclideanHalfSpace 1 → W :=
    fun q ↦ φ.symm (Ψ (φ q.1) (q.2.val 0))
  have hloc : IsLocalDiffeomorphAt ((𝓡 n).prod (𝓡∂ 1)) (𝓡∂ (n + 1)) ∞ F (p, 0) :=
    isLocalDiffeomorphAt_flowOut_boundary (-Y) hYneg hpY
      (W := (φ.source ∩ φ ⁻¹' U) ×ˢ Iio ε) (Φ := fun x t ↦ φ.symm (Ψ (φ x) t))
      (prod_mem_nhds (inter_mem (extChartAt_source_mem_nhds _)
        ((continuousAt_extChartAt _).preimage_mem_nhds hU)) (Iio_mem_nhds hε))
      fun x _ t ht _ ↦ ⟨by simp only [hΨ0]; exact φ.left_inv ht.1.1,
        (hcurve _ ht.1.2 (hφ0 x ht.1.1)).mono (Icc_subset_Ico_right ht.2)⟩
  -- The boundary chart `β` at `p`, read in `φ` through the hyperplane parametrization `ι`.
  set ι := euclideanHalfSpaceBoundaryParam n
  set β := extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) p
  have hz₀ : ι (β p) = φ p := boundaryParam_extChartAt (mem_extChartAt_source _)
  have hU' : interior U ∈ 𝓝 (φ p) := isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.2 hU)
  -- A partial diffeomorphism `Φ` agreeing with `F`, with source in the chart domain at `p`, and a
  -- product box in its source.
  set B₀ : Set ((𝓡∂ (n + 1)).boundary W) := β.source ∩ β ⁻¹' (ι ⁻¹' interior U)
  have hB₀ : IsOpen B₀ :=
    isOpen_extChartAt_preimage' p (isOpen_interior.preimage (by fun_prop))
  have hpB₀ : p ∈ B₀ := ⟨mem_extChartAt_source p, by
    rw [mem_preimage, mem_preimage, hz₀]; exact mem_of_mem_nhds hU'⟩
  obtain ⟨Φ, hΦ0, hΦB₀, hFΦ⟩ :=
    hloc.exists_partialDiffeomorph_eqOn (hB₀.preimage continuous_fst) hpB₀
  obtain ⟨B, V, hB, hpB, hV, h0V, hBV⟩ := mem_nhds_prod_iff'.1 (Φ.open_source.mem_nhds hΦ0)
  obtain ⟨δ, hδ, hδV⟩ := EuclideanHalfSpace.exists_normalIio_subset hV h0V
  have hBB₀ : ∀ x ∈ B, x ∈ B₀ := fun x hx ↦
    mem_preimage.1 (hΦB₀ (hBV (mk_mem_prod hx h0V)))
  have hBsrc : ∀ x ∈ B, (x : W) ∈ φ.source := fun x hx ↦ by
    simpa only [φ, β, extChartAt_source, boundaryChartedSpace_chartAt_source, mem_preimage] using
      (hBB₀ x hx).1
  have hBU : ∀ x ∈ B, φ x ∈ U := fun x hx ↦ by
    rw [← boundaryParam_extChartAt (hBB₀ x hx).1]
    exact interior_subset (hBB₀ x hx).2
  have hB0 : ∀ x ∈ B, φ x 0 = 0 := fun x hx ↦ by
    rw [← boundaryParam_extChartAt (hBB₀ x hx).1]
    exact euclideanHalfSpaceBoundaryParam_apply_zero _
  have hη (s : ℝ) (hs : s ∈ Ioc (-min ε δ) 0) : -s ∈ Ico 0 ε :=
    ⟨neg_nonneg.2 hs.2, by linarith [hs.1, min_le_left ε δ]⟩
  refine ⟨B, min ε δ, fun q ↦ φ.symm (Ψ (φ q.2) (-q.1)), hB, hpB, lt_min hε hδ, fun x hx ↦ ?_,
    fun x hx s hs ↦ ?_, fun x hx ↦ ?_, ?_⟩
  · -- The curves start on the boundary.
    simp only [neg_zero, hΨ0]
    exact φ.left_inv (hBsrc x hx)
  · -- They run in the interior at negative times.
    have ht := hη s ⟨hs.1, hs.2.le⟩
    exact extChartAt_symm_mem_interior (hdom _ (hBU x hx) (hB0 x hx).ge _ ht).1
      ((hsign _ (hBU x hx) (hB0 x hx) _ ⟨by linarith [ht.1, hε], ht.2⟩).2 (by linarith [hs.2]))
  · -- They are the forward integral curves of `-Y` run backwards.
    have h := IsMIntegralCurveOn.comp_mul (hcurve _ (hBU x hx) (hB0 x hx).ge) (-1)
    have hsub : Ioc (-min ε δ) 0 ⊆ {t | t * -1 ∈ Ico 0 ε} := fun s hs ↦ by simpa using hη s hs
    convert h.mono hsub using 1
    · ext s
      simp only [comp_apply, mul_neg_one, φ]
    · ext y
      simp
  · -- `(x, t) ↦ γ (-t, x)` is `F`, which agrees with `Φ` on the source of `Φ`.
    simp only [neg_neg]
    rintro ⟨q, hq1, hq2⟩
    refine isLocalDiffeomorphAt_of_eqOn (hBV ⟨hq1, hδV ?_⟩) hFΦ
    rw [EuclideanHalfSpace.mem_normalIio] at hq2 ⊢
    exact lt_of_lt_of_le hq2 (min_le_right _ _)

end TauCeti

end
