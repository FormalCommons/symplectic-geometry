/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.TopForm
public import TauCeti.Geometry.Manifold.Orientation.Prod
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Basic
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Regularity
import TauCeti.Geometry.Manifold.MFDeriv.Prod
import TauCeti.LinearAlgebra.Basis.Fin
import TauCeti.Topology.Algebra.Module.Alternating.Wedge.Append

/-!
# The integral of a product of top forms supported in charts

Let `B` and `F` be oriented boundaryless manifolds of dimensions `m` and `n`, and let `β` and `γ`
be continuous compactly supported top forms on `B` and on `F`. This file proves the chart-wise case
of the splitting

`∫_{B × F} pr₁^* β ∧ pr₂^* γ = (∫_B β) (∫_F γ)`

for the product orientation `TauCeti.Manifold.Orientation.prod` of `B × F`, in which the tangent
directions of `B` come first: when `β` is supported in the source of one chart of `B` and `γ` in
the source of one chart of `F`
(`TauCeti.integralTopForm_wedge_mpullback_fst_snd_of_tsupport_subset_chart`). The forms are rough
forms of class `C⁰` rather than smooth forms, so that the pieces `ρ • β` of a form cut by a smooth
partition of unity can be fed to it.

The proof works in the product of the two charts, whose target is the product of their targets.
On the block basis `(b₁, 0), …, (b_m, 0), (0, b'₁), …, (0, b'_n)` of `E × E'` the chart coefficient
of `pr₁^* β ∧ pr₂^* γ` is the product of the chart coefficients of `β` on `b` and of `γ` on `b'`
(`TauCeti.mpullback_extChartAt_prod_symm_wedge_apply`), the chart sign of the product lift is the
product of the chart signs, and the Haar measure of the block basis is the product of the Haar
measures; Fubini's theorem then splits the chart integral. This adapts the proof of Tau Ceti's
`TauCeti.integralTopForm_wedge_mpullback_fst_of_tsupport_subset_chart`
(`TauCeti/Geometry/Manifold/DeRham/Integration/FiberFlux.lean`), which treats a product `M × ℂ` with
a form on `M × ℂ` that need not be a wedge of pullbacks, to a product of two arbitrary
factors.

## Main results

* `TauCeti.mpullback_extChartAt_prod_symm_wedge_apply`: in the product chart, the coefficient of
  `pr₁^* β ∧ pr₂^* γ` on a block basis is the product of the coefficients of `β` and of `γ`.
* `TauCeti.integralTopForm_wedge_mpullback_fst_snd_of_tsupport_subset_chart`: the splitting
  `∫ pr₁^* β ∧ pr₂^* γ = (∫ β) (∫ γ)` for `β` and `γ` supported in one chart each.

## References

* [R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §3 (integration
  of top forms on oriented manifolds)
-/

public section

noncomputable section

open MeasureTheory Set
open scoped Manifold ContDiff

namespace TauCeti

variable {E E' H H' B F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
  [TopologicalSpace B] [ChartedSpace H B] [TopologicalSpace F] [ChartedSpace H' F]
  [IsManifold I 1 B] [IsManifold J 1 F] [I.Boundaryless] [J.Boundaryless]

/-- On the target of the product chart at `p`, the pullback of `pr₁^* β` along the inverse
product chart, evaluated on vectors `v i` of `E × E'`, is the pullback of `β` along the inverse
chart of the first factor, evaluated on the first components of the `v i`. -/
theorem mpullback_extChartAt_prod_symm_mpullback_fst_apply {k : ℕ}
    (β : RoughForm I B ℝ k) (p : B × F) {y : E × E'} (hy : y ∈ (extChartAt (I.prod J) p).target)
    (v : Fin k → E × E') :
    mpullback 𝓘(ℝ, E × E') (I.prod J) (extChartAt (I.prod J) p).symm
        (mpullback (I.prod J) I Prod.fst β) y v =
      mpullback 𝓘(ℝ, E) I (extChartAt I p.1).symm β y.1 (fun i ↦ (v i).1) := by
  -- The vectors `v i` are tangent vectors of the model `E × E'` only up to unfolding
  -- `TangentSpace`, so the evaluation lemma is applied with `erw`.
  erw [mpullback_apply, mpullback_apply, mpullback_apply]
  simp only [mfderiv_extChartAt_symm_prod_apply hy, mfderiv_fst]
  -- A projection applied to a pair is its component.
  rfl

/-- On the target of the product chart at `p`, the pullback of `pr₂^* γ` along the inverse
product chart, evaluated on vectors `v i` of `E × E'`, is the pullback of `γ` along the inverse
chart of the second factor, evaluated on the second components of the `v i`. -/
theorem mpullback_extChartAt_prod_symm_mpullback_snd_apply {k : ℕ}
    (γ : RoughForm J F ℝ k) (p : B × F) {y : E × E'} (hy : y ∈ (extChartAt (I.prod J) p).target)
    (v : Fin k → E × E') :
    mpullback 𝓘(ℝ, E × E') (I.prod J) (extChartAt (I.prod J) p).symm
        (mpullback (I.prod J) J Prod.snd γ) y v =
      mpullback 𝓘(ℝ, E') J (extChartAt J p.2).symm γ y.2 (fun i ↦ (v i).2) := by
  -- The vectors `v i` are tangent vectors of the model `E × E'` only up to unfolding
  -- `TangentSpace`, so the evaluation lemma is applied with `erw`.
  erw [mpullback_apply, mpullback_apply, mpullback_apply]
  simp only [mfderiv_extChartAt_symm_prod_apply hy, mfderiv_snd]
  -- A projection applied to a pair is its component.
  rfl

/-- **The chart coefficient of a wedge of pullbacks from the two factors.** On the target of the
product chart at `p`, the pullback of `pr₁^* β ∧ pr₂^* γ` along the inverse product chart takes on
the block basis `(b₁, 0), …, (b_m, 0), (0, b'₁), …, (0, b'_n)` the product of the values of the
chart pullbacks of `β` on `b` and of `γ` on `b'`. -/
theorem mpullback_extChartAt_prod_symm_wedge_apply {m n : ℕ}
    (β : RoughForm I B ℝ m) (γ : RoughForm J F ℝ n) (p : B × F) {y : E × E'}
    (hy : y ∈ (extChartAt (I.prod J) p).target) (b : Module.Basis (Fin m) ℝ E)
    (b' : Module.Basis (Fin n) ℝ E') :
    mpullback 𝓘(ℝ, E × E') (I.prod J) (extChartAt (I.prod J) p).symm
        (RoughForm.wedge (mpullback (I.prod J) I Prod.fst β) (mpullback (I.prod J) J Prod.snd γ))
        y ((b.prod b').reindex finSumFinEquiv) =
      mpullback 𝓘(ℝ, E) I (extChartAt I p.1).symm β y.1 b *
        mpullback 𝓘(ℝ, E') J (extChartAt J p.2).symm γ y.2 b' := by
  rw [mpullback_wedge, RoughForm.wedge_def, RoughForm.wedgeWith_apply',
    Module.Basis.coe_prod_reindex_finSumFinEquiv]
  refine (ContinuousAlternatingMap.pairedWedge_apply_append_of_forall _ _ _ _ _ _
    fun v i j ↦ ?_).trans ?_
  · -- The second factor vanishes on a tuple with an entry tangent to the first factor; as above,
    -- the entries are tangent vectors of `E × E'` only up to unfolding, hence `erw`.
    erw [mpullback_extChartAt_prod_symm_mpullback_snd_apply γ p hy]
    exact ContinuousAlternatingMap.map_coord_zero _ j
      (congrArg Prod.snd (Function.update_self j ((b i, 0) : E × E') v))
  · rw [ContinuousLinearMap.mul_apply']
    erw [mpullback_extChartAt_prod_symm_mpullback_fst_apply β p hy,
      mpullback_extChartAt_prod_symm_mpullback_snd_apply γ p hy]

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']

/-- **The integral of a product of top forms, in one chart of each factor.** Let `β` and `γ` be
continuous compactly supported top forms on oriented boundaryless manifolds `B` and `F`, with the
support of `β` in the source of the chart at `x₀` and that of `γ` in the source of the chart at
`y₀`. Then `∫_{B × F} pr₁^* β ∧ pr₂^* γ = (∫_B β) (∫_F γ)` for the product orientation. -/
theorem integralTopForm_wedge_mpullback_fst_snd_of_tsupport_subset_chart {m n : ℕ}
    (o : Manifold.Orientation I B (Fin m)) (o' : Manifold.Orientation J F (Fin n))
    {β : RoughForm I B ℝ m} {γ : RoughForm J F ℝ n} (hβ : IsSmoothForm I 0 β)
    (hγ : IsSmoothForm J 0 γ) (hβc : IsCompact (_root_.tsupport (α := E [⋀^Fin m]→L[ℝ] ℝ) β))
    (hγc : IsCompact (_root_.tsupport (α := E' [⋀^Fin n]→L[ℝ] ℝ) γ)) {x₀ : B} {y₀ : F}
    (hβx : _root_.tsupport (α := E [⋀^Fin m]→L[ℝ] ℝ) β ⊆ (chartAt H x₀).source)
    (hγy : _root_.tsupport (α := E' [⋀^Fin n]→L[ℝ] ℝ) γ ⊆ (chartAt H' y₀).source) :
    integralTopForm (o.prod o')
        (RoughForm.wedge (mpullback (I.prod J) I Prod.fst β) (mpullback (I.prod J) J Prod.snd γ)) =
      integralTopForm o β * integralTopForm o' γ := by
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  let : MeasurableSpace E' := borel E'
  let : BorelSpace E' := ⟨rfl⟩
  -- Bases of `E` and `E'`, and lifts of the orientations whose models these bases orient.
  let b := Module.finBasisOfFinrankEq ℝ E (by simpa using o.card_eq.symm)
  let b' := Module.finBasisOfFinrankEq ℝ E' (by simpa using o'.card_eq.symm)
  obtain ⟨l, rfl, hb⟩ := o.exists_lift_modelOrientation_eq b.orientation
  obtain ⟨l', rfl, hb'⟩ := o'.exists_lift_modelOrientation_eq b'.orientation
  rw [Manifold.Orientation.prod_mk]
  let P := (b.prod b').reindex finSumFinEquiv
  have hP : P.orientation = (l.prod l').modelOrientation := by
    rw [Manifold.OrientationLift.prod_modelOrientation, hb, hb']
    exact (Orientation.prod_basis_orientation b b' _ _).symm
  set φ := RoughForm.wedge (mpullback (I.prod J) I Prod.fst β)
    (mpullback (I.prod J) J Prod.snd γ) with hφ
  have hφs : IsSmoothForm (I.prod J) 0 φ :=
    (hβ.mpullback contMDiff_fst).wedge (hγ.mpullback contMDiff_snd)
  -- The support of `φ` lies in the product of the supports of `β` and `γ`.
  have hsupp : _root_.tsupport (α := (E × E') [⋀^Fin (m + n)]→L[ℝ] ℝ) φ ⊆
      _root_.tsupport (α := E [⋀^Fin m]→L[ℝ] ℝ) β ×ˢ
        _root_.tsupport (α := E' [⋀^Fin n]→L[ℝ] ℝ) γ := by
    rw [hφ, RoughForm.wedge_def]
    exact subset_inter
      ((RoughForm.tsupport_wedgeWith_subset_left _ _ _).trans
        (RoughForm.tsupport_mpullback_subset_preimage continuous_fst β))
      ((RoughForm.tsupport_wedgeWith_subset_right _ _ _).trans
        (RoughForm.tsupport_mpullback_subset_preimage continuous_snd γ))
  have hc : IsCompact (_root_.tsupport (α := (E × E') [⋀^Fin (m + n)]→L[ℝ] ℝ) φ) :=
    (hβc.prod hγc).of_isClosed_subset (isClosed_tsupport _) hsupp
  have hs : _root_.tsupport (α := (E × E') [⋀^Fin (m + n)]→L[ℝ] ℝ) φ ⊆
      (chartAt (ModelProd H H') (x₀, y₀)).source := by
    refine hsupp.trans fun q hq ↦ ?_
    simpa only [prodChartedSpace_chartAt, OpenPartialHomeomorph.prod_source, mem_prod] using
      And.intro (hβx hq.1) (hγy hq.2)
  -- The product chart has the product target, with the product Haar measure.
  have htarget : (extChartAt (I.prod J) (x₀, y₀)).target =
      (extChartAt I x₀).target ×ˢ (extChartAt J y₀).target := by
    rw [extChartAt_prod, PartialEquiv.prod_target]
  have hmeas : P.addHaar = b.addHaar.prod b'.addHaar := by
    simp only [P, Module.Basis.addHaar_reindex, Module.Basis.prod_addHaar]
  have hint := ((l.prod l').integrable_signedInChartAt_iff_mpullback φ P (x₀, y₀) P.addHaar).mp
    ((l.prod l').integrable_signedInChartAt hφs P (x₀, y₀) hc
      (by simpa only [extChartAt_source] using hs))
  rw [htarget, hmeas] at hint
  -- Fubini's theorem in the product chart.
  rw [integralTopForm_of_tsupport_subset_chart (l.prod l') hφs hc (x₀, y₀) hs P hP,
    integralTopForm_of_tsupport_subset_chart l hβ hβc x₀ hβx b hb.symm,
    integralTopForm_of_tsupport_subset_chart l' hγ hγc y₀ hγy b' hb'.symm,
    htarget, hmeas, setIntegral_prod _ hint, ← integral_mul_const]
  refine setIntegral_congr_fun (isOpen_extChartAt_target x₀).measurableSet fun a ha ↦ ?_
  rw [← integral_const_mul]
  refine setIntegral_congr_fun (isOpen_extChartAt_target y₀).measurableSet fun c hc ↦ ?_
  have hac : (a, c) ∈ (extChartAt (I.prod J) (x₀, y₀)).target := by
    rw [htarget]
    exact ⟨ha, hc⟩
  -- The block basis is a frame of `E × E'`, a tangent space only up to unfolding, hence `erw`.
  erw [mpullback_extChartAt_prod_symm_wedge_apply β γ (x₀, y₀) hac b b',
    extChartAt_prod_symm_apply, Manifold.OrientationLift.prod_signAt_of_mem l l'
      (by simpa only [extChartAt_source] using (extChartAt I x₀).map_target ha)
      (by simpa only [extChartAt_source] using (extChartAt J y₀).map_target hc)]
  push_cast
  ring

end TauCeti
