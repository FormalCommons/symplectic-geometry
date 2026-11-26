/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Average
public import TauCeti.Geometry.Manifold.DeRham.PathIntegral
import TauCeti.Geometry.Manifold.SmoothApprox.Basic
import SymplecticGeometry.Geometry.Manifold.DeRham.Basic
import SymplecticGeometry.Geometry.Manifold.GroupAction.BoundarylessModel
import SymplecticGeometry.Geometry.Manifold.DeRham.Map
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.Basic
import SymplecticGeometry.Geometry.Manifold.GroupAction.Opens
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.Smooth

/-!
# Averaging closed one-forms over a connected group

Let a group `G` that is a compact, path-connected smooth manifold act smoothly on a boundaryless
manifold `M`, and let `μ` be a probability measure on `G`. Tau Ceti's
`TauCeti.SmoothForm.measureAverage J μ` averages a form over the action, and keeps closed forms
closed. This file shows that on a Hausdorff
preconnected `M` the average of a closed one-form `γ` lies in the de Rham class of `γ`. No
invariance of `μ` is needed; with a right-invariant `μ` the average is moreover invariant
(`TauCeti.SmoothForm.mpullback_smul_measureAverage_eq_self`), so every class of `H¹` has an
invariant representative.

The argument has three steps.

* Each `g ∈ G` is joined to `1` by a path, which can be taken smooth
  (`Path.exists_homotopic_contMDiff_extend`). Acting along it is a smooth homotopy from the
  identity of `M` to `g • ·`, so by homotopy invariance
  (`TauCeti.SmoothForm.mpullback_sub_mem_exactForms_of_homotopy`) the closed form
  `(g •)^* γ - γ` is exact, in every degree.
* Along a smooth curve `c`, the integrand `(g •)^* γ` evaluated on the velocity of `c` is jointly
  continuous in the time and in `g`: it comes from a smooth family of one-forms on `ℝ` indexed by
  `G` (`SymplecticGeometry.IsSmoothFamily.continuous_apply_one`). Fubini's theorem on the compact
  `[a, b] × G` then exchanges the line integral and the average.
* Around a smooth loop, each `(g •)^* γ` has the same integral as `γ`, hence so does their
  average against a probability measure. A closed one-form on a preconnected manifold whose loop
  integrals vanish is exact (`mem_exactForms_one_iff_forall_pathIntegral_eq_zero`).

Tau Ceti's average asks the model of `M` to have no boundary. On a boundaryless manifold whose
model may have boundary, a closed one-form is carried to the copy `TauCeti.BoundarylessModel I M`
with charts in the model vector space along the inverse of the identity diffeomorphism
`TauCeti.BoundarylessModel.interiorDiffeomorph`, averaged there, and pulled back. The
diffeomorphism is equivariant, so the result is invariant, and pullback keeps closed and exact
forms, so it lies in the class of the original form. The transport follows
`TauCeti.mlieDerivForm_fundamentalVectorField_eq_zero_of_boundarylessManifold`.

## Main results

* `TauCeti.SmoothForm.mpullback_smul_sub_mem_exactForms`: an element of a path-connected group
  acts trivially on de Rham cohomology.
* `TauCeti.SmoothForm.mpullback_smul_measureAverage_eq_self`,
  `TauCeti.SmoothForm.measureAverage_eq_self_iff_forall_mpullback_smul`: Tau Ceti's invariance of
  averages, and its description of the forms that averaging fixes, stated with smooth pullbacks.
* `TauCeti.SmoothForm.pathIntegral_measureAverage`: the line integral of an average is the
  average of the line integrals.
* `TauCeti.SmoothForm.measureAverage_sub_mem_exactForms_one`: averaging a closed one-form
  changes it by an exact form.
* `TauCeti.SmoothForm.exists_invariant_sub_mem_exactForms_one`: on a boundaryless manifold, whose
  model may have boundary, every closed one-form is cohomologous to an invariant closed one-form.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  proof of Theorem 5.1.6.
* G. E. Bredon, *Introduction to Compact Transformation Groups*, Academic Press (1972),
  Chapter VI, for averaging over smooth compact transformation groups.
-/

public section

open MeasureTheory Set Bundle
open scoped Manifold ContDiff

namespace TauCeti.SmoothForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {G : Type*} [Group G] [MulAction G M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] (J : ModelWithCorners ℝ E' H')
  [TopologicalSpace G] [ChartedSpace H' G] [IsManifold J ∞ G] [ContMDiffSMul J I ∞ G M]

include J in
/-- **Elements of a path-connected group act trivially on de Rham cohomology.** If a
group `G` that is a path-connected Hausdorff manifold without boundary acts smoothly on `M`, then
for every closed real form `γ` on `M` and every `g : G`, the difference `(g •)^* γ - γ` is exact. -/
theorem mpullback_smul_sub_mem_exactForms [FiniteDimensional ℝ E'] [J.Boundaryless] [T2Space G]
    [PathConnectedSpace G] {k : ℕ} {γ : SmoothForm I M ℝ k} (hγ : γ ∈ closedForms I M k)
    (g : G) :
    mpullback (g • ·) (ContMDiffSMul.contMDiff_const_smul (I := J) (I' := I) g) γ - γ ∈
      exactForms I M k := by
  obtain ⟨p, -, hp⟩ := (PathConnectedSpace.somePath (1 : G) g).exists_homotopic_contMDiff_extend
    (J := J) ⊤
  have hF : ContMDiff (I.prod (𝓡∂ 1)) I ∞ fun q : M × Icc (0 : ℝ) 1 ↦ p.extend q.2 • q.1 :=
    (contMDiff_smul (I := J) (I' := I)).comp
      ((hp.comp (contMDiff_subtypeVal_Icc.comp contMDiff_snd)).prodMk contMDiff_fst)
  simpa using neg_mem (mpullback_sub_mem_exactForms_of_homotopy contMDiff_id
    (ContMDiffSMul.contMDiff_const_smul (I := J) (I' := I) g) hF (fun x ↦ by simp)
    (fun x ↦ by simp) hγ)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

include J in
/-- Along a smooth curve `c`, the pullbacks of a smooth one-form `γ` by the action, evaluated on
the velocity of `c`, depend jointly continuously on the time and the group element. -/
theorem continuous_mpullback_smul_apply_curveVelocity (γ : SmoothForm I M F 1)
    {c : ℝ → M} (hc : ContMDiff 𝓘(ℝ, ℝ) I ∞ c) :
    Continuous fun q : ℝ × G ↦
      TauCeti.mpullback (F := F) I I (q.2 • ·) γ.val (c q.1)
        (fun _ ↦ Manifold.curveVelocity I c q.1) := by
  have hf : ContMDiff (J.prod 𝓘(ℝ, ℝ)) I ∞ fun q : G × ℝ ↦ q.1 • c q.2 :=
    (contMDiff_smul (I := J) (I' := I)).comp (contMDiff_fst.prodMk (hc.comp contMDiff_snd))
  have key : ∀ q : ℝ × G, TauCeti.mpullback (F := F) I I (q.2 • ·) γ.val (c q.1)
      (fun _ ↦ Manifold.curveVelocity I c q.1) =
      (SmoothForm.mpullback (fun s ↦ q.2 • c s)
        (hf.comp (contMDiff_const.prodMk contMDiff_id)) γ).val q.1 (fun _ ↦ 1) := by
    intro q
    rw [SmoothForm.mpullback_apply, TauCeti.mpullback_apply, Manifold.curveVelocity_apply]
    congr 1
    funext _
    exact (mfderiv_comp_apply (I' := I) q.1
      ((ContMDiffSMul.contMDiff_const_smul (I := J) (I' := I) q.2).mdifferentiableAt (n := ∞)
        (by simp)) ((hc q.1).mdifferentiableAt (by simp)) 1).symm
  simp_rw [key]
  exact ((SymplecticGeometry.isSmoothFamily_const (J := J) (N := G) γ).mpullback_family
    hf).continuous_apply_one.comp continuous_swap

variable [MeasurableSpace G] [OpensMeasurableSpace G] [CompactSpace G] [T2Space G] (μ : Measure G)

section Invariant

variable [I.Boundaryless] [CompleteSpace F] [IsFiniteMeasure μ] [MeasurableMul G]
  [μ.IsMulRightInvariant] {k : ℕ}

/-- **Averages are invariant**, for smooth forms. For a right-invariant finite measure `μ` on `G`,
the smooth pullback by each `b • ·` fixes the average of a smooth form `α`. Tau Ceti's
`TauCeti.SmoothForm.mpullback_smul_measureAverage` states this on the underlying rough forms. -/
theorem mpullback_smul_measureAverage_eq_self (α : SmoothForm I M F k) (b : G) :
    mpullback (b • ·) (ContMDiffSMul.contMDiff_const_smul (I := J) (I' := I) b)
      (measureAverage J μ α) = measureAverage J μ α :=
  (mpullback_eq_iff _).2 (mpullback_smul_measureAverage J μ α b)

/-- **Averaging fixes exactly the invariant forms**, for smooth forms. For a right-invariant
probability measure `μ` on `G`, the average of a smooth form `α` is `α` if and only if the smooth
pullback by every `a • ·` fixes `α`. Tau Ceti's `TauCeti.SmoothForm.measureAverage_eq_self_iff`
states the invariance on the underlying rough forms. -/
theorem measureAverage_eq_self_iff_forall_mpullback_smul [IsProbabilityMeasure μ]
    (α : SmoothForm I M F k) :
    measureAverage J μ α = α ↔ ∀ a : G,
      mpullback (a • ·) (ContMDiffSMul.contMDiff_const_smul (I := J) (I' := I) a) α = α := by
  simp only [mpullback_eq_iff]
  exact measureAverage_eq_self_iff J μ α

end Invariant

/-- **Line integrals commute with averaging.** Along a smooth curve `c`, the line integral of the
average of a smooth one-form `γ` over `G` is the average over `G` of the line integrals of the
pullbacks `(g •)^* γ`. -/
theorem pathIntegral_measureAverage [I.Boundaryless] [CompleteSpace F] [IsFiniteMeasure μ]
    (γ : SmoothForm I M F 1) {c : ℝ → M} (hc : ContMDiff 𝓘(ℝ, ℝ) I ∞ c) (a b : ℝ) :
    pathIntegral (measureAverage J μ γ : RoughForm I M F 1) c a b =
      ∫ g, pathIntegral (mpullback (g • ·)
        (ContMDiffSMul.contMDiff_const_smul (I := J) (I' := I) g) γ : RoughForm I M F 1)
          c a b ∂μ := by
  have hint : Integrable (Function.uncurry fun (t : ℝ) (g : G) ↦
      TauCeti.mpullback (F := F) I I (g • ·) γ.val (c t)
        (fun _ ↦ Manifold.curveVelocity I c t)) ((volume.restrict (uIoc a b)).prod μ) := by
    rw [← Measure.restrict_univ (μ := μ), Measure.prod_restrict, ← IntegrableOn]
    exact ((continuous_mpullback_smul_apply_curveVelocity J γ hc).continuousOn.integrableOn_compact
      (isCompact_uIcc.prod isCompact_univ)).mono_set (prod_mono uIoc_subset_uIcc subset_rfl)
  simp only [pathIntegral_def, coe_mpullback]
  rw [← intervalIntegral_integral_swap hint]
  refine intervalIntegral.integral_congr fun t _ ↦ ?_
  simp only [measureAverage_apply, TauCeti.mpullback_apply]

/-- **Averaging a closed one-form changes it by an exact form.** Let a group `G` that is a
compact, path-connected smooth manifold act smoothly on a Hausdorff, preconnected, boundaryless
manifold `M`, and let `μ` be a probability measure on `G`. For a closed real one-form `γ` on `M`,
the difference between its average over `G` and `γ` is exact: the average represents the de Rham
class of `γ`. -/
theorem measureAverage_sub_mem_exactForms_one [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
    [I.Boundaryless] [J.Boundaryless] [T2Space M] [PreconnectedSpace M] [PathConnectedSpace G]
    [IsProbabilityMeasure μ] {γ : SmoothForm I M ℝ 1} (hγ : γ ∈ closedForms I M 1) :
    measureAverage J μ γ - γ ∈ exactForms I M 1 := by
  rcases isEmpty_or_nonempty M with hM | ⟨⟨x₀⟩⟩
  · rw [Subsingleton.elim (measureAverage J μ γ - γ) 0]
    exact zero_mem _
  have hclosed : measureAverage J μ γ ∈ closedForms I M 1 :=
    (IsClosed.measureAverage J μ ((isClosed_iff_mem_closedForms γ).2 hγ)).mem_closedForms
  rw [mem_exactForms_one_iff_forall_pathIntegral_eq_zero (sub_mem hclosed hγ) x₀]
  intro c hc hc₀ hc₁
  have hc' : ContMDiff 𝓘(ℝ, ℝ) I 1 c := hc.of_le (by simp)
  have hint (φ : SmoothForm I M ℝ 1) := (φ.isSmoothForm.of_le (by simp) :
    IsSmoothForm I 0 φ.val).intervalIntegrable_apply_curveVelocity hc' 0 1
  -- Each `(g •)^* γ - γ` is exact, so `(g •)^* γ` and `γ` have the same integral around `c`.
  have h (g : G) : pathIntegral (mpullback (g • ·)
      (ContMDiffSMul.contMDiff_const_smul (I := J) (I' := I) g) γ : RoughForm I M ℝ 1) c 0 1 =
      pathIntegral (γ : RoughForm I M ℝ 1) c 0 1 := by
    have := pathIntegral_eq_zero_of_mem_exactForms (mpullback_smul_sub_mem_exactForms J hγ g) hc'
      (hc₀.trans hc₁.symm)
    rwa [Submodule.coe_sub, pathIntegral_sub (hint _) (hint _), sub_eq_zero] at this
  rw [Submodule.coe_sub, pathIntegral_sub (hint _) (hint _), pathIntegral_measureAverage J μ γ hc]
  simp only [h, integral_const, probReal_univ, one_smul, sub_self]

attribute [local instance] BoundarylessModel.interiorChartedSpace in
/-- **Closed one-forms have invariant representatives**, on a boundaryless manifold whose model
may have boundary. Let a group `G` that is a compact, path-connected smooth manifold act smoothly
on a Hausdorff, preconnected, boundaryless manifold `M`, and let `μ` be a right-invariant
probability measure on `G`. Every closed real one-form `γ` on `M` differs by an exact form from a
closed one-form `γ'` invariant under every `g • ·`. -/
theorem exists_invariant_sub_mem_exactForms_one [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
    [BoundarylessManifold I M] [J.Boundaryless] [T2Space M] [PreconnectedSpace M]
    [PathConnectedSpace G] [MeasurableMul G] [μ.IsMulRightInvariant] [IsProbabilityMeasure μ]
    {γ : SmoothForm I M ℝ 1} (hγ : γ ∈ closedForms I M 1) :
    ∃ γ' ∈ closedForms I M 1, (∀ g : G,
      mpullback (g • ·) (ContMDiffSMul.contMDiff_const_smul (I := J) (I' := I) g) γ' = γ') ∧
        γ' - γ ∈ exactForms I M 1 := by
  -- Carry `γ` to the copy of `M` with charts in `E`, average it there, and carry it back.
  let Φ := BoundarylessModel.interiorDiffeomorph I (M := M) ∞
  let β := mpullback Φ.symm Φ.symm.contMDiff γ
  have hβ : β ∈ closedForms 𝓘(ℝ, E) (BoundarylessModel I M) 1 :=
    mpullback_mem_closedForms _ _ hγ
  have hβ' : measureAverage J μ β ∈ closedForms 𝓘(ℝ, E) (BoundarylessModel I M) 1 :=
    (IsClosed.measureAverage J μ ((isClosed_iff_mem_closedForms β).2 hβ)).mem_closedForms
  refine ⟨mpullback Φ Φ.contMDiff (measureAverage J μ β), mpullback_mem_closedForms _ _ hβ',
    fun g ↦ ?_, ?_⟩
  · -- The map `Φ` is equivariant, and the average is invariant.
    have : ContMDiffConstSMul I ∞ G M := ContMDiffSMul.contMDiffConstSMul J
    exact mpullback_smul_mpullback Φ.contMDiff (BoundarylessModel.interiorDiffeomorph_smul I ∞ g)
      (mpullback_smul_measureAverage_eq_self J μ β g)
  · -- The difference is the pullback of the exact form `avg β - β`.
    have h := closedForms.mpullback_mem_exactForms Φ Φ.contMDiff 1
      ⟨_, sub_mem hβ' hβ⟩ (measureAverage_sub_mem_exactForms_one J μ hβ)
    rwa [closedForms.coe_mpullback, map_sub, mpullback_mpullback_symm] at h

end TauCeti.SmoothForm
