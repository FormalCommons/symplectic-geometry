/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Blowup.Weight.Basic
public import SymplecticGeometry.Geometry.Symplectic.IsotopyExtension.Ball.Volume

/-!
# The volume of the blowup of weight `λ`

Let `ψ` be a symplectic embedding of the closed ball of radius `√(l² + ε²)` into `M`, for
`0 ≤ l` and `0 < ε`, and let `M̃_ψ = WeightBlowup hψ hl hε` be the blowup of weight `l` of
`Blowup/Weight/Basic.lean`, with its form `ω̃_ψ`. Following McDuff–Salamon, §7.1, blowing up
removes the volume of the ball `B(l)`: the Liouville measure of `M̃_ψ` plus the Lebesgue measure of
`B(l)`, which is the Liouville measure of the standard form `ω₀`, is the Liouville measure of `M`,
in `ℝ≥0∞`, so that `M` need not be compact.

## Main results

* `SymplecticGeometry.BlowupModel.liouvilleMeasure_exceptionalDivisor`: the exceptional divisor
  `Z` of the model `BlowupModel n` is null for the Liouville measure of every two-form. In the
  chart `blowupModelChart i`, `Z` lies in the hyperplane `w i = 0`.
* `SymplecticGeometry.WeightBlowup.liouvilleMeasure_form_add`: the volume of the blowup of weight
  `l` plus the volume of `B(l)` is the volume of `M`.

The proof cuts the blowup in two: the complement of the divisor, which is the image of the outer
piece `M ∖ ψ(B(l))` under the open embedding `GluedAlong.inl` pulling `ω̃_ψ` back to `σ`, and the
divisor, the image of `Z` under `GluedAlong.inr`, which is null. It cuts `M` into the outer piece
and `ψ(B(l))`, and computes the measure of the latter with
`SymplecticGeometry.IsSymplecticBallEmbedding.liouvilleMeasure_image`, since `ψ` pulls `σ` back
to `ω₀` on the open ball of radius `√(l² + ε²)`. Neither `σ` nor `ω̃_ψ` needs to be closed or
nondegenerate for this.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §7.1.
-/

public section

noncomputable section

open Set Metric MeasureTheory TopologicalSpace TauCeti Module Projectivization
open scoped Manifold ContDiff ENNReal TauCeti.ComplexManifold

namespace SymplecticGeometry

namespace BlowupModel

variable {n m : ℕ}

/-- In the chart `blowupModelChart i`, the exceptional divisor lies in the real hyperplane
`w i = 0`. -/
private theorem blowupModelChart_image_exceptionalDivisor_subset (i : Fin (n + 1)) :
    blowupModelChart i '' exceptionalDivisor n ⊆
      (LinearMap.ker (LinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) ↦ ℂ) i) :
        Set (Fin (n + 1) → ℂ)) := by
  rintro _ ⟨p, hp, rfl⟩
  simp [(mem_exceptionalDivisor_iff).1 hp]

/-- The part of the exceptional divisor in the source of the chart at a point is null for the
Liouville measure of every two-form. -/
private theorem liouvilleMeasure_exceptionalDivisor_inter_chartAt_source
    [Fact (finrank ℝ (Fin (n + 1) → ℂ) = 2 * m)] [MeasurableSpace (BlowupModel n)]
    [BorelSpace (BlowupModel n)] (σ : SmoothTwoForm 𝓘(ℝ, Fin (n + 1) → ℂ) (BlowupModel n))
    (p : BlowupModel n) :
    σ.liouvilleMeasure m (exceptionalDivisor n ∩ (chartAt (Fin (n + 1) → ℂ) p).source) = 0 := by
  let : MeasurableSpace (Fin (n + 1) → ℂ) := borel _
  have : BorelSpace (Fin (n + 1) → ℂ) := ⟨rfl⟩
  rw [SmoothTwoForm.liouvilleMeasure_apply_of_subset (α := p)
    (isClosed_exceptionalDivisor.measurableSet.inter
      (chartAt (Fin (n + 1) → ℂ) p).open_source.measurableSet)
    (by rw [extChartAt_source]; exact inter_subset_right)]
  refine setLIntegral_measure_zero _ _ (measure_mono_null ?_
    (Measure.addHaar_submodule _ (LinearMap.ker (LinearMap.proj (R := ℝ)
      (φ := fun _ : Fin (n + 1) ↦ ℂ) (exists_mem_affineOpen p.pr).choose)) ?_))
  · rw [extChartAt_coe, modelWithCornersSelf_coe, Function.id_comp, chartAt_eq]
    exact (image_mono inter_subset_left).trans (blowupModelChart_image_exceptionalDivisor_subset _)
  · intro h
    have : Pi.single (exists_mem_affineOpen p.pr).choose (1 : ℂ) ∈
        LinearMap.ker (LinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) ↦ ℂ)
          (exists_mem_affineOpen p.pr).choose) := h ▸ Submodule.mem_top
    simp at this

variable [Fact (finrank ℝ (Fin (n + 1) → ℂ) = 2 * m)]
  [MeasurableSpace (BlowupModel n)] [BorelSpace (BlowupModel n)]

/-- **The exceptional divisor is null**: for every two-form `σ` on the model `BlowupModel n`, the
exceptional divisor `Z` has Liouville measure zero. -/
theorem liouvilleMeasure_exceptionalDivisor
    (σ : SmoothTwoForm 𝓘(ℝ, Fin (n + 1) → ℂ) (BlowupModel n)) :
    σ.liouvilleMeasure m (exceptionalDivisor n) = 0 := by
  -- The charts at the points of `Z` are among the finitely many charts `blowupModelChart i`.
  have hcover : exceptionalDivisor n ⊆ ⋃ (i : Fin (n + 1))
      (_ : ∃ p ∈ exceptionalDivisor n, chartAt (Fin (n + 1) → ℂ) p = blowupModelChart i),
      exceptionalDivisor n ∩ (blowupModelChart i).source := by
    intro p hp
    simp only [mem_iUnion]
    exact ⟨_, ⟨p, hp, chartAt_eq p⟩, hp, chartAt_eq p ▸ mem_chart_source _ p⟩
  refine measure_mono_null hcover (measure_iUnion_null fun i ↦ measure_iUnion_null ?_)
  rintro ⟨p, -, hp⟩
  rw [← hp]
  exact liouvilleMeasure_exceptionalDivisor_inter_chartAt_source σ p

end BlowupModel

namespace WeightBlowup

open BlowupModel

variable {n m : ℕ} [Fact (finrank ℝ (Fin (n + 1) → ℂ) = 2 * m)]
  {M : Type} [TopologicalSpace M] [ChartedSpace (Fin (n + 1) → ℂ) M]
  [IsManifold 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]
  {σ : SmoothTwoForm 𝓘(ℝ, Fin (n + 1) → ℂ) M} {ψ : StdSpace (Fin (n + 1)) → M} {l ε : ℝ}

variable (hψ : IsSymplecticBallEmbedding σ (√(l ^ 2 + ε ^ 2)) ψ) (hl : 0 ≤ l) (hε : 0 < ε)
  [MeasurableSpace (WeightBlowup hψ hl hε)] [BorelSpace (WeightBlowup hψ hl hε)]

/-- The complement of the divisor has, for the Liouville measure of `ω̃_ψ`, the volume of
`M ∖ ψ(B(l))` for that of `σ`. -/
theorem liouvilleMeasure_form_complDivisor :
    (form hψ hl hε).liouvilleMeasure m (complDivisor hψ hl hε) =
      σ.liouvilleMeasure m (outerPiece hψ) := by
  have hinl :=
    (GluedAlong.isOpenEmbedding_inl (gluingDiffeomorph hψ hl hε).symm).measurableEmbedding
  -- `inl` pulls `ω̃_ψ` back to the restriction of `σ`.
  have hmap := hinl.map_liouvilleMeasure (n := m)
    ((GluedAlong.isLocalDiffeomorph_inl _).contMDiff.mdifferentiable (by simp))
    (τ := form hψ hl hε) (σ := SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ)
    (by rw [← mpullback_inl_form hψ hl hε, SmoothForm.coe_mpullback])
  rw [← Measure.restrict_apply_univ, coe_complDivisor, ← hmap,
    Measure.map_apply hinl.measurable MeasurableSet.univ, preimage_univ,
    ← Measure.restrict_apply_univ (s := (outerPiece hψ : Set M)),
    ← SmoothTwoForm.map_liouvilleMeasure_mpullback_subtypeVal,
    Measure.map_apply measurable_subtypeVal MeasurableSet.univ, preimage_univ]

omit [MeasurableSpace M] [BorelSpace M] in
/-- The divisor of the blowup is null for the Liouville measure of `ω̃_ψ`. -/
theorem liouvilleMeasure_form_range_divisor :
    (form hψ hl hε).liouvilleMeasure m (range (divisor hψ hl hε)) = 0 := by
  let : MeasurableSpace (BlowupModel n) := borel _
  have : BorelSpace (BlowupModel n) := ⟨rfl⟩
  have hinr :=
    (GluedAlong.isOpenEmbedding_inr (gluingDiffeomorph hψ hl hε).symm).measurableEmbedding
  -- `inr` pulls `ω̃_ψ` back to the restriction of `ω̃_l`.
  have hmap := hinr.map_liouvilleMeasure (n := m)
    ((GluedAlong.isLocalDiffeomorph_inr _).contMDiff.mdifferentiable (by simp))
    (τ := form hψ hl hε)
    (σ := SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (blowupForm n l))
    (by rw [← mpullback_inr_form hψ hl hε, SmoothForm.coe_mpullback])
  -- The divisor is the image under `inr` of the exceptional divisor of the model piece.
  have hrange : range (divisor hψ hl hε) = GluedAlong.inr (gluingDiffeomorph hψ hl hε).symm ''
      {y : modelPiece n ε | (y : BlowupModel n) ∈ exceptionalDivisor n} := by
    ext z
    rw [range_divisor, mem_compl_iff, SetLike.mem_coe, mem_complDivisor_iff, not_not]
  have hsub : range (divisor hψ hl hε) ⊆ range (GluedAlong.inr (gluingDiffeomorph hψ hl hε).symm) :=
    hrange ▸ image_subset_range _ _
  rw [← Measure.restrict_eq_self _ hsub, ← hmap, hinr.map_apply, hrange,
    preimage_image_eq _ (GluedAlong.inr_injective _),
    SmoothTwoForm.liouvilleMeasure_mpullback_subtypeVal,
    MeasurableEmbedding.comap_apply (f := (Subtype.val : modelPiece n ε → BlowupModel n))
      (MeasurableEmbedding.subtypeVal (modelPiece n ε).isOpen.measurableSet)]
  exact measure_mono_null (by rintro _ ⟨y, hy, rfl⟩; exact hy)
    (liouvilleMeasure_exceptionalDivisor _)

/-- **The volume of the blowup of weight `l`**, following McDuff–Salamon, §7.1: the Liouville
measure of the blowup `M̃_ψ` for its form `ω̃_ψ`, plus the volume of the closed ball `B(l)`, is the
Liouville measure of `M` for `σ`. The volume of `B(l)` is its Lebesgue measure, which is its
Liouville measure for the standard form `ω₀` (`liouvilleMeasure_constSmooth_stdForm`). -/
theorem liouvilleMeasure_form_add :
    (form hψ hl hε).liouvilleMeasure m univ + volume (closedBall (0 : StdSpace (Fin (n + 1))) l) =
      σ.liouvilleMeasure m univ := by
  obtain rfl : m = n + 1 := by
    have h := (Fact.out : finrank ℝ (Fin (n + 1) → ℂ) = 2 * m)
    rw [Module.finrank_pi_fintype] at h
    simp at h
    omega
  have hc : ((outerPiece hψ : Set M))ᶜ = ψ '' closedBall 0 l := by
    ext
    simp
  rw [← measure_add_measure_compl (complDivisor hψ hl hε).isOpen.measurableSet,
    ← measure_add_measure_compl (s := (outerPiece hψ : Set M)) (outerPiece hψ).isOpen.measurableSet,
    ← range_divisor, liouvilleMeasure_form_range_divisor, liouvilleMeasure_form_complDivisor,
    add_zero, hc, hψ.liouvilleMeasure_image
      (closedBall_subset_ball (Real.lt_sqrt_of_sq_lt (by nlinarith)))]

end WeightBlowup

end SymplecticGeometry

end
