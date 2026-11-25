/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import TauCeti.MeasureTheory.Measure.Lebesgue.OrthogonalSlices

/-!
# Slices of a set along a complex direction

Let `E` be a finite-dimensional complex vector space with a real inner product for which
scalars act compatibly (such as `EuclideanSpace ℂ (Fin m)`), `v : E`, and `A` a closed set
that meets each complex line `{c + s • v | s : ℂ}` in at most `N` points. Then the points `c`
of the unit ball for which `c + s • v ∈ A` for some `‖s‖ < ρ` form a set of volume at most
`C * N * ρ ^ 2 * ‖v‖ ^ 2`, with `C` the volume of the ball of radius `2` about `0` in `E`
(`MeasureTheory.volume_setOf_exists_add_smul_mem_le`).

The proof is Tonelli's theorem along `E = Kᗮ ⊕ K`, with `K` the complex line spanned by `v`,
in the form of Tau Ceti's `Submodule.lintegral_eq_lintegral_lintegral_add`. A slice parallel
to `K` meets the set only over the unit ball of `Kᗮ`, and then lies in at most `N` discs of
radius `ρ * ‖v‖` in `K`. The volumes of the unit balls of `K` and `Kᗮ` multiply to at most
the volume of the ball of radius `2` in `E`
(`Submodule.volume_ball_mul_volume_ball_orthogonal_le`, from Tau Ceti's
`Submodule.volume_preimage_measurableEquivProd_prod`).

That `A` is closed makes the set measurable
(`IsClosed.setOf_exists_norm_le_add_smul_mem`); zero sets of polynomials are closed.

## Main results

* `MeasureTheory.volume_setOf_exists_add_smul_mem_le`: the volume bound.
* `Submodule.volume_ball_mul_volume_ball_orthogonal_le`: balls in a subspace and in its
  orthogonal complement.
* `Submodule.finrank_restrictScalars_span_singleton_complex`: a complex line has real
  dimension `2`.
-/

public section

open MeasureTheory Metric Set
open scoped ENNReal

/-- The points from which a closed set can be reached by a move of size at most `ρ` along the
complex direction `v` form a closed set. -/
theorem IsClosed.setOf_exists_norm_le_add_smul_mem {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {A : Set E} (hA : IsClosed A) (v : E) (ρ : ℝ) :
    IsClosed {c : E | ∃ s : ℂ, ‖s‖ ≤ ρ ∧ c + s • v ∈ A} := by
  have hD : IsCompact ((fun s : ℂ ↦ -(s • v)) '' closedBall 0 ρ) :=
    (isCompact_closedBall 0 ρ).image (by fun_prop)
  convert hA.add_left_of_isCompact hD using 1
  ext c
  simp only [mem_ofPred_eq, Set.mem_add, mem_image, mem_closedBall, dist_zero_right]
  constructor
  · rintro ⟨s, hs, hc⟩
    exact ⟨-(s • v), ⟨s, hs, rfl⟩, c + s • v, hc, by abel⟩
  · rintro ⟨_, ⟨s, hs, rfl⟩, a, ha, rfl⟩
    exact ⟨s, hs, by simpa using ha⟩

namespace Submodule

/-- The complex line spanned by a nonzero vector has real dimension `2`. -/
theorem finrank_restrictScalars_span_singleton_complex {V : Type*} [AddCommGroup V]
    [Module ℂ V] [Module ℝ V] [IsScalarTower ℝ ℂ V] {v : V} (hv : v ≠ 0) :
    Module.finrank ℝ ((ℂ ∙ v).restrictScalars ℝ) = 2 := by
  rw [← Complex.finrank_real_complex,
    (((LinearEquiv.toSpanNonzeroSingleton ℂ V v hv) ≪≫ₗ
      (restrictScalarsEquiv ℝ ℂ V (ℂ ∙ v)).symm).restrictScalars ℝ).finrank_eq]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The balls of radii `r` and `r'` about `0` in a subspace `K` and in its orthogonal
complement have volumes whose product is at most the volume of the ball of radius `r + r'`
about `0` in the whole space. -/
theorem volume_ball_mul_volume_ball_orthogonal_le (K : Submodule ℝ E) (r r' : ℝ) :
    volume (ball (0 : K) r) * volume (ball (0 : Kᗮ) r') ≤ volume (ball (0 : E) (r + r')) := by
  rw [← K.volume_preimage_measurableEquivProd_prod 0]
  refine measure_mono fun x hx ↦ ?_
  rw [mem_ball_zero_iff, ← K.measurableEquivProd_fst_add_add_snd 0 x, add_zero]
  exact (norm_add_le _ _).trans_lt (add_lt_add (by simpa using hx.1) (by simpa using hx.2))

end Submodule

namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A slice of `{c ∈ ball 0 1 | ∃ s, ‖s‖ ≤ ρ ∧ c + s • v ∈ A}` parallel to the complex line
`K` spanned by `v` is empty over the outside of the unit ball of `Kᗮ`, and lies in `N` discs
of radius `ρ * ‖v‖` over its inside. -/
private theorem lintegral_indicator_add_le {A : Set E} (v : E) (N : ℕ)
    (hN : ∀ c : E, {s : ℂ | c + s • v ∈ A}.encard ≤ N) (ρ : ℝ) :
    ∀ w : ((ℂ ∙ v).restrictScalars ℝ)ᗮ,
    ∫⁻ a : (ℂ ∙ v).restrictScalars ℝ,
        (ball (0 : E) 1 ∩ {c : E | ∃ s : ℂ, ‖s‖ ≤ ρ ∧ c + s • v ∈ A}).indicator 1 (w + a) ≤
      (ball 0 1).indicator
        (fun _ ↦ N * volume (closedBall (0 : (ℂ ∙ v).restrictScalars ℝ) (ρ * ‖v‖))) w := by
  set K : Submodule ℝ E := (ℂ ∙ v).restrictScalars ℝ
  set T := ball (0 : E) 1 ∩ {c : E | ∃ s : ℂ, ‖s‖ ≤ ρ ∧ c + s • v ∈ A}
  have hvK (u : ℂ) : u • v ∈ K := (ℂ ∙ v).smul_mem u (Submodule.mem_span_singleton_self v)
  intro w
  by_cases hw : w ∈ ball (0 : Kᗮ) 1
  swap
  · -- Off the unit ball of `Kᗮ`, the slice is empty, since `‖w‖ ≤ ‖w + a‖`.
    rw [indicator_of_notMem hw]
    refine (lintegral_mono fun a ↦ (indicator_of_notMem (fun ha ↦ hw ?_) _).le).trans_eq
      lintegral_zero
    have h0 : inner ℝ (w : E) a = 0 :=
      Submodule.inner_left_of_mem_orthogonal a.property w.property
    have h1 := norm_add_sq_eq_norm_sq_add_norm_sq_real h0
    have h2 : ‖(w : E) + a‖ < 1 := mem_ball_zero_iff.1 ha.1
    rw [mem_ball_zero_iff, ← Submodule.norm_coe]
    nlinarith [norm_nonneg (w : E), norm_nonneg ((w : E) + a), norm_nonneg (a : E)]
  rw [indicator_of_mem hw]
  have hfin : {u : ℂ | (w : E) + u • v ∈ A}.Finite := finite_of_encard_le_coe (hN w)
  -- The slice lies in the discs about the points `u • v` with `w + u • v ∈ A`.
  set U : Set K := ⋃ u ∈ hfin.toFinset, closedBall ⟨u • v, hvK u⟩ (ρ * ‖v‖)
  have hU : MeasurableSet U := Finset.measurableSet_biUnion _ fun _ _ ↦ measurableSet_closedBall
  have hTU (a : K) : T.indicator 1 ((w : E) + a) ≤ U.indicator (1 : K → ℝ≥0∞) a := by
    by_cases ha : (w : E) + a ∈ T
    · obtain ⟨-, s, hs, hsA⟩ := ha
      obtain ⟨t, ht⟩ :=
        Submodule.mem_span_singleton.1 ((Submodule.restrictScalars_mem ℝ _ _).1 a.property)
      have hu : t + s ∈ hfin.toFinset := by
        rw [← ht] at hsA
        simpa [add_smul, add_assoc] using hsA
      rw [indicator_of_mem (show a ∈ U from mem_biUnion hu ?_)]
      · exact indicator_apply_le' (fun _ ↦ le_rfl) fun _ ↦ by simp
      rw [mem_closedBall, dist_eq_norm, ← Submodule.norm_coe, Submodule.coe_sub, ← ht,
        ← sub_smul, norm_smul, sub_add_cancel_left, norm_neg]
      exact mul_le_mul_of_nonneg_right hs (norm_nonneg v)
    · simp [indicator_of_notMem ha]
  calc ∫⁻ a : K, T.indicator 1 ((w : E) + a) ≤ ∫⁻ a : K, U.indicator 1 a := lintegral_mono hTU
    _ = volume U := lintegral_indicator_one hU
    _ ≤ ∑ u ∈ hfin.toFinset, volume (closedBall (⟨u • v, hvK u⟩ : K) (ρ * ‖v‖)) :=
      measure_biUnion_finset_le _ _
    _ = hfin.toFinset.card * volume (closedBall (0 : K) (ρ * ‖v‖)) := by
      simp [Measure.addHaar_closedBall_center]
    _ ≤ N * volume (closedBall (0 : K) (ρ * ‖v‖)) := by
      gcongr
      rw [← Set.ncard_eq_toFinset_card _ hfin, ← Nat.cast_le (α := ℕ∞), hfin.cast_ncard_eq]
      exact hN w

/-- **Slices along a complex direction.** Let `A` be a closed set in a finite-dimensional
complex space `E` with a real inner product, and `v : E`. If `A` meets every complex line
`{c + s • v | s : ℂ}` in at most `N` points, then the points `c` of the unit ball such that
`c + s • v ∈ A` for some `‖s‖ < ρ` form a set of volume at most `C * N * ρ ^ 2 * ‖v‖ ^ 2`,
where `C` is the volume of the ball of radius `2` about `0` in `E`. -/
theorem volume_setOf_exists_add_smul_mem_le {A : Set E} (hA : IsClosed A) (v : E) (N : ℕ)
    (hN : ∀ c : E, {s : ℂ | c + s • v ∈ A}.encard ≤ N) (ρ : ℝ) :
    volume {c ∈ ball (0 : E) 1 | ∃ s : ℂ, ‖s‖ < ρ ∧ c + s • v ∈ A} ≤
      ENNReal.ofReal (volume.real (ball (0 : E) 2) * N * ρ ^ 2 * ‖v‖ ^ 2) := by
  set S := {c ∈ ball (0 : E) 1 | ∃ s : ℂ, ‖s‖ < ρ ∧ c + s • v ∈ A}
  -- If `v = 0`, the hypothesis forces `A = ∅`; if `ρ ≤ 0`, no `s` qualifies.
  rcases eq_or_ne v 0 with rfl | hv
  · suffices S = ∅ by simp [this]
    refine eq_empty_of_forall_notMem fun c ⟨_, s, _, hc⟩ ↦ ?_
    have := hN c
    simp_all
  rcases le_or_gt ρ 0 with hρ | hρ
  · suffices S = ∅ by simp [this]
    exact eq_empty_of_forall_notMem fun c ⟨_, s, hs, _⟩ ↦ ((norm_nonneg s).trans_lt hs).not_ge hρ
  set K : Submodule ℝ E := (ℂ ∙ v).restrictScalars ℝ
  set T := ball (0 : E) 1 ∩ {c : E | ∃ s : ℂ, ‖s‖ ≤ ρ ∧ c + s • v ∈ A}
  have hT : MeasurableSet T :=
    measurableSet_ball.inter (hA.setOf_exists_norm_le_add_smul_mem v ρ).measurableSet
  have hball : volume (ball (0 : E) 2) ≠ ∞ := measure_ball_lt_top.ne
  calc volume S ≤ volume T := measure_mono fun c ⟨hc, s, hs, hcs⟩ ↦ ⟨hc, s, hs.le, hcs⟩
    _ = ∫⁻ x, T.indicator 1 x := (lintegral_indicator_one hT).symm
    _ = ∫⁻ w : Kᗮ, ∫⁻ a : K, T.indicator 1 ((w : E) + a) :=
      K.lintegral_eq_lintegral_lintegral_add (measurable_one.indicator hT).aemeasurable
    _ ≤ ∫⁻ w : Kᗮ, (ball (0 : Kᗮ) 1).indicator
        (fun _ ↦ N * volume (closedBall (0 : K) (ρ * ‖v‖))) w :=
      lintegral_mono (lintegral_indicator_add_le v N hN ρ)
    _ = N * ENNReal.ofReal ((ρ * ‖v‖) ^ 2) *
        (volume (ball (0 : K) 1) * volume (ball (0 : Kᗮ) 1)) := by
      rw [lintegral_indicator_const measurableSet_ball, Measure.addHaar_closedBall _ _
        (by positivity), Submodule.finrank_restrictScalars_span_singleton_complex hv]
      ring
    _ ≤ N * ENNReal.ofReal ((ρ * ‖v‖) ^ 2) * volume (ball (0 : E) 2) := by
      gcongr
      simpa [one_add_one_eq_two] using K.volume_ball_mul_volume_ball_orthogonal_le 1 1
    _ = ENNReal.ofReal (volume.real (ball (0 : E) 2) * N * ρ ^ 2 * ‖v‖ ^ 2) := by
      rw [show volume.real (ball (0 : E) 2) * N * ρ ^ 2 * ‖v‖ ^ 2 =
          N * ((ρ * ‖v‖) ^ 2 * volume.real (ball (0 : E) 2)) by ring,
        ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
        ENNReal.ofReal_mul (by positivity), measureReal_def, ENNReal.ofReal_toReal hball,
        mul_assoc]

end MeasureTheory

end
