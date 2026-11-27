/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.AsymptoticallyHolomorphic.RescaledChart
public import SymplecticGeometry.Geometry.Symplectic.AsymptoticallyHolomorphic.Power.Basic
public import SymplecticGeometry.Analysis.Calculus.IteratedFDeriv.JetNorm

/-!
# Sections read in rescaled unitary charts, and their jet norms

Let `D` be rescaled unitary charts (`SymplecticGeometry.RescaledUnitaryCharts`) for a principal
`Circle`-bundle `P`. For a power `k` and a point `x`, the chart `D.chart k x` and the frame
`D.frame k x` turn a section `s` of the line bundle `PowerBundle P k` into a complex function on
`StdSpace ι`: its value at `z` is the coordinate of `s` at the point `(D.chart k x).symm z`, in the
unitary frame `[D.frame k x _, 1]` of that fibre. This is `D.reading k x s`, and
`SymplecticGeometry.RescaledUnitaryCharts.apply_chart_symm_eq_mk` recovers `s` from it. The
reading is complex linear in `s`.

The `r`-jet norm `D.jetNorm k r s x` is the jet norm `SymplecticGeometry.jetNormAt ℝ r` of the
reading at the centre `0` of the chart: the sum, over the orders `j ≤ r`, of the norms of the
`j`-th derivatives (Mathlib's `iteratedFDeriv`) of the reading there. Its lemmas come from those
of `jetNormAt`. It is nonnegative and monotone in `r`; for `k₀ ≤ k` its order `0` is the norm of
`s x`, since the chart sends `x` to `0` (`SymplecticGeometry.RescaledUnitaryCharts.chart_symm_zero`)
and the frame is unitary; it vanishes on the zero section and is unchanged by negation; and for
sections whose readings are `C^r` at `0` it satisfies the triangle inequality and scales by `‖c‖`
under multiplication by `c : ℂ`.

These are the chart norms by which the estimates on asymptotically holomorphic sequences of
sections are stated, in the rescaled metrics `k ω(·, J ·)`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §7.4
* [S. K. Donaldson, *Symplectic submanifolds and almost-complex geometry*][Donaldson1996]
* [D. Auroux, *A remark about Donaldson's construction of symplectic submanifolds*][Auroux2002],
  Lemma 1
-/

public section

open scoped Manifold ContDiff
open TauCeti Bundle

namespace SymplecticGeometry

namespace RescaledUnitaryCharts

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {ι : Type*} [Fintype ι]
  {P : M → Type*} [TopologicalSpace (TotalSpace Circle P)] [∀ x, TopologicalSpace (P x)]
  [FiberBundle Circle P] [∀ x, MulAction Circleᵐᵒᵖ (P x)] [PrincipalBundle Circle P]
  [ContMDiffFiberBundle ∞ Circle P I (𝓡 1)]
  {σ : SmoothTwoForm I M} {J : SmoothAlmostComplexStructure I M}
  {α : SmoothForm (I.prod (𝓡 1)) (ManifoldTotalSpace Circle P) ℝ 1} {k₀ : ℕ} {ρ₀ : ℝ}
  (D : RescaledUnitaryCharts P σ J α ι k₀ ρ₀)

/-- The **reading of a section** `s` of `PowerBundle P k` in the chart `D.chart k x` and the
frame `D.frame k x`: the complex function on `StdSpace ι` whose value at `z` is the coordinate
of `s ((D.chart k x).symm z)` in the frame `[D.frame k x _, 1]` of its fibre. -/
noncomputable def reading (k : ℕ) (x : M) (s : Π y, PowerBundle P k y) : StdSpace ι → ℂ :=
  fun z ↦ PowerModel.toComplex ((AssociatedBundle.mkLinearIsometryEquiv ℂ Circle
    (D.frame k x ((D.chart k x).symm z))).symm (s ((D.chart k x).symm z)))

theorem reading_def (k : ℕ) (x : M) (s : Π y, PowerBundle P k y) (z : StdSpace ι) :
    D.reading k x s z = PowerModel.toComplex ((AssociatedBundle.mkLinearIsometryEquiv ℂ Circle
      (D.frame k x ((D.chart k x).symm z))).symm (s ((D.chart k x).symm z))) :=
  (rfl)

/-- A section is recovered from its reading: at the point `(D.chart k x).symm z`, it is the
class of the frame and of the reading at `z`. -/
theorem apply_chart_symm_eq_mk (k : ℕ) (x : M) (s : Π y, PowerBundle P k y) (z : StdSpace ι) :
    s ((D.chart k x).symm z) = AssociatedBundle.mk Circle (D.frame k x ((D.chart k x).symm z))
      (PowerModel.toComplex.symm (D.reading k x s z)) := by
  rw [reading_def, LinearIsometryEquiv.symm_apply_apply,
    ← AssociatedBundle.mkLinearIsometryEquiv_apply (𝕜 := ℂ),
    LinearIsometryEquiv.apply_symm_apply]

@[simp]
theorem reading_add (k : ℕ) (x : M) (s t : Π y, PowerBundle P k y) :
    D.reading k x (s + t) = D.reading k x s + D.reading k x t := by
  ext z
  simp only [reading_def, Pi.add_apply, map_add]

@[simp]
theorem reading_smul (k : ℕ) (x : M) (c : ℂ) (s : Π y, PowerBundle P k y) :
    D.reading k x (c • s) = c • D.reading k x s := by
  ext z
  simp only [reading_def, Pi.smul_apply, map_smul]

@[simp]
theorem reading_zero (k : ℕ) (x : M) : D.reading k x (0 : Π y, PowerBundle P k y) = 0 := by
  simpa using D.reading_smul k x 0 0

@[simp]
theorem reading_neg (k : ℕ) (x : M) (s : Π y, PowerBundle P k y) :
    D.reading k x (-s) = -D.reading k x s := by
  ext z
  simp only [reading_def, Pi.neg_apply, map_neg]

@[simp]
theorem reading_sub (k : ℕ) (x : M) (s t : Π y, PowerBundle P k y) :
    D.reading k x (s - t) = D.reading k x s - D.reading k x t := by
  ext z
  simp only [reading_def, Pi.sub_apply, map_sub]

/-- The reading has the norm of the section: at `z`, it is `‖s ((D.chart k x).symm z)‖`. -/
@[simp]
theorem norm_reading (k : ℕ) (x : M) (s : Π y, PowerBundle P k y) (z : StdSpace ι) :
    ‖D.reading k x s z‖ = ‖s ((D.chart k x).symm z)‖ := by
  rw [reading_def, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map]

/-- The **`r`-jet norm at `x`** of a section `s` of `PowerBundle P k`: the jet norm
`SymplecticGeometry.jetNormAt ℝ r` at `0` of the reading of `s` in the chart and the frame
centred at `x`, that is, the sum over the orders `j ≤ r` of the norms of its `j`-th derivatives
at `0`. -/
noncomputable def jetNorm (k r : ℕ) (s : Π y, PowerBundle P k y) (x : M) : ℝ :=
  jetNormAt ℝ r (D.reading k x s) 0

theorem jetNorm_def (k r : ℕ) (s : Π y, PowerBundle P k y) (x : M) :
    D.jetNorm k r s x = jetNormAt ℝ r (D.reading k x s) 0 :=
  (rfl)

theorem jetNorm_nonneg (k r : ℕ) (s : Π y, PowerBundle P k y) (x : M) :
    0 ≤ D.jetNorm k r s x := by
  rw [jetNorm_def]
  exact jetNormAt_nonneg _ _ _

/-- The jet norm grows with the order. -/
theorem jetNorm_mono (k : ℕ) (s : Π y, PowerBundle P k y) (x : M) :
    Monotone fun r ↦ D.jetNorm k r s x := by
  simpa only [jetNorm_def] using jetNormAt_mono (D.reading k x s) 0

/-- The jet norm of order `0` is the norm of the section at the centre. -/
theorem jetNorm_zero {k : ℕ} (hk : k₀ ≤ k) (s : Π y, PowerBundle P k y) (x : M) :
    D.jetNorm k 0 s x = ‖s x‖ := by
  rw [jetNorm_def, jetNormAt_zero, norm_reading, D.chart_symm_zero hk x]

/-- The zero section has jet norm `0`. -/
@[simp]
theorem jetNorm_zero_fun (k r : ℕ) (x : M) :
    D.jetNorm k r (0 : Π y, PowerBundle P k y) x = 0 := by
  rw [jetNorm_def, reading_zero, jetNormAt_zero_fun]

@[simp]
theorem jetNorm_neg (k r : ℕ) (s : Π y, PowerBundle P k y) (x : M) :
    D.jetNorm k r (-s) x = D.jetNorm k r s x := by
  rw [jetNorm_def, jetNorm_def, reading_neg, jetNormAt_neg]

/-- The **triangle inequality for jet norms**, for sections whose readings are `C^r` at `0`. -/
theorem jetNorm_add_le {k r : ℕ} {s t : Π y, PowerBundle P k y} {x : M}
    (hs : ContDiffAt ℝ r (D.reading k x s) 0) (ht : ContDiffAt ℝ r (D.reading k x t) 0) :
    D.jetNorm k r (s + t) x ≤ D.jetNorm k r s x + D.jetNorm k r t x := by
  simpa only [jetNorm_def, reading_add] using jetNormAt_add_le hs ht

/-- The jet norm of a complex multiple of a section whose reading is `C^r` at `0`. -/
theorem jetNorm_smul {k r : ℕ} {s : Π y, PowerBundle P k y} {x : M}
    (hs : ContDiffAt ℝ r (D.reading k x s) 0) (c : ℂ) :
    D.jetNorm k r (c • s) x = ‖c‖ * D.jetNorm k r s x := by
  rw [jetNorm_def, jetNorm_def, reading_smul, jetNormAt_smul hs]

end RescaledUnitaryCharts

end SymplecticGeometry

end
