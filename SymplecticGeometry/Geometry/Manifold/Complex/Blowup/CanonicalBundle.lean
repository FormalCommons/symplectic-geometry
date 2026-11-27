/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.Blowup.Basic
public import SymplecticGeometry.Geometry.Manifold.Complex.Hypersurface.LineBundle
public import TauCeti.Geometry.Manifold.Projectivization.LineBundle

/-!
# The canonical bundle of the blowup

Let `M` be a complex manifold modelled on `E = ℂⁿ⁺¹` and `c` a chart of its holomorphic atlas at
`p₀` with `c p₀ = 0`. This file gives local equations of the exceptional divisor of
`SymplecticGeometry.Blowup c`, as data `SymplecticGeometry.HypersurfaceData` indexed by
`Option (Fin (n + 1))`:

* the index `none` is the complement of the divisor, `Blowup.offDivisorOpens c`, with local
  equation `1`;
* the index `some i` is the domain of the chart `blowupModelChart i ∘ Blowup.lift c`, inside the
  image of the model, with local equation the coordinate `w i` of that chart, which is the
  coordinate `i` of the point of `E` under the point of the model.

The transition functions are `w i` from `some i` to `none` and its inverse from `none` to
`some i`. From `some i` to `some j` the transition is the ratio `v i / v j` of homogeneous
coordinates `v` of the line of the point of the model; off the divisor it is the ratio
`z i / z j` of the coordinates of the point `z` of `E` below. It is Tau Ceti's
`Projectivization.twistTransition (-1) j i`, the transition function of the tautological
bundle `𝒪(-1)`.

## Main definitions

* `SymplecticGeometry.Blowup.hypersurfaceData c`: the local equations of the exceptional divisor.
  Its cover, local equations and transition functions are given by `hypersurfaceData_U_none`,
  `hypersurfaceData_U_some`, `hypersurfaceData_f_none`, `hypersurfaceData_f_some` and the lemmas
  `hypersurfaceData_g_*`.

## Main results

* `SymplecticGeometry.Blowup.support_hypersurfaceData`: the common zero set of the local
  equations is the exceptional divisor `Blowup.exceptionalDivisor c`.

## References

* [P. Griffiths, J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978], Chapter 1,
  §4 (the exceptional divisor of the blowup of a point and its local equations).
-/

public noncomputable section

open Set Projectivization
open scoped Manifold ContDiff LinearAlgebra.Projectivization

namespace SymplecticGeometry

namespace Blowup

open BlowupModel

open GluedAlong (inr)

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Fin (n + 1) → ℂ) M] {p₀ : M}
  (c : BlowupChart (n := n) M p₀)

/-! ### The cover, the local equations and the transition functions -/

/-- The open sets of the cover: the complement of the divisor, and the domains of the charts
`blowupModelChart i ∘ lift c` in the image of the model. -/
private def divisorU : Option (Fin (n + 1)) → Set (Blowup c)
  | none => offDivisorOpens c
  | some i => range (inr (gluingHomeomorph c)) ∩ lift c ⁻¹' (blowupModelChart i).source

/-- The local equations: `1` off the divisor, and the coordinate `i` of the point of `E` below in
the chart `i`. -/
private def divisorF : Option (Fin (n + 1)) → Blowup c → ℂ
  | none => fun _ ↦ 1
  | some i => fun z ↦ (lift c z).blowdown i

/-- The transition functions of the local equations. -/
private def divisorG : Option (Fin (n + 1)) → Option (Fin (n + 1)) → Blowup c → ℂ
  | none, none => fun _ ↦ 1
  | none, some i => fun z ↦ ((lift c z).blowdown i)⁻¹
  | some i, none => fun z ↦ (lift c z).blowdown i
  | some i, some j => fun z ↦ twistTransition (-1) j i (lift c z).pr

open scoped Classical in
/-- The preferred chart at a point: `none` off the divisor, and a chart of the line on it. -/
private def divisorIndexAt (z : Blowup c) : Option (Fin (n + 1)) :=
  if z ∈ exceptionalDivisor c then some (exists_mem_affineOpen (lift c z).pr).choose else none

private theorem divisorF_some_apply (i : Fin (n + 1)) (z : Blowup c) :
    divisorF c (some i) z = (lift c z).blowdown i :=
  (rfl)

/-- In the chart `i`, a point is on the divisor exactly when its local equation vanishes. -/
private theorem divisorF_some_eq_zero_iff {i : Fin (n + 1)} {z : Blowup c}
    (hz : z ∈ divisorU c (some i)) :
    divisorF c (some i) z = 0 ↔ z ∈ exceptionalDivisor c := by
  obtain ⟨⟨y, rfl⟩, hy⟩ := hz
  rw [mem_preimage, lift_inr] at hy
  rw [divisorF_some_apply, lift_inr, blowdown_apply_eq_zero_iff i hy,
    inr_mem_exceptionalDivisor_iff]

private theorem divisorF_some_ne_zero {i : Fin (n + 1)} {z : Blowup c}
    (hi : z ∈ divisorU c (some i)) (h : z ∈ divisorU c none) : divisorF c (some i) z ≠ 0 :=
  fun h0 ↦ (mem_offDivisorOpens c).1 h ((divisorF_some_eq_zero_iff c hi).1 h0)

private theorem mem_affineOpen_of_mem_divisorU {i : Fin (n + 1)} {z : Blowup c}
    (hz : z ∈ divisorU c (some i)) : (lift c z).pr ∈ affineOpen i := by
  simpa using hz.2

/-- The local equations of the charts `i` and `j` differ by the ratio of the homogeneous
coordinates `i` and `j` of the line. -/
private theorem divisorF_some_eq_mul {i j : Fin (n + 1)} {z : Blowup c}
    (hj : z ∈ divisorU c (some j)) :
    divisorF c (some i) z = twistTransition (-1) j i (lift c z).pr * divisorF c (some j) z :=
  (twistTransition_neg_one_mul i (mem_affineOpen_of_mem_divisorU c hj)
    (lift c z).blowdown_mem_submodule).symm


private theorem mem_divisorU_divisorIndexAt (z : Blowup c) :
    z ∈ divisorU c (divisorIndexAt c z) := by
  by_cases hz : z ∈ exceptionalDivisor c
  · simp only [divisorIndexAt, hz, ite_true]
    have hr : z ∈ range (inr (gluingHomeomorph c)) := by
      rw [range_inr]
      exact Or.inl hz
    refine ⟨hr, ?_⟩
    rw [mem_preimage, blowupModelChart_source, mem_preimage]
    exact (exists_mem_affineOpen (lift c z).pr).choose_spec
  · simp only [divisorIndexAt, hz, ite_false]
    exact (mem_offDivisorOpens c).2 hz


private theorem divisorF_eq_divisorG_mul {i j : Option (Fin (n + 1))} {z : Blowup c}
    (hi : z ∈ divisorU c i) (hj : z ∈ divisorU c j) :
    divisorF c i z = divisorG c i j z * divisorF c j z := by
  cases i with
  | none =>
    cases j with
    | none => simp [divisorF, divisorG]
    | some j =>
      exact (inv_mul_cancel₀ (divisorF_some_ne_zero c hj hi)).symm
  | some i =>
    cases j with
    | none => simp [divisorF, divisorG]
    | some j => exact divisorF_some_eq_mul c hj

private theorem divisorG_ne_zero {i j : Option (Fin (n + 1))} {z : Blowup c}
    (hi : z ∈ divisorU c i) (hj : z ∈ divisorU c j) : divisorG c i j z ≠ 0 := by
  cases i with
  | none =>
    cases j with
    | none => exact one_ne_zero
    | some j => exact inv_ne_zero (divisorF_some_ne_zero c hj hi)
  | some i =>
    cases j with
    | none => exact divisorF_some_ne_zero c hi hj
    | some j =>
      have hi' := (mem_affineOpen_iff i _).1 (mem_affineOpen_of_mem_divisorU c hi)
      have hj' := (mem_affineOpen_iff j _).1 (mem_affineOpen_of_mem_divisorU c hj)
      simp only [divisorG, twistTransition_def, zpow_neg, zpow_one]
      exact inv_ne_zero (div_ne_zero hj' hi')

private theorem divisorG_mul_divisorG {i j k : Option (Fin (n + 1))} {z : Blowup c}
    (hi : z ∈ divisorU c i) (hj : z ∈ divisorU c j) (hk : z ∈ divisorU c k) :
    divisorG c i j z * divisorG c j k z = divisorG c i k z := by
  by_cases h0 : z ∈ divisorU c none
  · -- Off the divisor every local equation is nonzero, and the transition functions are their
    -- ratios.
    have hne {a : Option (Fin (n + 1))} (ha : z ∈ divisorU c a) : divisorF c a z ≠ 0 := by
      cases a with
      | none => exact one_ne_zero
      | some a => exact divisorF_some_ne_zero c ha h0
    have hdiv {a b : Option (Fin (n + 1))} (ha : z ∈ divisorU c a) (hb : z ∈ divisorU c b) :
        divisorG c a b z = divisorF c a z / divisorF c b z :=
      eq_div_of_mul_eq (hne hb) (divisorF_eq_divisorG_mul c ha hb).symm
    rw [hdiv hi hj, hdiv hj hk, hdiv hi hk, div_mul_div_cancel₀ (hne hj)]
  · -- On the divisor all three charts are charts of the model.
    cases i with
    | none => exact absurd hi h0
    | some i =>
      cases j with
      | none => exact absurd hj h0
      | some j =>
        cases k with
        | none => exact absurd hk h0
        | some k =>
          exact twistTransition_mul_twistTransition (-1) k i
            (mem_affineOpen_of_mem_divisorU c hj)

variable [IsManifold 𝓘(ℂ, Fin (n + 1) → ℂ) ω M]
  [Fact (c.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin (n + 1) → ℂ) ω M)]

private theorem isOpen_divisorU (i : Option (Fin (n + 1))) : IsOpen (divisorU c i) := by
  cases i with
  | none => exact (offDivisorOpens c).isOpen
  | some i =>
    exact (contMDiffOn_lift c).continuousOn.isOpen_inter_preimage
      (GluedAlong.isOpen_range_inr _) (blowupModelChart i).open_source

private theorem contMDiffOn_divisorF_some (i : Fin (n + 1)) :
    ContMDiffOn 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ) ω (divisorF c (some i))
      (range (inr (gluingHomeomorph c))) :=
  ((contDiff_apply ℂ (fun _ ↦ ℂ) i).contMDiff.comp
    (BlowupModel.contMDiff_blowdown ω)).comp_contMDiffOn (contMDiffOn_lift c)

private theorem contMDiffOn_divisorF (i : Option (Fin (n + 1))) :
    ContMDiffOn 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ) ω (divisorF c i) (divisorU c i) := by
  cases i with
  | none => exact contMDiffOn_const
  | some i => exact (contMDiffOn_divisorF_some c i).mono fun _ hz ↦ hz.1

private theorem contMDiffOn_divisorG (i j : Option (Fin (n + 1))) :
    ContMDiffOn 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ) ω (divisorG c i j) (divisorU c i ∩ divisorU c j) := by
  cases i with
  | none =>
    cases j with
    | none => exact contMDiffOn_const
    | some j =>
      exact ContMDiffOn.inv₀ ((contMDiffOn_divisorF_some c j).mono
        (inter_subset_right.trans inter_subset_left))
        fun _ hz ↦ divisorF_some_ne_zero c hz.2 hz.1
  | some i =>
    cases j with
    | none => exact (contMDiffOn_divisorF_some c i).mono fun _ hz ↦ hz.1.1
    | some j =>
      refine (contMDiffOn_twistTransition (-1) j i ω).comp
        (((BlowupModel.contMDiff_pr ω).comp_contMDiffOn (contMDiffOn_lift c)).mono
          fun _ hz ↦ hz.1.1) fun _ hz ↦ ?_
      exact ⟨mem_affineOpen_of_mem_divisorU c hz.2, mem_affineOpen_of_mem_divisorU c hz.1⟩

/-! ### The local equations of the exceptional divisor -/

/-- **The local equations of the exceptional divisor.** The cover of the blowup by the
complement `offDivisorOpens c` of the exceptional divisor (the index `none`), with local
equation `1`, and by the domains of the charts `blowupModelChart i ∘ lift c` in the image of the
model (the index `some i`), with local equation the coordinate `w i` of the chart. The transition
functions are `w i` from `some i` to `none`, its inverse from `none` to `some i`, and, from
`some i` to `some j`, the ratio `v i / v j` of homogeneous coordinates of the line of the point
of the model (Tau Ceti's `Projectivization.twistTransition (-1) j i`). -/
def hypersurfaceData :
    HypersurfaceData 𝓘(ℂ, Fin (n + 1) → ℂ) (Blowup c) (Option (Fin (n + 1))) where
  U := divisorU c
  isOpen_U := isOpen_divisorU c
  indexAt := divisorIndexAt c
  mem_U_indexAt := mem_divisorU_divisorIndexAt c
  g := divisorG c
  g_ne_zero := divisorG_ne_zero c
  g_mul_g := divisorG_mul_divisorG c
  f := divisorF c
  contMDiffOn_f := contMDiffOn_divisorF c
  contMDiffOn_g := contMDiffOn_divisorG c
  f_eq_g_mul := divisorF_eq_divisorG_mul c

/-- The chart `none` is the complement of the exceptional divisor. -/
theorem hypersurfaceData_U_none :
    (hypersurfaceData c).U none = offDivisorOpens c :=
  (rfl)

/-- The chart `some i` is the domain of the chart `blowupModelChart i ∘ lift c` in the image of
the model. -/
theorem hypersurfaceData_U_some (i : Fin (n + 1)) :
    (hypersurfaceData c).U (some i) =
      range (inr (gluingHomeomorph c)) ∩ lift c ⁻¹' (blowupModelChart i).source :=
  (rfl)

/-- A point of the model lies in the chart `some i` exactly when its line lies in the affine
open `affineOpen i`. -/
@[simp]
theorem inr_mem_hypersurfaceData_U_some_iff (i : Fin (n + 1)) {y : modelOpens c} :
    inr (gluingHomeomorph c) y ∈ (hypersurfaceData c).U (some i) ↔
      (y : BlowupModel n).pr ∈ affineOpen i := by
  simp [hypersurfaceData_U_some]

/-- The preferred chart of a point off the divisor is `none`. -/
theorem hypersurfaceData_indexAt_of_notMem {z : Blowup c} (hz : z ∉ exceptionalDivisor c) :
    (hypersurfaceData c).indexAt z = none := by
  simp [hypersurfaceData, divisorIndexAt, hz]

/-- The preferred chart of a point of the divisor is a chart `some i`. -/
theorem exists_hypersurfaceData_indexAt_eq_some {z : Blowup c} (hz : z ∈ exceptionalDivisor c) :
    ∃ i, (hypersurfaceData c).indexAt z = some i :=
  ⟨(exists_mem_affineOpen (lift c z).pr).choose, by simp [hypersurfaceData, divisorIndexAt, hz]⟩

/-- The local equation off the divisor is `1`. -/
@[simp]
theorem hypersurfaceData_f_none (z : Blowup c) : (hypersurfaceData c).f none z = 1 :=
  (rfl)

/-- The local equation of the chart `some i` is the coordinate `i` of the point of `E` under
the point of the model, which is the coordinate `w i` of the chart `blowupModelChart i`. -/
theorem hypersurfaceData_f_some (i : Fin (n + 1)) (z : Blowup c) :
    (hypersurfaceData c).f (some i) z = (lift c z).blowdown i :=
  (rfl)

@[simp]
theorem hypersurfaceData_f_some_inr (i : Fin (n + 1)) (y : modelOpens c) :
    (hypersurfaceData c).f (some i) (inr (gluingHomeomorph c) y) =
      (y : BlowupModel n).blowdown i := by
  rw [hypersurfaceData_f_some, lift_inr]

/-- The local equation of the chart `some i` is the coordinate `w i` of the chart
`blowupModelChart i ∘ lift c`. -/
theorem hypersurfaceData_f_some_eq_blowupModelChart (i : Fin (n + 1)) (z : Blowup c) :
    (hypersurfaceData c).f (some i) z = blowupModelChart i (lift c z) i := by
  rw [hypersurfaceData_f_some, blowupModelChart_apply_self]

@[simp]
theorem hypersurfaceData_g_none_none (z : Blowup c) : (hypersurfaceData c).g none none z = 1 :=
  (rfl)

/-- The transition function from the chart `none` to the chart `some i` is the inverse of the
local equation of `some i`. -/
theorem hypersurfaceData_g_none_some (i : Fin (n + 1)) (z : Blowup c) :
    (hypersurfaceData c).g none (some i) z = ((lift c z).blowdown i)⁻¹ :=
  (rfl)

/-- The transition function from the chart `some i` to the chart `none` is the local equation
of `some i`. -/
theorem hypersurfaceData_g_some_none (i : Fin (n + 1)) (z : Blowup c) :
    (hypersurfaceData c).g (some i) none z = (lift c z).blowdown i :=
  (rfl)

/-- The transition function from the chart `some i` to the chart `some j` is the transition
function of `𝒪(-1)` from the chart `j` to the chart `i` at the line of the point of the model,
that is, the ratio `v i / v j` of its homogeneous coordinates
(`hypersurfaceData_g_some_some_eq`). -/
theorem hypersurfaceData_g_some_some (i j : Fin (n + 1)) (z : Blowup c) :
    (hypersurfaceData c).g (some i) (some j) z = twistTransition (-1) j i (lift c z).pr :=
  (rfl)

/-- The transition function from the chart `some i` to the chart `some j` is the ratio
`v i / v j` of the coordinates of any `v` spanning the line of the point of the model. -/
theorem hypersurfaceData_g_some_some_eq (i j : Fin (n + 1)) {z : Blowup c} {v : Fin (n + 1) → ℂ}
    (hv : v ≠ 0) (hz : (lift c z).pr = mk ℂ v hv) :
    (hypersurfaceData c).g (some i) (some j) z = v i / v j := by
  rw [hypersurfaceData_g_some_some, hz, twistTransition_mk, zpow_neg, zpow_one, inv_div]

/-! ### The support -/

/-- **The support of the local equations is the exceptional divisor.** -/
theorem support_hypersurfaceData : (hypersurfaceData c).support = exceptionalDivisor c := by
  ext z
  rw [HypersurfaceData.mem_support_iff]
  refine ⟨fun ⟨i, hi, h0⟩ ↦ ?_, fun hz ↦ ?_⟩
  · cases i with
    | none => exact absurd h0 one_ne_zero
    | some i => exact (divisorF_some_eq_zero_iff c hi).1 h0
  · have hi := (hypersurfaceData c).mem_U_indexAt z
    obtain ⟨i, hi'⟩ := exists_hypersurfaceData_indexAt_eq_some c hz
    rw [hi'] at hi
    exact ⟨some i, hi, (divisorF_some_eq_zero_iff c hi).2 hz⟩

end Blowup

end SymplecticGeometry

end
