/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.Blowup.Chart
public import SymplecticGeometry.Geometry.Manifold.Complex.Hypersurface.LineBundle
public import TauCeti.Analysis.Normed.Module.Alternating.TopDegree
public import TauCeti.Geometry.Manifold.Projectivization.LineBundle

import SymplecticGeometry.Geometry.Manifold.Projectivization.TwistCore
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Canonical

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

For a holomorphic chart `φ` of `M` at `p₀` and the blowdown `π : Blowup c → M`, the file also
computes the pull-back by `π` of the coordinate form of `φ`. For a chart `e` of a manifold
modelled on `E` and a basis `b` of `E`, the coordinate form `dz₁ ∧ ⋯ ∧ dzₙ₊₁` of `e` at `x` is the
determinant form `b.continuousDet` pulled back by the differential of `e` at `x`; for the chart
`chartAt E x₀` this is Tau Ceti's `TauCeti.CanonicalBundle.coordForm`
(`TauCeti.CanonicalBundle.coordForm_eq_compContinuousLinearMap_mfderiv`).

It computes this in the chart `liftChart c φ` followed by `blowupModelChart i` of the blowup.
In that chart, `φ ∘ π` is the blowdown of the model read in the chart `i`,
`w ↦ (z i = w i, z j = w i * w j for j ≠ i)`, whose Jacobian determinant is `(w i) ^ n`
(`SymplecticGeometry.BlowupModel.det_fderiv_blowdown_blowupModelChart_symm`). So the pull-back
is `(w i) ^ n` times the coordinate form of the chart
(`SymplecticGeometry.Blowup.coordForm_blowdown`).
For `φ = c`, the lifted chart is `Blowup.lift c` over the source of `c`
(`SymplecticGeometry.Blowup.liftChart_self`), so the chart is `blowupModelChart i ∘ lift c`.

## Main definitions

* `SymplecticGeometry.Blowup.hypersurfaceData c`: the local equations of the exceptional divisor.
  Its cover, local equations and transition functions are given by `hypersurfaceData_U_none`,
  `hypersurfaceData_U_some`, `hypersurfaceData_f_none`, `hypersurfaceData_f_some` and the lemmas
  `hypersurfaceData_g_*`.

## Main results

* `SymplecticGeometry.Blowup.support_hypersurfaceData`: the common zero set of the local
  equations is the exceptional divisor `Blowup.exceptionalDivisor c`.
* `SymplecticGeometry.BlowupModel.hasFDerivAt_blowdown_blowupModelChart_symm`: the derivative of
  the blowdown of the model read in the chart `i`.
* `SymplecticGeometry.BlowupModel.det_fderiv_blowdown_blowupModelChart_symm`: its Jacobian
  determinant is `(w i) ^ n`.
* `SymplecticGeometry.Blowup.coordForm_blowdown`: the pull-back by the blowdown of the coordinate
  form of `φ` is `(w i) ^ n` times the coordinate form of the chart `i` of the blowup.

## References

* [P. Griffiths, J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978], Chapter 1,
  §4 (the exceptional divisor of the blowup of a point and its local equations).
* [C. Schnell, lecture notes on complex manifolds][Schnell2024], Lemma 23.5.
-/

public noncomputable section

open Function Module Set Projectivization
open scoped Manifold ContDiff LinearAlgebra.Projectivization

namespace SymplecticGeometry

variable {n : ℕ}

namespace BlowupModel

/-- The blowdown of the model read in the chart `i`, `w ↦ w i • update w i 1`, has at `w` the
derivative `v ↦ w i • update v i 0 + v i • update w i 1`. -/
theorem hasFDerivAt_blowdown_blowupModelChart_symm (i : Fin (n + 1)) (w : Fin (n + 1) → ℂ) :
    HasFDerivAt (fun w ↦ ((blowupModelChart i).symm w).blowdown)
      (w i • (ContinuousLinearMap.id ℂ (Fin (n + 1) → ℂ) -
          (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 1) ↦ ℂ) i).smulRight
            (Pi.single i 1)) +
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 1) ↦ ℂ) i).smulRight
          (update w i 1)) w := by
  set A := ContinuousLinearMap.id ℂ (Fin (n + 1) → ℂ) -
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 1) ↦ ℂ) i).smulRight (Pi.single i 1)
  have hA : (fun w : Fin (n + 1) → ℂ ↦ update w i 1) = fun w ↦ A w + Pi.single i 1 := by
    ext w j
    by_cases h : j = i
    · subst h; simp [A]
    · simp [A, h]
  have hg : HasFDerivAt (fun w : Fin (n + 1) → ℂ ↦ update w i 1) A w :=
    hA ▸ (A.hasFDerivAt).add_const _
  simp_rw [blowdown_blowupModelChart_symm_apply]
  exact (hasFDerivAt_apply i w).smul hg

/-- **The Jacobian of the blowdown in a chart.** In the chart `i` of the model, the blowdown is
`w ↦ (z i = w i, z j = w i * w j for j ≠ i)`, and its Jacobian determinant is `(w i) ^ n`. -/
theorem det_fderiv_blowdown_blowupModelChart_symm (i : Fin (n + 1)) (w : Fin (n + 1) → ℂ) :
    LinearMap.det (fderiv ℂ (fun w ↦ ((blowupModelChart i).symm w).blowdown) w :
      (Fin (n + 1) → ℂ) →ₗ[ℂ] Fin (n + 1) → ℂ) = w i ^ n := by
  rw [(hasFDerivAt_blowdown_blowupModelChart_symm i w).fderiv, ← LinearMap.det_toMatrix',
    Matrix.det_succ_row _ i, Finset.sum_eq_single i (fun j _ hj ↦ by
      simp [LinearMap.toMatrix'_apply, hj]) (by simp)]
  have : (LinearMap.toMatrix' (((w i • (ContinuousLinearMap.id ℂ (Fin (n + 1) → ℂ) -
          (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 1) ↦ ℂ) i).smulRight
            (Pi.single i 1)) +
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 1) ↦ ℂ) i).smulRight
          (update w i 1)) : (Fin (n + 1) → ℂ) →L[ℂ] _) : (Fin (n + 1) → ℂ) →ₗ[ℂ] _)).submatrix
        i.succAbove i.succAbove = w i • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    ext a b
    by_cases hab : a = b
    · subst hab; simp [LinearMap.toMatrix'_apply, Fin.succAbove_ne]
    · simp [LinearMap.toMatrix'_apply, Fin.succAbove_ne, hab]
  rw [this]
  simp [LinearMap.toMatrix'_apply]

end BlowupModel

namespace Blowup

open BlowupModel

section HypersurfaceData

open GluedAlong (inr)

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Fin (n + 1) → ℂ) M] {p₀ : M}
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
      exact twistTransition_ne_zero (-1) (mem_affineOpen_of_mem_divisorU c hj)
        (mem_affineOpen_of_mem_divisorU c hi)

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
@[simp]
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
@[simp]
theorem hypersurfaceData_f_some (i : Fin (n + 1)) (z : Blowup c) :
    (hypersurfaceData c).f (some i) z = (lift c z).blowdown i :=
  (rfl)

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
@[simp]
theorem hypersurfaceData_g_none_some (i : Fin (n + 1)) (z : Blowup c) :
    (hypersurfaceData c).g none (some i) z = ((lift c z).blowdown i)⁻¹ :=
  (rfl)

/-- The transition function from the chart `some i` to the chart `none` is the local equation
of `some i`. -/
@[simp]
theorem hypersurfaceData_g_some_none (i : Fin (n + 1)) (z : Blowup c) :
    (hypersurfaceData c).g (some i) none z = (lift c z).blowdown i :=
  (rfl)

/-- The transition function from the chart `some i` to the chart `some j` is the transition
function of `𝒪(-1)` from the chart `j` to the chart `i` at the line of the point of the model,
that is, the ratio `v i / v j` of its homogeneous coordinates
(`hypersurfaceData_g_some_some_eq`). -/
@[simp]
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

end HypersurfaceData

section CoordForm

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Fin (n + 1) → ℂ) M]
  [IsManifold 𝓘(ℂ, Fin (n + 1) → ℂ) ω M] {p₀ : M} (c φ : BlowupChart (n := n) M p₀)
  [hc : Fact (c.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin (n + 1) → ℂ) ω M)]
  [hφ : Fact (φ.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin (n + 1) → ℂ) ω M)]
  {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℂ (Fin (n + 1) → ℂ))

/-- **The coordinate form pulled back by the blowdown.** Let `φ` be a holomorphic chart of `M` at
the centre, and `χ` the chart `liftChart c φ` followed by `blowupModelChart i` of the blowup,
with coordinates `w`. At a point `z` of the source of `χ`, the coordinate form of `φ` at the
blowdown of `z`, pulled back by the differential of the blowdown, is `(w i) ^ n` times the
coordinate form of `χ` at `z`; here the coordinate form of a chart is the determinant form of
the basis `b` pulled back by its differential. -/
theorem coordForm_blowdown (i : Fin (n + 1)) {z : Blowup c}
    (hz : z ∈ ((liftChartPartialDiffeomorph c φ).toOpenPartialHomeomorph.trans
      (blowupModelChart i)).source) :
    (b.continuousDet.compContinuousLinearMap (mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ)
        𝓘(ℂ, Fin (n + 1) → ℂ) φ (blowdown c z))).compContinuousLinearMap
        (mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) (blowdown c) z) =
      (blowupModelChart i (liftChart c φ z) i) ^ n •
        b.continuousDet.compContinuousLinearMap
          (mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ)
            ((liftChartPartialDiffeomorph c φ).toOpenPartialHomeomorph.trans
              (blowupModelChart i)) z) := by
  have hs : (liftChartPartialDiffeomorph c φ).toOpenPartialHomeomorph.source =
      blowdown c ⁻¹' φ.source :=
    liftChartPartialDiffeomorph_source c φ
  set χ := (liftChartPartialDiffeomorph c φ).toOpenPartialHomeomorph.trans (blowupModelChart i)
  have hχ : χ ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin (n + 1) → ℂ) ω (Blowup c) :=
    liftChart_mem_maximalAtlas c φ i
  have hzχ := hz
  simp only [χ, OpenPartialHomeomorph.trans_source, hs,
    PartialDiffeomorph.toFun'_toOpenPartialHomeomorph, coe_liftChartPartialDiffeomorph,
    Set.mem_inter_iff, Set.mem_preimage] at hzχ
  -- Near `z`, `φ ∘ blowdown c` is the blowdown of the model read in the chart `χ`.
  have heq : (fun z' ↦ φ (blowdown c z')) =ᶠ[nhds z]
      (fun w ↦ ((blowupModelChart i).symm w).blowdown) ∘ χ := by
    filter_upwards [χ.open_source.mem_nhds hz] with z' hz'
    simp only [χ, OpenPartialHomeomorph.trans_source, hs,
      PartialDiffeomorph.toFun'_toOpenPartialHomeomorph, coe_liftChartPartialDiffeomorph,
      Set.mem_inter_iff, Set.mem_preimage] at hz'
    simp only [comp_apply, χ, OpenPartialHomeomorph.coe_trans,
      PartialDiffeomorph.toFun'_toOpenPartialHomeomorph, coe_liftChartPartialDiffeomorph]
    rw [(blowupModelChart i).left_inv hz'.2, blowdown_liftChart c φ hz'.1]
  have hφd : MDifferentiableAt 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) φ (blowdown c z) :=
    (contMDiffAt_of_mem_maximalAtlas hφ.out hzχ.1).mdifferentiableAt (by simp)
  have hbd : MDifferentiableAt 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) (blowdown c) z :=
    ((contMDiff_blowdown c) z).mdifferentiableAt (by simp)
  have hχd : MDifferentiableAt 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) χ z :=
    (contMDiffAt_of_mem_maximalAtlas hχ hz).mdifferentiableAt (by simp)
  have hχz : χ z = blowupModelChart i (liftChart c φ z) := by
    simp only [χ, OpenPartialHomeomorph.coe_trans, comp_apply,
      PartialDiffeomorph.toFun'_toOpenPartialHomeomorph, coe_liftChartPartialDiffeomorph]
  rw [b.continuousDet_compContinuousLinearMap_mfderiv_comp hφd hbd hχd
    (hasFDerivAt_blowdown_blowupModelChart_symm i (χ z)).differentiableAt heq,
    det_fderiv_blowdown_blowupModelChart_symm, hχz]

end CoordForm

end Blowup

end SymplecticGeometry

end
