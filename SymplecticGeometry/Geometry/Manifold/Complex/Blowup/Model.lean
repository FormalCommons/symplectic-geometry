/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.OpenPartialHomeomorph.Composition
public import SymplecticGeometry.Algebra.Notation.Pi.Basic
public import SymplecticGeometry.LinearAlgebra.Projectivization.Basic
public import TauCeti.Topology.Algebra.Projectivization

/-!
# The model blowup of `ℂⁿ⁺¹` at the origin

For `n : ℕ` and `E := Fin (n + 1) → ℂ`, the blowup of `E` at `0` is the incidence set of the pairs
`(ℓ, z) ∈ ℙ ℂ E × E` with `z` on the line `ℓ`, as in McDuff–Salamon (7.1.1). It comes with the
projection `pr` to `ℙ ℂ E` and the blowdown map to `E`; the blowdown is a bijection off the
exceptional divisor, the fibre `ℙ ℂ E × {0}` over the origin.

This file sets up the incidence set with its subspace topology, the two projections, the
exceptional divisor, and the `n + 1` charts of McDuff–Salamon, Exercise 7.1.2 (i), with the
transitions between them. The complex manifold structure comes later.

## Main definitions and results

* `SymplecticGeometry.blowupModel n`: the incidence set in `ℙ ℂ E × E`, and
  `SymplecticGeometry.isClosed_blowupModel`: it is closed (Tau Ceti's
  `Projectivization.isClosed_setOfPred_mem_submodule`).
* `SymplecticGeometry.BlowupModel n`: the incidence set as a type, with the subspace topology.
* `SymplecticGeometry.BlowupModel.pr` and `SymplecticGeometry.BlowupModel.blowdown`: the
  continuous projections to `ℙ ℂ E` and to `E`.
* `SymplecticGeometry.BlowupModel.exceptionalDivisor n`: the fibre of the blowdown over `0`,
  which is the range of the zero section `SymplecticGeometry.BlowupModel.zeroSection`
  (`SymplecticGeometry.BlowupModel.exceptionalDivisor_eq_range`).
* `SymplecticGeometry.BlowupModel.dense_exceptionalDivisor_compl`: the complement of the
  exceptional divisor is dense, since `(ℓ, t • v)` tends to `(ℓ, 0)` as `t → 0`.
* `SymplecticGeometry.BlowupModel.blowupModelChart i`, for `i : Fin (n + 1)`: the chart of the
  blowup over Tau Ceti's affine open `Projectivization.affineOpen i`, onto all of `E`. At the place
  `i` it records `z i`, and at the others the affine coordinates `Projectivization.affineChart i ℓ`
  of the line; its inverse is `w ↦ ([update w i 1], w i • update w i 1)`. In this chart the
  blowdown is `z i = w i`, `z j = w i * w j` (`blowdown_blowupModelChart_symm_apply`).
* `SymplecticGeometry.BlowupModel.blowupModelChart_symm_trans_source` and
  `SymplecticGeometry.BlowupModel.blowupModelChart_symm_trans_apply`: the transition from the
  chart `i` to the chart `k`. For `k ≠ i` it is defined where `w k ≠ 0`, and sends `w` to `w'`
  with `w' k = w i * w k` and `w' j = v j / w k` for `j ≠ k`, where `v = update w i 1`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §7.1.
* [P. Griffiths, J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978],
  Chapter 1, §4.
-/

public section

open Projectivization Filter Topology
open scoped LinearAlgebra.Projectivization

namespace SymplecticGeometry

variable (n : ℕ)

/-- The incidence set of the blowup of `ℂⁿ⁺¹` at the origin: the pairs `(ℓ, z)` of a complex line
`ℓ` through the origin and a vector `z` on it. -/
def blowupModel : Set (ℙ ℂ (Fin (n + 1) → ℂ) × (Fin (n + 1) → ℂ)) :=
  {p | p.2 ∈ p.1.submodule}

variable {n} in
@[simp]
theorem mem_blowupModel_iff {p : ℙ ℂ (Fin (n + 1) → ℂ) × (Fin (n + 1) → ℂ)} :
    p ∈ blowupModel n ↔ p.2 ∈ p.1.submodule :=
  Iff.rfl

/-- The incidence set of the blowup is closed in `ℙ ℂ E × E`. -/
theorem isClosed_blowupModel : IsClosed (blowupModel n) :=
  isClosed_setOfPred_mem_submodule

/-- The blowup of `ℂⁿ⁺¹` at the origin, as the incidence set `blowupModel n` with the subspace
topology. -/
abbrev BlowupModel : Type := blowupModel n

namespace BlowupModel

variable {n}

/-- The projection of the blowup to the projective space: `(ℓ, z) ↦ ℓ`. -/
def pr (p : BlowupModel n) : ℙ ℂ (Fin (n + 1) → ℂ) :=
  p.val.fst

/-- The blowdown map of the blowup to `ℂⁿ⁺¹`: `(ℓ, z) ↦ z`. -/
def blowdown (p : BlowupModel n) : Fin (n + 1) → ℂ :=
  p.val.snd

theorem pr_def (p : BlowupModel n) : p.pr = p.val.1 :=
  (rfl)

theorem blowdown_def (p : BlowupModel n) : p.blowdown = p.val.2 :=
  (rfl)

@[simp]
theorem pr_mk (ℓ : ℙ ℂ (Fin (n + 1) → ℂ)) (z : Fin (n + 1) → ℂ) (h : (ℓ, z) ∈ blowupModel n) :
    pr ⟨(ℓ, z), h⟩ = ℓ :=
  (rfl)

@[simp]
theorem blowdown_mk (ℓ : ℙ ℂ (Fin (n + 1) → ℂ)) (z : Fin (n + 1) → ℂ)
    (h : (ℓ, z) ∈ blowupModel n) : blowdown ⟨(ℓ, z), h⟩ = z :=
  (rfl)

theorem blowdown_mem_submodule (p : BlowupModel n) : p.blowdown ∈ p.pr.submodule :=
  p.property

/-- A point of the blowup is determined by its projection and its blowdown. -/
theorem ext {p q : BlowupModel n} (h₁ : p.pr = q.pr) (h₂ : p.blowdown = q.blowdown) : p = q :=
  Subtype.ext (Prod.ext h₁ h₂)

@[fun_prop, continuity]
theorem continuous_pr : Continuous (pr : BlowupModel n → ℙ ℂ (Fin (n + 1) → ℂ)) :=
  continuous_fst.comp continuous_subtypeVal

@[fun_prop, continuity]
theorem continuous_blowdown : Continuous (blowdown : BlowupModel n → Fin (n + 1) → ℂ) :=
  continuous_snd.comp continuous_subtypeVal

variable (n) in
/-- The exceptional divisor of the blowup: the fibre `{(ℓ, 0)}` of the blowdown over the
origin. -/
def exceptionalDivisor : Set (BlowupModel n) :=
  {p | p.blowdown = 0}

@[simp]
theorem mem_exceptionalDivisor_iff {p : BlowupModel n} :
    p ∈ exceptionalDivisor n ↔ p.blowdown = 0 :=
  Iff.rfl

theorem isClosed_exceptionalDivisor : IsClosed (exceptionalDivisor n) :=
  isClosed_eq continuous_blowdown continuous_const

/-- The zero section of the blowup over the projective space: `ℓ ↦ (ℓ, 0)`. -/
def zeroSection (ℓ : ℙ ℂ (Fin (n + 1) → ℂ)) : BlowupModel n :=
  ⟨(ℓ, 0), ℓ.submodule.zero_mem⟩

@[simp]
theorem coe_zeroSection (ℓ : ℙ ℂ (Fin (n + 1) → ℂ)) :
    (zeroSection ℓ : ℙ ℂ (Fin (n + 1) → ℂ) × (Fin (n + 1) → ℂ)) = (ℓ, 0) :=
  (rfl)

@[simp]
theorem pr_zeroSection (ℓ : ℙ ℂ (Fin (n + 1) → ℂ)) : (zeroSection ℓ).pr = ℓ :=
  (rfl)

@[simp]
theorem blowdown_zeroSection (ℓ : ℙ ℂ (Fin (n + 1) → ℂ)) : (zeroSection ℓ).blowdown = 0 :=
  (rfl)

theorem zeroSection_injective :
    Function.Injective (zeroSection : ℙ ℂ (Fin (n + 1) → ℂ) → BlowupModel n) :=
  fun ℓ ℓ' h => by simpa using congrArg pr h

@[fun_prop, continuity]
theorem continuous_zeroSection :
    Continuous (zeroSection : ℙ ℂ (Fin (n + 1) → ℂ) → BlowupModel n) :=
  (continuous_id.prodMk continuous_const).subtype_mk _

/-- The exceptional divisor is the image of the zero section. -/
theorem exceptionalDivisor_eq_range : exceptionalDivisor n = Set.range zeroSection := by
  ext p
  refine ⟨fun hp => ⟨p.pr, ?_⟩, ?_⟩
  · exact ext rfl (mem_exceptionalDivisor_iff.1 hp).symm
  · rintro ⟨ℓ, rfl⟩
    exact blowdown_zeroSection ℓ

/-- The complement of the exceptional divisor is dense in the blowup: a point `(ℓ, 0)` is the
limit of `(ℓ, t • v)` as `t → 0`, for `v` spanning `ℓ`. -/
theorem dense_exceptionalDivisor_compl : Dense (exceptionalDivisor n)ᶜ := by
  intro p
  by_cases hp : p.blowdown = 0
  · have hrep : p.pr.rep ∈ p.pr.submodule := mem_submodule_iff.2 fun _ => mk_rep _
    let γ : ℂ → BlowupModel n := fun t => ⟨(p.pr, t • p.pr.rep), p.pr.submodule.smul_mem t hrep⟩
    have hγ : Continuous γ :=
      (continuous_const.prodMk (continuous_id.smul continuous_const)).subtype_mk _
    have h0 : γ 0 = p := ext rfl (by simp [γ, hp])
    rw [← h0]
    refine mem_closure_of_tendsto (hγ.continuousAt.mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))) ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : t ≠ 0)
    exact fun h => smul_ne_zero ht p.pr.rep_ne_zero
      ((blowdown_mk _ _ _).symm.trans (mem_exceptionalDivisor_iff.1 h))
  · exact subset_closure hp

/-! ### The charts -/

section Chart

open Function

/-- The line through `update w i 1` contains `w i • update w i 1`. -/
theorem mk_update_one_smul_mem_blowupModel (w : Fin (n + 1) → ℂ) (i : Fin (n + 1)) :
    (mk ℂ (update w i 1) (update_ne_zero w i one_ne_zero), w i • update w i 1) ∈ blowupModel n := by
  rw [mem_blowupModel_iff, submodule_mk]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

/-- The chart `i` of the blowup `BlowupModel n`, defined on the pairs `(ℓ, z)` whose line `ℓ`
lies in the affine open `affineOpen i` of `ℙ ℂ E`. Its value `w` has `w i = z i`, and for
`j ≠ i` its coordinate `w j` is the ratio `v j / v i` for any `v` spanning `ℓ`, so that the
coordinates other than `i` are the affine coordinates `affineChart i ℓ` of the line. Its inverse
sends `w` to the pair `(ℓ, z)` with `ℓ` spanned by `update w i 1` and `z = w i • update w i 1`. -/
noncomputable def blowupModelChart (i : Fin (n + 1)) :
    OpenPartialHomeomorph (BlowupModel n) (Fin (n + 1) → ℂ) where
  toFun p := Fin.insertNth i (p.blowdown i) (affineChart i p.pr)
  invFun w := ⟨_, mk_update_one_smul_mem_blowupModel w i⟩
  source := pr ⁻¹' affineOpen i
  target := Set.univ
  map_source' _ _ := Set.mem_univ _
  map_target' w _ := (mk_mem_affineOpen_iff i _ (update_ne_zero w i one_ne_zero)).2 (by simp)
  left_inv' p hp := by
    have hv (x : ℂ) : update (Fin.insertNth i x (affineChart i p.pr)) i 1 =
        normalizedRep (LinearMap.proj i) p.pr := by
      rw [Fin.update_insertNth, insertNth_one_affineChart_eq_normalizedRep i hp]
    refine ext ?_ ?_
    · simp only [pr_mk, Fin.insertNth_apply_same, hv]
      conv_rhs => rw [← mk_rep p.pr]
      exact (mk_eq_mk_iff' ℂ _ _ _ _).2 ⟨_, (normalizedRep_def _ _).symm⟩
    · simp only [blowdown_mk, Fin.insertNth_apply_same, hv]
      rw [affineOpen_eq_linearProjectionDomain] at hp
      simpa using apply_smul_normalizedRep hp p.blowdown_mem_submodule
  right_inv' w _ := by
    ext j
    refine Fin.succAboveCases i ?_ (fun j => ?_) j <;>
      simp [Fin.succAbove_ne]
  open_source := (isOpen_affineOpen i).preimage continuous_pr
  open_target := isOpen_univ
  continuousOn_toFun :=
    ((continuous_apply i).comp continuous_blowdown).continuousOn.finInsertNth i
      ((continuousOn_affineChart i).comp continuous_pr.continuousOn fun _ hp => hp)
  continuousOn_invFun := by
    refine (Continuous.subtype_mk ?_ _).continuousOn
    have hv : Continuous fun w : Fin (n + 1) → ℂ => update w i 1 :=
      continuous_id.update i continuous_const
    refine Continuous.prodMk ?_ ((continuous_apply i).smul hv)
    simp_rw [← affineChart_symm_removeNth]
    exact (continuous_affineChart_symm i).comp (continuous_pi fun _ => continuous_apply _)

variable (i : Fin (n + 1))

/-- The chart `i` reads off `z i` at the place `i` and the affine coordinates of the line at the
other places. -/
theorem blowupModelChart_apply (p : BlowupModel n) :
    blowupModelChart i p = Fin.insertNth i (p.blowdown i) (affineChart i p.pr) :=
  (rfl)

@[simp]
theorem blowupModelChart_apply_self (p : BlowupModel n) :
    blowupModelChart i p i = p.blowdown i := by
  simp [blowupModelChart_apply]

/-- Off the place `i`, the chart `i` is the ratio `v j / v i` for any `v` spanning the line.
(Outside the source both sides are `0`.) -/
theorem blowupModelChart_apply_of_ne (p : BlowupModel n) {v : Fin (n + 1) → ℂ} (hv : v ≠ 0)
    (hpv : p.pr = mk ℂ v hv) {j : Fin (n + 1)} (hj : j ≠ i) :
    blowupModelChart i p j = v j / v i := by
  obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hj
  simp [blowupModelChart_apply, hpv]

/-- The inverse of the chart `i` sends `w` to `([update w i 1], w i • update w i 1)`. -/
theorem blowupModelChart_symm_apply (w : Fin (n + 1) → ℂ) :
    (blowupModelChart i).symm w =
      ⟨(mk ℂ (update w i 1) (update_ne_zero w i one_ne_zero), w i • update w i 1),
        mk_update_one_smul_mem_blowupModel w i⟩ :=
  (rfl)

@[simp]
theorem pr_blowupModelChart_symm_apply (w : Fin (n + 1) → ℂ) :
    ((blowupModelChart i).symm w).pr = mk ℂ (update w i 1) (update_ne_zero w i one_ne_zero) :=
  (rfl)

/-- The blowdown read in the chart `i` is `w ↦ w i • update w i 1`; that is, `z i = w i` and
`z j = w i * w j` for `j ≠ i`. -/
theorem blowdown_blowupModelChart_symm_apply (w : Fin (n + 1) → ℂ) :
    ((blowupModelChart i).symm w).blowdown = w i • update w i 1 :=
  (rfl)

@[simp]
theorem blowdown_blowupModelChart_symm_apply_self (w : Fin (n + 1) → ℂ) :
    ((blowupModelChart i).symm w).blowdown i = w i := by
  simp [blowdown_blowupModelChart_symm_apply]

@[simp]
theorem blowdown_blowupModelChart_symm_apply_of_ne (w : Fin (n + 1) → ℂ) {j : Fin (n + 1)}
    (hj : j ≠ i) : ((blowupModelChart i).symm w).blowdown j = w i * w j := by
  simp [blowdown_blowupModelChart_symm_apply, hj]

@[simp]
theorem blowupModelChart_source : (blowupModelChart i).source = pr ⁻¹' affineOpen i :=
  (rfl)

@[simp]
theorem blowupModelChart_target : (blowupModelChart (n := n) i).target = Set.univ :=
  (rfl)

/-! ### Transitions between the charts -/

/-- The transition from the chart `i` to the chart `k` is defined where `update w i 1` has a
nonzero coordinate `k`. -/
theorem blowupModelChart_symm_trans_source (k : Fin (n + 1)) :
    ((blowupModelChart i).symm.trans (blowupModelChart k)).source =
      {w | update w i 1 k ≠ 0} := by
  ext w
  simp

/-- For `k ≠ i`, the transition from the chart `i` to the chart `k` is defined where `w k ≠ 0`. -/
theorem blowupModelChart_symm_trans_source_of_ne {k : Fin (n + 1)} (hk : k ≠ i) :
    ((blowupModelChart i).symm.trans (blowupModelChart k)).source = {w | w k ≠ 0} := by
  rw [blowupModelChart_symm_trans_source]
  ext w
  simp [update_of_ne hk]

/-- The chart `k` at the image of `w` under the inverse of the chart `i`, at a place `j ≠ k`:
with `v = update w i 1`, it is `v j / v k`. -/
@[simp]
theorem blowupModelChart_blowupModelChart_symm_apply_of_ne (k : Fin (n + 1))
    (w : Fin (n + 1) → ℂ) {j : Fin (n + 1)} (hj : j ≠ k) :
    blowupModelChart k ((blowupModelChart i).symm w) j = update w i 1 j / update w i 1 k :=
  blowupModelChart_apply_of_ne k _ _ (pr_blowupModelChart_symm_apply i w) hj

/-- The transition from the chart `i` to the chart `k`: with `v = update w i 1`, it sends `w` to
`w'` with `w' k = w i * v k` and `w' j = v j / v k` for `j ≠ k`. -/
theorem blowupModelChart_symm_trans_apply (k : Fin (n + 1)) (w : Fin (n + 1) → ℂ) :
    (blowupModelChart i).symm.trans (blowupModelChart k) w =
      Fin.insertNth k (w i * update w i 1 k)
        (fun j => update w i 1 (k.succAbove j) / update w i 1 k) := by
  ext j
  refine Fin.succAboveCases k ?_ (fun j => ?_) j <;>
    simp [Fin.succAbove_ne, blowdown_blowupModelChart_symm_apply]

theorem blowupModelChart_symm_trans_apply_self (k : Fin (n + 1)) (w : Fin (n + 1) → ℂ) :
    (blowupModelChart i).symm.trans (blowupModelChart k) w k = w i * update w i 1 k := by
  simp [blowdown_blowupModelChart_symm_apply]

theorem blowupModelChart_symm_trans_apply_of_ne (k : Fin (n + 1)) (w : Fin (n + 1) → ℂ)
    {j : Fin (n + 1)} (hj : j ≠ k) :
    (blowupModelChart i).symm.trans (blowupModelChart k) w j =
      update w i 1 j / update w i 1 k := by
  simp [hj]

end Chart

end BlowupModel

end SymplecticGeometry

end
