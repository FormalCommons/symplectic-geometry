/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Topology.OpenPartialHomeomorph.Composition
public import SymplecticGeometry.Algebra.Notation.Pi.Basic
public import SymplecticGeometry.LinearAlgebra.Projectivization.Basic
public import TauCeti.Analysis.Calculus.ContDiff.Pi
public import TauCeti.Geometry.Manifold.ContMDiff.Subtype
public import TauCeti.Geometry.Manifold.AnalyticSubmanifold.Transport
public import TauCeti.Geometry.Manifold.Immersion.Differential
public import TauCeti.Geometry.Manifold.Instances.Projectivization
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
public import TauCeti.Topology.Algebra.Projectivization

/-!
# The model blowup of `ℂⁿ⁺¹` at the origin

For `n : ℕ` and `E := Fin (n + 1) → ℂ`, the blowup of `E` at `0` is the incidence set of the pairs
`(ℓ, z) ∈ ℙ ℂ E × E` with `z` on the line `ℓ`, as in McDuff–Salamon (7.1.1). It comes with the
projection `pr` to `ℙ ℂ E` and the blowdown map to `E`; the blowdown is a bijection off the
exceptional divisor, the fibre `ℙ ℂ E × {0}` over the origin.

This file sets up the incidence set with its subspace topology, the two projections, the
exceptional divisor, and the `n + 1` charts of McDuff–Salamon, Exercise 7.1.2 (i), with the
transitions between them, and makes the incidence set a complex manifold on which both
projections, and the inclusion into `ℙ ℂ E × E`, are holomorphic. Off the divisor, the
blowdown is a biholomorphism onto the nonzero vectors of `E`.

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
* `SymplecticGeometry.BlowupModel.instChartedSpace` and
  `SymplecticGeometry.BlowupModel.instIsManifold`: these charts form an atlas modelled on `E`, whose
  transitions are analytic, so the blowup is a complex manifold of dimension `n + 1` (a `C^r`
  manifold for every `r`). The chart at `p` is taken at the index Tau Ceti's atlas of `ℙ ℂ E` uses
  at `p.pr`. Instance search finds `T2Space` and `SecondCountableTopology` from the subspace.
* `SymplecticGeometry.BlowupModel.contMDiff_iff_forall_contMDiff_comp_blowupModelChart_symm`: a
  map out of the blowup is `C^r` exactly when it is `C^r` read in each chart, and
  `SymplecticGeometry.BlowupModel.contMDiffAt_of_contMDiffAt_comp_blowupModelChart_symm`: the same
  at one point.
* `SymplecticGeometry.BlowupModel.contMDiffAt_iff_contMDiffAt_pr_comp_and_blowdown_comp`: a map
  into the blowup is `C^r` at a point, for `r ≥ 1`, exactly when its two projections are.
* `SymplecticGeometry.BlowupModel.contMDiff_pr`, `SymplecticGeometry.BlowupModel.contMDiff_blowdown`
  and `SymplecticGeometry.BlowupModel.contMDiff_blowupModel_val`: the projection to `ℙ ℂ E`, the
  blowdown and the inclusion into `ℙ ℂ E × E` are holomorphic.
* `SymplecticGeometry.BlowupModel.isSmoothEmbedding_blowupModel_val`: the inclusion into
  `ℙ ℂ E × E` is a holomorphic embedding (`Manifold.IsSmoothEmbedding`), and
  `SymplecticGeometry.BlowupModel.isMAnalyticSubmanifold_blowupModel`: so the incidence set is a
  complex submanifold of `ℙ ℂ E × E` of dimension `n + 1` (Tau Ceti's
  `TauCeti.IsMAnalyticSubmanifold`).
* `SymplecticGeometry.BlowupModel.blowdownDiffeomorph n`: off the exceptional divisor, the blowdown
  is a biholomorphism of open subsets onto `{z : E | z ≠ 0}`, with inverse `z ↦ ([z], z)`
  (`coe_blowdownDiffeomorph`, `blowdownDiffeomorph_symm_apply`).

## Implementation notes

The atlas, the choice of `chartAt`, the proof of the manifold instance by
`isManifold_of_contDiffOn`, and the smoothness of the charts and of their inverses follow Tau Ceti's
`Projectivization.instChartedSpace`, `Projectivization.instIsManifold`,
`Projectivization.contMDiffOn_affineChart` and `Projectivization.contMDiff_affineChart_symm`
(`TauCeti.Geometry.Manifold.Instances.Projectivization`). The projection is shown holomorphic by
Tau Ceti's `Projectivization.contMDiffAt_of_eventually_eq_mk`.

The inclusion is an immersion by Tau Ceti's `ContMDiffOn.isImmersionAt_of_comp_eventuallyEq_id`:
near a point whose line lies in `affineOpen i`, reading the chart `i` on `ℙ ℂ E × E` and applying
its inverse gives a holomorphic left inverse. The submanifold statement then follows from Tau
Ceti's `Manifold.IsSmoothEmbedding.isMAnalyticSubmanifold_range`.

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

/-! ### The complex manifold structure -/

section Manifold

open Function
open scoped ContDiff Manifold

/-- The atlas of the blowup consisting of its `n + 1` charts `blowupModelChart i`. The chart at a
point `p` is the chart at the index that Tau Ceti's atlas of `ℙ ℂ E` uses at `p.pr`. -/
noncomputable instance instChartedSpace : ChartedSpace (Fin (n + 1) → ℂ) (BlowupModel n) where
  atlas := Set.range blowupModelChart
  chartAt p := blowupModelChart (exists_mem_affineOpen p.pr).choose
  mem_chart_source p := by
    rw [blowupModelChart_source]
    exact (exists_mem_affineOpen p.pr).choose_spec
  chart_mem_atlas _ := Set.mem_range_self _

/-- The charts of the atlas of the blowup are exactly the charts `blowupModelChart i`. -/
theorem mem_atlas_iff (e : OpenPartialHomeomorph (BlowupModel n) (Fin (n + 1) → ℂ)) :
    e ∈ atlas (Fin (n + 1) → ℂ) (BlowupModel n) ↔ ∃ i, blowupModelChart i = e :=
  Iff.rfl

/-- Each chart `blowupModelChart i` belongs to the atlas of the blowup. -/
theorem blowupModelChart_mem_atlas (i : Fin (n + 1)) :
    blowupModelChart i ∈ atlas (Fin (n + 1) → ℂ) (BlowupModel n) :=
  Set.mem_range_self i

/-- The chart at `p` is the chart `blowupModelChart i` at the index `i` that Tau Ceti's atlas of
`ℙ ℂ E` uses at `p.pr`. -/
theorem chartAt_eq (p : BlowupModel n) :
    chartAt (Fin (n + 1) → ℂ) p = blowupModelChart (exists_mem_affineOpen p.pr).choose :=
  (rfl)

/-- The transitions between the charts of the blowup are `C^r` for every `r`, including the
analytic order `ω`. -/
theorem contDiffOn_blowupModelChart_symm_trans (i k : Fin (n + 1)) (r : ℕ∞ω) :
    ContDiffOn ℂ r ((blowupModelChart i).symm.trans (blowupModelChart k))
      ((blowupModelChart i).symm.trans (blowupModelChart k)).source := by
  have hv (j : Fin (n + 1)) : ContDiff ℂ r fun w : Fin (n + 1) → ℂ => update w i 1 j :=
    (contDiff_apply ℂ (fun _ => ℂ) j).comp (ContDiff.update_self i contDiff_const)
  rw [blowupModelChart_symm_trans_source]
  refine contDiffOn_pi.2 fun j => ?_
  by_cases hj : j = k
  · subst hj
    refine (((contDiff_apply ℂ (fun _ => ℂ) i).mul (hv j)).contDiffOn).congr fun w _ => ?_
    exact blowupModelChart_symm_trans_apply_self i j w
  · refine ((hv j).contDiffOn.div (hv k).contDiffOn fun w hw => hw).congr fun w _ => ?_
    exact blowupModelChart_symm_trans_apply_of_ne i k w hj

/-- The blowup of `ℂⁿ⁺¹` at the origin, with the charts `blowupModelChart i`, is a `C^r` manifold
for every `r`; for `r = ω` it is a complex manifold of dimension `n + 1`. -/
instance instIsManifold (r : ℕ∞ω) : IsManifold 𝓘(ℂ, Fin (n + 1) → ℂ) r (BlowupModel n) := by
  apply isManifold_of_contDiffOn
  rintro _ _ ⟨i, rfl⟩ ⟨k, rfl⟩
  simpa using contDiffOn_blowupModelChart_symm_trans i k r

/-- Each chart `blowupModelChart i` lies in the maximal atlas of the blowup. -/
theorem blowupModelChart_mem_maximalAtlas (r : ℕ∞ω) (i : Fin (n + 1)) :
    blowupModelChart i ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin (n + 1) → ℂ) r (BlowupModel n) :=
  IsManifold.subset_maximalAtlas (blowupModelChart_mem_atlas i)

/-- Each chart of the blowup is a `C^r` map on its source. -/
theorem contMDiffOn_blowupModelChart (i : Fin (n + 1)) (r : ℕ∞ω) :
    ContMDiffOn 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) r (blowupModelChart i)
      (blowupModelChart i).source :=
  contMDiffOn_of_mem_maximalAtlas (blowupModelChart_mem_maximalAtlas r i)

/-- The inverse of each chart of the blowup is a `C^r` map on all of `E`. -/
theorem contMDiff_blowupModelChart_symm (i : Fin (n + 1)) (r : ℕ∞ω) :
    ContMDiff 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) r (blowupModelChart (n := n) i).symm := by
  rw [← contMDiffOn_univ]
  simpa using contMDiffOn_symm_of_mem_maximalAtlas (blowupModelChart_mem_maximalAtlas r i)

/-- A map out of the blowup is `C^r` at a point `p` of the source of the chart `i` if it is `C^r`
read in that chart, at the image of `p`. -/
theorem contMDiffAt_of_contMDiffAt_comp_blowupModelChart_symm {F H M : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F] [TopologicalSpace H] {I : ModelWithCorners ℂ F H}
    [TopologicalSpace M] [ChartedSpace H M] {f : BlowupModel n → M} {r : ℕ∞ω} {p : BlowupModel n}
    {i : Fin (n + 1)} (hp : p ∈ (blowupModelChart i).source)
    (hf : ContMDiffAt 𝓘(ℂ, Fin (n + 1) → ℂ) I r (f ∘ (blowupModelChart i).symm)
      (blowupModelChart i p)) :
    ContMDiffAt 𝓘(ℂ, Fin (n + 1) → ℂ) I r f p := by
  have hsrc : (blowupModelChart i).source ∈ 𝓝 p := (blowupModelChart i).open_source.mem_nhds hp
  refine (hf.comp p ((contMDiffOn_blowupModelChart i r).contMDiffAt hsrc)).congr_of_eventuallyEq ?_
  filter_upwards [hsrc] with q hq
  rw [comp_apply, comp_apply, (blowupModelChart i).left_inv hq]

/-- A map out of the blowup is `C^r` if and only if it is `C^r` read in each chart
`blowupModelChart i`, that is, composed with the inverse of each chart, a map defined on all of
`E`. -/
theorem contMDiff_iff_forall_contMDiff_comp_blowupModelChart_symm {F H M : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F] [TopologicalSpace H] {I : ModelWithCorners ℂ F H}
    [TopologicalSpace M] [ChartedSpace H M] {f : BlowupModel n → M} {r : ℕ∞ω} :
    ContMDiff 𝓘(ℂ, Fin (n + 1) → ℂ) I r f ↔
      ∀ i, ContMDiff 𝓘(ℂ, Fin (n + 1) → ℂ) I r (f ∘ (blowupModelChart i).symm) := by
  refine ⟨fun hf i => hf.comp (contMDiff_blowupModelChart_symm i r), fun hf p => ?_⟩
  obtain ⟨i, hi⟩ := exists_mem_affineOpen p.pr
  exact contMDiffAt_of_contMDiffAt_comp_blowupModelChart_symm (by rwa [blowupModelChart_source])
    (hf i _)

/-- The projection of the blowup to `ℙ ℂ E` is `C^r` for every `r`; for `r = ω` it is
holomorphic. -/
theorem contMDiff_pr (r : ℕ∞ω) :
    ContMDiff 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin n → ℂ) r (pr : BlowupModel n → _) :=
  -- In the chart `i`, the line `pr` is spanned by `update w i 1`.
  contMDiff_iff_forall_contMDiff_comp_blowupModelChart_symm.2 fun i _ =>
    contMDiffAt_of_eventually_eq_mk
      (ContDiff.update_self i contDiff_const).contMDiff.contMDiffAt
      (Eventually.of_forall fun w =>
        ⟨update_ne_zero w i one_ne_zero, pr_blowupModelChart_symm_apply i w⟩)

/-- The blowdown map of the blowup to `E` is `C^r` for every `r`; for `r = ω` it is
holomorphic. -/
theorem contMDiff_blowdown (r : ℕ∞ω) :
    ContMDiff 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) r (blowdown : BlowupModel n → _) :=
  -- In the chart `i`, the blowdown is `w ↦ w i • update w i 1`.
  contMDiff_iff_forall_contMDiff_comp_blowupModelChart_symm.2 fun i =>
    (((contDiff_apply ℂ (fun _ => ℂ) i).smul
      (ContDiff.update_self i contDiff_const)).contMDiff).congr fun w =>
        blowdown_blowupModelChart_symm_apply i w

/-- The inclusion of the blowup into `ℙ ℂ E × E` is `C^r` for every `r`; for `r = ω` it is
holomorphic. -/
theorem contMDiff_blowupModel_val (r : ℕ∞ω) :
    ContMDiff 𝓘(ℂ, Fin (n + 1) → ℂ) (𝓘(ℂ, Fin n → ℂ).prod 𝓘(ℂ, Fin (n + 1) → ℂ)) r
      (Subtype.val : BlowupModel n → ℙ ℂ (Fin (n + 1) → ℂ) × (Fin (n + 1) → ℂ)) := by
  have h : (Subtype.val : BlowupModel n → _) = fun p => (pr p, blowdown p) :=
    funext fun p => Prod.ext (pr_def p).symm (blowdown_def p).symm
  rw [h]
  exact (contMDiff_pr r).prodMk (contMDiff_blowdown r)

/-- The blowup is nonempty; for instance, it contains the image of `0` under the inverse of the
chart `0`. -/
instance instNonempty : Nonempty (BlowupModel n) :=
  ⟨(blowupModelChart 0).symm 0⟩

/-- The inclusion of the blowup into `ℙ ℂ E × E` is a `C^r` smooth embedding for every `r ≥ 1`;
for `r = ω` it is a holomorphic embedding. -/
theorem isSmoothEmbedding_blowupModel_val {r : ℕ∞ω} (hr : 1 ≤ r) :
    Manifold.IsSmoothEmbedding 𝓘(ℂ, Fin (n + 1) → ℂ) (𝓘(ℂ, Fin n → ℂ).prod 𝓘(ℂ, Fin (n + 1) → ℂ))
      r (Subtype.val : BlowupModel n → ℙ ℂ (Fin (n + 1) → ℂ) × (Fin (n + 1) → ℂ)) := by
  refine ⟨TauCeti.isImmersion_iff_forall_isImmersionAt.2 fun p => ?_, IsEmbedding.subtypeVal⟩
  obtain ⟨i, hi⟩ := exists_mem_affineOpen (pr p)
  have hsrc : p ∈ (blowupModelChart i).source := by rw [blowupModelChart_source]; exact hi
  -- Near `p`, the chart `i` read on `ℙ ℂ E × E`, followed by its inverse, is a `C^r` left inverse
  -- of the inclusion.
  let φ : ℙ ℂ (Fin (n + 1) → ℂ) × (Fin (n + 1) → ℂ) → Fin (n + 1) → ℂ :=
    fun q => Fin.insertNth i (q.2 i) (affineChart i q.1)
  have hL : ContDiff ℂ r fun q : (Fin n → ℂ) × (Fin (n + 1) → ℂ) =>
      Fin.insertNth (α := fun _ => ℂ) i (q.2 i) q.1 :=
    ((contDiff_apply ℂ (fun _ => ℂ) i).comp contDiff_snd).finInsertNth (F := fun _ => ℂ) i
      contDiff_fst
  have hpair : ContMDiffOn (𝓘(ℂ, Fin n → ℂ).prod 𝓘(ℂ, Fin (n + 1) → ℂ))
      𝓘(ℂ, (Fin n → ℂ) × (Fin (n + 1) → ℂ)) r
      (fun q : ℙ ℂ (Fin (n + 1) → ℂ) × (Fin (n + 1) → ℂ) => (affineChart i q.1, q.2))
      (Prod.fst ⁻¹' affineOpen i) :=
    ((contMDiffOn_affineChart i r).comp contMDiffOn_fst fun _ hq => hq).prodMk_space
      contMDiffOn_snd
  have hφ : ContMDiffAt (𝓘(ℂ, Fin n → ℂ).prod 𝓘(ℂ, Fin (n + 1) → ℂ)) 𝓘(ℂ, Fin (n + 1) → ℂ) r φ
      p.val :=
    hL.contMDiff.contMDiffAt.comp _
      (hpair.contMDiffAt (((isOpen_affineOpen i).preimage continuous_fst).mem_nhds hi))
  have hφval : φ ∘ Subtype.val = blowupModelChart i := by
    funext q
    rw [comp_apply, blowupModelChart_apply, pr_def, blowdown_def]
  have hleft : (blowupModelChart i).symm ∘ φ ∘ Subtype.val =ᶠ[𝓝 p] id := by
    rw [hφval]
    exact (blowupModelChart i).eventually_left_inverse hsrc
  exact (contMDiff_blowupModel_val r).contMDiffOn.isImmersionAt_of_comp_eventuallyEq_id
    isOpen_univ (Set.mem_univ p) hr
    (((contMDiff_blowupModelChart_symm i r).contMDiffAt.comp _ hφ).mdifferentiableAt
      (by rintro rfl; simp at hr)) hleft

/-- The incidence set `blowupModel n` is a complex submanifold of `ℙ ℂ E × E` of dimension
`n + 1`: Tau Ceti's `TauCeti.IsMAnalyticSubmanifold` for the product model, with any continuous
linear identification `e` of the model space `(Fin n → ℂ) × E` with some `Fin m → ℂ`. -/
theorem isMAnalyticSubmanifold_blowupModel {m : ℕ}
    (e : ((Fin n → ℂ) × (Fin (n + 1) → ℂ)) ≃L[ℂ] Fin m → ℂ) :
    TauCeti.IsMAnalyticSubmanifold (𝓘(ℂ, Fin n → ℂ).prod 𝓘(ℂ, Fin (n + 1) → ℂ)) e (n + 1)
      (blowupModel n) := by
  have := (isSmoothEmbedding_blowupModel_val (n := n) (r := ω) le_top).isMAnalyticSubmanifold_range
    (ContinuousLinearEquiv.refl ℂ (Fin (n + 1) → ℂ)) e
  rwa [Subtype.range_coe] at this

/-- A map into the blowup is `C^r` at a point, for `r ≥ 1`, if and only if its composites with the
projection to `ℙ ℂ E` and with the blowdown are. -/
theorem contMDiffAt_iff_contMDiffAt_pr_comp_and_blowdown_comp {F H M : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F] [TopologicalSpace H] {I : ModelWithCorners ℂ F H}
    [TopologicalSpace M] [ChartedSpace H M] {f : M → BlowupModel n} {x : M} {r : ℕ∞ω}
    (hr : 1 ≤ r) :
    ContMDiffAt I 𝓘(ℂ, Fin (n + 1) → ℂ) r f x ↔
      ContMDiffAt I 𝓘(ℂ, Fin n → ℂ) r (fun y => (f y).pr) x ∧
        ContMDiffAt I 𝓘(ℂ, Fin (n + 1) → ℂ) r (fun y => (f y).blowdown) x := by
  rw [(isSmoothEmbedding_blowupModel_val hr).contMDiffAt_iff_comp, contMDiffAt_prod_iff]
  simp only [comp_def, ← pr_def, ← blowdown_def]

-- Instance search finds the subspace instances of `ℙ ℂ E × E`.
example : T2Space (BlowupModel n) := inferInstance

example : SecondCountableTopology (BlowupModel n) := inferInstance

end Manifold

/-! ### The blowdown off the exceptional divisor -/

section Blowdown

open Function TopologicalSpace
open scoped ContDiff Manifold

/-- A nonzero vector `z` lies on the line it spans, so `(mk z, z)` is a point of the blowup. -/
theorem mk_self_mem_blowupModel {z : Fin (n + 1) → ℂ} (hz : z ≠ 0) :
    (mk ℂ z hz, z) ∈ blowupModel n := by
  rw [mem_blowupModel_iff, submodule_mk]
  exact Submodule.mem_span_singleton_self z

/-- Off the exceptional divisor, the line of a point of the blowup is spanned by its blowdown. -/
theorem mk_blowdown {p : BlowupModel n} (hp : p.blowdown ≠ 0) : mk ℂ p.blowdown hp = p.pr :=
  mem_submodule_iff.1 p.blowdown_mem_submodule hp

variable (n) in
/-- The blowdown `π` off the exceptional divisor, as a biholomorphism from the open complement of
the divisor onto the open set of nonzero vectors of `E`. Its inverse sends `z ≠ 0` to the point
`(mk z, z)`. -/
noncomputable def blowdownDiffeomorph :
    (⟨(exceptionalDivisor n)ᶜ, isClosed_exceptionalDivisor.isOpen_compl⟩ : Opens (BlowupModel n))
      ≃ₘ^ω⟮𝓘(ℂ, Fin (n + 1) → ℂ), 𝓘(ℂ, Fin (n + 1) → ℂ)⟯
      (⟨{z | z ≠ 0}, isOpen_ne⟩ : Opens (Fin (n + 1) → ℂ)) where
  toFun p := ⟨p.val.blowdown, p.property⟩
  invFun z := ⟨⟨_, mk_self_mem_blowupModel z.property⟩, z.property⟩
  left_inv p := Subtype.ext <| ext (mk_blowdown p.property) rfl
  right_inv _ := rfl
  contMDiff_toFun := (TauCeti.ContMDiff.subtypeVal_comp_iff _ _).1
    ((contMDiff_blowdown ω).comp contMDiff_subtypeVal)
  contMDiff_invFun := by
    refine (TauCeti.ContMDiff.subtypeVal_comp_iff _ _).1 ?_
    refine ((isSmoothEmbedding_blowupModel_val (n := n) (r := ω) le_top).contMDiff_iff_comp).2
      fun z => ?_
    exact (contMDiffAt_of_eventually_eq_mk contMDiff_subtypeVal.contMDiffAt
      (Eventually.of_forall fun y => ⟨y.property, rfl⟩)).prodMk contMDiff_subtypeVal.contMDiffAt

@[simp]
theorem coe_blowdownDiffeomorph (p : (⟨(exceptionalDivisor n)ᶜ, _⟩ : Opens (BlowupModel n))) :
    (blowdownDiffeomorph n p : Fin (n + 1) → ℂ) = p.val.blowdown :=
  (rfl)

@[simp]
theorem blowdownDiffeomorph_symm_apply
    (z : (⟨{z | z ≠ 0}, isOpen_ne⟩ : Opens (Fin (n + 1) → ℂ))) :
    ((blowdownDiffeomorph n).symm z : BlowupModel n) =
      ⟨(mk ℂ z z.property, z), mk_self_mem_blowupModel z.property⟩ :=
  (rfl)

end Blowdown

end BlowupModel

end SymplecticGeometry

end
