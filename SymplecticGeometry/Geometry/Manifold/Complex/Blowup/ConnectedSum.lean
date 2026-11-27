/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Euclidean.Inversion.Basic
public import SymplecticGeometry.Geometry.Manifold.Complex.Blowup.Model
public import TauCeti.Algebra.Group.Fin.Tuple
public import TauCeti.LinearAlgebra.Projectivization.Basic
import SymplecticGeometry.Geometry.Manifold.ContMDiff.RestrictScalars
import SymplecticGeometry.Geometry.Manifold.Projectivization.Hopf
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.Projectivization.Map
import TauCeti.Topology.Algebra.Projectivization

/-!
# Projective space minus a point as the model blowup

For `n : ℕ` and `E := Fin (n + 1) → ℂ`, write a point of `ℙ ℂ (Fin (n + 2) → ℂ)` as `[z : w]`
with `z ∈ E` and `w ∈ ℂ` (`Fin.snoc z w`). Off the point `[0 : ⋯ : 0 : 1]` the vector `z` is
nonzero, and
$$[z : w] \longmapsto \bigl([z],\ \bar w\, z / \lvert z\rvert^2\bigr)$$
is a well-defined map onto the model blowup `BlowupModel n`, where `|z|² = ∑ i, ‖z i‖ ^ 2` is the
Hermitian norm. Its inverse sends `(ℓ, t • z)`, for `z` spanning `ℓ`, to `[z : t̄ |z|²]`. This is
the identification of the complement of the point with the total space of the dual of the
tautological line bundle, followed by the conjugate-linear identification of that dual with the
tautological bundle by the Hermitian metric, as in McDuff–Salamon, §7.1. The map is not
holomorphic, so it is a diffeomorphism of the underlying real manifolds.

## Main definitions and results

* `SymplecticGeometry.projectiveBlowupOpens n`: the complement of `[0 : ⋯ : 0 : 1]` in
  `ℙ ℂ (Fin (n + 2) → ℂ)`, as an open set: Tau Ceti's `Projectivization.linearProjectionDomain`
  of `Fin.init`. By `SymplecticGeometry.mk_mem_projectiveBlowupOpens`, the line of `v` lies in it
  exactly when `Fin.init v ≠ 0`, and `SymplecticGeometry.coe_projectiveBlowupOpens` says that it
  is the complement of the point.
* `SymplecticGeometry.projectiveBlowupModelDiffeomorph n`: the smooth diffeomorphism above, for
  the real manifold structures modelled on `𝓘(ℝ, Fin (n + 1) → ℂ)`, with
  `projectiveBlowupModelDiffeomorph_apply` and `projectiveBlowupModelDiffeomorph_symm_apply` on
  representatives.
* `SymplecticGeometry.projectiveBlowupModelDiffeomorph_apply_snoc_one`: it sends `[u : 1]` to
  `([u], u / |u|²)`, and `SymplecticGeometry.blowdown_projectiveBlowupModelDiffeomorph_snoc_one`:
  read on `EuclideanSpace ℂ (Fin (n + 1))`, its blowdown there is the inversion
  `EuclideanGeometry.inversion 0 1 u` in the unit sphere.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §7.1.
-/

public section

open Function Filter Set Projectivization
open scoped ContDiff Manifold LinearAlgebra.Projectivization Topology ComplexConjugate

namespace SymplecticGeometry

variable {n : ℕ}

/-! ### The complement of the point `[0 : ⋯ : 0 : 1]` -/

/-- `Fin.init`, read as the linear map `LinearMap.funLeft ℂ ℂ Fin.castSucc`. -/
private theorem funLeft_castSucc_apply (v : Fin (n + 2) → ℂ) :
    LinearMap.funLeft ℂ ℂ Fin.castSucc v = Fin.init v :=
  (rfl)

variable (n) in
/-- The complement in `ℙ ℂ (Fin (n + 2) → ℂ)` of the point `[0 : ⋯ : 0 : 1]`, the line of the last
basis vector, as an open set: the domain of the projection `[v] ↦ [Fin.init v]`. -/
noncomputable def projectiveBlowupOpens : TopologicalSpace.Opens (ℙ ℂ (Fin (n + 2) → ℂ)) :=
  ⟨linearProjectionDomain (LinearMap.funLeft ℂ ℂ Fin.castSucc),
    isOpen_linearProjectionDomain (LinearMap.continuous_on_pi _)⟩

theorem projectiveBlowupOpens_def :
    (projectiveBlowupOpens n : Set (ℙ ℂ (Fin (n + 2) → ℂ))) =
      linearProjectionDomain (LinearMap.funLeft ℂ ℂ Fin.castSucc) :=
  (rfl)

/-- The line of a nonzero vector `v` lies off `[0 : ⋯ : 0 : 1]` exactly when the first `n + 1`
coordinates `Fin.init v` of `v` are not all zero. -/
@[simp]
theorem mk_mem_projectiveBlowupOpens {v : Fin (n + 2) → ℂ} (hv : v ≠ 0) :
    mk ℂ v hv ∈ projectiveBlowupOpens n ↔ Fin.init v ≠ 0 := by
  rw [← SetLike.mem_coe, projectiveBlowupOpens_def, mk_mem_linearProjectionDomain_iff,
    funLeft_castSucc_apply]

/-- `projectiveBlowupOpens n` is the complement of the point `[0 : ⋯ : 0 : 1]`. -/
theorem coe_projectiveBlowupOpens :
    (projectiveBlowupOpens n : Set (ℙ ℂ (Fin (n + 2) → ℂ))) =
      {mk ℂ (Pi.single (Fin.last (n + 1)) 1) (by simp)}ᶜ := by
  ext x
  induction x using Projectivization.ind with
  | h v hv =>
    rw [SetLike.mem_coe, mk_mem_projectiveBlowupOpens, mem_compl_singleton_iff, Ne, Ne,
      not_iff_not, mk_eq_mk_iff']
    constructor
    · intro h
      refine ⟨v (Fin.last _), funext fun j => ?_⟩
      induction j using Fin.lastCases with
      | last => simp
      | cast j => simpa [Fin.castSucc_ne_last, Fin.init] using (congrFun h j).symm
    · rintro ⟨a, rfl⟩
      funext j
      simp [Fin.init, Fin.castSucc_ne_last]

/-! ### Homogeneous coordinates -/

/-- The squared Hermitian norm of a scalar multiple. -/
private theorem sum_norm_smul_sq (a : ℂ) (z : Fin (n + 1) → ℂ) :
    ∑ i, ‖(a • z) i‖ ^ 2 = ‖a‖ ^ 2 * ∑ i, ‖z i‖ ^ 2 := by
  simp [mul_pow, Finset.mul_sum]

private theorem sum_norm_sq_ne_zero {z : Fin (n + 1) → ℂ} (hz : z ≠ 0) :
    ∑ i, ‖z i‖ ^ 2 ≠ 0 := by
  rw [Ne, Finset.sum_eq_zero_iff_of_nonneg fun i _ => by positivity]
  exact fun h => hz (funext fun i => by simpa using h i (Finset.mem_univ i))

/-- The blowdown coordinate `w̄ z / |z|²` of the point `[z : w]`, for `z = Fin.init v` and
`w = v (Fin.last _)`. -/
private noncomputable def blowdownCoord (v : Fin (n + 2) → ℂ) : Fin (n + 1) → ℂ :=
  (∑ i, ‖Fin.init v i‖ ^ 2)⁻¹ • conj (v (Fin.last _)) • Fin.init v

private theorem blowdownCoord_eq (v : Fin (n + 2) → ℂ) :
    blowdownCoord v =
      (((∑ i, ‖Fin.init v i‖ ^ 2 : ℝ) : ℂ)⁻¹ * conj (v (Fin.last _))) • Fin.init v := by
  rw [blowdownCoord, ← Complex.coe_smul, smul_smul, Complex.ofReal_inv]

private theorem blowdownCoord_smul {a : ℂ} (ha : a ≠ 0) {v : Fin (n + 2) → ℂ}
    (hz : Fin.init v ≠ 0) : blowdownCoord (a • v) = blowdownCoord v := by
  have hS : ((∑ i, ‖Fin.init v i‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast sum_norm_sq_ne_zero hz
  have ha' : conj a ≠ 0 := (map_ne_zero _).2 ha
  rw [blowdownCoord_eq, blowdownCoord_eq, ← funLeft_castSucc_apply (a • v), map_smul,
    funLeft_castSucc_apply, sum_norm_smul_sq, Pi.smul_apply,
    smul_eq_mul, map_mul, smul_smul, Complex.ofReal_mul, Complex.ofReal_pow, ← Complex.conj_mul' a]
  congr 1
  field_simp

private theorem mem_blowupModel_blowdownCoord {v : Fin (n + 2) → ℂ} (hz : Fin.init v ≠ 0) :
    (mk ℂ (Fin.init v) hz, blowdownCoord v) ∈ blowupModel n := by
  rw [mem_blowupModel_iff, submodule_mk, blowdownCoord_eq]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

/-- The point `[z : c]` lies off `[0 : ⋯ : 0 : 1]` when `z ≠ 0`. -/
theorem mk_snoc_mem_projectiveBlowupOpens {z : Fin (n + 1) → ℂ} (hz : z ≠ 0) (c : ℂ) :
    mk ℂ (Fin.snoc z c : Fin (n + 2) → ℂ) (Fin.snoc_ne_zero_iff.2 (Or.inl hz)) ∈
      projectiveBlowupOpens n := by
  rw [mk_mem_projectiveBlowupOpens, Fin.init_snoc]
  exact hz

private theorem init_rep_ne_zero (x : projectiveBlowupOpens n) : Fin.init x.val.rep ≠ 0 := by
  rw [← funLeft_castSucc_apply, ← mem_linearProjectionDomain_iff, ← projectiveBlowupOpens_def]
  exact x.property

/-! ### The map and its inverse -/

/-- The map `[z : w] ↦ ([z], w̄ z / |z|²)`, computed on the representative `rep`. -/
private noncomputable def toFun (x : projectiveBlowupOpens n) : BlowupModel n :=
  ⟨(mk ℂ (Fin.init x.val.rep) (init_rep_ne_zero x), blowdownCoord x.val.rep),
    mem_blowupModel_blowdownCoord _⟩

private theorem toFun_val (x : projectiveBlowupOpens n) :
    (toFun x : ℙ ℂ (Fin (n + 1) → ℂ) × (Fin (n + 1) → ℂ)) =
      (mk ℂ (Fin.init x.val.rep) (init_rep_ne_zero x), blowdownCoord x.val.rep) :=
  (rfl)

private theorem toFun_eq {x : projectiveBlowupOpens n} {v : Fin (n + 2) → ℂ} (hv : v ≠ 0)
    (hx : x.val = mk ℂ v hv) (hz : Fin.init v ≠ 0) :
    (toFun x : ℙ ℂ (Fin (n + 1) → ℂ) × (Fin (n + 1) → ℂ)) =
      (mk ℂ (Fin.init v) hz, blowdownCoord v) := by
  obtain ⟨a, ha⟩ : ∃ a : ℂ, a • v = x.val.rep :=
    (mk_eq_mk_iff' ℂ _ _ x.val.rep_ne_zero hv).1 (by rw [mk_rep]; exact hx)
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact x.val.rep_ne_zero (by rw [← ha, zero_smul])
  rw [toFun_val, Prod.mk.injEq]
  refine ⟨(mk_eq_mk_iff' ℂ _ _ _ _).2 ⟨a, by
    rw [← ha, ← funLeft_castSucc_apply (a • v), map_smul, funLeft_castSucc_apply]⟩, ?_⟩
  rw [← ha, blowdownCoord_smul ha0 hz]

/-- The coefficient of the blowdown of `p` along the representative of its line. -/
private theorem exists_smul_rep (p : BlowupModel n) : ∃ t : ℂ, t • p.pr.rep = p.blowdown :=
  Submodule.mem_span_singleton.1 (by rw [← submodule_eq]; exact p.blowdown_mem_submodule)

/-- The inverse `(ℓ, t • z) ↦ [z : t̄ |z|²]`, computed on the representative `rep` of `ℓ`. -/
private noncomputable def invFun (p : BlowupModel n) : projectiveBlowupOpens n :=
  ⟨mk ℂ (Fin.snoc p.pr.rep (conj (exists_smul_rep p).choose *
      ((∑ i, ‖p.pr.rep i‖ ^ 2 : ℝ) : ℂ)) : Fin (n + 2) → ℂ)
      (Fin.snoc_ne_zero_iff.2 (Or.inl p.pr.rep_ne_zero)),
    mk_snoc_mem_projectiveBlowupOpens p.pr.rep_ne_zero _⟩

private theorem invFun_val (p : BlowupModel n) :
    (invFun p : ℙ ℂ (Fin (n + 2) → ℂ)) = mk ℂ (Fin.snoc p.pr.rep (conj (exists_smul_rep p).choose *
      ((∑ i, ‖p.pr.rep i‖ ^ 2 : ℝ) : ℂ)) : Fin (n + 2) → ℂ)
      (Fin.snoc_ne_zero_iff.2 (Or.inl p.pr.rep_ne_zero)) :=
  (rfl)

private theorem invFun_eq {p : BlowupModel n} {z : Fin (n + 1) → ℂ} (hz : z ≠ 0)
    (hpr : p.pr = mk ℂ z hz) {c : ℂ} (hbl : p.blowdown = c • z) :
    (invFun p : ℙ ℂ (Fin (n + 2) → ℂ)) =
      mk ℂ (Fin.snoc z (conj c * ((∑ i, ‖z i‖ ^ 2 : ℝ) : ℂ)) : Fin (n + 2) → ℂ)
        (Fin.snoc_ne_zero_iff.2 (Or.inl hz)) := by
  obtain ⟨a, ha⟩ : ∃ a : ℂ, a • z = p.pr.rep :=
    (mk_eq_mk_iff' ℂ _ _ p.pr.rep_ne_zero hz).1 (by rw [mk_rep]; exact hpr)
  set t := (exists_smul_rep p).choose
  have ht : t • p.pr.rep = p.blowdown := (exists_smul_rep p).choose_spec
  have hc : t * a = c := by
    have h : (t * a) • z = c • z := by rw [mul_smul, ha, ht, hbl]
    exact smul_left_injective ℂ hz h
  have hS : ∑ i, ‖p.pr.rep i‖ ^ 2 = ‖a‖ ^ 2 * ∑ i, ‖z i‖ ^ 2 := by
    rw [← ha, sum_norm_smul_sq]
  refine (mk_eq_mk_iff' ℂ _ _ _ _).2 ⟨a, funext fun j => ?_⟩
  induction j using Fin.lastCases with
  | last =>
    simp only [Pi.smul_apply, Fin.snoc_last, smul_eq_mul, hS, ← hc, map_mul]
    push_cast
    rw [← Complex.conj_mul' a]
    ring
  | cast j => simp [← ha]

private theorem invFun_toFun (x : projectiveBlowupOpens n) : invFun (toFun x) = x := by
  have hz := init_rep_ne_zero x
  have hS : ((∑ i, ‖Fin.init x.val.rep i‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast sum_norm_sq_ne_zero hz
  refine Subtype.ext ?_
  rw [invFun_eq hz (by rw [BlowupModel.pr_def, toFun_val])
    (by rw [BlowupModel.blowdown_def, toFun_val, blowdownCoord_eq])]
  conv_rhs => rw [← mk_rep x.val]
  congr 1
  conv_rhs => rw [← Fin.snoc_init_self x.val.rep]
  congr 1
  simp only [map_mul, map_inv₀, Complex.conj_ofReal, Complex.conj_conj]
  field_simp

private theorem toFun_invFun (p : BlowupModel n) : toFun (invFun p) = p := by
  have hz := p.pr.rep_ne_zero
  have hS : ((∑ i, ‖p.pr.rep i‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast sum_norm_sq_ne_zero hz
  have h := toFun_eq (x := invFun p) _ (invFun_val p)
    (by rw [Fin.init_snoc]; exact hz)
  refine BlowupModel.ext ?_ ?_
  · rw [BlowupModel.pr_def, h]
    simp only [Fin.init_snoc, mk_rep]
  · rw [BlowupModel.blowdown_def, h, blowdownCoord_eq]
    simp only [Fin.init_snoc, Fin.snoc_last, map_mul, Complex.conj_ofReal, Complex.conj_conj]
    refine Eq.trans ?_ (exists_smul_rep p).choose_spec
    congr 1
    field_simp

/-! ### Smoothness -/

private theorem contDiffAt_blowdownCoord {v : Fin (n + 2) → ℂ} (hz : Fin.init v ≠ 0) :
    ContDiffAt ℝ ∞ blowdownCoord v := by
  have hinit : ContDiff ℝ ∞ fun v : Fin (n + 2) → ℂ => Fin.init v :=
    (LinearMap.funLeft ℝ ℂ Fin.castSucc).toContinuousLinearMap.contDiff
  have hS : ContDiff ℝ ∞ fun v : Fin (n + 2) → ℂ => ∑ i, ‖Fin.init v i‖ ^ 2 :=
    ContDiff.sum fun i _ =>
      (contDiff_norm_sq ℝ).comp ((contDiff_apply ℝ (fun _ => ℂ) i).comp hinit)
  have hw : ContDiff ℝ ∞ fun v : Fin (n + 2) → ℂ => conj (v (Fin.last _)) :=
    Complex.conjCLE.contDiff.comp (contDiff_apply ℝ (fun _ => ℂ) _)
  exact (hS.contDiffAt.inv (sum_norm_sq_ne_zero hz)).smul (hw.contDiffAt.smul hinit.contDiffAt)

/-- The first component of the map is the projection `[v] ↦ [Fin.init v]`. -/
private theorem pr_toFun (x : projectiveBlowupOpens n) :
    (toFun x).pr = linearProjection (LinearMap.funLeft ℂ ℂ Fin.castSucc) x.val := by
  conv_rhs => rw [← mk_rep x.val]
  rw [BlowupModel.pr_def, toFun_val,
    linearProjection_mk _ _ (by rw [funLeft_castSucc_apply]; exact init_rep_ne_zero x)]
  simp only [funLeft_castSucc_apply]

private theorem contMDiff_toFun :
    ContMDiff 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ (toFun (n := n)) := by
  intro x
  have hval := contMDiff_subtypeVal (I := 𝓘(ℂ, Fin (n + 1) → ℂ)) (n := ∞)
    (U := projectiveBlowupOpens n)
  refine BlowupModel.contMDiffAt_real_iff_contMDiffAt_pr_comp_and_blowdown_comp.2 ⟨?_, ?_⟩
  · have hpr := ((contMDiffOn_linearProjection (LinearMap.funLeft ℂ ℂ Fin.castSucc) ∞).contMDiffAt
      (((projectiveBlowupOpens n).isOpen).mem_nhds x.property)).comp x hval.contMDiffAt
    simpa only [comp_def, pr_toFun] using hpr.restrictScalars' ℝ
  · obtain ⟨F, hF, hFx⟩ := exists_contMDiffAt_eventually_eq_mk (r := ∞) hval.contMDiffAt (x := x)
    have hev : ∀ᶠ y in 𝓝 x, ∃ (_ : F y ≠ 0) (hz : Fin.init (F y) ≠ 0),
        (toFun y : ℙ ℂ (Fin (n + 1) → ℂ) × (Fin (n + 1) → ℂ)) =
          (mk ℂ (Fin.init (F y)) hz, blowdownCoord (F y)) := by
      filter_upwards [hFx] with y ⟨hy, hyF⟩
      have hz : Fin.init (F y) ≠ 0 := (mk_mem_projectiveBlowupOpens hy).1 (hyF ▸ y.property)
      exact ⟨hy, hz, toFun_eq hy hyF hz⟩
    obtain ⟨-, hzx, -⟩ := hev.self_of_nhds
    refine ((contDiffAt_blowdownCoord hzx).comp_contMDiffAt (hF.restrictScalars' ℝ))
      |>.congr_of_eventuallyEq ?_
    filter_upwards [hev] with y ⟨_, _, hy⟩
    exact (BlowupModel.blowdown_def _).trans (congrArg Prod.snd hy)

/-- The inverse read in the chart `i` of the blowup, in homogeneous coordinates. -/
private noncomputable def invCoord (i : Fin (n + 1)) (w : Fin (n + 1) → ℂ) : Fin (n + 2) → ℂ :=
  Fin.snoc (update w i 1) (conj (w i) * ((∑ j, ‖update w i 1 j‖ ^ 2 : ℝ) : ℂ))

private theorem contDiff_invCoord (i : Fin (n + 1)) : ContDiff ℝ ∞ (invCoord (n := n) i) := by
  have hv : ContDiff ℝ ∞ fun w : Fin (n + 1) → ℂ => update w i 1 :=
    ContDiff.update_self i contDiff_const
  have hS : ContDiff ℝ ∞ fun w : Fin (n + 1) → ℂ => ∑ j, ‖update w i 1 j‖ ^ 2 :=
    ContDiff.sum fun j _ => (contDiff_norm_sq ℝ).comp ((contDiff_apply ℝ (fun _ => ℂ) j).comp hv)
  have hc : ContDiff ℝ ∞ fun w : Fin (n + 1) → ℂ =>
      conj (w i) * ((∑ j, ‖update w i 1 j‖ ^ 2 : ℝ) : ℂ) :=
    (Complex.conjCLE.contDiff.comp (contDiff_apply ℝ (fun _ => ℂ) i)).mul
      (Complex.ofRealCLM.contDiff.comp hS)
  refine contDiff_pi.2 fun j => ?_
  induction j using Fin.lastCases with
  | last => simpa [invCoord] using hc
  | cast j => simpa [invCoord, comp_def] using (contDiff_apply ℝ (fun _ => ℂ) j).comp hv

private theorem invFun_blowupModelChart_symm (i : Fin (n + 1)) (w : Fin (n + 1) → ℂ) :
    (invFun ((BlowupModel.blowupModelChart i).symm w) : ℙ ℂ (Fin (n + 2) → ℂ)) =
      mk ℂ (invCoord i w) (Fin.snoc_ne_zero_iff.2 (Or.inl (update_ne_zero w i one_ne_zero))) :=
  invFun_eq _ (BlowupModel.pr_blowupModelChart_symm_apply i w)
    (BlowupModel.blowdown_blowupModelChart_symm_apply i w)

private theorem contMDiff_invFun :
    ContMDiff 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ (invFun (n := n)) := by
  refine (TauCeti.ContMDiff.subtypeVal_comp_iff _ _).1 fun p => ?_
  obtain ⟨i, hi⟩ := exists_mem_affineOpen p.pr
  have hsrc : p ∈ (BlowupModel.blowupModelChart i).source := by
    rw [BlowupModel.blowupModelChart_source]
    exact hi
  have hopen := (BlowupModel.blowupModelChart (n := n) i).open_source
  -- In the chart `i`, the inverse is `w ↦ [invCoord i w]`.
  have hG := (contMDiff_mkNonzero ℂ (n + 1) ∞).comp
    ((TauCeti.ContMDiff.subtypeVal_comp_iff (TauCeti.puncturedSpace _) (fun w => ⟨invCoord i w,
        TauCeti.mem_puncturedSpace.2
          (Fin.snoc_ne_zero_iff.2 (Or.inl (update_ne_zero w i one_ne_zero)))⟩)).1
      (contDiff_invCoord i).contMDiff)
  have hc := ((BlowupModel.contMDiffOn_blowupModelChart i ∞).restrictScalars' ℝ).contMDiffAt
    (hopen.mem_nhds hsrc)
  refine ((hG.contMDiffAt).comp p hc).congr_of_eventuallyEq ?_
  filter_upwards [hopen.mem_nhds hsrc] with q hq
  rw [comp_apply, comp_apply, comp_apply, mkNonzero_apply, ← invFun_blowupModelChart_symm,
    (BlowupModel.blowupModelChart i).left_inv hq]

/-! ### The diffeomorphism -/

variable (n) in
/-- The diffeomorphism `[z : w] ↦ ([z], w̄ z / |z|²)` from the complement of `[0 : ⋯ : 0 : 1]` in
`ℙ ℂ (Fin (n + 2) → ℂ)` onto the model blowup `BlowupModel n`, for the real smooth structures.
Here `z = Fin.init v` and `w = v (Fin.last _)` for homogeneous coordinates `v`, and
`|z|² = ∑ i, ‖z i‖ ^ 2`.
Its inverse sends `(ℓ, t • z)`, for `z` spanning `ℓ`, to `[z : t̄ |z|²]`. -/
noncomputable def projectiveBlowupModelDiffeomorph :
    projectiveBlowupOpens n ≃ₘ^∞⟮𝓘(ℝ, Fin (n + 1) → ℂ), 𝓘(ℝ, Fin (n + 1) → ℂ)⟯ BlowupModel n where
  toFun := toFun
  invFun := invFun
  left_inv := invFun_toFun
  right_inv := toFun_invFun
  contMDiff_toFun := contMDiff_toFun
  contMDiff_invFun := contMDiff_invFun

private theorem coe_projectiveBlowupModelDiffeomorph :
    ⇑(projectiveBlowupModelDiffeomorph n) = toFun :=
  (rfl)

private theorem coe_projectiveBlowupModelDiffeomorph_symm :
    ⇑(projectiveBlowupModelDiffeomorph n).symm = invFun :=
  (rfl)

/-- The point `([z], w̄ z / |z|²)` of the blowup, for `z = Fin.init v ≠ 0` and `w = v (Fin.last _)`,
is the image of `[v]`. -/
theorem projectiveBlowupModelDiffeomorph_apply {v : Fin (n + 2) → ℂ} (hv : v ≠ 0)
    (h : mk ℂ v hv ∈ projectiveBlowupOpens n) :
    (projectiveBlowupModelDiffeomorph n ⟨mk ℂ v hv, h⟩ :
        ℙ ℂ (Fin (n + 1) → ℂ) × (Fin (n + 1) → ℂ)) =
      (mk ℂ (Fin.init v) ((mk_mem_projectiveBlowupOpens hv).1 h),
        (∑ i, ‖Fin.init v i‖ ^ 2)⁻¹ • conj (v (Fin.last _)) • Fin.init v) := by
  rw [coe_projectiveBlowupModelDiffeomorph]
  exact toFun_eq hv rfl _

/-- The inverse sends `(ℓ, t • z)`, for a nonzero `z` spanning `ℓ`, to `[z : t̄ |z|²]`. -/
theorem projectiveBlowupModelDiffeomorph_symm_apply {z : Fin (n + 1) → ℂ} (hz : z ≠ 0) (t : ℂ)
    (h : (mk ℂ z hz, t • z) ∈ blowupModel n) :
    ((projectiveBlowupModelDiffeomorph n).symm ⟨(mk ℂ z hz, t • z), h⟩ :
        ℙ ℂ (Fin (n + 2) → ℂ)) =
      mk ℂ (Fin.snoc z (conj t * ((∑ i, ‖z i‖ ^ 2 : ℝ) : ℂ)) : Fin (n + 2) → ℂ)
        (Fin.snoc_ne_zero_iff.2 (Or.inl hz)) := by
  rw [coe_projectiveBlowupModelDiffeomorph_symm]
  exact invFun_eq hz (BlowupModel.pr_mk _ _ h) (BlowupModel.blowdown_mk _ _ h)

/-- The point `[u : 1]`, for `u ≠ 0`, goes to `([u], u / |u|²)`. -/
theorem projectiveBlowupModelDiffeomorph_apply_snoc_one {u : Fin (n + 1) → ℂ} (hu : u ≠ 0) :
    (projectiveBlowupModelDiffeomorph n ⟨mk ℂ (Fin.snoc u 1 : Fin (n + 2) → ℂ)
        (Fin.snoc_ne_zero_iff.2 (Or.inl hu)), mk_snoc_mem_projectiveBlowupOpens hu 1⟩ :
        ℙ ℂ (Fin (n + 1) → ℂ) × (Fin (n + 1) → ℂ)) =
      (mk ℂ u hu, (∑ i, ‖u i‖ ^ 2)⁻¹ • u) := by
  rw [projectiveBlowupModelDiffeomorph_apply]
  simp only [Fin.init_snoc, Fin.snoc_last, map_one, one_smul]

/-- Read on `EuclideanSpace ℂ (Fin (n + 1))`, the blowdown of the image of `[u : 1]` is the
inversion of `u ≠ 0` in the unit sphere. -/
theorem blowdown_projectiveBlowupModelDiffeomorph_snoc_one {u : EuclideanSpace ℂ (Fin (n + 1))}
    (hu : u ≠ 0) :
    (projectiveBlowupModelDiffeomorph n ⟨mk ℂ (Fin.snoc u.ofLp 1 : Fin (n + 2) → ℂ)
        (Fin.snoc_ne_zero_iff.2 (Or.inl (by rwa [Ne, WithLp.ofLp_eq_zero]))),
        mk_snoc_mem_projectiveBlowupOpens (by rwa [Ne, WithLp.ofLp_eq_zero]) 1⟩).blowdown =
      (EuclideanGeometry.inversion 0 1 u).ofLp := by
  rw [BlowupModel.blowdown_def,
    projectiveBlowupModelDiffeomorph_apply_snoc_one (by rwa [Ne, WithLp.ofLp_eq_zero])]
  simp only [EuclideanGeometry.inversion, dist_zero_right, vsub_eq_sub, sub_zero, vadd_eq_add,
    add_zero, one_div, inv_pow, EuclideanSpace.norm_sq_eq, WithLp.ofLp_smul]

end SymplecticGeometry

end
