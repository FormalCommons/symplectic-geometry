/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Fibration.Connection
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Disc
public import TauCeti.Geometry.Symplectic.Flux.Hamiltonian
import SymplecticGeometry.Analysis.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Holonomy around loops that bound discs

A loop `γ : ℝ → B` *bounds a smooth disc* (`SymplecticGeometry.BoundsSmoothDisc IB γ`) when it is
the boundary `t ↦ w (exp (2πit))` of a map `w` of the plane that is smooth on the closed unit
disc. Such a loop is smooth and `1`-periodic, and it is the boundary of a smooth disc in the sense
of Tau Ceti (`TauCeti.IsSmoothDisc`): `D (s, t) = w ((1 - φ s) + φ s · exp (2πit))`, for a smooth
profile `φ` from `0` to `1`. Conversely, each loop `t ↦ D (s, t)` of a smooth disc `D` bounds a
smooth disc, namely `z ↦ D (s · ψ ‖z‖, arg z / 2π)`, where `ψ` vanishes near `0` and is `1` at
`1`: the map is constant near the origin, where the polar angle is not smooth.

For an Ehresmann connection `D` on `proj : M → B` with an atlas `A` whose model fibre carries a
two-form `σ`, the holonomy around a loop `γ` at `b`, read in a chart `e` of `A` at `b`, is the
transport `hD.parallelTransportIn e e γ 0 1` from time `0` to time `1`. The connection has
*Hamiltonian holonomy around discs* when this holonomy is a Hamiltonian diffeomorphism of
`(F, σ)` for every loop that bounds a smooth disc and every chart at its base point.

## Main definitions

* `SymplecticGeometry.BoundsSmoothDisc IB γ`: the loop `γ` bounds a smooth disc.
* `SymplecticGeometry.BoundsSmoothDisc.path`: such a loop, as a based loop `Path (γ 0) (γ 0)`.
* `TauCeti.IsEhresmannConnection.HasHamiltonianDiscHolonomy hD A σ`: the holonomy of `D` around
  every loop that bounds a smooth disc, read in every chart of `A` at its base point, is a
  Hamiltonian diffeomorphism of `σ`.

## Main results

* `SymplecticGeometry.BoundsSmoothDisc.exists_isSmoothDisc`: a loop that bounds a smooth disc is
  the boundary of a smooth disc in the sense of Tau Ceti.
* `SymplecticGeometry.BoundsSmoothDisc.of_isSmoothDisc_slice`: every loop `t ↦ D (s, t)` of a
  smooth disc `D` bounds a smooth disc.
* `TauCeti.IsEhresmannConnection.hasHamiltonianDiscHolonomy_iff`: the definition, with the
  holonomy as the diffeomorphism `parallelTransportInDiffeomorph`.
* `TauCeti.IsEhresmannConnection.hasHamiltonianDiscHolonomy_iff_forall_exists`: for an atlas whose
  coordinate changes preserve `σ`, one chart per loop suffices, since a change of charts
  conjugates the holonomy by a diffeomorphism preserving `σ`, and the Hamiltonian group is normal
  in the group of such diffeomorphisms.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §6.4.
* [V. Guillemin, E. Lerman, S. Sternberg, *Symplectic Fibrations and Multiplicity
  Diagrams*][GuilleminLermanSternberg1996], §1.4.
-/

public section

noncomputable section

open Bundle Complex Function Set
open scoped ContDiff Manifold Topology Real

namespace SymplecticGeometry

section Disc

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]

variable (IB) in
/-- A loop `γ : ℝ → B` *bounds a smooth disc* when some map `w` of the complex plane to `B`,
smooth on the closed unit disc, has `w (exp (2πit)) = γ t` for every `t`. -/
def BoundsSmoothDisc (γ : ℝ → B) : Prop :=
  ∃ w : ℂ → B, ContMDiffOn 𝓘(ℝ, ℂ) IB ∞ w (Metric.closedBall 0 1) ∧
    ∀ t : ℝ, w (Circle.exp (2 * π * t)) = γ t

theorem boundsSmoothDisc_def (γ : ℝ → B) :
    BoundsSmoothDisc IB γ ↔ ∃ w : ℂ → B, ContMDiffOn 𝓘(ℝ, ℂ) IB ∞ w (Metric.closedBall 0 1) ∧
      ∀ t : ℝ, w (Circle.exp (2 * π * t)) = γ t :=
  Iff.rfl

/-- A constant loop bounds a smooth disc. -/
theorem boundsSmoothDisc_const (b : B) : BoundsSmoothDisc IB fun _ : ℝ ↦ b :=
  ⟨fun _ ↦ b, contMDiffOn_const, fun _ ↦ rfl⟩

namespace BoundsSmoothDisc

variable {γ : ℝ → B}

/-- A loop that bounds a smooth disc is `1`-periodic. -/
theorem periodic (h : BoundsSmoothDisc IB γ) : Periodic γ 1 := by
  obtain ⟨w, -, hw⟩ := h
  intro t
  rw [← hw, ← hw, mul_add, mul_one, Circle.exp_add, Circle.exp_two_pi, mul_one]

/-- A loop that bounds a smooth disc ends where it starts. -/
theorem apply_one (h : BoundsSmoothDisc IB γ) : γ 1 = γ 0 := by
  simpa using h.periodic 0

/-- A loop that bounds a smooth disc is smooth. -/
theorem contMDiff (h : BoundsSmoothDisc IB γ) : ContMDiff 𝓘(ℝ, ℝ) IB ∞ γ := by
  obtain ⟨w, hw, hγ⟩ := h
  have hc : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ fun t : ℝ ↦ (Circle.exp (2 * π * t) : ℂ) :=
    (Circle.contDiff_coe_exp.comp (contDiff_const.mul contDiff_id)).contMDiff
  refine (hw.comp_contMDiff hc fun t ↦ ?_).congr fun t ↦ (hγ t).symm
  rw [mem_closedBall_zero_iff, Circle.norm_coe]

/-- A loop that bounds a smooth disc is continuous. -/
theorem continuous (h : BoundsSmoothDisc IB γ) : Continuous γ :=
  h.contMDiff.continuous

/-- A loop `γ` that bounds a smooth disc, as a loop based at `γ 0` parametrized by the unit
interval. -/
def path (h : BoundsSmoothDisc IB γ) : Path (γ 0) (γ 0) where
  toFun t := γ t
  continuous_toFun := h.continuous.comp continuous_subtypeVal
  source' := rfl
  target' := h.apply_one

@[simp]
theorem path_apply (h : BoundsSmoothDisc IB γ) (t : unitInterval) : h.path t = γ t :=
  (rfl)

/-- **A loop that bounds a smooth disc bounds a disc of Tau Ceti.** If `γ` is the boundary of a
map `w` smooth on the closed unit disc, then `(s, t) ↦ w ((1 - φ s) + φ s · exp (2πit))`, for a
smooth profile `φ` from `0` to `1`, is a smooth disc bounding `γ` with centre `γ 0`. -/
theorem exists_isSmoothDisc (h : BoundsSmoothDisc IB γ) :
    ∃ D : ℝ × ℝ → B, TauCeti.IsSmoothDisc IB h.path D := by
  obtain ⟨w, hw, hγ⟩ := id h
  set φ := Real.smoothTransition
  let c : ℝ × ℝ → ℂ := fun z ↦ (1 - φ z.1 : ℝ) + (φ z.1 : ℝ) * Circle.exp (2 * π * z.2)
  have hc : ContDiff ℝ ∞ c := by
    have hφ : ContDiff ℝ ∞ φ := Real.smoothTransition.contDiff (n := ⊤)
    have hof : ContDiff ℝ ∞ fun t : ℝ ↦ (t : ℂ) := ofRealCLM.contDiff
    exact (hof.comp (contDiff_const.sub (hφ.comp contDiff_fst))).add
      ((hof.comp (hφ.comp contDiff_fst)).mul
        (Circle.contDiff_coe_exp.comp (contDiff_const.mul contDiff_snd)))
  have hcmem (z : ℝ × ℝ) : c z ∈ Metric.closedBall (0 : ℂ) 1 := by
    have h0 := Real.smoothTransition.nonneg z.1
    have h1 := Real.smoothTransition.le_one z.1
    rw [mem_closedBall_zero_iff]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Circle.norm_coe, mul_one, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (sub_nonneg.2 h1), Real.norm_of_nonneg h0, sub_add_cancel]
  have hc_one (t : ℝ) : c (1, t) = Circle.exp (2 * π * t) := by
    simp [c, φ]
  have hw1 : w 1 = γ 0 := by simpa using hγ 0
  refine ⟨w ∘ c, ⟨hw.comp_contMDiff hc.contMDiff hcmem, fun z ↦ ?_, fun t ↦ ?_, fun t ↦ ?_,
    fun s ↦ ?_⟩⟩
  · simp only [comp_apply, c]
    rw [mul_add, mul_one, Circle.exp_add, Circle.exp_two_pi, mul_one]
  · simp [c, φ, hw1]
  · simp only [comp_apply, hc_one, hγ, path_apply]
  · simp [c, hw1]

/-- **The slices of a smooth disc bound smooth discs.** For a smooth disc `D` and every `s`, the
loop `t ↦ D (s, t)` bounds a smooth disc: `z ↦ D (s · ψ ‖z‖, arg z / 2π)`, with `ψ` vanishing
near `0` and equal to `1` at `1`. -/
theorem of_isSmoothDisc_slice {x : B} {γ' : Path x x} {D : ℝ × ℝ → B}
    (hD : TauCeti.IsSmoothDisc IB γ' D) (s : ℝ) : BoundsSmoothDisc IB fun t ↦ D (s, t) := by
  have hπ : (2 * π) ≠ 0 := by positivity
  -- The disc takes the same value at two angles with the same exponential.
  have hexp (r : ℝ) {θ θ' : ℝ}
      (h : Complex.exp (↑(2 * π * θ) * I) = Complex.exp (↑(2 * π * θ') * I)) :
      D (r, θ) = D (r, θ') := by
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 h
    have hθ : θ = θ' + n * 1 := by
      have := congrArg Complex.im hn
      simp only [Complex.ofReal_mul, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, Complex.mul_re, Complex.add_im, Complex.intCast_re,
        Complex.intCast_im, Complex.re_ofNat, Complex.im_ofNat] at this
      apply mul_left_cancel₀ hπ
      linear_combination this
    rw [hθ]
    exact (Periodic.int_mul (show Periodic (fun t ↦ D (r, t)) 1 from
      fun t ↦ hD.apply_add_one (r, t)) n) θ'
  set ψ : ℝ → ℝ := fun r ↦ Real.smoothTransition (2 * r - 1)
  have hψ : ContDiff ℝ ∞ ψ := Real.smoothTransition.contDiff.comp (by fun_prop)
  set w : ℂ → B := fun z ↦ D (s * ψ ‖z‖, arg z / (2 * π))
  -- Away from `0`, the angle `arg z / 2π` can be replaced by a smooth local angle.
  have hangle (z : ℂ) (hz : z ≠ 0) (θ : ℝ) (hθ : Complex.exp (↑(2 * π * θ) * I) * ‖z‖ = z)
      (r : ℝ) :
      D (r, θ) = D (r, arg z / (2 * π)) := by
    refine hexp r ?_
    have hz' : (‖z‖ : ℂ) ≠ 0 := by simpa using hz
    apply mul_right_cancel₀ hz'
    rw [hθ, mul_div_cancel₀ _ hπ, mul_comm, norm_mul_exp_arg_mul_I]
  refine ⟨w, fun z _ ↦ (?_ : ContMDiffAt 𝓘(ℝ, ℂ) IB ∞ w z).contMDiffWithinAt, fun t ↦ ?_⟩
  · rcases lt_or_ge ‖z‖ (1 / 2) with hz | hz
    · -- Near the origin, `w` is the centre of the disc.
      refine (contMDiffAt_const (c := x)).congr_of_eventuallyEq ?_
      filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hz] with y hy
      have : ψ ‖y‖ = 0 := Real.smoothTransition.zero_of_nonpos (by simp at hy; linarith)
      simp only [w, this, mul_zero]
      exact hD.apply_zero_eq _
    · have hz0 : z ≠ 0 := by rintro rfl; norm_num at hz
      have hr : ContDiffAt ℝ ∞ (fun y : ℂ ↦ s * ψ ‖y‖) z :=
        contDiffAt_const.mul (hψ.contDiffAt.comp z (contDiffAt_norm ℝ hz0))
      -- A local angle `θ`, smooth at `z`, with `exp (2πiθ(y)) = y / ‖y‖` near `z`.
      obtain ⟨θ, hθ, hθe⟩ : ∃ θ : ℂ → ℝ, ContDiffAt ℝ ∞ θ z ∧ ∀ᶠ y in 𝓝 z,
          Complex.exp (↑(2 * π * θ y) * I) * ‖y‖ = y := by
        by_cases hzs : z ∈ slitPlane
        · refine ⟨fun y ↦ arg y / (2 * π), ?_, ?_⟩
          · have : ContDiffAt ℝ ∞ (fun y ↦ (Complex.log y).im) z :=
              Complex.imCLM.contDiff.contDiffAt.comp z
                ((Complex.contDiffAt_log hzs).restrict_scalars ℝ)
            simp_rw [← Complex.log_im]
            exact this.div_const _
          · filter_upwards with y
            rw [mul_div_cancel₀ _ hπ, mul_comm, norm_mul_exp_arg_mul_I]
        · have hzs' : -z ∈ slitPlane := by
            rw [Complex.mem_slitPlane_iff, not_or, not_lt, not_not] at hzs
            rw [Complex.mem_slitPlane_iff, neg_re]
            refine Or.inl (neg_pos.2 (hzs.1.lt_of_ne fun h ↦ hz0 ?_))
            exact Complex.ext (by simpa using h) (by simpa using hzs.2)
          refine ⟨fun y ↦ arg (-y) / (2 * π) + 1 / 2, ?_, ?_⟩
          · have : ContDiffAt ℝ ∞ (fun y ↦ (Complex.log (-y)).im) z :=
              Complex.imCLM.contDiff.contDiffAt.comp z
                (((Complex.contDiffAt_log hzs').restrict_scalars ℝ).comp z contDiff_neg.contDiffAt)
            simp_rw [← Complex.log_im]
            exact (this.div_const _).add contDiffAt_const
          · filter_upwards with y
            have h := norm_mul_exp_arg_mul_I (-y)
            rw [norm_neg] at h
            push_cast
            rw [mul_add, add_mul, Complex.exp_add, mul_div_cancel₀ _
              (mul_ne_zero two_ne_zero (ofReal_ne_zero.2 Real.pi_ne_zero))]
            have : Complex.exp (2 * π * (1 / 2) * I) = -1 := by
              rw [show (2 : ℂ) * π * (1 / 2) * I = π * I by ring, Complex.exp_pi_mul_I]
            rw [this, mul_neg_one, neg_mul, mul_comm, h, neg_neg]
      have hD' : ContMDiffAt 𝓘(ℝ, ℂ) IB ∞ (fun y ↦ D (s * ψ ‖y‖, θ y)) z :=
        hD.contMDiff.contMDiffAt.comp z (hr.prodMk hθ).contMDiffAt
      refine hD'.congr_of_eventuallyEq ?_
      filter_upwards [hθe, isOpen_ne.mem_nhds hz0] with y hy hy0
      exact (hangle y hy0 _ hy _).symm
  · simp only [w, Circle.norm_coe]
    have : ψ 1 = 1 := Real.smoothTransition.one_of_one_le (by norm_num)
    rw [this, mul_one]
    refine (hangle _ (Circle.coe_ne_zero _) t ?_ s).symm
    rw [Circle.norm_coe, ofReal_one, mul_one, Circle.coe_exp]

end BoundsSmoothDisc

end Disc

end SymplecticGeometry

namespace TauCeti

namespace IsEhresmannConnection

open SymplecticGeometry

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [FiniteDimensional ℝ EM]
  {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M] [IsManifold IM ∞ M] [IM.Boundaryless]
  [T2Space M]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B] [IB.Boundaryless]
  [T2Space B]
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace ℝ EF]
  {HF : Type*} [TopologicalSpace HF] {IF : ModelWithCorners ℝ EF HF}
  {F : Type*} [TopologicalSpace F] [ChartedSpace HF F] [IsManifold IF ∞ F]
  {n : ℕ∞} {proj : M → B} {D : Π x : M, Submodule ℝ (TangentSpace IM x)}
  (hD : IsEhresmannConnection IM IB n proj D) (A : MapFiber.Atlas F proj)
  (σ : SmoothTwoForm IF F)

/-- An Ehresmann connection `D` on `proj` has *Hamiltonian holonomy around discs*, for an atlas
`A` of `proj` and a two-form `σ` on its model fibre, when for every loop `γ` that bounds a smooth
disc and every chart `A.trivAt b` whose base set contains `γ 0`, the holonomy of `γ` read in
this chart, transport along `γ` from `0` to `1`, is a Hamiltonian diffeomorphism of `σ`. -/
def HasHamiltonianDiscHolonomy : Prop :=
  ∀ γ : ℝ → B, BoundsSmoothDisc IB γ → ∀ b : B, γ 0 ∈ (A.trivAt b).baseSet →
    ∃ φ ∈ SmoothForm.hamiltonianGroup σ,
      ⇑φ = hD.parallelTransportIn (A.trivAt b) (A.trivAt b) γ 0 1

omit [FiniteDimensional ℝ EM] [IM.Boundaryless] [T2Space M]
  [FiniteDimensional ℝ EB] [IsManifold IB ∞ B] [IB.Boundaryless] [T2Space B] in
theorem hasHamiltonianDiscHolonomy_def :
    hD.HasHamiltonianDiscHolonomy A σ ↔
      ∀ γ : ℝ → B, BoundsSmoothDisc IB γ → ∀ b : B, γ 0 ∈ (A.trivAt b).baseSet →
        ∃ φ ∈ SmoothForm.hamiltonianGroup σ,
          ⇑φ = hD.parallelTransportIn (A.trivAt b) (A.trivAt b) γ 0 1 :=
  Iff.rfl

variable {hD A σ}

/-- **Hamiltonian holonomy around discs, with the holonomy as a diffeomorphism.** For a smooth
Ehresmann connection on a proper map with a smooth atlas `A`, the connection has Hamiltonian
holonomy around discs exactly when, for every loop `γ` that bounds a smooth disc and every chart
`A.trivAt b` at `γ 0`, the diffeomorphism `parallelTransportInDiffeomorph` of transport along `γ`
from `0` to `1`, read in this chart, lies in the Hamiltonian group of `σ`. -/
theorem hasHamiltonianDiscHolonomy_iff {hD : IsEhresmannConnection IM IB ∞ proj D}
    (hfp : IsProperMap proj) (hA : A.IsContMDiff ∞ IB IF IM) :
    hD.HasHamiltonianDiscHolonomy A σ ↔
      ∀ γ : ℝ → B, ∀ hγ : BoundsSmoothDisc IB γ, ∀ b : B, ∀ hb : γ 0 ∈ (A.trivAt b).baseSet,
        hD.parallelTransportInDiffeomorph (A.trivAt b) (A.trivAt b) γ 0 1 le_top
            (hA.contMDiff_proj.of_le (by simp)) hfp (hγ.contMDiff.of_le (by simp))
            (hA.contMDiffOn_trivAt b) (hA.contMDiffOn_trivAt_symm b) (hA.contMDiffOn_trivAt b)
            (hA.contMDiffOn_trivAt_symm b) hb (hγ.apply_one ▸ hb) ∈
          SmoothForm.hamiltonianGroup σ := by
  refine forall_congr' fun γ ↦ forall_congr' fun hγ ↦ forall_congr' fun b ↦
    forall_congr' fun hb ↦ ⟨?_, fun h ↦ ⟨_, h, coe_parallelTransportInDiffeomorph ..⟩⟩
  rintro ⟨φ, hφ, hφe⟩
  convert hφ
  exact DFunLike.coe_injective (hφe ▸ coe_parallelTransportInDiffeomorph ..)

/-- **One chart per loop suffices.** Let `D` be a `C^n` Ehresmann connection, `1 ≤ n`, on a
proper map `proj` with a smooth atlas `A` whose coordinate changes preserve `σ`. Then `D` has
Hamiltonian holonomy around discs exactly when the holonomy of every loop that bounds a smooth
disc is a Hamiltonian diffeomorphism of `σ` when read in some chart of `A` at its base point. -/
theorem hasHamiltonianDiscHolonomy_iff_forall_exists (hn : 1 ≤ n) (hfp : IsProperMap proj)
    (hA : A.IsContMDiff ∞ IB IF IM)
    (hH : A.HasStructureGroup (SmoothForm.diffeomorphStabilizer σ)) :
    hD.HasHamiltonianDiscHolonomy A σ ↔
      ∀ γ : ℝ → B, BoundsSmoothDisc IB γ → ∃ b : B, γ 0 ∈ (A.trivAt b).baseSet ∧
        ∃ φ ∈ SmoothForm.hamiltonianGroup σ,
          ⇑φ = hD.parallelTransportIn (A.trivAt b) (A.trivAt b) γ 0 1 := by
  refine ⟨fun h γ hγ ↦ ⟨γ 0, A.mem_baseSet_trivAt _, h γ hγ _ (A.mem_baseSet_trivAt _)⟩,
    fun h γ hγ b₂ hb₂ ↦ ?_⟩
  obtain ⟨b, hb, φ, hφ, hφe⟩ := h γ hγ
  obtain ⟨ψ, hψ, hψe⟩ := MapFiber.Atlas.hasStructureGroup_iff.1 hH b₂ b (γ 0) hb₂ hb
  have hn' : (n : ℕ∞ω) + 1 ≤ ∞ := by exact_mod_cast le_top
  -- The inverse of `ψ` is the coordinate change back.
  have hψi : ⇑ψ⁻¹ = (A.trivAt b).coordChange (A.trivAt b₂) (γ 0) := by
    funext v
    rw [Diffeomorph.coe_inv]
    refine ψ.injective (?_ : ψ (ψ.symm v) = ψ _)
    rw [ψ.apply_symm_apply, hψe, Trivialization.coordChange_coordChange _ _ _ hb hb₂,
      Trivialization.coordChange_same_apply _ hb]
  have hmem : ψ⁻¹ * φ * ψ ∈ SmoothForm.hamiltonianGroup σ := by
    simpa using SmoothForm.mul_mul_inv_mem_hamiltonianGroup (inv_mem hψ) hφ
  refine ⟨ψ⁻¹ * φ * ψ, hmem, ?_⟩
  funext v
  rw [hD.parallelTransportIn_coordChange hn (hA.contMDiff_proj.of_le hn') hfp
    (hγ.contMDiff.of_le hn') hb hb₂ (hγ.apply_one ▸ hb) v, Diffeomorph.coe_mul,
    Diffeomorph.coe_mul, comp_apply, comp_apply, hψi, hφe, hψe, hγ.apply_one]

end IsEhresmannConnection

end TauCeti

end
