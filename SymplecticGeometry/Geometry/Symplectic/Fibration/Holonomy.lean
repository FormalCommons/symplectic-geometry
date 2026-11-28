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
import TauCeti.Analysis.SpecialFunctions.Complex.Arg
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
`1`: the map is constant near the origin, where the polar angle is not smooth. Away from the
origin, the proof of its smoothness follows Tau Ceti's `ContDiff.contDiffAt_comp_arg`, for a map
into a manifold rather than a normed space.

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
def path (h : BoundsSmoothDisc IB γ) : Path (γ 0) (γ 0) :=
  Path.ofLine h.continuous.continuousOn rfl h.apply_one

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
  -- The disc, as a function of the angle `2πt`, is `2π`-periodic.
  have hper (r : ℝ) : Periodic (fun a ↦ D (r, a / (2 * π))) (2 * π) := fun a ↦ by
    simpa only [add_div, div_self hπ] using hD.apply_add_one (r, a / (2 * π))
  set ψ : ℝ → ℝ := fun r ↦ Real.smoothTransition (2 * r - 1)
  have hψ : ContDiff ℝ ∞ ψ := Real.smoothTransition.contDiff.comp (by fun_prop)
  refine ⟨fun z ↦ D (s * ψ ‖z‖, arg z / (2 * π)),
    fun z _ ↦ (?_ : ContMDiffAt 𝓘(ℝ, ℂ) IB ∞ _ z).contMDiffWithinAt, fun t ↦ ?_⟩
  · rcases lt_or_ge ‖z‖ (1 / 2) with hz | hz
    · -- Near the origin, the map is the centre of the disc.
      refine (contMDiffAt_const (c := x)).congr_of_eventuallyEq ?_
      filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hz] with y hy
      have : ψ ‖y‖ = 0 := Real.smoothTransition.zero_of_nonpos (by simp at hy; linarith)
      simp only [this, mul_zero]
      exact hD.apply_zero_eq _
    · have hz0 : z ≠ 0 := by rintro rfl; norm_num at hz
      have hr : ContDiffAt ℝ ∞ (fun y : ℂ ↦ s * ψ ‖y‖) z :=
        contDiffAt_const.mul (hψ.contDiffAt.comp z (contDiffAt_norm ℝ hz0))
      rcases mem_slitPlane_or_neg_mem_slitPlane hz0 with h | h
      · exact hD.contMDiff.contMDiffAt.comp z
          (hr.prodMk ((contDiffAt_arg h).div_const _)).contMDiffAt
      · -- Off the slit plane, the angle is read from `arg (-y) + π`.
        have h' : ContDiffAt ℝ ∞ (fun y : ℂ ↦ (arg (-y) + π) / (2 * π)) z :=
          (((contDiffAt_arg h).comp z contDiff_neg.contDiffAt).add contDiffAt_const).div_const _
        refine (hD.contMDiff.contMDiffAt.comp z (hr.prodMk h').contMDiffAt).congr_of_eventuallyEq
          ?_
        filter_upwards [isOpen_ne.mem_nhds hz0] with y hy
        exact (hper _).apply_arg_eq_apply_arg_neg_add_pi hy
  · have : ψ 1 = 1 := Real.smoothTransition.one_of_one_le (by norm_num)
    simp only [Circle.norm_coe, this, mul_one]
    rw [Circle.coe_exp, arg_exp_mul_I, toIocMod]
    rw [(hper s).sub_zsmul_eq, mul_div_cancel_left₀ _ hπ]

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
