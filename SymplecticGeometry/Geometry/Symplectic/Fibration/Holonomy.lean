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
import SymplecticGeometry.Geometry.Diffeomorphism.Diffeotopy.OfContMDiff
import TauCeti.Geometry.Manifold.ContMDiff.Prod
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

A smooth disc `Δ` with centre `x` sweeps out loops `t ↦ Δ (s, t)` at `x`, constant for `s = 0`.
Read in a chart `e` at `x`, their holonomies form a diffeotopy of the model fibre
(`TauCeti.IsEhresmannConnection.holonomyDiffeotopy`), built with the library's
`TauCeti.Diffeotopy.ofContMDiff`: it starts at the identity since transport along a constant
curve is trivial, and it is jointly smooth because transport depends smoothly on a family of
curves (`TauCeti.IsEhresmannConnection.contMDiffOn_parallelTransport_param`). It ends at the
holonomy of the boundary loop of the disc, and for a symplectic connection all its slices
preserve `σ`.

## Main definitions

* `SymplecticGeometry.BoundsSmoothDisc IB γ`: the loop `γ` bounds a smooth disc.
* `SymplecticGeometry.BoundsSmoothDisc.path`: such a loop, as a based loop `Path (γ 0) (γ 0)`.
* `TauCeti.IsEhresmannConnection.HasHamiltonianDiscHolonomy hD A σ`: the holonomy of `D` around
  every loop that bounds a smooth disc, read in every chart of `A` at its base point, is a
  Hamiltonian diffeomorphism of `σ`.
* `TauCeti.IsEhresmannConnection.holonomyDiffeotopy`: the diffeotopy of the model fibre whose
  slice at `s` is the holonomy, read in a chart, of the loop `t ↦ Δ (s, t)` of a smooth disc.

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
* `TauCeti.IsEhresmannConnection.contMDiff_parallelTransportIn_isSmoothDisc`: the holonomies of
  the loops of a smooth disc depend smoothly on the loop.
* `TauCeti.IsEhresmannConnection.final_holonomyDiffeotopy`: the holonomy diffeotopy of a disc
  ends at the holonomy of its boundary loop.
* `TauCeti.IsEhresmannConnection.timeSlice_holonomyDiffeotopy_mem_diffeomorphStabilizer`: for a
  symplectic connection, every slice of the holonomy diffeotopy preserves `σ`.

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

section HolonomyDiffeotopy

omit [FiniteDimensional ℝ EB] [IsManifold IB ∞ B] [IB.Boundaryless] [T2Space B] in
/-- Each loop `t ↦ Δ (s, t)` of a smooth disc `Δ` is smooth. -/
theorem _root_.TauCeti.IsSmoothDisc.contMDiff_slice {x : B} {γ : Path x x} {Δ : ℝ × ℝ → B}
    (hΔ : IsSmoothDisc IB γ Δ) (s : ℝ) : ContMDiff 𝓘(ℝ, ℝ) IB ∞ fun t ↦ Δ (s, t) :=
  hΔ.contMDiff.comp (contDiff_const.prodMk contDiff_id).contMDiff

variable [CompleteSpace EF] [BoundarylessManifold IF F]
  {e : Trivialization F proj} {x : B} {γ : Path x x} {Δ : ℝ × ℝ → B}

omit [IsManifold IF ∞ F] [CompleteSpace EF] [BoundarylessManifold IF F] in
/-- **The holonomies of the slices of a disc depend smoothly on the slice.** Let `D` be a smooth
Ehresmann connection on a proper smooth map `proj`, `Δ` a smooth disc with centre `x`, and `e` a
trivialization of `proj`, smooth with a smooth inverse, whose base set contains `x`. The map
`(s, v) ↦` transport of `v` along the loop `t ↦ Δ (s, t)` from `0` to `1`, read in `e`, is smooth
on `[0, 1] × F`. -/
theorem contMDiff_parallelTransportIn_isSmoothDisc
    (hD : IsEhresmannConnection IM IB ∞ proj D) (hf : ContMDiff IM IB ∞ proj)
    (hfp : IsProperMap proj) (he : ContMDiffOn IM (IB.prod IF) ∞ e e.source)
    (he_symm : ContMDiffOn (IB.prod IF) IM ∞ e.toOpenPartialHomeomorph.symm e.target)
    (hΔ : IsSmoothDisc IB γ Δ) (hx : x ∈ e.baseSet) :
    ContMDiff ((𝓡∂ 1).prod IF) IF ∞
      fun p : unitInterval × F ↦ hD.parallelTransportIn e e (fun t ↦ Δ (p.1, t)) 0 1 p.2 := by
  have hf' : ContMDiff IM IB ((⊤ : ℕ∞) + 1) proj := hf.of_le (by simp)
  have hΔc : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) IB ((⊤ : ℕ∞) + 1) Δ :=
    contMDiff_prod_modelWithCornersSelf_iff.2 (hΔ.contMDiff.of_le (by simp))
  have hT := hD.contMDiffOn_parallelTransport_param le_top hf' hfp isOpen_univ
    hΔc.contMDiffOn 0 1
  -- The point of the fibre over the centre with coordinate `v`, at the parameter `s`.
  have hg : ContMDiff ((𝓡∂ 1).prod IF) (𝓘(ℝ, ℝ).prod IM) ∞
      fun p : unitInterval × F ↦ ((p.1 : ℝ), e.fiberInclusionMap hx p.2) :=
    (contMDiff_subtypeVal_Icc.comp contMDiff_fst).prodMk
      ((e.contMDiff_fiberInclusionMap he_symm hx).comp contMDiff_snd)
  have h₁ := hT.comp_contMDiff hg fun p ↦
    ⟨mem_univ _, (e.proj_fiberInclusionMap hx p.2).trans (hΔ.apply_seam p.1).symm⟩
  have h₂ := he.comp_contMDiff h₁ fun p ↦ by
    refine e.mem_source.2 ?_
    have hy := hD.parallelTransport_mem_preimage le_top hf' hfp
      ((hΔ.contMDiff_slice p.1).of_le (by simp))
      (x := e.fiberInclusionMap hx p.2)
      ((e.proj_fiberInclusionMap hx p.2).trans (hΔ.apply_seam p.1).symm) 1
    rw [mem_preimage, mem_singleton_iff] at hy
    rw [comp_apply, hy]
    exact (hΔ.apply_seam_one p.1).symm ▸ hx
  refine (contMDiff_snd.comp h₂).congr fun p ↦ ?_
  simp only [comp_apply, parallelTransportIn_def, hΔ.apply_seam p.1, e.fiberInclusionMap_apply]

/-- **The holonomy diffeotopy of a smooth disc.** Let `D` be a smooth Ehresmann connection on a
proper smooth map `proj`, `Δ` a smooth disc bounding a loop `γ` at `x`, and `e` a trivialization
of `proj`, smooth with a smooth inverse, whose base set contains `x`. The diffeotopy of the model
fibre `F` whose slice at time `s` is the holonomy of the loop `t ↦ Δ (s, t)` read in `e`, the
transport `hD.parallelTransportIn e e (fun t ↦ Δ (s, t)) 0 1`. It starts at the identity, since
the loop at `s = 0` is constant, and ends at the holonomy of the boundary loop
`t ↦ Δ (1, t)`. -/
def holonomyDiffeotopy (hD : IsEhresmannConnection IM IB ∞ proj D)
    (hf : ContMDiff IM IB ∞ proj) (hfp : IsProperMap proj)
    (he : ContMDiffOn IM (IB.prod IF) ∞ e e.source)
    (he_symm : ContMDiffOn (IB.prod IF) IM ∞ e.toOpenPartialHomeomorph.symm e.target)
    (hΔ : IsSmoothDisc IB γ Δ) (hx : x ∈ e.baseSet) : Diffeotopy IF ∞ F :=
  Diffeotopy.ofContMDiff
    (fun s ↦ hD.parallelTransportInDiffeomorph e e (fun t ↦ Δ (s, t)) 0 1 le_top
      (hf.of_le (by simp)) hfp
      ((hΔ.contMDiff_slice _).of_le (by simp)) he he_symm he
      he_symm ((hΔ.apply_seam s).symm ▸ hx) ((hΔ.apply_seam_one s).symm ▸ hx))
    (by simpa only [coe_parallelTransportInDiffeomorph] using
      hD.contMDiff_parallelTransportIn_isSmoothDisc hf hfp he he_symm hΔ hx)
    fun v ↦ by
      simp only [coe_parallelTransportInDiffeomorph, Set.Icc.coe_zero, hΔ.apply_zero_eq,
        parallelTransportIn_def]
      rw [hD.parallelTransport_const (by simp) (hf.of_le (by simp)), e.apply_symm_apply' hx]

variable {hD : IsEhresmannConnection IM IB ∞ proj D} {hf : ContMDiff IM IB ∞ proj}
  {hfp : IsProperMap proj} {he : ContMDiffOn IM (IB.prod IF) ∞ e e.source}
  {he_symm : ContMDiffOn (IB.prod IF) IM ∞ e.toOpenPartialHomeomorph.symm e.target}

/-- The holonomy diffeotopy of a disc `Δ` sends `(s, v)` to the transport of `v` along the loop
`t ↦ Δ (s, t)` from `0` to `1`, read in `e`. -/
@[simp]
theorem holonomyDiffeotopy_apply (hΔ : IsSmoothDisc IB γ Δ) (hx : x ∈ e.baseSet)
    (p : unitInterval × F) :
    hD.holonomyDiffeotopy hf hfp he he_symm hΔ hx p =
      hD.parallelTransportIn e e (fun t ↦ Δ (p.1, t)) 0 1 p.2 := by
  rw [holonomyDiffeotopy, Diffeotopy.ofContMDiff_apply, coe_parallelTransportInDiffeomorph]

/-- The slice at time `s` of the holonomy diffeotopy of a disc `Δ` is the holonomy of the loop
`t ↦ Δ (s, t)` read in `e`, as a diffeomorphism. -/
theorem timeSlice_holonomyDiffeotopy (hΔ : IsSmoothDisc IB γ Δ) (hx : x ∈ e.baseSet)
    (s : unitInterval) :
    (hD.holonomyDiffeotopy hf hfp he he_symm hΔ hx).timeSlice s =
      hD.parallelTransportInDiffeomorph e e (fun t ↦ Δ (s, t)) 0 1 le_top
        (hf.of_le (by simp)) hfp
        ((hΔ.contMDiff_slice _).of_le (by simp)) he he_symm he
        he_symm ((hΔ.apply_seam s).symm ▸ hx) ((hΔ.apply_seam_one s).symm ▸ hx) :=
  by rw [holonomyDiffeotopy, Diffeotopy.timeSlice_ofContMDiff]

/-- **The holonomy diffeotopy ends at the holonomy.** The final map of the holonomy diffeotopy of
a disc `Δ` is the holonomy, read in `e`, of its boundary loop `t ↦ Δ (1, t)`, the `1`-periodic
smooth loop that agrees with `γ` on `[0, 1]`: transport along it from `0` to `1`, as a
diffeomorphism. -/
theorem final_holonomyDiffeotopy (hΔ : IsSmoothDisc IB γ Δ) (hx : x ∈ e.baseSet) :
    (hD.holonomyDiffeotopy hf hfp he he_symm hΔ hx).final =
      hD.parallelTransportInDiffeomorph e e (fun t ↦ Δ (1, t)) 0 1 le_top (hf.of_le (by simp))
        hfp ((hΔ.contMDiff_slice _).of_le (by simp)) he
        he_symm he he_symm ((hΔ.apply_seam 1).symm ▸ hx) ((hΔ.apply_seam_one 1).symm ▸ hx) := by
  rw [Diffeotopy.final_def, timeSlice_holonomyDiffeotopy]
  rfl

/-- **The holonomy diffeotopy of a symplectic connection is symplectic.** For a symplectic smooth
Ehresmann connection on a proper map with a smooth atlas `A`, every slice of the holonomy
diffeotopy of a disc, read in a chart of `A` whose base set contains the centre of the disc,
preserves `σ`. -/
theorem timeSlice_holonomyDiffeotopy_mem_diffeomorphStabilizer {A : MapFiber.Atlas F proj}
    {σ : SmoothTwoForm IF F} (h : hD.IsSymplectic A σ) (hA : A.IsContMDiff ∞ IB IF IM) {b : B}
    (hΔ : IsSmoothDisc IB γ Δ) (hx : x ∈ (A.trivAt b).baseSet) (s : unitInterval) :
    (hD.holonomyDiffeotopy hA.contMDiff_proj hfp (hA.contMDiffOn_trivAt b)
        (hA.contMDiffOn_trivAt_symm b) hΔ hx).timeSlice s ∈
      SmoothForm.diffeomorphStabilizer σ := by
  rw [timeSlice_holonomyDiffeotopy]
  exact h.parallelTransportInDiffeomorph_mem_diffeomorphStabilizer hfp hA
    (hΔ.contMDiff_slice _) _ _

end HolonomyDiffeotopy

end IsEhresmannConnection

end TauCeti

end
