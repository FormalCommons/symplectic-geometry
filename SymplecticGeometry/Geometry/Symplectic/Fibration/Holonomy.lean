/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Fibration.Connection
public import SymplecticGeometry.Geometry.Symplectic.Fibration.HorizontalDistribution
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Disc
public import TauCeti.Geometry.Symplectic.Flux.Hamiltonian
import SymplecticGeometry.Analysis.Complex.Circle
import SymplecticGeometry.Geometry.Diffeomorphism.Diffeotopy.OfContMDiff
import SymplecticGeometry.Geometry.Manifold.MFDeriv.UniqueDifferential
import TauCeti.Geometry.Manifold.ContMDiff.Prod
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Calculus.Deriv.Prod
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
curves (`TauCeti.IsEhresmannConnection.contMDiffOn_parallelTransportIn_param`). It ends at the
holonomy of the boundary loop of the disc, and for a symplectic connection all its slices
preserve `σ`.

The variation of this diffeotopy in `s` is computed on the cylinders swept out by transport:
for a loop `c` in the model fibre, the point `C (s, t, θ)` is the transport along
`t ↦ Δ (s, t)` from `0` to `t` of the point with coordinates `(Δ (s, 0), c θ)` in `e`
(`TauCeti.IsEhresmannConnection.transportedCylinder`). Starting at `Δ (s, 0)` rather than at the
centre `x` makes `C` smooth on an open set of parameters that contains `[0, 1] × ℝ × ℝ`, so
that its derivative in `s` is an ordinary one even at `s = 0` and `s = 1`; for `s ∈ [0, 1]`
the two starting points agree. Smoothness in the time `t` comes from the smoothness of
transport in a family of curves and in its final time
(`TauCeti.IsEhresmannConnection.contMDiffOn_parallelTransport_param_endTime`).

At `t = 1`, the cylinder is read through the holonomy diffeotopy `Φ`: for `s ∈ [0, 1]`,
`C (s, 1, θ) = e⁻¹ (x, Φ (s, c θ))`. Its derivative in `s` is an ordinary one, while the velocity
`X_s` of `Φ` is a derivative on `[0, 1]`, one-sided at the ends. The two are compared through the
fibre coordinate `r ↦ (e (C (r, 1, θ))).2`, a curve on `ℝ` that extends `r ↦ Φ (r, c θ)` and is
differentiable at every `s ∈ [0, 1]`, so that its derivative there is `X_s`
(`TauCeti.Diffeotopy.velocity_apply_eq_mfderiv`); two maps differentiable at `s` that agree on
`[0, 1]` have the same derivative there, as in the proof that the cylinder does not move in `s` at
`t = 0`.

## Main definitions

* `SymplecticGeometry.BoundsSmoothDisc IB γ`: the loop `γ` bounds a smooth disc.
* `SymplecticGeometry.BoundsSmoothDisc.path`: such a loop, as a based loop `Path (γ 0) (γ 0)`.
* `TauCeti.IsEhresmannConnection.HasHamiltonianDiscHolonomy hD A σ`: the holonomy of `D` around
  every loop that bounds a smooth disc, read in every chart of `A` at its base point, is a
  Hamiltonian diffeomorphism of `σ`.
* `TauCeti.IsEhresmannConnection.holonomyDiffeotopy`: the diffeotopy of the model fibre whose
  slice at `s` is the holonomy, read in a chart, of the loop `t ↦ Δ (s, t)` of a smooth disc.
* `TauCeti.IsEhresmannConnection.transportedCylinder`: the cylinder `C (s, t, θ)` swept out by
  transporting a loop of the fibre over `Δ (s, 0)` along the curves `t ↦ Δ (s, t)`.

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
* `IsSymplectic.timeSlice_holonomyDiffeotopy_mem_diffeomorphStabilizer`, in the namespace
  `TauCeti.IsEhresmannConnection`: for a symplectic connection, every slice of the holonomy
  diffeotopy preserves `σ`.
* `TauCeti.IsEhresmannConnection.contMDiffOn_transportedCylinder`,
  `TauCeti.IsEhresmannConnection.transportedCylinder_add_one`: the transported cylinder is smooth
  where it starts in the base set of the chart, and `1`-periodic in `θ` for a periodic loop.
* `TauCeti.IsEhresmannConnection.transportedCylinder_zero_of_isSmoothDisc`,
  `TauCeti.IsEhresmannConnection.mfderiv_transportedCylinder_zero_apply`: for a smooth disc and
  `s ∈ [0, 1]`, the cylinder starts at `e.symm (x, c θ)` and does not move in `s` at `t = 0`.
* `TauCeti.IsEhresmannConnection.mfderiv_transportedCylinder_apply_mem`,
  `TauCeti.IsEhresmannConnection.mfderiv_transportedCylinder_apply_mem_ker`: the derivative of the
  cylinder in `t` is horizontal, since its curves in `t` are horizontal lifts, and its derivative
  in `θ` is vertical, since its curves in `θ` stay in one fibre.
* `TauCeti.IsEhresmannConnection.val_mfderiv_transportedCylinder_eq_zero`,
  `TauCeti.IsEhresmannConnection.val_mfderiv_transportedCylinder_slice_eq_zero`: hence a two-form
  whose horizontal spaces are `D` vanishes on these two derivatives, and the integrand of the
  area of each slice `(t, θ) ↦ C (s, t, θ)` for that form is zero.
* `TauCeti.IsEhresmannConnection.transportedCylinder_one_of_isSmoothDisc`,
  `TauCeti.IsEhresmannConnection.apply_transportedCylinder_one`: for `s ∈ [0, 1]`, the cylinder
  ends at the point with coordinates `(x, Φ (s, c θ))` in `e`, where `Φ` is the holonomy
  diffeotopy.
* `TauCeti.IsEhresmannConnection.mfderiv_transportedCylinder_one_apply`: at `t = 1` the
  derivative of the cylinder in `s` is the image under `d(e⁻¹)` of `(0, X_s)`, with `X_s` the
  velocity of `Φ`, for every `s ∈ [0, 1]`, ends included.
* `TauCeti.IsEhresmannConnection.apply_mfderiv_transportedCylinder_one_of_restrictsTo`: for a form
  `τ` that restricts to `σ` along an atlas containing `e`, its value at `t = 1` on the derivatives
  of the cylinder in `s` and `θ` is `σ (X_s, ∂_θ Φ (s, c θ))`, the integrand of the line
  integral of `ι_{X_s} σ` along the curve `θ ↦ Φ (s, c θ)`.

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

/-- Each loop `t ↦ Δ (s, t)` of a smooth disc `Δ` is smooth. -/
theorem _root_.TauCeti.IsSmoothDisc.contMDiff_slice {x : B} {γ : Path x x} {Δ : ℝ × ℝ → B}
    (hΔ : TauCeti.IsSmoothDisc IB γ Δ) (s : ℝ) : ContMDiff 𝓘(ℝ, ℝ) IB ∞ fun t ↦ Δ (s, t) :=
  hΔ.contMDiff.comp (contDiff_const.prodMk contDiff_id).contMDiff

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
  have hΔc : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) IB ((⊤ : ℕ∞) + 1) Δ :=
    contMDiff_prod_modelWithCornersSelf_iff.2 (hΔ.contMDiff.of_le (by simp))
  have hT := hD.contMDiffOn_parallelTransportIn_param le_top (hf.of_le (by simp)) hfp
    isOpen_univ hΔc.contMDiffOn he_symm he 0 1
  exact hT.comp_contMDiff ((contMDiff_subtypeVal_Icc.comp contMDiff_fst).prodMk contMDiff_snd)
    fun p ↦ ⟨mem_univ _, (hΔ.apply_seam p.1).symm ▸ hx, (hΔ.apply_seam_one p.1).symm ▸ hx⟩

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
  simp only [Set.Icc.coe_one]

/-- **The holonomy diffeotopy of a symplectic connection is symplectic.** For a symplectic smooth
Ehresmann connection on a proper map with a smooth atlas `A`, every slice of the holonomy
diffeotopy of a disc, read in a chart of `A` whose base set contains the centre of the disc,
preserves `σ`. -/
theorem IsSymplectic.timeSlice_holonomyDiffeotopy_mem_diffeomorphStabilizer
    {A : MapFiber.Atlas F proj} {σ : SmoothTwoForm IF F} (h : hD.IsSymplectic A σ)
    (hfp : IsProperMap proj) (hA : A.IsContMDiff ∞ IB IF IM) {b : B}
    (hΔ : IsSmoothDisc IB γ Δ) (hx : x ∈ (A.trivAt b).baseSet) (s : unitInterval) :
    (hD.holonomyDiffeotopy hA.contMDiff_proj hfp (hA.contMDiffOn_trivAt b)
        (hA.contMDiffOn_trivAt_symm b) hΔ hx).timeSlice s ∈
      SmoothForm.diffeomorphStabilizer σ := by
  rw [timeSlice_holonomyDiffeotopy]
  exact h.parallelTransportInDiffeomorph_mem_diffeomorphStabilizer hfp hA
    (hΔ.contMDiff_slice _) _ _

end HolonomyDiffeotopy

section TransportedCylinder

variable {e : Trivialization F proj} {x : B} {γ : Path x x} {Δ : ℝ × ℝ → B} {c : ℝ → F}

/-- **The transported cylinder of a family of curves.** For a family of curves `t ↦ Δ (s, t)` in
`B`, a trivialization `e` of `proj` with fibre `F` and a map `c : ℝ → F`, the point
`hD.transportedCylinder e Δ c (s, t, θ)` is the transport along `t ↦ Δ (s, t)`, from time `0` to
time `t`, of the point with coordinates `(Δ (s, 0), c θ)` in `e`. For a smooth disc `Δ` with
centre `x` and `s ∈ [0, 1]`, it starts at `e.symm (x, c θ)`. -/
def transportedCylinder (hD : IsEhresmannConnection IM IB n proj D) (e : Trivialization F proj)
    (Δ : ℝ × ℝ → B) (c : ℝ → F) (p : ℝ × ℝ × ℝ) : M :=
  hD.parallelTransport (fun t ↦ Δ (p.1, t)) 0 p.2.1
    (e.toOpenPartialHomeomorph.symm (Δ (p.1, 0), c p.2.2))

omit [FiniteDimensional ℝ EM] [IM.Boundaryless] [T2Space M] [FiniteDimensional ℝ EB]
  [IsManifold IB ∞ B] [IB.Boundaryless] [T2Space B] in
theorem transportedCylinder_def (p : ℝ × ℝ × ℝ) :
    hD.transportedCylinder e Δ c p = hD.parallelTransport (fun t ↦ Δ (p.1, t)) 0 p.2.1
      (e.toOpenPartialHomeomorph.symm (Δ (p.1, 0), c p.2.2)) :=
  (rfl)

omit [FiniteDimensional ℝ EM] [IM.Boundaryless] [T2Space M] [FiniteDimensional ℝ EB]
  [IsManifold IB ∞ B] [IB.Boundaryless] [T2Space B] in
/-- At `t = 0` the transported cylinder is the point with coordinates `(Δ (s, 0), c θ)` in
`e`. -/
@[simp]
theorem transportedCylinder_zero (s θ : ℝ) :
    hD.transportedCylinder e Δ c (s, 0, θ) = e.toOpenPartialHomeomorph.symm (Δ (s, 0), c θ) := by
  rw [transportedCylinder_def, parallelTransport_self]

omit [FiniteDimensional ℝ EM] [IM.Boundaryless] [T2Space M] [FiniteDimensional ℝ EB]
  [IsManifold IB ∞ B] [IB.Boundaryless] [T2Space B] in
/-- The transported cylinder of a `1`-periodic map `c` is `1`-periodic in `θ`. -/
theorem transportedCylinder_add_one (hc : Periodic c 1) (s t θ : ℝ) :
    hD.transportedCylinder e Δ c (s, t, θ + 1) = hD.transportedCylinder e Δ c (s, t, θ) := by
  simp only [transportedCylinder_def, hc θ]

omit [FiniteDimensional ℝ EM] [IM.Boundaryless] [T2Space M] [FiniteDimensional ℝ EB]
  [IsManifold IB ∞ B] [IB.Boundaryless] [T2Space B] in
/-- For a smooth disc `Δ` with centre `x` and `s ∈ [0, 1]`, the transported cylinder starts at
`e.symm (x, c θ)`. -/
theorem transportedCylinder_zero_of_isSmoothDisc (hΔ : IsSmoothDisc IB γ Δ) (s : unitInterval)
    (θ : ℝ) :
    hD.transportedCylinder e Δ c (s, 0, θ) = e.toOpenPartialHomeomorph.symm (x, c θ) := by
  rw [transportedCylinder_zero, hΔ.apply_seam]

omit [FiniteDimensional ℝ EM] [IM.Boundaryless] [T2Space M] [FiniteDimensional ℝ EB]
  [IsManifold IB ∞ B] [IB.Boundaryless] [T2Space B] in
/-- **The transported cylinder does not move in `s` at `t = 0`.** For a smooth disc `Δ` and
`s ∈ [0, 1]`, the derivative of the transported cylinder at `(s, 0, θ)` in the direction of `s`
vanishes. -/
theorem mfderiv_transportedCylinder_zero_apply (hΔ : IsSmoothDisc IB γ Δ) {s : ℝ}
    (hs : s ∈ Icc 0 1) (θ : ℝ) :
    mfderiv 𝓘(ℝ, ℝ × ℝ × ℝ) IM (hD.transportedCylinder e Δ c) (s, 0, θ) (1, 0, 0) = 0 := by
  by_cases hC : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ × ℝ) IM (hD.transportedCylinder e Δ c) (s, 0, θ)
  swap
  · rw [mfderiv_zero_of_not_mdifferentiableAt hC]
    -- `rw [zero_apply]` misses the pattern: the argument is typed as a tangent vector.
    exact zero_apply _
  -- The line `r ↦ (r, 0, θ)` and its derivative.
  have hι : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) (fun r : ℝ ↦ (r, (0 : ℝ), θ)) s
      (ContinuousLinearMap.inl ℝ ℝ (ℝ × ℝ)) :=
    hasMFDerivAt_iff_hasFDerivAt.2 (hasFDerivAt_prodMk_left s ((0 : ℝ), θ))
  have h₁ := hC.hasMFDerivAt.comp s hι
  -- Along the line, the cylinder is constant on `[0, 1]`.
  have h₂ : HasMFDerivWithinAt 𝓘(ℝ, ℝ) IM
      (hD.transportedCylinder e Δ c ∘ fun r : ℝ ↦ (r, (0 : ℝ), θ)) (Icc 0 1) s 0 :=
    (hasMFDerivWithinAt_const (e.toOpenPartialHomeomorph.symm (x, c θ)) _ _).congr_mono
      (fun r hr ↦ transportedCylinder_zero_of_isSmoothDisc hΔ ⟨r, hr⟩ θ)
      (transportedCylinder_zero_of_isSmoothDisc hΔ ⟨s, hs⟩ θ) subset_rfl
  have h := (uniqueMDiffWithinAt_iff_uniqueDiffWithinAt.2
    (uniqueDiffOn_Icc zero_lt_one s hs)).eq h₁.hasMFDerivWithinAt h₂
  -- The value of `(mfderiv C p).comp inl` at `1` is that of `mfderiv C p` at `(1, 0, 0)`.
  exact DFunLike.congr_fun h 1

omit [IsManifold IF ∞ F] in
/-- **The transported cylinder is smooth.** Let `D` be a smooth Ehresmann connection on a proper
smooth map `proj`, `Δ : ℝ × ℝ → B` smooth, `e` a trivialization of `proj` with a smooth inverse,
and `c : ℝ → F` smooth. The transported cylinder is smooth in `(s, t, θ)` on the set of the
parameters with `Δ (s, 0) ∈ e.baseSet`. -/
theorem contMDiffOn_transportedCylinder (hD : IsEhresmannConnection IM IB ∞ proj D)
    (hf : ContMDiff IM IB ∞ proj) (hfp : IsProperMap proj)
    (he_symm : ContMDiffOn (IB.prod IF) IM ∞ e.toOpenPartialHomeomorph.symm e.target)
    (hΔ : ContMDiff 𝓘(ℝ, ℝ × ℝ) IB ∞ Δ) (hc : ContMDiff 𝓘(ℝ, ℝ) IF ∞ c) :
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ × ℝ) IM ∞ (hD.transportedCylinder e Δ c)
      {p | Δ (p.1, 0) ∈ e.baseSet} := by
  have hT := hD.contMDiffOn_parallelTransport_param_endTime le_top (hf.of_le (by simp)) hfp
    ((contMDiff_prod_modelWithCornersSelf_iff.2 hΔ).of_le (by simp)) 0
  -- The parameters `(s, t)` and the point where the transport starts.
  have hv : ContMDiff 𝓘(ℝ, ℝ × ℝ × ℝ) (IB.prod IF) ∞
      fun p : ℝ × ℝ × ℝ ↦ (Δ (p.1, 0), c p.2.2) :=
    (hΔ.comp (by fun_prop : ContDiff ℝ ∞ fun p : ℝ × ℝ × ℝ ↦ (p.1, (0 : ℝ))).contMDiff).prodMk
      (hc.comp (by fun_prop : ContDiff ℝ ∞ fun p : ℝ × ℝ × ℝ ↦ p.2.2).contMDiff)
  have hg : ContMDiffOn 𝓘(ℝ, ℝ × ℝ × ℝ) ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod IM) ∞
      (fun p : ℝ × ℝ × ℝ ↦ ((p.1, p.2.1), e.toOpenPartialHomeomorph.symm (Δ (p.1, 0), c p.2.2)))
      {p | Δ (p.1, 0) ∈ e.baseSet} :=
    ((contDiff_fst.contMDiff.prodMk (contDiff_snd.fst).contMDiff).contMDiffOn).prodMk
      (he_symm.comp hv.contMDiffOn fun _ hp ↦ e.mem_target.2 hp)
  exact (hT.comp hg fun p hp ↦ e.proj_symm_apply' hp).congr fun p _ ↦ transportedCylinder_def p

omit [IsManifold IF ∞ F] in
/-- For a smooth disc `Δ` with centre `x` and a trivialization `e` whose base set contains `x`,
the transported cylinder is smooth at every `(s, t, θ)` with `s ∈ [0, 1]`. -/
theorem contMDiffAt_transportedCylinder (hD : IsEhresmannConnection IM IB ∞ proj D)
    (hf : ContMDiff IM IB ∞ proj) (hfp : IsProperMap proj)
    (he_symm : ContMDiffOn (IB.prod IF) IM ∞ e.toOpenPartialHomeomorph.symm e.target)
    (hΔ : IsSmoothDisc IB γ Δ) (hx : x ∈ e.baseSet) (hc : ContMDiff 𝓘(ℝ, ℝ) IF ∞ c)
    {p : ℝ × ℝ × ℝ} (hp : p.1 ∈ Icc 0 1) :
    ContMDiffAt 𝓘(ℝ, ℝ × ℝ × ℝ) IM ∞ (hD.transportedCylinder e Δ c) p := by
  refine (hD.contMDiffOn_transportedCylinder hf hfp he_symm hΔ.contMDiff hc).contMDiffAt
    (IsOpen.mem_nhds (e.open_baseSet.preimage ?_) ?_)
  · exact hΔ.contMDiff.continuous.comp (by fun_prop)
  · exact (congrArg (· ∈ e.baseSet) (hΔ.apply_seam ⟨p.1, hp⟩)).mpr hx

/-! ### Horizontal and vertical derivatives -/

/-- For a `C^n` connection, `1 ≤ n`, on a proper `C^(n+1)` map, a `C^(n+1)` family `Δ` and an `s`
with `Δ (s, 0)` in the base set of `e`, each curve `t ↦ C (s, t, θ)` of the transported cylinder
is horizontal, as the transport of `e.symm (Δ (s, 0), c θ)` along `t ↦ Δ (s, t)`. -/
theorem isHorizontalMap_transportedCylinder (hn : 1 ≤ n) (hf : ContMDiff IM IB (n + 1) proj)
    (hfp : IsProperMap proj) (hΔ : ContMDiff 𝓘(ℝ, ℝ × ℝ) IB (n + 1) Δ) {s : ℝ}
    (hs : Δ (s, 0) ∈ e.baseSet) (θ : ℝ) :
    IsHorizontalMap 𝓘(ℝ, ℝ) D fun t ↦ hD.transportedCylinder e Δ c (s, t, θ) := by
  simp only [transportedCylinder_def]
  exact hD.isHorizontalMap_parallelTransport hn hf hfp
    (hΔ.comp (contDiff_const.prodMk contDiff_id).contMDiff) (e.proj_symm_apply' hs)

/-- For a `C^n` connection, `1 ≤ n`, on a proper `C^(n+1)` map and a `C^(n+1)` family `Δ`, the
transported cylinder at `(s, t, θ)` lies over `Δ (s, t)` when `Δ (s, 0)` is in the base set of
`e`. -/
theorem proj_transportedCylinder (hn : 1 ≤ n) (hf : ContMDiff IM IB (n + 1) proj)
    (hfp : IsProperMap proj) (hΔ : ContMDiff 𝓘(ℝ, ℝ × ℝ) IB (n + 1) Δ) {s : ℝ}
    (hs : Δ (s, 0) ∈ e.baseSet) (t θ : ℝ) :
    proj (hD.transportedCylinder e Δ c (s, t, θ)) = Δ (s, t) := by
  rw [transportedCylinder_def]
  exact hD.apply_parallelTransport hn hf hfp (hΔ.comp (contDiff_const.prodMk contDiff_id).contMDiff)
    (e.proj_symm_apply' hs) t

/-- **The derivative of the transported cylinder in `t` is horizontal.** For a `C^n` connection
`D`, `1 ≤ n`, on a proper `C^(n+1)` map and a `C^(n+1)` family `Δ`, the derivative of the
transported cylinder at `p` in the direction of `t` lies in `D` at `C p`, when `Δ (p.1, 0)` is in
the base set of `e`. -/
theorem mfderiv_transportedCylinder_apply_mem (hn : 1 ≤ n) (hf : ContMDiff IM IB (n + 1) proj)
    (hfp : IsProperMap proj) (hΔ : ContMDiff 𝓘(ℝ, ℝ × ℝ) IB (n + 1) Δ) {p : ℝ × ℝ × ℝ}
    (hp : Δ (p.1, 0) ∈ e.baseSet) :
    mfderiv 𝓘(ℝ, ℝ × ℝ × ℝ) IM (hD.transportedCylinder e Δ c) p (0, 1, 0) ∈
      D (hD.transportedCylinder e Δ c p) := by
  by_cases hC : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ × ℝ) IM (hD.transportedCylinder e Δ c) p
  swap
  · rw [mfderiv_zero_of_not_mdifferentiableAt hC]
    exact (D _).zero_mem
  obtain ⟨s, t, θ⟩ := p
  rw [← hC.curveVelocity_comp_mfderiv (g := fun r : ℝ ↦ (s, r, θ))
    (HasDerivAt.prodMk (hasDerivAt_const t s)
      (HasDerivAt.prodMk (hasDerivAt_id t) (hasDerivAt_const t θ))),
    Manifold.curveVelocity_apply]
  exact (hD.isHorizontalMap_transportedCylinder hn hf hfp hΔ hp θ).mfderiv_mem t 1

/-- **The derivative of the transported cylinder in `θ` is vertical.** For a `C^n` connection,
`1 ≤ n`, on a proper `C^(n+1)` map and a `C^(n+1)` family `Δ`, the derivative of the transported
cylinder at `p` in the direction of `θ` is in the kernel of the derivative of `proj`, when
`Δ (p.1, 0)` is in the base set of `e`: the curve `θ ↦ C (s, t, θ)` stays in the fibre over
`Δ (s, t)`. -/
theorem mfderiv_transportedCylinder_apply_mem_ker (hn : 1 ≤ n)
    (hf : ContMDiff IM IB (n + 1) proj) (hfp : IsProperMap proj)
    (hΔ : ContMDiff 𝓘(ℝ, ℝ × ℝ) IB (n + 1) Δ) {p : ℝ × ℝ × ℝ} (hp : Δ (p.1, 0) ∈ e.baseSet) :
    mfderiv 𝓘(ℝ, ℝ × ℝ × ℝ) IM (hD.transportedCylinder e Δ c) p (0, 0, 1) ∈
      (mfderiv IM IB proj (hD.transportedCylinder e Δ c p)).ker := by
  obtain ⟨s, t, θ⟩ := p
  by_cases hC : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ × ℝ) IM (hD.transportedCylinder e Δ c) (s, t, θ)
  swap
  · rw [mfderiv_zero_of_not_mdifferentiableAt hC]
    exact (LinearMap.ker _).zero_mem
  have hproj : MDifferentiableAt IM IB proj (hD.transportedCylinder e Δ c (s, t, θ)) :=
    (hf.mdifferentiable (by simp)).mdifferentiableAt
  -- Along the line through `(s, t, θ)` in the direction of `θ`, the projection of the cylinder
  -- is constant.
  have h := mfderiv_apply_eq_zero_of_const_line (I := IB)
    (f := proj ∘ hD.transportedCylinder e Δ c)
    (z := (s, t, θ)) (w := (0, 0, 1)) fun r ↦ by
      have hr : (s, t, θ) + r • ((0 : ℝ), (0 : ℝ), (1 : ℝ)) = (s, t, θ + r) := by
        ext <;> simp
      rw [hr, comp_apply, comp_apply, hD.proj_transportedCylinder hn hf hfp hΔ hp,
        hD.proj_transportedCylinder hn hf hfp hΔ hp]
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
  -- `h` applies the derivative to `(0, 0, 1)` as a vector of `ℝ × ℝ × ℝ`, and the chain rule to a
  -- tangent vector, so `rw` does not match them.
  exact (mfderiv_comp_apply (s, t, θ) hproj hC _).symm.trans h

/-- **A two-form defining the connection vanishes on the derivatives of the transported cylinder
in `t` and in `θ`.** Let `τ` be a two-form on `M` whose horizontal spaces form the connection
`D` of a proper `C^(n+1)` map, `1 ≤ n`, and `Δ` a `C^(n+1)` family. At every `p` with
`Δ (p.1, 0)` in the base set of `e`, `τ` pairs the derivative of the transported cylinder in `t`
with its derivative in `θ` to zero. -/
theorem val_mfderiv_transportedCylinder_eq_zero {τ : SmoothTwoForm IM M}
    (hτ : SmoothTwoForm.horizontalDistribution IB proj τ = D) (hn : 1 ≤ n)
    (hf : ContMDiff IM IB (n + 1) proj) (hfp : IsProperMap proj)
    (hΔ : ContMDiff 𝓘(ℝ, ℝ × ℝ) IB (n + 1) Δ) {p : ℝ × ℝ × ℝ} (hp : Δ (p.1, 0) ∈ e.baseSet) :
    τ.val (hD.transportedCylinder e Δ c p)
      ![mfderiv 𝓘(ℝ, ℝ × ℝ × ℝ) IM (hD.transportedCylinder e Δ c) p (0, 1, 0),
        mfderiv 𝓘(ℝ, ℝ × ℝ × ℝ) IM (hD.transportedCylinder e Δ c) p (0, 0, 1)] = 0 :=
  SmoothTwoForm.val_eq_zero_of_mem_horizontalDistribution_of_mem_ker
    (hτ ▸ hD.mfderiv_transportedCylinder_apply_mem hn hf hfp hΔ hp)
    (hD.mfderiv_transportedCylinder_apply_mem_ker hn hf hfp hΔ hp)

/-- **The area integrand of each slice of the transported cylinder vanishes.** Let `τ` be a
two-form on `M` whose horizontal spaces form the connection `D` of a proper `C^(n+1)` map,
`1 ≤ n`, and `Δ` a `C^(n+1)` family with `Δ (s, 0)` in the base set of `e`. For the slice
`u (t, θ) = C (s, t, θ)` of the transported cylinder, the integrand
`τ (u q) (∂₁u q, ∂₂u q)` of its `τ`-area vanishes at every `q`. -/
theorem val_mfderiv_transportedCylinder_slice_eq_zero {τ : SmoothTwoForm IM M}
    (hτ : SmoothTwoForm.horizontalDistribution IB proj τ = D) (hn : 1 ≤ n)
    (hf : ContMDiff IM IB (n + 1) proj) (hfp : IsProperMap proj)
    (hΔ : ContMDiff 𝓘(ℝ, ℝ × ℝ) IB (n + 1) Δ) {s : ℝ} (hs : Δ (s, 0) ∈ e.baseSet)
    (q : ℝ × ℝ) :
    τ.val (hD.transportedCylinder e Δ c (s, q))
      ![mfderiv 𝓘(ℝ, ℝ × ℝ) IM (fun q' ↦ hD.transportedCylinder e Δ c (s, q')) q (1, 0),
        mfderiv 𝓘(ℝ, ℝ × ℝ) IM (fun q' ↦ hD.transportedCylinder e Δ c (s, q')) q (0, 1)] = 0 := by
  subst hτ
  obtain ⟨t, θ⟩ := q
  by_cases hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) IM
    (fun q' ↦ hD.transportedCylinder e Δ c (s, q')) (t, θ)
  swap
  · rw [mfderiv_zero_of_not_mdifferentiableAt hu]
    exact SmoothTwoForm.val_eq_zero_of_mem_horizontalDistribution_of_mem_ker
      (IB := IB) (proj := proj) (Submodule.zero_mem _) (LinearMap.ker _).zero_mem
  refine SmoothTwoForm.val_eq_zero_of_mem_horizontalDistribution_of_mem_ker (IB := IB)
    (proj := proj) ?_ ?_
  · rw [← hu.curveVelocity_comp_mfderiv (g := fun r : ℝ ↦ (r, θ))
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t θ)), Manifold.curveVelocity_apply]
    exact (hD.isHorizontalMap_transportedCylinder hn hf hfp hΔ hs θ).mfderiv_mem t 1
  · have hproj : MDifferentiableAt IM IB proj (hD.transportedCylinder e Δ c (s, t, θ)) :=
      (hf.mdifferentiable (by simp)).mdifferentiableAt
    -- Along the line through `(t, θ)` in the direction of `θ`, the projection of the slice is
    -- constant.
    have h := mfderiv_apply_eq_zero_of_const_line (I := IB)
      (f := proj ∘ fun q' ↦ hD.transportedCylinder e Δ c (s, q'))
      (z := (t, θ)) (w := (0, 1)) fun r ↦ by
        have hr : (t, θ) + r • ((0 : ℝ), (1 : ℝ)) = (t, θ + r) := by
          ext <;> simp
        rw [hr, comp_apply, comp_apply, hD.proj_transportedCylinder hn hf hfp hΔ hs,
          hD.proj_transportedCylinder hn hf hfp hΔ hs]
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
    -- As in `mfderiv_transportedCylinder_apply_mem_ker`, `h` and the chain rule type `(0, 1)`
    -- differently, so `rw` does not match them.
    exact (mfderiv_comp_apply (t, θ) hproj hu _).symm.trans h

end TransportedCylinder

section HolonomyCylinder

variable [CompleteSpace EF] [BoundarylessManifold IF F]
  {e : Trivialization F proj} {x : B} {γ : Path x x} {Δ : ℝ × ℝ → B} {c : ℝ → F}
  {hD : IsEhresmannConnection IM IB ∞ proj D}

/-- **The transported cylinder at `t = 1`.** For a smooth disc `Δ` with centre `x`, a
trivialization `e` whose base set contains `x`, and `s ∈ [0, 1]`, the transported cylinder at
`(s, 1, θ)` is the point with coordinates `(x, Φ (s, c θ))` in `e`, where `Φ` is the holonomy
diffeotopy of `Δ` read in `e`. -/
theorem transportedCylinder_one_of_isSmoothDisc (hf : ContMDiff IM IB ∞ proj)
    (hfp : IsProperMap proj) (he : ContMDiffOn IM (IB.prod IF) ∞ e e.source)
    (he_symm : ContMDiffOn (IB.prod IF) IM ∞ e.toOpenPartialHomeomorph.symm e.target)
    (hΔ : IsSmoothDisc IB γ Δ) (hx : x ∈ e.baseSet) (s : unitInterval) (θ : ℝ) :
    hD.transportedCylinder e Δ c (s, 1, θ) = e.toOpenPartialHomeomorph.symm
      (x, hD.holonomyDiffeotopy hf hfp he he_symm hΔ hx (s, c θ)) := by
  have h₀ : Δ ((s : ℝ), 0) ∈ e.baseSet := (hΔ.apply_seam s).symm ▸ hx
  have h₁ : Δ ((s : ℝ), 1) ∈ e.baseSet := (hΔ.apply_seam_one s).symm ▸ hx
  have h := hD.fiberInclusionMap_parallelTransportIn le_top (hf.of_le (by simp)) hfp
    ((hΔ.contMDiff_slice s).of_le (by simp)) h₀ h₁ (c θ)
  rw [holonomyDiffeotopy_apply, transportedCylinder_def, ← e.fiberInclusionMap_apply h₀, ← h,
    e.fiberInclusionMap_apply, hΔ.apply_seam_one]

/-- For a smooth disc `Δ` with centre `x` and `s ∈ [0, 1]`, the trivialization `e` sends the
transported cylinder at `(s, 1, θ)` to `(x, Φ (s, c θ))`, where `Φ` is the holonomy diffeotopy
of `Δ` read in `e`. -/
theorem apply_transportedCylinder_one (hf : ContMDiff IM IB ∞ proj)
    (hfp : IsProperMap proj) (he : ContMDiffOn IM (IB.prod IF) ∞ e e.source)
    (he_symm : ContMDiffOn (IB.prod IF) IM ∞ e.toOpenPartialHomeomorph.symm e.target)
    (hΔ : IsSmoothDisc IB γ Δ) (hx : x ∈ e.baseSet) (s : unitInterval) (θ : ℝ) :
    e (hD.transportedCylinder e Δ c (s, 1, θ)) =
      (x, hD.holonomyDiffeotopy hf hfp he he_symm hΔ hx (s, c θ)) := by
  rw [transportedCylinder_one_of_isSmoothDisc hf hfp he he_symm hΔ hx, e.apply_symm_apply' hx]

/-- **The derivative in `s` of the transported cylinder at `t = 1`.** Let `Δ` be a smooth disc
with centre `x`, `e` a trivialization, smooth with a smooth inverse, whose base set contains `x`,
`c` a smooth map, and `Φ` the holonomy diffeotopy of `Δ` read in `e`. For `s ∈ [0, 1]`, ends
included, the derivative of the transported cylinder at `(s, 1, θ)` in the direction of `s` is the
image, under the derivative of `e⁻¹` at `(x, Φ (s, c θ))`, of `(0, X_s (Φ (s, c θ)))`, where
`X_s` is the velocity of `Φ`. -/
theorem mfderiv_transportedCylinder_one_apply (hf : ContMDiff IM IB ∞ proj)
    (hfp : IsProperMap proj) (he : ContMDiffOn IM (IB.prod IF) ∞ e e.source)
    (he_symm : ContMDiffOn (IB.prod IF) IM ∞ e.toOpenPartialHomeomorph.symm e.target)
    (hΔ : IsSmoothDisc IB γ Δ) (hx : x ∈ e.baseSet)
    (hc : ContMDiff 𝓘(ℝ, ℝ) IF ∞ c) (s : unitInterval) (θ : ℝ) :
    mfderiv 𝓘(ℝ, ℝ × ℝ × ℝ) IM (hD.transportedCylinder e Δ c) ((s : ℝ), 1, θ) (1, 0, 0) =
      mfderiv (IB.prod IF) IM e.toOpenPartialHomeomorph.symm
        (x, hD.holonomyDiffeotopy hf hfp he he_symm hΔ hx (s, c θ))
        ((0 : EB), (hD.holonomyDiffeotopy hf hfp he he_symm hΔ hx).velocity s
          (hD.holonomyDiffeotopy hf hfp he he_symm hΔ hx (s, c θ))) := by
  set Φ := hD.holonomyDiffeotopy hf hfp he he_symm hΔ hx
  -- On `[0, 1]`, the slice `t = 1` of the cylinder is `r ↦ e⁻¹ (x, Φ (r, c θ))`.
  have hC1 (r : unitInterval) : hD.transportedCylinder e Δ c ((r : ℝ), 1, θ) =
      e.toOpenPartialHomeomorph.symm (x, Φ (r, c θ)) :=
    transportedCylinder_one_of_isSmoothDisc hf hfp he he_symm hΔ hx r θ
  obtain ⟨C, hC⟩ : ∃ C, C = hD.transportedCylinder e Δ c := ⟨_, rfl⟩
  rw [← hC]
  rw [← hC] at hC1
  have hCd : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ × ℝ) IM C ((s : ℝ), 1, θ) :=
    hC ▸ (hD.contMDiffAt_transportedCylinder hf hfp he_symm hΔ hx hc s.property).mdifferentiableAt
      (by simp)
  have hmem : C ((s : ℝ), 1, θ) ∈ e.source := by
    rw [hC1]
    exact e.toOpenPartialHomeomorph.map_target (e.mem_target.2 hx)
  have hed : MDifferentiableAt IM (IB.prod IF) e (C ((s : ℝ), 1, θ)) :=
    (he.contMDiffAt (e.open_source.mem_nhds hmem)).mdifferentiableAt (by simp)
  -- The line `r ↦ (r, 1, θ)` and its derivative.
  have hι : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) (fun r : ℝ ↦ (r, (1 : ℝ), θ)) s
      (ContinuousLinearMap.inl ℝ ℝ (ℝ × ℝ)) :=
    hasMFDerivAt_iff_hasFDerivAt.2 (hasFDerivAt_prodMk_left (s : ℝ) ((1 : ℝ), θ))
  -- The fibre coordinate of the cylinder along the line extends `r ↦ Φ (r, c θ)` past `[0, 1]`.
  obtain ⟨g, hgdef⟩ : ∃ g : ℝ → F, g = fun r ↦ (e (C (r, 1, θ))).2 := ⟨_, rfl⟩
  have hg : MDifferentiableAt 𝓘(ℝ, ℝ) IF g s := hgdef ▸
    mdifferentiableAt_snd.comp (s : ℝ) (hed.comp (s : ℝ) (hCd.comp (s : ℝ) hι.mdifferentiableAt))
  have hgΦ (r : unitInterval) : g r = Φ (r, c θ) := by
    rw [hgdef]; dsimp only; rw [hC1 r, e.apply_symm_apply' hx]
  have hX := Φ.velocity_apply_eq_mfderiv (by simp) hgΦ hg
  have hesd : MDifferentiableAt (IB.prod IF) IM e.toOpenPartialHomeomorph.symm (x, g s) :=
    (he_symm.contMDiffAt (e.open_target.mem_nhds (e.mem_target.2 hx))).mdifferentiableAt
      (by simp)
  have h₁ := (hCd.hasMFDerivAt.comp (s : ℝ) hι).mfderiv
  have h₂ := (hesd.hasMFDerivAt.comp (s : ℝ)
    ((hasMFDerivAt_const x (s : ℝ)).prodMk hg.hasMFDerivAt)).mfderiv
  -- Both maps are differentiable at `s` and agree on `[0, 1]`.
  have h := (uniqueMDiffWithinAt_iff_uniqueDiffWithinAt.2
    (uniqueDiffOn_Icc zero_lt_one s s.property)).mfderiv_eq_of_eqOn
    (f := C ∘ fun r : ℝ ↦ (r, (1 : ℝ), θ))
    (g := e.toOpenPartialHomeomorph.symm ∘ fun r ↦ (x, g r)) s.property
    (hCd.comp (s : ℝ) hι.mdifferentiableAt)
    (hesd.comp (s : ℝ) (mdifferentiableAt_const.prodMk hg))
    fun r hr ↦ by rw [comp_apply, comp_apply, hC1 ⟨r, hr⟩, ← hgΦ ⟨r, hr⟩]
  rw [h₁, h₂] at h
  refine (DFunLike.congr_fun h 1).trans ?_
  rw [hX, ← hgΦ]
  -- The tangent space of `B × F` at `(x, g s)` is `EB × EF` only by definition, so the composite
  -- and the pair are evaluated through `exact`, up to that unfolding.
  exact congrArg (mfderiv (IB.prod IF) IM e.toOpenPartialHomeomorph.symm (x, g s))
    (ContinuousLinearMap.prod_apply (R := ℝ) 0 (mfderiv 𝓘(ℝ, ℝ) IF g s) 1)

/-- **The coupling integrand on the edge `t = 1`.** Let `Δ` be a smooth disc with centre `x`,
`c` a smooth map, `e = A.trivAt b` a chart of an atlas `A`, smooth with a smooth inverse, whose
base set contains `x`, and `Φ` the holonomy diffeotopy of `Δ` read in `e`. If the two-form `τ`
restricts to `σ` along `A`, then for `s ∈ [0, 1]` the value of `τ` at the point `C (s, 1, θ)` of
the transported cylinder `C`, on the derivatives of `C` in `s` and in `θ`, is
`σ (X_s, ∂_θ Φ (s, c θ))` at `Φ (s, c θ)`, where `X_s` is the velocity of `Φ`: the integrand of
the line integral of the contraction of `σ` with `X_s` along the curve `θ ↦ Φ (s, c θ)`. -/
theorem apply_mfderiv_transportedCylinder_one_of_restrictsTo {A : MapFiber.Atlas F proj} {b : B}
    (hA : A.trivAt b = e) {σ : SmoothTwoForm IF F} {τ : SmoothTwoForm IM M}
    (hτ : A.RestrictsTo σ τ) (hf : ContMDiff IM IB ∞ proj)
    (hfp : IsProperMap proj) (he : ContMDiffOn IM (IB.prod IF) ∞ e e.source)
    (he_symm : ContMDiffOn (IB.prod IF) IM ∞ e.toOpenPartialHomeomorph.symm e.target)
    (hΔ : IsSmoothDisc IB γ Δ) (hx : x ∈ e.baseSet)
    (hc : ContMDiff 𝓘(ℝ, ℝ) IF ∞ c) (s : unitInterval) (θ : ℝ) :
    τ.val (hD.transportedCylinder e Δ c ((s : ℝ), 1, θ))
        ![mfderiv 𝓘(ℝ, ℝ × ℝ × ℝ) IM (hD.transportedCylinder e Δ c) ((s : ℝ), 1, θ) (1, 0, 0),
          mfderiv 𝓘(ℝ, ℝ × ℝ × ℝ) IM (hD.transportedCylinder e Δ c) ((s : ℝ), 1, θ) (0, 0, 1)] =
      σ.val (hD.holonomyDiffeotopy hf hfp he he_symm hΔ hx (s, c θ))
        ![(hD.holonomyDiffeotopy hf hfp he he_symm hΔ hx).velocity s
            (hD.holonomyDiffeotopy hf hfp he he_symm hΔ hx (s, c θ)),
          Manifold.curveVelocity IF
            (fun θ ↦ hD.holonomyDiffeotopy hf hfp he he_symm hΔ hx (s, c θ)) θ] := by
  subst hA
  set C := hD.transportedCylinder (A.trivAt b) Δ c
  set Φ := hD.holonomyDiffeotopy hf hfp he he_symm hΔ hx
  set ι := (A.trivAt b).fiberInclusionMap hx
  have hesd : MDifferentiableAt (IB.prod IF) IM (A.trivAt b).toOpenPartialHomeomorph.symm
      (x, Φ (s, c θ)) :=
    (he_symm.contMDiffAt ((A.trivAt b).open_target.mem_nhds
      ((A.trivAt b).mem_target.2 hx))).mdifferentiableAt (by simp)
  -- The loop `θ ↦ Φ (s, c θ)` and the slice `θ ↦ C (s, 1, θ)`, which is its image under `ι`.
  set φ : ℝ → F := fun θ ↦ Φ (s, c θ)
  have hφ : MDifferentiableAt 𝓘(ℝ, ℝ) IF φ θ :=
    ((Φ.contMDiff.comp (contMDiff_const.prodMk hc)).mdifferentiable (by simp)) θ
  have hCι : (fun θ' : ℝ ↦ C ((s : ℝ), 1, θ')) = ι ∘ φ := funext fun θ' ↦ by
    simp only [comp_apply, C, ι, φ, Φ, (A.trivAt b).fiberInclusionMap_apply,
      transportedCylinder_one_of_isSmoothDisc hf hfp he he_symm hΔ hx]
  have hιd : MDifferentiableAt IF IM ι (φ θ) :=
    ((A.trivAt b).contMDiff_fiberInclusionMap he_symm hx).mdifferentiableAt (by simp)
  have hCd : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ × ℝ) IM C ((s : ℝ), 1, θ) :=
    (hD.contMDiffAt_transportedCylinder hf hfp he_symm hΔ hx hc s.property).mdifferentiableAt
      (by simp)
  -- The derivative in `θ`.
  have hdθ : mfderiv 𝓘(ℝ, ℝ × ℝ × ℝ) IM C ((s : ℝ), 1, θ) (0, 0, 1) =
      mfderiv IF IM ι (φ θ) (Manifold.curveVelocity IF φ θ) := by
    rw [← hCd.curveVelocity_comp_mfderiv (g := fun r : ℝ ↦ ((s : ℝ), (1 : ℝ), r))
      ((hasDerivAt_const θ (s : ℝ)).prodMk ((hasDerivAt_const θ (1 : ℝ)).prodMk
        (hasDerivAt_id θ))), comp_def, hCι, ← Manifold.curveVelocityWithin_univ,
      ← Manifold.curveVelocityWithin_univ,
      Manifold.curveVelocityWithin_map hιd uniqueDiffWithinAt_univ hφ.mdifferentiableWithinAt]
  -- The derivative in `s`.
  have hds : mfderiv 𝓘(ℝ, ℝ × ℝ × ℝ) IM C ((s : ℝ), 1, θ) (1, 0, 0) =
      mfderiv IF IM ι (φ θ) (Φ.velocity s (Φ (s, c θ))) := by
    rw [mfderiv_transportedCylinder_one_apply hf hfp he he_symm hΔ hx hc,
      (A.trivAt b).mfderiv_fiberInclusionMap_apply hx _ hesd]
  have hp : C ((s : ℝ), 1, θ) = ι (φ θ) := congrFun hCι θ
  rw [hds, hdθ, hp, ← TauCeti.mpullback_apply_pair, MapFiber.Atlas.restrictsTo_iff.1 hτ b x hx]

end HolonomyCylinder

end IsEhresmannConnection

end TauCeti

end
