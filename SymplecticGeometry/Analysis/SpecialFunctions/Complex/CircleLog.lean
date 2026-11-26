/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.Topology.Circle.FreeLoop
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import SymplecticGeometry.Geometry.Manifold.Instances.Sphere
import SymplecticGeometry.Topology.Circle.FreeLoop
import TauCeti.AlgebraicTopology.UniversalCover.Circle.FreeLoop.Basic
import TauCeti.Geometry.Manifold.Algebra.LieGroup
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition
import TauCeti.Topology.Covering.LiftOn

/-!
# Smooth real logarithms of circle-valued maps on an annulus

A continuous real function `θ` whose exponential `Circle.exp ∘ θ` is `C^n` is itself `C^n`
(`Circle.contDiffAt_of_contDiffAt_exp`), since `Circle.exp` is a local diffeomorphism
(`isLocalDiffeomorph_circleExp`) and a continuous map whose composite with a local diffeomorphism
is `C^n` is `C^n` (Tau Ceti's `ContMDiffWithinAt.of_comp_isLocalDiffeomorph`).

On the open annulus `A = {z : ℂ | a < ‖z‖ < b}`, `0 ≤ a`, a `C^n` map `u : ℂ → S¹` whose loop
`ζ ↦ u (r ζ)` on one circle of radius `r ∈ (a, b)` has degree `0` is `exp (i h)` for a real
function `h` that is `C^n` on `A`
(`Circle.exists_contDiffOn_exp_eq_of_circleDegree_eq_zero`).

The proof pulls `u` back along the universal covering `Complex.exp` of `A` by the vertical strip
`S = exp⁻¹ A`, which is convex, so simply connected. The lifting criterion for covering maps, in
Tau Ceti's form for maps continuous on a set (`IsCoveringMap.exists_continuousOn_lift`), lifts
`u ∘ exp` through `Circle.exp` to a function `G` continuous on `S`. The lifts `G (w + 2πi)`
and `G w` of the same map differ by a constant multiple of `2π` (Tau Ceti's
`Circle.exists_int_forall_eq_add_of_exp_eq`), which on the line `Re w = log r` is the degree of
the loop on the circle of radius `r`, so `G` is `2πi`-periodic.
Then `h = G ∘ log` is continuous on `A`, as near each point it agrees with `G` composed with a
continuous branch of the logarithm (`Function.Periodic.continuousOn_comp_log`), and smooth by the
first result, in the form `Circle.contDiffOn_of_contMDiffOn_exp`.

As an application, a smooth map `w : ℂ → S¹` on a punctured disc `0 < ‖z‖ < b` can be brought to
the normal form `(z / ‖z‖) ^ k` near the centre (`Circle.exists_contMDiffOn_mul_eq_exp_arg_zpow`),
whose smoothness on `ℂ \ {0}` is `Circle.contMDiffOn_exp_arg` (`Instances/Sphere.lean`):
with `k` the degree of `w` on a circle of radius `r₁`, the map `w · (z / ‖z‖) ^ (-k)` has
degree `0`, so it is `exp (i h)` for a smooth real `h`, and multiplying `w` by `exp (-i χ h)`, for
a radial cut-off `χ` (`ContDiffBump`) equal to `1` up to radius `r₁` and to `0` from radius `r₂`
on, gives `(z / ‖z‖) ^ k` up to radius `r₁` without changing `w` from radius `r₂` on.

## Main results

* `Circle.contDiffAt_of_contDiffAt_exp`: continuous lifts of `C^n` circle-valued maps through
  `Circle.exp` are `C^n`.
* `Circle.contDiffOn_of_contMDiffOn_exp`: the same on an open set, for a lift whose exponential
  is `C^n` as a map into the manifold `Circle`.
* `Function.Periodic.continuousOn_comp_log`: a `2πi`-periodic function continuous on
  `exp ⁻¹' U` becomes continuous on `U` after composing with `Complex.log`.
* `Circle.exists_contDiffOn_exp_eq_of_circleDegree_eq_zero`: a `C^n` circle-valued map of
  degree `0` on an annulus has a `C^n` real logarithm.
* `Circle.exists_contMDiffOn_mul_eq_exp_arg_zpow`: a smooth circle-valued map on a punctured
  disc agrees with `(z / ‖z‖) ^ k` near the centre after multiplication by a smooth map that is
  `1` near the edge.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Proposition 1.33 (the
  lifting criterion).
-/

public section

open Complex Filter Set Topology
open scoped Manifold ContDiff Real

/-- If `G` is `2πi`-periodic and continuous on `exp ⁻¹' U`, for a set `U` not containing `0`,
then `z ↦ G (log z)` is continuous on `U`. -/
theorem Function.Periodic.continuousOn_comp_log {α : Type*} [TopologicalSpace α] {G : ℂ → α}
    {U : Set ℂ} (hper : Function.Periodic G (2 * π * I)) (h0 : (0 : ℂ) ∉ U)
    (hG : ContinuousOn G (Complex.exp ⁻¹' U)) : ContinuousOn (fun z ↦ G (log z)) U := by
  intro z₀ hz₀
  have hz₀0 : z₀ ≠ 0 := ne_of_mem_of_not_mem hz₀ h0
  -- near `z₀`, `G ∘ log` agrees with `G` after the continuous branch `L` of the logarithm
  let L : ℂ → ℂ := fun z ↦ log (z * z₀⁻¹) + log z₀
  have hL : ContinuousAt L z₀ := by
    refine ((continuousAt_clog ?_).comp (continuousAt_id.mul continuousAt_const)).add
      continuousAt_const
    simp [hz₀0]
  have hLz₀ : L z₀ = log z₀ := by simp [L, hz₀0]
  have hexpL {z : ℂ} (hz : z ≠ 0) : Complex.exp (L z) = z := by
    simp [L, Complex.exp_add, exp_log, hz, hz₀0]
  have hmaps : MapsTo L U (Complex.exp ⁻¹' U) := fun z hz ↦ by
    simpa [hexpL (ne_of_mem_of_not_mem hz h0)] using hz
  have hGL : ContinuousWithinAt (G ∘ L) U z₀ := by
    refine ContinuousWithinAt.comp ?_ hL.continuousWithinAt hmaps
    rw [hLz₀]
    exact hG _ (by simpa [exp_log hz₀0] using hz₀)
  refine hGL.congr_of_mem (fun z hz ↦ ?_) hz₀
  obtain ⟨k, hk⟩ := exp_eq_exp_iff_exists_int.1
    (show Complex.exp (log z) = Complex.exp (L z) by
      rw [hexpL (ne_of_mem_of_not_mem hz h0), exp_log (ne_of_mem_of_not_mem hz h0)])
  simp [hk, hper.int_mul k (L z)]

namespace Circle

attribute [local instance] finrank_real_complex_fact'

/-- A real function `θ`, continuous at `x`, whose exponential `y ↦ exp (i θ y)` is `C^n` at `x`
is `C^n` at `x`. -/
theorem contDiffAt_of_contDiffAt_exp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : WithTop ℕ∞} {θ : E → ℝ} {x : E} (hθ : ContinuousAt θ x)
    (h : ContDiffAt ℝ n (fun y ↦ (exp (θ y) : ℂ)) x) : ContDiffAt ℝ n θ x := by
  rw [← contMDiffAt_iff_contDiffAt, ← contMDiffWithinAt_univ]
  exact ContMDiffWithinAt.of_comp_isLocalDiffeomorph
    (SymplecticGeometry.isLocalDiffeomorph_circleExp n (θ x))
    hθ.continuousWithinAt (contMDiffAt_iff_contDiffAt.2 h).of_coe_sphere.contMDiffWithinAt

/-- A real function `θ`, continuous on an open set `s`, whose exponential `y ↦ exp (i θ y)` is
`C^n` on `s` as a map into the circle, is `C^n` on `s`. -/
theorem contDiffOn_of_contMDiffOn_exp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : WithTop ℕ∞} {θ : E → ℝ} {s : Set E} (hs : IsOpen s) (hθ : ContinuousOn θ s)
    (h : ContMDiffOn 𝓘(ℝ, E) (𝓡 1) n (fun y ↦ exp (θ y)) s) : ContDiffOn ℝ n θ s := by
  intro x hx
  refine (contDiffAt_of_contDiffAt_exp (hθ.continuousAt (hs.mem_nhds hx)) ?_).contDiffWithinAt
  have h' := (contMDiff_coe_sphere (m := n)).contMDiffAt.comp_contMDiffWithinAt x (h x hx)
  exact (contMDiffWithinAt_iff_contDiffWithinAt.1 h').contDiffAt (hs.mem_nhds hx)

/-- **Smooth logarithms on an annulus.** Let `0 ≤ a < r < b` and let `u : ℂ → S¹` be `C^n` on the
open annulus `a < ‖z‖ < b`. If the loop `ζ ↦ u (r ζ)` on the circle of radius `r` has degree `0`,
then `u = exp (i h)` on the annulus for a real function `h` that is `C^n` there. -/
theorem exists_contDiffOn_exp_eq_of_circleDegree_eq_zero {n : WithTop ℕ∞} {a b r : ℝ}
    (ha : 0 ≤ a) (har : a < r) (hrb : r < b) {u : ℂ → Circle}
    (hu : ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 1) n u {z | a < ‖z‖ ∧ ‖z‖ < b}) (f : C(Circle, Circle))
    (hf : ∀ ζ : Circle, f ζ = u (r * ζ)) (hdeg : f.circleDegree = 0) :
    ∃ h : ℂ → ℝ, ContDiffOn ℝ n h {z | a < ‖z‖ ∧ ‖z‖ < b} ∧
      ∀ z, a < ‖z‖ → ‖z‖ < b → u z = exp (h z) := by
  set A : Set ℂ := {z | a < ‖z‖ ∧ ‖z‖ < b}
  have hA : IsOpen A :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  -- the strip `S = exp⁻¹ A` covers the annulus
  set S : Set ℂ := Complex.exp ⁻¹' A
  have hSo : IsOpen S := hA.preimage Complex.continuous_exp
  have hSc : Convex ℝ S := by
    have : S = re ⁻¹' (Real.exp ⁻¹' Ioo a b) := by ext w; simp [S, A, norm_exp]
    rw [this]
    exact (ordConnected_Ioo.preimage_mono Real.exp_monotone).convex.linear_preimage reLm
  have hr : 0 < r := ha.trans_lt har
  have hrS : ((Real.log r : ℝ) : ℂ) ∈ S := by
    simp [S, A, norm_exp, Real.exp_log hr, har, hrb]
  have hshift (w : ℂ) : w + 2 * π * I ∈ S ↔ w ∈ S := by simp [S, exp_periodic w]
  have : ContractibleSpace S := hSc.contractibleSpace ⟨_, hrS⟩
  have : LocallyPathConnectedSpace S := hSo.locallyPathConnectedSpace
  -- lift `u ∘ exp` through `Circle.exp` on `S`, and take the lift to be `0` off `S`
  obtain ⟨G₀, hG₀c, -, hG₀⟩ := isCoveringMap_exp.exists_continuousOn_lift
    (f := fun w ↦ u (Complex.exp w))
    (hu.continuousOn.comp Complex.continuous_exp.continuousOn fun _ hw ↦ hw) hrS (exp_arg _)
  classical
  let Gx : ℂ → ℝ := fun w ↦ if w ∈ S then G₀ w else 0
  have hGxc : ContinuousOn Gx S := hG₀c.congr fun w hw ↦ by simp [Gx, hw]
  let G : C(S, ℝ) := ⟨S.domRestrict Gx, hGxc.domRestrict⟩
  have hGx (w : S) : Gx w = G w := rfl
  have hGF (w : S) : exp (G w) = u (Complex.exp w) := by
    simpa [← hGx, Gx, w.property] using hG₀ w.property
  -- `G` is `2πi`-periodic
  let τ : C(S, S) := ⟨fun w ↦ ⟨w + 2 * π * I, (hshift w).2 w.property⟩, by fun_prop⟩
  obtain ⟨m, hm⟩ := exists_int_forall_eq_add_of_exp_eq (G.continuous.comp τ.continuous)
    G.continuous fun w ↦ by simp [τ, hGF, exp_periodic _]
  have hm0 : m = 0 := by
    let γ : C(unitInterval, S) := ⟨fun t ↦ ⟨(Real.log r : ℂ) + 2 * π * (t : ℝ) * I, by
      simp [S, A, norm_exp, Real.exp_log hr, har, hrb]⟩, by fun_prop⟩
    have h := f.sub_eq_circleDegree_mul (θ := G ∘ γ) (G.continuous.comp γ.continuous) fun t ↦ by
      rw [Function.comp_apply, hGF, hf, TauCeti.unitToCircle_apply, coe_exp]
      congr 1
      simp only [γ, ContinuousMap.coe_mk]
      rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hr]
      push_cast
      ring_nf
    have h1 : γ 1 = τ ⟨_, hrS⟩ := by ext; simp [γ, τ]
    have h0 : γ 0 = ⟨_, hrS⟩ := by ext; simp [γ]
    have hτ := hm ⟨_, hrS⟩
    rw [Function.comp_apply] at hτ
    rw [hdeg, Function.comp_apply, Function.comp_apply, h1, h0, hτ] at h
    simpa [Real.pi_ne_zero] using h
  -- the extension `Gx` of `G` by `0` off the strip is `2πi`-periodic
  have hper : Function.Periodic Gx (2 * π * I) := fun w ↦ by
    by_cases hw : w ∈ S
    · have h := hm ⟨w, hw⟩
      rw [hm0, Function.comp_apply] at h
      rw [← hGx ⟨w, hw⟩, ← hGx (τ ⟨w, hw⟩)] at h
      simpa [τ] using h
    · simp [Gx, hw, hshift]
  have hA0 : (0 : ℂ) ∉ A := fun h ↦ (ha.trans_lt h.1).ne' norm_zero
  have hexp {z : ℂ} (hz : z ∈ A) : u z = exp (Gx (log z)) := by
    have hz0 : z ≠ 0 := ne_of_mem_of_not_mem hz hA0
    rw [hGx ⟨log z, by simpa [S, exp_log hz0] using hz⟩, hGF, exp_log hz0]
  refine ⟨fun z ↦ Gx (log z), ?_, fun z h₁ h₂ ↦ hexp ⟨h₁, h₂⟩⟩
  exact contDiffOn_of_contMDiffOn_exp hA (hper.continuousOn_comp_log hA0 hGxc)
    (hu.congr fun z hz ↦ (hexp hz).symm)

/-- **Normal form of a smooth circle-valued map on a punctured disc.** Let `0 < r₁ < r₂` and
`r₁ < b`, and let `w : ℂ → S¹` be smooth on the punctured disc `0 < ‖z‖ < b`. Then there are an
integer `k` and a map `c : ℂ → S¹`, smooth on the punctured disc and equal to `1` where
`r₂ ≤ ‖z‖`, such that `w z * c z = (z / ‖z‖) ^ k` (written `exp (i arg z) ^ k`) whenever
`0 < ‖z‖ ≤ r₁`. -/
theorem exists_contMDiffOn_mul_eq_exp_arg_zpow {r₁ r₂ b : ℝ} (h₁ : 0 < r₁) (h₁₂ : r₁ < r₂)
    (h₁b : r₁ < b) {w : ℂ → Circle}
    (hw : ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 1) ∞ w {z | 0 < ‖z‖ ∧ ‖z‖ < b}) :
    ∃ (k : ℤ) (c : ℂ → Circle), ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 1) ∞ c {z | 0 < ‖z‖ ∧ ‖z‖ < b} ∧
      (∀ z, r₂ ≤ ‖z‖ → c z = 1) ∧
      ∀ z, 0 < ‖z‖ → ‖z‖ ≤ r₁ → w z * c z = exp (arg z) ^ k := by
  have hmem (ζ : Circle) : ((r₁ : ℂ) * ζ) ∈ {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < b} := by
    simp [abs_of_pos h₁, h₁.ne', h₁b]
  -- the loop of `w` on the circle of radius `r₁`, and its degree `k`
  let f : C(Circle, Circle) := ⟨fun ζ ↦ w (r₁ * ζ), hw.continuousOn.comp_continuous
    (continuous_const.mul continuous_subtypeVal) hmem⟩
  set k := f.circleDegree
  -- `v = w / (z / ‖z‖) ^ k` has degree `0`, so it has a smooth logarithm `h`
  let v : ℂ → Circle := fun z ↦ w z * (exp (arg z) ^ k)⁻¹
  have hv : ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 1) ∞ v {z | 0 < ‖z‖ ∧ ‖z‖ < b} :=
    hw.mul (((TauCeti.contMDiff_zpow k).comp_contMDiffOn
      (contMDiffOn_exp_arg.mono (t := {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < b})
        fun z hz ↦ norm_pos_iff.1 hz.1)).inv)
  let g : C(Circle, Circle) := f * (⟨(· ^ k), continuous_zpow k⟩ : C(Circle, Circle))⁻¹
  have hg (ζ : Circle) : g ζ = v (r₁ * ζ) := by
    simp [g, v, f, arg_ofReal_mul h₁, exp_arg]
  obtain ⟨h, hh, hvh⟩ := exists_contDiffOn_exp_eq_of_circleDegree_eq_zero le_rfl h₁ h₁b hv g hg
    (by simp [g, k])
  -- `c = exp (-i χ h)` for a radial cut-off `χ`, equal to `1` on `‖z‖ ≤ r₁` and `0` on `r₂ ≤ ‖z‖`
  let χ : ContDiffBump (0 : ℂ) := ⟨r₁, r₂, h₁, h₁₂⟩
  refine ⟨k, fun z ↦ exp (-(χ z * h z)), contMDiff_circleExp.comp_contMDiffOn
    ((χ.contDiff.contDiffOn.mul hh).neg).contMDiffOn, fun z hz ↦ ?_, fun z hz hz₁ ↦ ?_⟩
  · simp [χ.zero_of_le_dist (by simpa using hz)]
  · dsimp only
    rw [χ.one_of_mem_closedBall (by simpa using hz₁), one_mul, exp_neg, ← hvh z hz
      (hz₁.trans_lt h₁b)]
    simp [v]

end Circle
