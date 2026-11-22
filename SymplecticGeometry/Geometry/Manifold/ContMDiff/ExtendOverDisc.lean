/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Geometry.Manifold.ContMDiff.Defs
public import Mathlib.Topology.Homotopy.Contractible
import TauCeti.Geometry.Manifold.SmoothApprox
import TauCeti.Topology.Homotopy.Extension.Ball
import TauCeti.Analysis.Normed.Module.Ball.Retraction

/-!
# Extending maps from an annulus over the disc

Let `0 ≤ a < a' < 1 < b` and let `f : ℂ → M` be `C^n` on the open annulus `a < ‖z‖ < b`, with
values in a Hausdorff boundaryless manifold modelled on a finite-dimensional real space. If the
loop of `f` on the unit circle is null-homotopic, then some `g : ℂ → M`, `C^n` on the open disc
`‖z‖ < b`, agrees with `f` on the smaller annulus `a' ≤ ‖z‖ < b`.

The proof first extends `f` continuously over the disc. For `0 < r ≤ 1 ≤ R`, the loop of `f` on
the circle of radius `r` is homotopic to the loop on the unit circle through the annulus
(`ContinuousOn.homotopic_of_eq_mul`), so it is null-homotopic and extends over the closed disc of
radius `r` (Tau Ceti's `ContinuousMap.nullhomotopic_iff_exists_extension_closedBall`). Continued
by `f` after Tau Ceti's radial retraction `TauCeti.radialRetraction` onto the closed disc of
radius `R`, this gives a continuous map on `ℂ` with relatively compact image that agrees with `f`
on `r ≤ ‖z‖ ≤ R`. For `a < r < a'` and `1 < R < b`, the
relative Whitney approximation theorem (Tau Ceti's
`ContinuousMap.exists_contMDiff_homotopicRel_of_isCompact_closure_range`) replaces it by a `C^n`
map equal to it on the closed annulus `a' ≤ ‖z‖ ≤ 1`, and that map, continued by `f` outside the
circle of radius `a'`, is `g`.

## Main results

* `ContinuousOn.homotopic_of_eq_mul`: the loops of a map continuous on a closed annulus, on the
  circles of its two radii, are homotopic.
* `ContinuousOn.exists_continuousMap_eq_of_nullhomotopic`: a map continuous on a closed annulus
  around the unit circle, with null-homotopic loop on the unit circle, agrees on that annulus with
  a continuous map on `ℂ` whose image has compact closure.
* `ContMDiffOn.exists_contMDiffOn_ball_eq_of_nullhomotopic`: the smooth extension above.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., GTM 218, Springer, 2013, Theorem 6.26
  (the relative Whitney approximation theorem).
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Proposition 0.16 (maps out
  of a sphere extend over the ball exactly when they are null-homotopic).
-/

public section

open Metric Set Topology TauCeti
open scoped Manifold ContDiff

/-- Let `0 < r ≤ s` and let `f : ℂ → M` be continuous on the closed annulus `r ≤ ‖z‖ ≤ s`. Then the
loops `ζ ↦ f (r ζ)` and `ζ ↦ f (s ζ)` of `f` on the circles of radii `r` and `s` are homotopic. -/
theorem ContinuousOn.homotopic_of_eq_mul {M : Type*} [TopologicalSpace M] {r s : ℝ} {f : ℂ → M}
    (hf : ContinuousOn f {z | r ≤ ‖z‖ ∧ ‖z‖ ≤ s}) (hr : 0 < r) (hrs : r ≤ s) (γ₀ γ₁ : C(Circle, M))
    (hγ₀ : ∀ ζ : Circle, γ₀ ζ = f (r * ζ)) (hγ₁ : ∀ ζ : Circle, γ₁ ζ = f (s * ζ)) :
    γ₀.Homotopic γ₁ := by
  have hnorm {t : ℝ} (ht : 0 ≤ t) (ζ : Circle) : ‖(t : ℂ) * ζ‖ = t := by
    simp [abs_of_nonneg ht]
  refine ⟨{ toFun := fun p ↦ f (((1 - (p.1 : ℝ)) * r + p.1 * s : ℝ) * p.2)
            continuous_toFun := hf.comp_continuous (by fun_prop) fun p ↦ ?_
            map_zero_left := fun ζ ↦ by simp [hγ₀]
            map_one_left := fun ζ ↦ by simp [hγ₁] }⟩
  have h0 := unitInterval.nonneg p.1
  have h1 := unitInterval.le_one p.1
  refine ⟨?_, ?_⟩ <;> rw [hnorm (by nlinarith)] <;> nlinarith

/-- **Continuous extension over the disc.** Let `0 < r ≤ 1 ≤ R` and let `f : ℂ → M` be continuous
on the closed annulus `r ≤ ‖z‖ ≤ R`. If the restriction `γ` of `f` to the unit circle is
null-homotopic, then some continuous `F : ℂ → M` whose image has compact closure agrees with `f`
on that annulus. -/
theorem ContinuousOn.exists_continuousMap_eq_of_nullhomotopic {M : Type*} [TopologicalSpace M]
    [T2Space M] {r R : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (h1R : 1 ≤ R) {f : ℂ → M}
    (hf : ContinuousOn f {z | r ≤ ‖z‖ ∧ ‖z‖ ≤ R}) (γ : C(Circle, M))
    (hγ : ∀ ζ : Circle, γ ζ = f ζ) (hγ0 : γ.Nullhomotopic) :
    ∃ F : C(ℂ, M), IsCompact (closure (range F)) ∧ ∀ z : ℂ, r ≤ ‖z‖ → ‖z‖ ≤ R → F z = f z := by
  have hR : 0 < R := by linarith
  -- the loop `γ₀` of `f` on the circle of radius `r` is homotopic to `γ`, so null-homotopic
  let γ₀ : C(Circle, M) := ⟨fun ζ ↦ f (r * ζ), hf.comp_continuous (by fun_prop) fun ζ ↦ by
    simp only [mem_ofPred_eq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
      Circle.norm_coe, mul_one]
    exact ⟨le_rfl, hr1.trans h1R⟩⟩
  have hγ₀ (ζ : Circle) : γ₀ ζ = f (r * ζ) := rfl
  have hγγ₀ : γ₀.Homotopic γ :=
    ContinuousOn.homotopic_of_eq_mul (hf.mono fun z hz ↦ ⟨hz.1, hz.2.trans h1R⟩) hr hr1 γ₀ γ hγ₀
      fun ζ ↦ by rw [hγ, Complex.ofReal_one, one_mul]
  obtain ⟨c, hc⟩ := hγ0
  -- so it extends over the closed unit disc, after rescaling by `r`
  let e : C(sphere (0 : ℂ) 1, Circle) :=
    ⟨fun y ↦ ⟨y, by simp [Submonoid.unitSphere]⟩, by fun_prop⟩
  have he (y : sphere (0 : ℂ) 1) : ((e y : Circle) : ℂ) = y := rfl
  obtain ⟨D, hD⟩ := (ContinuousMap.nullhomotopic_iff_exists_extension_closedBall (γ₀.comp e)).1
    (ContinuousMap.Nullhomotopic.comp_left ⟨c, hγγ₀.trans hc⟩ e)
  -- `F` is given by `D` inside the circle of radius `r`, and by `f` after the radial retraction
  -- onto the closed disc of radius `R` outside it
  have hinD (z : ℂ) : r⁻¹ • radialRetraction r z ∈ closedBall (0 : ℂ) 1 := by
    rw [mem_closedBall_zero_iff, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hr,
      norm_radialRetraction hr.le, inv_mul_le_one₀ hr]
    exact min_le_right _ _
  let inner : ℂ → M := fun z ↦ D ⟨r⁻¹ • radialRetraction r z, hinD z⟩
  have hinner : Continuous inner := by
    have h : Continuous fun z : ℂ ↦ radialRetraction r z :=
      continuous_const.radialRetraction (fun _ ↦ hr.le) continuous_id
    have h' : Continuous fun z : ℂ ↦ r⁻¹ • radialRetraction r z := by fun_prop
    exact D.continuous.comp (h'.subtype_mk hinD)
  have hκ : Continuous fun z : ℂ ↦ radialRetraction R z :=
    continuous_const.radialRetraction (fun _ ↦ hR.le) continuous_id
  have hκ_norm {z : ℂ} (hz : r ≤ ‖z‖) :
      r ≤ ‖radialRetraction R z‖ ∧ ‖radialRetraction R z‖ ≤ R := by
    rw [norm_radialRetraction hR.le]
    exact ⟨le_min hz (by linarith), min_le_right _ _⟩
  classical
  let Fc : ℂ → M := fun z ↦ if ‖z‖ ≤ r then inner z else f (radialRetraction R z)
  have hagree {z : ℂ} (hz : ‖z‖ = r) : inner z = f z := by
    have hy : r⁻¹ • z ∈ sphere (0 : ℂ) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hr, hz,
        inv_mul_cancel₀ hr.ne']
    have h := hD ⟨_, hy⟩
    rw [ContinuousMap.comp_apply, hγ₀, he] at h
    simp only [inner, radialRetraction_of_norm_le hz.le]
    refine h.trans (congr_arg f ?_)
    rw [Subtype.coe_mk, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
      mul_inv_cancel₀ hr.ne', Complex.ofReal_one, one_mul]
  have hFc : Continuous Fc :=
    continuous_if_le continuous_norm continuous_const hinner.continuousOn
      (hf.comp hκ.continuousOn fun z hz ↦ hκ_norm hz) fun z hz ↦ by
        rw [hagree hz, radialRetraction_of_norm_le (hz.le.trans hr1 |>.trans h1R)]
  refine ⟨⟨Fc, hFc⟩, ?_, fun z h₁ h₂ ↦ ?_⟩
  · -- the image of `F` lies in the compact set `range D ∪ f '' {r ≤ ‖z‖ ≤ R}`
    have hK : IsCompact (range D ∪ f '' {z | r ≤ ‖z‖ ∧ ‖z‖ ≤ R}) := by
      refine (isCompact_range D.continuous).union (IsCompact.image_of_continuousOn ?_ hf)
      exact (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset
        ((isClosed_le continuous_const continuous_norm).inter
          (isClosed_le continuous_norm continuous_const))
        fun z hz ↦ mem_closedBall_zero_iff.2 hz.2
    refine hK.of_isClosed_subset isClosed_closure (closure_minimal ?_ hK.isClosed)
    rintro _ ⟨z, rfl⟩
    by_cases hz : ‖z‖ ≤ r
    · exact Or.inl ⟨_, (ite_eq_left hz).symm⟩
    · exact Or.inr ⟨radialRetraction R z, hκ_norm (not_le.1 hz).le, (ite_eq_right hz).symm⟩
  · by_cases h : ‖z‖ ≤ r
    · exact (ite_eq_left h).trans (hagree (le_antisymm h h₁))
    · exact (ite_eq_right h).trans (congr_arg f (radialRetraction_of_norm_le h₂))

variable {F G M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace G M] [IsManifold J ∞ M] [T2Space M]

/-- **Smooth extension over the disc.** Let `0 ≤ a < a' < 1 < b` and let `f : ℂ → M` be `C^n` on
the open annulus `a < ‖z‖ < b`. If the restriction `γ` of `f` to the unit circle is
null-homotopic, then there is `g : ℂ → M`, `C^n` on the open disc `‖z‖ < b`, with `g z = f z`
whenever `a' ≤ ‖z‖ < b`. -/
theorem ContMDiffOn.exists_contMDiffOn_ball_eq_of_nullhomotopic {n : ℕ∞} {a a' b : ℝ}
    (ha : 0 ≤ a) (haa' : a < a') (ha'1 : a' < 1) (h1b : 1 < b) {f : ℂ → M}
    (hf : ContMDiffOn 𝓘(ℝ, ℂ) J n f {z | a < ‖z‖ ∧ ‖z‖ < b}) (γ : C(Circle, M))
    (hγ : ∀ ζ : Circle, γ ζ = f ζ) (hγ0 : γ.Nullhomotopic) :
    ∃ g : ℂ → M, ContMDiffOn 𝓘(ℝ, ℂ) J n g (ball 0 b) ∧
      ∀ z : ℂ, a' ≤ ‖z‖ → ‖z‖ < b → g z = f z := by
  set r₀ : ℝ := (a + a') / 2 with hr₀_def
  set b' : ℝ := (1 + b) / 2 with hb'_def
  -- a continuous extension `F₀` of `f` from the annulus `r₀ ≤ ‖z‖ ≤ b'` with relatively compact
  -- image
  obtain ⟨F₀, hF₀K, hF₀f⟩ := ContinuousOn.exists_continuousMap_eq_of_nullhomotopic
    (r := r₀) (R := b') (by linarith) (by linarith) (by linarith)
    (hf.continuousOn.mono fun z hz ↦ ⟨by linarith [hz.1], by linarith [hz.2]⟩) γ hγ hγ0
  set S : Set ℂ := {z | a' ≤ ‖z‖ ∧ ‖z‖ ≤ 1}
  set U : Set ℂ := {z | r₀ < ‖z‖ ∧ ‖z‖ < b'}
  have hS : IsClosed S :=
    (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  have hU : IsOpen U :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hSU : S ⊆ U := fun z hz ↦ ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have hF₀U (z : ℂ) (hz : z ∈ U) : F₀ z = f z := hF₀f z hz.1.le hz.2.le
  -- the relative Whitney approximation gives a `C^n` map `g₀` equal to `F₀` on `S`
  obtain ⟨g₀, hg₀, hF₀g₀⟩ :=
    F₀.exists_contMDiff_homotopicRel_of_isCompact_closure_range (I := 𝓘(ℝ, ℂ)) n hF₀K hS
      (hU.mem_nhdsSet.2 hSU)
      ((hf.mono fun z (hz : z ∈ U) ↦ ⟨by linarith [hz.1], by linarith [hz.2]⟩).congr hF₀U)
  have hg₀f {z : ℂ} (hz : z ∈ S) : g₀ z = f z :=
    (hF₀g₀.fst_eq_snd hz).symm.trans (hF₀U z (hSU hz))
  -- `g₀` inside the circle of radius `a'`, and `f` outside
  let g : ℂ → M := fun z ↦ if ‖z‖ ≤ a' then g₀ z else f z
  have hgf {z : ℂ} (h₁ : a' ≤ ‖z‖) : g z = f z := by
    by_cases h : ‖z‖ ≤ a'
    · exact (ite_eq_left h).trans (hg₀f ⟨h₁, h.trans ha'1.le⟩)
    · exact ite_eq_right h
  have hgg₀ {z : ℂ} (h₁ : ‖z‖ < 1) : g z = g₀ z := by
    by_cases h : ‖z‖ ≤ a'
    · exact ite_eq_left h
    · rw [hgf (not_le.1 h).le, hg₀f ⟨(not_le.1 h).le, h₁.le⟩]
  refine ⟨g, fun z hz ↦ ContMDiffAt.contMDiffWithinAt ?_, fun z h₁ _ ↦ hgf h₁⟩
  by_cases h : ‖z‖ < 1
  · exact (hg₀ z).congr_of_eventuallyEq <| Filter.eventually_of_mem
      ((isOpen_lt continuous_norm continuous_const).mem_nhds h) fun w hw ↦ hgg₀ hw
  · have hV : IsOpen {w : ℂ | a' < ‖w‖ ∧ ‖w‖ < b} :=
      (isOpen_lt continuous_const continuous_norm).inter
        (isOpen_lt continuous_norm continuous_const)
    have hzV : {w : ℂ | a' < ‖w‖ ∧ ‖w‖ < b} ∈ 𝓝 z :=
      hV.mem_nhds ⟨by linarith [not_lt.1 h], mem_ball_zero_iff.1 hz⟩
    exact (hf.contMDiffAt (Filter.mem_of_superset hzV fun w hw ↦ ⟨by linarith [hw.1], hw.2⟩)
      ).congr_of_eventuallyEq <| Filter.eventually_of_mem hzV fun w hw ↦ hgf hw.1.le
