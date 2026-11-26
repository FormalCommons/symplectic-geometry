/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Topology.Homotopy.Contractible
public import TauCeti.Analysis.Complex.ClosedAnnulus
import SymplecticGeometry.Topology.Sets.Annulus
import TauCeti.Topology.Homotopy.Extension.Ball
import TauCeti.Analysis.Normed.Module.Ball.Retraction

/-!
# Loops on circles of `ℂ` and their extension over discs

For a map `f : ℂ → M` into a topological space, the loops `ζ ↦ f (r ζ)` on circles of radius `r`
around `0` are homotopic to each other as long as `f` is continuous on the closed annulus between
them. A null-homotopic loop `γ : C(Circle, M)` extends continuously over the closed disc of any
positive radius `r`, as a map equal to `γ ζ` at `r ζ`. Together, these extend a map continuous on
a closed annulus around the unit circle, with null-homotopic loop on the unit circle, to a
continuous map on all of `ℂ`.

The extension over a disc rescales Tau Ceti's
`ContinuousMap.nullhomotopic_iff_exists_extension_closedBall`, stated for the unit sphere of a
normed space, to the circle of radius `r` in `ℂ`. The map on `ℂ`
is obtained outside the annulus by composing `f` with Tau Ceti's radial retraction
`TauCeti.radialRetraction`.

## Main results

* `ContinuousOn.homotopic_of_eq_mul`: the loops of a map continuous on a closed annulus, on the
  circles of its two radii, are homotopic.
* `ContinuousMap.Nullhomotopic.exists_extension_closedBall`: a null-homotopic loop in `M`
  extends continuously over the closed disc of radius `r > 0`.
* `ContinuousOn.exists_continuousMap_eq_of_nullhomotopic`: a map continuous on a closed annulus
  around the unit circle, with null-homotopic loop on the unit circle, agrees on that annulus with
  a continuous map on `ℂ` whose image has compact closure.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, proof of Proposition 0.16
  (the homotopy extension property of the pair `(Dⁿ, Sⁿ⁻¹)`), from which the criterion that a map
  out of a sphere is null-homotopic exactly when it extends over the ball follows.
-/

public section

open Metric Set TauCeti
open Complex (closedAnnulus closedAnnulus_subset_closedAnnulus isCompact_closedAnnulus
  mem_closedAnnulus)

/-- Let `0 ≤ r ≤ s` and let `f : ℂ → M` be continuous on the closed annulus `r ≤ ‖z‖ ≤ s`. Then the
loops `ζ ↦ f (r ζ)` and `ζ ↦ f (s ζ)` of `f` on the circles of radii `r` and `s` are homotopic. -/
theorem ContinuousOn.homotopic_of_eq_mul {M : Type*} [TopologicalSpace M] {r s : ℝ} {f : ℂ → M}
    (hf : ContinuousOn f (closedAnnulus r s)) (hr : 0 ≤ r) (hrs : r ≤ s) (γ₀ γ₁ : C(Circle, M))
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
  refine mem_closedAnnulus.2 ⟨?_, ?_⟩ <;> rw [hnorm (by nlinarith)] <;> nlinarith

/-- A null-homotopic loop `γ : C(Circle, M)` extends continuously over the closed disc of radius
`r > 0` in `ℂ`: some `D : ℂ → M`, continuous on `closedBall 0 r`, has `D (r ζ) = γ ζ` for every
`ζ : Circle`. -/
theorem ContinuousMap.Nullhomotopic.exists_extension_closedBall {M : Type*} [TopologicalSpace M]
    {γ : C(Circle, M)} (hγ : γ.Nullhomotopic) {r : ℝ} (hr : 0 < r) :
    ∃ D : ℂ → M, ContinuousOn D (closedBall 0 r) ∧ ∀ ζ : Circle, D (r * ζ) = γ ζ := by
  let e : C(sphere (0 : ℂ) 1, Circle) :=
    ⟨fun y ↦ ⟨y, by simp [Submonoid.unitSphere]⟩, by fun_prop⟩
  obtain ⟨D₁, hD₁⟩ :=
    (ContinuousMap.nullhomotopic_iff_exists_extension_closedBall (γ.comp e)).1 (hγ.comp_left e)
  have hin (z : ℂ) : r⁻¹ • radialRetraction r z ∈ closedBall (0 : ℂ) 1 := by
    simp [abs_of_pos hr, norm_radialRetraction hr.le, inv_mul_le_one₀ hr]
  refine ⟨fun z ↦ D₁ ⟨r⁻¹ • radialRetraction r z, hin z⟩, Continuous.continuousOn ?_, fun ζ ↦ ?_⟩
  · have h : Continuous fun z : ℂ ↦ radialRetraction r z :=
      continuous_const.radialRetraction (fun _ ↦ Or.inr hr.le) continuous_id
    exact D₁.continuous.comp ((h.const_smul r⁻¹).subtype_mk hin)
  · have hζ : r⁻¹ • radialRetraction r ((r : ℂ) * ζ) = ζ := by
      rw [radialRetraction_of_norm_le (by simp [abs_of_pos hr]), Complex.real_smul, ← mul_assoc]
      simp [hr.ne']
    have hs : (ζ : ℂ) ∈ sphere (0 : ℂ) 1 := by simp
    have h := hD₁ ⟨ζ, hs⟩
    rw [ContinuousMap.comp_apply] at h
    exact (congr_arg D₁ (Subtype.ext hζ)).trans (h.trans (congr_arg γ (Subtype.ext rfl)))

/-- **Continuous extension over the disc.** Let `0 < r ≤ 1 ≤ R` and let `f : ℂ → M` be continuous
on the closed annulus `r ≤ ‖z‖ ≤ R`. If the restriction `γ` of `f` to the unit circle is
null-homotopic, then some continuous `F : ℂ → M` whose image has compact closure agrees with `f`
on that annulus. -/
theorem ContinuousOn.exists_continuousMap_eq_of_nullhomotopic {M : Type*} [TopologicalSpace M]
    [T2Space M] {r R : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (h1R : 1 ≤ R) {f : ℂ → M}
    (hf : ContinuousOn f (closedAnnulus r R)) (γ : C(Circle, M))
    (hγ : ∀ ζ : Circle, γ ζ = f ζ) (hγ0 : γ.Nullhomotopic) :
    ∃ F : C(ℂ, M), IsCompact (closure (range F)) ∧ ∀ z : ℂ, r ≤ ‖z‖ → ‖z‖ ≤ R → F z = f z := by
  have hR : 0 < R := by linarith
  -- the loop `γ₀` of `f` on the circle of radius `r` is homotopic to `γ`, so null-homotopic, and
  -- it extends over the closed disc of radius `r`
  let γ₀ : C(Circle, M) := ⟨fun ζ ↦ f (r * ζ), hf.comp_continuous (by fun_prop) fun ζ ↦ by
    simpa [abs_of_pos hr] using hr1.trans h1R⟩
  have hγ₀ (ζ : Circle) : γ₀ ζ = f (r * ζ) := rfl
  have hγγ₀ : γ₀.Homotopic γ :=
    ContinuousOn.homotopic_of_eq_mul (hf.mono (closedAnnulus_subset_closedAnnulus le_rfl h1R))
      hr.le hr1 γ₀ γ hγ₀ fun ζ ↦ by simp [hγ]
  obtain ⟨c, hc⟩ := hγ0
  obtain ⟨D, hDc, hD⟩ := ContinuousMap.Nullhomotopic.exists_extension_closedBall
    ⟨c, hγγ₀.trans hc⟩ hr
  -- `F` is given by `D` after the radial retraction onto the closed disc of radius `r` inside the
  -- circle of radius `r`, and by `f` after the radial retraction onto the closed disc of radius
  -- `R` outside it
  have hκ (t : ℝ) (ht : 0 ≤ t) : Continuous fun z : ℂ ↦ TauCeti.radialRetraction t z :=
    continuous_const.radialRetraction (fun _ ↦ Or.inr ht) continuous_id
  have hκ_norm {z : ℂ} (hz : r ≤ ‖z‖) :
      TauCeti.radialRetraction R z ∈ closedAnnulus r R := by
    rw [mem_closedAnnulus, norm_radialRetraction hR.le]
    exact ⟨le_min hz (by linarith), min_le_right _ _⟩
  classical
  let Fc : ℂ → M := fun z ↦
    if ‖z‖ ≤ r then D (TauCeti.radialRetraction r z) else f (TauCeti.radialRetraction R z)
  have hagree {z : ℂ} (hz : ‖z‖ = r) : D z = f z := by
    have hζ : (r : ℂ)⁻¹ * z ∈ Submonoid.unitSphere ℂ := by
      simp [Submonoid.unitSphere, abs_of_pos hr, hz, hr.ne']
    have h := (hD ⟨_, hζ⟩).trans (hγ₀ _)
    have hz' : (r : ℂ) * ((⟨_, hζ⟩ : Circle) : ℂ) = z := by
      rw [Subtype.coe_mk, mul_inv_cancel_left₀ (Complex.ofReal_ne_zero.2 hr.ne')]
    rwa [hz'] at h
  have hFc : Continuous Fc :=
    continuous_if_le continuous_norm continuous_const
      (hDc.comp_continuous (hκ r hr.le) (radialRetraction_mem_closedBall hr.le)).continuousOn
      (hf.comp (hκ R hR.le).continuousOn fun z hz ↦ hκ_norm hz) fun z hz ↦ by
        rw [radialRetraction_of_norm_le hz.le, hagree hz,
          radialRetraction_of_norm_le (hz.le.trans hr1 |>.trans h1R)]
  refine ⟨⟨Fc, hFc⟩, ?_, fun z h₁ h₂ ↦ ?_⟩
  · -- the image of `F` lies in the compact set `D '' closedBall 0 r ∪ f '' closedAnnulus r R`
    have hK : IsCompact (D '' closedBall 0 r ∪ f '' closedAnnulus r R) :=
      ((isCompact_closedBall 0 r).image_of_continuousOn hDc).union
        ((isCompact_closedAnnulus r R).image_of_continuousOn hf)
    refine hK.of_isClosed_subset isClosed_closure (closure_minimal ?_ hK.isClosed)
    rintro _ ⟨z, rfl⟩
    by_cases hz : ‖z‖ ≤ r
    · exact Or.inl ⟨_, radialRetraction_mem_closedBall hr.le z, (ite_eq_left hz).symm⟩
    · exact Or.inr ⟨TauCeti.radialRetraction R z, hκ_norm (not_le.1 hz).le, (ite_eq_right hz).symm⟩
  · by_cases h : ‖z‖ ≤ r
    · exact (ite_eq_left h).trans <| by
        rw [radialRetraction_of_norm_le h, hagree (le_antisymm h h₁)]
    · exact (ite_eq_right h).trans (congr_arg f (radialRetraction_of_norm_le h₂))

end
