/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothSingular.Period
public import TauCeti.Geometry.Symplectic.Flux.Endpoint
public import TauCeti.Geometry.Symplectic.Flux.Sweep
import SymplecticGeometry.Geometry.Manifold.SmoothSingular.Period
import SymplecticGeometry.Geometry.Manifold.SmoothSingular.Rectangle
import TauCeti.Geometry.Manifold.DeRham.FiniteDimensional
import TauCeti.Geometry.Manifold.Instances.Icc
import TauCeti.Geometry.Manifold.SmoothApprox
import TauCeti.Geometry.Manifold.Topology
import TauCeti.Geometry.Symplectic.Flux.Reparam

/-!
# The flux group is countable

Let `σ` be a closed two-form on a manifold `M`. This file shows that the periods of the flux of a
loop of diffeomorphisms are periods of `σ` on `H₂(M; ℤ)`, and deduces that on a closed connected
manifold the flux group `Γ_σ = TauCeti.fluxGroup σ` is countable.

Let `φ` be a diffeotopy with `φ₁ = id` and `γ` a loop. Up to homotopy `γ` is smooth
(`Path.exists_homotopic_contMDiff_extend`). The period of the flux of `φ` on `γ` is the
`σ`-area swept by `γ` along `φ` (`TauCeti.Diffeotopy.period_flux_ofMul_eq_rectangleIntegral`).
Reparametrizing `φ` in time by Tau Ceti's `TauCeti.collaredFirstHalf`, which is constant near
both ends of the unit interval, changes neither the flux (`TauCeti.Diffeotopy.flux_reparam`) nor
the final map, and makes the swept map `(t, s) ↦ φ_t (γ s)` smooth on all of `ℝ²`. Since `φ` is
a loop and `γ` is closed, that map agrees on opposite edges of the unit square, so its area is a
period of `σ` (`TauCeti.rectangleIntegral_mem_range_closedFormHomologyPeriod`).

On a closed connected manifold, `H₁(M; ℤ)` is the abelianized fundamental group
(`TauCeti.HurewiczOne.hurewiczHomologyAddEquiv`), so the periods of every element of `Γ_σ` on
`H₁(M; ℤ)` lie in the countable set of periods of `σ`
(`TauCeti.countable_range_closedFormHomologyPeriod`). A class of `H¹_dR(M)` is determined by its
periods on finitely many integral classes (`TauCeti.deRhamCohomology.periodHomologyClass`), so
`Γ_σ` injects into a finite power of a countable set. This replaces the argument of
McDuff–Salamon through the local contractibility of the symplectomorphism group.

## Main results

* `TauCeti.Diffeotopy.period_flux_mem_range_closedFormHomologyPeriod`: the period of the flux of a
  loop of diffeomorphisms on a loop class is a period of `σ` on `H₂(M; ℤ)`.
* `TauCeti.countable_fluxGroup`: on a closed connected manifold the flux group is countable.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §10.2.
-/

public section

open Set
open scoped Manifold ContDiff

noncomputable section

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {J : ModelWithCorners ℝ E H} [J.Boundaryless] {M : Type}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold J ∞ M] [T2Space M]

namespace Diffeotopy

/-- Clamping the time to `[0, 1]` does not change the collared transition at twice the time. -/
private theorem collaredSmoothTransitionUnit_two_mul_projIcc (t : ℝ) :
    collaredSmoothTransitionUnit (2 * (projIcc (0 : ℝ) 1 zero_le_one t : ℝ)) =
      collaredSmoothTransitionUnit (2 * t) := by
  rw [coe_projIcc]
  rcases le_total t 0 with h | h
  · rw [max_eq_left (min_le_of_right_le h),
      collaredSmoothTransitionUnit_eq_zero_of_le (by norm_num),
      collaredSmoothTransitionUnit_eq_zero_of_le (by linarith)]
  rcases le_total t 1 with h' | h'
  · rw [min_eq_right h', max_eq_right h]
  · rw [min_eq_left h', max_eq_right zero_le_one,
      collaredSmoothTransitionUnit_eq_one_of_ge (by norm_num),
      collaredSmoothTransitionUnit_eq_one_of_ge (by linarith)]

variable [SigmaCompactSpace M]

/-- **Fluxes of loops have periods in the periods of `σ`.** Let `σ` be a closed two-form and `φ`
a diffeotopy whose final diffeomorphism is the identity. Then the period of the flux of `φ` on
each element of `π₁(M, x)` is the period of `σ` on some class of `H₂(M; ℤ)`. The time slices of
`φ` need not preserve `σ`. -/
theorem period_flux_mem_range_closedFormHomologyPeriod (σ : closedForms J M 2)
    (Φ : Diffeotopy J ∞ M) (hΦ : Φ.final ∈ SmoothForm.diffeomorphStabilizer σ.val)
    (h : Φ.final = 1) {x : M} (g : FundamentalGroup M x) :
    deRhamCohomology.period x (Φ.flux σ hΦ) (Additive.ofMul g) ∈
      range (closedFormHomologyPeriod σ) := by
  obtain ⟨p⟩ := g
  induction p using Path.Homotopic.Quotient.ind with | mk γ =>
  obtain ⟨γ', hγγ', hγ'⟩ := γ.exists_homotopic_contMDiff_extend (J := J) (⊤ : ℕ∞)
  set ρ := collaredFirstHalf (n := ∞) le_rfl
  set Ψ := Φ.reparam ρ
  have hΨapp (t : unitInterval) (y : M) : Ψ (t, y) = Φ (ρ t, y) :=
    Φ.reparam_apply_of_map_zero (collaredFirstHalf_zero _) _
  have hΨ₁ : Ψ.final = 1 := by
    ext y
    rw [final_apply, hΨapp, collaredFirstHalf_one, ← final_apply, h, Diffeomorph.one_apply]
  have hΨ : Ψ.final ∈ SmoothForm.diffeomorphStabilizer σ.val := hΨ₁ ▸ h ▸ hΦ
  rw [← Φ.flux_reparam σ (collaredFirstHalf_zero _) (collaredFirstHalf_one _) hΦ hΨ,
    show ({ asHom := .mk γ } : FundamentalGroup M x) = { asHom := .mk γ' } by
      rw [Path.Homotopic.Quotient.eq.mpr hγγ'],
    Ψ.period_flux_ofMul_eq_rectangleIntegral σ hΨ (hγ'.of_le (by simp))
      fun t ↦ (γ'.extend_extends' t).symm]
  -- With the collared time, the swept map is smooth on the whole plane.
  have hsw : Ψ.sweep γ'.extend =
      fun z ↦ Φ.cylinderMap (γ'.extend z.2, collaredSmoothTransitionUnit (2 * z.1)) := by
    ext z
    rw [sweep_apply, hΨapp, cylinderMap_apply]
    simp only [ρ, collaredFirstHalf_apply, collaredSmoothTransitionUnit_two_mul_projIcc]
  refine rectangleIntegral_mem_range_closedFormHomologyPeriod σ ?_ (fun s _ ↦ ?_) fun t _ ↦ ?_
  · rw [hsw]
    exact Φ.contMDiff_cylinderMap.comp ((hγ'.comp contDiff_snd.contMDiff).prodMk
      ((contMDiff_collaredSmoothTransitionUnit le_rfl).comp
        (contDiff_const.mul contDiff_fst).contMDiff))
  · rw [sweep_one, sweep_zero, hΨ₁, Diffeomorph.one_apply]
  · rw [sweep_apply, sweep_apply, γ'.extend_one, γ'.extend_zero]

end Diffeotopy

/-- **The flux group is countable.** On a closed connected manifold, the flux group `Γ_σ` of a
closed two-form `σ`, the set of fluxes of loops of diffeomorphisms preserving `σ`, is a countable
subset of `H¹_dR(M)`. -/
theorem countable_fluxGroup [CompactSpace M] [ConnectedSpace M] (σ : closedForms J M 2) :
    (fluxGroup σ : Set (deRhamCohomology J M 1)).Countable := by
  have := J.pathConnectedSpace M
  obtain ⟨x⟩ : Nonempty M := inferInstance
  have hper : ∀ c ∈ fluxGroup σ, ∀ a, deRhamCohomology.homologyPeriod c a ∈
      range (closedFormHomologyPeriod σ) := by
    intro c hc a
    obtain ⟨Φ, hΦ, h₁, rfl⟩ := mem_fluxGroup.mp hc
    obtain ⟨b, rfl⟩ := (HurewiczOne.hurewiczHomologyAddEquiv (X := .of M) x).surjective a
    obtain ⟨g, rfl⟩ := Group.Abelianization.exists_eq_ofMul_of b
    obtain ⟨φ, hφ⟩ := deRhamCohomology.mk_surjective J 1
      (Φ.flux σ (SmoothForm.final_mem_diffeomorphStabilizer hΦ))
    have := Φ.period_flux_mem_range_closedFormHomologyPeriod σ
      (SmoothForm.final_mem_diffeomorphStabilizer hΦ) h₁ g
    rw [← hφ] at this ⊢
    rwa [deRhamCohomology.homologyPeriod_mk, homologyPeriodHom_hurewiczHomologyAddEquiv,
      ← deRhamCohomology.period_mk]
  refine ((countable_pi fun _ ↦ countable_range_closedFormHomologyPeriod σ).preimage
    (deRhamCohomology.homologyPeriods_periodHomologyClass_bijective (I := J) (M := M)).1).mono
    fun c hc ↦ ?_
  simp only [mem_preimage, mem_ofPred_eq, deRhamCohomology.homologyPeriods_apply]
  exact fun i ↦ hper c hc _

end TauCeti

end
