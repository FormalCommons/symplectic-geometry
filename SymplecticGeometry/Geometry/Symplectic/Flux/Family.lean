/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Flux.Hamiltonian
import SymplecticGeometry.Geometry.Symplectic.Flux.Kernel
import Mathlib.Topology.Separation.CompletelyRegular
import SymplecticGeometry.Geometry.Manifold.SmoothSingular.Period
import SymplecticGeometry.Geometry.Symplectic.Flux.Countable

/-!
# Smooth paths of Hamiltonian diffeomorphisms

Let `σ` be a closed two-form on a closed manifold `M`. This file shows that a
diffeotopy `φ_t` all of whose maps are Hamiltonian diffeomorphisms of `σ` is a Hamiltonian
diffeotopy (McDuff–Salamon, Proposition 10.2.12).

The argument goes through the countability of the flux group `Γ_σ = TauCeti.fluxGroup σ`. For
`T ∈ [0, 1]`, the truncation `t ↦ φ_{T t}` ends at the Hamiltonian diffeomorphism `φ_T`, which
is also the end of a Hamiltonian diffeotopy, of zero flux. So the flux of the truncation lies in
`Γ_σ` (`TauCeti.flux_sub_flux_mem_fluxGroup`), and its period on each class of `H₁(M; ℤ)` is a
period of `σ` on `H₂(M; ℤ)`
(`TauCeti.homologyPeriod_mem_range_closedFormHomologyPeriod_of_mem_fluxGroup`). These form a
countable set (`TauCeti.countable_range_closedFormHomologyPeriod`). On the other hand, this
period is the integral over `[0, T]` of a continuous function of time
(`TauCeti.Diffeotopy.homologyPeriod_flux_truncate`), so it is continuous in `T`, and it vanishes
at `T = 0`. A continuous function on `[0, 1]` with countably many values is constant, so every
truncation has zero flux, and `φ_t` is Hamiltonian by
`TauCeti.Diffeotopy.isHamiltonian_of_forall_flux_truncate_eq_zero`.

Nondegeneracy of `σ` is not used, and neither is connectedness of `M`.

## Main results

* `TauCeti.Diffeotopy.isHamiltonian_of_forall_timeSlice_mem_hamiltonianGroup`: a diffeotopy all
  of whose maps lie in the Hamiltonian group is Hamiltonian.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §10.2,
  Proposition 10.2.12.
-/

public section

open Set
open scoped Manifold ContDiff

namespace TauCeti.Diffeotopy

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {J : ModelWithCorners ℝ E H} [J.Boundaryless] {M : Type}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold J ∞ M] [T2Space M]

/-- **Smooth paths of Hamiltonian diffeomorphisms are Hamiltonian.** Let `σ` be a closed two-form
on a closed manifold. A diffeotopy `φ_t` such that every `φ_t` is a Hamiltonian
diffeomorphism of `σ` is a Hamiltonian diffeotopy of `σ`. -/
theorem isHamiltonian_of_forall_timeSlice_mem_hamiltonianGroup [CompactSpace M]
    {σ : closedForms J M 2} {Φ : Diffeotopy J ∞ M}
    (h : ∀ t, Φ.timeSlice t ∈ SmoothForm.hamiltonianGroup σ.val) :
    Φ.IsHamiltonian σ.val := by
  have hΦ (t : unitInterval) : Φ.timeSlice t ∈ SmoothForm.diffeomorphStabilizer σ.val :=
    (SmoothForm.hamiltonianGroup_le_isotopyStabilizer.trans
      SmoothForm.isotopyStabilizer_le_diffeomorphStabilizer) (h t)
  -- The flux of every truncation lies in the flux group.
  have hmem (T : unitInterval) : (Φ.truncate T).flux σ (SmoothForm.final_mem_diffeomorphStabilizer
      (SmoothForm.timeSlice_truncate_mem_diffeomorphStabilizer hΦ T)) ∈ fluxGroup σ := by
    obtain ⟨Ψ, hΨ, hΨT⟩ := SmoothForm.mem_hamiltonianGroup.mp (h T)
    have := flux_sub_flux_mem_fluxGroup (SmoothForm.timeSlice_truncate_mem_diffeomorphStabilizer
      hΦ T) hΨ.timeSlice_mem_diffeomorphStabilizer ((Φ.final_truncate T).trans hΨT.symm)
    rwa [hΨ.flux_eq_zero, sub_zero] at this
  refine isHamiltonian_of_forall_flux_truncate_eq_zero hΦ fun T ↦
    deRhamCohomology.homologyPeriod_injective ?_
  rw [map_zero]
  ext c
  -- The period on `c` of the flux of the truncation at time `S`, as an integral over `[0, S]`.
  set F : unitInterval → ℝ := fun S ↦ ∫ t in (0 : ℝ)..S, homologyPeriodHom
    (SmoothTwoForm.interiorₗ σ.val (Φ.smoothVelocity (projIcc 0 1 zero_le_one t)) :
      RoughForm J M ℝ 1) c
  have hFc : Continuous F :=
    (intervalIntegral.continuous_primitive (fun _ _ ↦
      (continuous_homologyPeriodHom_interiorₗ_smoothVelocity hΦ c).intervalIntegrable _ _) 0).comp
      continuous_subtypeVal
  have hrange : range F ⊆ range (closedFormHomologyPeriod σ) := by
    rintro _ ⟨S, rfl⟩
    have := homologyPeriod_mem_range_closedFormHomologyPeriod_of_mem_fluxGroup (hmem S) c
    rwa [homologyPeriod_flux_truncate hΦ S c] at this
  have hsub := Set.Countable.isTotallyDisconnected
    (countable_range_closedFormHomologyPeriod σ) _ hrange
    (isPreconnected_range hFc)
  rw [homologyPeriod_flux_truncate hΦ T c, AddMonoidHom.zero_apply]
  have h0 : F 0 = 0 := intervalIntegral.integral_same
  exact (hsub (mem_range_self T) (mem_range_self 0)).trans h0

end TauCeti.Diffeotopy

end
