/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Diffeomorphism.Diffeotopy.Truncate
public import SymplecticGeometry.Geometry.Symplectic.Flux.Hamiltonian
public import TauCeti.Geometry.Manifold.DeRham.HomologyPeriod
import TauCeti.Geometry.Symplectic.Flux.Eulerian
import SymplecticGeometry.Geometry.Manifold.DeRham.Basic
import SymplecticGeometry.Geometry.Manifold.DeRham.HomologyPeriod
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.Basic
import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.SymplecticIsotopy

/-!
# Fluxes of truncations and the Hamiltonian criterion

Let `σ` be a closed two-form on a manifold `M` and `φ_t`, `t ∈ [0, 1]`, a diffeotopy all of whose
maps preserve `σ`, with velocity `X_t`. For `T ∈ [0, 1]` the truncation `Φ.truncate T`
(`t ↦ φ_{T t}`) runs through `φ` up to time `T`. This file computes the periods of its flux on
`H₁(M; ℤ)`: on a class `c`, the period is `∫₀ᵀ ⟨[ι_{X_t} σ], c⟩ dt`. In period coordinates, the
flux of `φ` up to time `T` is thus an integral over `[0, T]` of a continuous function of time.

The flux of the truncation is the class of its Eulerian flux form `∫₀¹ ι_{T X_{T t}} σ dt`
(Tau Ceti's `TauCeti.Diffeotopy.flux_eq_mk_eulerianFluxForm`, with the velocity of the truncation
from `TauCeti.Diffeotopy.smoothVelocity_truncate`). Its periods are the time integrals of the
periods of the contractions
(`SymplecticGeometry.IsSmoothFamily.homologyPeriodHom_eq_intervalIntegral`), and the substitution
`s = T t` gives the integral over `[0, T]`.

As a consequence, if every truncation of `φ` has zero flux, then every period of every
`ι_{X_t} σ` vanishes: a continuous function whose integrals over every `[0, T]` vanish is the
derivative of zero, hence zero. Every `ι_{X_t} σ` is then exact (Tau Ceti's
`TauCeti.mem_exactForms_one_iff_homologyPeriodHom_eq_zero`), so `φ` is Hamiltonian
(`TauCeti.Diffeotopy.isHamiltonian_iff_forall_interiorₗ_velocity_mem_exactForms`). This is the
way McDuff–Salamon pass from fluxes to Hamiltonian isotopies in the proofs of Theorem 10.2.5 and
Proposition 10.2.12.

## Main results

* `TauCeti.Diffeotopy.homologyPeriod_flux_truncate`: the periods of the flux of the truncation at
  time `T` are the integrals over `[0, T]` of the periods of the contractions `ι_{X_t} σ`.
* `TauCeti.Diffeotopy.isHamiltonian_of_forall_flux_truncate_eq_zero`: a diffeotopy preserving
  `σ` all of whose truncations have zero flux is Hamiltonian.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §10.2.
-/

public section

open Set MeasureTheory Filter
open scoped Manifold ContDiff Topology

namespace TauCeti.Diffeotopy

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {J : ModelWithCorners ℝ E H} {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold J ∞ M] {σ : closedForms J M 2} {Φ : Diffeotopy J ∞ M}

/-- The maps of a truncation of a diffeotopy preserving `σ` preserve `σ`. -/
theorem timeSlice_truncate_mem_diffeomorphStabilizer
    (hΦ : ∀ t, Φ.timeSlice t ∈ SmoothForm.diffeomorphStabilizer σ.val) (T t : unitInterval) :
    (Φ.truncate T).timeSlice t ∈ SmoothForm.diffeomorphStabilizer σ.val := by
  rw [timeSlice_truncate]
  exact hΦ _

variable [J.Boundaryless] [FiniteDimensional ℝ E] [T2Space M]

/-- **Periods of the flux of a truncation.** Let every map of the diffeotopy `φ_t` preserve the
closed two-form `σ`, and let `X_t` be its velocity. On a class `c ∈ H₁(M; ℤ)`, the period of the
flux of the truncation `t ↦ φ_{T t}` is the integral over `[0, T]` of the periods of the
contractions `ι_{X_t} σ` on `c`. -/
theorem homologyPeriod_flux_truncate
    (hΦ : ∀ t, Φ.timeSlice t ∈ SmoothForm.diffeomorphStabilizer σ.val) (T : unitInterval)
    (c : ((singularChains ℤ).obj (.of M)).homology 1) :
    deRhamCohomology.homologyPeriod ((Φ.truncate T).flux σ
        (SmoothForm.final_mem_diffeomorphStabilizer
          (timeSlice_truncate_mem_diffeomorphStabilizer hΦ T))) c =
      ∫ t in (0 : ℝ)..T, homologyPeriodHom (SmoothTwoForm.interiorₗ σ.val
        (Φ.smoothVelocity (projIcc 0 1 zero_le_one t)) : RoughForm J M ℝ 1) c := by
  have hσ := (SmoothForm.isClosed_iff_mem_closedForms σ.val).2 σ.property
  have hΨ := timeSlice_truncate_mem_diffeomorphStabilizer hΦ T
  -- The periods of the contractions of `Φ`, as a function of real time.
  set g : ℝ → ℝ := fun s ↦ homologyPeriodHom (SmoothTwoForm.interiorₗ σ.val
    (Φ.smoothVelocity (projIcc 0 1 zero_le_one s)) : RoughForm J M ℝ 1) c
  -- The integrand of the truncation at time `t` is `T g (T t)`.
  have hstep (t : ℝ) (ht : t ∈ uIcc (0 : ℝ) 1) :
      homologyPeriodHom (SmoothTwoForm.interiorₗ σ.val ((Φ.truncate T).smoothVelocity
        (projIcc 0 1 zero_le_one t)) : RoughForm J M ℝ 1) c = T * g (T * t) := by
    rw [uIcc_of_le zero_le_one] at ht
    have hTt : (T * projIcc 0 1 zero_le_one t : unitInterval) =
        projIcc 0 1 zero_le_one (T * t) := by
      ext
      rw [Set.Icc.coe_mul, projIcc_of_mem _ ht,
        projIcc_of_mem _ (unitInterval.mul_mem T.property ht)]
    rw [smoothVelocity_truncate, map_smul, Submodule.coe_smul, homologyPeriodHom_smul,
      AddMonoidHom.smul_apply, smul_eq_mul, hTt]
  rw [(Φ.truncate T).flux_eq_mk_eulerianFluxForm σ hΨ, deRhamCohomology.homologyPeriod_mk,
    SymplecticGeometry.IsSmoothFamily.homologyPeriodHom_eq_intervalIntegral
      (SymplecticGeometry.isSmoothFamily_interiorₗ σ.val (Φ.truncate T).contMDiff_smoothVelocity)
      ((Φ.truncate T).interiorₗ_smoothVelocity_mem_closedForms hσ hΨ) (a := 0) (b := 1)
      (continuous_projIcc (h := zero_le_one))
      (((Φ.truncate T).isSmoothForm_eulerianFluxForm hΨ).of_le (by simp))
      ((Φ.truncate T).mextDeriv_eulerianFluxForm_eq_zero
        hσ hΨ)
      -- The two integrals differ only in reading the covectors over `TangentSpace J x` or over
      -- `E`, the model space that the time integral is taken in.
      (fun x ↦ by
        simp only [eulerianFluxForm_apply, SmoothTwoForm.coe_interiorₗ, coe_smoothVelocity]
        rfl),
    intervalIntegral.integral_congr hstep, intervalIntegral.integral_const_mul,
    intervalIntegral.mul_integral_comp_mul_left, mul_zero, mul_one]

/-- **The Hamiltonian criterion by truncations.** If every map of the diffeotopy `φ_t` preserves
the closed two-form `σ`, and the truncation `t ↦ φ_{T t}` has zero flux for every `T ∈ [0, 1]`,
then `φ_t` is Hamiltonian. -/
theorem isHamiltonian_of_forall_flux_truncate_eq_zero
    (hΦ : ∀ t, Φ.timeSlice t ∈ SmoothForm.diffeomorphStabilizer σ.val)
    (h : ∀ T, (Φ.truncate T).flux σ (SmoothForm.final_mem_diffeomorphStabilizer
      (timeSlice_truncate_mem_diffeomorphStabilizer hΦ T)) = 0) :
    Φ.IsHamiltonian σ.val := by
  have hσ := (SmoothForm.isClosed_iff_mem_closedForms σ.val).2 σ.property
  refine (isHamiltonian_iff_forall_interiorₗ_velocity_mem_exactForms hΦ).2 fun t ↦ ?_
  rw [mem_exactForms_one_iff_homologyPeriodHom_eq_zero
    (Φ.interiorₗ_smoothVelocity_mem_closedForms hσ hΦ t)]
  ext c
  -- The periods on `c` of the contractions, as a continuous function of real time.
  set g : ℝ → ℝ := fun s ↦ homologyPeriodHom (SmoothTwoForm.interiorₗ σ.val
    (Φ.smoothVelocity (projIcc 0 1 zero_le_one s)) : RoughForm J M ℝ 1) c
  have hg : Continuous g :=
    (SymplecticGeometry.IsSmoothFamily.contMDiff_homologyPeriodHom
      (SymplecticGeometry.isSmoothFamily_interiorₗ σ.val Φ.contMDiff_smoothVelocity)
      (Φ.interiorₗ_smoothVelocity_mem_closedForms hσ hΦ) c).continuous.comp continuous_projIcc
  -- Its integrals over the intervals `[0, s]`, `s ∈ [0, 1]`, vanish.
  have hint (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : ∫ u in (0 : ℝ)..s, g u = 0 := by
    have := homologyPeriod_flux_truncate hΦ ⟨s, hs⟩ c
    rw [h, map_zero, AddMonoidHom.zero_apply] at this
    exact this.symm
  -- So `g` vanishes on `(0, 1)`, as the derivative of these integrals, and then on `[0, 1]`.
  have hzero : EqOn g 0 (Ioo 0 1) := fun s hs ↦ by
    have hF : (fun r ↦ ∫ u in (0 : ℝ)..r, g u) =ᶠ[𝓝 s] fun _ ↦ 0 :=
      Filter.mem_of_superset (Ioo_mem_nhds hs.1 hs.2) fun r hr ↦ hint r (Ioo_subset_Icc_self hr)
    rw [← hg.deriv_integral g 0 s, hF.deriv_eq, deriv_const, Pi.zero_apply]
  have := hzero.of_subset_closure hg.continuousOn continuousOn_const Ioo_subset_Icc_self
    (closure_Ioo zero_ne_one).ge t.property
  simpa only [g, projIcc_val, Pi.zero_apply, AddMonoidHom.zero_apply] using this

end TauCeti.Diffeotopy

end
