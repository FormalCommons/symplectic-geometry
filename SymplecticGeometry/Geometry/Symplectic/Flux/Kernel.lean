/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Diffeomorphism.Diffeotopy.Truncate
public import SymplecticGeometry.Geometry.Symplectic.Flux.Hamiltonian
public import TauCeti.Geometry.Manifold.DeRham.FiniteDimensional
public import TauCeti.Geometry.Manifold.DeRham.HomologyPeriod
import TauCeti.Analysis.Calculus.IntervalIntegral.ParametricPrimitive
import TauCeti.Geometry.Manifold.Flow.Complete
import TauCeti.Geometry.Symplectic.Flux.Eulerian
import TauCeti.Geometry.Symplectic.Flux.OrderedFlow
import TauCeti.Geometry.Symplectic.Flux.Reparam
import TauCeti.Geometry.Symplectic.Flux.Trans
import SymplecticGeometry.Geometry.Diffeomorphism.Diffeotopy.OrderedFlow
import SymplecticGeometry.Geometry.Manifold.DeRham.Basic
import SymplecticGeometry.Geometry.Manifold.DeRham.HomologyPeriod
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.Basic
import SymplecticGeometry.Geometry.Manifold.SmoothTransition
import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.SymplecticIsotopy
import SymplecticGeometry.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Fluxes of truncations, and isotopies with zero flux

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
derivative of zero, hence zero (`ContinuousOn.eqOn_zero_of_forall_intervalIntegral_eq_zero`). Every
`ι_{X_t} σ` is then exact (Tau Ceti's
`TauCeti.mem_exactForms_one_iff_homologyPeriodHom_eq_zero`), so `φ` is Hamiltonian
(`TauCeti.Diffeotopy.isHamiltonian_iff_forall_interiorₗ_velocity_mem_exactForms`). This is the
way McDuff–Salamon pass from fluxes to Hamiltonian isotopies in the proofs of Theorem 10.2.5 and
Proposition 10.2.12.

When `H¹_dR(M)` is finite-dimensional, as on a closed manifold, the periods on Tau Ceti's period
classes `c_i`
(`TauCeti.deRhamCohomology.periodHomologyClass`) are the coordinates in the period-dual basis
`θ_i` (`TauCeti.deRhamCohomology.periodDualBasis`). So the flux of `φ` up to time `T` is
`∑ i, A i T • θ_i`, where `A i T = ∫₀ᵀ ⟨[ι_{X_t} σ], c_i⟩ dt`. The integrand is a smooth function
of `t ∈ [0, 1]` (`SymplecticGeometry.IsSmoothFamily.contMDiff_homologyPeriodHom`); if the velocity
vanishes near both ends, it is zero near both ends, so its extension to `ℝ` through the clamp
`Set.projIcc 0 1` is smooth, and so is `A i`. A reparametrization along a map constant near both
ends, such as Tau Ceti's `TauCeti.collaredFirstHalf`, has this property
(`TauCeti.Diffeotopy.eventually_velocity_reparam_eq_zero`). These are the time functions of the
ordered flow in McDuff–Salamon's proof of Theorem 10.2.5.

That theorem is the last part of this file. Let `σ` be symplectic and `M` closed, and let `φ_t`
have zero flux. After a reparametrization along `TauCeti.collaredFirstHalf`, which changes
neither the flux nor the homotopy class (`TauCeti.Diffeotopy.reparam_homotopic`), the velocity
vanishes near both ends. Take the time functions `A i` above, and symplectic vector fields `Y i`
with `[ι_{Y i} σ] = θ_i` (`TauCeti.SmoothTwoForm.IsNondegenerate.interiorClass_surjective`),
complete since `M` is compact. Let `ψ_t` be the ordered flow of the `Y i` along the times `A i`
(`TauCeti.orderedGlobalFlowDiffeotopy`). Its truncation at `T` is the ordered flow along
`t ↦ A i (T t)`, with flux `∑ i, A i T • θ_i`
(`TauCeti.Diffeotopy.flux_orderedGlobalFlowDiffeotopy`), so every truncation of
`t ↦ ψ_t⁻¹ ∘ φ_t` has zero flux, and this diffeotopy is Hamiltonian by the criterion above. Since
the flux of `φ` is zero, every `A i 1` vanishes, so `ψ` is a loop, homotopic to the constant
diffeotopy (`TauCeti.Diffeotopy.orderedGlobalFlowDiffeotopy_homotopic_refl`),
and `φ` is homotopic to `t ↦ ψ_t⁻¹ ∘ φ_t`. With Tau Ceti's
`TauCeti.mem_ker_endpointFlux_iff` and `TauCeti.hamiltonianGroup_subgroupOf_le_ker_endpointFlux`,
this identifies the kernel of the endpoint flux with the Hamiltonian group.

## Main results

* `TauCeti.Diffeotopy.homologyPeriod_flux_truncate`: the periods of the flux of the truncation at
  time `T` are the integrals over `[0, T]` of the periods of the contractions `ι_{X_t} σ`.
* `TauCeti.Diffeotopy.continuous_homologyPeriodHom_interiorₗ_smoothVelocity`: these periods of
  the contractions are continuous in time.
* `TauCeti.Diffeotopy.isHamiltonian_of_forall_flux_truncate_eq_zero`: a diffeotopy preserving
  `σ` all of whose truncations have zero flux is Hamiltonian.
* `TauCeti.Diffeotopy.exists_contDiff_flux_truncate_eq_sum_smul_periodDualBasis`: when
  `H¹_dR(M)` is finite-dimensional, if the velocity vanishes near both ends, the fluxes of the
  truncations are `∑ i, A i T • θ_i` for smooth functions `A i` with `A i 0 = 0`.
* `TauCeti.Diffeotopy.exists_isHamiltonian_homotopic_of_flux_eq_zero` (McDuff–Salamon,
  Theorem 10.2.5): on a closed symplectic manifold, a symplectic isotopy with zero flux is
  homotopic with fixed ends to a Hamiltonian one.
* `TauCeti.Diffeotopy.final_mem_hamiltonianGroup_of_flux_eq_zero`: its final map is Hamiltonian.
* `TauCeti.ker_endpointFlux`: the kernel of the endpoint flux is the Hamiltonian group.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §10.2.
-/

public section

open Set MeasureTheory Filter Module
open scoped Manifold ContDiff Topology

namespace TauCeti.Diffeotopy

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {J : ModelWithCorners ℝ E H} {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold J ∞ M] {σ : closedForms J M 2} {Φ : Diffeotopy J ∞ M}

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
          (SmoothForm.timeSlice_truncate_mem_diffeomorphStabilizer hΦ T))) c =
      ∫ t in (0 : ℝ)..T, homologyPeriodHom (SmoothTwoForm.interiorₗ σ.val
        (Φ.smoothVelocity (projIcc 0 1 zero_le_one t)) : RoughForm J M ℝ 1) c := by
  have hσ := (SmoothForm.isClosed_iff_mem_closedForms σ.val).2 σ.property
  have hΨ := SmoothForm.timeSlice_truncate_mem_diffeomorphStabilizer hΦ T
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

/-- **The periods of the contractions are continuous in time.** If every map of the diffeotopy
`φ_t` preserves the closed two-form `σ`, then for each class `c ∈ H₁(M; ℤ)` the period on `c` of
the contraction `ι_{X_t} σ`, with `X_t` the velocity, is a continuous function of real time `t`,
read through the projection of `ℝ` onto `[0, 1]`. -/
theorem continuous_homologyPeriodHom_interiorₗ_smoothVelocity
    (hΦ : ∀ t, Φ.timeSlice t ∈ SmoothForm.diffeomorphStabilizer σ.val)
    (c : ((singularChains ℤ).obj (.of M)).homology 1) :
    Continuous fun s : ℝ ↦ homologyPeriodHom (SmoothTwoForm.interiorₗ σ.val
      (Φ.smoothVelocity (projIcc 0 1 zero_le_one s)) : RoughForm J M ℝ 1) c :=
  (SymplecticGeometry.IsSmoothFamily.contMDiff_homologyPeriodHom
    (SymplecticGeometry.isSmoothFamily_interiorₗ σ.val Φ.contMDiff_smoothVelocity)
    (Φ.interiorₗ_smoothVelocity_mem_closedForms
      ((SmoothForm.isClosed_iff_mem_closedForms σ.val).2 σ.property) hΦ) c).continuous.comp
    continuous_projIcc

/-- **The Hamiltonian criterion by truncations.** If every map of the diffeotopy `φ_t` preserves
the closed two-form `σ`, and the truncation `t ↦ φ_{T t}` has zero flux for every `T ∈ [0, 1]`,
then `φ_t` is Hamiltonian. -/
theorem isHamiltonian_of_forall_flux_truncate_eq_zero
    (hΦ : ∀ t, Φ.timeSlice t ∈ SmoothForm.diffeomorphStabilizer σ.val)
    (h : ∀ T, (Φ.truncate T).flux σ (SmoothForm.final_mem_diffeomorphStabilizer
      (SmoothForm.timeSlice_truncate_mem_diffeomorphStabilizer hΦ T)) = 0) :
    Φ.IsHamiltonian σ.val := by
  have hσ := (SmoothForm.isClosed_iff_mem_closedForms σ.val).2 σ.property
  have hX := Φ.interiorₗ_smoothVelocity_mem_closedForms hσ hΦ
  refine (isHamiltonian_iff_forall_interiorₗ_velocity_mem_exactForms hΦ).2 fun t ↦ ?_
  rw [mem_exactForms_one_iff_homologyPeriodHom_eq_zero (hX t)]
  ext c
  -- The periods on `c` of the contractions, as a continuous function of real time.
  set g : ℝ → ℝ := fun s ↦ homologyPeriodHom (SmoothTwoForm.interiorₗ σ.val
    (Φ.smoothVelocity (projIcc 0 1 zero_le_one s)) : RoughForm J M ℝ 1) c
  have hg : Continuous g := continuous_homologyPeriodHom_interiorₗ_smoothVelocity hΦ c
  -- Its integrals over the intervals `[0, s]`, `s ∈ [0, 1]`, vanish, so it vanishes on `[0, 1]`.
  have hzero := hg.continuousOn.eqOn_zero_of_forall_intervalIntegral_eq_zero zero_lt_one
    fun s hs ↦ by
      have := homologyPeriod_flux_truncate hΦ ⟨s, hs⟩ c
      rw [h, map_zero, AddMonoidHom.zero_apply] at this
      exact this.symm
  simpa only [g, projIcc_val, Pi.zero_apply, AddMonoidHom.zero_apply] using hzero t.property

/-- **Smooth time functions for the fluxes of truncations.** Let `H¹_dR(M)` be
finite-dimensional, as it is when `M` is closed, let every map of the diffeotopy `φ_t` preserve
the closed two-form `σ`, and let its velocity vanish near both ends of the time interval.
Then there are smooth functions `A i : ℝ → ℝ`, one for each vector `θ_i` of the period-dual basis
of `H¹_dR(M)`, with `A i 0 = 0`, such that for every `T ∈ [0, 1]` the flux of the truncation
`t ↦ φ_{T t}` is `∑ i, A i T • θ_i`. -/
theorem exists_contDiff_flux_truncate_eq_sum_smul_periodDualBasis
    [FiniteDimensional ℝ (deRhamCohomology J M 1)]
    (hΦ : ∀ t, Φ.timeSlice t ∈ SmoothForm.diffeomorphStabilizer σ.val)
    (h₀ : ∀ᶠ t in 𝓝 0, Φ.velocity t = 0) (h₁ : ∀ᶠ t in 𝓝 1, Φ.velocity t = 0) :
    ∃ A : Fin (finrank ℝ (deRhamCohomology J M 1)) → ℝ → ℝ,
      (∀ i, ContDiff ℝ ∞ (A i)) ∧ (∀ i, A i 0 = 0) ∧
      ∀ T : unitInterval, (Φ.truncate T).flux σ (SmoothForm.final_mem_diffeomorphStabilizer
          (SmoothForm.timeSlice_truncate_mem_diffeomorphStabilizer hΦ T)) =
        ∑ i, A i T • deRhamCohomology.periodDualBasis J M i := by
  have hσ := (SmoothForm.isClosed_iff_mem_closedForms σ.val).2 σ.property
  have hX := Φ.interiorₗ_smoothVelocity_mem_closedForms hσ hΦ
  -- The `i`-th class coordinate of the contraction `ι_{X_t} σ`, as a function of real time.
  set g : Fin (finrank ℝ (deRhamCohomology J M 1)) → ℝ → ℝ := fun i s ↦
    homologyPeriodHom (SmoothTwoForm.interiorₗ σ.val
      (Φ.smoothVelocity (projIcc 0 1 zero_le_one s)) : RoughForm J M ℝ 1)
      (deRhamCohomology.periodHomologyClass J M i) with hg_def
  -- It vanishes near every real time whose clamp is a time near which the velocity vanishes.
  have hzero {s : ℝ} {e : unitInterval} (hs : projIcc 0 1 zero_le_one s = e)
      (he : ∀ᶠ t in 𝓝 e, Φ.velocity t = 0) (i) : g i =ᶠ[𝓝 s] fun _ ↦ 0 := by
    filter_upwards [(continuous_projIcc.tendsto s).eventually (hs ▸ he)] with u hu
    have hv : Φ.smoothVelocity (projIcc 0 1 zero_le_one u) = 0 :=
      ContMDiffSection.ext fun y ↦ by simp [hu]
    simp only [hg_def]
    rw [hv, map_zero]
    simp
  -- It is smooth on `[0, 1]`, and zero near `(-∞, 0]` and `[1, ∞)`, hence smooth.
  have hg (i) : ContDiff ℝ ∞ (g i) := by
    have hc : ContDiffOn ℝ ∞ (g i) (Icc 0 1) := contMDiffOn_iff_contDiffOn.1
      ((SymplecticGeometry.IsSmoothFamily.contMDiff_homologyPeriodHom
        (SymplecticGeometry.isSmoothFamily_interiorₗ σ.val Φ.contMDiff_smoothVelocity) hX
        _).comp_contMDiffOn contMDiffOn_projIcc)
    refine contDiff_iff_contDiffAt.2 fun s ↦ ?_
    rcases le_or_gt s 0 with hs | hs
    · exact contDiffAt_const.congr_of_eventuallyEq (hzero (projIcc_of_le_left _ hs) h₀ i)
    rcases lt_or_ge s 1 with hs' | hs'
    · exact hc.contDiffAt (Icc_mem_nhds hs hs')
    · exact contDiffAt_const.congr_of_eventuallyEq (hzero (projIcc_of_right_le _ hs') h₁ i)
  refine ⟨fun i t ↦ ∫ s in (0 : ℝ)..t, g i s,
    fun i ↦ (intervalIntegral.contDiff_primitive_of_contDiff (n := ⊤) (hg i) 0).of_le
      le_self_add,
    fun i ↦ intervalIntegral.integral_same, fun T ↦ ?_⟩
  -- The coordinates of the flux in the period-dual basis are its periods on the period classes.
  rw [← (deRhamCohomology.periodDualBasis J M).sum_repr ((Φ.truncate T).flux σ _)]
  simp_rw [deRhamCohomology.periodDualBasis_repr_apply, homologyPeriod_flux_truncate hΦ, hg_def]


section Kernel

variable [CompactSpace M]

/-- **Symplectic isotopies with zero flux are homotopic to Hamiltonian ones.** Let `σ` be a
symplectic form on a closed manifold `M`, and let every map of the diffeotopy `φ_t` preserve `σ`.
If `φ_t` has zero flux, then it is homotopic, with fixed ends, to a Hamiltonian diffeotopy. -/
theorem exists_isHamiltonian_homotopic_of_flux_eq_zero (hσ : SmoothTwoForm.IsNondegenerate σ.val)
    (hΦ : ∀ t, Φ.timeSlice t ∈ SmoothForm.diffeomorphStabilizer σ.val)
    (h : Φ.flux σ (SmoothForm.final_mem_diffeomorphStabilizer hΦ) = 0) :
    ∃ Ψ : Diffeotopy J ∞ M, Ψ.IsHamiltonian σ.val ∧ Φ.Homotopic Ψ := by
  have hσc := (SmoothForm.isClosed_iff_mem_closedForms σ.val).2 σ.property
  -- The flux does not see which proof that the final map preserves `σ` it is given.
  have hfl {Φ₁ Φ₂ : Diffeotopy J ∞ M} (e : Φ₁ = Φ₂) (h₁ h₂) : Φ₁.flux σ h₁ = Φ₂.flux σ h₂ := by
    subst e
    rfl
  -- Reparametrize `Φ` so that its velocity vanishes near both ends.
  set Φ' := Φ.reparam (collaredFirstHalf le_rfl)
  have hΦ' (t) : Φ'.timeSlice t ∈ SmoothForm.diffeomorphStabilizer σ.val := by
    rw [timeSlice_reparam, ← Diffeomorph.inv_def, ← Diffeomorph.mul_def]
    exact mul_mem (hΦ _) (inv_mem (hΦ _))
  have hhom : Φ.Homotopic Φ' :=
    (Φ.reparam_homotopic (collaredFirstHalf_zero le_rfl) (collaredFirstHalf_one le_rfl)).symm
  -- The time functions of the fluxes of the truncations of `Φ'`; they vanish at time `1`.
  obtain ⟨A, hA, hA₀, hAT⟩ := exists_contDiff_flux_truncate_eq_sum_smul_periodDualBasis hΦ'
    (Φ.eventually_velocity_reparam_eq_zero (by simp) (eventually_collaredFirstHalf_eq_zero _))
    (Φ.eventually_velocity_reparam_eq_zero (by simp) (eventually_collaredFirstHalf_eq_one _))
  have hA₁ (i) : A i 1 = 0 := by
    have key := hAT 1
    rw [hfl (truncate_one Φ') _ (SmoothForm.final_mem_diffeomorphStabilizer hΦ'),
      flux_reparam Φ σ (collaredFirstHalf_zero le_rfl) (collaredFirstHalf_one le_rfl)
        (SmoothForm.final_mem_diffeomorphStabilizer hΦ), h] at key
    exact Fintype.linearIndependent_iff.1 (deRhamCohomology.periodDualBasis J M).linearIndependent
      (fun i ↦ A i 1) key.symm i
  -- Symplectic fields `Y i` whose contractions `ι_{Y i} σ` represent the period-dual basis.
  choose Y hY using fun i ↦ hσ.interiorClass_surjective (deRhamCohomology.periodDualBasis J M i)
  have hc (i) : IsCompleteVectorField (Y i).val :=
    isCompleteVectorField_of_compactSpace ((Y i).val.contMDiff.of_le (by simp))
  -- The ordered flow `θ` of the `Y i` along the times `A i`, a loop since every `A i 1 = 0`.
  set θ := orderedGlobalFlowDiffeotopy le_top (fun i ↦ (Y i).val) (fun i ↦ (Y i).val.contMDiff)
    hc A hA hA₀
  have hθ := timeSlice_orderedGlobalFlowDiffeotopy_mem_diffeomorphStabilizer hσc
    (fun i ↦ (Y i).property) hc A hA hA₀
  have hΨ := SmoothForm.timeSlice_trans_mem_diffeomorphStabilizer hΦ'
    (SmoothForm.timeSlice_symm_mem_diffeomorphStabilizer hθ)
  refine ⟨Φ'.trans θ.symm, isHamiltonian_of_forall_flux_truncate_eq_zero hΨ fun T ↦ ?_, ?_⟩
  · -- The truncations of `θ` have the fluxes of the truncations of `Φ'`.
    have hθT := SmoothForm.timeSlice_truncate_mem_diffeomorphStabilizer hθ T
    rw [hfl (truncate_trans _ _ T) _ (SmoothForm.final_mem_diffeomorphStabilizer
        (SmoothForm.timeSlice_trans_mem_diffeomorphStabilizer
          (SmoothForm.timeSlice_truncate_mem_diffeomorphStabilizer hΦ' T)
          (SmoothForm.timeSlice_truncate_mem_diffeomorphStabilizer
            (SmoothForm.timeSlice_symm_mem_diffeomorphStabilizer hθ) T))),
      flux_trans _ _ σ (SmoothForm.final_mem_diffeomorphStabilizer
          (SmoothForm.timeSlice_truncate_mem_diffeomorphStabilizer hΦ' T))
        (SmoothForm.final_mem_diffeomorphStabilizer
          (SmoothForm.timeSlice_truncate_mem_diffeomorphStabilizer
            (SmoothForm.timeSlice_symm_mem_diffeomorphStabilizer hθ) T)),
      hfl (truncate_symm θ T) _ (SmoothForm.final_mem_diffeomorphStabilizer
        (SmoothForm.timeSlice_symm_mem_diffeomorphStabilizer hθT)),
      flux_symm _ σ (SmoothForm.final_mem_diffeomorphStabilizer hθT),
      hfl (truncate_orderedGlobalFlowDiffeotopy le_top _ _ hc A hA hA₀ T) _
        (SmoothForm.final_mem_diffeomorphStabilizer
          (timeSlice_orderedGlobalFlowDiffeotopy_mem_diffeomorphStabilizer hσc
            (fun i ↦ (Y i).property) hc _ _ _)),
      flux_orderedGlobalFlowDiffeotopy σ (fun i ↦ (Y i).property), hAT T]
    simp [hY]
  · -- `θ` is homotopic to the constant diffeotopy, so `Φ' = (Φ' θ⁻¹) θ` is homotopic to `Φ' θ⁻¹`.
    have key := (Homotopic.refl (Φ'.trans θ.symm)).trans_congr
      (orderedGlobalFlowDiffeotopy_homotopic_refl le_top (fun i ↦ (Y i).val.contMDiff) hc hA hA₀
        hA₁)
    rw [trans_assoc, symm_trans_self, trans_refl, trans_refl] at key
    exact hhom.trans key le_rfl

/-- **Symplectic isotopies with zero flux end at Hamiltonian diffeomorphisms.** Let `σ` be a
symplectic form on a closed manifold `M`, and let every map of the diffeotopy `φ_t` preserve `σ`.
If `φ_t` has zero flux, then its final map `φ_1` lies in the Hamiltonian group of `σ`. -/
theorem final_mem_hamiltonianGroup_of_flux_eq_zero (hσ : SmoothTwoForm.IsNondegenerate σ.val)
    (hΦ : ∀ t, Φ.timeSlice t ∈ SmoothForm.diffeomorphStabilizer σ.val)
    (h : Φ.flux σ (SmoothForm.final_mem_diffeomorphStabilizer hΦ) = 0) :
    Φ.final ∈ SmoothForm.hamiltonianGroup σ.val := by
  obtain ⟨Ψ, hΨ, hhom⟩ := exists_isHamiltonian_homotopic_of_flux_eq_zero hσ hΦ h
  rw [hhom.final_eq]
  exact SmoothForm.final_mem_hamiltonianGroup hΨ

end Kernel

end TauCeti.Diffeotopy

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {J : ModelWithCorners ℝ E H} {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold J ∞ M] [J.Boundaryless] [FiniteDimensional ℝ E] [T2Space M] [CompactSpace M]

/-- **The kernel of the endpoint flux is the Hamiltonian group.** For a symplectic form `σ` on a
closed manifold `M`, an element of the isotopy stabilizer of `σ` has trivial endpoint flux exactly
when it lies in the Hamiltonian group of `σ`. -/
theorem ker_endpointFlux {σ : closedForms J M 2} (hσ : SmoothTwoForm.IsNondegenerate σ.val) :
    (endpointFlux σ).ker =
      (SmoothForm.hamiltonianGroup σ.val).subgroupOf (SmoothForm.isotopyStabilizer σ.val) := by
  refine le_antisymm (fun φ hφ ↦ ?_) (hamiltonianGroup_subgroupOf_le_ker_endpointFlux σ)
  obtain ⟨Φ, hΦ, hfin, h⟩ := mem_ker_endpointFlux_iff.1 hφ
  rw [Subgroup.mem_subgroupOf, ← hfin]
  exact Diffeotopy.final_mem_hamiltonianGroup_of_flux_eq_zero hσ hΦ h

end TauCeti

end
