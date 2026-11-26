/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.IsotopyExtension.Velocity
public import SymplecticGeometry.Geometry.Symplectic.Flux.CompactSupport
public import TauCeti.Geometry.Manifold.DeRham.HomologyPeriod
public import TauCeti.Topology.Homotopy.Extension.NDRPair
import SymplecticGeometry.Geometry.Symplectic.IsotopyExtension.Cohomological.Primitive
import SymplecticGeometry.Geometry.Symplectic.IsotopyExtension.Flow

/-!
# The symplectic isotopy extension theorem

Let `σ` be a symplectic form on `M`, `Q ⊆ M` a compact set with NDR data (`TauCeti.NDRPair`), `U`
an open set containing `Q`, and `φ` a smooth isotopy of `U` into `M` that starts at the inclusion
and whose slices pull `σ` back to its restriction to `U`. The first cohomology of `Q` is read
through singular homology, as additive maps `H₁(Q; ℤ) → ℝ`, and a de Rham class of `M` restricts
to `Q` through its periods.

* `TauCeti.SmoothIsotopy.exists_diffeotopy_mem_diffeomorphStabilizer_eqOn`: if `M` is compact and
  every additive map `H₁(Q; ℤ) → ℝ` is the restriction of a de Rham class of `M`, then near `Q`
  the isotopy `φ` is the restriction of a diffeotopy of `M` whose slices preserve `σ`.
* `TauCeti.SmoothIsotopy.exists_hasHamiltonian_eqOn`: if `H₁(Q; ℤ)` has no nonzero additive map
  to `ℝ`, then near `Q` the isotopy `φ` is the restriction of a compactly supported Hamiltonian
  diffeotopy of `M`, with no compactness of `M`.
* `TauCeti.SmoothIsotopy.exists_symplectic_extension_and_hamiltonian_extension`: both, for a
  compact `M`.

The proofs follow McDuff–Salamon, proof of Theorem 3.3.2. The velocity forms `α_t` of `φ` are
closed, since `φ` is symplectic. On a compact `M`, the hypothesis on `Q` gives a smooth family of
closed forms `β_t` on `M` with the periods of `α_t` on `H₁(Q; ℤ)`
(`SymplecticGeometry.exists_closedForms_periods_eq`); when `H₁(Q; ℤ)` has no nonzero map to `ℝ`,
`β = 0` has them. Then `α_t - φ_t^* β_t = dh_t` on an open `V` with `Q ⊆ V ⊆ U`, for an `h` smooth
on `[0, 1] × V` (`SymplecticGeometry.exists_contMDiff_primitive_of_periods`). The restriction of
`φ` to `V` (`TauCeti.SmoothIsotopy.restrict`) has velocity forms `φ_t^* β_t + dh_t`, and the
extension by an ambient flow of `SymplecticGeometry.Geometry.Symplectic.IsotopyExtension.Flow`
applies on a compact neighbourhood of `Q` in `V`.

## Implementation notes

The isotopy starts at a map `f₀` with `f₀ x = x` for every `x`, that is at the inclusion of `U`.
Singular homology lives in `TopCat.{0}`, so `M : Type`. The form on `M` is called `σ` and not `ω`,
which is a token once the scope `ContDiff` is open.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §3.3,
  Theorem 3.3.2 and its proof.
-/

public section

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace TauCeti.SmoothIsotopy

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {σ : SmoothTwoForm I M} {U : Opens M} {f₀ f₁ : C^∞⟮I, U; I, M⟯}

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] in
/-- **Velocity forms of a restriction, corrected by a primitive.** Let `φ` be a smooth isotopy of
an open `U ⊆ M`, `V ⊆ U` open, `β_t` the slices of a form `Ω` on `[0, 1] × M`, and `h` a function on
`[0, 1] × V` such that `dh_t` is the restriction to `V` of `α_t - φ_t^* β_t`, where `α_t` are the
velocity forms of `φ`. Then the velocity forms of the restriction `ψ` of `φ` to `V` are
`ψ_t^* β_t + dh_t`. -/
theorem mpullback_prodMk_velocityForm_restrict_eq_add (φ : SmoothIsotopy f₀ f₁) {V : Opens M}
    (hVU : V ≤ U) (Ω : SmoothForm ((𝓡∂ 1).prod I) (unitInterval × M) ℝ 1)
    {h : unitInterval × V → ℝ} (t : unitInterval)
    (hdh : mextDeriv (RoughForm.ofFunction I fun x ↦ h (t, x)) =
      (SmoothForm.mpullback (Opens.inclusion hVU) (contMDiff_inclusion hVU)
        (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id)
            (φ.velocityForm σ) -
          SmoothForm.mpullback (fun x : U ↦ φ (t, x))
            (φ.contMDiff.comp (contMDiff_const.prodMk contMDiff_id))
            (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) Ω)) :
        RoughForm I V ℝ 1)) :
    (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id)
        ((φ.restrict hVU).velocityForm σ)).val =
      mpullback I I (fun x ↦ φ.restrict hVU (t, x))
          (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) Ω).val +
        mextDeriv (RoughForm.ofFunction I fun x ↦ h (t, x)) := by
  have hψ : (fun x ↦ φ.restrict hVU (t, x)) = (fun x : U ↦ φ (t, x)) ∘ Opens.inclusion hVU :=
    funext fun x ↦ restrict_apply φ hVU (t, x)
  have hc : (SmoothForm.mpullback (Opens.inclusion hVU) (contMDiff_inclusion hVU)
      (SmoothForm.mpullback (fun x : U ↦ φ (t, x))
        (φ.contMDiff.comp (contMDiff_const.prodMk contMDiff_id))
        (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) Ω)) :
        RoughForm I V ℝ 1) =
      mpullback I I ((fun x : U ↦ φ (t, x)) ∘ Opens.inclusion hVU)
        (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) Ω).val := by
    rw [SmoothForm.mpullback_mpullback, SmoothForm.coe_mpullback]
  rw [hdh, mpullback_prodMk_velocityForm_restrict, map_sub, Submodule.coe_sub, hψ, hc,
    add_sub_cancel]

/-- **Symplectic isotopy extension.** Let `σ` be a symplectic form on a compact manifold `M`, and
`Q ⊆ M` a compact set with NDR data such that every additive map `H₁(Q; ℤ) → ℝ` is the restriction
of the periods of a de Rham class of `M`. Let `φ` be a smooth isotopy of an open `U ⊇ Q` into `M`,
starting at the inclusion `f₀` of `U`, whose slices pull `σ` back to its restriction to `U`. Then
there are an open `N` with `Q ⊆ N ⊆ U` and a diffeotopy `Ψ` of `M` whose slices preserve `σ`, with
`Ψ_t x = φ_t x` for every `t` and every `x ∈ N`. -/
theorem exists_diffeotopy_mem_diffeomorphStabilizer_eqOn [CompactSpace M] (hσ : σ.IsSymplectic)
    {Q : Set M} (hQ : IsCompact Q) (hQr : Nonempty (NDRPair Q)) (hQU : Q ⊆ U)
    (φ : SmoothIsotopy f₀ f₁) (hf₀ : ∀ x, f₀ x = x)
    (hφ : φ.IsSymplectic (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ) σ)
    (hsurj : ∀ f : ((singularChains ℤ).obj (.of Q)).homology 1 →+ ℝ,
      ∃ c : deRhamCohomology I M 1, (deRhamCohomology.homologyPeriod c).comp
        (ContinuousMap.singularHomologyMap ℤ 1
          (⟨Subtype.val, continuous_subtypeVal⟩ : C(Q, M))).toAddMonoidHom = f) :
    ∃ N : Opens M, Q ⊆ N ∧ N ≤ U ∧ ∃ Ψ : Diffeotopy I ∞ M,
      (∀ t, Ψ.timeSlice t ∈ SmoothForm.diffeomorphStabilizer σ) ∧
      ∀ t, ∀ x : U, (x : M) ∈ N → Ψ (t, x) = φ (t, x) := by
  have hα := SymplecticGeometry.isSmoothFamily_mpullback_prodMk (φ.velocityForm σ)
  have hαcl (t : unitInterval) := (mem_closedForms I _).2
    (hφ.mextDeriv_mpullback_prodMk_velocityForm hσ.isClosed t)
  obtain ⟨β, hβ, hβcl, hper⟩ := SymplecticGeometry.exists_closedForms_periods_eq hQU hsurj hα hαcl
  obtain ⟨V, hQV, hVU, h, hh, hdh⟩ := SymplecticGeometry.exists_contMDiff_primitive_of_periods
    hQr.some hQU φ hf₀ hα hαcl hβ hβcl hper
  obtain ⟨Ω, hΩ⟩ := SymplecticGeometry.isSmoothFamily_def.1 hβ
  exact φ.exists_opens_forall_apply_eq_of_forall_isCompact hf₀ hVU hQ hQV fun K hK ↦
    (φ.restrict hVU).exists_diffeotopy_mem_diffeomorphStabilizer_forall_apply_eq hσ rfl hK
      (β := Ω) (fun t ↦ by rw [hΩ]; exact (mem_closedForms I _).1 (hβcl t)) hh
      fun t ↦ mpullback_prodMk_velocityForm_restrict_eq_add φ hVU Ω t (by rw [hdh, hΩ])

/-- **Hamiltonian isotopy extension.** Let `σ` be a symplectic form on a Hausdorff σ-compact
manifold `M`, and `Q ⊆ M` a compact set with NDR data such that `H₁(Q; ℤ)` has no nonzero
additive map to `ℝ`. Let `φ` be a smooth isotopy of an open `U ⊇ Q` into `M`, starting at the
inclusion `f₀` of `U`, whose slices pull `σ` back to its restriction to `U`. Then there are an
open `N` with `Q ⊆ N ⊆ U` and a compactly supported Hamiltonian diffeotopy `Ψ` of `M` with
`Ψ_t x = φ_t x` for every `t` and every `x ∈ N`: there are a compact `K` and a Hamiltonian `F` of
`Ψ`, read along the motion, with `F (y, t) = 0` and `Ψ_t y = y` for `y ∉ K`. -/
theorem exists_hasHamiltonian_eqOn [SigmaCompactSpace M] (hσ : σ.IsSymplectic) {Q : Set M}
    (hQ : IsCompact Q) (hQr : Nonempty (NDRPair Q)) (hQU : Q ⊆ U)
    (φ : SmoothIsotopy f₀ f₁) (hf₀ : ∀ x, f₀ x = x)
    (hφ : φ.IsSymplectic (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ) σ)
    (hQ1 : Subsingleton (((singularChains ℤ).obj (.of Q)).homology 1 →+ ℝ)) :
    ∃ N : Opens M, Q ⊆ N ∧ N ≤ U ∧ ∃ (Ψ : Diffeotopy I ∞ M) (F : M × unitInterval → ℝ)
      (K : Set M), IsCompact K ∧ Ψ.IsCompactlySupportedHamiltonian σ ∧ Ψ.HasHamiltonian σ F ∧
      (∀ p, p.1 ∉ K → F p = 0) ∧ (∀ t, ∀ y ∉ K, Ψ (t, y) = y) ∧
      ∀ t, ∀ x : U, (x : M) ∈ N → Ψ (t, x) = φ (t, x) := by
  have hα := SymplecticGeometry.isSmoothFamily_mpullback_prodMk (φ.velocityForm σ)
  have hαcl (t : unitInterval) := (mem_closedForms I _).2
    (hφ.mextDeriv_mpullback_prodMk_velocityForm hσ.isClosed t)
  obtain ⟨V, hQV, hVU, h, hh, hdh⟩ := SymplecticGeometry.exists_contMDiff_primitive_of_periods
    hQr.some hQU φ hf₀ hα hαcl (SymplecticGeometry.isSmoothFamily_const 0)
    (fun _ ↦ zero_mem _) fun _ ↦ Subsingleton.elim _ _
  have h0 (t : unitInterval) : SmoothForm.mpullback (Prod.mk t)
      (contMDiff_const.prodMk contMDiff_id) (0 : SmoothForm ((𝓡∂ 1).prod I) (unitInterval × M) ℝ 1)
      = 0 := map_zero _
  obtain ⟨N, hQN, hNU, Ψ, ⟨F, K, hK, hΨ, hF, hFK, hΨK⟩, happly⟩ :=
    φ.exists_opens_forall_apply_eq_of_forall_isCompact hf₀ hVU hQ hQV
      (R := fun Ψ ↦ ∃ (F : M × unitInterval → ℝ) (K : Set M),
        IsCompact K ∧ Ψ.IsCompactlySupportedHamiltonian σ ∧ Ψ.HasHamiltonian σ F ∧
        (∀ p, p.1 ∉ K → F p = 0) ∧ ∀ t, ∀ y ∉ K, Ψ (t, y) = y) fun L hL ↦ by
      obtain ⟨Ψ, F, K, hK, hΨ, hF, hFK, hΨK, happly⟩ :=
        (φ.restrict hVU).exists_hasHamiltonian_forall_apply_eq hσ rfl hL hh fun t ↦ by
          rw [mpullback_prodMk_velocityForm_restrict_eq_add φ hVU 0 t (by rw [hdh, h0]), h0,
            ZeroMemClass.coe_zero, mpullback_zero, zero_add]
      exact ⟨Ψ, ⟨F, K, hK, hΨ, hF, hFK, hΨK⟩, happly⟩
  exact ⟨N, hQN, hNU, Ψ, F, K, hK, hΨ, hF, hFK, hΨK, happly⟩

/-- **The symplectic isotopy extension theorem.** Let `σ` be a symplectic form on a compact
manifold `M`, `Q ⊆ M` a compact set with NDR data, and `φ` a smooth isotopy of an open `U ⊇ Q`
into `M`, starting at the inclusion `f₀` of `U`, whose slices pull `σ` back to its restriction to
`U`. If every additive map `H₁(Q; ℤ) → ℝ` is the restriction of the periods of a de Rham class of
`M`, then near `Q` the isotopy `φ` is the restriction of a diffeotopy of `M` whose slices preserve
`σ`. If `H₁(Q; ℤ)` has no nonzero additive map to `ℝ`, then near `Q` it is the restriction of a
compactly supported Hamiltonian diffeotopy of `M`.

Milestone: *Symplectic isotopy extension*. -/
theorem exists_symplectic_extension_and_hamiltonian_extension [CompactSpace M]
    (hσ : σ.IsSymplectic) {Q : Set M} (hQ : IsCompact Q) (hQr : Nonempty (NDRPair Q))
    (hQU : Q ⊆ U) (φ : SmoothIsotopy f₀ f₁) (hf₀ : ∀ x, f₀ x = x)
    (hφ : φ.IsSymplectic (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ) σ) :
    ((∀ f : ((singularChains ℤ).obj (.of Q)).homology 1 →+ ℝ,
      ∃ c : deRhamCohomology I M 1, (deRhamCohomology.homologyPeriod c).comp
        (ContinuousMap.singularHomologyMap ℤ 1
          (⟨Subtype.val, continuous_subtypeVal⟩ : C(Q, M))).toAddMonoidHom = f) →
      ∃ N : Opens M, Q ⊆ N ∧ N ≤ U ∧ ∃ Ψ : Diffeotopy I ∞ M,
        (∀ t, Ψ.timeSlice t ∈ SmoothForm.diffeomorphStabilizer σ) ∧
        ∀ t, ∀ x : U, (x : M) ∈ N → Ψ (t, x) = φ (t, x)) ∧
    (Subsingleton (((singularChains ℤ).obj (.of Q)).homology 1 →+ ℝ) →
      ∃ N : Opens M, Q ⊆ N ∧ N ≤ U ∧ ∃ (Ψ : Diffeotopy I ∞ M) (F : M × unitInterval → ℝ)
        (K : Set M), IsCompact K ∧ Ψ.IsCompactlySupportedHamiltonian σ ∧ Ψ.HasHamiltonian σ F ∧
        (∀ p, p.1 ∉ K → F p = 0) ∧ (∀ t, ∀ y ∉ K, Ψ (t, y) = y) ∧
        ∀ t, ∀ x : U, (x : M) ∈ N → Ψ (t, x) = φ (t, x)) :=
  ⟨exists_diffeotopy_mem_diffeomorphStabilizer_eqOn hσ hQ hQr hQU φ hf₀ hφ,
    exists_hasHamiltonian_eqOn hσ hQ hQr hQU φ hf₀ hφ⟩

end TauCeti.SmoothIsotopy

end
