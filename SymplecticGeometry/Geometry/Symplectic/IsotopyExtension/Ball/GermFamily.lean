/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.IsotopyExtension.Ball.Basic
import SymplecticGeometry.Analysis.Calculus.FDeriv.Equiv
import SymplecticGeometry.Geometry.Symplectic.IsotopyExtension.Ball.Comp
import SymplecticGeometry.Geometry.Symplectic.IsotopyExtension.Ball.Parametric
import SymplecticGeometry.Geometry.Symplectic.IsotopyExtension.Ball.Polar
import SymplecticGeometry.Geometry.Symplectic.IsotopyExtension.Ball.Rescaling
import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Basic
import SymplecticGeometry.Topology.MetricSpace.Tube
import TauCeti.Geometry.Manifold.ContMDiff.ContinuousLinearEquiv

/-!
# Realizing a family of symplectic germs by symplectomorphisms of a ball

Let `κ` be a smooth family over `[0, 1]` of symplectic embeddings of a closed ball `B(δ)`,
`0 < δ`, of `StdSpace (Fin n)` into itself, with the standard form `ω₀`, each fixing `0`. For
every `0 < r` there are `0 < ε` and a jointly smooth family `χ` over `[0, 1]` of symplectic
embeddings of `B(r)`, each mapping `B(r)` onto itself, with `χ_t = κ_t` on `B(ε)`, and `χ_t` the
identity whenever `κ_t` is the identity on `B(δ)`
(`SymplecticGeometry.IsSymplecticBallFamily.exists_symplectomorphism_family_eq_of_map_zero`).
This is the core of the second part of McDuff–Salamon, Proposition 7.1.22.

The proof assembles earlier steps:

1. The polar decomposition of the derivatives `dκ_t(0)` gives linear isometries `U_t` and a
   two-parameter family `Q` of linear symplectic maps
   (`SymplecticGeometry.IsSymplecticBallFamily.exists_polar_fderiv_zero`).
2. The family `θ_t = κ_t ∘ U_t⁻¹` is rescaled to a two-parameter family `G (t, s)` of symplectic
   embeddings of a smaller ball, from the identity at `s = 0` to `θ_t` at `s = 1`
   (`SymplecticGeometry.IsSymplecticBallFamily.exists_rescaling_family`).
3. Near `0` the family `G` stays in the open ball `B°(r)`, and is extended there by compactly
   supported Hamiltonian diffeotopies `Φ_t`
   (`SymplecticGeometry.exists_isCompactlySupportedHamiltonian_param_apply_eq`).
4. `χ_t = Φ_t (1, ·) ∘ U_t`. Each `Φ_t (1, ·)` preserves `ω₀` and fixes every point outside a
   compact subset of `B°(r)`, so `χ_t` is a symplectic embedding of `B(r)` onto itself
   (`SymplecticGeometry.IsSymplecticBallEmbedding.diffeotopy_comp`, Mathlib's `Set.image_perm`).

## Main results

* `SymplecticGeometry.IsSymplecticBallFamily.exists_symplectomorphism_family_eq_of_map_zero`:
  the family `χ` described above.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Proposition 7.1.22.
-/

public section

noncomputable section

open Set Function Metric
open scoped ContDiff Manifold

namespace SymplecticGeometry

open TauCeti

variable {n : ℕ}

/-- **Realizing a family of symplectic germs by symplectomorphisms of a ball.** Let `κ` be a
smooth family over `[0, 1]` of symplectic embeddings of `B(δ)`, `0 < δ`, into `StdSpace (Fin n)`
with `ω₀`, with `κ_t (0) = 0` for every `t`, and let `0 < r`. Then there are `0 < ε` and a map
`χ : [0, 1] × StdSpace (Fin n) → StdSpace (Fin n)`, smooth, such that for every `t`
* `χ_t` is a symplectic embedding of `B(r)` and maps `B(r)` onto itself;
* `χ_t = κ_t` on `B(ε)`;
* `χ_t` is the identity if `κ_t` is the identity on `B(δ)`. -/
theorem IsSymplecticBallFamily.exists_symplectomorphism_family_eq_of_map_zero {δ r : ℝ}
    (hδ : 0 < δ) (hr : 0 < r) {κ : unitInterval × StdSpace (Fin n) → StdSpace (Fin n)}
    (hκ : IsSymplecticBallFamily (stdForm (Fin n)).constSmooth δ κ) (hκ0 : ∀ t, κ (t, 0) = 0) :
    ∃ ε, 0 < ε ∧ ∃ χ : unitInterval × StdSpace (Fin n) → StdSpace (Fin n),
      ContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, StdSpace (Fin n))) 𝓘(ℝ, StdSpace (Fin n)) ∞ χ ∧
      (∀ t, IsSymplecticBallEmbedding (stdForm (Fin n)).constSmooth r fun z ↦ χ (t, z)) ∧
      (∀ t, (fun z ↦ χ (t, z)) '' closedBall 0 r = closedBall 0 r) ∧
      (∀ t, ∀ z ∈ closedBall 0 ε, χ (t, z) = κ (t, z)) ∧
      ∀ t, (∀ z ∈ closedBall 0 δ, κ (t, z) = z) → ∀ z, χ (t, z) = z := by
  set ω₀ := (stdForm (Fin n)).constSmooth
  -- Step 1: the polar decomposition of `dκ_t(0)`.
  obtain ⟨U, Q, hU, hQ, hUs, hQs, hQ1, hQ0, h1⟩ := hκ.exists_polar_fderiv_zero hδ
  set Uinv : ℝ → StdSpace (Fin n) →L[ℝ] StdSpace (Fin n) :=
    fun t ↦ ((U t).symm : StdSpace (Fin n) →L[ℝ] StdSpace (Fin n))
  have hUinv : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, StdSpace (Fin n) →L[ℝ] StdSpace (Fin n)) ∞ Uinv := by
    simpa only [Uinv, LinearIsometryEquiv.toContinuousLinearEquiv_symm] using
      ContMDiff.continuousLinearEquiv_symm (A := fun t ↦ (U t).toContinuousLinearEquiv)
        hU.contMDiff
  have hUinvs (t : unitInterval) (v w : StdSpace (Fin n)) :
      stdForm (Fin n) (Uinv t v) (Uinv t w) = stdForm (Fin n) v w := by
    simpa [Uinv] using (hUs t ((U t).symm v) ((U t).symm w)).symm
  -- Step 2: `θ_t = κ_t ∘ U_t⁻¹`, a family of symplectic embeddings of `B(δ / 2)`.
  set θ : unitInterval × StdSpace (Fin n) → StdSpace (Fin n) := fun p ↦ κ (p.1, Uinv p.1 p.2)
  have hδ2 : 0 < δ / 2 := half_pos hδ
  have hUball (t : ℝ) {z : StdSpace (Fin n)} {ρ : ℝ} (hz : z ∈ ball 0 ρ) : Uinv t z ∈ ball 0 ρ := by
    simpa [Uinv] using hz
  have hθ : IsSymplecticBallFamily ω₀ (δ / 2) θ := by
    obtain ⟨V, -, hδV, hκV⟩ := hκ.exists_contMDiffOn
    have hm : ContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, StdSpace (Fin n))) ((𝓡∂ 1).prod 𝓘(ℝ, StdSpace (Fin n)))
        ∞ fun p : unitInterval × StdSpace (Fin n) ↦ (p.1, Uinv p.1 p.2) :=
      contMDiff_fst.prodMk ((hUinv.comp (contMDiff_subtypeVal_Icc.comp
        contMDiff_fst)).clm_apply contMDiff_snd)
    refine (isSymplecticBallFamily_def _ _ _).2 ⟨⟨ball 0 δ, isOpen_ball,
      closedBall_subset_ball (half_lt_self hδ),
      hκV.comp hm.contMDiffOn fun p hp ↦ ⟨trivial, hδV (ball_subset_closedBall
        (hUball p.1 hp.2))⟩⟩, fun t ↦ ?_⟩
    exact (hκ.isSymplecticBallEmbedding t).comp_continuousLinearMap (hUinvs t) fun z hz ↦
      hUball t (closedBall_subset_ball (half_lt_self hδ) hz)
  have hθ0 (t : unitInterval) : θ (t, 0) = 0 := by simp [θ, hκ0]
  have hdθ (t : unitInterval) : fderiv ℝ (fun z ↦ θ (t, z)) 0 =
      (fderiv ℝ (fun z ↦ κ (t, z)) 0).comp (Uinv t) := by
    simpa [θ, Uinv, comp_def] using (U t).symm.comp_right_fderiv (f := fun z ↦ κ (t, z)) (x := 0)
  -- The rescaled two-parameter family `G`.
  obtain ⟨ρ, hρ, G, ⟨W, hWo, hρW, hGW⟩, hGfam, hG0, hG1, hGz, hGid⟩ :=
    hθ.exists_rescaling_family hδ2 hθ0 hQ (fun t s ↦ hQs t s) (fun t ↦ hQ1 t)
      fun t ↦ by rw [hdθ t]; exact hQ0 t
  -- Step 3: near `0`, `G` takes values in `B°(r)`, by the tube lemma.
  have hGc : ContinuousOn (fun q : (unitInterval × unitInterval) × StdSpace (Fin n) ↦
      G (q.1.1, q.1.2, q.2)) (univ ×ˢ W) :=
    hGW.continuousOn.comp (by fun_prop) fun q hq ↦ ⟨trivial, trivial, hq.2⟩
  obtain ⟨ε₀, hε₀, hε₀G⟩ := isCompact_univ.exists_prod_ball_subset (y := 0)
    (hGc.isOpen_inter_preimage (isOpen_univ.prod hWo) isOpen_ball) (by
      rintro ⟨p, z⟩ ⟨-, hz⟩
      obtain rfl : z = 0 := mem_singleton_iff.1 hz
      exact ⟨⟨trivial, hρW (mem_closedBall_self hρ.le)⟩,
        mem_preimage.2 (by rw [hGz]; exact mem_ball_self hr)⟩)
  set ε := min (ρ / 2) (ε₀ / 2)
  have hε : 0 < ε := lt_min (half_pos hρ) (half_pos hε₀)
  have hερ : ε < ρ := (min_le_left _ _).trans_lt (half_lt_self hρ)
  have hεG (t s : unitInterval) {z : StdSpace (Fin n)} (hz : z ∈ closedBall 0 ε) :
      G (t, s, z) ∈ ball 0 r :=
    mem_preimage.1 (hε₀G (mk_mem_prod (mem_univ (t, s)) (closedBall_subset_ball
      ((min_le_right _ _).trans_lt (half_lt_self hε₀)) hz))).2
  -- The Hamiltonian extension `Φ` of `G` inside `B°(r)`.
  obtain ⟨Φ, K, -, hKr, hΦH, hΦs, hΦK, hΦG, hΦid⟩ :=
    exists_isCompactlySupportedHamiltonian_param_apply_eq
      (SymplecticForm.isSymplectic_constSmooth _)
      (by rw [finrank_stdSpace, Fintype.card_fin]) hρ hερ
      (hGW.mono (prod_mono subset_rfl (prod_mono subset_rfl
        (ball_subset_closedBall.trans hρW))))
      hGfam isOpen_ball fun t s z hz ↦ hεG t s hz
  -- Step 4: `χ_t = Φ_t (1, ·) ∘ U_t`.
  set χ : unitInterval × StdSpace (Fin n) → StdSpace (Fin n) := fun p ↦ Φ p.1 (1, U p.1 p.2)
  refine ⟨ε, hε, χ, ?_, fun t ↦ ?_, fun t ↦ ?_, fun t z hz ↦ ?_, fun t ht z ↦ ?_⟩
  · exact hΦs.comp ((contMDiff_fst.prodMk contMDiff_const).prodMk
      ((hU.contMDiff.comp (contMDiff_subtypeVal_Icc.comp contMDiff_fst)).clm_apply contMDiff_snd))
  · exact (SymplecticForm.IsSymplectomorphism.isSymplecticBallEmbedding
      (e := (U t).toContinuousLinearEquiv) (SymplecticForm.isSymplectomorphism_iff.2 (hUs t))
      r).diffeotopy_comp ((Diffeotopy.isCompactlySupportedHamiltonian_iff.1 (hΦH t)).1 1)
  · have hχ : (fun z ↦ χ (t, z)) = ((Φ t).timeSlice 1).toEquiv ∘ U t := by
      funext z
      simp [χ, Diffeotopy.timeSlice_apply]
    rw [hχ, image_comp, LinearIsometryEquiv.image_closedBall, map_zero]
    refine image_perm fun y hy ↦ ?_
    by_contra hyr
    have hfix := hΦK t 1 y fun hyK ↦ hyr (ball_subset_closedBall (hKr hyK))
    exact hy (by simpa [Diffeotopy.timeSlice_apply] using hfix)
  · have hz' : U t z ∈ closedBall 0 ε := by simpa using hz
    have h := hΦG t 1 (U t z) hz'
    rw [hG0, hG1] at h
    simpa [χ, θ, Uinv] using h
  · have hd : fderiv ℝ (fun z ↦ κ (t, z)) 0 = 1 := by
      rw [Filter.EventuallyEq.fderiv_eq (f := id)
        (Filter.eventually_of_mem (closedBall_mem_nhds 0 hδ) ht)]
      exact fderiv_id
    obtain ⟨hU1, hQ1'⟩ := h1 t hd
    have hUz (z : StdSpace (Fin n)) : (U t).symm z = z := (U t).symm_apply_eq.2 (by simp [hU1])
    have hθid : ∀ z ∈ closedBall 0 (δ / 2), θ (t, z) = z := fun z hz ↦ by
      simpa [θ, Uinv, hUz] using ht z (closedBall_subset_closedBall (half_le_self hδ.le) hz)
    have h := hΦid t (fun s z hz ↦ by
      rw [hG0, hGid t hθid (fun s ↦ hQ1' s) s z (ball_subset_closedBall hz)]) 1 (U t z)
    simpa [χ, hU1] using h

end SymplecticGeometry

end
