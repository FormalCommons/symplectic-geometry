/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Blowup.Normalized.Class
public import SymplecticGeometry.Geometry.Symplectic.Manifold.FirstChernClass
import SymplecticGeometry.Geometry.Manifold.Complex.Blowup.ChernClass
import SymplecticGeometry.Geometry.Symplectic.IsotopyExtension.Ball.Comp
import SymplecticGeometry.Geometry.Symplectic.IsotopyExtension.Ball.Homogeneity

/-!
# Symplectic forms on the blowup from ball embeddings

Let `(M, σ)` be a connected symplectic manifold of real dimension `2(n + 1)`, normalized at
`p₀` by `hN : IsNormalizedAt σ J p₀ δ ψ₀`, so that the almost complex blowup
`Blowup hN.blowupChart` of `M` at `p₀` is defined, with blowdown `π` and exceptional class `e`
(`Blowup.exceptionalClass`). If `(M, σ)` contains a symplectic ball `B(l)`, `0 < l`, then the
blowup carries a symplectic form `τ` whose de Rham class is `π^*[σ] + π l² e` and whose first
Chern class is `π^* c₁(σ) - n e` (`exists_symplectic_class_firstChernClass`).

The proof follows McDuff–Salamon, Corollary 7.1.24:

1. extend the ball embedding to a slightly larger ball
   (`IsSymplecticBallEmbedding.exists_lt_isSymplecticBallEmbedding_eqOn`);
2. move it by a compactly supported Hamiltonian diffeotopy so that it agrees with the
   normalization `ψ₀` near `0` (`exists_hamiltonian_comp_eqOn`); it is then a normalized ball
   embedding of weight `l` (`IsNormalizedBallEmbedding`);
3. take the form `ω̃_{ψ,l,ε}` of the blowup (`IsNormalizedBallEmbedding.normalizedBlowupForm`),
   whose class is given by Theorem 7.1.21 (v)
   (`IsNormalizedBallEmbedding.deRhamHom_normalizedBlowupForm`).

For the first Chern class, which the book states as (7.1.31) without proof, Theorem 7.1.21 (vi)
(`IsNormalizedBallEmbedding.exists_path_compatible`) joins `ω̃_{ψ,l,ε}` to a form compatible with
the almost complex blowup `J̃` by a smooth family of symplectic forms. Along it the first Chern
class does not change (`IsSmoothFamily.firstChernClass_eq`), so it is `c₁(J̃)`, which
`Blowup.firstChernClass_tangent` computes.

The Chern class formula is (7.1.31) as the book states it, with `e` and `c₁` both taken in
Tau Ceti's integral convention, in which `e` restricts on the exceptional divisor `Z` to the
first Chern class of its normal bundle. Only the de Rham class changes sign: there the real image
of `e` is minus McDuff–Salamon's Poincaré dual of `Z`, so their `π^*[σ] - π l² PD(Z)` reads
`π^*[σ] + π l² e` (see `ERRATA.md` and
`IsNormalizedBallEmbedding.deRhamHom_normalizedBlowupForm`).

## Main results

* `SymplecticGeometry.exists_symplectic_class_firstChernClass`: a symplectic ball of radius `l`
  gives a symplectic form on the blowup in the class `π^*[σ] + π l² e`, with first Chern class
  `π^* c₁(σ) - n e`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §7.1,
  Corollary 7.1.24, (7.1.30) and (7.1.31).
-/

public section

open Set Metric Module
open scoped ContDiff Manifold

namespace SymplecticGeometry

open TauCeti

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Fin (n + 1) → ℂ) M]
  [IsManifold 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ M] [T2Space M]
  {σ : SmoothTwoForm 𝓘(ℝ, Fin (n + 1) → ℂ) M}
  {J : SmoothAlmostComplexStructure 𝓘(ℝ, Fin (n + 1) → ℂ) M} {p₀ : M} {δ : ℝ}
  {ψ₀ : StdSpace (Fin (n + 1)) → M}

/-- A symplectic embedding of a closed ball of positive radius `l` into a connected manifold
gives a normalized ball embedding of weight `l`, for a normalization `hN` of the symplectic
form: extend it to a larger ball, then move it onto `ψ₀` near `0` by a Hamiltonian
diffeotopy. -/
theorem IsNormalizedAt.exists_isNormalizedBallEmbedding [SigmaCompactSpace M]
    [PreconnectedSpace M] (hN : IsNormalizedAt σ J p₀ δ ψ₀) (hσ : σ.IsSymplectic) {l : ℝ}
    (hl : 0 < l) {ψ : StdSpace (Fin (n + 1)) → M} (hψ : IsSymplecticBallEmbedding σ l ψ) :
    ∃ (ψ' : StdSpace (Fin (n + 1)) → M) (r ε : ℝ), IsNormalizedBallEmbedding hN ψ' r l ε := by
  have hdim : finrank ℝ (Fin (n + 1) → ℂ) = 2 * (n + 1) := by
    simp [Module.finrank_pi_fintype, mul_comm]
  obtain ⟨r, hlr, ψ₁, hψ₁, -⟩ := hψ.exists_lt_isSymplecticBallEmbedding_eqOn hσ.isClosed hl
  obtain ⟨Φ, ρ, hρ, hΦ, hΦψ, -⟩ := exists_hamiltonian_comp_eqOn hσ hdim
    (lt_min (hl.trans hlr) hN.pos) (hψ₁.mono (min_le_left r δ))
    (hN.isSymplecticBallEmbedding.mono (min_le_right r δ))
  have hδ := hN.pos
  set ε := min (min ρ (δ / 2)) (min (1 / 2) ((r - l) / 2))
  have hερ : ε ≤ ρ := (min_le_left _ _).trans (min_le_left _ _)
  have hεδ : ε ≤ δ / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hε1 : ε ≤ 1 / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hεr : ε ≤ (r - l) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hε : 0 < ε := lt_min (lt_min hρ (by positivity)) (lt_min (by norm_num) (by linarith))
  refine ⟨fun z ↦ Φ (1, ψ₁ z), r, ε, isNormalizedBallEmbedding_def.2
    ⟨hψ₁.diffeotopy_comp
      ((Diffeotopy.isCompactlySupportedHamiltonian_iff.1 hΦ).1 1), hl, hε, by linarith,
      by linarith, by linarith, fun z hz ↦ ?_⟩⟩
  rw [← Diffeotopy.final_apply]
  exact hΦψ (closedBall_subset_closedBall hερ hz)

/-- **Ball embeddings give symplectic forms on the blowup** (McDuff–Salamon, Corollary 7.1.24,
with (7.1.30) and (7.1.31)). Let `σ` be a symplectic form on a connected, Hausdorff, second
countable, σ-compact manifold `M` modelled on `Fin (n + 1) → ℂ`, normalized at `p₀` by `hN`,
and let `ψ` be a symplectic embedding of the closed ball `B(l)`, `0 < l`. Then the blowup
`Blowup hN.blowupChart` of `M` at `p₀`, with blowdown `π`, carries a symplectic form `τ` such that
* the image under `TauCeti.deRhamHom` of its class is the pull-back by `π` of that of `σ`, plus
  `π l²` times the real image of the exceptional class `e = Blowup.exceptionalClass`;
* its first Chern class is `π^* c₁(σ) - n • e`, both computed with the complex model `G`.

The Chern class part is the book's formula as stated, with `e` and `c₁` in Tau Ceti's integral
convention, where `e` restricts on the exceptional divisor to the first Chern class of its normal
bundle. Only the de Rham class changes sign: by integration the real image of `e` is minus the
book's Poincaré dual of the divisor, so the book's `- π l²` term reads `+ π l² e` (see
`ERRATA.md`).

Milestone: *Ball embeddings give symplectic forms on the blowup*. -/
theorem exists_symplectic_class_firstChernClass [SecondCountableTopology M] [SigmaCompactSpace M]
    [PreconnectedSpace M]
    (G : Type*) [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
    [Fact (finrank ℝ (Fin (n + 1) → ℂ) = 2 * finrank ℂ G)]
    (hN : IsNormalizedAt σ J p₀ δ ψ₀) (hσ : σ.IsSymplectic) {l : ℝ} (hl : 0 < l)
    {ψ : StdSpace (Fin (n + 1)) → M} (hψ : IsSymplecticBallEmbedding σ l ψ) :
    ∃ (τ : SmoothTwoForm 𝓘(ℝ, Fin (n + 1) → ℂ) (Blowup hN.blowupChart)) (hτ : τ.IsSymplectic),
      deRhamHom 𝓘(ℝ, Fin (n + 1) → ℂ) (Blowup hN.blowupChart) 2
          (deRhamCohomology.mk _ 2 ⟨τ, hτ.isClosed.mem_closedForms⟩) =
        TopCat.singularCohomologyMap (TopCat.ofHom ⟨Blowup.blowdown hN.blowupChart,
            (Blowup.contMDiff_blowdown_real hN.blowupChart).continuous⟩) 2
          (deRhamHom 𝓘(ℝ, Fin (n + 1) → ℂ) M 2
            (deRhamCohomology.mk _ 2 ⟨σ, hσ.isClosed.mem_closedForms⟩)) +
        (Real.pi * l ^ 2) •
          (TopCat.of (Blowup hN.blowupChart)).singularCohomologyRealImageAddMonoidHom 2
            (Blowup.exceptionalClass hN.blowupChart) ∧
      hτ.isNondegenerate.firstChernClass G =
        TopCat.singularCohomologyMap (TopCat.ofHom (Blowup.blowdown hN.blowupChart)) 2
            (hσ.isNondegenerate.firstChernClass G) -
          n • Blowup.exceptionalClass hN.blowupChart := by
  obtain ⟨ψ', r, ε, hψ'⟩ := hN.exists_isNormalizedBallEmbedding hσ hl hψ
  have hh := BlowupModel.isBlowupProfile_blowupProfile hψ'.weight_pos hψ'.width_pos
  have hτ := hψ'.isSymplectic_normalizedBlowupForm hh hσ
  refine ⟨_, hτ, hψ'.deRhamHom_normalizedBlowupForm hh hσ, ?_⟩
  obtain ⟨τ, hτf, hτs, hτ0, hτ1⟩ := hψ'.exists_path_compatible hσ
  calc hτ.isNondegenerate.firstChernClass G = (hτs 0).isNondegenerate.firstChernClass G :=
        hτ.isNondegenerate.firstChernClass_congr G _ hτ0.symm
    _ = _ := by
      rw [hτf.firstChernClass_eq G fun t ↦ (hτs t).isNondegenerate,
        (hτs 1).isNondegenerate.firstChernClass_eq_of_compatible G hτ1,
        Blowup.firstChernClass_tangent, hσ.isNondegenerate.firstChernClass_eq_of_compatible G
          hN.compatible]

end SymplecticGeometry

end
