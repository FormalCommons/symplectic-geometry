/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.WeightModel.NormalForm
public import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Basic
import TauCeti.Analysis.InnerProductSpace.PiL2
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv

/-!
# The weight chart of a Hamiltonian torus action, with period-one weights

Let a compact commutative Lie group `G`, such as a torus, act smoothly on a finite-dimensional
symplectic manifold `(M, σ)` without boundary, preserving `σ`, with a moment map `μ` in the
library's sign, `d⟨μ, ξ⟩ = -ι_{ξ_M} σ` (so that Tau Ceti's moment map is `-μ`), and let `p` be a
fixed point. This file reads Tau Ceti's weight chart
`TauCeti.SmoothTwoForm.IsMomentMap.exists_weightModelChart` in the library's conventions
(`SymplecticGeometry.exists_weightChart`):

* the chart goes from the model to `M`: it is the inverse of Tau Ceti's chart, composed with
  `EuclideanSpace.sumEquivProd`, and is defined on a round ball of `StdSpace (Fin n)`, centred at
  `0`, which it sends to `p`;
* it pulls `σ` back to `stdForm (Fin n)`, by `isSymplectomorphism_sumEquivProd`;
* the weights have period one: `αₖ = α^{TC}ₖ / 2π`, so that `χₖ (exp ξ) = e^{2π i αₖ(ξ)}`, and
  they lie in the character lattice, `αₖ(ξ) ∈ ℤ` whenever `exp ξ = 1`;
* `g` acts in the complex coordinates `z = complexToRealEuclidean (Fin n) u` by `uₖ ↦ χₖ(g) uₖ`;
* `μ(Φ z) = μ(p) + π Σₖ |zₖ|² αₖ`, where `|zₖ|² = xₖ(z)² + yₖ(z)²`.

Zero weights are allowed, and neither compactness of `M` nor isolatedness of `p` is assumed.

The proof of `TauCeti.weightRotation_arg_sumEquivProd_complexToRealEuclidean` follows the step of
`TauCeti.SymplecticForm.exists_continuousLinearEquiv_weightRotation` that computes the cosine and
sine of the argument of a unit complex number.

## References

* [A. Cannas da Silva, *Symplectic Toric Manifolds*][CannasdaSilva2001], Theorems 3.1.1–3.1.2
* [V. Guillemin, S. Sternberg, *Symplectic Techniques in Physics*][GuilleminSternberg1990],
  Theorems 22.1 and 32.1
-/

public section

noncomputable section

open Real
open scoped Manifold ContDiff

namespace TauCeti

/-- Read through `EuclideanSpace.sumEquivProd` and `complexToRealEuclidean`, the rotation of
`ℂ^ι` by the arguments of unit complex numbers `cₖ` is the multiplication `uₖ ↦ cₖ uₖ`. -/
theorem weightRotation_arg_sumEquivProd_complexToRealEuclidean {ι : Type*} [Fintype ι]
    (c : ι → Circle) (u : ι → ℂ) :
    weightRotation (fun k ↦ Complex.arg (c k))
        (EuclideanSpace.sumEquivProd (complexToRealEuclidean ι u)) =
      EuclideanSpace.sumEquivProd (complexToRealEuclidean ι fun k ↦ (c k : ℂ) * u k) := by
  have hcos (k : ι) : cos (Complex.arg (c k)) = (c k : ℂ).re := by
    rw [Complex.cos_arg (Circle.coe_ne_zero _), Circle.norm_coe, div_one]
  have hsin (k : ι) : sin (Complex.arg (c k)) = (c k : ℂ).im := by
    rw [Complex.sin_arg, Circle.norm_coe, div_one]
  ext k <;> simp [complexToRealEuclidean_apply, hcos, hsin]
  ring

end TauCeti

namespace SymplecticGeometry

open TauCeti

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M]
  {σ : SmoothTwoForm I' M}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [CommGroup G] [LieGroup I ∞ G] [T2Space G]
  [IsTopologicalGroup G] [CompactSpace G] [MulAction G M] [ContMDiffSMul I I' ∞ G M]
  {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-- **The weight chart at a fixed point, with period-one weights.** Let a compact commutative Lie
group `G`, with Lie algebra `𝔤 = E`, act smoothly on a finite-dimensional symplectic manifold
`(M, σ)` without boundary, preserving `σ`, with moment map `μ` in the sign
`d⟨μ, ξ⟩ = -ι_{ξ_M} σ`, that is, `-μ` is a moment map for Tau Ceti's `IsMomentMap`; and let `p`
be a fixed point. Then there are continuous characters `χₖ : G → S¹`, `k < n`, with weights
`αₖ ∈ 𝔤*` of period one, `χₖ (exp ξ) = e^{2π i αₖ(ξ)}`, lying in the character lattice
(`αₖ(ξ) ∈ ℤ` whenever `exp ξ = 1`), and a smooth partial diffeomorphism `Φ` from the ball of
radius `r > 0` about `0` in `StdSpace (Fin n)` onto a `G`-invariant open set of `M`, with
`Φ 0 = p`, such that

* in the complex coordinates `z = complexToRealEuclidean (Fin n) u`, `Φ` is equivariant for the
  action `uₖ ↦ χₖ(g) uₖ` of `g` on the ball;
* `Φ` pulls `σ` back to the standard form `stdForm (Fin n)`;
* `μ (Φ z) = μ p + π Σₖ (xₖ(z)² + yₖ(z)²) αₖ` on the ball.

Milestone: *Equivariant Darboux theorem and quadratic local moment maps*. -/
theorem exists_weightChart
    (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) fun x ↦ -μ x)
    (hσ : σ.IsSymplectic)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    {p : M} (hp : ∀ g : G, g • p = p) :
    ∃ (n : ℕ) (χ : Fin n → G →ₜ* Circle) (α : Fin n → StrongDual ℝ E)
      (Φ : PartialDiffeomorph 𝓘(ℝ, StdSpace (Fin n)) I' (StdSpace (Fin n)) M ∞) (r : ℝ),
      (∀ k (ξ : GroupLieAlgebra I G),
        χ k (mulInvariantExp (I := I) ξ) = Circle.exp (2 * π * α k ξ)) ∧
      (∀ k (ξ : GroupLieAlgebra I G), mulInvariantExp (I := I) ξ = 1 → ∃ m : ℤ, α k ξ = m) ∧
      0 < r ∧ Φ.source = Metric.ball 0 r ∧ Φ 0 = p ∧
      (∀ g : G, ∀ x ∈ Φ.target, g • x ∈ Φ.target) ∧
      (∀ g : G, ∀ u : Fin n → ℂ, complexToRealEuclidean (Fin n) u ∈ Φ.source →
        complexToRealEuclidean (Fin n) (fun k ↦ (χ k g : ℂ) * u k) ∈ Φ.source ∧
        Φ (complexToRealEuclidean (Fin n) fun k ↦ (χ k g : ℂ) * u k) =
          g • Φ (complexToRealEuclidean (Fin n) u)) ∧
      (∀ z ∈ Φ.source, ∀ v w : StdSpace (Fin n),
        σ.eval₂ (Φ z) (mfderiv 𝓘(ℝ, StdSpace (Fin n)) I' Φ z v)
          (mfderiv 𝓘(ℝ, StdSpace (Fin n)) I' Φ z w) = stdForm (Fin n) v w) ∧
      ∀ z ∈ Φ.source, ∀ ξ : GroupLieAlgebra I G,
        μ (Φ z) ξ = μ p ξ + π * ∑ k, α k ξ * (z.x k ^ 2 + z.y k ^ 2) := by
  obtain ⟨n, χ, β, chart, r, hβ, hβℤ, hpchart, hchartp, hr, htarget, hequiv, hform, -, hmom⟩ :=
    hμ.exists_weightModelChart hσ hG hp
  let A : StdSpace (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) :=
    EuclideanSpace.sumEquivProd.toContinuousLinearEquiv
  let Φ := (A.toPartialDiffeomorph (n := ∞)).trans chart.symm
  have hΦ : ∀ z, Φ z = chart.symm (A z) := fun z ↦ by
    rw [PartialDiffeomorph.coe_trans, ContinuousLinearEquiv.coe_toPartialDiffeomorph,
      Function.comp_apply]
  have hsrc : Φ.source = A ⁻¹' chart.target := by
    rw [PartialDiffeomorph.trans_source]; simp
  have htgt : Φ.target = chart.source := by
    rw [PartialDiffeomorph.trans_target]; simp
  have hA (z : StdSpace (Fin n)) (k : Fin n) : (A z).1 k = z.x k ∧ (A z).2 k = z.y k :=
    ⟨(EuclideanSpace.sumEquivProd_apply_fst z k).trans (StdSpace.x_apply z k).symm,
      (EuclideanSpace.sumEquivProd_apply_snd z k).trans (StdSpace.y_apply z k).symm⟩
  have hnorm (z : StdSpace (Fin n)) : ‖(A z).1‖ ^ 2 + ‖(A z).2‖ ^ 2 = ‖z‖ ^ 2 := by
    rw [StdSpace.norm_sq_eq_sum, Finset.sum_add_distrib, EuclideanSpace.norm_sq_eq,
      EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs, sq_abs, (hA z _).1, (hA z _).2]
  -- On the source, `chart ∘ Φ` is `A`.
  have hmem {z : StdSpace (Fin n)} (hz : z ∈ Φ.source) : A z ∈ chart.target := by
    rwa [hsrc] at hz
  have hchartΦ {z : StdSpace (Fin n)} (hz : z ∈ Φ.source) : chart (Φ z) = A z := by
    rw [hΦ]; exact chart.right_inv (hmem hz)
  have hΦsrc {z : StdSpace (Fin n)} (hz : z ∈ Φ.source) : Φ z ∈ chart.source := by
    rw [← htgt]; exact Φ.map_source hz
  let α : Fin n → StrongDual ℝ E := fun k ↦ (2 * π)⁻¹ • β k
  have hα (k : Fin n) (ξ : E) : α k ξ = (2 * π)⁻¹ * β k ξ := by
    simp only [α, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  have hβα (k : Fin n) (ξ : E) : β k ξ = 2 * π * α k ξ := by
    rw [hα, ← mul_assoc, mul_inv_cancel₀ (by positivity : (2 * π : ℝ) ≠ 0), one_mul]
  refine ⟨n, χ, α, Φ, r, fun k ξ ↦ by rw [hβ, hβα k ξ], fun k ξ hξ ↦ ?_, hr, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Integrality: `ξ / 2π` lies in Tau Ceti's period lattice.
    obtain ⟨m, hm⟩ := hβℤ k ((2 * π)⁻¹ • ξ) (by
      rwa [smul_smul, mul_inv_cancel₀ (by positivity : (2 * π : ℝ) ≠ 0), one_smul])
    refine ⟨m, ?_⟩
    rw [hα k ξ, ← hm]
    exact ((β k).map_smul ((2 * π)⁻¹) ξ).symm
  · ext z
    rw [hsrc, Set.mem_preimage, htarget, Set.mem_ofPred_eq, hnorm, mem_ball_zero_iff,
      sq_lt_sq₀ (norm_nonneg _) hr.le]
  · rw [hΦ, map_zero, ← hchartp]; exact chart.left_inv hpchart
  · intro g x hx
    rw [htgt] at hx ⊢; exact (hequiv g x hx).1
  · intro g u hu
    obtain ⟨h₁, h₂⟩ := hequiv g _ (hΦsrc hu)
    have hrot : A (complexToRealEuclidean (Fin n) fun k ↦ (χ k g : ℂ) * u k) =
        chart (g • Φ (complexToRealEuclidean (Fin n) u)) := by
      rw [h₂, hchartΦ hu]
      exact (weightRotation_arg_sumEquivProd_complexToRealEuclidean (fun k ↦ χ k g) u).symm
    refine ⟨?_, ?_⟩
    · rw [hsrc, Set.mem_preimage, hrot]; exact chart.map_source h₁
    · rw [hΦ, hrot]; exact chart.left_inv h₁
  · intro z hz v w
    -- `Φ` is `chart.symm ∘ A`, and `chart` undoes the differential of `chart.symm`.
    have hd (u : StdSpace (Fin n)) :
        mvfderiv I' chart (Φ z) (mfderiv 𝓘(ℝ, StdSpace (Fin n)) I' Φ z u) = A u := by
      have hc : (Φ : StdSpace (Fin n) → M) = chart.symm ∘ A := funext hΦ
      have h := chart.mfderiv_apply_mfderiv_symm_apply (by simp) (hmem hz) (A u)
      rw [mvfderiv_apply_eq_mfderiv_apply, hc,
        mfderiv_comp z (chart.symm.mdifferentiableAt (by simp) (by simpa using hmem hz))
          A.mdifferentiableAt, A.mfderiv_eq]
      -- The base point is `chart.symm (A z)` and the vector `d(chart.symm) (A u)`, unfolded
      -- through `Function.comp` and `ContinuousLinearMap.comp`, which `rw` cannot reach in the
      -- dependent tangent spaces.
      exact h
    rw [hform _ (hΦsrc hz), hd v, hd w]
    exact (SymplecticForm.isSymplectomorphism_iff.1 isSymplectomorphism_sumEquivProd) v w
  · -- Tau Ceti's weights are functionals on the model space `E` of `𝔤`; read `ξ` there, as
    -- tactics do not see through `GroupLieAlgebra I G`.
    intro z hz (ξ : E)
    have h := hmom (Φ z) (hΦsrc hz) ξ
    rw [hchartΦ hz] at h
    simp only [weightMomentMap_apply] at h
    simp only [(hA z _).1, (hA z _).2, hβα] at h
    have hs : ∑ i, 2 * π * α i ξ * (z.x i ^ 2 + z.y i ^ 2) =
        2 * (π * ∑ i, α i ξ * (z.x i ^ 2 + z.y i ^ 2)) := by
      rw [Finset.mul_sum, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ ↦ by ring
    rw [hs] at h
    rw [LinearMap.neg_apply (μ (Φ z)) ξ, LinearMap.neg_apply (μ p) ξ] at h
    linarith

end SymplecticGeometry

end
