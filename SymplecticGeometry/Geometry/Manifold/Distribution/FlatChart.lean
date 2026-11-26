/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.Distribution.FlatChart
public import TauCeti.Geometry.Manifold.Diffeomorph.NormedSpace
import SymplecticGeometry.Geometry.Manifold.IsManifold.InteriorBoundary
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic

/-!
# Flat charts of a distribution into a product

Let `D` be a smooth involutive distribution of rank `k` on a boundaryless finite-dimensional
manifold `M`, and let `F₁ × F₂` be a product of normed spaces with `dim F₁ = k` and
`dim M = k + dim F₂`. Around every point `x` there is a partial diffeomorphism
`Φ : M → F₁ × F₂` with `Φ x = 0`, whose target contains the open unit ball, and whose derivative
at each point `y` of its source carries `D y` onto the vectors with second component `0`
(`TauCeti.IsInvolutiveDistribution.exists_flatPartialDiffeomorph`).

It is Tau Ceti's Frobenius theorem `TauCeti.IsInvolutiveDistribution.exists_flatChart`, read in
coordinates adapted to the flat subspace: split the model space along that subspace, identify the
two factors with `F₁` and `F₂`, and translate and rescale (Tau Ceti's `Diffeomorph.smulAdd`) so
that the point goes to `0` and the unit ball lies in the target. The flat chart is read as a
partial diffeomorphism into the model space as in Tau Ceti's
`OpenPartialHomeomorph.toPartialDiffeomorphOfMemMaximalAtlas`, which asks for a boundaryless
model; here only `M` is boundaryless, and the target is open by
`OpenPartialHomeomorph.isOpen_extend_target_of_mem_maximalAtlas`.

## Main results

* `TauCeti.IsInvolutiveDistribution.exists_flatPartialDiffeomorph`: a flat partial
  diffeomorphism into `F₁ × F₂`, centred at a given point, whose target contains the unit ball.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Theorem 19.12
  (the Frobenius theorem)
-/

public section

noncomputable section

open Set Function Manifold Module
open scoped Manifold ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [BoundarylessManifold I M]
  {F₁ F₂ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]

/-- **Flat charts into a product.** Let `D` be a smooth involutive distribution of rank `k` on a
boundaryless manifold modelled on `E`, with `dim F₁ = k` and `dim E = k + dim F₂`. Every point `x`
is in the source of a partial diffeomorphism `Φ` into `F₁ × F₂` with `Φ x = 0`, whose target
contains the open unit ball, and such that at every `y` in its source a tangent vector `v` lies in
`D y` exactly when the second component of `dΦ_y v` is `0`. -/
theorem IsInvolutiveDistribution.exists_flatPartialDiffeomorph {k : ℕ}
    {D : Π x : M, Submodule ℝ (TangentSpace I x)} (hinv : IsInvolutiveDistribution I D)
    (hD : IsContMDiffDistribution I ∞ k D) (h₁ : finrank ℝ F₁ = k)
    (h₂ : finrank ℝ E = k + finrank ℝ F₂) (x : M) :
    ∃ Φ : PartialDiffeomorph I 𝓘(ℝ, F₁ × F₂) M (F₁ × F₂) ∞,
      x ∈ Φ.source ∧ Φ x = 0 ∧ Metric.ball 0 1 ⊆ Φ.target ∧
        ∀ y ∈ Φ.source, ∀ v : TangentSpace I y,
          (mfderiv I 𝓘(ℝ, F₁ × F₂) Φ y v).2 = 0 ↔ v ∈ D y := by
  -- A flat chart `e` of `D` at `x`: `d(I ∘ e)` carries `D` onto `W`.
  obtain ⟨e, W, he, hxe, hW, hflat⟩ :=
    hinv.exists_flatChart (m := ⊤) le_top (n := ∞) (by simp) hD
      (BoundarylessManifold.isInteriorPoint (I := I) (x := x))
  -- A splitting `A : E ≃ F₁ × F₂` that carries `W` onto the first factor.
  obtain ⟨C, hWC⟩ := W.exists_isCompl
  have hC : finrank ℝ C = finrank ℝ F₂ := by
    have := Submodule.finrank_add_eq_of_isCompl hWC
    omega
  let A : E ≃L[ℝ] F₁ × F₂ :=
    (Submodule.prodEquivOfIsCompl W C hWC).symm.toContinuousLinearEquiv.trans
      ((ContinuousLinearEquiv.ofFinrankEq (hW.trans h₁.symm)).prodCongr
        (ContinuousLinearEquiv.ofFinrankEq hC))
  have hA (z : E) : (A z).2 = 0 ↔ z ∈ W := by
    simp only [A, ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.prodCongr_apply,
      LinearEquiv.coe_toContinuousLinearEquiv', ContinuousLinearEquiv.map_eq_zero_iff,
      Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero]
  -- `I ∘ e` as a partial diffeomorphism into `E`. Its target is open because `M` has no boundary
  -- (Tau Ceti's `toPartialDiffeomorphOfMemMaximalAtlas` asks the model `I` to be boundaryless).
  let κ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞ :=
    { toPartialEquiv := e.extend I
      open_source := e.isOpen_extend_source
      open_target := e.isOpen_extend_target_of_mem_maximalAtlas (by simp) he
      contMDiffOn_toFun := by simpa only [e.extend_source] using e.contMDiffOn_extend he
      contMDiffOn_invFun := by
        simpa only [PartialEquiv.invFun_as_coe, e.extend_target'] using contMDiffOn_extend_symm he }
  have hκ : (κ : M → E) = I ∘ e := e.extend_coe
  have hxκ : x ∈ κ.source := by simpa [κ] using hxe
  -- `Φ` is `κ` followed by the affine map `z ↦ ε⁻¹ • A (z - κ x)`, with `ε` small enough.
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (A.toHomeomorph.isOpenMap _ κ.open_target)
    (A (κ x)) (mem_image_of_mem _ (κ.map_source hxκ))
  let G : E ≃ₘ^∞⟮𝓘(ℝ, E), 𝓘(ℝ, F₁ × F₂)⟯ F₁ × F₂ :=
    (A.toContDiffDiffeomorph ∞).trans
      (Diffeomorph.smulAdd ∞ ε⁻¹ (-(ε⁻¹ • A (κ x))) (inv_ne_zero hε.ne'))
  have hG (z : E) : G z = ε⁻¹ • (A z - A (κ x)) := by simp [G, sub_eq_add_neg]
  have hGs (v) : G.symm v = A.symm (ε • v + A (κ x)) := by
    simp [G, smul_add, smul_smul, hε.ne']
  let Φ := κ.trans G.toPartialDiffeomorph
  have hΦ : (Φ : M → F₁ × F₂) = (fun z ↦ ε⁻¹ • (A z - A (κ x))) ∘ (I ∘ e) := by
    ext1 y; simp [Φ, hG, hκ]
  refine ⟨Φ, by simpa [Φ] using hxκ, by simp [hΦ, ← hκ], fun v hv ↦ ?_, fun y hy v ↦ ?_⟩
  · have hv' : ε • v + A (κ x) ∈ Metric.ball (A (κ x)) ε := by
      rw [mem_ball_zero_iff] at hv
      simpa [norm_smul, abs_of_pos hε] using mul_lt_of_lt_one_right hε hv
    obtain ⟨z, hz, hz'⟩ := hball hv'
    have : G.symm v ∈ κ.target := by rw [hGs, ← hz']; simpa using hz
    simpa [Φ] using this
  · have hye : y ∈ e.source := by simpa [Φ, κ] using hy
    have hd : MDifferentiableAt I 𝓘(ℝ, E) (I ∘ e) y := by
      rw [← hκ]
      exact κ.mdifferentiableAt (by simp) (by simpa [κ] using hye)
    have hg : HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, F₁ × F₂)
        (fun z ↦ ε⁻¹ • (A z - A (κ x))) ((I ∘ e) y) (ε⁻¹ • (A : E →L[ℝ] F₁ × F₂)) :=
      ((A.hasFDerivAt.sub_const _).const_smul ε⁻¹).hasMFDerivAt
    have hinj : Injective (mfderiv I 𝓘(ℝ, E) (I ∘ e) y) := by
      rw [← hκ]; exact (κ.isInvertible_mfderiv (by simp) (by simpa [κ] using hye)).injective
    rw [hΦ, (hg.comp y hd.hasMFDerivAt).mfderiv]
    -- The derivatives land in tangent spaces of normed spaces, which are the spaces themselves;
    -- `change` reads the composite as a plain composite, which `rw` cannot reach through them.
    change (ε⁻¹ • A (mfderiv I 𝓘(ℝ, E) (I ∘ e) y v)).2 = 0 ↔ _
    simp only [Prod.smul_snd, smul_eq_zero, inv_eq_zero, hε.ne', false_or]
    refine (hA _).trans ?_
    rw [← hflat y hye]
    exact ⟨fun ⟨w, hw, hwv⟩ ↦ hinj hwv ▸ hw, fun h ↦ ⟨v, h, rfl⟩⟩

end TauCeti
