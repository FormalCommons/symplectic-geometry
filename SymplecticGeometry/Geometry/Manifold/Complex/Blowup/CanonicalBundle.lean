/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.Blowup.Chart
public import TauCeti.Analysis.Normed.Module.Alternating.TopDegree

/-!
# The coordinate form pulled back by the blowdown

Let `c : BlowupChart M p₀` be a holomorphic chart of a complex manifold `M` of dimension `n + 1`
at `p₀`, and `π : Blowup c → M` the blowdown. For a chart `e` of a manifold modelled on
`E = ℂⁿ⁺¹` and a basis `b` of `E`, the coordinate form `dz₁ ∧ ⋯ ∧ dzₙ₊₁` of `e` at `x` is the
determinant form `b.continuousDet` pulled back by the differential of `e` at `x`; for the chart
`chartAt E x₀` this is Tau Ceti's `TauCeti.CanonicalBundle.coordForm`
(`TauCeti.CanonicalBundle.coordForm_eq_compContinuousLinearMap_mfderiv`).

This file computes the pull-back by `π` of the coordinate form of a second holomorphic chart `φ`
at `p₀`, in the chart `liftChart c φ` followed by `blowupModelChart i` of the blowup. In that
chart, `φ ∘ π` is the blowdown of the model read in the chart `i`,
`w ↦ (z i = w i, z j = w i * w j for j ≠ i)`, whose Jacobian determinant is `(w i) ^ n`
(`SymplecticGeometry.BlowupModel.det_fderiv_blowdown_blowupModelChart_symm`). So the pull-back
is `(w i) ^ n` times the coordinate form of the chart
(`SymplecticGeometry.Blowup.coordForm_blowdown`).
For `φ = c`, the lifted chart is `Blowup.lift c` over the source of `c`
(`SymplecticGeometry.Blowup.liftChart_self`), so the chart is `blowupModelChart i ∘ lift c`.

## Main results

* `SymplecticGeometry.BlowupModel.hasFDerivAt_blowdown_blowupModelChart_symm`: the derivative of
  the blowdown of the model read in the chart `i`.
* `SymplecticGeometry.BlowupModel.det_fderiv_blowdown_blowupModelChart_symm`: its Jacobian
  determinant is `(w i) ^ n`.
* `SymplecticGeometry.Blowup.coordForm_blowdown`: the pull-back by the blowdown of the coordinate
  form of `φ` is `(w i) ^ n` times the coordinate form of the chart `i` of the blowup.

## References

* [C. Schnell, lecture notes on complex manifolds][Schnell2024], Lemma 23.5.
* [P. Griffiths, J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978], Chapter 1,
  §4.
-/

public section

open Function Module
open scoped Manifold ContDiff

noncomputable section

namespace SymplecticGeometry

variable {n : ℕ}

namespace BlowupModel

/-- The blowdown of the model read in the chart `i`, `w ↦ w i • update w i 1`, has at `w` the
derivative `v ↦ w i • update v i 0 + v i • update w i 1`. -/
theorem hasFDerivAt_blowdown_blowupModelChart_symm (i : Fin (n + 1)) (w : Fin (n + 1) → ℂ) :
    HasFDerivAt (fun w ↦ ((blowupModelChart i).symm w).blowdown)
      (w i • (ContinuousLinearMap.id ℂ (Fin (n + 1) → ℂ) -
          (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 1) ↦ ℂ) i).smulRight
            (Pi.single i 1)) +
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 1) ↦ ℂ) i).smulRight
          (update w i 1)) w := by
  set A := ContinuousLinearMap.id ℂ (Fin (n + 1) → ℂ) -
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 1) ↦ ℂ) i).smulRight (Pi.single i 1)
  have hA : (fun w : Fin (n + 1) → ℂ ↦ update w i 1) = fun w ↦ A w + Pi.single i 1 := by
    ext w j
    by_cases h : j = i
    · subst h; simp [A]
    · simp [A, h]
  have hg : HasFDerivAt (fun w : Fin (n + 1) → ℂ ↦ update w i 1) A w :=
    hA ▸ (A.hasFDerivAt).add_const _
  simp_rw [blowdown_blowupModelChart_symm_apply]
  exact (hasFDerivAt_apply i w).smul hg

/-- **The Jacobian of the blowdown in a chart.** In the chart `i` of the model, the blowdown is
`w ↦ (z i = w i, z j = w i * w j for j ≠ i)`, and its Jacobian determinant is `(w i) ^ n`. -/
theorem det_fderiv_blowdown_blowupModelChart_symm (i : Fin (n + 1)) (w : Fin (n + 1) → ℂ) :
    LinearMap.det (fderiv ℂ (fun w ↦ ((blowupModelChart i).symm w).blowdown) w :
      (Fin (n + 1) → ℂ) →ₗ[ℂ] Fin (n + 1) → ℂ) = w i ^ n := by
  rw [(hasFDerivAt_blowdown_blowupModelChart_symm i w).fderiv, ← LinearMap.det_toMatrix',
    Matrix.det_succ_row _ i, Finset.sum_eq_single i (fun j _ hj ↦ by
      simp [LinearMap.toMatrix'_apply, hj]) (by simp)]
  have : (LinearMap.toMatrix' (((w i • (ContinuousLinearMap.id ℂ (Fin (n + 1) → ℂ) -
          (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 1) ↦ ℂ) i).smulRight
            (Pi.single i 1)) +
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 1) ↦ ℂ) i).smulRight
          (update w i 1)) : (Fin (n + 1) → ℂ) →L[ℂ] _) : (Fin (n + 1) → ℂ) →ₗ[ℂ] _)).submatrix
        i.succAbove i.succAbove = w i • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    ext a b
    by_cases hab : a = b
    · subst hab; simp [LinearMap.toMatrix'_apply, Fin.succAbove_ne]
    · simp [LinearMap.toMatrix'_apply, Fin.succAbove_ne, hab]
  rw [this]
  simp [LinearMap.toMatrix'_apply]

end BlowupModel

namespace Blowup

open BlowupModel

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Fin (n + 1) → ℂ) M]
  [IsManifold 𝓘(ℂ, Fin (n + 1) → ℂ) ω M] {p₀ : M} (c φ : BlowupChart (n := n) M p₀)
  [hc : Fact (c.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin (n + 1) → ℂ) ω M)]
  [hφ : Fact (φ.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin (n + 1) → ℂ) ω M)]
  {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℂ (Fin (n + 1) → ℂ))

/-- **The coordinate form pulled back by the blowdown.** Let `φ` be a holomorphic chart of `M` at
the centre, and `χ` the chart `liftChart c φ` followed by `blowupModelChart i` of the blowup,
with coordinates `w`. At a point `z` of the source of `χ`, the coordinate form of `φ` at the
blowdown of `z`, pulled back by the differential of the blowdown, is `(w i) ^ n` times the
coordinate form of `χ` at `z`; here the coordinate form of a chart is the determinant form of
the basis `b` pulled back by its differential. -/
theorem coordForm_blowdown (i : Fin (n + 1)) {z : Blowup c}
    (hz : z ∈ ((liftChartPartialDiffeomorph c φ).toOpenPartialHomeomorph.trans
      (blowupModelChart i)).source) :
    (b.continuousDet.compContinuousLinearMap (mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ)
        𝓘(ℂ, Fin (n + 1) → ℂ) φ (blowdown c z))).compContinuousLinearMap
        (mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) (blowdown c) z) =
      (blowupModelChart i (liftChart c φ z) i) ^ n •
        b.continuousDet.compContinuousLinearMap
          (mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ)
            ((liftChartPartialDiffeomorph c φ).toOpenPartialHomeomorph.trans
              (blowupModelChart i)) z) := by
  have hs : (liftChartPartialDiffeomorph c φ).toOpenPartialHomeomorph.source =
      blowdown c ⁻¹' φ.source :=
    liftChartPartialDiffeomorph_source c φ
  set χ := (liftChartPartialDiffeomorph c φ).toOpenPartialHomeomorph.trans (blowupModelChart i)
  have hχ : χ ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin (n + 1) → ℂ) ω (Blowup c) :=
    liftChart_mem_maximalAtlas c φ i
  have hzχ := hz
  simp only [χ, OpenPartialHomeomorph.trans_source, hs,
    PartialDiffeomorph.toFun'_toOpenPartialHomeomorph, coe_liftChartPartialDiffeomorph,
    Set.mem_inter_iff, Set.mem_preimage] at hzχ
  -- Near `z`, `φ ∘ blowdown c` is the blowdown of the model read in the chart `χ`.
  have heq : (fun z' ↦ φ (blowdown c z')) =ᶠ[nhds z]
      (fun w ↦ ((blowupModelChart i).symm w).blowdown) ∘ χ := by
    filter_upwards [χ.open_source.mem_nhds hz] with z' hz'
    simp only [χ, OpenPartialHomeomorph.trans_source, hs,
      PartialDiffeomorph.toFun'_toOpenPartialHomeomorph, coe_liftChartPartialDiffeomorph,
      Set.mem_inter_iff, Set.mem_preimage] at hz'
    simp only [comp_apply, χ, OpenPartialHomeomorph.coe_trans,
      PartialDiffeomorph.toFun'_toOpenPartialHomeomorph, coe_liftChartPartialDiffeomorph]
    rw [(blowupModelChart i).left_inv hz'.2, blowdown_liftChart c φ hz'.1]
  have hφd : MDifferentiableAt 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) φ (blowdown c z) :=
    (contMDiffAt_of_mem_maximalAtlas hφ.out hzχ.1).mdifferentiableAt (by simp)
  have hbd : MDifferentiableAt 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) (blowdown c) z :=
    ((contMDiff_blowdown c) z).mdifferentiableAt (by simp)
  have hχd : MDifferentiableAt 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) χ z :=
    (contMDiffAt_of_mem_maximalAtlas hχ hz).mdifferentiableAt (by simp)
  have hF := ((hasFDerivAt_blowdown_blowupModelChart_symm i (χ z)).differentiableAt.hasFDerivAt
    ).hasMFDerivAt
  have key := (mfderiv_comp z hφd hbd).symm.trans (heq.mfderiv_eq.trans
    ((hF.comp z hχd.hasMFDerivAt).mfderiv))
  have hχz : χ z = blowupModelChart i (liftChart c φ z) := by
    simp only [χ, OpenPartialHomeomorph.coe_trans, comp_apply,
      PartialDiffeomorph.toFun'_toOpenPartialHomeomorph, coe_liftChartPartialDiffeomorph]
  ext v
  have h : b.det (mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) φ (blowdown c z) ∘
      (mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) (blowdown c) z ∘ v)) =
      b.det ((fderiv ℂ (fun w ↦ ((blowupModelChart i).symm w).blowdown) (χ z) :
        (Fin (n + 1) → ℂ) →ₗ[ℂ] Fin (n + 1) → ℂ) ∘
        (mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) χ z ∘ v)) :=
    congrArg (fun L : (Fin (n + 1) → ℂ) →L[ℂ] Fin (n + 1) → ℂ ↦ b.det (L ∘ v)) key
  rw [Basis.det_comp, det_fderiv_blowdown_blowupModelChart_symm, hχz] at h
  rw [← Basis.continuousDet_apply, ← Basis.continuousDet_apply] at h
  -- The two sides of `h` are those of the goal applied to `v`, by the definitions of
  -- `compContinuousLinearMap` and of the scalar action. The rewriting lemmas for these do not
  -- unify here, where the tangent spaces of the blowup are `E` only by definition, so the goal is
  -- closed by `exact`.
  exact h

end Blowup

end SymplecticGeometry

end
