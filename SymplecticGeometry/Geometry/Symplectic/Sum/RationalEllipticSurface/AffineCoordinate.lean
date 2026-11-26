/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Sum.RationalEllipticSurface
public import TauCeti.Geometry.Manifold.RegularValue

/-!
# The affine coordinate of the rational elliptic surface over `ℂℙ¹`

The projection of the rational elliptic surface `E(1)` to `ℂℙ¹`, followed by the standard affine
chart of `ℂℙ¹` where `s ≠ 0`, is the complex function `affineCoordinate : E(1) → ℂ`, which sends a
point `(L, [s : t])` with `s ≠ 0` to `t / s`. This file shows that it is a defining function of
the fibre `x ↦ (x, [1 : 0])` over `[1 : 0]`
(`SymplecticGeometry.rationalEllipticSurface.fibreEmbedding`): it is analytic near the fibre, it
vanishes on it, and its differential is onto at every point of it.

## Main definitions and results

* `SymplecticGeometry.rationalEllipticSurface.affineCoordinate`: the affine coordinate `t / s`,
  with `affineCoordinate_mk_snd` evaluating it on representatives.
* `SymplecticGeometry.rationalEllipticSurface.contMDiffAt_affineCoordinate`: it is analytic at
  every point over the affine open `s ≠ 0`, and
  `SymplecticGeometry.rationalEllipticSurface.contMDiffAt_affineCoordinate_fibreEmbedding`: it is
  smooth over `ℝ` at the points of the fibre.
* `SymplecticGeometry.rationalEllipticSurface.affineCoordinate_fibreEmbedding`: it vanishes on the
  fibre.
* `SymplecticGeometry.rationalEllipticSurface.isRegularPoint_affineCoordinate`: its complex
  differential is onto at every point of the fibre, and
  `SymplecticGeometry.rationalEllipticSurface.isRegularPoint_restrictScalars_affineCoordinate`:
  so is its real differential.

## Regularity

Fix a point `(L, [1 : 0])` of the fibre, a standard affine chart `i` of `ℂℙ²` containing `L`, and
the chart `s ≠ 0` of `ℂℙ¹`. In the product of these two charts the surface has the single equation
`SymplecticGeometry.prodChartEquations`, its tangent space is the kernel of the derivative of that
equation (`SymplecticGeometry.tangentRange_complexProjectiveProdZeroLocusEmbedding`), and the
affine coordinate is the coordinate of the second chart. So it suffices to exhibit a kernel vector
whose `t`-component is `1`. The derivative of the pencil in `t` is `x y z`; it vanishes at the
base points of the pencil, which lie on the cubic, so it is of no use here. At `t = 0`, though, the
derivative in a plane coordinate `l` is `3 v_l²`, and `v_l ≠ 0` for some `l ≠ i`, because
`v_i = 1` while `v_0³ + v_1³ + v_2³ = 0`. Subtracting a multiple of that plane direction from the
`t`-direction gives the kernel vector. The chain rule through the product chart is set up as in
`SymplecticGeometry.surjective_mfderiv_prodChartEquations_affineChart_iff`. The real statement
comes from the complex one: a holomorphic map has the same derivative over `ℝ` as over `ℂ`
(`MDifferentiableAt.mfderiv_modelWithCornersSelf_restrictScalars_apply`).

## References

* [R. E. Gompf, *A new construction of symplectic manifolds*][Gompf1995].
* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §7.2.
-/

public section

open MvPolynomial Set TauCeti Projectivization
open scoped ContDiff Manifold LinearAlgebra.Projectivization

namespace SymplecticGeometry.rationalEllipticSurface

/-- The **affine coordinate** `t / s` of the projection of the rational elliptic surface to
`ℂℙ¹`: the coordinate of the standard affine chart `s ≠ 0` of `ℂℙ¹` at the image of a point. It
is `0` on the fibre over `[1 : 0]`; off the affine open `s ≠ 0` its value carries no meaning. -/
noncomputable def affineCoordinate (p : rationalEllipticSurface) : ℂ :=
  affineChart 0 (p : ℙ ℂ (Fin 3 → ℂ) × ℙ ℂ (Fin 2 → ℂ)).2 0

theorem affineCoordinate_def (p : rationalEllipticSurface) :
    affineCoordinate p = affineChart 0 (p : ℙ ℂ (Fin 3 → ℂ) × ℙ ℂ (Fin 2 → ℂ)).2 0 :=
  (rfl)

/-- At a point over `[s : t]`, the affine coordinate is `t / s`. -/
theorem affineCoordinate_mk_snd {p : rationalEllipticSurface} {w : Fin 2 → ℂ} (hw : w ≠ 0)
    (h : (p : ℙ ℂ (Fin 3 → ℂ) × ℙ ℂ (Fin 2 → ℂ)).2 = mk ℂ w hw) :
    affineCoordinate p = w 1 / w 0 := by
  simp [affineCoordinate_def, h, affineChart_mk]

/-- The affine coordinate vanishes on the fibre over `[1 : 0]`. -/
@[simp]
theorem affineCoordinate_fibreEmbedding (x : SmoothProjectiveHypersurface.fermat 1 3) :
    affineCoordinate (fibreEmbedding x) = 0 := by
  rw [affineCoordinate_mk_snd _ (by rw [coe_fibreEmbedding_apply])]
  simp

/-- The affine coordinate is analytic at every point over the affine open `s ≠ 0` of `ℂℙ¹`. -/
theorem contMDiffAt_affineCoordinate {p : rationalEllipticSurface}
    (hp : (p : ℙ ℂ (Fin 3 → ℂ) × ℙ ℂ (Fin 2 → ℂ)).2 ∈ affineOpen 0) (r : ℕ∞ω) :
    ContMDiffAt 𝓘(ℂ, Fin 2 → ℂ) 𝓘(ℂ, ℂ) r affineCoordinate p :=
  (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 ↦ ℂ) 0).contMDiff.contMDiffAt.comp p
    (((contMDiffOn_affineChart 0 r).contMDiffAt ((isOpen_affineOpen 0).mem_nhds hp)).comp p
      ((contMDiff_snd p).of_le le_top))

/-- The fibre over `[1 : 0]` lies over the affine open `s ≠ 0` of `ℂℙ¹`. -/
theorem snd_fibreEmbedding_mem_affineOpen (x : SmoothProjectiveHypersurface.fermat 1 3) :
    (fibreEmbedding x : ℙ ℂ (Fin 3 → ℂ) × ℙ ℂ (Fin 2 → ℂ)).2 ∈ affineOpen 0 := by
  simp [coe_fibreEmbedding_apply]

/-- The affine coordinate is smooth, over `ℝ`, at every point of the fibre over `[1 : 0]`. -/
theorem contMDiffAt_affineCoordinate_fibreEmbedding (x : SmoothProjectiveHypersurface.fermat 1 3) :
    ContMDiffAt 𝓘(ℝ, Fin 2 → ℂ) 𝓘(ℝ, ℂ) ∞ affineCoordinate (fibreEmbedding x) :=
  (contMDiffAt_affineCoordinate (snd_fibreEmbedding_mem_affineOpen x) ∞).restrictScalars' ℝ

/-- At a zero `a` of the chart equation of the Hesse pencil in the product of the affine charts
`i` of `ℂℙ²` and `s ≠ 0` of `ℂℙ¹` that lies over `t = 0`, some vector of the kernel of the
derivative of the chart equation has `t`-component `1`. -/
private theorem exists_fderiv_prodChartEquations_eq_zero {i : Fin 3}
    {a : (Fin 2 → ℂ) × (Fin 1 → ℂ)} (ha : a.2 = 0)
    (hmem : prodChartEquations i 0 (fun _ : Unit ↦ hessePencil ℂ) a () = 0) :
    ∃ w, fderiv ℂ (prodChartEquations i 0 fun _ : Unit ↦ hessePencil ℂ) a w = 0 ∧ w.2 0 = 1 := by
  have hb : (0 : Fin 2).insertNth (1 : ℂ) a.2 = ![1, 0] := by
    ext k
    fin_cases k <;> simp [ha]
  rw [prodChartEquations_apply, hb, eval_hessePencil] at hmem
  simp only [Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one,
    one_mul, zero_mul, add_zero] at hmem
  -- Some plane coordinate of the chart point other than `i` is nonzero, since the point lies on
  -- the Fermat cubic and its coordinate `i` is `1`.
  obtain ⟨c, hc⟩ : ∃ c, a.1 c ≠ 0 := by
    by_contra! h
    have hv : ∀ k, Fin.insertNth (α := fun _ ↦ ℂ) i 1 a.1 k = if k = i then 1 else 0 := by
      intro k
      refine Fin.succAboveCases i ?_ (fun c ↦ ?_) k <;> simp [h, Fin.succAbove_ne]
    simp only [hv] at hmem
    fin_cases i <;> simp at hmem
  -- The derivative in the plane direction `i.succAbove c` is `3 (a.1 c)² ≠ 0`.
  set D := fderiv ℂ (prodChartEquations i 0 fun _ : Unit ↦ hessePencil ℂ) a
  set w₀ : (Fin 2 → ℂ) × (Fin 1 → ℂ) := (Pi.single c 1, 0)
  have hz : Sum.elim (Fin.insertNth (α := fun _ ↦ ℂ) i 0 w₀.1)
      (Fin.insertNth (α := fun _ ↦ ℂ) (0 : Fin 2) 0 w₀.2) =
      Pi.single (Sum.inl (i.succAbove c)) 1 := by
    ext (k | k)
    · refine Fin.succAboveCases i ?_ (fun d ↦ ?_) k <;> simp [w₀, Pi.single_apply]
    · refine Fin.succAboveCases 0 ?_ (fun d ↦ ?_) k <;> simp [w₀]
  have hD₀ : D w₀ () ≠ 0 := by
    rw [fderiv_prodChartEquations_apply, hz, Matrix.mulVec_single_one, Matrix.col_apply,
      jacobiMatrixAt_apply, hb, eval_pderiv_inl_hessePencil, eval_pderiv_hesseCubics_zero,
      Fin.insertNth_apply_succAbove]
    simpa using hc
  -- Correct the `t`-direction by a multiple of that plane direction.
  refine ⟨(0, fun _ ↦ 1) - (D (0, fun _ ↦ 1) () / D w₀ ()) • w₀, funext fun u ↦ ?_, ?_⟩
  · simp [hD₀]
  · simp [w₀]

/-- **The fibre over `[1 : 0]` is a regular level of the affine coordinate.** The complex
differential of the affine coordinate is onto at every point of the fibre. -/
theorem isRegularPoint_affineCoordinate (x : SmoothProjectiveHypersurface.fermat 1 3) :
    IsRegularPoint 𝓘(ℂ, Fin 2 → ℂ) 𝓘(ℂ, ℂ) affineCoordinate (fibreEmbedding x) := by
  set q := fibreEmbedding x
  set P := embedding q with hP
  have hq : (q : ℙ ℂ (Fin 3 → ℂ) × ℙ ℂ (Fin 2 → ℂ)) = P := by rw [hP, coe_embedding]
  obtain ⟨i, hi⟩ : ∃ i, P.1 ∈ affineOpen i := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp P.1.rep_ne_zero
    exact ⟨i, (mem_affineOpen_iff i _).2 hi⟩
  have hj : P.2 ∈ affineOpen 0 := hq ▸ snd_fibreEmbedding_mem_affineOpen x
  -- The product of the two affine charts, a chart of `ℂℙ² × ℂℙ¹` at `P`.
  set e := (affineOpenPartialHomeomorph (K := ℂ) i).prod (affineOpenPartialHomeomorph (K := ℂ) 0)
  have he : e ∈ atlas (ModelProd (Fin 2 → ℂ) (Fin 1 → ℂ))
      (ℙ ℂ (Fin 3 → ℂ) × ℙ ℂ (Fin 2 → ℂ)) :=
    mem_image2_of_mem (affineOpenPartialHomeomorph_mem_atlas (𝕜 := ℂ) i)
      (affineOpenPartialHomeomorph_mem_atlas (𝕜 := ℂ) 0)
  have hPe : P ∈ e.source := by simpa [e] using ⟨hi, hj⟩
  have he' := mdifferentiable_of_mem_atlas (I := 𝓘(ℂ, Fin 2 → ℂ).prod 𝓘(ℂ, Fin 1 → ℂ)) he
  have hePe := (he'.mdifferentiableAt hPe).hasMFDerivAt
  set p : Unit → MvPolynomial (Fin 3 ⊕ Fin 2) ℂ := fun _ ↦ hessePencil ℂ
  have ha : e P = (affineChart i P.1, affineChart 0 P.2) := by simp [e]
  -- The chart equation and the affine coordinate, read in the chart `e`.
  set D := fderiv ℂ (prodChartEquations i 0 p) (e P)
  have hD : HasMFDerivAt (𝓘(ℂ, Fin 2 → ℂ).prod 𝓘(ℂ, Fin 1 → ℂ)) 𝓘(ℂ, Unit → ℂ)
      (prodChartEquations i 0 p) (e P) D := by
    rw [← modelWithCornersSelf_prod]
    exact (hasStrictFDerivAt_prodChartEquations i 0 p _).hasFDerivAt.hasMFDerivAt
  set L : (Fin 2 → ℂ) × (Fin 1 → ℂ) →L[ℂ] ℂ :=
    (ContinuousLinearMap.proj 0).comp (ContinuousLinearMap.snd ℂ _ _)
  have hL : HasMFDerivAt (𝓘(ℂ, Fin 2 → ℂ).prod 𝓘(ℂ, Fin 1 → ℂ)) 𝓘(ℂ, ℂ) L (e P) L := by
    rw [← modelWithCornersSelf_prod]
    exact L.hasFDerivAt.hasMFDerivAt
  have hval : HasMFDerivAt 𝓘(ℂ, Fin 2 → ℂ) (𝓘(ℂ, Fin 2 → ℂ).prod 𝓘(ℂ, Fin 1 → ℂ))
      (⇑embedding) q
      (mfderiv 𝓘(ℂ, Fin 2 → ℂ) (𝓘(ℂ, Fin 2 → ℂ).prod 𝓘(ℂ, Fin 1 → ℂ)) (⇑embedding) q) :=
    ((embedding.contMDiff q).mdifferentiableAt (by simp)).hasMFDerivAt
  have hg : affineCoordinate = (⇑L ∘ e) ∘ ⇑embedding := by
    ext y
    simp [affineCoordinate_def, L, e, coe_embedding]
  have hF : (fun y : ℙ ℂ (Fin 3 → ℂ) × ℙ ℂ (Fin 2 → ℂ) ↦
      prodChartEquations i 0 p (affineChart i y.1, affineChart 0 y.2)) =
      prodChartEquations i 0 p ∘ e := by
    ext y
    simp [e]
  -- A vector of the kernel of `D` whose `t`-component is `1`.
  obtain ⟨w, hwD, hw1⟩ : ∃ w, D w = 0 ∧ L w = 1 := by
    refine exists_fderiv_prodChartEquations_eq_zero (funext fun k ↦ ?_) ?_
    · rw [Subsingleton.elim k 0, ha, ← hq]
      exact (affineCoordinate_def _).symm.trans (affineCoordinate_fibreEmbedding x)
    · rw [ha]
      exact (mem_complexProjectiveProdZeroLocus_iff_prodChartEquations
        (fun _ ↦ isWeightedHomogeneous_hessePencil_inl)
        (fun _ ↦ isWeightedHomogeneous_hessePencil_inr) hi hj).1
        (by rw [← rationalEllipticSurface_def, ← hq]; exact q.property) ()
  refine isRegularPoint_iff.2 fun (c : ℂ) ↦ ?_
  obtain ⟨v, hv⟩ := (he'.mfderiv_bijective hPe).surjective (c • w)
  have hvker : v ∈ (mfderiv (𝓘(ℂ, Fin 2 → ℂ).prod 𝓘(ℂ, Fin 1 → ℂ)) 𝓘(ℂ, Unit → ℂ)
      (fun y : ℙ ℂ (Fin 3 → ℂ) × ℙ ℂ (Fin 2 → ℂ) ↦
        prodChartEquations i 0 p (affineChart i y.1, affineChart 0 y.2)) P).ker := by
    rw [LinearMap.mem_ker, hF, (hD.comp P hePe).mfderiv]
    -- `rfl` identifies the zero of `Unit → ℂ` with that of the tangent space it models.
    exact (congrArg D hv).trans (by rw [D.map_smul, hwD, smul_zero]; rfl)
  -- The tangent space of the surface is the kernel of the differential of the chart equation.
  have hT := tangentRange_complexProjectiveProdZeroLocusEmbedding (k := 2) (by simp)
    (fun _ ↦ isWeightedHomogeneous_hessePencil_inl) (fun _ ↦ isWeightedHomogeneous_hessePencil_inr)
    isOpen_univ eq_inter_univ (fun x _ ↦ surjective_jacobiMatrixAt x) (r := ω) (by simp) q
    (hq ▸ hi) (hq ▸ hj)
  rw [← embedding_def, hq] at hT
  have hvT : v ∈ embedding.tangentRange q (by simp) := by
    rw [hT]
    exact hvker
  obtain ⟨u, hu⟩ := hvT
  refine ⟨u, ?_⟩
  -- The affine coordinate is `L ∘ e` on the surface, so its differential sends `u` to `L (c • w)`.
  have hfin := ((hL.comp P hePe).comp q hval).congr_of_eventuallyEq_abuse
    (f₁ := affineCoordinate) (Filter.Eventually.of_forall fun y ↦ congrFun hg y)
  rw [hfin.mfderiv]
  exact (congrArg L ((congrArg _ hu).trans hv)).trans
    (by rw [L.map_smul, hw1, smul_eq_mul, mul_one])

/-- **The affine coordinate is a defining function of the fibre over `[1 : 0]`.** Its real
differential is onto at every point of the fibre. -/
theorem isRegularPoint_restrictScalars_affineCoordinate
    (x : SmoothProjectiveHypersurface.fermat 1 3) :
    IsRegularPoint 𝓘(ℝ, Fin 2 → ℂ) 𝓘(ℝ, ℂ) affineCoordinate (fibreEmbedding x) := by
  have hd : MDifferentiableAt 𝓘(ℂ, Fin 2 → ℂ) 𝓘(ℂ, ℂ) affineCoordinate (fibreEmbedding x) :=
    (contMDiffAt_affineCoordinate (snd_fibreEmbedding_mem_affineOpen x) 1).mdifferentiableAt
      one_ne_zero
  refine isRegularPoint_iff.2 fun c ↦ ?_
  obtain ⟨u, hu⟩ := isRegularPoint_iff.1 (isRegularPoint_affineCoordinate x) c
  exact ⟨u, (hd.mfderiv_modelWithCornersSelf_restrictScalars_apply ℝ u).trans hu⟩

end SymplecticGeometry.rationalEllipticSurface

end
