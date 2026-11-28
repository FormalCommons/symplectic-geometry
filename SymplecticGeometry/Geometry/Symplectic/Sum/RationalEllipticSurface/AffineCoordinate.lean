/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Sum.RationalEllipticSurface.Basic
public import TauCeti.Geometry.Manifold.RegularValue
public import TauCeti.Topology.FiberBundle.MapFiber
public import SymplecticGeometry.Geometry.Symplectic.Sum.ProductNeighborhood
import Mathlib.Topology.LocalAtTarget
import SymplecticGeometry.Geometry.Manifold.Instances.Projectivization
import SymplecticGeometry.Geometry.Manifold.RegularValue.CriticalSet
import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.NormalSpace.LevelTrivialization
import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.Submanifold
import TauCeti.Topology.Homeomorph.SetCongr

/-!
# The affine coordinate of the rational elliptic surface over `ℂℙ¹`

The projection of the rational elliptic surface `E(1)` to `ℂℙ¹`, followed by the standard affine
chart of `ℂℙ¹` where `s ≠ 0`, is the complex function `affineCoordinate : E(1) → ℂ`, which sends a
point `(L, [s : t])` with `s ≠ 0` to `t / s`. This file shows that it is a defining function of
the fibre `x ↦ (x, [1 : 0])` over `[1 : 0]`
(`SymplecticGeometry.rationalEllipticSurface.fibreEmbedding`): it is analytic near the fibre, it
vanishes on it, and its differential is onto at every point of it. Its differential then
trivializes the normal bundle of the fibre, compatibly with the complex structures, and a
rescaling of that trivialization is a symplectic framing of the fibre.

## Main definitions and results

* `SymplecticGeometry.rationalEllipticSurface.affineCoordinate`: the affine coordinate `t / s`,
  with `affineCoordinate_mk_snd` evaluating it on representatives.
* `SymplecticGeometry.rationalEllipticSurface.contMDiffAt_affineCoordinate`: it is analytic at
  every point over the affine open `s ≠ 0`, and
  `SymplecticGeometry.rationalEllipticSurface.contMDiffAt_affineCoordinate_fibreEmbedding`: it is
  smooth over `ℝ` at the points of the fibre.
* `SymplecticGeometry.rationalEllipticSurface.affineCoordinate_fibreEmbedding`: it vanishes on the
  fibre.
* `SymplecticGeometry.rationalEllipticSurface.mem_range_fibreEmbedding_iff`: the fibre is the set
  of points over the affine open `s ≠ 0` where it vanishes.
* `SymplecticGeometry.rationalEllipticSurface.isRegularPoint_affineCoordinate`: its complex
  differential is onto at every point of the fibre, and
  `SymplecticGeometry.rationalEllipticSurface.isRegularPoint_restrictScalars_affineCoordinate`:
  so is its real differential.
* `SymplecticGeometry.rationalEllipticSurface.overAffineOpen`: the open set of points over the
  affine open `s ≠ 0`. On it the affine coordinate is a proper map
  (`isProperMap_affineCoordinate_comp_subtypeVal`), smooth over `ℝ`
  (`contMDiff_affineCoordinate_comp_subtypeVal`), with `0` as a regular value
  (`isRegularValue_affineCoordinate_comp_subtypeVal_zero`).
* `SymplecticGeometry.rationalEllipticSurface.fibreHomeomorph`: the Fermat cubic is homeomorphic,
  through `fibreEmbedding`, to the fibre over `0` of the affine coordinate on that open set.
* `SymplecticGeometry.rationalEllipticSurface.fibreNormalEquiv`: the normal trivialization
  `ℂ ≃L[ℝ] N_x` of the fibre, the inverse of the isomorphism of the normal space with `ℂ` induced
  by the real differential of the affine coordinate (`fibreNormalEquiv_mfderiv`,
  `fibreNormalEquiv_symm_normalClass`).
* `SymplecticGeometry.rationalEllipticSurface.contMDiff_fibreNormalEquiv`: it is smooth, as a map
  from the product of the Fermat cubic with `ℂ` to the normal bundle, the form that
  `SymplecticGeometry.SymplecticFraming.ofPos` takes.
* `SymplecticGeometry.rationalEllipticSurface.normalComplexStructureAt_fibreNormalEquiv`: it
  intertwines multiplication by `i` with the complex structure that the surface induces on the
  normal spaces.
* `SymplecticGeometry.rationalEllipticSurface.fibreFraming`: the symplectic framing of the fibre
  for the symplectic form of the surface, with `fibreFraming_apply`.

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
`t`-direction gives the kernel vector. The chain rule through the product chart is
`Projectivization.hasMFDerivAt_comp_affineChart_prodMap`, and its differential is bijective by
`Projectivization.bijective_mfderiv_affineChart_prodMap`. The differential of
the composite is read off through `TauCeti.isRegularPoint_comp_iff`, and the real statement comes
from the complex one by `TauCeti.IsRegularPoint.restrictScalars'`.

## The normal trivialization

Since the affine coordinate cuts out the fibre near each of its points, its real differential at
`x` descends to an isomorphism of the normal space at `x` with `ℂ`
(`TauCeti.SmoothEmbedding.normalSpaceEquivOfLevel`), and the inverses of these isomorphisms are
smooth in `x` because one function does this at every point
(`TauCeti.SmoothEmbedding.contMDiff_normalSpaceEquivOfLevel_symm`). These inverses are complex
linear because the affine coordinate is holomorphic
(`TauCeti.SmoothEmbedding.normalComplexStructureAt_normalSpaceEquivOfLevel_symm`).

So the complex structure of the normal space sends `fibreNormalEquiv x 1` to
`fibreNormalEquiv x i`. The symplectic form of the surface tames its complex structure
(`SymplecticGeometry.rationalEllipticSurface.tames_symplecticForm`), so the normal symplectic
form is positive on this pair
(`TauCeti.SmoothEmbedding.symplecticNormalForm_normalComplexStructureAt_pos`), and
`SymplecticGeometry.SymplecticFraming.ofPos` rescales the trivialization to a symplectic framing.

## References

* [R. E. Gompf, *A new construction of symplectic manifolds*][Gompf1995].
* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §7.2.
-/

public section

open MvPolynomial Set TauCeti Projectivization TopologicalSpace
open scoped ContDiff Manifold LinearAlgebra.Projectivization

namespace SymplecticGeometry.rationalEllipticSurface

/-- The **affine coordinate** `t / s` of the projection of the rational elliptic surface to
`ℂℙ¹`: the coordinate of the standard affine chart `s ≠ 0` of `ℂℙ¹` at the image of a point. It
is `0` on the fibre over `[1 : 0]`. Off the affine open `s ≠ 0` it is `0` too, the value of
`t / 0`, so its zero set also contains the fibre over `[0 : 1]`. -/
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
    ((contMDiffAt_affineChart hp r).comp p ((contMDiff_snd p).of_le le_top))

/-- The fibre over `[1 : 0]` lies over the affine open `s ≠ 0` of `ℂℙ¹`. -/
theorem snd_fibreEmbedding_mem_affineOpen (x : SmoothProjectiveHypersurface.fermat 1 3) :
    (fibreEmbedding x : ℙ ℂ (Fin 3 → ℂ) × ℙ ℂ (Fin 2 → ℂ)).2 ∈ affineOpen 0 := by
  simp [coe_fibreEmbedding_apply]

/-- A point over the affine open `s ≠ 0` is determined over `ℂℙ¹` by its affine coordinate. -/
theorem snd_eq_affineChart_symm_affineCoordinate {p : rationalEllipticSurface}
    (hp : (p : ℙ ℂ (Fin 3 → ℂ) × ℙ ℂ (Fin 2 → ℂ)).2 ∈ affineOpen 0) :
    (p : ℙ ℂ (Fin 3 → ℂ) × ℙ ℂ (Fin 2 → ℂ)).2 =
      (affineChart 0).symm (fun _ ↦ affineCoordinate p) := by
  have h : (fun _ : Fin 1 ↦ affineCoordinate p) =
      affineChart 0 (p : ℙ ℂ (Fin 3 → ℂ) × ℙ ℂ (Fin 2 → ℂ)).2 := by
    funext k
    rw [Subsingleton.elim k 0, affineCoordinate_def]
  rw [h, (affineChart 0).left_inv (by rwa [affineChart_source])]

/-- A point of the rational elliptic surface lies on the fibre over `[1 : 0]` exactly when it lies
over the affine open `s ≠ 0` of `ℂℙ¹` and its affine coordinate vanishes. -/
theorem mem_range_fibreEmbedding_iff {p : rationalEllipticSurface} :
    p ∈ range fibreEmbedding ↔
      (p : ℙ ℂ (Fin 3 → ℂ) × ℙ ℂ (Fin 2 → ℂ)).2 ∈ affineOpen 0 ∧ affineCoordinate p = 0 := by
  refine ⟨?_, fun ⟨hp, h⟩ ↦ ?_⟩
  · rintro ⟨x, rfl⟩
    exact ⟨snd_fibreEmbedding_mem_affineOpen x, affineCoordinate_fibreEmbedding x⟩
  rw [range_fibreEmbedding, mem_ofPred_eq, snd_eq_affineChart_symm_affineCoordinate hp, h,
    ← Pi.zero_def, affineChart_symm_zero]
  congr 1
  funext k
  fin_cases k <;> simp

/-- The open set of points of the rational elliptic surface over the affine open `s ≠ 0` of
`ℂℙ¹`. -/
noncomputable def overAffineOpen : Opens rationalEllipticSurface :=
  ⟨(fun p : rationalEllipticSurface ↦ (p : ℙ ℂ (Fin 3 → ℂ) × ℙ ℂ (Fin 2 → ℂ)).2) ⁻¹'
      affineOpen 0,
    (isOpen_affineOpen 0).preimage (continuous_snd.comp continuous_subtypeVal)⟩

theorem coe_overAffineOpen : SetLike.coe overAffineOpen =
    (fun p : rationalEllipticSurface ↦ (p : ℙ ℂ (Fin 3 → ℂ) × ℙ ℂ (Fin 2 → ℂ)).2) ⁻¹'
      affineOpen 0 :=
  (rfl)

@[simp]
theorem mem_overAffineOpen {p : rationalEllipticSurface} :
    p ∈ overAffineOpen ↔ (p : ℙ ℂ (Fin 3 → ℂ) × ℙ ℂ (Fin 2 → ℂ)).2 ∈ affineOpen 0 := by
  rw [← SetLike.mem_coe, coe_overAffineOpen, mem_preimage]

/-- The affine coordinate is a proper map on the points over the affine open `s ≠ 0`. -/
theorem isProperMap_affineCoordinate_comp_subtypeVal :
    IsProperMap (affineCoordinate ∘ Subtype.val : overAffineOpen → ℂ) := by
  -- It is the restriction over the affine open of the projection to `ℂℙ¹`, which is proper
  -- since the surface is compact, followed by the affine chart.
  set φ := affineOpenPartialHomeomorph (K := ℂ) (n := 1) 0
  set F := fun p : rationalEllipticSurface ↦ (p : ℙ ℂ (Fin 3 → ℂ) × ℙ ℂ (Fin 2 → ℂ)).2
  have hS : SetLike.coe overAffineOpen = F ⁻¹' φ.source := by
    simp [φ, F, coe_overAffineOpen, ← affineChart_source]
  have hT : IsClosed φ.target := by
    simp only [φ, affineOpenPartialHomeomorph_toPartialEquiv, affineChart_target, isClosed_univ]
  have hF := (continuous_snd.comp continuous_subtypeVal : Continuous F).isProperMap
  convert (Homeomorph.funUnique (Fin 1) ℂ).isProperMap.comp
    (hT.isClosedEmbedding_subtypeVal.isProperMap.comp (φ.toHomeomorphSourceTarget.isProperMap.comp
      ((hF.restrictPreimage φ.source).comp (Homeomorph.setCongr hS).isProperMap))) using 1
  funext p
  simp only [φ, affineCoordinate_def, Homeomorph.setCongr_apply, Function.comp_apply,
    Homeomorph.funUnique_apply, Fin.default_eq_zero,
    OpenPartialHomeomorph.toHomeomorphSourceTarget_apply_coe, restrictPreimage_coe,
    coe_affineOpenPartialHomeomorph]

/-- The Fermat cubic is homeomorphic, through `fibreEmbedding`, to the fibre over `0` of the affine
coordinate on the points over the affine open `s ≠ 0`. -/
noncomputable def fibreHomeomorph : SmoothProjectiveHypersurface.fermat 1 3 ≃ₜ
    MapFiber (affineCoordinate ∘ Subtype.val : overAffineOpen → ℂ) 0 :=
  Topology.IsEmbedding.toHomeomorphOfSurjective
    (f := fun x ↦ ⟨⟨fibreEmbedding x, mem_overAffineOpen.2 (snd_fibreEmbedding_mem_affineOpen x)⟩,
      affineCoordinate_fibreEmbedding x⟩)
    (.of_comp ((fibreEmbedding.isEmbedding.continuous.subtype_mk _).subtype_mk _)
      (continuous_subtypeVal.comp continuous_subtypeVal) fibreEmbedding.isEmbedding)
    (by
      intro z
      obtain ⟨x, hx⟩ := mem_range_fibreEmbedding_iff.2
        ⟨mem_overAffineOpen.1 z.val.property, z.property⟩
      exact ⟨x, Subtype.ext (Subtype.ext hx)⟩)

@[simp]
theorem coe_coe_fibreHomeomorph_apply (x : SmoothProjectiveHypersurface.fermat 1 3) :
    ((fibreHomeomorph x : overAffineOpen) : rationalEllipticSurface) = fibreEmbedding x :=
  (rfl)

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

/-- The complex differential of the affine coordinate is onto at every point of the fibre over
`[1 : 0]`. -/
theorem isRegularPoint_affineCoordinate (x : SmoothProjectiveHypersurface.fermat 1 3) :
    IsRegularPoint 𝓘(ℂ, Fin 2 → ℂ) 𝓘(ℂ, ℂ) affineCoordinate (fibreEmbedding x) := by
  set q := fibreEmbedding x
  set P := embedding q with hP
  have hq : (q : ℙ ℂ (Fin 3 → ℂ) × ℙ ℂ (Fin 2 → ℂ)) = P := by rw [hP, coe_embedding]
  obtain ⟨i, hi⟩ : ∃ i, P.1 ∈ affineOpen i := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp P.1.rep_ne_zero
    exact ⟨i, (mem_affineOpen_iff i _).2 hi⟩
  have hj : P.2 ∈ affineOpen 0 := hq ▸ snd_fibreEmbedding_mem_affineOpen x
  set p : Unit → MvPolynomial (Fin 3 ⊕ Fin 2) ℂ := fun _ ↦ hessePencil ℂ
  -- The chart equation and the affine coordinate, read in the product of the two affine charts.
  set D := fderiv ℂ (prodChartEquations i 0 p) (affineChart i P.1, affineChart 0 P.2)
  have hD := hasMFDerivAt_comp_affineChart_prodMap
    (hasStrictFDerivAt_prodChartEquations i 0 p _).hasFDerivAt hi hj
  set L : (Fin 2 → ℂ) × (Fin 1 → ℂ) →L[ℂ] ℂ :=
    (ContinuousLinearMap.proj 0).comp (ContinuousLinearMap.snd ℂ _ _)
  have hL := hasMFDerivAt_comp_affineChart_prodMap L.hasFDerivAt hi hj
  simp only [Function.comp_def, Prod.map_apply'] at hD hL
  have hg : affineCoordinate =
      (fun y : ℙ ℂ (Fin 3 → ℂ) × ℙ ℂ (Fin 2 → ℂ) ↦ L (affineChart i y.1, affineChart 0 y.2)) ∘
        ⇑embedding := by
    ext y
    simp [affineCoordinate_def, L, coe_embedding]
  -- A vector of the kernel of `D` whose `t`-component is `1`.
  obtain ⟨w, hwD, hw1⟩ : ∃ w, D w = 0 ∧ L w = 1 := by
    refine exists_fderiv_prodChartEquations_eq_zero (funext fun k ↦ ?_) ?_
    · rw [Subsingleton.elim k 0, ← hq]
      exact (affineCoordinate_def _).symm.trans (affineCoordinate_fibreEmbedding x)
    · exact (mem_complexProjectiveProdZeroLocus_iff_prodChartEquations
        (fun _ ↦ isWeightedHomogeneous_hessePencil_inl)
        (fun _ ↦ isWeightedHomogeneous_hessePencil_inr) hi hj).1
        (by rw [← rationalEllipticSurface_def, ← hq]; exact q.property) ()
  -- The tangent space of the surface is the kernel of the differential of the chart equation.
  have hT := tangentRange_complexProjectiveProdZeroLocusEmbedding (k := 2) (by simp)
    (fun _ ↦ isWeightedHomogeneous_hessePencil_inl) (fun _ ↦ isWeightedHomogeneous_hessePencil_inr)
    isOpen_univ eq_inter_univ (fun x _ ↦ surjective_jacobiMatrixAt x) (r := ω) (by simp) q
    (hq ▸ hi) (hq ▸ hj)
  rw [← embedding_def, hq] at hT
  -- The affine coordinate is `L` read in the product chart on the surface, so it suffices that
  -- the differential of the latter sends the tangent space of the surface onto `ℂ`.
  rw [hg, isRegularPoint_comp_iff (g := ⇑embedding) hL.mdifferentiableAt
    ((embedding.contMDiff q).mdifferentiableAt (by simp)), Submodule.eq_top_iff']
  intro (c : ℂ)
  obtain ⟨v, hv⟩ := (bijective_mfderiv_affineChart_prodMap hi hj).surjective (c • w)
  have hvker : v ∈ (mfderiv (𝓘(ℂ, Fin 2 → ℂ).prod 𝓘(ℂ, Fin 1 → ℂ)) 𝓘(ℂ, Unit → ℂ)
      (fun y : ℙ ℂ (Fin 3 → ℂ) × ℙ ℂ (Fin 2 → ℂ) ↦
        prodChartEquations i 0 p (affineChart i y.1, affineChart 0 y.2)) P).ker := by
    rw [LinearMap.mem_ker, hD.mfderiv]
    -- `rfl` identifies the zero of `Unit → ℂ` with that of the tangent space it models.
    exact (congrArg D hv).trans (by rw [D.map_smul, hwD, smul_zero]; rfl)
  refine ⟨v, ?_, ?_⟩
  · exact LinearMap.mem_range.2
      ((embedding.isImmersion.mem_tangentRange_iff q (by simp) v).1 (hT ▸ hvker))
  · rw [hL.mfderiv]
    exact (congrArg L hv).trans (by rw [L.map_smul, hw1, smul_eq_mul, mul_one])

/-- The real differential of the affine coordinate is onto at every point of the fibre over
`[1 : 0]`. -/
theorem isRegularPoint_restrictScalars_affineCoordinate
    (x : SmoothProjectiveHypersurface.fermat 1 3) :
    IsRegularPoint 𝓘(ℝ, Fin 2 → ℂ) 𝓘(ℝ, ℂ) affineCoordinate (fibreEmbedding x) :=
  (isRegularPoint_affineCoordinate x).restrictScalars'
    ((contMDiffAt_affineCoordinate (snd_fibreEmbedding_mem_affineOpen x) 1).mdifferentiableAt
      one_ne_zero)

/-- The affine coordinate on the points over the affine open `s ≠ 0`, as a smooth map over `ℝ`. -/
theorem contMDiff_affineCoordinate_comp_subtypeVal :
    ContMDiff 𝓘(ℝ, Fin 2 → ℂ) 𝓘(ℝ, ℂ) ∞ (affineCoordinate ∘ Subtype.val : overAffineOpen → ℂ) :=
  fun p ↦ ((contMDiffAt_affineCoordinate (mem_overAffineOpen.1 p.property) ∞).restrictScalars'
    ℝ).comp p (contMDiff_subtypeVal p)

/-- `0` is a regular value, over `ℝ`, of the affine coordinate on the points over the affine open
`s ≠ 0`: its real differential is onto at each of them where it vanishes. -/
theorem isRegularValue_affineCoordinate_comp_subtypeVal_zero :
    IsRegularValue 𝓘(ℝ, Fin 2 → ℂ) 𝓘(ℝ, ℂ) (affineCoordinate ∘ Subtype.val : overAffineOpen → ℂ)
      0 := by
  refine isRegularValue_iff.2 fun p hp ↦ ?_
  obtain ⟨x, hx⟩ := mem_range_fibreEmbedding_iff.2 ⟨mem_overAffineOpen.1 p.property, hp⟩
  have h := isRegularPoint_restrictScalars_affineCoordinate x
  rw [hx] at h
  exact h.comp (isRegularPoint_subtype_val p)


/-! ### The normal trivialization of the fibre -/

open scoped ComplexManifold

/-- The real dimensions of the fibre and of `ℂ` add up to that of the rational elliptic surface:
`2 + 2 = 4`. -/
theorem finrank_add_finrank_eq_fibreEmbedding :
    Module.finrank ℝ (Fin 1 → ℂ) + Module.finrank ℝ ℂ = Module.finrank ℝ (Fin 2 → ℂ) := by
  simp [Module.finrank_pi_fintype]

/-- The affine coordinate is constant, equal to `0`, on the fibre over `[1 : 0]`. -/
theorem eventually_affineCoordinate_fibreEmbedding (x : SmoothProjectiveHypersurface.fermat 1 3) :
    ∀ᶠ y in nhds x, affineCoordinate (fibreEmbedding y) = affineCoordinate (fibreEmbedding x) :=
  .of_forall fun y ↦ by simp

/-- **The normal trivialization of the fibre over `[1 : 0]`.** At a point `x` of the Fermat
cubic, the inverse of the isomorphism from the normal space of the fibre embedding at `x` onto
`ℂ` that the real differential of the affine coordinate induces: it sends `z ∈ ℂ` to the normal
class of any tangent vector `v` of the surface with `d(affineCoordinate)(v) = z`
(`fibreNormalEquiv_mfderiv`). -/
noncomputable def fibreNormalEquiv (x : SmoothProjectiveHypersurface.fermat 1 3) :
    ℂ ≃L[ℝ] fibreEmbedding.isImmersion.NormalSpace x ENat.coe_top_ne_zero :=
  (fibreEmbedding.normalSpaceEquivOfLevel x _ (eventually_affineCoordinate_fibreEmbedding x)
    (isRegularPoint_restrictScalars_affineCoordinate x)
    finrank_add_finrank_eq_fibreEmbedding).symm

theorem fibreNormalEquiv_def (x : SmoothProjectiveHypersurface.fermat 1 3) :
    fibreNormalEquiv x =
      (fibreEmbedding.normalSpaceEquivOfLevel x _ (eventually_affineCoordinate_fibreEmbedding x)
        (isRegularPoint_restrictScalars_affineCoordinate x)
        finrank_add_finrank_eq_fibreEmbedding).symm :=
  (rfl)

/-- The inverse of the normal trivialization sends the normal class of a tangent vector `v` to
the real differential of the affine coordinate applied to `v`. -/
@[simp]
theorem fibreNormalEquiv_symm_normalClass (x : SmoothProjectiveHypersurface.fermat 1 3)
    (v : TangentSpace 𝓘(ℝ, Fin 2 → ℂ) (fibreEmbedding x)) :
    (fibreNormalEquiv x).symm
        (fibreEmbedding.isImmersion.normalClass x ENat.coe_top_ne_zero v) =
      mfderiv 𝓘(ℝ, Fin 2 → ℂ) 𝓘(ℝ, ℂ) affineCoordinate (fibreEmbedding x) v := by
  rw [fibreNormalEquiv_def, ContinuousLinearEquiv.symm_symm,
    SmoothEmbedding.normalSpaceEquivOfLevel_normalClass]

/-- The normal trivialization sends the real differential of the affine coordinate applied to a
tangent vector `v` to the normal class of `v`. -/
@[simp]
theorem fibreNormalEquiv_mfderiv (x : SmoothProjectiveHypersurface.fermat 1 3)
    (v : TangentSpace 𝓘(ℝ, Fin 2 → ℂ) (fibreEmbedding x)) :
    fibreNormalEquiv x (mfderiv 𝓘(ℝ, Fin 2 → ℂ) 𝓘(ℝ, ℂ) affineCoordinate (fibreEmbedding x) v) =
      fibreEmbedding.isImmersion.normalClass x ENat.coe_top_ne_zero v := by
  rw [← fibreNormalEquiv_symm_normalClass, ContinuousLinearEquiv.apply_symm_apply]

/-- The normal trivialization is smooth: `(x, z) ↦ fibreNormalEquiv x z` is a smooth map from
the product of the Fermat cubic with `ℂ` to the normal bundle of the fibre embedding. -/
theorem contMDiff_fibreNormalEquiv :
    letI := fibreEmbedding.normalSpaceFiberBundle ENat.coe_top_ne_zero
      (Nat.eq_sub_of_add_eq' finrank_add_finrank_eq_fibreEmbedding)
    ContMDiff (𝓘(ℝ, Fin 1 → ℂ).prod 𝓘(ℝ, ℂ)) (𝓘(ℝ, Fin 1 → ℂ).prod 𝓘(ℝ, ℂ)) ∞
      (fun x : SmoothProjectiveHypersurface.fermat 1 3 × ℂ ↦
        (⟨x.1, fibreNormalEquiv x.1 x.2⟩ : Bundle.TotalSpace ℂ
          (fun q ↦ fibreEmbedding.isImmersion.NormalSpace q
            ENat.coe_top_ne_zero))) :=
  SmoothEmbedding.contMDiff_normalSpaceEquivOfLevel_symm
    contMDiffAt_affineCoordinate_fibreEmbedding eventually_affineCoordinate_fibreEmbedding
    isRegularPoint_restrictScalars_affineCoordinate _ finrank_add_finrank_eq_fibreEmbedding
    (m := ∞) (by simp)

/-- The normal trivialization is complex linear: the complex structure that the surface induces
on the normal space of the fibre sends `fibreNormalEquiv x z` to `fibreNormalEquiv x (i z)`. -/
@[simp]
theorem normalComplexStructureAt_fibreNormalEquiv (x : SmoothProjectiveHypersurface.fermat 1 3)
    (z : ℂ) :
    fibreEmbedding.normalComplexStructureAt ENat.coe_top_ne_zero
        (SmoothAlmostComplexStructure.ofComplexManifold (Fin 2 → ℂ) rationalEllipticSurface) x
        (mapsTo_ofComplexManifold_tangentRange_fibreEmbedding x) (fibreNormalEquiv x z) =
      fibreNormalEquiv x (Complex.I * z) := by
  rw [fibreNormalEquiv_def, ← smul_eq_mul]
  exact SmoothEmbedding.normalComplexStructureAt_normalSpaceEquivOfLevel_symm _ _ x _ _ _ _
    ((contMDiffAt_affineCoordinate (snd_fibreEmbedding_mem_affineOpen x) 1).mdifferentiableAt
      one_ne_zero) z

/-! ### The symplectic framing of the fibre -/

/-- The normal symplectic form of the fibre over `[1 : 0]` is positive on the pair
`(fibreNormalEquiv x 1, fibreNormalEquiv x i)`: the second is the image of the first under the
complex structure of the normal space, and the symplectic form of the surface tames the complex
structure. -/
theorem symplecticNormalForm_fibreNormalEquiv_pos (x : SmoothProjectiveHypersurface.fermat 1 3) :
    0 < fibreEmbedding.symplecticNormalForm hasSymplecticTangentImages_fibreEmbedding x
      ENat.coe_top_ne_zero (fibreNormalEquiv x 1)
        (fibreNormalEquiv x Complex.I) := by
  have h := normalComplexStructureAt_fibreNormalEquiv x 1
  rw [mul_one] at h
  rw [← h]
  exact SmoothEmbedding.symplecticNormalForm_normalComplexStructureAt_pos tames_symplecticForm
    fibreEmbedding hasSymplecticTangentImages_fibreEmbedding _
    (mapsTo_ofComplexManifold_tangentRange_fibreEmbedding x)
    ((fibreNormalEquiv x).map_ne_zero_iff.2 one_ne_zero)

/-- **The symplectic framing of the fibre over `[1 : 0]`.** The symplectic framing of the normal
bundle of the Fermat cubic, embedded in the rational elliptic surface as the fibre over `[1 : 0]`,
for the symplectic form of the surface: the normal trivialization `fibreNormalEquiv` given by the
affine coordinate of the projection to `ℂℙ¹`, rescaled at each point so that it carries the
standard form of `ℂ` to the normal symplectic form (`SymplecticFraming.ofPos`). -/
noncomputable def fibreFraming :
    SymplecticFraming hasSymplecticTangentImages_fibreEmbedding
      (Nat.eq_sub_of_add_eq' finrank_add_finrank_eq_fibreEmbedding) :=
  .ofPos fibreNormalEquiv contMDiff_fibreNormalEquiv symplecticNormalForm_fibreNormalEquiv_pos

theorem fibreFraming_def :
    fibreFraming = .ofPos fibreNormalEquiv contMDiff_fibreNormalEquiv
      symplecticNormalForm_fibreNormalEquiv_pos :=
  (rfl)

/-- The framing of the fibre sends a normal vector `v` at `x` of the zero slice of the product of
the Fermat cubic with `ℂ` to
`fibreNormalEquiv x ((√λ)⁻¹ • z)`, where `z ∈ ℂ` is the `ℂ`-component of `v` and `λ` is the
normal symplectic form of the fibre on `(fibreNormalEquiv x 1, fibreNormalEquiv x i)`. -/
@[simp]
theorem fibreFraming_apply (x : SmoothProjectiveHypersurface.fermat 1 3)
    (v : (zeroSlice 𝓘(ℝ, Fin 1 → ℂ)
      (SmoothProjectiveHypersurface.fermat 1 3)).isImmersion.NormalSpace
        x ENat.coe_top_ne_zero) :
    fibreFraming x v = fibreNormalEquiv x
      ((√(fibreEmbedding.symplecticNormalForm hasSymplecticTangentImages_fibreEmbedding x
        ENat.coe_top_ne_zero (fibreNormalEquiv x 1)
          (fibreNormalEquiv x Complex.I)))⁻¹ •
        zeroSliceNormalEquiv 𝓘(ℝ, Fin 1 → ℂ) (SmoothProjectiveHypersurface.fermat 1 3) x v) := by
  rw [fibreFraming_def, SymplecticFraming.ofPos_apply]

end SymplecticGeometry.rationalEllipticSurface

end
