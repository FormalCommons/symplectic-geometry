/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Analysis.InnerProductSpace.Symplectic.PolarComplexStructure.Smooth
public import SymplecticGeometry.Geometry.Symplectic.Cayley.Domain
public import SymplecticGeometry.LinearAlgebra.Symplectic.Compatible
public import Mathlib.Topology.Homotopy.Affine
public import Mathlib.Topology.Homotopy.Equiv

/-!
# Symplectic forms and complex structures for a fixed inner product

Fix an inner product `g` on a finite-dimensional real normed space `V`. A complex structure `J`
gives the symplectic form `ω_{g,J}(v, w) = ½ (g (J v) w - g v (J w))`, which `J` tames, and which
is `g (J ·, ·)` when `J` preserves `g`. In the other direction, a symplectic form `ω` gives the
complex structure `J_{g,ω}` of `SymplecticGeometry.metricPolarComplexStructure`. These two
continuous maps are mutually inverse up to homotopy:

* `ω ↦ ω_{g,J_{g,ω}}` is joined to the identity by the straight line between the two forms,
  which both tame `J_{g,ω}`;
* `J ↦ J_{g,ω_{g,J}}` is joined to the identity by Tau Ceti's Cayley interpolation, from the
  `ω_{g,J}`-compatible structure `J_{g,ω_{g,J}}` towards the `ω_{g,J}`-tame structure `J`.

So the space of symplectic forms on `V` and the space of complex structures on `V` are homotopy
equivalent.

## Main definitions

* `SymplecticGeometry.metricSymplecticForm g J`: the form `ω_{g,J}`.
* `SymplecticGeometry.polarStraightHomotopy g`: the straight-line homotopy from
  `ω ↦ ω_{g,J_{g,ω}}` to the identity of the symplectic forms.
* `SymplecticGeometry.polarCayleyHomotopy g`: the Cayley homotopy from `J ↦ J_{g,ω_{g,J}}` to
  the identity of the complex structures.
* `SymplecticGeometry.polarHomotopyEquiv g`: the homotopy equivalence between the symplectic
  forms and the complex structures, with maps `ω ↦ J_{g,ω}` and `J ↦ ω_{g,J}`.

## Main results

* `SymplecticGeometry.tames_metricSymplecticForm`: `J` tames `ω_{g,J}`.
* `SymplecticGeometry.metricSymplecticForm_eq_of_apply_apply`: for `g`-orthogonal `J`,
  `ω_{g,J}(v, w) = g (J v) w`.
* `SymplecticGeometry.continuous_metricSymplecticForm`: `J ↦ ω_{g,J}` is continuous.
* `SymplecticGeometry.metricSymplecticForm_innerSL`: for the inner product of an inner product
  space, `ω_{g,J}` is Tau Ceti's `AlmostComplexStructure.symplecticForm`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Proposition 2.5.6.
-/

public section

open TauCeti TauCeti.SymplecticForm Set unitInterval

namespace SymplecticGeometry

section MetricSymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (g : innerProducts V)
  (J : AlmostComplexStructure V)

private theorem isAlt_metricSymplecticBilinForm :
    LinearMap.BilinForm.IsAlt ((2 : ℝ)⁻¹ •
      ((g : V →L[ℝ] V →L[ℝ] ℝ).toBilinForm.compl₁₂ J.toLinearMap LinearMap.id -
      (g : V →L[ℝ] V →L[ℝ] ℝ).toBilinForm.compl₁₂ LinearMap.id J.toLinearMap)) := by
  intro v
  simp [(mem_innerProducts.1 g.property).1 v (J v)]

private theorem metricSymplecticBilinForm_pos {v : V} (hv : v ≠ 0) :
    0 < ((2 : ℝ)⁻¹ • ((g : V →L[ℝ] V →L[ℝ] ℝ).toBilinForm.compl₁₂ J.toLinearMap LinearMap.id -
      (g : V →L[ℝ] V →L[ℝ] ℝ).toBilinForm.compl₁₂ LinearMap.id J.toLinearMap)) v (J v) := by
  have h₁ := (mem_innerProducts.1 g.property).2 v hv
  have h₂ := (mem_innerProducts.1 g.property).2 (J v) (J.map_ne_zero_iff.2 hv)
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.compl₁₂_apply,
    LinearMap.id_apply, ContinuousLinearMap.toBilinForm_apply, AlmostComplexStructure.apply_apply,
    map_neg, smul_eq_mul]
  linarith

/-- The symplectic form `ω_{g,J}(v, w) = ½ (g (J v) w - g v (J w))` of an inner product `g` and a
complex structure `J`. It is tamed by `J` (`SymplecticGeometry.tames_metricSymplecticForm`), and
it is `g (J ·, ·)` when `J` preserves `g`
(`SymplecticGeometry.metricSymplecticForm_eq_of_apply_apply`). -/
noncomputable def metricSymplecticForm : SymplecticForm V :=
  ofTames _ (isAlt_metricSymplecticBilinForm g J) fun _ hv ↦ metricSymplecticBilinForm_pos g J hv

/-- The bilinear form of `ω_{g,J}` is `½ (g (J ·) · - g · (J ·))`. -/
@[simp]
theorem toBilinForm_metricSymplecticForm :
    (metricSymplecticForm g J).toBilinForm = (2 : ℝ)⁻¹ •
      ((g : V →L[ℝ] V →L[ℝ] ℝ).toBilinForm.compl₁₂ J.toLinearMap LinearMap.id -
        (g : V →L[ℝ] V →L[ℝ] ℝ).toBilinForm.compl₁₂ LinearMap.id J.toLinearMap) :=
  ofTames_toBilinForm _ _

theorem metricSymplecticForm_apply (v w : V) :
    metricSymplecticForm g J v w =
      2⁻¹ * ((g : V →L[ℝ] V →L[ℝ] ℝ) (J v) w - (g : V →L[ℝ] V →L[ℝ] ℝ) v (J w)) := by
  simp

/-- A complex structure `J` tames `ω_{g,J}`. -/
theorem tames_metricSymplecticForm : (metricSymplecticForm g J).Tames J :=
  tames_ofTames _ _

variable {g J} in
/-- For a complex structure `J` that preserves `g`, `ω_{g,J}(v, w) = g (J v) w`. -/
theorem metricSymplecticForm_eq_of_apply_apply
    (hJ : ∀ u v, (g : V →L[ℝ] V →L[ℝ] ℝ) (J u) (J v) = (g : V →L[ℝ] V →L[ℝ] ℝ) u v)
    (v w : V) : metricSymplecticForm g J v w = (g : V →L[ℝ] V →L[ℝ] ℝ) (J v) w := by
  have h := J.bilinForm_apply_left_eq_neg_apply_right
    (g := (g : V →L[ℝ] V →L[ℝ] ℝ).toBilinForm) hJ v w
  simp only [ContinuousLinearMap.toBilinForm_apply] at h
  rw [metricSymplecticForm_apply, h]
  ring

/-- For the inner product of a real inner product space and a complex structure `J` that
preserves it, `ω_{g,J}` is Tau Ceti's symplectic form `⟪J ·, ·⟫` of `J`. -/
theorem metricSymplecticForm_innerSL {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {J : AlmostComplexStructure E} (hJ : ∀ v w, inner ℝ (J v) (J w) = inner ℝ v w) :
    metricSymplecticForm ⟨innerSL ℝ, innerSL_mem_innerProducts⟩ J = J.symplecticForm hJ :=
  toBilinForm_injective <| LinearMap.ext₂ fun v w ↦
    (metricSymplecticForm_eq_of_apply_apply (g := ⟨innerSL ℝ, innerSL_mem_innerProducts⟩)
      (fun u v ↦ by rw [innerSL_apply_apply, innerSL_apply_apply]; exact hJ u v) v w).trans
      (J.symplecticForm_apply hJ v w).symm

variable [FiniteDimensional ℝ V]

/-- The symplectic form `ω_{g,J}` depends continuously on `J`. -/
theorem continuous_metricSymplecticForm : Continuous (metricSymplecticForm g) := by
  set G : V →L[ℝ] V →L[ℝ] ℝ := (g : V →L[ℝ] V →L[ℝ] ℝ)
  have hJ : Continuous fun J : AlmostComplexStructure V ↦
      LinearMap.toContinuousLinearMap J.toLinearMap :=
    AlmostComplexStructure.continuous_iff.1 continuous_id
  have h : (fun J ↦ (metricSymplecticForm g J).toBilinForm.toContinuousBilinearMap) =
      fun J : AlmostComplexStructure V ↦ (2 : ℝ)⁻¹ •
        (G.comp (LinearMap.toContinuousLinearMap J.toLinearMap) -
          (G.flip.comp (LinearMap.toContinuousLinearMap J.toLinearMap)).flip) := by
    ext J v w
    simp [G]
  rw [SymplecticForm.continuous_iff, h]
  exact (continuous_const (y := (2 : ℝ)⁻¹)).smul ((continuous_const.clm_comp hJ).sub
    ((ContinuousLinearMap.flipₗᵢ ℝ V V ℝ).continuous.comp (continuous_const.clm_comp hJ)))

end MetricSymplecticForm

section HomotopyEquiv

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (g : innerProducts V)

private theorem continuous_polarStraightHomotopy :
    Continuous fun p : I × SymplecticForm V ↦
      (tames_metricSymplecticForm g (metricPolarComplexStructure g p.2)).lineMap
        (compatible_metricPolarComplexStructure g p.2).tames p.1.property := by
  rw [SymplecticForm.continuous_iff]
  refine (ContinuousMap.Homotopy.affine
    ⟨_, SymplecticForm.continuous_iff.1 ((continuous_metricSymplecticForm g).comp
      ((continuous_const (y := g)).metricPolarComplexStructure continuous_id))⟩
    ⟨_, SymplecticForm.continuous_iff.1 continuous_id⟩).continuous.congr fun p ↦ ?_
  ext v w
  simp [AffineMap.lineMap_apply_module]

/-- The straight-line homotopy `(t, ω) ↦ (1 - t) ω_{g,J_{g,ω}} + t ω`, from `ω ↦ ω_{g,J_{g,ω}}` at
`t = 0` to the identity of the symplectic forms at `t = 1`. Both forms are tamed by `J_{g,ω}`, so
every form on the segment is symplectic. -/
noncomputable def polarStraightHomotopy :
    ContinuousMap.Homotopy
      ((⟨metricSymplecticForm g, continuous_metricSymplecticForm g⟩ :
          C(AlmostComplexStructure V, SymplecticForm V)).comp
        ⟨metricPolarComplexStructure g, continuous_const.metricPolarComplexStructure continuous_id⟩)
      (ContinuousMap.id (SymplecticForm V)) where
  toFun p := (tames_metricSymplecticForm g (metricPolarComplexStructure g p.2)).lineMap
    (compatible_metricPolarComplexStructure g p.2).tames p.1.property
  continuous_toFun := continuous_polarStraightHomotopy g
  map_zero_left _ := toBilinForm_injective (by simp)
  map_one_left _ := toBilinForm_injective (by simp)

/-- The value of `polarStraightHomotopy g` at `(t, ω)` is `(1 - t) ω_{g,J_{g,ω}} + t ω`, as a
bilinear form. -/
@[simp]
theorem toBilinForm_polarStraightHomotopy_apply (t : I) (ω : SymplecticForm V) :
    (polarStraightHomotopy g (t, ω)).toBilinForm =
      (1 - (t : ℝ)) • (metricSymplecticForm g (metricPolarComplexStructure g ω)).toBilinForm +
        (t : ℝ) • ω.toBilinForm :=
  Tames.toBilinForm_lineMap _ _ _

/-- The value of `polarStraightHomotopy g` at `(t, ω)` on a pair of vectors. -/
theorem polarStraightHomotopy_apply_apply (t : I) (ω : SymplecticForm V) (v w : V) :
    polarStraightHomotopy g (t, ω) v w =
      (1 - (t : ℝ)) * metricSymplecticForm g (metricPolarComplexStructure g ω) v w +
        (t : ℝ) * ω v w := by
  simp

private theorem continuous_polarCayleyHomotopy :
    Continuous fun p : I × AlmostComplexStructure V ↦
      (compatible_metricPolarComplexStructure g (metricSymplecticForm g p.2)).cayleyInterp
        (tames_metricSymplecticForm g p.2) p.1.property := by
  have hJ : Continuous fun J : AlmostComplexStructure V ↦
      LinearMap.toContinuousLinearMap J.toLinearMap :=
    AlmostComplexStructure.continuous_iff.1 continuous_id
  have hJ₀ := hJ.comp (((continuous_const (y := g)).metricPolarComplexStructure continuous_id).comp
    (continuous_metricSymplecticForm g))
  have hq : Continuous fun p : I × AlmostComplexStructure V ↦
      ((p.1 : ℝ), LinearMap.toContinuousLinearMap
          (metricPolarComplexStructure g (metricSymplecticForm g p.2)).toLinearMap,
        LinearMap.toContinuousLinearMap p.2.toLinearMap) :=
    (continuous_subtypeVal.comp continuous_fst).prodMk
      ((hJ₀.comp continuous_snd).prodMk (hJ.comp continuous_snd))
  have hf := (contDiffOn_cayleyPathFormula (R := V →L[ℝ] V) (n := 0)).continuousOn.comp_continuous
    hq fun p ↦ (compatible_metricPolarComplexStructure g _).mem_cayleyDomain
      (tames_metricSymplecticForm g p.2)
      (abs_le.2 ⟨by linarith [p.1.property.1], p.1.property.2⟩) rfl rfl
  rw [AlmostComplexStructure.continuous_iff]
  exact hf.congr fun p ↦
    ((compatible_metricPolarComplexStructure g _).toContinuousLinearMap_cayleyInterp
      (tames_metricSymplecticForm g p.2) p.1.property rfl rfl).symm

/-- The Cayley homotopy from `J ↦ J_{g,ω_{g,J}}` at `t = 0` to the identity of the complex
structures at `t = 1`: at time `t` it is Tau Ceti's Cayley interpolation with weight `t` from the
`ω_{g,J}`-compatible structure `J_{g,ω_{g,J}}` towards the `ω_{g,J}`-tame structure `J`. -/
noncomputable def polarCayleyHomotopy :
    ContinuousMap.Homotopy
      ((⟨metricPolarComplexStructure g,
          continuous_const.metricPolarComplexStructure continuous_id⟩ :
          C(SymplecticForm V, AlmostComplexStructure V)).comp
        ⟨metricSymplecticForm g, continuous_metricSymplecticForm g⟩)
      (ContinuousMap.id (AlmostComplexStructure V)) where
  toFun p := (compatible_metricPolarComplexStructure g (metricSymplecticForm g p.2)).cayleyInterp
    (tames_metricSymplecticForm g p.2) p.1.property
  continuous_toFun := continuous_polarCayleyHomotopy g
  map_zero_left _ := Compatible.cayleyInterp_zero _ _
  map_one_left _ := Compatible.cayleyInterp_one _ _

/-- The value of `polarCayleyHomotopy g` at `(t, J)` is the Cayley interpolation with weight `t`
from `J_{g,ω_{g,J}}` towards `J`. -/
@[simp]
theorem polarCayleyHomotopy_apply (t : I) (J : AlmostComplexStructure V) :
    polarCayleyHomotopy g (t, J) =
      (compatible_metricPolarComplexStructure g (metricSymplecticForm g J)).cayleyInterp
        (tames_metricSymplecticForm g J) t.property :=
  (rfl)

/-- For a fixed inner product `g`, the symplectic forms and the complex structures of `V` are
homotopy equivalent, through `ω ↦ J_{g,ω}` and `J ↦ ω_{g,J}`. The homotopies are
`polarStraightHomotopy g` and `polarCayleyHomotopy g`. -/
noncomputable def polarHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (SymplecticForm V) (AlmostComplexStructure V) where
  toFun :=
    ⟨metricPolarComplexStructure g, continuous_const.metricPolarComplexStructure continuous_id⟩
  invFun := ⟨metricSymplecticForm g, continuous_metricSymplecticForm g⟩
  left_inv := ⟨polarStraightHomotopy g⟩
  right_inv := ⟨polarCayleyHomotopy g⟩

/-- The forward map of `polarHomotopyEquiv g` is `ω ↦ J_{g,ω}`. -/
@[simp]
theorem polarHomotopyEquiv_toFun (ω : SymplecticForm V) :
    (polarHomotopyEquiv g).toFun ω = metricPolarComplexStructure g ω :=
  (rfl)

/-- The homotopy inverse of `polarHomotopyEquiv g` is `J ↦ ω_{g,J}`. -/
@[simp]
theorem polarHomotopyEquiv_symm_apply (J : AlmostComplexStructure V) :
    (polarHomotopyEquiv g).symm J = metricSymplecticForm g J :=
  (rfl)

end HomotopyEquiv

end SymplecticGeometry

end
