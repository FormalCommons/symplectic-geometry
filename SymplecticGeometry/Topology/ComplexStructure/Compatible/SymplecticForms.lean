/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Analysis.InnerProductSpace.Symplectic.PolarComplexStructure.Smooth
public import SymplecticGeometry.Topology.ComplexStructure.Orthogonal
public import Mathlib.Topology.Homotopy.Affine
public import Mathlib.Topology.Homotopy.Equiv
public import TauCeti.Topology.Homotopy.DeformationRetract
public import TauCeti.Geometry.Symplectic.Cayley.Smooth
import SymplecticGeometry.Geometry.Symplectic.Cayley.Domain
import SymplecticGeometry.LinearAlgebra.Symplectic.Compatible
import SymplecticGeometry.Analysis.InnerProductSpace.LinearMap

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
equivalent. The same inverses fix the complex structures that preserve `g` and the forms
`g (J ·, ·)` they give, so the inclusions of these two subsets are homotopy equivalences too.

## Main definitions

* `SymplecticGeometry.metricSymplecticForm g J`: the form `ω_{g,J}`.
* `SymplecticGeometry.polarStraightHomotopy g`: the straight-line homotopy from
  `ω ↦ ω_{g,J_{g,ω}}` to the identity of the symplectic forms.
* `SymplecticGeometry.polarCayleyHomotopy g`: the Cayley homotopy from `J ↦ J_{g,ω_{g,J}}` to
  the identity of the complex structures.
* `SymplecticGeometry.polarHomotopyEquiv g`: the homotopy equivalence between the symplectic
  forms and the complex structures, with maps `ω ↦ J_{g,ω}` and `J ↦ ω_{g,J}`.
* `SymplecticGeometry.metricComplexStructures g`, `SymplecticGeometry.metricSymplecticForms g`:
  the complex structures that preserve `g`, and the forms `g (J ·, ·)` of these structures.
* `SymplecticGeometry.metricComplexStructuresHomotopyEquiv g`,
  `SymplecticGeometry.metricSymplecticFormsHomotopyEquiv g`: their inclusions, as homotopy
  equivalences.

## Main results

* `SymplecticGeometry.tames_metricSymplecticForm`: `J` tames `ω_{g,J}`.
* `SymplecticGeometry.metricSymplecticForm_eq_of_apply_apply`: for `g`-orthogonal `J`,
  `ω_{g,J}(v, w) = g (J v) w`.
* `SymplecticGeometry.continuous_metricSymplecticForm`: `J ↦ ω_{g,J}` is continuous.
* `SymplecticGeometry.metricSymplecticForm_innerSL`: for the inner product of an inner product
  space, `ω_{g,J}` is Tau Ceti's `AlmostComplexStructure.symplecticForm`.
* `SymplecticGeometry.mem_metricComplexStructures_innerSL`: for the inner product of an inner
  product space, `J` preserves it exactly when `⟪J u, J v⟫ = ⟪u, v⟫`.
* `SymplecticGeometry.metricComplexStructures_innerSL`: for the standard inner product of
  `EuclideanSpace ℝ n`, the `g`-orthogonal structures are `orthogonalComplexStructures n`.
* `SymplecticGeometry.metricPolarComplexStructure_eq_inverse_mul_and_homotopyEquiv`: the formula,
  smoothness, naturality and compatibility of `J_{g,ω}`, its value for `g = ω(·, J ·)`, and the
  three homotopy equivalences.

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
      (fun u v ↦ by simpa only [innerSL_real_apply_apply] using hJ u v) v w).trans
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

section MetricSubsets

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (g : innerProducts V)

/-- The complex structures that preserve the inner product `g`, the space `𝒥(V, g)` of
`g`-orthogonal complex structures. -/
def metricComplexStructures : Set (AlmostComplexStructure V) :=
  {J | ∀ u v, (g : V →L[ℝ] V →L[ℝ] ℝ) (J u) (J v) = (g : V →L[ℝ] V →L[ℝ] ℝ) u v}

/-- The symplectic forms `g (J ·, ·)` for the `g`-orthogonal complex structures `J`, the space
`Ω(V, g)` of symplectic forms compatible with `g`. -/
def metricSymplecticForms : Set (SymplecticForm V) :=
  {ω | ∃ J ∈ metricComplexStructures g, ∀ v w, ω v w = (g : V →L[ℝ] V →L[ℝ] ℝ) (J v) w}

variable {g}

@[simp]
theorem mem_metricComplexStructures {J : AlmostComplexStructure V} :
    J ∈ metricComplexStructures g ↔
      ∀ u v, (g : V →L[ℝ] V →L[ℝ] ℝ) (J u) (J v) = (g : V →L[ℝ] V →L[ℝ] ℝ) u v :=
  Iff.rfl

/-- For the inner product of a real inner product space, a complex structure preserves it
exactly when `⟪J u, J v⟫ = ⟪u, v⟫` for all `u` and `v`. -/
theorem mem_metricComplexStructures_innerSL {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {J : AlmostComplexStructure E} :
    J ∈ metricComplexStructures ⟨innerSL ℝ, innerSL_mem_innerProducts⟩ ↔
      ∀ u v, inner ℝ (J u) (J v) = inner ℝ u v :=
  Iff.rfl

@[simp]
theorem mem_metricSymplecticForms {ω : SymplecticForm V} :
    ω ∈ metricSymplecticForms g ↔
      ∃ J ∈ metricComplexStructures g, ∀ v w, ω v w = (g : V →L[ℝ] V →L[ℝ] ℝ) (J v) w :=
  Iff.rfl

/-- For the standard inner product of `EuclideanSpace ℝ n`, the `g`-orthogonal complex structures
are the orthogonal complex structures `orthogonalComplexStructures n`. -/
theorem metricComplexStructures_innerSL (n : Type*) [Fintype n] :
    metricComplexStructures ⟨innerSL ℝ, innerSL_mem_innerProducts⟩ =
      orthogonalComplexStructures n := by
  ext J
  rw [mem_metricComplexStructures_innerSL, mem_orthogonalComplexStructures_iff_inner]

/-- The forms compatible with `g` are the forms `ω_{g,J}` of the `g`-orthogonal complex
structures `J`. -/
theorem metricSymplecticForms_eq_image :
    metricSymplecticForms g = metricSymplecticForm g '' metricComplexStructures g := by
  ext ω
  refine exists_congr fun J ↦ and_congr_right fun hJ ↦ ⟨fun h ↦ ?_, ?_⟩
  · exact toBilinForm_injective <| LinearMap.ext₂ fun v w ↦
      (metricSymplecticForm_eq_of_apply_apply hJ v w).trans (h v w).symm
  · rintro rfl
    exact metricSymplecticForm_eq_of_apply_apply hJ

/-- For a `g`-orthogonal complex structure `J`, the form `ω_{g,J}` is compatible with `g`. -/
theorem metricSymplecticForm_mem_metricSymplecticForms {J : AlmostComplexStructure V}
    (hJ : J ∈ metricComplexStructures g) : metricSymplecticForm g J ∈ metricSymplecticForms g :=
  ⟨J, hJ, metricSymplecticForm_eq_of_apply_apply hJ⟩

/-- A `g`-orthogonal complex structure `J` is compatible with `ω_{g,J}`. -/
theorem compatible_metricSymplecticForm {J : AlmostComplexStructure V}
    (hJ : J ∈ metricComplexStructures g) : (metricSymplecticForm g J).Compatible J :=
  .of_tames ((invariant_iff _ _).2 fun v w ↦ by
    rw [metricSymplecticForm_eq_of_apply_apply hJ, metricSymplecticForm_eq_of_apply_apply hJ,
      hJ]) (tames_metricSymplecticForm g J)

variable [FiniteDimensional ℝ V]

variable (g) in
/-- `J_{g,ω}` is `g`-orthogonal. -/
theorem metricPolarComplexStructure_mem_metricComplexStructures (ω : SymplecticForm V) :
    metricPolarComplexStructure g ω ∈ metricComplexStructures g :=
  apply_metricPolarComplexStructure_apply g ω

/-- A `g`-orthogonal complex structure `J` is `J_{g,ω}` for `ω = ω_{g,J}`. -/
theorem metricPolarComplexStructure_metricSymplecticForm {J : AlmostComplexStructure V}
    (hJ : J ∈ metricComplexStructures g) :
    metricPolarComplexStructure g (metricSymplecticForm g J) = J :=
  metricPolarComplexStructure_eq_iff.2 ⟨hJ, compatible_metricSymplecticForm hJ⟩

/-- A form `ω` compatible with `g` is `ω_{g,J}` for `J = J_{g,ω}`. -/
theorem metricSymplecticForm_metricPolarComplexStructure {ω : SymplecticForm V}
    (hω : ω ∈ metricSymplecticForms g) :
    metricSymplecticForm g (metricPolarComplexStructure g ω) = ω := by
  rw [metricSymplecticForms_eq_image] at hω
  obtain ⟨J, hJ, rfl⟩ := hω
  rw [metricPolarComplexStructure_metricSymplecticForm hJ]

variable (g)

/-- The inclusion of the `g`-orthogonal complex structures into all complex structures is a
homotopy equivalence, with homotopy inverse `J ↦ J_{g,ω_{g,J}}`. This inverse fixes the
`g`-orthogonal structures, and its composite with the inclusion is joined to the identity by
`polarCayleyHomotopy g`. -/
noncomputable def metricComplexStructuresHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (metricComplexStructures g) (AlmostComplexStructure V) :=
  .ofDeformationRetraction (ContinuousMap.subtypeVal _)
    ⟨fun J ↦ ⟨metricPolarComplexStructure g (metricSymplecticForm g J),
        metricPolarComplexStructure_mem_metricComplexStructures g _⟩,
      ((continuous_const.metricPolarComplexStructure continuous_id).comp
        (continuous_metricSymplecticForm g)).subtype_mk _⟩
    (fun J ↦ Subtype.ext (metricPolarComplexStructure_metricSymplecticForm J.property))
    ⟨polarCayleyHomotopy g⟩

/-- The forward map of `metricComplexStructuresHomotopyEquiv g` is the inclusion. -/
@[simp]
theorem metricComplexStructuresHomotopyEquiv_toFun :
    (metricComplexStructuresHomotopyEquiv g).toFun = ContinuousMap.subtypeVal _ :=
  ContinuousMap.HomotopyEquiv.ofDeformationRetraction_toFun _ _ _ _

/-- `metricComplexStructuresHomotopyEquiv g` sends a `g`-orthogonal structure to itself. -/
theorem metricComplexStructuresHomotopyEquiv_apply (J : metricComplexStructures g) :
    metricComplexStructuresHomotopyEquiv g J = J :=
  ContinuousMap.HomotopyEquiv.ofDeformationRetraction_apply _ _ _ _ J

/-- The homotopy inverse of `metricComplexStructuresHomotopyEquiv g` is `J ↦ J_{g,ω_{g,J}}`. -/
@[simp]
theorem coe_metricComplexStructuresHomotopyEquiv_symm_apply (J : AlmostComplexStructure V) :
    ((metricComplexStructuresHomotopyEquiv g).symm J : AlmostComplexStructure V) =
      metricPolarComplexStructure g (metricSymplecticForm g J) :=
  congrArg Subtype.val (ContinuousMap.HomotopyEquiv.ofDeformationRetraction_symm_apply _ _ _ _ J)

/-- The inclusion of the symplectic forms compatible with `g` into all symplectic forms is a
homotopy equivalence, with homotopy inverse `ω ↦ ω_{g,J_{g,ω}}`. This inverse fixes the forms
compatible with `g`, and its composite with the inclusion is joined to the identity by
`polarStraightHomotopy g`. -/
noncomputable def metricSymplecticFormsHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (metricSymplecticForms g) (SymplecticForm V) :=
  .ofDeformationRetraction (ContinuousMap.subtypeVal _)
    ⟨fun ω ↦ ⟨metricSymplecticForm g (metricPolarComplexStructure g ω),
        metricSymplecticForm_mem_metricSymplecticForms
          (metricPolarComplexStructure_mem_metricComplexStructures g ω)⟩,
      ((continuous_metricSymplecticForm g).comp
        (continuous_const.metricPolarComplexStructure continuous_id)).subtype_mk _⟩
    (fun ω ↦ Subtype.ext (metricSymplecticForm_metricPolarComplexStructure ω.property))
    ⟨polarStraightHomotopy g⟩

/-- The forward map of `metricSymplecticFormsHomotopyEquiv g` is the inclusion. -/
@[simp]
theorem metricSymplecticFormsHomotopyEquiv_toFun :
    (metricSymplecticFormsHomotopyEquiv g).toFun = ContinuousMap.subtypeVal _ :=
  ContinuousMap.HomotopyEquiv.ofDeformationRetraction_toFun _ _ _ _

/-- `metricSymplecticFormsHomotopyEquiv g` sends a form compatible with `g` to itself. -/
theorem metricSymplecticFormsHomotopyEquiv_apply (ω : metricSymplecticForms g) :
    metricSymplecticFormsHomotopyEquiv g ω = ω :=
  ContinuousMap.HomotopyEquiv.ofDeformationRetraction_apply _ _ _ _ ω

/-- The homotopy inverse of `metricSymplecticFormsHomotopyEquiv g` is `ω ↦ ω_{g,J_{g,ω}}`. -/
@[simp]
theorem coe_metricSymplecticFormsHomotopyEquiv_symm_apply (ω : SymplecticForm V) :
    ((metricSymplecticFormsHomotopyEquiv g).symm ω : SymplecticForm V) =
      metricSymplecticForm g (metricPolarComplexStructure g ω) :=
  congrArg Subtype.val (ContinuousMap.HomotopyEquiv.ofDeformationRetraction_symm_apply _ _ _ _ ω)

end MetricSubsets

section Milestone

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- Let `V` be a finite-dimensional real normed space, `g` an inner product on `V` and `ω` a
symplectic form on `V`.

* If `g (A u) v = ω u v` and `Q` is the square root of `-A²` that is self-adjoint and positive
  definite for `g` (such `A` and `Q` exist), then `J_{g,ω} = Q⁻¹ A`.
* `J_{g,ω}` is smooth, indeed analytic, in `(g, ω)`: for every finite-dimensional real inner
  product space `W` and isomorphism `e : V ≃L[ℝ] W`, the formula
  `SymplecticGeometry.metricPolarFormula` is analytic on the open set
  `SymplecticGeometry.polarDomain W`, which contains the pair of `g` and `ω` carried to `W`, and its
  value there is `J_{g,ω}` conjugated by `e`.
* `J_{g,ω}` is natural under linear isomorphisms, so equivariant under `GL(V)`.
* `J_{g,ω}` is compatible with `ω` and preserves `g`.
* If `J` is compatible with `ω`, then `J_{g,ω} = J` for `g = ω(·, J ·)`.
* For fixed `g`, the map `ω ↦ J_{g,ω}` is a homotopy equivalence from the symplectic forms to
  the complex structures, with homotopy inverse `J ↦ ω_{g,J} = ½ (g (J ·, ·) - g (·, J ·))`; and
  the inclusions of the `g`-orthogonal complex structures and of the symplectic forms compatible
  with `g` are homotopy equivalences.

No parity hypothesis on the dimension is needed: in odd dimension there are no symplectic forms
and no complex structures, and every statement holds trivially.

Milestone: *Complex structures versus symplectic forms*. -/
theorem metricPolarComplexStructure_eq_inverse_mul_and_homotopyEquiv :
    (∀ (g : innerProducts V) (ω : SymplecticForm V),
      (∃ A Q : V →L[ℝ] V, (∀ u v, (g : V →L[ℝ] V →L[ℝ] ℝ) (A u) v = ω u v) ∧
        (∀ u v, (g : V →L[ℝ] V →L[ℝ] ℝ) (Q u) v = (g : V →L[ℝ] V →L[ℝ] ℝ) u (Q v)) ∧
        (∀ v, v ≠ 0 → 0 < (g : V →L[ℝ] V →L[ℝ] ℝ) (Q v) v) ∧ Q * Q = -(A * A)) ∧
      ∀ A Q : V →L[ℝ] V, (∀ u v, (g : V →L[ℝ] V →L[ℝ] ℝ) (A u) v = ω u v) →
        (∀ u v, (g : V →L[ℝ] V →L[ℝ] ℝ) (Q u) v = (g : V →L[ℝ] V →L[ℝ] ℝ) u (Q v)) →
        (∀ v, v ≠ 0 → 0 < (g : V →L[ℝ] V →L[ℝ] ℝ) (Q v) v) → Q * Q = -(A * A) →
        LinearMap.toContinuousLinearMap (metricPolarComplexStructure g ω).toLinearMap =
          Ring.inverse Q * A) ∧
    (∀ (W : Type*) [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
        (e : V ≃L[ℝ] W),
      IsOpen (polarDomain W) ∧
        ContDiffOn ℝ ⊤ (fun p ↦ metricPolarFormula p.1 p.2) (polarDomain W) ∧
        ∀ (g : innerProducts V) (ω : SymplecticForm V),
          ((innerProducts.transport e g : W →L[ℝ] W →L[ℝ] ℝ),
              (ω.transport e.toLinearEquiv).toBilinForm.toContinuousBilinearMap) ∈
            polarDomain W ∧
          metricPolarFormula (innerProducts.transport e g)
              (ω.transport e.toLinearEquiv).toBilinForm.toContinuousBilinearMap =
            e.conjContinuousAlgEquiv
              (LinearMap.toContinuousLinearMap (metricPolarComplexStructure g ω).toLinearMap)) ∧
    (∀ (W : Type*) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
        (e : V ≃L[ℝ] W) (g : innerProducts V) (ω : SymplecticForm V),
      metricPolarComplexStructure (innerProducts.transport e g) (ω.transport e.toLinearEquiv) =
        (metricPolarComplexStructure g ω).transport e.toLinearEquiv) ∧
    (∀ (g : innerProducts V) (ω : SymplecticForm V),
      ω.Compatible (metricPolarComplexStructure g ω) ∧
        metricPolarComplexStructure g ω ∈ metricComplexStructures g) ∧
    (∀ (ω : SymplecticForm V) (J : AlmostComplexStructure V) (h : ω.Compatible J),
      metricPolarComplexStructure ⟨_, h.associatedBilinForm_mem_innerProducts⟩ ω = J) ∧
    ∀ g : innerProducts V,
      (∃ e : ContinuousMap.HomotopyEquiv (SymplecticForm V) (AlmostComplexStructure V),
        (∀ ω, e ω = metricPolarComplexStructure g ω) ∧ ∀ J, e.symm J = metricSymplecticForm g J) ∧
      (∃ e : ContinuousMap.HomotopyEquiv (metricComplexStructures g) (AlmostComplexStructure V),
        ∀ J, e J = J) ∧
      ∃ e : ContinuousMap.HomotopyEquiv (metricSymplecticForms g) (SymplecticForm V),
        ∀ ω, e ω = ω := by
  refine ⟨fun g ω ↦ ⟨exists_operator_and_sqrt_neg_mul_self g ω,
      fun _ _ hA hQs hQp hQ ↦ metricPolarComplexStructure_eq_inverse_mul hA hQs hQp hQ⟩,
    fun W _ _ _ e ↦ ⟨isOpen_polarDomain W, contDiffOn_metricPolarFormula, fun g ω ↦
      ⟨mem_polarDomain _ _, ?_⟩⟩,
    fun W _ _ _ e g ω ↦ metricPolarComplexStructure_transport g ω e,
    fun g ω ↦ ⟨compatible_metricPolarComplexStructure g ω,
      metricPolarComplexStructure_mem_metricComplexStructures g ω⟩,
    fun ω J h ↦ metricPolarComplexStructure_associatedBilinForm h,
    fun g ↦ ⟨⟨polarHomotopyEquiv g, polarHomotopyEquiv_toFun g, polarHomotopyEquiv_symm_apply g⟩,
      ⟨metricComplexStructuresHomotopyEquiv g, metricComplexStructuresHomotopyEquiv_apply g⟩,
      ⟨metricSymplecticFormsHomotopyEquiv g, metricSymplecticFormsHomotopyEquiv_apply g⟩⟩⟩
  rw [metricPolarFormula_eq, metricPolarComplexStructure_transport]
  ext v
  simp

end Milestone

end SymplecticGeometry

end
