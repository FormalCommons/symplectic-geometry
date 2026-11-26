/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.UnitInterval
public import SymplecticGeometry.Analysis.Complex.RadialProjection
public import TauCeti.Topology.Algebra.Projectivization

/-!
# Two discs and an annulus in the complex projective line

The projective line `ℙ ℂ (Fin 2 → ℂ)` is the union of two open discs: the inner disc
`ProjectiveLine.innerDisc` of the points `[z : 1]` with `|z| < 2`, and the outer disc
`ProjectiveLine.outerDisc` of the points `[1 : w]` with `|w| < 2`. Their intersection is the
annulus `1/2 < |z| < 2` of the affine chart, which retracts radially onto the unit circle. This
file sets up these sets, and the continuous maps between products `X × ℙ ℂ (Fin 2 → ℂ)`, their
parts over the discs and the annulus, and `X × Circle` that the clutching construction over
`X × ℂP¹` of [Hatcher2017, §2.1] uses.

## Main definitions and results

* `SymplecticGeometry.ProjectiveLine.innerDisc`, `SymplecticGeometry.ProjectiveLine.outerDisc`:
  the two open discs, open (`isOpen_innerDisc`, `isOpen_outerDisc`) and covering the projective
  line (`innerDisc_union_outerDisc`), and inside the affine opens `1` and `0`
  (`innerDisc_subset_affineOpen`, `outerDisc_subset_affineOpen`).
* `SymplecticGeometry.ProjectiveLine.affineChart_symm_mem_annulus_iff`: the point `[z : 1]` lies
  in the annulus `innerDisc ∩ outerDisc` exactly when `1/2 < |z| < 2`.
* `SymplecticGeometry.ProjectiveLine.annulusCoord`: the affine coordinate `z` of the points
  `[z : 1]` of the annulus, as a nonzero complex number.
* `SymplecticGeometry.ProjectiveLine.annulusToCircle`: the radial retraction of the annulus onto
  `Circle`, `[z : 1] ↦ z / |z|` (`coe_annulusToCircle_apply`).
* `SymplecticGeometry.ProjectiveLine.clutchingMap X`: the map `(x, [z : 1]) ↦ (x, z / |z|)` from
  the product of `X` with the annulus to `X × Circle`.
* `SymplecticGeometry.ProjectiveLine.affineChartMap X i`: the inverse of the affine chart `i` in
  the second factor, from `X × (Fin 1 → ℂ)` to `X × ℙ ℂ (Fin 2 → ℂ)`.
* `SymplecticGeometry.ProjectiveLine.prodMkOne X`: the inclusion `x ↦ (x, [1 : 1])` of `X` in
  `X × ℙ ℂ (Fin 2 → ℂ)`.
* `SymplecticGeometry.ProjectiveLine.circleToAnnulus X`: the map `(x, u) ↦ (x, [u : 1])` from
  `X × Circle` to the product of `X` with the annulus, and
  `SymplecticGeometry.ProjectiveLine.annulusDeformation X`: the deformation
  `((x, [z : 1]), t) ↦ (x, [((1 - t) + t / |z|) z : 1])` (`radialDeform` in the affine coordinate)
  of that product onto the image of the
  first map, which is the identity at time `0` (`annulusDeformation_zero`) and `clutchingMap`
  followed by `circleToAnnulus` at time `1` (`annulusDeformation_one`).

## References

* [A. Hatcher, *Vector Bundles and K-Theory*][Hatcher2017], §2.1 (clutching functions over
  `X × S²`).
-/

public section

noncomputable section

open Set Projectivization

open scoped unitInterval LinearAlgebra.Projectivization

namespace SymplecticGeometry.ProjectiveLine

/-! ### The two discs of the projective line and their annulus -/

/-- The inner disc of the projective line: the points `[z : 1]` with `|z| < 2`. -/
def innerDisc : Set (ℙ ℂ (Fin 2 → ℂ)) :=
  affineOpen 1 ∩ affineChart 1 ⁻¹' {z | ‖z 0‖ < 2}

/-- The outer disc of the projective line: the points `[1 : w]` with `|w| < 2`, that is the points
`[z : 1]` with `|z| > 1/2` together with `∞ = [1 : 0]`. -/
def outerDisc : Set (ℙ ℂ (Fin 2 → ℂ)) :=
  affineOpen 0 ∩ affineChart 0 ⁻¹' {z | ‖z 0‖ < 2}

theorem innerDisc_def : innerDisc = affineOpen 1 ∩ affineChart 1 ⁻¹' {z | ‖z 0‖ < 2} :=
  (rfl)

theorem outerDisc_def : outerDisc = affineOpen 0 ∩ affineChart 0 ⁻¹' {z | ‖z 0‖ < 2} :=
  (rfl)

theorem mem_innerDisc_iff {p : ℙ ℂ (Fin 2 → ℂ)} :
    p ∈ innerDisc ↔ p ∈ affineOpen 1 ∧ ‖affineChart 1 p 0‖ < 2 :=
  Iff.rfl

theorem mem_outerDisc_iff {p : ℙ ℂ (Fin 2 → ℂ)} :
    p ∈ outerDisc ↔ p ∈ affineOpen 0 ∧ ‖affineChart 0 p 0‖ < 2 :=
  Iff.rfl

@[simp]
theorem mk_mem_innerDisc_iff (v : Fin 2 → ℂ) (hv : v ≠ 0) :
    mk ℂ v hv ∈ innerDisc ↔ v 1 ≠ 0 ∧ ‖v 0 / v 1‖ < 2 := by
  simp [mem_innerDisc_iff]

@[simp]
theorem mk_mem_outerDisc_iff (v : Fin 2 → ℂ) (hv : v ≠ 0) :
    mk ℂ v hv ∈ outerDisc ↔ v 0 ≠ 0 ∧ ‖v 1 / v 0‖ < 2 := by
  simp [mem_outerDisc_iff]

theorem innerDisc_subset_affineOpen : innerDisc ⊆ affineOpen 1 :=
  fun _ hp ↦ (mem_innerDisc_iff.1 hp).1

theorem outerDisc_subset_affineOpen : outerDisc ⊆ affineOpen 0 :=
  fun _ hp ↦ (mem_outerDisc_iff.1 hp).1

theorem isOpen_innerDisc : IsOpen innerDisc := by
  rw [innerDisc_def]
  simpa using (affineOpenPartialHomeomorph (K := ℂ) (n := 1) 1).isOpen_inter_preimage
    (isOpen_lt (continuous_norm.comp (continuous_apply 0)) continuous_const)

theorem isOpen_outerDisc : IsOpen outerDisc := by
  rw [outerDisc_def]
  simpa using (affineOpenPartialHomeomorph (K := ℂ) (n := 1) 0).isOpen_inter_preimage
    (isOpen_lt (continuous_norm.comp (continuous_apply 0)) continuous_const)

/-- The inner and outer discs cover the projective line. -/
theorem innerDisc_union_outerDisc : innerDisc ∪ outerDisc = univ := by
  refine eq_univ_of_forall fun p ↦ ?_
  induction p using Projectivization.ind with | h v hv =>
  simp only [mem_union, mk_mem_innerDisc_iff, mk_mem_outerDisc_iff]
  by_cases h1 : v 1 = 0
  · have h0 : v 0 ≠ 0 := fun h0 ↦ hv (funext fun i ↦ by fin_cases i <;> assumption)
    exact Or.inr ⟨h0, by simp [h1]⟩
  by_cases h : ‖v 0 / v 1‖ < 2
  · exact Or.inl ⟨h1, h⟩
  have h0 : v 0 ≠ 0 := fun h0 ↦ h (by simp [h0])
  refine Or.inr ⟨h0, ?_⟩
  rw [not_lt] at h
  have h' : ‖v 0 / v 1‖⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) h
  rw [← inv_div, norm_inv]
  linarith

/-- On the annulus, the affine coordinate `z` of a point `[z : 1]` is nonzero. -/
theorem affineChart_one_ne_zero_of_mem {p : ℙ ℂ (Fin 2 → ℂ)} (hp : p ∈ innerDisc ∩ outerDisc) :
    affineChart 1 p 0 ≠ 0 := by
  induction p using Projectivization.ind with | h v hv =>
  simp only [mem_inter_iff, mk_mem_innerDisc_iff, mk_mem_outerDisc_iff] at hp
  simpa using div_ne_zero hp.2.1 hp.1.1

/-- The affine coordinate `z` of the points `[z : 1]` of the annulus `innerDisc ∩ outerDisc`, as a
nonzero complex number. -/
def annulusCoord : C(↥(innerDisc ∩ outerDisc), ({0}ᶜ : Set ℂ)) :=
  ⟨fun p ↦ ⟨affineChart 1 p.val 0, affineChart_one_ne_zero_of_mem p.property⟩,
    (continuousOn_iff_continuous_domRestrict.1 ((continuous_apply 0).comp_continuousOn
      ((continuousOn_affineChart (K := ℂ) 1).mono
        fun _ (hp : _ ∈ innerDisc ∩ outerDisc) ↦ hp.1.1))).subtype_mk _⟩

@[simp]
theorem coe_annulusCoord_apply (p : ↥(innerDisc ∩ outerDisc)) :
    (annulusCoord p : ℂ) = affineChart 1 p.val 0 :=
  (rfl)

/-- The radial retraction of the annulus `innerDisc ∩ outerDisc` onto the unit circle,
`[z : 1] ↦ z / |z|`. -/
def annulusToCircle : C(↥(innerDisc ∩ outerDisc), Circle) :=
  Circle.radialProjection.comp annulusCoord

theorem annulusToCircle_def : annulusToCircle = Circle.radialProjection.comp annulusCoord :=
  (rfl)

/-- The radial retraction of the annulus sends `[z : 1]` to `z / |z|`. -/
@[simp]
theorem coe_annulusToCircle_apply (p : ↥(innerDisc ∩ outerDisc)) :
    (annulusToCircle p : ℂ) = ‖affineChart 1 p.val 0‖⁻¹ • affineChart 1 p.val 0 := by
  simp [annulusToCircle_def]

/-- The point `[z : 1]` of the projective line lies in the annulus `innerDisc ∩ outerDisc` exactly
when `1/2 < |z| < 2`. -/
theorem affineChart_symm_mem_annulus_iff (z : Fin 1 → ℂ) :
    (affineChart 1).symm z ∈ innerDisc ∩ outerDisc ↔ 2⁻¹ < ‖z 0‖ ∧ ‖z 0‖ < 2 := by
  rw [affineChart_symm_apply, mem_inter_iff, mk_mem_innerDisc_iff, mk_mem_outerDisc_iff]
  have h0 : Fin.insertNth (α := fun _ ↦ ℂ) 1 1 z 0 = z 0 := by
    simp
  rw [Fin.insertNth_apply_same, h0, div_one, one_div, norm_inv]
  constructor
  · rintro ⟨⟨-, h2⟩, hz, h'⟩
    refine ⟨?_, h2⟩
    have hpos : 0 < ‖z 0‖ := norm_pos_iff.2 hz
    rwa [inv_lt_comm₀ hpos (by norm_num)] at h'
  · rintro ⟨h', h2⟩
    have hpos : 0 < ‖z 0‖ := lt_trans (by norm_num) h'
    refine ⟨⟨one_ne_zero, h2⟩, norm_pos_iff.1 hpos, ?_⟩
    rwa [inv_lt_comm₀ hpos (by norm_num)]

/-! ### Maps on products with the projective line

The bodies of these maps are exposed: pullbacks of cores along them are compared with pullbacks
along the projections by definitional unfolding, as in `TauCeti.FiniteRankBundleCore.clutchingAut`.
-/

variable (X : Type*) [TopologicalSpace X]

/-- The map from the product of `X` with the annulus of the projective line to `X × Circle`:
the identity on `X`, and the radial retraction `annulusToCircle` on the annulus. -/
@[expose]
def clutchingMap :
    C(↥(Prod.snd ⁻¹' innerDisc ∩ Prod.snd ⁻¹' outerDisc : Set (X × ℙ ℂ (Fin 2 → ℂ))),
      X × Circle) :=
  ⟨fun w ↦ (w.val.1, annulusToCircle ⟨w.val.2, w.property⟩),
    (continuous_fst.comp continuous_subtypeVal).prodMk
      (annulusToCircle.continuous.comp
        ((continuous_snd.comp continuous_subtypeVal).subtype_mk _))⟩

@[simp]
theorem clutchingMap_apply
    (w : ↥(Prod.snd ⁻¹' innerDisc ∩ Prod.snd ⁻¹' outerDisc : Set (X × ℙ ℂ (Fin 2 → ℂ)))) :
    clutchingMap X w = (w.val.1, annulusToCircle ⟨w.val.2, w.property⟩) :=
  (rfl)

/-- The inverse of the affine chart `i` of the projective line, in the second factor of
`X × (Fin 1 → ℂ)`. -/
@[expose]
def affineChartMap (i : Fin 2) : C(X × (Fin 1 → ℂ), X × ℙ ℂ (Fin 2 → ℂ)) :=
  ContinuousMap.prodMap (.id X) ⟨(affineChart i).symm, continuous_affineChart_symm i⟩

@[simp]
theorem affineChartMap_apply (i : Fin 2) (p : X × (Fin 1 → ℂ)) :
    affineChartMap X i p = (p.1, (affineChart i).symm p.2) :=
  (rfl)

/-- The inclusion `x ↦ (x, [1 : 1])` of `X` in `X × ℙ ℂ (Fin 2 → ℂ)`. -/
def prodMkOne : C(X, X × ℙ ℂ (Fin 2 → ℂ)) :=
  (ContinuousMap.id X).prodMk (.const X (Projectivization.mk ℂ 1 one_ne_zero))

@[simp]
theorem prodMkOne_apply (x : X) : prodMkOne X x = (x, Projectivization.mk ℂ 1 one_ne_zero) :=
  (rfl)

/-! ### The circle in the annulus, and the radial deformation onto it -/

/-- The radial deformation of the annulus onto the unit circle, at time `t`, in the affine
coordinate: `z ↦ ((1 - t) + t / |z|) z`. -/
@[expose]
def radialDeform (z : Fin 1 → ℂ) (t : ℝ) : Fin 1 → ℂ :=
  ((1 - t) + t * ‖z 0‖⁻¹ : ℝ) • z

/-- The radial deformation keeps the annulus `1/2 < |z| < 2` in itself at each time `t ∈ [0, 1]`. -/
theorem radialDeform_mem {z : Fin 1 → ℂ} (hz : 2⁻¹ < ‖z 0‖ ∧ ‖z 0‖ < 2) {t : ℝ}
    (ht : t ∈ I) : 2⁻¹ < ‖radialDeform z t 0‖ ∧ ‖radialDeform z t 0‖ < 2 := by
  have hpos : 0 < ‖z 0‖ := lt_trans (by norm_num) hz.1
  have hc : 0 ≤ (1 - t) + t * ‖z 0‖⁻¹ :=
    add_nonneg (sub_nonneg.2 ht.2) (mul_nonneg ht.1 (inv_nonneg.2 (norm_nonneg _)))
  -- The new modulus `(1 - t) |z| + t` lies between `|z|` and `1`.
  have hn : ‖radialDeform z t 0‖ = (1 - t) * ‖z 0‖ + t := by
    rw [radialDeform, Pi.smul_apply, norm_smul, Real.norm_of_nonneg hc, add_mul, mul_assoc,
      inv_mul_cancel₀ hpos.ne', mul_one]
  rw [hn]
  obtain ⟨h0, h1⟩ := ht
  constructor <;> nlinarith [hz.1, hz.2]

/-- The map `(x, u) ↦ (x, [u : 1])` from `X × Circle` to the product of `X` with the annulus
`innerDisc ∩ outerDisc`. -/
@[expose]
def circleToAnnulus :
    C(X × Circle, ↥(Prod.snd ⁻¹' innerDisc ∩ Prod.snd ⁻¹' outerDisc :
      Set (X × ℙ ℂ (Fin 2 → ℂ)))) :=
  ⟨fun q ↦ ⟨(q.1, (affineChart 1).symm fun _ ↦ (q.2 : ℂ)),
      (affineChart_symm_mem_annulus_iff _).2 (by simp; norm_num)⟩,
    ((continuous_fst.prodMk ((continuous_affineChart_symm 1).comp
      (continuous_pi fun _ ↦ continuous_subtypeVal.comp continuous_snd)))).subtype_mk _⟩

@[simp]
theorem coe_circleToAnnulus_apply (q : X × Circle) :
    (circleToAnnulus X q : X × ℙ ℂ (Fin 2 → ℂ)) =
      (q.1, (affineChart 1).symm fun _ ↦ (q.2 : ℂ)) :=
  (rfl)

/-- The radial deformation of the product of `X` with the annulus onto the product with the unit
circle, `((x, [z : 1]), t) ↦ (x, [((1 - t) + t / |z|) z : 1])`, on the part over the annulus of
`(X × ℙ ℂ (Fin 2 → ℂ)) × I`. -/
@[expose]
def annulusDeformation :
    C(↥(Prod.fst ⁻¹' (Prod.snd ⁻¹' innerDisc) ∩ Prod.fst ⁻¹' (Prod.snd ⁻¹' outerDisc) :
        Set ((X × ℙ ℂ (Fin 2 → ℂ)) × I)),
      ↥(Prod.snd ⁻¹' innerDisc ∩ Prod.snd ⁻¹' outerDisc : Set (X × ℙ ℂ (Fin 2 → ℂ)))) :=
  ⟨fun w ↦ ⟨(w.val.1.1, (affineChart 1).symm
      (radialDeform (affineChart 1 w.val.1.2) (w.val.2 : ℝ))),
      (affineChart_symm_mem_annulus_iff _).2 <| radialDeform_mem
        (by
          rw [← affineChart_symm_mem_annulus_iff, (affineChart 1).left_inv
            (by rw [affineChart_source]; exact innerDisc_subset_affineOpen w.property.1)]
          exact w.property)
        w.val.2.property⟩, by
    refine Continuous.subtype_mk (continuous_fst.comp (continuous_fst.comp continuous_subtypeVal)
      |>.prodMk ((continuous_affineChart_symm 1).comp ?_)) _
    -- The affine coordinate is continuous on the annulus, and nonzero there.
    have hz : Continuous fun w : ↥(Prod.fst ⁻¹' (Prod.snd ⁻¹' innerDisc) ∩
        Prod.fst ⁻¹' (Prod.snd ⁻¹' outerDisc) : Set ((X × ℙ ℂ (Fin 2 → ℂ)) × I)) ↦
        affineChart 1 w.val.1.2 :=
      continuousOn_iff_continuous_domRestrict.1
        ((continuousOn_affineChart (K := ℂ) (n := 1) 1).mono (t := innerDisc)
          innerDisc_subset_affineOpen) |>.comp
        ((continuous_snd.comp (continuous_fst.comp continuous_subtypeVal)).subtype_mk
          fun w ↦ w.property.1)
    have ht : Continuous fun w : ↥(Prod.fst ⁻¹' (Prod.snd ⁻¹' innerDisc) ∩
        Prod.fst ⁻¹' (Prod.snd ⁻¹' outerDisc) : Set ((X × ℙ ℂ (Fin 2 → ℂ)) × I)) ↦
        (w.val.2 : ℝ) :=
      continuous_subtypeVal.comp (continuous_snd.comp continuous_subtypeVal)
    have hne : ∀ w : ↥(Prod.fst ⁻¹' (Prod.snd ⁻¹' innerDisc) ∩
        Prod.fst ⁻¹' (Prod.snd ⁻¹' outerDisc) : Set ((X × ℙ ℂ (Fin 2 → ℂ)) × I)),
        ‖affineChart 1 w.val.1.2 0‖ ≠ 0 := fun w ↦
      norm_ne_zero_iff.2 (affineChart_one_ne_zero_of_mem w.property)
    exact (((continuous_const.sub ht).add (ht.mul
      (((continuous_apply 0).comp hz).norm.inv₀ hne))).smul hz)⟩

theorem coe_annulusDeformation_apply
    (w : ↥(Prod.fst ⁻¹' (Prod.snd ⁻¹' innerDisc) ∩ Prod.fst ⁻¹' (Prod.snd ⁻¹' outerDisc) :
      Set ((X × ℙ ℂ (Fin 2 → ℂ)) × I))) :
    (annulusDeformation X w : X × ℙ ℂ (Fin 2 → ℂ)) =
      (w.val.1.1, (affineChart 1).symm
        (((1 - w.val.2) + w.val.2 * ‖affineChart 1 w.val.1.2 0‖⁻¹ : ℝ) •
          affineChart 1 w.val.1.2)) :=
  (rfl)

/-- At time `0`, the radial deformation of the annulus is the identity. -/
theorem annulusDeformation_zero
    (w : ↥(Prod.snd ⁻¹' innerDisc ∩ Prod.snd ⁻¹' outerDisc : Set (X × ℙ ℂ (Fin 2 → ℂ)))) :
    annulusDeformation X ⟨(w.val, 0), w.property⟩ = w :=
  Subtype.ext <| Prod.ext (by simp [coe_annulusDeformation_apply]) <| by
    simpa [coe_annulusDeformation_apply] using (affineChart 1).left_inv
      (by rw [affineChart_source]; exact innerDisc_subset_affineOpen w.property.1)

/-- At time `1`, the radial deformation of the annulus is the radial retraction `clutchingMap`
onto `X × Circle`, followed by the inclusion of `X × Circle` in the product with the annulus. -/
theorem annulusDeformation_one
    (w : ↥(Prod.snd ⁻¹' innerDisc ∩ Prod.snd ⁻¹' outerDisc : Set (X × ℙ ℂ (Fin 2 → ℂ)))) :
    annulusDeformation X ⟨(w.val, 1), w.property⟩ = circleToAnnulus X (clutchingMap X w) := by
  refine Subtype.ext <| Prod.ext (by simp [coe_annulusDeformation_apply]) ?_
  simp only [coe_annulusDeformation_apply, coe_circleToAnnulus_apply, clutchingMap_apply,
    coe_annulusToCircle_apply, Set.Icc.coe_one, sub_self, one_mul, zero_add]
  congr 1
  funext j
  rw [Subsingleton.elim j 0, Pi.smul_apply]

end SymplecticGeometry.ProjectiveLine

end
