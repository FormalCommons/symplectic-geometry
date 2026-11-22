/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Topology.LocalAtTarget
public import TauCeti.AlgebraicTopology.Sphere.CubeQuotient

/-!
# The collapse of the cube is an open embedding on the interior

Tau Ceti's `TauCeti.cubeToSphere n : I^n → Sⁿ` collapses the boundary of the cube to the north
pole and is injective elsewhere. Since the cube is compact and the sphere Hausdorff, it is a closed
map, and its restriction to the preimage of the complement of the north pole, which is the
complement of the boundary, is a homeomorphism onto that complement. So the collapse restricted to
the complement of the boundary is an open embedding into the sphere
(`TauCeti.isOpenEmbedding_cubeToSphere_comp_subtypeVal`).

In dimension `2` the complement of the boundary of the square is read in `ℂ`: the open square
`SymplecticGeometry.openSquare` of the points `z` with `0 < re z < 1` and `0 < im z < 1` is
homeomorphic to it through `z ↦ (re z, im z)` (`SymplecticGeometry.openSquareHomeomorph`), and the
composite `SymplecticGeometry.openSquareToSphere` is an open embedding of the open square into
`S²`.

## Main definitions

* `SymplecticGeometry.openSquare`: the open unit square of `ℂ`, as an open set.
* `SymplecticGeometry.openSquareHomeomorph`: the open square is the complement of the boundary of
  `I^2`.
* `SymplecticGeometry.openSquareToSphere`: the collapse of the square, read on the open square.

## Main results

* `TauCeti.isOpenEmbedding_cubeToSphere_comp_subtypeVal`: the collapse is an open embedding on
  the complement of the boundary of the cube.
* `SymplecticGeometry.isOpenEmbedding_openSquareToSphere`: the same for the open square of `ℂ`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.1, where `πₙ(X, x₀)` is described by maps out of `Iⁿ / ∂Iⁿ = Sⁿ`.
-/

public section

noncomputable section

open Metric Set Topology Topology.Homotopy
open scoped unitInterval

namespace TauCeti

/-- **The collapse of the cube is an open embedding on the interior.** The map
`TauCeti.cubeToSphere n : I^n → Sⁿ`, restricted to the complement of the boundary of the cube, is
an open embedding. -/
theorem isOpenEmbedding_cubeToSphere_comp_subtypeVal (n : ℕ) :
    IsOpenEmbedding (cubeToSphere n ∘
      ((↑) : ((Cube.boundary (Fin n))ᶜ : Set (I^(Fin n))) → I^(Fin n))) := by
  set f := cubeToSphere n
  set V : Set (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := {sphereNorthPole n}ᶜ
  have hpre : f ⁻¹' V = (Cube.boundary (Fin n))ᶜ := by
    ext y
    simp [f, V, cubeToSphere_eq_sphereNorthPole_iff]
  have hinj : Function.Injective (V.restrictPreimage f) := by
    rintro ⟨y, hy⟩ ⟨z, _⟩ h
    rcases cubeToSphere_eq_cubeToSphere_iff.1 (congrArg Subtype.val h) with h' | ⟨h', -⟩
    · exact Subtype.ext h'
    · rw [hpre] at hy
      exact absurd h' hy
  have hsurj : Function.Surjective (V.restrictPreimage f) := by
    rintro ⟨s, hs⟩
    obtain ⟨y, rfl⟩ := exists_cubeToSphere_eq_of_ne hs
    exact ⟨⟨y, hs⟩, rfl⟩
  -- The cube is compact and the sphere Hausdorff, so the restriction to the preimage of `V` is a
  -- closed embedding onto `V`, hence a homeomorphism onto `V`.
  have hemb := IsClosedEmbedding.of_continuous_injective_isClosedMap
    (f.continuous.restrictPreimage (s := V)) hinj
    (IsClosedMap.restrictPreimage f.continuous.isClosedMap V)
  let h := (Equiv.ofBijective _ ⟨hinj, hsurj⟩).toHomeomorphOfIsInducing hemb.isInducing
  convert (isOpen_compl_singleton.isOpenEmbedding_subtypeVal.comp h.isOpenEmbedding).comp
    (Homeomorph.setCongr hpre.symm).isOpenEmbedding using 1
  -- Both sides send `y` to `f y`; `Homeomorph.setCongr` has no lemma for its values.
  ext y : 1
  rfl

end TauCeti

namespace SymplecticGeometry

open Complex

/-- The open unit square of `ℂ`: the points `z` with `0 < re z < 1` and `0 < im z < 1`, as an
open set. -/
def openSquare : TopologicalSpace.Opens ℂ :=
  ⟨Ioo 0 1 ×ℂ Ioo 0 1, isOpen_Ioo.reProdIm isOpen_Ioo⟩

theorem coe_openSquare : (openSquare : Set ℂ) = Ioo 0 1 ×ℂ Ioo 0 1 :=
  (rfl)

@[simp]
theorem mem_openSquare_iff {z : ℂ} :
    z ∈ openSquare ↔ (0 < z.re ∧ z.re < 1) ∧ 0 < z.im ∧ z.im < 1 :=
  mem_reProdIm

/-- The open square is connected. -/
instance : ConnectedSpace openSquare := by
  have h : convexHull ℝ (openSquare : Set ℂ) = openSquare := by
    rw [coe_openSquare, convexHull_reProdIm, (convex_Ioo 0 1).convexHull_eq]
  refine Subtype.connectedSpace (Convex.isConnected (h ▸ convex_convexHull ℝ _) ?_)
  exact ⟨⟨1 / 2, 1 / 2⟩, by norm_num⟩

/-- A point of the cube lies off the boundary exactly when its coordinates lie in `(0, 1)`. -/
theorem _root_.Cube.notMem_boundary_iff {N : Type*} {y : I^N} :
    y ∉ Cube.boundary N ↔ ∀ i, 0 < (y i : ℝ) ∧ (y i : ℝ) < 1 := by
  simp only [Cube.boundary, mem_ofPred_eq, not_exists, not_or, Subtype.ext_iff, Icc.coe_zero,
    Icc.coe_one]
  exact forall_congr' fun i ↦
    ⟨fun h ↦ ⟨(y i).property.1.lt_of_ne (Ne.symm h.1), (y i).property.2.lt_of_ne h.2⟩,
      fun h ↦ ⟨h.1.ne', h.2.ne⟩⟩

/-- The open square of `ℂ` is the complement of the boundary of `I^2`, through
`z ↦ (re z, im z)`. -/
def openSquareHomeomorph : openSquare ≃ₜ ((Cube.boundary (Fin 2))ᶜ : Set (I^(Fin 2))) where
  toFun z := ⟨fun i ↦ ⟨![(z : ℂ).re, (z : ℂ).im] i, by
      have h := mem_openSquare_iff.1 z.prop
      fin_cases i <;> simp <;> constructor <;> linarith⟩, by
    rw [mem_compl_iff, Cube.notMem_boundary_iff]
    have h := mem_openSquare_iff.1 z.prop
    intro i
    fin_cases i <;> simpa using by tauto⟩
  invFun y := ⟨(y.val 0 : ℝ) + (y.val 1 : ℝ) * Complex.I, by
    have h := Cube.notMem_boundary_iff.1 y.prop
    simpa using ⟨h 0, h 1⟩⟩
  left_inv z := Subtype.ext (by simp)
  right_inv y := by
    ext i
    fin_cases i <;> simp
  continuous_toFun := by
    refine Continuous.subtype_mk (continuous_pi fun i ↦ Continuous.subtype_mk ?_ _) _
    fin_cases i
    · exact continuous_re.comp continuous_subtypeVal
    · exact continuous_im.comp continuous_subtypeVal
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    have h (i : Fin 2) : Continuous fun y : ((Cube.boundary (Fin 2))ᶜ : Set (I^(Fin 2))) ↦
        ((y.val i : ℝ) : ℂ) :=
      continuous_ofReal.comp (continuous_subtypeVal.comp
        ((continuous_apply i).comp continuous_subtypeVal))
    exact (h 0).add ((h 1).mul continuous_const)

@[simp]
theorem coe_openSquareHomeomorph_apply_zero (z : openSquare) :
    ((openSquareHomeomorph z : I^(Fin 2)) 0 : ℝ) = (z : ℂ).re :=
  (rfl)

@[simp]
theorem coe_openSquareHomeomorph_apply_one (z : openSquare) :
    ((openSquareHomeomorph z : I^(Fin 2)) 1 : ℝ) = (z : ℂ).im :=
  (rfl)

@[simp]
theorem coe_openSquareHomeomorph_symm_apply (y : ((Cube.boundary (Fin 2))ᶜ : Set (I^(Fin 2)))) :
    (openSquareHomeomorph.symm y : ℂ) = (y.val 0 : ℝ) + (y.val 1 : ℝ) * Complex.I :=
  (rfl)

/-- The collapse `TauCeti.cubeToSphere 2` of the square onto `S²`, read on the open square of
`ℂ` through `z ↦ (re z, im z)`. -/
def openSquareToSphere (z : openSquare) : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  TauCeti.cubeToSphere 2 (openSquareHomeomorph z)

theorem openSquareToSphere_def (z : openSquare) :
    openSquareToSphere z = TauCeti.cubeToSphere 2 (openSquareHomeomorph z) :=
  (rfl)

/-- The collapse of the square, read on the open square of `ℂ`, is an open embedding into `S²`. -/
theorem isOpenEmbedding_openSquareToSphere : IsOpenEmbedding openSquareToSphere :=
  (TauCeti.isOpenEmbedding_cubeToSphere_comp_subtypeVal 2).comp
    openSquareHomeomorph.isOpenEmbedding

end SymplecticGeometry

end
