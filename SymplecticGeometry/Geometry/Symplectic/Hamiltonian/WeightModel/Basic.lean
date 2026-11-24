/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Complex.Euclidean.Space
public import TauCeti.Analysis.InnerProductSpace.PiL2
public import TauCeti.Geometry.Symplectic.Hamiltonian.WeightModel.Basic
public import TauCeti.Geometry.Symplectic.StandardCompatible

/-!
# Coordinates of the weight model

Tau Ceti's `TauCeti.weightRotation θ` rotates the `k`-th coordinate plane of
`EuclideanSpace ℝ ι × EuclideanSpace ℝ ι` by the angle `θₖ`. This file reads it in the complex
coordinates `u : ι → ℂ`, through `TauCeti.complexToRealEuclidean ι` (real and imaginary parts)
and `EuclideanSpace.sumEquivProd`: it is the coordinatewise multiplication
`uₖ ↦ exp (θₖ i) uₖ` (`TauCeti.weightRotation_sumEquivProd_complexToRealEuclidean`).

It also computes the standard symplectic form of these coordinates on vectors with disjoint
supports: `TauCeti.stdSymplecticForm_eq_zero_of_forall`.

Last, it splits `ℂ^ι = ℝ^ι × ℝ^ι` along a predicate `p` on the indices.
`TauCeti.weightModelSplit p` is the continuous linear equivalence of `ℂ^ι` with
`ℂ^{i // p i} × ℂ^{i // ¬p i}` restricting both real coordinates to each part; it is Tau Ceti's
`EuclideanSpace.sumComplEquivProd` applied to both coordinates. The squared norm on `ℂ^ι` is the
sum of those of the parts (`TauCeti.norm_sq_add_norm_sq_eq_weightModelSplit`), so a round ball of
`ℂ^ι` contains a product of round balls of the parts. When the weights vanish at each index
outside `p`, the moment map of the weight model factors through the first part:
`TauCeti.weightMomentMap_eq_weightMomentMap_weightModelSplit_fst`.
-/

public section

namespace TauCeti

/-- Read through `EuclideanSpace.sumEquivProd` and `complexToRealEuclidean`, the rotation
`weightRotation θ` of `ℂ^ι` is the multiplication `uₖ ↦ exp (θₖ i) uₖ`. -/
theorem weightRotation_sumEquivProd_complexToRealEuclidean {ι : Type*} [Fintype ι]
    (θ : ι → ℝ) (u : ι → ℂ) :
    weightRotation θ (EuclideanSpace.sumEquivProd (complexToRealEuclidean ι u)) =
      EuclideanSpace.sumEquivProd
        (complexToRealEuclidean ι fun k ↦ Complex.exp (θ k * Complex.I) * u k) := by
  ext k <;> simp [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  ring

/-- The standard symplectic form of `ℂ^ι = ℝ^ι × ℝ^ι` vanishes on two vectors that have, at each
index, one of them with both coordinates zero. -/
theorem stdSymplecticForm_eq_zero_of_forall {ι : Type*} [Fintype ι]
    {v w : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι}
    (h : ∀ k, v.1 k = 0 ∧ v.2 k = 0 ∨ w.1 k = 0 ∧ w.2 k = 0) : stdSymplecticForm v w = 0 := by
  rw [stdSymplecticForm_apply, PiLp.inner_apply, PiLp.inner_apply, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun k _ ↦ ?_
  rcases h k with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]

section Split

variable {ι : Type*} [Fintype ι] (p : ι → Prop) [DecidablePred p]

/-- The splitting of `ℂ^ι = ℝ^ι × ℝ^ι` along a predicate `p` on the indices: the pair `(x, y)`
goes to the restrictions of `x` and `y` to the indices with `p`, and those to the others. -/
noncomputable def weightModelSplit :
    (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ≃L[ℝ]
      (EuclideanSpace ℝ {i // p i} × EuclideanSpace ℝ {i // p i}) ×
        (EuclideanSpace ℝ {i // ¬p i} × EuclideanSpace ℝ {i // ¬p i}) :=
  ((EuclideanSpace.sumComplEquivProd ℝ p).prodCongr
    (EuclideanSpace.sumComplEquivProd ℝ p)).trans (ContinuousLinearEquiv.prodProdProdComm ℝ _ _ _ _)

variable {p}

theorem weightModelSplit_apply (z : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    weightModelSplit p z =
      (((EuclideanSpace.sumComplEquivProd ℝ p z.1).1,
          (EuclideanSpace.sumComplEquivProd ℝ p z.2).1),
        ((EuclideanSpace.sumComplEquivProd ℝ p z.1).2,
          (EuclideanSpace.sumComplEquivProd ℝ p z.2).2)) :=
  (rfl)

@[simp]
theorem weightModelSplit_apply_fst_fst (z : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)
    (i : {i // p i}) : (weightModelSplit p z).1.1 i = z.1 i := by
  simp [weightModelSplit_apply]

@[simp]
theorem weightModelSplit_apply_fst_snd (z : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)
    (i : {i // p i}) : (weightModelSplit p z).1.2 i = z.2 i := by
  simp [weightModelSplit_apply]

@[simp]
theorem weightModelSplit_apply_snd_fst (z : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)
    (i : {i // ¬p i}) : (weightModelSplit p z).2.1 i = z.1 i := by
  simp [weightModelSplit_apply]

@[simp]
theorem weightModelSplit_apply_snd_snd (z : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)
    (i : {i // ¬p i}) : (weightModelSplit p z).2.2 i = z.2 i := by
  simp [weightModelSplit_apply]

@[simp]
theorem weightModelSplit_symm_apply_fst
    (w : (EuclideanSpace ℝ {i // p i} × EuclideanSpace ℝ {i // p i}) ×
      (EuclideanSpace ℝ {i // ¬p i} × EuclideanSpace ℝ {i // ¬p i})) (i : ι) :
    ((weightModelSplit p).symm w).1 i = if h : p i then w.1.1 ⟨i, h⟩ else w.2.1 ⟨i, h⟩ := by
  obtain ⟨z, rfl⟩ := (weightModelSplit p).surjective w
  by_cases h : p i <;> simp [h]

@[simp]
theorem weightModelSplit_symm_apply_snd
    (w : (EuclideanSpace ℝ {i // p i} × EuclideanSpace ℝ {i // p i}) ×
      (EuclideanSpace ℝ {i // ¬p i} × EuclideanSpace ℝ {i // ¬p i})) (i : ι) :
    ((weightModelSplit p).symm w).2 i = if h : p i then w.1.2 ⟨i, h⟩ else w.2.2 ⟨i, h⟩ := by
  obtain ⟨z, rfl⟩ := (weightModelSplit p).surjective w
  by_cases h : p i <;> simp [h]

/-- The squared norm `‖x‖² + ‖y‖²` of `(x, y) ∈ ℂ^ι` is the sum of the squared norms of the two
parts of `weightModelSplit p (x, y)`. -/
theorem norm_sq_add_norm_sq_eq_weightModelSplit (z : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 =
      (‖(weightModelSplit p z).1.1‖ ^ 2 + ‖(weightModelSplit p z).1.2‖ ^ 2) +
        (‖(weightModelSplit p z).2.1‖ ^ 2 + ‖(weightModelSplit p z).2.2‖ ^ 2) := by
  rw [weightModelSplit_apply,
    ← EuclideanSpace.norm_fst_sumComplEquivProd_sq_add_norm_snd_sq (p := p) z.1,
    ← EuclideanSpace.norm_fst_sumComplEquivProd_sq_add_norm_snd_sq (p := p) z.2]
  ring

/-- If the weights `αₖ` vanish at every index `k` outside `p`, the moment map of the weight model
on `ℂ^ι` is the moment map of the weight model on `ℂ^{k // p k}`, with the weights restricted,
composed with the restriction of coordinates `z ↦ (weightModelSplit p z).1`. -/
theorem weightMomentMap_eq_weightMomentMap_weightModelSplit_fst {𝔱 : Type*}
    [NormedAddCommGroup 𝔱] [NormedSpace ℝ 𝔱] {α : ι → StrongDual ℝ 𝔱} (hα : ∀ k, ¬p k → α k = 0)
    (z : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    weightMomentMap α z = weightMomentMap (fun k : {k // p k} ↦ α k) (weightModelSplit p z).1 := by
  ext ξ
  rw [weightMomentMap_apply, weightMomentMap_apply,
    ← Fintype.sum_subtype_add_sum_subtype p (fun k ↦ α k ξ * (z.1 k ^ 2 + z.2 k ^ 2)),
    Finset.sum_eq_zero (s := Finset.univ (α := {k // ¬p k})) fun k _ ↦ by simp [hα k k.property],
    add_zero]
  simp

end Split

end TauCeti

end
