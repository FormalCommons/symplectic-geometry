/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
public import TauCeti.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Geometry.Symplectic.Darboux.Basis
public import TauCeti.LinearAlgebra.SesquilinearForm.IsometryGroup
public import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Basic
import SymplecticGeometry.Analysis.InnerProductSpace.Adjoint
import SymplecticGeometry.Geometry.Symplectic.SymplecticTransport
import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Matrix
import TauCeti.LinearAlgebra.BilinearForm.Similitude
import TauCeti.LinearAlgebra.SesquilinearForm.Separating

/-!
# Affine symplectic maps, cylinders and the reflection of the standard model

This file collects the objects in terms of which the affine nonsqueezing theorem and the linear
symplectic width are stated.

* `SymplecticGeometry.affineSymplecticGroup ω`: the group `ASp(V, ω)` of affine automorphisms of
  a real symplectic vector space whose linear part is a symplectomorphism, as the preimage of
  Tau Ceti's `LinearMap.isometryGroup ω.toBilinForm` under `AffineEquiv.linearHom`. In the
  standard model these are the maps `z ↦ A z + z₀` with `A` a symplectic matrix
  (`SymplecticGeometry.mem_affineSymplecticGroup_stdForm_iff_matrix`).
* `SymplecticGeometry.stdCylinder i R`: the closed cylinder `Z(R) = {z | √(xᵢ² + yᵢ²) ≤ R}` over
  the disc of radius `R` in the `(xᵢ, yᵢ)`-plane, empty for `R < 0`.
* `SymplecticGeometry.stdConj ι`: the reflection `(x, y) ↦ (x, -y)`, complex conjugation in the
  coordinates of `TauCeti.complexToRealEuclidean ι`. It reverses the sign of `ω₀`, so the
  anti-symplectic linear equivalences (`Ψ^* ω₀ = -ω₀`) are exactly the compositions of
  symplectic ones with it. Their determinant is `(-1) ^ n`
  (`SymplecticGeometry.det_eq_neg_one_pow_of_forall_apply_eq_neg`): this is Tau Ceti's
  `LinearMap.BilinForm.det_eq_pow_of_isAlt_of_compl₁₂_self_eq_smul` for the multiplier `-1`.
* `TauCeti.SymplecticForm.IsSymplectomorphism.adjoint`: the adjoint of a linear symplectomorphism
  of `ω₀` is again one, which is the statement that the transpose of a symplectic matrix is
  symplectic. Likewise the transpose of an anti-symplectic linear equivalence is
  anti-symplectic (`SymplecticGeometry.forall_adjointEquiv_apply_eq_neg_of_forall_apply_eq_neg`).
* `SymplecticGeometry.image_adjointEquiv_symm_stdCylinder`: the image of a cylinder under the
  inverse transpose of a linear equivalence `σ` is `{z | ⟪σ e, z⟫² + ⟪σ f, z⟫² ≤ R²}`, for the
  coordinate vectors `e`, `f` of the cylinder's plane.

The conventions are those of McDuff–Salamon, Sections 2.1 and 2.4.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017]
-/

public section

namespace SymplecticGeometry

open TauCeti

/-! ### The affine symplectic group -/

section Affine

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (ω : SymplecticForm V)

/-- The affine symplectic group `ASp(V, ω)`: the affine automorphisms of `V` whose linear part
is a symplectomorphism of `ω`. -/
def affineSymplecticGroup : Subgroup (V ≃ᵃ[ℝ] V) :=
  (LinearMap.isometryGroup ω.toBilinForm).comap AffineEquiv.linearHom

theorem affineSymplecticGroup_def :
    affineSymplecticGroup ω =
      (LinearMap.isometryGroup ω.toBilinForm).comap AffineEquiv.linearHom :=
  (rfl)

variable {ω}

/-- An affine automorphism is affine symplectic if and only if its linear part is a
symplectomorphism. -/
@[simp]
theorem mem_affineSymplecticGroup_iff {f : V ≃ᵃ[ℝ] V} :
    f ∈ affineSymplecticGroup ω ↔ ω.IsSymplectomorphism ω f.linear := by
  rw [affineSymplecticGroup_def, Subgroup.mem_comap, LinearMap.mem_isometryGroup_iff,
    SymplecticForm.isSymplectomorphism_iff]
  rfl

/-- Translations are affine symplectic. -/
theorem _root_.AffineEquiv.constVAdd_mem_affineSymplecticGroup (v : V) :
    AffineEquiv.constVAdd ℝ V v ∈ affineSymplecticGroup ω := by
  simp

/-- A linear automorphism, as an affine one, is affine symplectic if and only if it is a
symplectomorphism. -/
theorem _root_.LinearEquiv.toAffineEquiv_mem_affineSymplecticGroup_iff (e : V ≃ₗ[ℝ] V) :
    e.toAffineEquiv ∈ affineSymplecticGroup ω ↔ ω.IsSymplectomorphism ω e :=
  mem_affineSymplecticGroup_iff

/-- An affine automorphism is affine symplectic if and only if it has the form `v ↦ e v + v₀`
for a linear symplectomorphism `e` and a vector `v₀`. -/
theorem mem_affineSymplecticGroup_iff_exists {f : V ≃ᵃ[ℝ] V} :
    f ∈ affineSymplecticGroup ω ↔
      ∃ e : V ≃ₗ[ℝ] V, ω.IsSymplectomorphism ω e ∧ ∃ v₀ : V, ⇑f = fun v ↦ e v + v₀ := by
  rw [mem_affineSymplecticGroup_iff]
  constructor
  · intro h
    exact ⟨f.linear, h, f 0, funext fun v ↦ congr_fun f.toAffineMap.decomp v⟩
  · rintro ⟨e, he, v₀, hf⟩
    have hlin : f.linear = e := LinearEquiv.ext fun v ↦ by
      simpa [hf] using f.toAffineMap.linear_apply_vsub v 0
    rwa [hlin]

end Affine

variable {ι : Type*}

/-- In the standard model, an affine automorphism is affine symplectic if and only if it has
the form `z ↦ A z + z₀` for a symplectic matrix `A` and a vector `z₀`. -/
theorem mem_affineSymplecticGroup_stdForm_iff_matrix [Fintype ι] [DecidableEq ι]
    {f : StdSpace ι ≃ᵃ[ℝ] StdSpace ι} :
    f ∈ affineSymplecticGroup (stdForm ι) ↔
      ∃ A ∈ Matrix.symplecticGroup ι ℝ, ∃ z₀ : StdSpace ι,
        ⇑f = fun z ↦ Matrix.toEuclideanLin A z + z₀ := by
  constructor
  · intro h
    obtain ⟨e, he, z₀, hf⟩ := mem_affineSymplecticGroup_iff_exists.1 h
    refine ⟨Matrix.toEuclideanLin.symm e.toLinearMap,
      (mem_symplecticGroup_iff_isSymplectomorphism e).2 he, z₀, ?_⟩
    simpa using hf
  · rintro ⟨A, hA, z₀, hf⟩
    rw [mem_affineSymplecticGroup_iff, SymplecticForm.isSymplectomorphism_iff]
    intro v w
    have hlin : ∀ v, f.linear v = Matrix.toEuclideanLin A v := fun v ↦ by
      simpa [hf] using f.toAffineMap.linear_apply_vsub v 0
    rw [hlin, hlin]
    exact mem_symplecticGroup_iff_forall_stdForm.1 hA v w

/-! ### Cylinders -/

/-- The closed cylinder `{z | √(xᵢ² + yᵢ²) ≤ R}` over the disc of radius `R` in the
`(xᵢ, yᵢ)`-plane of the standard model. It is empty for `R < 0`. -/
def stdCylinder (i : ι) (R : ℝ) : Set (StdSpace ι) :=
  {z | √(z.x i ^ 2 + z.y i ^ 2) ≤ R}

theorem stdCylinder_def (i : ι) (R : ℝ) :
    stdCylinder i R = {z : StdSpace ι | √(z.x i ^ 2 + z.y i ^ 2) ≤ R} :=
  (rfl)

theorem mem_stdCylinder_iff {i : ι} {R : ℝ} {z : StdSpace ι} :
    z ∈ stdCylinder i R ↔ √(z.x i ^ 2 + z.y i ^ 2) ≤ R :=
  Iff.rfl

/-- For `0 ≤ R`, a point lies in the cylinder of radius `R` if and only if
`xᵢ² + yᵢ² ≤ R²`. -/
theorem mem_stdCylinder_iff_of_nonneg {i : ι} {R : ℝ} (hR : 0 ≤ R) {z : StdSpace ι} :
    z ∈ stdCylinder i R ↔ z.x i ^ 2 + z.y i ^ 2 ≤ R ^ 2 := by
  rw [mem_stdCylinder_iff, Real.sqrt_le_left hR]

/-- The cylinder of a negative radius is empty. -/
theorem stdCylinder_eq_empty {i : ι} {R : ℝ} (hR : R < 0) : stdCylinder i R = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ h ↦ (Real.sqrt_nonneg _).not_gt (h.trans_lt hR)

/-- Cylinders grow with the radius. -/
theorem stdCylinder_mono (i : ι) : Monotone (stdCylinder (ι := ι) i) :=
  fun _ _ h _ hz ↦ le_trans hz h

variable [Fintype ι]

/-- The closed ball of radius `R` lies in the cylinder of radius `R`. -/
theorem closedBall_subset_stdCylinder (i : ι) (R : ℝ) :
    Metric.closedBall (0 : StdSpace ι) R ⊆ stdCylinder i R := by
  intro z hz
  rw [mem_closedBall_zero_iff] at hz
  rw [mem_stdCylinder_iff]
  calc √(z.x i ^ 2 + z.y i ^ 2) ≤ √(‖z‖ ^ 2) := Real.sqrt_le_sqrt (z.sq_x_add_sq_y_le_norm_sq i)
    _ = ‖z‖ := Real.sqrt_sq (norm_nonneg z)
    _ ≤ R := hz

/-- The image of the cylinder of radius `R ≥ 0` over the `(xᵢ, yᵢ)`-plane under the inverse of
the transpose of a linear equivalence `σ` is `{z | ⟪σ eᵢ, z⟫² + ⟪σ fᵢ, z⟫² ≤ R²}`, where `eᵢ` and
`fᵢ` are the unit vectors of the coordinates `xᵢ` and `yᵢ`. -/
theorem image_adjointEquiv_symm_stdCylinder [DecidableEq ι] (σ : StdSpace ι ≃ₗ[ℝ] StdSpace ι)
    (i : ι) {R : ℝ} (hR : 0 ≤ R) :
    (ContinuousLinearEquiv.adjointEquiv σ.toContinuousLinearEquiv).symm '' stdCylinder i R =
      {z | inner ℝ (σ (EuclideanSpace.single (Sum.inl i) 1)) z ^ 2 +
        inner ℝ (σ (EuclideanSpace.single (Sum.inr i) 1)) z ^ 2 ≤ R ^ 2} := by
  ext z
  rw [ContinuousLinearEquiv.image_symm_eq_preimage, Set.mem_preimage,
    mem_stdCylinder_iff_of_nonneg hR, StdSpace.x_apply, StdSpace.y_apply,
    ContinuousLinearEquiv.adjointEquiv_apply, ContinuousLinearMap.adjoint_apply_apply,
    ContinuousLinearMap.adjoint_apply_apply, ContinuousLinearEquiv.coe_coe]
  simp only [LinearEquiv.coe_toContinuousLinearEquiv', Set.mem_ofPred_eq]

/-! ### The reflection `(x, y) ↦ (x, -y)` -/

variable (ι) in
/-- The reflection `(x, y) ↦ (x, -y)` of the standard model, a linear isometry. Under
`TauCeti.complexToRealEuclidean ι` it is complex conjugation. -/
noncomputable def stdConj : StdSpace ι ≃ₗᵢ[ℝ] StdSpace ι :=
  LinearIsometryEquiv.piLpCongrRight 2
    (Sum.elim (fun _ ↦ LinearIsometryEquiv.refl ℝ ℝ) fun _ ↦ LinearIsometryEquiv.neg ℝ)

theorem stdConj_def :
    stdConj ι = LinearIsometryEquiv.piLpCongrRight 2
      (Sum.elim (fun _ ↦ LinearIsometryEquiv.refl ℝ ℝ) fun _ ↦ LinearIsometryEquiv.neg ℝ) :=
  (rfl)

@[simp]
theorem stdConj_apply_inl (z : StdSpace ι) (i : ι) : stdConj ι z (Sum.inl i) = z (Sum.inl i) := by
  simp [stdConj_def]

@[simp]
theorem stdConj_apply_inr (z : StdSpace ι) (i : ι) :
    stdConj ι z (Sum.inr i) = -z (Sum.inr i) := by
  simp [stdConj_def]

@[simp]
theorem stdConj_x (z : StdSpace ι) : (stdConj ι z).x = z.x := by
  ext i
  simp

@[simp]
theorem stdConj_y (z : StdSpace ι) : (stdConj ι z).y = -z.y := by
  ext i
  simp

/-- The reflection is an involution. -/
@[simp]
theorem stdConj_stdConj (z : StdSpace ι) : stdConj ι (stdConj ι z) = z := by
  ext <;> simp

@[simp]
theorem stdConj_symm : (stdConj ι).symm = stdConj ι := by
  ext z : 1
  rw [LinearIsometryEquiv.symm_apply_eq, stdConj_stdConj]

/-- Under `TauCeti.complexToRealEuclidean ι`, `stdConj ι` is complex conjugation. -/
theorem stdConj_complexToRealEuclidean (u : ι → ℂ) :
    stdConj ι (complexToRealEuclidean ι u) = complexToRealEuclidean ι (star u) := by
  ext <;> simp

/-- The reflection reverses the sign of `ω₀`. -/
theorem stdForm_stdConj (z w : StdSpace ι) :
    stdForm ι (stdConj ι z) (stdConj ι w) = -stdForm ι z w := by
  simp only [stdForm_apply, stdConj_x, stdConj_y, Pi.neg_apply, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun _ _ ↦ by ring

/-- The reflection maps each closed ball about `0` onto itself. -/
theorem stdConj_image_closedBall (r : ℝ) :
    stdConj ι '' Metric.closedBall 0 r = Metric.closedBall 0 r := by
  rw [LinearIsometryEquiv.image_closedBall, map_zero]

/-- The reflection maps each cylinder onto itself. -/
theorem stdConj_image_stdCylinder (i : ι) (R : ℝ) :
    stdConj ι '' stdCylinder i R = stdCylinder i R := by
  rw [LinearIsometryEquiv.image_eq_preimage_symm, stdConj_symm]
  ext z
  simp only [Set.mem_preimage, mem_stdCylinder_iff, stdConj_x, stdConj_y, Pi.neg_apply, neg_sq]

/-- The determinant of the reflection `(x, y) ↦ (x, -y)` is `(-1) ^ n`. -/
theorem det_stdConj :
    LinearMap.det ((stdConj ι).toLinearEquiv : StdSpace ι →ₗ[ℝ] StdSpace ι) =
      (-1) ^ Fintype.card ι := by
  classical
  have h : ((stdConj ι).toLinearEquiv : StdSpace ι →ₗ[ℝ] StdSpace ι) =
      Matrix.toEuclideanLin (Matrix.diagonal (Sum.elim (fun _ ↦ 1) fun _ ↦ -1)) := by
    refine LinearMap.ext fun z ↦ PiLp.ext fun j ↦ ?_
    rcases j with j | j <;> simp [Matrix.mulVec_diagonal]
  rw [h, Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.det_toLin, Matrix.det_diagonal,
    Fintype.prod_sum_type]
  simp

/-! ### Anti-symplectic linear equivalences -/

variable {Ψ : StdSpace ι ≃ₗ[ℝ] StdSpace ι}

/-- An anti-symplectic linear equivalence followed by the reflection is symplectic. -/
theorem isSymplectomorphism_trans_stdConj_of_forall_apply_eq_neg
    (hΨ : ∀ z w, stdForm ι (Ψ z) (Ψ w) = -stdForm ι z w) :
    (stdForm ι).IsSymplectomorphism (stdForm ι) (Ψ.trans (stdConj ι).toLinearEquiv) := by
  rw [SymplecticForm.isSymplectomorphism_iff]
  intro z w
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply]
  exact (stdForm_stdConj _ _).trans (by rw [hΨ, neg_neg])

/-- The reflection followed by an anti-symplectic linear equivalence is symplectic. -/
theorem isSymplectomorphism_stdConj_trans_of_forall_apply_eq_neg
    (hΨ : ∀ z w, stdForm ι (Ψ z) (Ψ w) = -stdForm ι z w) :
    (stdForm ι).IsSymplectomorphism (stdForm ι) ((stdConj ι).toLinearEquiv.trans Ψ) := by
  rw [SymplecticForm.isSymplectomorphism_iff]
  intro z w
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply]
  exact (hΨ _ _).trans (by rw [LinearIsometryEquiv.coe_toLinearEquiv, stdForm_stdConj, neg_neg])

/-- An anti-symplectic linear equivalence of the standard model has determinant `(-1) ^ n`. -/
theorem det_eq_neg_one_pow_of_forall_apply_eq_neg
    (hΨ : ∀ z w, stdForm ι (Ψ z) (Ψ w) = -stdForm ι z w) :
    LinearMap.det (Ψ : StdSpace ι →ₗ[ℝ] StdSpace ι) = (-1) ^ Fintype.card ι := by
  have : (stdForm ι).toBilinForm.IsPerfPair :=
    .of_injective (stdForm ι).nondegenerate.1.injective (stdForm ι).nondegenerate.flip.1.injective
  rw [LinearMap.BilinForm.det_eq_pow_of_isAlt_of_compl₁₂_self_eq_smul _ (stdForm ι).isAlt
    (c := -1) (LinearMap.ext₂ fun z w ↦ by simpa using hΨ z w), finrank_stdSpace,
    Nat.mul_div_cancel_left _ two_pos]

end SymplecticGeometry

namespace TauCeti.SymplecticForm.IsSymplectomorphism

open SymplecticGeometry

variable {ι : Type*} [Fintype ι]

/-- The adjoint of a linear symplectomorphism of the standard model is a symplectomorphism:
the transpose of a symplectic matrix is symplectic. -/
theorem adjoint {e : StdSpace ι ≃ₗ[ℝ] StdSpace ι}
    (he : (stdForm ι).IsSymplectomorphism (stdForm ι) e) :
    (stdForm ι).IsSymplectomorphism (stdForm ι)
      (ContinuousLinearEquiv.adjointEquiv e.toContinuousLinearEquiv).toLinearEquiv := by
  classical
  set A := Matrix.toEuclideanLin.symm e.toLinearMap
  have hA : A.transpose ∈ Matrix.symplecticGroup ι ℝ :=
    SymplecticGroup.transpose_mem ((mem_symplecticGroup_iff_isSymplectomorphism e).2 he)
  have hadj : ∀ v, ContinuousLinearEquiv.adjointEquiv e.toContinuousLinearEquiv v =
      Matrix.toEuclideanLin A.transpose v := by
    intro v
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_eq_toCLM_adjoint,
      ContinuousLinearEquiv.adjointEquiv_apply]
    simp only [A, LinearEquiv.apply_symm_apply]
    rfl
  rw [SymplecticForm.isSymplectomorphism_iff]
  intro v w
  simp only [ContinuousLinearEquiv.coe_toLinearEquiv, hadj]
  exact mem_symplecticGroup_iff_forall_stdForm.1 hA v w

end TauCeti.SymplecticForm.IsSymplectomorphism

namespace SymplecticGeometry

open TauCeti

variable {ι : Type*} [Fintype ι]

/-- The transpose of an anti-symplectic linear equivalence of the standard model is
anti-symplectic: if `Ψ^* ω₀ = -ω₀`, then `(Ψᵀ)^* ω₀ = -ω₀`. -/
theorem forall_adjointEquiv_apply_eq_neg_of_forall_apply_eq_neg
    {Ψ : StdSpace ι ≃ₗ[ℝ] StdSpace ι} (hΨ : ∀ z w, stdForm ι (Ψ z) (Ψ w) = -stdForm ι z w)
    (z w : StdSpace ι) :
    stdForm ι (ContinuousLinearEquiv.adjointEquiv Ψ.toContinuousLinearEquiv z)
      (ContinuousLinearEquiv.adjointEquiv Ψ.toContinuousLinearEquiv w) = -stdForm ι z w := by
  set e := (stdConj ι).toLinearEquiv.trans Ψ
  -- the adjoint of `Ψ ∘ stdConj` is `stdConj ∘ Ψ†`
  have hadj : ∀ v, ContinuousLinearEquiv.adjointEquiv e.toContinuousLinearEquiv v =
      stdConj ι (ContinuousLinearEquiv.adjointEquiv Ψ.toContinuousLinearEquiv v) := by
    intro v
    refine ext_inner_right ℝ fun u ↦ ?_
    calc inner ℝ (ContinuousLinearEquiv.adjointEquiv e.toContinuousLinearEquiv v) u
        = inner ℝ (ContinuousLinearEquiv.adjointEquiv Ψ.toContinuousLinearEquiv v)
            (stdConj ι u) := by
          simp [e, ContinuousLinearMap.adjoint_inner_left]
      _ = _ := by rw [← (stdConj ι).inner_map_map, stdConj_stdConj]
  have he : ∀ z w, stdForm ι (ContinuousLinearEquiv.adjointEquiv e.toContinuousLinearEquiv z)
      (ContinuousLinearEquiv.adjointEquiv e.toContinuousLinearEquiv w) = stdForm ι z w :=
    SymplecticForm.isSymplectomorphism_iff.1
      (isSymplectomorphism_stdConj_trans_of_forall_apply_eq_neg hΨ).adjoint
  have h := he z w
  rw [hadj, hadj, stdForm_stdConj] at h
  linarith

end SymplecticGeometry

end
