/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.SymplecticGroup
public import TauCeti.Analysis.Complex.Euclidean.Space
public import TauCeti.Geometry.Symplectic.Complex.CoordinateSpace
public import TauCeti.Geometry.Symplectic.CompatibleMetric
public import TauCeti.Geometry.Symplectic.Prod.Basic
public import TauCeti.Geometry.Symplectic.StandardCompatible
public import TauCeti.Geometry.Symplectic.SymplecticTransport
public import TauCeti.Geometry.Symplectic.Transport

/-!
# The standard model `(ℝ²ⁿ, ω₀, J₀)`

This file sets up the model space of linear symplectic geometry and its two standard
structures.

* `SymplecticGeometry.StdSpace ι` is `EuclideanSpace ℝ (ι ⊕ ι)`, with coordinates
  `z.x = z ∘ Sum.inl` and `z.y = z ∘ Sum.inr`, so `z = (x, y)`. Its norm is the Euclidean norm
  of all `2n` coordinates, and Mathlib's `Matrix.J ι ℝ` and `Matrix.symplecticGroup ι ℝ` act on
  it through `Matrix.toEuclideanLin` without reindexing.
* `SymplecticGeometry.stdForm ι` is `ω₀ = ∑ᵢ dxᵢ ∧ dyᵢ`, defined by transporting Tau Ceti's
  `TauCeti.stdComplexPiSymplecticForm ι` along `TauCeti.complexToRealEuclidean ι`, which sends
  `u : ι → ℂ` to its real parts (`x`) and imaginary parts (`y`).
* `SymplecticGeometry.stdComplexStructure ι` is `J₀`, the transport of multiplication by `I`,
  so that `x (J₀ z) = -y z` and `y (J₀ z) = x z`; it is the map of `Matrix.J ι ℝ`.
* `SymplecticGeometry.StdSpace.complexEuclideanEquiv ι` identifies `EuclideanSpace ℂ ι` with
  `StdSpace ι` by real and imaginary parts, so that subspaces of `ℂⁿ` can be compared with
  subspaces of the model; it carries multiplication by `I` to `J₀`
  (`stdComplexStructure_complexEuclideanEquiv`).
* `SymplecticGeometry.StdSpace.swap ι` is the coordinate swap `(x, y) ↦ (y, x)`.

The main facts fixing the conventions are `stdForm_apply`
(`ω₀(z, w) = ∑ᵢ (xᵢ(z) yᵢ(w) - yᵢ(z) xᵢ(w))`), `stdComplexStructure_eq_toEuclideanLin_J`,
`stdForm_apply_eq_inner` (`ω₀(z, w) = ⟪J₀ z, w⟫`), `stdForm_toBilinForm`
(`ω₀ = -Matrix.toBilin' (Matrix.J ι ℝ)` in coordinates), and `stdForm_compatible`, with the
Cauchy–Schwarz inequality `abs_stdForm_apply_le` (`|ω₀(z, w)| ≤ ‖z‖ ‖w‖`).
Finally, `isSymplectomorphism_sumEquivProd` and `stdComplexStructure_transport_sumEquivProd`
compare the model with Tau Ceti's product model `TauCeti.stdSymplecticForm` and
`TauCeti.AlmostComplexStructure.product` on `EuclideanSpace ℝ ι × EuclideanSpace ℝ ι`, and
`isSymplectomorphism_piLpCongrLeft_sumCongr` says that relabelling the coordinate pairs along
`σ : ι ≃ κ` is symplectic, with its coordinates given by `x_piLpCongrLeft_sumCongr` and
`y_piLpCongrLeft_sumCongr`. The splitting `SymplecticGeometry.StdSpace.sumEquiv ι κ` of
`StdSpace (ι ⊕ κ)` into `StdSpace ι × StdSpace κ` carries `ω₀` to the direct sum of the two
standard forms (`isSymplectomorphism_sumEquiv`).

The sign conventions are those of McDuff–Salamon, Section 2.1.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017]
-/

public section

namespace SymplecticGeometry

open TauCeti

/-- The standard model `ℝ²ⁿ = ℝⁿ ⊕ ℝⁿ` of linear symplectic geometry, as the Euclidean space
on `ι ⊕ ι`: the coordinates at `Sum.inl i` are the `xᵢ`, those at `Sum.inr i` the `yᵢ`. -/
abbrev StdSpace (ι : Type*) := EuclideanSpace ℝ (ι ⊕ ι)

variable {ι : Type*}

namespace StdSpace

variable (ι) in
/-- The identification of `StdSpace ι` with pairs `(x, y)` of real coordinate vectors. -/
noncomputable def equivProd : StdSpace ι ≃ₗ[ℝ] (ι → ℝ) × (ι → ℝ) :=
  (EuclideanSpace.equiv (ι ⊕ ι) ℝ).toLinearEquiv.trans
    (ContinuousLinearEquiv.sumPiEquivProdPi ℝ ι ι fun _ ↦ ℝ).toLinearEquiv

/-- The `x`-coordinates `(z (Sum.inl i))ᵢ` of a point of the standard model. -/
noncomputable def x : StdSpace ι →ₗ[ℝ] (ι → ℝ) :=
  LinearMap.fst ℝ _ _ ∘ₗ (equivProd ι).toLinearMap

/-- The `y`-coordinates `(z (Sum.inr i))ᵢ` of a point of the standard model. -/
noncomputable def y : StdSpace ι →ₗ[ℝ] (ι → ℝ) :=
  LinearMap.snd ℝ _ _ ∘ₗ (equivProd ι).toLinearMap

@[simp]
theorem x_apply (z : StdSpace ι) (i : ι) : z.x i = z (Sum.inl i) := (rfl)

@[simp]
theorem y_apply (z : StdSpace ι) (i : ι) : z.y i = z (Sum.inr i) := (rfl)

/-- A point of the standard model is determined by its `x`- and `y`-coordinates. -/
@[ext]
theorem ext {z w : StdSpace ι} (hx : z.x = w.x) (hy : z.y = w.y) : z = w := by
  ext (i | i)
  · exact congr_fun hx i
  · exact congr_fun hy i

@[simp]
theorem equivProd_apply (z : StdSpace ι) : equivProd ι z = (z.x, z.y) := (rfl)

@[simp]
theorem x_equivProd_symm (a b : ι → ℝ) : ((equivProd ι).symm (a, b)).x = a := (rfl)

@[simp]
theorem y_equivProd_symm (a b : ι → ℝ) : ((equivProd ι).symm (a, b)).y = b := (rfl)

@[simp]
theorem equivProd_symm_apply_inl (a b : ι → ℝ) (i : ι) :
    (equivProd ι).symm (a, b) (Sum.inl i) = a i := (rfl)

@[simp]
theorem equivProd_symm_apply_inr (a b : ι → ℝ) (i : ι) :
    (equivProd ι).symm (a, b) (Sum.inr i) = b i := (rfl)

variable (ι) in
/-- The coordinate swap `(x, y) ↦ (y, x)` of `StdSpace ι`. -/
noncomputable def swap : StdSpace ι ≃ₗ[ℝ] StdSpace ι :=
  (equivProd ι).trans ((LinearEquiv.prodComm ℝ (ι → ℝ) (ι → ℝ)).trans (equivProd ι).symm)

variable (ι) in
theorem swap_def :
    swap ι =
      (equivProd ι).trans ((LinearEquiv.prodComm ℝ (ι → ℝ) (ι → ℝ)).trans (equivProd ι).symm) :=
  (rfl)

@[simp]
theorem x_swap (z : StdSpace ι) : (swap ι z).x = z.y := (rfl)

@[simp]
theorem y_swap (z : StdSpace ι) : (swap ι z).y = z.x := (rfl)

@[simp]
theorem swap_swap (z : StdSpace ι) : swap ι (swap ι z) = z :=
  StdSpace.ext (by simp) (by simp)

@[simp]
theorem symm_swap : (swap ι).symm = swap ι :=
  LinearEquiv.ext fun z ↦ (swap ι).symm_apply_eq.2 (swap_swap z).symm

/-- The coordinate swap sends the vertical subspace `{x = 0}` to the horizontal one `{y = 0}`. -/
@[simp]
theorem map_swap_ker_x :
    (LinearMap.ker x).map (swap ι : StdSpace ι →ₗ[ℝ] StdSpace ι) = LinearMap.ker (y (ι := ι)) := by
  ext z
  simp [Submodule.mem_map_equiv]

/-- The coordinate swap sends the horizontal subspace `{y = 0}` to the vertical one `{x = 0}`. -/
@[simp]
theorem map_swap_ker_y :
    (LinearMap.ker y).map (swap ι : StdSpace ι →ₗ[ℝ] StdSpace ι) = LinearMap.ker (x (ι := ι)) := by
  rw [← symm_swap, Submodule.map_symm_eq_iff, map_swap_ker_x]

variable [Fintype ι]

/-- The `x`-coordinates of `complexToRealEuclidean ι u` are the real parts of `u`. -/
@[simp]
theorem x_complexToRealEuclidean (u : ι → ℂ) :
    x (complexToRealEuclidean ι u) = fun i ↦ (u i).re := by
  ext i
  simp [complexToRealEuclidean_apply]

/-- The `y`-coordinates of `complexToRealEuclidean ι u` are the imaginary parts of `u`. -/
@[simp]
theorem y_complexToRealEuclidean (u : ι → ℂ) :
    y (complexToRealEuclidean ι u) = fun i ↦ (u i).im := by
  ext i
  simp [complexToRealEuclidean_apply]

variable (ι) in
/-- The real-linear identification of `ℂⁿ = EuclideanSpace ℂ ι` with the standard model
`ℝ²ⁿ = StdSpace ι`, sending `v` to `(Re v, Im v)`. It is how subspaces of `ℂⁿ` (as in Tau Ceti's
totally real geometry) are compared with subspaces of `StdSpace ι`. -/
noncomputable def complexEuclideanEquiv : EuclideanSpace ℂ ι ≃L[ℝ] StdSpace ι :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι ↦ ℂ)).trans (complexToRealEuclidean ι)

theorem complexEuclideanEquiv_def :
    complexEuclideanEquiv ι =
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι ↦ ℂ)).trans (complexToRealEuclidean ι) :=
  (rfl)

/-- The `x`-coordinates of `complexEuclideanEquiv ι v` are the real parts of `v`. -/
@[simp]
theorem x_complexEuclideanEquiv (v : EuclideanSpace ℂ ι) :
    (complexEuclideanEquiv ι v).x = fun i ↦ (v i).re := by
  simp [complexEuclideanEquiv_def]

/-- The `y`-coordinates of `complexEuclideanEquiv ι v` are the imaginary parts of `v`. -/
@[simp]
theorem y_complexEuclideanEquiv (v : EuclideanSpace ℂ ι) :
    (complexEuclideanEquiv ι v).y = fun i ↦ (v i).im := by
  simp [complexEuclideanEquiv_def]

/-- The inner product of the standard model in coordinates. -/
theorem inner_eq_sum (z w : StdSpace ι) :
    inner ℝ z w = ∑ i, (z.x i * w.x i + z.y i * w.y i) := by
  simp [PiLp.inner_apply, Fintype.sum_sum_type, Finset.sum_add_distrib, mul_comm]

/-- The squared norm of the standard model in coordinates: `‖z‖² = ∑ᵢ (xᵢ² + yᵢ²)`. -/
theorem norm_sq_eq_sum (z : StdSpace ι) : ‖z‖ ^ 2 = ∑ i, (z.x i ^ 2 + z.y i ^ 2) := by
  rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_sum_type, Finset.sum_add_distrib]
  rfl

/-- The squares of the `i`-th coordinates `xᵢ` and `yᵢ` of `z` add up to at most `‖z‖²`. -/
theorem sq_x_add_sq_y_le_norm_sq (z : StdSpace ι) (i : ι) :
    z.x i ^ 2 + z.y i ^ 2 ≤ ‖z‖ ^ 2 := by
  classical
  rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_sum_type, x_apply, y_apply]
  gcongr
  · exact Finset.single_le_sum (f := fun j ↦ z (Sum.inl j) ^ 2) (fun _ _ ↦ sq_nonneg _)
      (Finset.mem_univ i)
  · exact Finset.single_le_sum (f := fun j ↦ z (Sum.inr j) ^ 2) (fun _ _ ↦ sq_nonneg _)
      (Finset.mem_univ i)

end StdSpace

open StdSpace

variable [Fintype ι]

/-- The standard model `StdSpace ι` has real dimension `2 * Fintype.card ι`. -/
theorem finrank_stdSpace : Module.finrank ℝ (StdSpace ι) = 2 * Fintype.card ι := by
  rw [finrank_euclideanSpace, Fintype.card_sum, two_mul]

variable (ι) in
/-- The standard symplectic form `ω₀ = ∑ᵢ dxᵢ ∧ dyᵢ` on `StdSpace ι`: the transport of
`TauCeti.stdComplexPiSymplecticForm ι` along `complexToRealEuclidean ι`. -/
noncomputable def stdForm : SymplecticForm (StdSpace ι) :=
  (stdComplexPiSymplecticForm ι).transport (complexToRealEuclidean ι).toLinearEquiv

theorem stdForm_def :
    stdForm ι =
      (stdComplexPiSymplecticForm ι).transport (complexToRealEuclidean ι).toLinearEquiv :=
  (rfl)

/-- `ω₀(z, w) = ∑ᵢ (xᵢ(z) yᵢ(w) - yᵢ(z) xᵢ(w))`. -/
@[simp]
theorem stdForm_apply (z w : StdSpace ι) :
    stdForm ι z w = ∑ i, (z.x i * w.y i - z.y i * w.x i) := by
  simp [stdForm_def, stdComplexSymplecticForm_apply]

variable (ι) in
/-- The standard complex structure `J₀` on `StdSpace ι`: the transport of multiplication by `I`
on `ι → ℂ` along `complexToRealEuclidean ι`, so `J₀ (x, y) = (-y, x)`. -/
noncomputable def stdComplexStructure : AlmostComplexStructure (StdSpace ι) :=
  (AlmostComplexStructure.ofComplexModule (ι → ℂ)).transport
    (complexToRealEuclidean ι).toLinearEquiv

theorem stdComplexStructure_def :
    stdComplexStructure ι =
      (AlmostComplexStructure.ofComplexModule (ι → ℂ)).transport
        (complexToRealEuclidean ι).toLinearEquiv :=
  (rfl)

/-- `x (J₀ z) = -y z`. -/
@[simp]
theorem stdComplexStructure_x (z : StdSpace ι) : (stdComplexStructure ι z).x = -z.y := by
  ext i
  simp [stdComplexStructure_def, AlmostComplexStructure.ofComplexModule_apply]

/-- `y (J₀ z) = x z`. -/
@[simp]
theorem stdComplexStructure_y (z : StdSpace ι) : (stdComplexStructure ι z).y = z.x := by
  ext i
  simp [stdComplexStructure_def, AlmostComplexStructure.ofComplexModule_apply]

/-- The `xᵢ`-coordinate of `J₀ z` is `-yᵢ(z)`. -/
@[simp]
theorem stdComplexStructure_apply_inl (z : StdSpace ι) (i : ι) :
    stdComplexStructure ι z (Sum.inl i) = -z (Sum.inr i) := by
  rw [← x_apply, stdComplexStructure_x]
  rfl

/-- The `yᵢ`-coordinate of `J₀ z` is `xᵢ(z)`. -/
@[simp]
theorem stdComplexStructure_apply_inr (z : StdSpace ι) (i : ι) :
    stdComplexStructure ι z (Sum.inr i) = z (Sum.inl i) := by
  rw [← y_apply, stdComplexStructure_y]
  rfl

/-- `complexEuclideanEquiv ι` carries multiplication by `I` on `ℂⁿ` to `J₀`. -/
@[simp]
theorem stdComplexStructure_complexEuclideanEquiv (v : EuclideanSpace ℂ ι) :
    stdComplexStructure ι (complexEuclideanEquiv ι v) = complexEuclideanEquiv ι (Complex.I • v) :=
  StdSpace.ext (by simp [Pi.neg_def]) (by simp)

/-- `J₀` is the linear map of the matrix `Matrix.J ι ℝ = !![0, -1; 1, 0]`. -/
theorem stdComplexStructure_eq_toEuclideanLin_J [DecidableEq ι] :
    (stdComplexStructure ι).toLinearMap = Matrix.toEuclideanLin (Matrix.J ι ℝ) := by
  refine LinearMap.ext fun z ↦
    StdSpace.ext ((stdComplexStructure_x z).trans ?_) ((stdComplexStructure_y z).trans ?_) <;>
    ext i <;>
    simp [Matrix.J, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.one_apply]

/-- The metric `ω₀(·, J₀ ·)` of the standard model is its inner product. -/
theorem stdForm_apply_stdComplexStructure (z w : StdSpace ι) :
    stdForm ι z (stdComplexStructure ι w) = inner ℝ z w := by
  rw [StdSpace.inner_eq_sum, stdForm_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [stdComplexStructure_x, stdComplexStructure_y, Pi.neg_apply]
  ring

/-- `ω₀(z, w) = ⟪J₀ z, w⟫`. -/
theorem stdForm_apply_eq_inner (z w : StdSpace ι) :
    stdForm ι z w = inner ℝ (stdComplexStructure ι z) w :=
  (SymplecticForm.inner_apply_left_eq_of_apply_apply_eq_inner
    stdForm_apply_stdComplexStructure z w).symm

/-- In coordinates, `ω₀(z, w) = -zᵀ J w` with `J = Matrix.J ι ℝ`. For `ι = Fin n` this says
that Tau Ceti's `TauCeti.stdSymplecticBilinForm ℝ n` is `-ω₀`. -/
theorem stdForm_toBilinForm [DecidableEq ι] :
    (stdForm ι).toBilinForm =
      -(Matrix.toBilin' (Matrix.J ι ℝ)).compl₁₂ (WithLp.linearEquiv 2 ℝ (ι ⊕ ι → ℝ)).toLinearMap
        (WithLp.linearEquiv 2 ℝ (ι ⊕ ι → ℝ)).toLinearMap := by
  ext z w
  simp [Matrix.toBilin'_apply', Matrix.J, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
    Matrix.one_apply, Finset.sum_sub_distrib]
  ring

/-- `J₀` is compatible with `ω₀`. -/
theorem stdForm_compatible : (stdForm ι).Compatible (stdComplexStructure ι) :=
  stdComplexPiSymplecticForm_compatible.transport _

/-- Cauchy–Schwarz for `ω₀`: `|ω₀(z, w)| ≤ ‖z‖ ‖w‖`. -/
theorem abs_stdForm_apply_le (z w : StdSpace ι) : |stdForm ι z w| ≤ ‖z‖ * ‖w‖ :=
  SymplecticForm.abs_apply_le_norm_mul_norm stdForm_apply_stdComplexStructure z w

/-! ### Relabelling the coordinate pairs -/

section Reindex

variable {κ : Type*} [Fintype κ]

/-- The reindexing `σ : ι ≃ κ` of the coordinate pairs `(xᵢ, yᵢ)`, which sends the coordinates
of index `i` to those of index `σ i`, is a symplectomorphism from `ω₀` on `StdSpace ι` to `ω₀`
on `StdSpace κ`. -/
theorem isSymplectomorphism_piLpCongrLeft_sumCongr (σ : ι ≃ κ) :
    (stdForm ι).IsSymplectomorphism (stdForm κ)
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (σ.sumCongr σ)).toLinearEquiv := by
  rw [SymplecticForm.isSymplectomorphism_iff]
  intro z w
  simp only [stdForm_apply, x_apply, y_apply, LinearIsometryEquiv.coe_toLinearEquiv,
    LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'_apply, Equiv.sumCongr_symm,
    Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr]
  exact Equiv.sum_comp σ.symm fun i ↦ z (Sum.inl i) * w (Sum.inr i) - z (Sum.inr i) * w (Sum.inl i)

namespace StdSpace

/-- The `x`-coordinates of `z` relabelled along `σ` are those of `z`, read through `σ.symm`. -/
@[simp]
theorem x_piLpCongrLeft_sumCongr (σ : ι ≃ κ) (z : StdSpace ι) :
    x (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (σ.sumCongr σ) z) = z.x ∘ σ.symm := by
  ext i
  simp [LinearIsometryEquiv.piLpCongrLeft_apply]

/-- The `y`-coordinates of `z` relabelled along `σ` are those of `z`, read through `σ.symm`. -/
@[simp]
theorem y_piLpCongrLeft_sumCongr (σ : ι ≃ κ) (z : StdSpace ι) :
    y (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (σ.sumCongr σ) z) = z.y ∘ σ.symm := by
  ext i
  simp [LinearIsometryEquiv.piLpCongrLeft_apply]

end StdSpace

end Reindex

/-! ### The direct sum of two models -/

section Sum

variable {κ : Type*} [Fintype κ]

namespace StdSpace

variable (ι κ) in
/-- The splitting `ℝ²⁽ⁿ⁺ᵐ⁾ ≅ ℝ²ⁿ × ℝ²ᵐ` of the standard model on `ι ⊕ κ`: the coordinate pairs
indexed by `ι` go to the first factor and those indexed by `κ` to the second. The coordinates are
regrouped by `Equiv.sumSumSumComm`, as in Tau Ceti's `Matrix.symplecticSum`. -/
noncomputable def sumEquiv : StdSpace (ι ⊕ κ) ≃L[ℝ] StdSpace ι × StdSpace κ :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
    (Equiv.sumSumSumComm ι κ ι κ)).toContinuousLinearEquiv.trans EuclideanSpace.sumEquivProd

variable (ι κ) in
theorem sumEquiv_def :
    sumEquiv ι κ =
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
        (Equiv.sumSumSumComm ι κ ι κ)).toContinuousLinearEquiv.trans EuclideanSpace.sumEquivProd :=
  (rfl)

@[simp]
theorem x_sumEquiv_fst (z : StdSpace (ι ⊕ κ)) : (sumEquiv ι κ z).1.x = fun i ↦ z.x (Sum.inl i) :=
  (rfl)

@[simp]
theorem y_sumEquiv_fst (z : StdSpace (ι ⊕ κ)) : (sumEquiv ι κ z).1.y = fun i ↦ z.y (Sum.inl i) :=
  (rfl)

@[simp]
theorem x_sumEquiv_snd (z : StdSpace (ι ⊕ κ)) : (sumEquiv ι κ z).2.x = fun k ↦ z.x (Sum.inr k) :=
  (rfl)

@[simp]
theorem y_sumEquiv_snd (z : StdSpace (ι ⊕ κ)) : (sumEquiv ι κ z).2.y = fun k ↦ z.y (Sum.inr k) :=
  (rfl)

@[simp]
theorem x_sumEquiv_symm (p : StdSpace ι × StdSpace κ) :
    ((sumEquiv ι κ).symm p).x = Sum.elim p.1.x p.2.x := by
  obtain ⟨z, rfl⟩ := (sumEquiv ι κ).surjective p
  ext (i | k) <;> simp

@[simp]
theorem y_sumEquiv_symm (p : StdSpace ι × StdSpace κ) :
    ((sumEquiv ι κ).symm p).y = Sum.elim p.1.y p.2.y := by
  obtain ⟨z, rfl⟩ := (sumEquiv ι κ).surjective p
  ext (i | k) <;> simp

end StdSpace

open StdSpace in
/-- The splitting `StdSpace.sumEquiv ι κ` is a symplectomorphism from `ω₀` on `StdSpace (ι ⊕ κ)`
to the direct sum `ω₀ ⊕ ω₀` on `StdSpace ι × StdSpace κ` (Tau Ceti's `SymplecticForm.prod`). -/
theorem isSymplectomorphism_sumEquiv :
    (stdForm (ι ⊕ κ)).IsSymplectomorphism ((stdForm ι).prod (stdForm κ))
      (sumEquiv ι κ).toLinearEquiv := by
  rw [SymplecticForm.isSymplectomorphism_iff]
  intro z w
  simp only [ContinuousLinearEquiv.coe_toLinearEquiv, SymplecticForm.prod_apply, stdForm_apply,
    x_sumEquiv_fst, y_sumEquiv_fst, x_sumEquiv_snd, y_sumEquiv_snd]
  rw [Fintype.sum_sum_type]

end Sum

/-! ### Comparison with the product model -/

/-- `EuclideanSpace.sumEquivProd` is a symplectomorphism from `(StdSpace ι, ω₀)` to Tau Ceti's
product model `TauCeti.stdSymplecticForm` on `EuclideanSpace ℝ ι × EuclideanSpace ℝ ι`. -/
theorem isSymplectomorphism_sumEquivProd :
    (stdForm ι).IsSymplectomorphism stdSymplecticForm
      (EuclideanSpace.sumEquivProd (𝕜 := ℝ) (ι := ι) (κ := ι)).toLinearEquiv := by
  rw [SymplecticForm.isSymplectomorphism_iff]
  intro z w
  simp [PiLp.inner_apply, ← Finset.sum_sub_distrib, mul_comm]

/-- `EuclideanSpace.sumEquivProd` carries `J₀` to Tau Ceti's product complex structure
`(x, y) ↦ (-y, x)`. -/
theorem stdComplexStructure_transport_sumEquivProd :
    (stdComplexStructure ι).transport
        (EuclideanSpace.sumEquivProd (𝕜 := ℝ) (ι := ι) (κ := ι)).toLinearEquiv =
      AlmostComplexStructure.product (EuclideanSpace ℝ ι) := by
  apply AlmostComplexStructure.toLinearMap_injective
  refine LinearMap.ext fun p ↦ Prod.ext ?_ ?_ <;> ext i <;> simp

end SymplecticGeometry

end
