/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.SymplecticGroup
public import SymplecticGeometry.LinearAlgebra.Symplectic.Basic
public import TauCeti.Analysis.Complex.Euclidean.Space
public import TauCeti.Geometry.Symplectic.Complex.CoordinateSpace
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

The main facts fixing the conventions are `stdForm_apply`
(`ω₀(z, w) = ∑ᵢ (xᵢ(z) yᵢ(w) - yᵢ(z) xᵢ(w))`), `stdComplexStructure_eq_toEuclideanLin_J`,
`stdForm_apply_eq_inner` (`ω₀(z, w) = ⟪J₀ z, w⟫`), `stdForm_toBilinForm`
(`ω₀ = -Matrix.toBilin' (Matrix.J ι ℝ)` in coordinates), and `stdForm_compatible`.
Finally, `isSymplectomorphism_sumEquivProd` and `stdComplexStructure_transport_sumEquivProd`
compare the model with Tau Ceti's product model `TauCeti.stdSymplecticForm` and
`TauCeti.AlmostComplexStructure.product` on `EuclideanSpace ℝ ι × EuclideanSpace ℝ ι`.

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

/-- The inner product of the standard model in coordinates. -/
theorem inner_eq_sum (z w : StdSpace ι) :
    inner ℝ z w = ∑ i, (z.x i * w.x i + z.y i * w.y i) := by
  simp [PiLp.inner_apply, Fintype.sum_sum_type, Finset.sum_add_distrib, mul_comm]

end StdSpace

open StdSpace

variable [Fintype ι]

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

/-- `J₀` is the linear map of the matrix `Matrix.J ι ℝ = !![0, -1; 1, 0]`. -/
theorem stdComplexStructure_eq_toEuclideanLin_J [DecidableEq ι] :
    (stdComplexStructure ι).toLinearMap = Matrix.toEuclideanLin (Matrix.J ι ℝ) := by
  refine LinearMap.ext fun z ↦
    StdSpace.ext ((stdComplexStructure_x z).trans ?_) ((stdComplexStructure_y z).trans ?_) <;>
    ext i <;>
    simp [Matrix.J, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.one_apply]

/-- `ω₀(z, w) = ⟪J₀ z, w⟫`. -/
theorem stdForm_apply_eq_inner (z w : StdSpace ι) :
    stdForm ι z w = inner ℝ (stdComplexStructure ι z) w := by
  rw [StdSpace.inner_eq_sum, stdForm_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [stdComplexStructure_x, stdComplexStructure_y, Pi.neg_apply]
  ring

/-- In coordinates, `ω₀(z, w) = -zᵀ J w` with `J = Matrix.J ι ℝ`. For `ι = Fin n` this says
that Tau Ceti's `TauCeti.stdSymplecticBilinForm ℝ n` is `-ω₀`. -/
theorem stdForm_toBilinForm [DecidableEq ι] :
    (stdForm ι).toBilinForm =
      -(Matrix.toBilin' (Matrix.J ι ℝ)).compl₁₂ (WithLp.linearEquiv 2 ℝ (ι ⊕ ι → ℝ)).toLinearMap
        (WithLp.linearEquiv 2 ℝ (ι ⊕ ι → ℝ)).toLinearMap := by
  ext z w
  rw [SymplecticForm.toBilinForm_apply]
  simp [Matrix.toBilin'_apply', Matrix.J, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
    Matrix.one_apply, Finset.sum_sub_distrib]
  ring

/-- `J₀` is compatible with `ω₀`. -/
theorem stdForm_compatible : (stdForm ι).Compatible (stdComplexStructure ι) :=
  stdComplexPiSymplecticForm_compatible.transport _

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
