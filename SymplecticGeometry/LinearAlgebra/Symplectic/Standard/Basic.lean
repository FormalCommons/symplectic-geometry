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
  (`stdComplexStructure_complexEuclideanEquiv`), as `complexToRealEuclidean ι` does
  (`stdComplexStructure_complexToRealEuclidean`).
* `SymplecticGeometry.StdSpace.swap ι` is the coordinate swap `(x, y) ↦ (y, x)`, which reverses
  the sign of `ω₀` (`stdForm_swap`).
* `SymplecticGeometry.StdSpace.finSumIsometry n` relabels the coordinates of `StdSpace (Fin n)`
  along `finSumFinEquiv`, a linear isometry onto `EuclideanSpace ℝ (Fin (n + n))`.

The main facts fixing the conventions are `stdForm_apply`
(`ω₀(z, w) = ∑ᵢ (xᵢ(z) yᵢ(w) - yᵢ(z) xᵢ(w))`), `stdComplexStructure_eq_toEuclideanLin_J`,
`stdForm_apply_eq_inner` (`ω₀(z, w) = ⟪J₀ z, w⟫`), `stdForm_toBilinForm`
(`ω₀ = -Matrix.toBilin' (Matrix.J ι ℝ)` in coordinates), and `stdForm_compatible`, with the
Cauchy–Schwarz inequality `abs_stdForm_apply_le` (`|ω₀(z, w)| ≤ ‖z‖ ‖w‖`).
Finally, `isSymplectomorphism_sumEquivProd` and `stdComplexStructure_transport_sumEquivProd`
compare the model with Tau Ceti's product model `TauCeti.stdSymplecticForm` and
`TauCeti.AlmostComplexStructure.product` on `EuclideanSpace ℝ ι × EuclideanSpace ℝ ι`
(complex linearity: `isComplexLinearMap_sumEquivProd`), and
`isSymplectomorphism_piLpCongrLeft_sumCongr` says that relabelling the coordinate pairs along
`σ : ι ≃ κ` is symplectic, with its coordinates given by `x_piLpCongrLeft_sumCongr` and
`y_piLpCongrLeft_sumCongr`, and that it commutes with `J₀`
(`stdComplexStructure_piLpCongrLeft_sumCongr`, `isComplexLinearMap_piLpCongrLeft_sumCongr`).
The splitting `SymplecticGeometry.StdSpace.sumEquiv ι κ` of
`StdSpace (ι ⊕ κ)` into `StdSpace ι × StdSpace κ` carries `ω₀` to the direct sum of the two
standard forms (`isSymplectomorphism_sumEquiv`). Through it, `StdSpace.stdInl k m` includes
`StdSpace (Fin k)` in `StdSpace (Fin (k + m))` as the first `k` coordinate pairs, preserving
`ω₀` (`stdForm_stdInl`), with range `range_stdInl`; and `StdSpace.ofX ι` includes `ι → ℝ` as
the `x`-coordinates, onto the isotropic subspace `{y = 0}` (`range_ofX`, `stdForm_ofX`).
Composed, `stdInl k m ∘ ofX (Fin k)` is onto the isotropic subspace
`{y = 0, and xⱼ = 0 for j ≥ k}` (`range_stdInl_ofX`).
Likewise `StdSpace.stdInr k m` includes `StdSpace (Fin m)` as the last `m` pairs, `ω₀`-orthogonal
to the first `k` (`stdForm_stdInl_add_stdInr`). Together with `ofX`, they parametrize the
coisotropic subspace `{yⱼ = 0 for j < k}` (`range_stdInl_ofX_add_stdInr`), whose `ω₀`-orthogonal
is the span of the first `k` vectors `∂/∂xⱼ`
(`forall_stdForm_eq_zero_iff_y_eq_zero_and_x_eq_zero`).

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

variable (ι) in
theorem equivProd_def :
    equivProd ι = (EuclideanSpace.equiv (ι ⊕ ι) ℝ).toLinearEquiv.trans
      (ContinuousLinearEquiv.sumPiEquivProdPi ℝ ι ι fun _ ↦ ℝ).toLinearEquiv :=
  (rfl)

/-- The `x`-coordinates `(z (Sum.inl i))ᵢ` of a point of the standard model. -/
noncomputable def x : StdSpace ι →ₗ[ℝ] (ι → ℝ) :=
  LinearMap.fst ℝ _ _ ∘ₗ (equivProd ι).toLinearMap

theorem x_def : x = LinearMap.fst ℝ (ι → ℝ) (ι → ℝ) ∘ₗ (equivProd ι).toLinearMap := (rfl)

/-- The `y`-coordinates `(z (Sum.inr i))ᵢ` of a point of the standard model. -/
noncomputable def y : StdSpace ι →ₗ[ℝ] (ι → ℝ) :=
  LinearMap.snd ℝ _ _ ∘ₗ (equivProd ι).toLinearMap

theorem y_def : y = LinearMap.snd ℝ (ι → ℝ) (ι → ℝ) ∘ₗ (equivProd ι).toLinearMap := (rfl)

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

/-- The `xᵢ`-coordinate of `swap ι z` is the `yᵢ`-coordinate of `z`. -/
@[simp]
theorem swap_apply_inl (z : StdSpace ι) (i : ι) : swap ι z (Sum.inl i) = z (Sum.inr i) := (rfl)

/-- The `yᵢ`-coordinate of `swap ι z` is the `xᵢ`-coordinate of `z`. -/
@[simp]
theorem swap_apply_inr (z : StdSpace ι) (i : ι) : swap ι z (Sum.inr i) = z (Sum.inl i) := (rfl)

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

variable (n : ℕ) in
/-- The linear isometry of `StdSpace (Fin n)` onto `EuclideanSpace ℝ (Fin (n + n))` that
relabels the coordinates along `finSumFinEquiv`: the `xᵢ` become the first `n` coordinates and
the `yᵢ` the last `n`. -/
noncomputable def finSumIsometry : StdSpace (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + n)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finSumFinEquiv

theorem finSumIsometry_def (n : ℕ) :
    finSumIsometry n = LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finSumFinEquiv :=
  (rfl)

@[simp]
theorem finSumIsometry_apply {n : ℕ} (z : StdSpace (Fin n)) (k : Fin (n + n)) :
    finSumIsometry n z k = z (finSumFinEquiv.symm k) := by
  simp [finSumIsometry_def, Equiv.piCongrLeft']

@[simp]
theorem finSumIsometry_symm_apply {n : ℕ} (v : EuclideanSpace ℝ (Fin (n + n)))
    (i : Fin n ⊕ Fin n) : (finSumIsometry n).symm v i = v (finSumFinEquiv i) := by
  simp [finSumIsometry_def, Equiv.piCongrLeft']

end StdSpace

open StdSpace

variable [Fintype ι]

/-- The standard model `StdSpace ι` has real dimension `2 * Fintype.card ι`. -/
theorem finrank_stdSpace : Module.finrank ℝ (StdSpace ι) = 2 * Fintype.card ι := by
  rw [finrank_euclideanSpace, Fintype.card_sum, two_mul]

/-- `StdSpace (Fin (n + 1))` has real dimension `2 * n + 1 + 1`. This is the form in which
Mathlib's charts on the unit sphere of `StdSpace (Fin (n + 1))`, modelled on `𝓡 (2 * n + 1)`,
ask for it. -/
scoped instance fact_finrank_stdSpace_fin_succ (n : ℕ) :
    Fact (Module.finrank ℝ (StdSpace (Fin (n + 1))) = 2 * n + 1 + 1) :=
  ⟨by rw [finrank_stdSpace, Fintype.card_fin]; omega⟩

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

/-- `complexToRealEuclidean ι` carries `stdComplexPiSymplecticForm ι` to `ω₀`. -/
theorem stdForm_complexToRealEuclidean (u v : ι → ℂ) :
    stdForm ι (complexToRealEuclidean ι u) (complexToRealEuclidean ι v) =
      stdComplexPiSymplecticForm ι u v :=
  SymplecticForm.transport_apply_apply _ _ u v

/-- The coordinate swap `(x, y) ↦ (y, x)` reverses the sign of the standard form:
`ω₀(swap z, swap w) = -ω₀(z, w)`. -/
theorem stdForm_swap (z w : StdSpace ι) : stdForm ι (swap ι z) (swap ι w) = -stdForm ι z w := by
  simp [stdForm_apply]

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

/-- `complexToRealEuclidean ι` carries multiplication by `I` on `ι → ℂ` to `J₀`. -/
@[simp]
theorem stdComplexStructure_complexToRealEuclidean (v : ι → ℂ) :
    stdComplexStructure ι (complexToRealEuclidean ι v) =
      complexToRealEuclidean ι (Complex.I • v) := by
  rw [stdComplexStructure_def, AlmostComplexStructure.transport_apply]
  simp [AlmostComplexStructure.ofComplexModule_apply]

/-- `complexToRealEuclidean ι` carries multiplication by `exp (t I)` on `ι → ℂ` to the rotation
`z ↦ cos t • z + sin t • J₀ z`. -/
theorem complexToRealEuclidean_exp_mul_I_smul (t : ℝ) (v : ι → ℂ) :
    complexToRealEuclidean ι (Complex.exp (t * Complex.I) • v) =
      Real.cos t • complexToRealEuclidean ι v +
        Real.sin t • stdComplexStructure ι (complexToRealEuclidean ι v) := by
  rw [stdComplexStructure_complexToRealEuclidean, ← map_smul, ← map_smul, ← map_add,
    Complex.exp_mul_I, add_smul, ← Complex.ofReal_cos, ← Complex.ofReal_sin, mul_smul,
    Complex.coe_smul, Complex.coe_smul]

/-- `complexToRealEuclidean ι` is compatible with the norms: scaling by `a : ℂ` scales the norm
of the image by `‖a‖`. -/
theorem norm_complexToRealEuclidean_smul (a : ℂ) (v : ι → ℂ) :
    ‖complexToRealEuclidean ι (a • v)‖ = ‖a‖ * ‖complexToRealEuclidean ι v‖ := by
  have h : ‖complexToRealEuclidean ι (a • v)‖ ^ 2 =
      (‖a‖ * ‖complexToRealEuclidean ι v‖) ^ 2 := by
    rw [mul_pow, ← real_inner_self_eq_norm_sq (complexToRealEuclidean ι (a • v)),
      ← real_inner_self_eq_norm_sq (complexToRealEuclidean ι v), inner_complexToRealEuclidean,
      inner_complexToRealEuclidean, star_smul, smul_dotProduct,
      dotProduct_smul, smul_eq_mul, smul_eq_mul, Complex.star_def, ← mul_assoc,
      Complex.conj_mul', ← Complex.ofReal_pow, Complex.re_ofReal_mul]
  exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h

/-- The squared norm of `complexToRealEuclidean ι u` is `∑ᵢ ‖uᵢ‖²`. -/
theorem norm_sq_complexToRealEuclidean (u : ι → ℂ) :
    ‖complexToRealEuclidean ι u‖ ^ 2 = ∑ i, ‖u i‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_complexToRealEuclidean, dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Pi.star_apply, Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

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

/-- `ω₀(z, w) = (⟪J₀ z, w⟫ - ⟪z, J₀ w⟫) / 2`: the form of the Euclidean inner product and `J₀`
is `ω₀`. -/
theorem stdForm_apply_eq_inner_sub_inner (z w : StdSpace ι) :
    stdForm ι z w =
      2⁻¹ * (inner ℝ (stdComplexStructure ι z) w - inner ℝ z (stdComplexStructure ι w)) := by
  rw [← stdForm_apply_eq_inner, ← stdForm_apply_stdComplexStructure,
    AlmostComplexStructure.apply_apply]
  simp only [map_neg]
  ring

/-- Read through `complexToRealEuclidean ι`, the inner product of `z` with `I • u` is
`-ω₀(z, u)`, for `ω₀ = stdComplexPiSymplecticForm ι`. -/
theorem inner_complexToRealEuclidean_I_smul (z u : ι → ℂ) :
    inner ℝ (complexToRealEuclidean ι z) (complexToRealEuclidean ι (Complex.I • u)) =
      -stdComplexPiSymplecticForm ι z u := by
  rw [← stdComplexStructure_complexToRealEuclidean, real_inner_comm, ← stdForm_apply_eq_inner,
    ← (stdForm _).neg_eq, stdForm_complexToRealEuclidean]

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

/-- Relabelling the coordinate pairs along `σ : ι ≃ κ` commutes with the standard complex
structures `J₀` on `StdSpace ι` and on `StdSpace κ`. -/
theorem stdComplexStructure_piLpCongrLeft_sumCongr (σ : ι ≃ κ) (z : StdSpace ι) :
    stdComplexStructure κ (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (σ.sumCongr σ) z) =
      LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (σ.sumCongr σ) (stdComplexStructure ι z) :=
  StdSpace.ext (by ext; simp) (by simp)

/-- Relabelling the coordinate pairs along `σ : ι ≃ κ` is complex linear from `J₀` on
`StdSpace ι` to `J₀` on `StdSpace κ`. -/
theorem isComplexLinearMap_piLpCongrLeft_sumCongr (σ : ι ≃ κ) :
    IsComplexLinearMap (stdComplexStructure ι) (stdComplexStructure κ)
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (σ.sumCongr σ)).toLinearEquiv.toLinearMap :=
  (isComplexLinearMap_iff_apply _ _ _).2 fun z ↦
    (stdComplexStructure_piLpCongrLeft_sumCongr σ z).symm

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

/-! ### A smaller model inside a larger one -/

section Inclusion

namespace StdSpace

variable (k m : ℕ) in
/-- `StdSpace (Fin k)` inside `StdSpace (Fin (k + m))`: a point goes to the point whose first `k`
coordinate pairs are its own and whose last `m` pairs are `0`. It is the inclusion of the first
factor of `StdSpace (Fin k) × StdSpace (Fin m)`, read through `sumEquiv` and the relabelling
along `finSumFinEquiv`. -/
noncomputable def stdInl : StdSpace (Fin k) →L[ℝ] StdSpace (Fin (k + m)) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
      (finSumFinEquiv.sumCongr finSumFinEquiv)).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((sumEquiv (Fin k) (Fin m)).symm.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ _ _))

variable (k m : ℕ) in
theorem stdInl_def :
    stdInl k m =
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finSumFinEquiv.sumCongr finSumFinEquiv)
          ).toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((sumEquiv (Fin k) (Fin m)).symm.toContinuousLinearMap.comp
          (ContinuousLinearMap.inl ℝ _ _)) :=
  (rfl)

theorem x_stdInl {k m : ℕ} (z : StdSpace (Fin k)) :
    (stdInl k m z).x = Sum.elim z.x 0 ∘ finSumFinEquiv.symm := by
  simp [stdInl_def]

theorem y_stdInl {k m : ℕ} (z : StdSpace (Fin k)) :
    (stdInl k m z).y = Sum.elim z.y 0 ∘ finSumFinEquiv.symm := by
  simp [stdInl_def]

@[simp]
theorem stdInl_apply_inl_castAdd {k m : ℕ} (z : StdSpace (Fin k)) (i : Fin k) :
    stdInl k m z (Sum.inl (Fin.castAdd m i)) = z (Sum.inl i) := by
  simpa using congr_fun (x_stdInl (m := m) z) (Fin.castAdd m i)

@[simp]
theorem stdInl_apply_inr_castAdd {k m : ℕ} (z : StdSpace (Fin k)) (i : Fin k) :
    stdInl k m z (Sum.inr (Fin.castAdd m i)) = z (Sum.inr i) := by
  simpa using congr_fun (y_stdInl (m := m) z) (Fin.castAdd m i)

@[simp]
theorem stdInl_apply_inl_natAdd {k m : ℕ} (z : StdSpace (Fin k)) (i : Fin m) :
    stdInl k m z (Sum.inl (Fin.natAdd k i)) = 0 := by
  simpa using congr_fun (x_stdInl (m := m) z) (Fin.natAdd k i)

@[simp]
theorem stdInl_apply_inr_natAdd {k m : ℕ} (z : StdSpace (Fin k)) (i : Fin m) :
    stdInl k m z (Sum.inr (Fin.natAdd k i)) = 0 := by
  simpa using congr_fun (y_stdInl (m := m) z) (Fin.natAdd k i)

theorem injective_stdInl {k m : ℕ} : Function.Injective (stdInl k m) := by
  rw [stdInl_def, ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_comp]
  exact (LinearIsometryEquiv.injective _).comp
    ((ContinuousLinearEquiv.injective _).comp (Prod.mk_left_injective 0))

/-- The range of `stdInl k m` is the set of points whose coordinate pairs of index at least `k`
vanish. -/
theorem range_stdInl {k m : ℕ} :
    Set.range (stdInl k m) = {z | ∀ j : Fin (k + m), k ≤ (j : ℕ) → z.x j = 0 ∧ z.y j = 0} := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩ j hj
    obtain ⟨i, rfl⟩ : ∃ i : Fin m, Fin.natAdd k i = j :=
      ⟨⟨j - k, by omega⟩, Fin.ext (by simp; omega)⟩
    simp [x_apply, y_apply]
  · intro hz
    refine ⟨(equivProd (Fin k)).symm
      (fun i ↦ z.x (Fin.castAdd m i), fun i ↦ z.y (Fin.castAdd m i)), ?_⟩
    refine ext (funext fun j ↦ ?_) (funext fun j ↦ ?_) <;>
      refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) j
    · simp [x_apply]
    · simpa [x_apply] using (hz (Fin.natAdd k i) (by simp)).1.symm
    · simp [y_apply]
    · simpa [y_apply] using (hz (Fin.natAdd k i) (by simp)).2.symm

variable (k m : ℕ) in
/-- `StdSpace (Fin m)` inside `StdSpace (Fin (k + m))`: a point goes to the point whose last `m`
coordinate pairs are its own and whose first `k` pairs are `0`. It is the inclusion of the second
factor of `StdSpace (Fin k) × StdSpace (Fin m)`, read through `sumEquiv` and the relabelling
along `finSumFinEquiv`, as `stdInl k m` is that of the first. -/
noncomputable def stdInr : StdSpace (Fin m) →L[ℝ] StdSpace (Fin (k + m)) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
      (finSumFinEquiv.sumCongr finSumFinEquiv)).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((sumEquiv (Fin k) (Fin m)).symm.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ _ _))

variable (k m : ℕ) in
theorem stdInr_def :
    stdInr k m =
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finSumFinEquiv.sumCongr finSumFinEquiv)
          ).toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((sumEquiv (Fin k) (Fin m)).symm.toContinuousLinearMap.comp
          (ContinuousLinearMap.inr ℝ _ _)) :=
  (rfl)

theorem x_stdInr {k m : ℕ} (z : StdSpace (Fin m)) :
    (stdInr k m z).x = Sum.elim (0 : Fin k → ℝ) z.x ∘ finSumFinEquiv.symm := by
  simp [stdInr_def]

theorem y_stdInr {k m : ℕ} (z : StdSpace (Fin m)) :
    (stdInr k m z).y = Sum.elim (0 : Fin k → ℝ) z.y ∘ finSumFinEquiv.symm := by
  simp [stdInr_def]

@[simp]
theorem stdInr_apply_inl_castAdd {k m : ℕ} (z : StdSpace (Fin m)) (i : Fin k) :
    stdInr k m z (Sum.inl (Fin.castAdd m i)) = 0 := by
  simpa using congr_fun (x_stdInr (k := k) z) (Fin.castAdd m i)

@[simp]
theorem stdInr_apply_inr_castAdd {k m : ℕ} (z : StdSpace (Fin m)) (i : Fin k) :
    stdInr k m z (Sum.inr (Fin.castAdd m i)) = 0 := by
  simpa using congr_fun (y_stdInr (k := k) z) (Fin.castAdd m i)

@[simp]
theorem stdInr_apply_inl_natAdd {k m : ℕ} (z : StdSpace (Fin m)) (i : Fin m) :
    stdInr k m z (Sum.inl (Fin.natAdd k i)) = z (Sum.inl i) := by
  simpa using congr_fun (x_stdInr (k := k) z) (Fin.natAdd k i)

@[simp]
theorem stdInr_apply_inr_natAdd {k m : ℕ} (z : StdSpace (Fin m)) (i : Fin m) :
    stdInr k m z (Sum.inr (Fin.natAdd k i)) = z (Sum.inr i) := by
  simpa using congr_fun (y_stdInr (k := k) z) (Fin.natAdd k i)

theorem injective_stdInr {k m : ℕ} : Function.Injective (stdInr k m) := by
  rw [stdInr_def, ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_comp]
  exact (LinearIsometryEquiv.injective _).comp
    ((ContinuousLinearEquiv.injective _).comp (Prod.mk_right_injective 0))

omit [Fintype ι] in
variable (ι) in
/-- The inclusion of `ι → ℝ` into `StdSpace ι` as the `x`-coordinates, the `y`-coordinates being
`0`. -/
noncomputable def ofX : (ι → ℝ) →ₗ[ℝ] StdSpace ι :=
  (equivProd ι).symm.toLinearMap ∘ₗ LinearMap.inl ℝ _ _

omit [Fintype ι] in
variable (ι) in
theorem ofX_def : ofX ι = (equivProd ι).symm.toLinearMap ∘ₗ LinearMap.inl ℝ _ _ := (rfl)

omit [Fintype ι] in
@[simp]
theorem x_ofX (a : ι → ℝ) : (ofX ι a).x = a := (rfl)

omit [Fintype ι] in
@[simp]
theorem y_ofX (a : ι → ℝ) : (ofX ι a).y = 0 := (rfl)

omit [Fintype ι] in
@[simp]
theorem ofX_apply_inl (a : ι → ℝ) (i : ι) : ofX ι a (Sum.inl i) = a i := (rfl)

omit [Fintype ι] in
@[simp]
theorem ofX_apply_inr (a : ι → ℝ) (i : ι) : ofX ι a (Sum.inr i) = 0 := (rfl)

omit [Fintype ι] in
theorem injective_ofX : Function.Injective (ofX ι) := fun a b h ↦ by
  simpa using congrArg x h

omit [Fintype ι] in
/-- The range of `ofX ι` is the subspace `{y = 0}`. -/
theorem range_ofX : Set.range (ofX ι) = {z | z.y = 0} := by
  ext z
  refine ⟨fun ⟨a, ha⟩ ↦ ha ▸ y_ofX a, fun hz ↦ ⟨z.x, ext (x_ofX _) ((y_ofX _).trans ?_)⟩⟩
  exact (Set.mem_ofPred_eq.mp hz).symm

/-- The points `(a, 0)`, with `a : Fin k → ℝ` in the first `k` coordinates `x`, form the subspace
`{y = 0, and xⱼ = 0 for j ≥ k}`. -/
theorem range_stdInl_ofX {k m : ℕ} :
    Set.range (stdInl k m ∘ ofX (Fin k)) =
      {z | z.y = 0 ∧ ∀ j : Fin (k + m), k ≤ (j : ℕ) → z.x j = 0} := by
  rw [Set.range_comp, range_ofX]
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨?_, fun j hj ↦ ((range_stdInl (m := m)).subset ⟨w, rfl⟩ j hj).1⟩
    rw [y_stdInl, show w.y = 0 from hw]
    funext j; simp
  · rintro ⟨hy, hx⟩
    obtain ⟨w, rfl⟩ : z ∈ Set.range (stdInl k m) := by
      rw [range_stdInl]; exact fun j hj ↦ ⟨hx j hj, congr_fun hy j⟩
    refine ⟨w, funext fun i ↦ ?_, rfl⟩
    simpa using congr_fun hy (Fin.castAdd m i)

/-- `(a, w) ↦ (a, 0) + w`, putting `a : Fin k → ℝ` into the first `k` coordinates `x` and
`w : StdSpace (Fin m)` into the last `m` coordinate pairs, is injective. -/
theorem injective_stdInl_ofX_add_stdInr {k m : ℕ} :
    Function.Injective fun p : (Fin k → ℝ) × StdSpace (Fin m) ↦
      stdInl k m (ofX (Fin k) p.1) + stdInr k m p.2 := by
  rintro ⟨a, w⟩ ⟨a', w'⟩ h
  have hc (j : Fin (k + m) ⊕ Fin (k + m)) := congr_fun (congrArg WithLp.ofLp h) j
  refine Prod.ext (funext fun i ↦ ?_) (ext (funext fun i ↦ ?_) (funext fun i ↦ ?_))
  · simpa using hc (Sum.inl (Fin.castAdd m i))
  · simpa using hc (Sum.inl (Fin.natAdd k i))
  · simpa using hc (Sum.inr (Fin.natAdd k i))

/-- The points `(a, 0) + w`, with `a : Fin k → ℝ` in the first `k` coordinates `x` and
`w : StdSpace (Fin m)` in the last `m` coordinate pairs, form the subspace `{yⱼ = 0 for j < k}`. -/
theorem range_stdInl_ofX_add_stdInr {k m : ℕ} :
    Set.range (fun p : (Fin k → ℝ) × StdSpace (Fin m) ↦
      stdInl k m (ofX (Fin k) p.1) + stdInr k m p.2) =
      {z | ∀ j : Fin (k + m), (j : ℕ) < k → z.y j = 0} := by
  ext z
  constructor
  · rintro ⟨⟨a, w⟩, rfl⟩ j hj
    obtain ⟨i, rfl⟩ : ∃ i : Fin k, Fin.castAdd m i = j := ⟨⟨j, hj⟩, rfl⟩
    simp
  · intro hz
    refine ⟨(fun i ↦ z.x (Fin.castAdd m i),
      (equivProd (Fin m)).symm (fun i ↦ z.x (Fin.natAdd k i), fun i ↦ z.y (Fin.natAdd k i))), ?_⟩
    refine ext (funext fun j ↦ ?_) (funext fun j ↦ ?_) <;>
      refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) j
    · simp
    · simp
    · simpa [y_apply] using (hz (Fin.castAdd m i) (by simp)).symm
    · simp

end StdSpace

open StdSpace

/-- The first `k` and the last `m` coordinate pairs of `StdSpace (Fin (k + m))` are
`ω₀`-orthogonal, and `ω₀` restricts to the standard form on each:
`ω₀(z + w, z' + w') = ω₀(z, z') + ω₀(w, w')` along `stdInl k m` and `stdInr k m`. -/
theorem stdForm_stdInl_add_stdInr {k m : ℕ} (z z' : StdSpace (Fin k)) (w w' : StdSpace (Fin m)) :
    stdForm (Fin (k + m)) (stdInl k m z + stdInr k m w) (stdInl k m z' + stdInr k m w') =
      stdForm (Fin k) z z' + stdForm (Fin m) w w' := by
  have h (v : StdSpace (Fin k)) (u : StdSpace (Fin m)) : stdInl k m v + stdInr k m u =
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
          (finSumFinEquiv.sumCongr finSumFinEquiv)).toLinearEquiv
        ((sumEquiv (Fin k) (Fin m)).toLinearEquiv.symm (v, u)) := by
    rw [show (v, u) = (v, 0) + (0, u) by simp, map_add, map_add]
    simp [stdInl_def, stdInr_def]
  rw [h, h, (isSymplectomorphism_piLpCongrLeft_sumCongr _).apply,
    isSymplectomorphism_sumEquiv.symm.apply]
  simp

/-- `stdInl k m` pulls the standard form of `StdSpace (Fin (k + m))` back to that of
`StdSpace (Fin k)`. -/
theorem stdForm_stdInl {k m : ℕ} (z w : StdSpace (Fin k)) :
    stdForm (Fin (k + m)) (stdInl k m z) (stdInl k m w) = stdForm (Fin k) z w := by
  simpa using stdForm_stdInl_add_stdInr (m := m) z w 0 0

/-- `stdInr k m` pulls the standard form of `StdSpace (Fin (k + m))` back to that of
`StdSpace (Fin m)`. -/
theorem stdForm_stdInr {k m : ℕ} (w w' : StdSpace (Fin m)) :
    stdForm (Fin (k + m)) (stdInr k m w) (stdInr k m w') = stdForm (Fin m) w w' := by
  simpa using stdForm_stdInl_add_stdInr (k := k) 0 0 w w'

/-- The `ω₀`-orthogonal of the coisotropic subspace `{yⱼ = 0 for j < k}` of `StdSpace (Fin n)` is
the span of the first `k` vectors `∂/∂xⱼ`: a point `v` is `ω₀`-orthogonal to every point of that
subspace exactly when `y = 0` and `xⱼ = 0` for all `j ≥ k`. -/
theorem forall_stdForm_eq_zero_iff_y_eq_zero_and_x_eq_zero {n : ℕ} (k : ℕ) (v : StdSpace (Fin n)) :
    (∀ z : StdSpace (Fin n), (∀ j : Fin n, (j : ℕ) < k → z.y j = 0) → stdForm (Fin n) z v = 0) ↔
      v.y = 0 ∧ ∀ j : Fin n, k ≤ (j : ℕ) → v.x j = 0 := by
  constructor
  · intro h
    refine ⟨funext fun j ↦ ?_, fun j hj ↦ ?_⟩
    · have := h ((equivProd (Fin n)).symm (Pi.single j 1, 0)) fun i _ ↦ by simp
      simpa [Pi.single_apply] using this
    · have := h ((equivProd (Fin n)).symm (0, Pi.single j 1)) fun i hi ↦ by
        simp [Fin.ext_iff, show (i : ℕ) ≠ j by omega]
      simpa [Pi.single_apply] using this
  · rintro ⟨hy, hx⟩ z hz
    rw [stdForm_apply]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [show v.y i = 0 from congr_fun hy i, mul_zero, zero_sub, neg_eq_zero]
    rcases lt_or_ge (i : ℕ) k with hi | hi
    · rw [hz i hi, zero_mul]
    · rw [hx i hi, mul_zero]

/-- The subspace `{y = 0}`, the range of `StdSpace.ofX`, is isotropic for `stdForm`. -/
theorem stdForm_ofX (a b : ι → ℝ) : stdForm ι (ofX ι a) (ofX ι b) = 0 := by
  rw [stdForm_apply]
  simp [-x_apply, -y_apply]

end Inclusion

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

/-- `EuclideanSpace.sumEquivProd` is complex linear from `J₀` to Tau Ceti's product complex
structure `(x, y) ↦ (-y, x)`. -/
theorem isComplexLinearMap_sumEquivProd :
    IsComplexLinearMap (stdComplexStructure ι) (AlmostComplexStructure.product (EuclideanSpace ℝ ι))
      (EuclideanSpace.sumEquivProd (𝕜 := ℝ) (ι := ι) (κ := ι)).toLinearEquiv.toLinearMap := by
  rw [← stdComplexStructure_transport_sumEquivProd]
  exact AlmostComplexStructure.isComplexLinearMap_transport _ _

end SymplecticGeometry

end
