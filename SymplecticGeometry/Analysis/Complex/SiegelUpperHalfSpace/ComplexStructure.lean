/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import SymplecticGeometry.Analysis.Complex.SiegelUpperHalfSpace.Action
public import SymplecticGeometry.LinearAlgebra.ComplexStructure.Action
public import TauCeti.Analysis.Matrix.EuclideanLin
public import TauCeti.Analysis.Matrix.Normed
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Basic
public import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Basic
import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Matrix
import TauCeti.Analysis.Calculus.ContinuousLinearMapInverse
import TauCeti.Analysis.Calculus.FDeriv.Inv
import TauCeti.Analysis.Matrix.Sqrt
import TauCeti.Geometry.Symplectic.Complex.Line
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Transpose
import SymplecticGeometry.LinearAlgebra.ComplexStructure.Standard
import SymplecticGeometry.LinearAlgebra.Matrix.Block
import SymplecticGeometry.LinearAlgebra.Matrix.SymplecticGroup.Basic
import SymplecticGeometry.Topology.Instances.Matrix
import SymplecticGeometry.LinearAlgebra.Matrix.PosDef.Basic
import Mathlib.RingTheory.PicardGroup
import TauCeti.Topology.Algebra.Module.FiniteDimension
import Mathlib.RingTheory.Valuation.ValuationRing
import SymplecticGeometry.LinearAlgebra.Matrix.OfReal

/-!
# The Siegel upper half space and the compatible complex structures

To a point `Z = X + iY` of the Siegel upper half space this file attaches the real matrix
`J(Z) = !![X Y⁻¹, -Y - X Y⁻¹ X; Y⁻¹, -Y⁻¹ X]`, written in the blocks of `ι ⊕ ι`, as in
`Matrix.J ι ℝ = !![0, -1; 1, 0]`. Its map on `StdSpace ι` is a complex structure compatible with
`ω₀ = stdForm ι`, and `Z ↦ J(Z)` is the unique bijection from the Siegel upper half space onto the
`ω₀`-compatible complex structures that sends `i𝟙` to `J₀` and intertwines the action
`Z ↦ (AZ + B)(CZ + D)⁻¹` of the symplectic group with conjugation `J ↦ Ψ J Ψ⁻¹`.

## Main definitions

* `SiegelUpperHalfSpace.complexStructureMatrix`: the formula `J(Z)`, for every complex matrix
  `Z`, with `X` and `Y` its real and imaginary parts.
* `SiegelUpperHalfSpace.ofComplexStructureMatrix`: the formula of the inverse,
  `M ↦ M₁₁ M₂₁⁻¹ + i M₂₁⁻¹`, for every real matrix `M` indexed by `ι ⊕ ι`.
* `SiegelUpperHalfSpace.complexStructure`: the complex structure of `J(Z)` on `StdSpace ι`.
* `SiegelUpperHalfSpace.compatibleEquiv`: the bijection `Z ↦ J(Z)` onto the `ω₀`-compatible
  complex structures, with inverse given by `ofComplexStructureMatrix`.
* `SiegelUpperHalfSpace.complexStructureMatrixDeriv Z`: the derivative `Ẑ ↦ K J(Z) - J(Z) K` of
  `J` at `Z`, described below.

## Main results

* `SiegelUpperHalfSpace.complexStructureMatrix_smul_I`: `J(Ψ • i𝟙) = Ψ J₀ Ψ⁻¹`, and
  `SiegelUpperHalfSpace.complexStructureMatrix_smul`: `J(Ψ • Z) = Ψ J(Z) Ψ⁻¹`.
* `SiegelUpperHalfSpace.compatible_complexStructure`: `J(Z)` is compatible with `ω₀`.
* `SiegelUpperHalfSpace.complexStructureMatrix_mul_self`: `J(Z)² = -1` whenever `Y` is invertible.
* `SiegelUpperHalfSpace.complexStructure_smul`: the complex structure of `Ψ • Z` is `Ψ` acting on
  that of `Z`, by the action of `GL` on complex structures.
* `SiegelUpperHalfSpace.eq_complexStructure_of_smul`: an equivariant map from the Siegel upper
  half space to the complex structures that sends `i𝟙` to `J₀` is `Z ↦ J(Z)`; and
  `SiegelUpperHalfSpace.eq_compatibleEquiv_iff`: `compatibleEquiv` is the only equivariant
  bijection onto the compatible complex structures sending `i𝟙` to `J₀`.
* `SiegelUpperHalfSpace.contDiffOn_complexStructureMatrix` and
  `SiegelUpperHalfSpace.contDiffOn_ofComplexStructureMatrix`: both formulas are smooth on open
  sets of matrices containing the Siegel upper half space and the compatible complex structures.
* `SiegelUpperHalfSpace.hasFDerivAt_complexStructureMatrix`: the derivative of `J(Z)` at every
  complex matrix with invertible imaginary part; and
  `SiegelUpperHalfSpace.complexStructureMatrixDeriv_I_smul` and
  `SiegelUpperHalfSpace.trace_complexStructureMatrixDeriv_mul_self`: it is complex linear, and
  half the trace of its square is Siegel's metric.
* `SiegelUpperHalfSpace.complexStructure_single_inl`: for one index, `J(x + iy)` sends `(1, 0)` to
  `(x + i) / y`; and
  `SiegelUpperHalfSpace.stdComplexSymplecticForm_tames_transport_complexStructure`: moved to `ℂ`,
  `J(Z)` is tamed by the standard area form, by Tau Ceti's
  `TauCeti.stdComplexSymplecticForm_tames_iff_im_pos`.
* `SiegelUpperHalfSpace.mulAction_symplecticGroup_and_compatibleEquiv`: the statement of
  McDuff–Salamon's Exercise 2.5.11 and Lemma 2.5.12 as one theorem.

## Implementation notes

McDuff–Salamon prove Lemma 2.5.12 with the transitivity of Exercise 2.5.11. Here transitivity
needs no complex structures: it comes from the explicit symplectic matrix
`Φ = !![G, X G⁻ᵀ; 0, G⁻ᵀ]` of `SiegelUpperHalfSpace.fromBlocks_re_smul_I`, with `G Gᵀ = Y`, and the
formula for `J(Z)` is checked directly: `J(Z) = Φ Φᵀ J₀ = Φ J₀ Φ⁻¹`. Since the stabilizer of
`i𝟙` consists of the symplectic matrices commuting with `J₀`
(`SiegelUpperHalfSpace.smul_I_eq_I_iff_commute`), this gives `J(Ψ • i𝟙) = Ψ J₀ Ψ⁻¹` for every
symplectic `Ψ`, from which equivariance, compatibility and uniqueness follow. The inverse is read
off the blocks `M₁₁` and `M₂₁` of a compatible structure.

Smoothness is stated in coordinates: `complexStructureMatrix` is smooth on the open set of complex
matrices with invertible imaginary part, which contains the Siegel upper half space, and
`ofComplexStructureMatrix` is smooth on the open set of real matrices with invertible lower left
block, which contains the matrices of the compatible complex structures. Matrices carry the
`L^∞` operator norm (`Matrix.Norms.Operator`); any other norm gives the same smooth maps.

For the derivative, write `P = !![Y, X; 0, 1]`. Then `J(Z) = P J₀ P⁻¹`
(`complexStructureMatrix_eq_mul_J_mul`), so the derivative of `J` at `Z` is the commutator
`Ẑ ↦ K J(Z) - J(Z) K` with `K = Ṗ P⁻¹` and `Ṗ = !![Ẏ, Ẋ; 0, 0]` (`imReBlocks`). Since
`Ṗ(iẐ) = Ṗ(Ẑ) J₀`, this gives `K(iẐ) = K(Ẑ) J(Z)`, and with `J(Z)² = -1` the derivative is complex
linear: `dJ(iẐ) = -J(Z) dJ(Ẑ)`. Its square has half trace `tr((Y⁻¹ Ẋ)² + (Y⁻¹ Ẏ)²)`, Siegel's
metric, by a computation of block traces. Both identities are proved at a general `Z`, without
reduction to `Z = i𝟙`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.5,
  Example 4.3.6 and Exercise 4.3.7.
* C. L. Siegel, *Symplectic geometry*, Amer. J. Math. 65 (1943), 1–86, for the metric on the
  Siegel upper half space.
-/

public section

noncomputable section

open Complex Matrix TauCeti

namespace SymplecticGeometry

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace SiegelUpperHalfSpace

/-! ### The matrix `J(Z)` -/

/-- The matrix `J(Z) = !![X Y⁻¹, -Y - X Y⁻¹ X; Y⁻¹, -Y⁻¹ X]` of a complex matrix `Z = X + iY`. -/
def complexStructureMatrix (Z : Matrix ι ι ℂ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ :=
  fromBlocks (Z.map Complex.re * (Z.map Complex.im)⁻¹)
    (-Z.map Complex.im - Z.map Complex.re * (Z.map Complex.im)⁻¹ * Z.map Complex.re)
    (Z.map Complex.im)⁻¹ (-((Z.map Complex.im)⁻¹ * Z.map Complex.re))

theorem complexStructureMatrix_def (Z : Matrix ι ι ℂ) :
    complexStructureMatrix Z =
      fromBlocks (Z.map Complex.re * (Z.map Complex.im)⁻¹)
        (-Z.map Complex.im - Z.map Complex.re * (Z.map Complex.im)⁻¹ * Z.map Complex.re)
        (Z.map Complex.im)⁻¹ (-((Z.map Complex.im)⁻¹ * Z.map Complex.re)) :=
  (rfl)

/-- On the Siegel upper half space, `J(Z)` in terms of `X = Z.re` and `Y = Z.im`. -/
theorem complexStructureMatrix_coe (Z : SiegelUpperHalfSpace ι) :
    complexStructureMatrix (Z : Matrix ι ι ℂ) =
      fromBlocks (Z.re * Z.im⁻¹) (-Z.im - Z.re * Z.im⁻¹ * Z.re) Z.im⁻¹ (-(Z.im⁻¹ * Z.re)) := by
  rw [complexStructureMatrix_def, re_def, im_def]

/-- `J(i𝟙) = J₀`. -/
@[simp]
theorem complexStructureMatrix_I_smul_one :
    complexStructureMatrix (Complex.I • 1 : Matrix ι ι ℂ) = J ι ℝ := by
  rw [← coe_I, complexStructureMatrix_coe]
  simp [J]

/-- For `G` invertible with `G Gᵀ = Y`, and `Φ = !![G, X G⁻ᵀ; 0, G⁻ᵀ]`, `J(Z) = Φ Φᵀ J₀`. -/
private theorem complexStructureMatrix_eq_mul_transpose_mul_J (Z : SiegelUpperHalfSpace ι)
    {G : GL ι ℝ} (hG : (G : Matrix ι ι ℝ) * (G : Matrix ι ι ℝ)ᵀ = Z.im) :
    complexStructureMatrix (Z : Matrix ι ι ℂ) =
      fromBlocks (G : Matrix ι ι ℝ) (Z.re * (↑G⁻¹ : Matrix ι ι ℝ)ᵀ) 0 (↑G⁻¹ : Matrix ι ι ℝ)ᵀ *
        (fromBlocks (G : Matrix ι ι ℝ) (Z.re * (↑G⁻¹ : Matrix ι ι ℝ)ᵀ) 0
          (↑G⁻¹ : Matrix ι ι ℝ)ᵀ)ᵀ * J ι ℝ := by
  set g : Matrix ι ι ℝ := ↑G
  set h : Matrix ι ι ℝ := ↑G⁻¹
  have hhg : h * g = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hYinv : Z.im⁻¹ = hᵀ * h := by
    rw [← hG]
    refine inv_eq_left_inv ?_
    calc hᵀ * h * (g * gᵀ) = hᵀ * (h * g) * gᵀ := by simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [hhg, Matrix.mul_one]
        exact mul_eq_one_comm.mp (GeneralLinearGroup.coe_transpose_mul_coe_inv_transpose G)
  have hX : Z.reᵀ = Z.re := Z.isSymm_re.eq
  rw [complexStructureMatrix_coe, hYinv, ← hG]
  simp only [fromBlocks_transpose, transpose_zero, transpose_transpose, transpose_mul, hX, J,
    fromBlocks_multiply]
  congr 1 <;> simp only [Matrix.mul_assoc, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_neg,
    Matrix.mul_one, add_zero, zero_add, neg_add_rev]
  simp only [← Matrix.mul_assoc]
  abel

/-- `J(Ψ • i𝟙) = Ψ J₀ Ψ⁻¹` for every symplectic matrix `Ψ`. -/
theorem complexStructureMatrix_smul_I (Ψ : symplecticGroup ι ℝ) :
    complexStructureMatrix ((Ψ • (SiegelUpperHalfSpace.I : SiegelUpperHalfSpace ι) :
        SiegelUpperHalfSpace ι) : Matrix ι ι ℂ) =
      (Ψ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) * J ι ℝ * (↑Ψ⁻¹ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) := by
  set Z := Ψ • (SiegelUpperHalfSpace.I : SiegelUpperHalfSpace ι) with hZ
  obtain ⟨G, hG⟩ := Z.posDef_im.exists_generalLinearGroup_mul_transpose_eq
  set Φ : symplecticGroup ι ℝ := ⟨_, fromBlocks_re_mem_symplecticGroup Z G⟩
  have hΦ : Φ • (SiegelUpperHalfSpace.I : SiegelUpperHalfSpace ι) = Z := fromBlocks_re_smul_I Z hG
  set K := Φ⁻¹ * Ψ
  have hK : Commute (J ι ℝ) (K : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) := by
    rw [← smul_I_eq_I_iff_commute, mul_smul, ← hZ, ← hΦ, inv_smul_smul]
  have hΨ : (Ψ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) = Φ * K := by
    rw [← Submonoid.coe_mul, mul_inv_cancel_left]
  have hΨinv : (↑Ψ⁻¹ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) =
      ((K⁻¹ : symplecticGroup ι ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) * (Φ⁻¹).val := by
    rw [← Submonoid.coe_mul, ← _root_.mul_inv_rev, mul_inv_cancel_left]
  have hKK : (K : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) *
      ((K⁻¹ : symplecticGroup ι ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) = 1 := by
    rw [← Submonoid.coe_mul, mul_inv_cancel, OneMemClass.coe_one]
  have hΦinv : (↑Φ⁻¹ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) = -J ι ℝ * (Φ : Matrix _ _ ℝ)ᵀ * J ι ℝ :=
    SymplecticGroup.coe_inv Φ
  calc complexStructureMatrix (Z : Matrix ι ι ℂ)
      = (Φ : Matrix _ _ ℝ) * (Φ : Matrix _ _ ℝ)ᵀ * J ι ℝ :=
        complexStructureMatrix_eq_mul_transpose_mul_J Z hG
    _ = (Φ : Matrix _ _ ℝ) * J ι ℝ * (Φ⁻¹).val := by
        rw [hΦinv]
        simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (J ι ℝ) (J ι ℝ), J_squared, Matrix.neg_mul, Matrix.one_mul,
          Matrix.mul_neg, neg_neg]
    _ = (Φ : Matrix _ _ ℝ) * J ι ℝ * ((K : Matrix _ _ ℝ) * (K⁻¹).val) * (Φ⁻¹).val := by
        rw [hKK, Matrix.mul_one]
    _ = (Ψ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) * J ι ℝ * (Ψ⁻¹).val := by
        rw [hΨ, hΨinv]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (J ι ℝ), hK.eq, Matrix.mul_assoc]

/-- The formula `J(Z)` intertwines the action of the symplectic group on the Siegel upper half
space with conjugation: `J(Ψ • Z) = Ψ J(Z) Ψ⁻¹`. -/
theorem complexStructureMatrix_smul (Ψ : symplecticGroup ι ℝ) (Z : SiegelUpperHalfSpace ι) :
    complexStructureMatrix ((Ψ • Z : SiegelUpperHalfSpace ι) : Matrix ι ι ℂ) =
      (Ψ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) * complexStructureMatrix (Z : Matrix ι ι ℂ) *
        (↑Ψ⁻¹ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) := by
  obtain ⟨Φ, rfl⟩ := exists_smul_I_eq Z
  rw [smul_smul, complexStructureMatrix_smul_I, complexStructureMatrix_smul_I,
    _root_.mul_inv_rev, Submonoid.coe_mul, Submonoid.coe_mul]
  simp only [Matrix.mul_assoc]

/-- `J(Z)² = -1` for every complex matrix `Z` with invertible imaginary part. -/
theorem complexStructureMatrix_mul_self {Z : Matrix ι ι ℂ} (hZ : IsUnit (Z.map Complex.im).det) :
    complexStructureMatrix Z * complexStructureMatrix Z = -1 := by
  have h₁ : Z.map Complex.im * (Z.map Complex.im)⁻¹ = 1 := mul_nonsing_inv _ hZ
  have h₂ : (Z.map Complex.im)⁻¹ * Z.map Complex.im = 1 := nonsing_inv_mul _ hZ
  rw [complexStructureMatrix_def, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]
  congr 1 <;> simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_neg, Matrix.neg_mul,
    Matrix.mul_assoc, h₁, h₂,
    ← Matrix.mul_assoc (Z.map Complex.im) (Z.map Complex.im)⁻¹, Matrix.one_mul,
    Matrix.mul_one, neg_neg, neg_zero] <;> abel

/-! ### The complex structure `J(Z)` on `StdSpace ι` -/

/-- The complex structure on `StdSpace ι` whose matrix is `J(Z)`. -/
def complexStructure (Z : SiegelUpperHalfSpace ι) : AlmostComplexStructure (StdSpace ι) where
  toLinearMap := toEuclideanLin (complexStructureMatrix (Z : Matrix ι ι ℂ))
  square_neg := by
    rw [← toLpLin_mul, complexStructureMatrix_mul_self (isUnit_det_map_im Z), map_neg,
      toLpLin_one]

@[simp]
theorem complexStructure_toLinearMap (Z : SiegelUpperHalfSpace ι) :
    (complexStructure Z).toLinearMap = toEuclideanLin (complexStructureMatrix (Z : Matrix ι ι ℂ)) :=
  (rfl)

/-- The complex structure of `i𝟙` is `J₀`. -/
@[simp]
theorem complexStructure_I :
    complexStructure (SiegelUpperHalfSpace.I : SiegelUpperHalfSpace ι) = stdComplexStructure ι :=
  AlmostComplexStructure.toLinearMap_injective <| by
    rw [complexStructure_toLinearMap, coe_I, complexStructureMatrix_I_smul_one,
      stdComplexStructure_eq_toEuclideanLin_J]

/-- The complex structure of `Ψ • Z` is `Ψ`, read in `GL`, acting on that of `Z`, that is, its
conjugate `Ψ J(Z) Ψ⁻¹`. -/
theorem complexStructure_smul (Ψ : symplecticGroup ι ℝ) (Z : SiegelUpperHalfSpace ι) :
    complexStructure (Ψ • Z) = GLSymplectic.ofSymplecticGroup ι ℝ Ψ • complexStructure Z := by
  rw [AlmostComplexStructure.generalLinearGroup_smul_def]
  refine AlmostComplexStructure.toLinearMap_injective (LinearMap.ext fun v ↦ ?_)
  simp only [complexStructure_toLinearMap, complexStructureMatrix_smul, SymplecticGroup.coe_inv',
    AlmostComplexStructure.transport_toLinearMap, LinearEquiv.conj_apply, LinearMap.comp_apply,
    toLpLin_mul_same]
  simp

/-- The complex structure `J(Z)` is compatible with `ω₀`. -/
theorem compatible_complexStructure (Z : SiegelUpperHalfSpace ι) :
    (stdForm ι).Compatible (complexStructure Z) := by
  obtain ⟨Φ, rfl⟩ := exists_smul_I_eq Z
  rw [complexStructure_smul, complexStructure_I]
  exact (compatible_generalLinearGroup_smul_iff (GLSymplectic.ofSymplecticGroup_mem ι ℝ Φ) _).2
    stdForm_compatible

/-- **Uniqueness.** A map from the Siegel upper half space to the complex structures on
`StdSpace ι` that sends `i𝟙` to `J₀` and intertwines the action of the symplectic group with
conjugation is `Z ↦ J(Z)`. -/
theorem eq_complexStructure_of_smul
    {F : SiegelUpperHalfSpace ι → AlmostComplexStructure (StdSpace ι)}
    (hI : F SiegelUpperHalfSpace.I = stdComplexStructure ι)
    (hF : ∀ (Ψ : symplecticGroup ι ℝ) Z, F (Ψ • Z) =
      GLSymplectic.ofSymplecticGroup ι ℝ Ψ • F Z) :
    F = complexStructure := by
  funext Z
  obtain ⟨Ψ, rfl⟩ := exists_smul_I_eq Z
  rw [hF, complexStructure_smul, hI, complexStructure_I]

/-! ### The inverse -/

/-- For a real matrix `M = !![M₁₁, M₁₂; M₂₁, M₂₂]`, the complex matrix `M₁₁ M₂₁⁻¹ + i M₂₁⁻¹`. On
the matrices of the compatible complex structures it inverts `complexStructureMatrix`. -/
def ofComplexStructureMatrix (M : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) : Matrix ι ι ℂ :=
  (M.toBlocks₁₁ * M.toBlocks₂₁⁻¹).map ofReal + Complex.I • M.toBlocks₂₁⁻¹.map ofReal

theorem ofComplexStructureMatrix_def (M : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) :
    ofComplexStructureMatrix M =
      (M.toBlocks₁₁ * M.toBlocks₂₁⁻¹).map ofReal + Complex.I • M.toBlocks₂₁⁻¹.map ofReal :=
  (rfl)

@[simp]
theorem map_re_ofComplexStructureMatrix (M : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) :
    (ofComplexStructureMatrix M).map Complex.re = M.toBlocks₁₁ * M.toBlocks₂₁⁻¹ := by
  ext i j
  simp [ofComplexStructureMatrix_def, -Matrix.map_ofReal_mul]

@[simp]
theorem map_im_ofComplexStructureMatrix (M : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) :
    (ofComplexStructureMatrix M).map Complex.im = M.toBlocks₂₁⁻¹ := by
  ext i j
  simp [ofComplexStructureMatrix_def, -Matrix.map_ofReal_mul]

/-- `ofComplexStructureMatrix` is a left inverse of `complexStructureMatrix` on the Siegel upper
half space. -/
@[simp]
theorem ofComplexStructureMatrix_complexStructureMatrix (Z : SiegelUpperHalfSpace ι) :
    ofComplexStructureMatrix (complexStructureMatrix (Z : Matrix ι ι ℂ)) = Z := by
  have hY : IsUnit Z.im.det := im_def Z ▸ isUnit_det_map_im Z
  rw [ofComplexStructureMatrix_def, complexStructureMatrix_coe, toBlocks_fromBlocks₁₁,
    toBlocks_fromBlocks₂₁, nonsing_inv_nonsing_inv _ hY, Matrix.mul_assoc,
    nonsing_inv_mul _ hY, Matrix.mul_one]
  exact (coe_eq_re_add_I_smul_im Z).symm

/-- `ofComplexStructureMatrix` is a right inverse of `complexStructureMatrix` on the real
matrices `M` with `M² = -1` whose lower left block is invertible. -/
theorem complexStructureMatrix_ofComplexStructureMatrix {M : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ}
    (hM : M * M = -1) (hM₂₁ : IsUnit M.toBlocks₂₁.det) :
    complexStructureMatrix (ofComplexStructureMatrix M) = M := by
  have h₁₁ := toBlocks₁₁_mul_toBlocks₁₁_add_of_mul_self_eq_neg_one hM
  have h₂₁ := toBlocks₂₁_mul_toBlocks₁₁_add_of_mul_self_eq_neg_one hM
  set B := M.toBlocks₂₁⁻¹
  have hBC : B * M.toBlocks₂₁ = 1 := nonsing_inv_mul _ hM₂₁
  have hCB : M.toBlocks₂₁ * B = 1 := mul_nonsing_inv _ hM₂₁
  rw [complexStructureMatrix_def, map_re_ofComplexStructureMatrix, map_im_ofComplexStructureMatrix,
    nonsing_inv_nonsing_inv _ hM₂₁]
  conv_rhs => rw [← fromBlocks_toBlocks M]
  congr 1
  · rw [Matrix.mul_assoc, hBC, Matrix.mul_one]
  · calc -B - M.toBlocks₁₁ * B * M.toBlocks₂₁ * (M.toBlocks₁₁ * B)
        = (-1 - M.toBlocks₁₁ * M.toBlocks₁₁) * B := by
          simp only [Matrix.mul_assoc, hBC, Matrix.sub_mul, Matrix.neg_mul, Matrix.one_mul]
      _ = M.toBlocks₁₂ := by
          rw [← h₁₁, add_sub_cancel_left, Matrix.mul_assoc, hCB, Matrix.mul_one]
  · rw [← Matrix.mul_assoc, eq_neg_of_add_eq_zero_left h₂₁, Matrix.neg_mul, neg_neg,
      Matrix.mul_assoc, hCB, Matrix.mul_one]

/-- The point `M₁₁ M₂₁⁻¹ + i M₂₁⁻¹` of the Siegel upper half space attached to an
`ω₀`-compatible complex structure with matrix `M`. -/
private def ofCompatible {J : AlmostComplexStructure (StdSpace ι)}
    (hJ : (stdForm ι).Compatible J) : SiegelUpperHalfSpace ι where
  coe := ofComplexStructureMatrix (toEuclideanLin.symm J.toLinearMap)
  isSymm := by
    rw [ofComplexStructureMatrix_def]
    exact ((isSymm_toBlocks₁₁_mul_inv_toBlocks₂₁_of_compatible hJ).map _).add
      (((isHermitian_iff_isSymm.1 (posDef_toBlocks₂₁_of_compatible hJ).inv.isHermitian).map
        _).smul _)
  posDef_map_im := by
    rw [map_im_ofComplexStructureMatrix]
    exact (posDef_toBlocks₂₁_of_compatible hJ).inv

private theorem coe_ofCompatible {J : AlmostComplexStructure (StdSpace ι)}
    (hJ : (stdForm ι).Compatible J) :
    (ofCompatible hJ : Matrix ι ι ℂ) =
      ofComplexStructureMatrix (toEuclideanLin.symm J.toLinearMap) :=
  (rfl)

/-- **The Siegel upper half space and the compatible complex structures.** `Z ↦ J(Z)` is a
bijection from the Siegel upper half space onto the `ω₀`-compatible complex structures on
`StdSpace ι`, with inverse `J ↦ M₁₁ M₂₁⁻¹ + i M₂₁⁻¹` for `M` the matrix of `J`. -/
def compatibleEquiv :
    SiegelUpperHalfSpace ι ≃ {J : AlmostComplexStructure (StdSpace ι) // (stdForm ι).Compatible J}
    where
  toFun Z := ⟨complexStructure Z, compatible_complexStructure Z⟩
  invFun J := ofCompatible J.property
  left_inv Z := by
    ext1
    rw [coe_ofCompatible, complexStructure_toLinearMap, LinearEquiv.symm_apply_apply,
      ofComplexStructureMatrix_complexStructureMatrix]
  right_inv J := by
    obtain ⟨J, hJ⟩ := J
    refine Subtype.ext (AlmostComplexStructure.toLinearMap_injective ?_)
    rw [complexStructure_toLinearMap, coe_ofCompatible,
      complexStructureMatrix_ofComplexStructureMatrix J.toEuclideanLin_symm_mul_self
        (isUnit_det_toBlocks₂₁_of_compatible hJ),
      LinearEquiv.apply_symm_apply]

@[simp]
theorem coe_compatibleEquiv_apply (Z : SiegelUpperHalfSpace ι) :
    (compatibleEquiv Z : AlmostComplexStructure (StdSpace ι)) = complexStructure Z :=
  (rfl)

@[simp]
theorem coe_compatibleEquiv_symm_apply
    (J : {J : AlmostComplexStructure (StdSpace ι) // (stdForm ι).Compatible J}) :
    (compatibleEquiv.symm J : Matrix ι ι ℂ) =
      ofComplexStructureMatrix (toEuclideanLin.symm (J : AlmostComplexStructure _).toLinearMap) :=
  (rfl)
/-- `compatibleEquiv` is the only bijection from the Siegel upper half space onto the
`ω₀`-compatible complex structures that sends `i𝟙` to `J₀` and intertwines the action of the
symplectic group with conjugation. In fact neither bijectivity nor compatibility is needed for
uniqueness, see `eq_complexStructure_of_smul`. -/
theorem eq_compatibleEquiv_iff
    (F : SiegelUpperHalfSpace ι → {J : AlmostComplexStructure (StdSpace ι) //
      (stdForm ι).Compatible J}) :
    (Function.Bijective F ∧
      (F SiegelUpperHalfSpace.I : AlmostComplexStructure (StdSpace ι)) = stdComplexStructure ι ∧
      ∀ (Ψ : symplecticGroup ι ℝ) Z,
        (F (Ψ • Z) : AlmostComplexStructure (StdSpace ι)) =
          GLSymplectic.ofSymplecticGroup ι ℝ Ψ • (F Z : AlmostComplexStructure (StdSpace ι))) ↔
      F = compatibleEquiv := by
  constructor
  · rintro ⟨-, hI, hF⟩
    funext Z
    exact Subtype.ext (congrFun (eq_complexStructure_of_smul (F := fun Z ↦ (F Z).val) hI hF) Z)
  · rintro rfl
    exact ⟨compatibleEquiv.bijective, complexStructure_I, complexStructure_smul⟩

/-! ### Smoothness in coordinates -/

section Smooth

open scoped Matrix.Norms.Operator ContDiff

/-- The formula `M ↦ M₁₁ M₂₁⁻¹ + i M₂₁⁻¹` of the inverse is smooth on the open set of real
matrices with invertible lower left block, which contains the matrices of the `ω₀`-compatible
complex structures (`isUnit_det_toBlocks₂₁_of_compatible`). -/
theorem contDiffOn_ofComplexStructureMatrix :
    ContDiffOn ℝ ∞ (ofComplexStructureMatrix : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ → Matrix ι ι ℂ)
      {M : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ | IsUnit M.toBlocks₂₁.det} := by
  intro M hM
  have hofReal : ContDiff ℝ ∞ fun Y : Matrix ι ι ℝ ↦ Y.map ofReal :=
    (LinearMap.toContinuousLinearMap
      (Complex.ofRealCLM.toLinearMap.mapMatrix : Matrix ι ι ℝ →ₗ[ℝ] Matrix ι ι ℂ)).contDiff
  /- The four blocks, as the inverse of `fromBlocksLinearEquiv`. Its smoothness goes through
  `IsBoundedLinearMap`, so that it stays in the operator norm's topology: the coercion lemma of
  `LinearMap.toContinuousLinearMap` would ask for the product topology on matrices instead. -/
  let blocks : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ →ₗ[ℝ]
      (Matrix ι ι ℝ × Matrix ι ι ℝ) × (Matrix ι ι ℝ × Matrix ι ι ℝ) :=
    (fromBlocksLinearEquiv ℝ).symm.toLinearMap
  have hblocks : ContDiff ℝ ∞ blocks :=
    ((IsBoundedLinearMap.isLinearMap_and_continuous_iff_isBoundedLinearMap blocks).1
      ⟨blocks.isLinear, blocks.continuous_of_finiteDimensional⟩).contDiff
  have h₁₁ : ContDiff ℝ ∞ fun N : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ ↦ N.toBlocks₁₁ := by
    simpa only [blocks, LinearEquiv.coe_coe, fromBlocksLinearEquiv_symm_apply] using
      hblocks.fst.fst
  have h₂₁ : ContDiff ℝ ∞ fun N : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ ↦ N.toBlocks₂₁ := by
    simpa only [blocks, LinearEquiv.coe_coe, fromBlocksLinearEquiv_symm_apply] using
      hblocks.snd.fst
  have hinv : ContDiffAt ℝ ∞ (fun N : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ ↦ N.toBlocks₂₁⁻¹) M := by
    simpa only [nonsing_inv_eq_ringInverse] using
      h₂₁.contDiffAt.inverse ((isUnit_iff_isUnit_det _).2 hM)
  exact ((hofReal.contDiffAt.comp M (h₁₁.contDiffAt.mul hinv)).add
    ((hofReal.contDiffAt.comp M hinv).const_smul Complex.I)).contDiffWithinAt

section LinftyOp

/- Matrices carry the topology of the operator norm here, so that the linear maps below are
continuous linear maps between normed spaces. -/
attribute [local instance] Matrix.linftyOpTopologicalSpace

/-- The formula `J(Z)` is smooth on the open set of complex matrices with invertible imaginary
part, which contains the Siegel upper half space (`isUnit_det_map_im`). -/
theorem contDiffOn_complexStructureMatrix :
    ContDiffOn ℝ ∞ (complexStructureMatrix : Matrix ι ι ℂ → Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ)
      {Z : Matrix ι ι ℂ | IsUnit (Z.map Complex.im).det} := by
  intro Z hZ
  have hre : ContDiff ℝ ∞ fun Z : Matrix ι ι ℂ ↦ Z.map Complex.re :=
    (LinearMap.toContinuousLinearMap
      (Complex.reLm.mapMatrix : Matrix ι ι ℂ →ₗ[ℝ] Matrix ι ι ℝ)).contDiff
  have him : ContDiff ℝ ∞ fun Z : Matrix ι ι ℂ ↦ Z.map Complex.im :=
    (LinearMap.toContinuousLinearMap
      (Complex.imLm.mapMatrix : Matrix ι ι ℂ →ₗ[ℝ] Matrix ι ι ℝ)).contDiff
  have hinv : ContDiffAt ℝ ∞ (fun W : Matrix ι ι ℂ ↦ (W.map Complex.im)⁻¹) Z := by
    simpa only [nonsing_inv_eq_ringInverse] using
      him.contDiffAt.inverse ((isUnit_iff_isUnit_det _).2 hZ)
  have hXYinv := hre.contDiffAt.mul hinv
  refine ContDiffAt.contDiffWithinAt ?_
  convert (LinearMap.toContinuousLinearMap
    ((fromBlocksLinearEquiv ℝ).toLinearMap :
      _ →ₗ[ℝ] Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ)).contDiff.contDiffAt.comp Z
    ((hXYinv.prodMk ((him.contDiffAt.neg).sub (hXYinv.mul hre.contDiffAt))).prodMk
      (hinv.prodMk (hinv.mul hre.contDiffAt).neg)) using 1
  funext W
  simp only [Function.comp_apply, LinearMap.coe_toContinuousLinearMap', LinearEquiv.coe_coe,
    fromBlocksLinearEquiv_apply, complexStructureMatrix_def]

/-! ### The derivative of `J(Z)` -/

/-- The real linear map `dZ ↦ !![Ẏ, Ẋ; 0, 0]` from complex matrices `dZ = Ẋ + iẎ` to real block
matrices: the derivative of `Z ↦ !![Y, X; 0, 1]`. -/
def imReBlocks : Matrix ι ι ℂ →L[ℝ] Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ :=
  LinearMap.toContinuousLinearMap <| (fromBlocksLinearEquiv ℝ).toLinearMap ∘ₗ
    (((Complex.imLm.mapMatrix : Matrix ι ι ℂ →ₗ[ℝ] Matrix ι ι ℝ).prod
      Complex.reLm.mapMatrix).prod 0)

/-- The value of `imReBlocks`: `!![Im W, Re W; 0, 0]`. -/
theorem imReBlocks_apply (W : Matrix ι ι ℂ) :
    imReBlocks W = fromBlocks (W.map Complex.im) (W.map Complex.re) 0 0 := by
  simp [imReBlocks]

/-- With `P = !![Y, X; 0, 1]` and `Y` invertible, `J(Z) = P J₀ P⁻¹`. -/
theorem complexStructureMatrix_eq_mul_J_mul {Z : Matrix ι ι ℂ}
    (hZ : IsUnit (Z.map Complex.im).det) :
    complexStructureMatrix Z =
      fromBlocks (Z.map Complex.im) (Z.map Complex.re) 0 1 * J ι ℝ *
        (fromBlocks (Z.map Complex.im) (Z.map Complex.re) 0 1)⁻¹ := by
  rw [inv_fromBlocks_zero₂₁_of_isUnit_iff _ _ _ (by simp [isUnit_iff_isUnit_det, hZ.ne_zero]),
    complexStructureMatrix_def, J, fromBlocks_multiply, fromBlocks_multiply]
  simp [Matrix.mul_assoc]
  abel

/-- The derivative of `J` at `Z = X + iY`: `dZ ↦ K J(Z) - J(Z) K` with `K = Ṗ P⁻¹`, where
`P = !![Y, X; 0, 1]` and `Ṗ = !![Ẏ, Ẋ; 0, 0]` (`complexStructureMatrixDeriv_apply`). It is the
derivative when `Y` is invertible (`hasFDerivAt_complexStructureMatrix`). -/
def complexStructureMatrixDeriv (Z : Matrix ι ι ℂ) :
    Matrix ι ι ℂ →L[ℝ] Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ :=
  ((ContinuousLinearMap.mul ℝ _).flip (complexStructureMatrix Z) -
      ContinuousLinearMap.mul ℝ _ (complexStructureMatrix Z)) ∘L
    (ContinuousLinearMap.mul ℝ _).flip
      (fromBlocks (Z.map Complex.im) (Z.map Complex.re) 0 1)⁻¹ ∘L
    imReBlocks

/-- The value of `complexStructureMatrixDeriv Z` at `dZ`: the commutator of `K = Ṗ P⁻¹` with
`J(Z)`. -/
theorem complexStructureMatrixDeriv_apply (Z dZ : Matrix ι ι ℂ) :
    complexStructureMatrixDeriv Z dZ =
      imReBlocks dZ * (fromBlocks (Z.map Complex.im) (Z.map Complex.re) 0 1)⁻¹ *
          complexStructureMatrix Z -
        complexStructureMatrix Z *
          (imReBlocks dZ * (fromBlocks (Z.map Complex.im) (Z.map Complex.re) 0 1)⁻¹) :=
  (rfl)

/-- The block formula `J(Z)` has derivative `complexStructureMatrixDeriv Z` at every complex
matrix `Z` with invertible imaginary part. -/
theorem hasFDerivAt_complexStructureMatrix {Z : Matrix ι ι ℂ}
    (hZ : IsUnit (Z.map Complex.im).det) :
    HasFDerivAt complexStructureMatrix (complexStructureMatrixDeriv Z) Z := by
  set P := fromBlocks (Z.map Complex.im) (Z.map Complex.re) 0 (1 : Matrix ι ι ℝ) with hP_def
  have hP : HasFDerivAt (fun W : Matrix ι ι ℂ ↦
      fromBlocks (W.map Complex.im) (W.map Complex.re) 0 (1 : Matrix ι ι ℝ)) imReBlocks Z := by
    have : (fun W : Matrix ι ι ℂ ↦
        fromBlocks (W.map Complex.im) (W.map Complex.re) 0 (1 : Matrix ι ι ℝ)) =
        fun W ↦ imReBlocks W + fromBlocks 0 0 0 1 := by
      funext W; rw [imReBlocks_apply, fromBlocks_add]; simp
    rw [this]
    exact imReBlocks.hasFDerivAt.add_const _
  have hPu : IsUnit P := by simp [hP_def, isUnit_iff_isUnit_det, hZ.ne_zero]
  have hR := (Matrix.hasFDerivAt_inv ((isUnit_iff_isUnit_det P).1 hPu)).comp Z hP
  have h := (hP.mul_const' (J ι ℝ)).mul' hR
  refine (h.congr_of_eventuallyEq ?_).congr_fderiv ?_
  · filter_upwards [Matrix.isOpen_setOfPred_isUnit_det_map_im.mem_nhds hZ] with W hW
    simp only [Pi.mul_apply, Function.comp_apply]
    exact complexStructureMatrix_eq_mul_J_mul hW
  · ext1 dZ
    simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply, neg_apply,
      ContinuousLinearMap.mulLeftRight_apply, complexStructureMatrixDeriv_apply,
      Function.comp_apply, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op, smul_eq_mul]
    rw [complexStructureMatrix_eq_mul_J_mul hZ, ← hP_def]
    rw [Matrix.mul_assoc _ P⁻¹, ← Matrix.mul_assoc P⁻¹, ← Matrix.mul_assoc P⁻¹,
      nonsing_inv_mul _ ((isUnit_iff_isUnit_det P).1 hPu), Matrix.one_mul]
    simp only [Matrix.mul_assoc, Matrix.mul_neg]
    abel

/-- Multiplication by `i` on `Ẑ` is multiplication of `Ṗ` by `J₀` on the right:
`Ṗ(iẐ) = Ṗ(Ẑ) J₀`. -/
theorem imReBlocks_I_smul (dZ : Matrix ι ι ℂ) :
    imReBlocks (Complex.I • dZ) = imReBlocks dZ * J ι ℝ := by
  rw [imReBlocks_apply, imReBlocks_apply, J, fromBlocks_multiply]
  congr 1 <;> ext <;> simp

/-- `Ṗ P⁻¹ J(Z) = Ṗ J₀ P⁻¹`, in the notation of `complexStructureMatrixDeriv`. -/
theorem imReBlocks_mul_inv_mul_complexStructureMatrix {Z : Matrix ι ι ℂ}
    (hZ : IsUnit (Z.map Complex.im).det) (dZ : Matrix ι ι ℂ) :
    imReBlocks dZ * (fromBlocks (Z.map Complex.im) (Z.map Complex.re) 0 1)⁻¹ *
        complexStructureMatrix Z =
      imReBlocks dZ * J ι ℝ * (fromBlocks (Z.map Complex.im) (Z.map Complex.re) 0 1)⁻¹ := by
  have hP : IsUnit (fromBlocks (Z.map Complex.im) (Z.map Complex.re) 0 (1 : Matrix ι ι ℝ)).det := by
    simp [hZ.ne_zero]
  rw [complexStructureMatrix_eq_mul_J_mul hZ, Matrix.mul_assoc (imReBlocks dZ),
    ← Matrix.mul_assoc _ (fromBlocks _ _ _ _ * _), ← Matrix.mul_assoc _ (fromBlocks _ _ _ _),
    nonsing_inv_mul _ hP, Matrix.one_mul, Matrix.mul_assoc]

/-- The derivative of `J` is complex linear for the structure `-J(Z)` on the target:
`dJ(i Ẑ) = -J(Z) dJ(Ẑ)`. -/
theorem complexStructureMatrixDeriv_I_smul {Z : Matrix ι ι ℂ}
    (hZ : IsUnit (Z.map Complex.im).det) (dZ : Matrix ι ι ℂ) :
    complexStructureMatrixDeriv Z (Complex.I • dZ) =
      -(complexStructureMatrix Z * complexStructureMatrixDeriv Z dZ) := by
  have hJ := complexStructureMatrix_mul_self hZ
  have hK := imReBlocks_mul_inv_mul_complexStructureMatrix hZ dZ
  rw [complexStructureMatrixDeriv_apply, complexStructureMatrixDeriv_apply, imReBlocks_I_smul,
    ← hK]
  simp only [Matrix.mul_sub, Matrix.mul_assoc, hJ, ← Matrix.mul_assoc (complexStructureMatrix Z)
    (complexStructureMatrix Z)]
  simp only [← Matrix.mul_assoc, neg_mul, mul_neg, mul_one, one_mul, neg_sub]

/-- Siegel's formula: half the trace of the square of `dJ(Ẑ)` at `Z = X + iY` is
`tr((Y⁻¹ Ẋ)² + (Y⁻¹ Ẏ)²)`. -/
theorem trace_complexStructureMatrixDeriv_mul_self {Z : Matrix ι ι ℂ}
    (hZ : IsUnit (Z.map Complex.im).det) (dZ : Matrix ι ι ℂ) :
    2⁻¹ * trace (complexStructureMatrixDeriv Z dZ * complexStructureMatrixDeriv Z dZ) =
      trace (((Z.map Complex.im)⁻¹ * dZ.map Complex.re) ^ 2 +
        ((Z.map Complex.im)⁻¹ * dZ.map Complex.im) ^ 2) := by
  have hJ := complexStructureMatrix_mul_self hZ
  have hKM := imReBlocks_mul_inv_mul_complexStructureMatrix hZ dZ
  have hQP : (fromBlocks (Z.map Complex.im) (Z.map Complex.re) 0 (1 : Matrix ι ι ℝ))⁻¹ *
      imReBlocks dZ =
      fromBlocks ((Z.map Complex.im)⁻¹ * dZ.map Complex.im)
        ((Z.map Complex.im)⁻¹ * dZ.map Complex.re) 0 0 := by
    rw [inv_fromBlocks_zero₂₁_of_isUnit_iff _ _ _ (by simp [isUnit_iff_isUnit_det, hZ.ne_zero]),
      imReBlocks_apply, fromBlocks_multiply]
    simp
  rw [complexStructureMatrixDeriv_apply]
  generalize complexStructureMatrix Z = M at hJ hKM ⊢
  generalize (fromBlocks (Z.map Complex.im) (Z.map Complex.re) 0 (1 : Matrix ι ι ℝ))⁻¹ = Q
    at hQP hKM ⊢
  generalize imReBlocks dZ = P at hQP hKM ⊢
  -- `tr((K M - M K)²) = 2 tr((K M)²) + 2 tr(K²)` for `K = P Q`, since `M² = -1`.
  have h₁ : ∀ K : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ, trace ((K * M - M * K) * (K * M - M * K)) =
      2 * trace (K * M * (K * M)) + 2 * trace (K * K) := by
    intro K
    have e₁ : trace (K * M * (M * K)) = -trace (K * K) := by
      rw [← Matrix.mul_assoc, Matrix.mul_assoc K, hJ]; simp
    have e₂ : trace (M * K * (K * M)) = -trace (K * K) := by
      rw [trace_mul_comm, ← Matrix.mul_assoc, Matrix.mul_assoc K, hJ]; simp
    have e₃ : trace (M * K * (M * K)) = trace (K * M * (K * M)) := by
      rw [Matrix.mul_assoc, trace_mul_comm]; simp only [Matrix.mul_assoc]
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, trace_sub, trace_sub, trace_sub, e₁, e₂,
      e₃]
    ring
  -- `tr((A Q)²) = tr((Q A)²)`.
  have h₂ : ∀ A : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ, trace (A * Q * (A * Q)) = trace (Q * A * (Q * A)) := by
    intro A
    rw [Matrix.mul_assoc, trace_mul_comm]; simp only [Matrix.mul_assoc]
  rw [h₁, hKM, h₂, h₂, ← Matrix.mul_assoc Q P (J ι ℝ), hQP, J]
  simp only [fromBlocks_multiply, trace_fromBlocks]
  simp [sq, trace_add]
  ring

end LinftyOp

/-- **The Siegel upper half space.** The symplectic group acts on the Siegel upper half space by
`Ψ • Z = (AZ + B)(CZ + D)⁻¹`, transitively, and holomorphically on an open set containing the
Siegel upper half space. The stabilizer of `i𝟙` is the realified unitary group, and the orbit map
of `i𝟙` is a bijection from the quotient by it. There is exactly one bijection onto the
`ω₀`-compatible complex structures on `StdSpace ι` that sends `i𝟙` to `J₀` and intertwines the
action with the action of `Ψ` in `GL`, that is, with conjugation `J ↦ Ψ J Ψ⁻¹`; its matrix is
`J(Z) = !![X Y⁻¹, -Y - X Y⁻¹ X; Y⁻¹, -Y⁻¹ X]`, and it is a diffeomorphism in coordinates: `J(Z)`
and the formula of the inverse are smooth on open sets of matrices containing the Siegel upper
half space and the compatible complex structures.

Milestone: *Siegel upper half space*. -/
theorem mulAction_symplecticGroup_and_compatibleEquiv :
    MulAction.IsPretransitive (symplecticGroup ι ℝ) (SiegelUpperHalfSpace ι) ∧
    (∀ Ψ : symplecticGroup ι ℝ,
      IsOpen {Z : Matrix ι ι ℂ | IsUnit (denom Ψ Z).det} ∧
      Set.range ((↑) : SiegelUpperHalfSpace ι → Matrix ι ι ℂ) ⊆
        {Z : Matrix ι ι ℂ | IsUnit (denom Ψ Z).det} ∧
      DifferentiableOn ℂ (fun Z ↦ num Ψ Z * (denom Ψ Z)⁻¹)
        {Z : Matrix ι ι ℂ | IsUnit (denom Ψ Z).det}) ∧
    (MulAction.stabilizer (symplecticGroup ι ℝ)
        (SiegelUpperHalfSpace.I : SiegelUpperHalfSpace ι)).toSubmonoid.map
        (symplecticGroup ι ℝ).subtype =
      (unitaryGroup ι ℂ).map (realifyAlgHom ι ℂ) ∧
    Function.Bijective (MulAction.ofQuotientStabilizer (symplecticGroup ι ℝ)
      (SiegelUpperHalfSpace.I : SiegelUpperHalfSpace ι)) ∧
    (∀ F : SiegelUpperHalfSpace ι → {J : AlmostComplexStructure (StdSpace ι) //
        (stdForm ι).Compatible J},
      (Function.Bijective F ∧
        (F SiegelUpperHalfSpace.I : AlmostComplexStructure (StdSpace ι)) = stdComplexStructure ι ∧
        ∀ (Ψ : symplecticGroup ι ℝ) Z,
          (F (Ψ • Z) : AlmostComplexStructure (StdSpace ι)) =
            GLSymplectic.ofSymplecticGroup ι ℝ Ψ • (F Z : AlmostComplexStructure (StdSpace ι))) ↔
        F = compatibleEquiv) ∧
    (∀ Z : SiegelUpperHalfSpace ι,
      toEuclideanLin.symm (compatibleEquiv Z : AlmostComplexStructure (StdSpace ι)).toLinearMap =
        complexStructureMatrix (Z : Matrix ι ι ℂ)) ∧
    (∀ J : {J : AlmostComplexStructure (StdSpace ι) // (stdForm ι).Compatible J},
      (compatibleEquiv.symm J : Matrix ι ι ℂ) =
        ofComplexStructureMatrix
          (toEuclideanLin.symm (J : AlmostComplexStructure (StdSpace ι)).toLinearMap)) ∧
    IsOpen {Z : Matrix ι ι ℂ | IsUnit (Z.map Complex.im).det} ∧
    (∀ Z : SiegelUpperHalfSpace ι, IsUnit ((Z : Matrix ι ι ℂ).map Complex.im).det) ∧
    ContDiffOn ℝ ∞ (complexStructureMatrix : Matrix ι ι ℂ → Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ)
      {Z : Matrix ι ι ℂ | IsUnit (Z.map Complex.im).det} ∧
    IsOpen {M : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ | IsUnit M.toBlocks₂₁.det} ∧
    (∀ J : {J : AlmostComplexStructure (StdSpace ι) // (stdForm ι).Compatible J},
      IsUnit (toEuclideanLin.symm
        (J : AlmostComplexStructure (StdSpace ι)).toLinearMap).toBlocks₂₁.det) ∧
    ContDiffOn ℝ ∞ (ofComplexStructureMatrix : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ → Matrix ι ι ℂ)
      {M : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ | IsUnit M.toBlocks₂₁.det} :=
  ⟨inferInstance,
    fun Ψ ↦ ⟨isOpen_setOfPred_isUnit_det_denom (Ψ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ),
      range_coe_subset_setOfPred_isUnit_det_denom Ψ.property,
      differentiableOn_num_mul_inv_denom (Ψ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ)⟩,
    map_stabilizer_I,
    ⟨MulAction.injective_ofQuotientStabilizer _ _, fun Z ↦
      (exists_smul_I_eq Z).imp' QuotientGroup.mk fun Ψ hΨ ↦
        (MulAction.ofQuotientStabilizer_mk _ _ Ψ).trans hΨ⟩,
    eq_compatibleEquiv_iff,
    fun _ ↦ LinearEquiv.symm_apply_apply _ _,
    fun _ ↦ rfl,
    isOpen_setOfPred_isUnit_det_map_im,
    isUnit_det_map_im,
    contDiffOn_complexStructureMatrix,
    isOpen_setOfPred_isUnit_det_toBlocks₂₁,
    fun J ↦ isUnit_det_toBlocks₂₁_of_compatible J.property,
    contDiffOn_ofComplexStructureMatrix⟩
end Smooth

/-! ### Index one -/

/-- For a type `ι` with one element and `Z = x + iy`, the complex structure `J(Z)` sends the
first basis vector `(1, 0)` to `(x / y, 1 / y)`, that is, to `(x + i) / y` in the coordinates of
`complexToRealEuclidean`. -/
theorem complexStructure_single_inl [Unique ι] (Z : SiegelUpperHalfSpace ι) :
    complexStructure Z (EuclideanSpace.single (Sum.inl default) 1) =
      complexToRealEuclidean ι fun _ ↦
        ((Z.re default default : ℂ) + Complex.I) / (Z.im default default : ℂ) := by
  have hy : ((Z : Matrix ι ι ℂ) default default).im ≠ 0 :=
    (posDef_iff_of_unique.1 Z.posDef_map_im).ne'
  have h : ((Z : Matrix ι ι ℂ) default default).im⁻¹ = ((Z : Matrix ι ι ℂ) default default).im *
      (((Z : Matrix ι ι ℂ) default default).im⁻¹ * ((Z : Matrix ι ι ℂ) default default).im⁻¹) := by
    field_simp
  refine StdSpace.ext ?_ ?_ <;> ext i <;>
    simp [Subsingleton.elim i default, StdSpace.x_apply, StdSpace.y_apply, toLpLin_apply,
      complexStructureMatrix_coe, div_eq_mul_inv, h.symm]

/-- For a type `ι` with one element, the complex structure `J(Z)`, moved to `ℂ` along
`(x, y) ↦ x + iy` (`StdSpace.equivComplex`), is tamed by the standard area form of `ℂ`: by Tau
Ceti's `TauCeti.stdComplexSymplecticForm_tames_iff_im_pos`, this says that it sends `1` to
`(x + i) / y`, whose imaginary part `1 / y` is positive. -/
theorem stdComplexSymplecticForm_tames_transport_complexStructure [Unique ι]
    (Z : SiegelUpperHalfSpace ι) :
    stdComplexSymplecticForm.Tames
      ((complexStructure Z).transport (StdSpace.equivComplex ι).toLinearEquiv) := by
  have hy : 0 < Z.im default default := posDef_iff_of_unique.1 Z.posDef_im
  rw [stdComplexSymplecticForm_tames_iff_im_pos, AlmostComplexStructure.transport_apply,
    LinearIsometryEquiv.coe_symm_toLinearEquiv, LinearIsometryEquiv.coe_toLinearEquiv,
    StdSpace.equivComplex_symm_one, complexStructure_single_inl]
  simpa [Complex.div_im] using hy

end SiegelUpperHalfSpace

end SymplecticGeometry

end
