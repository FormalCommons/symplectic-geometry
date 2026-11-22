/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Matrix.Normed
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import SymplecticGeometry.Analysis.Complex.SiegelUpperHalfSpace.ComplexStructure
public import SymplecticGeometry.Geometry.Manifold.Instances.SiegelUpperHalfSpace
public import SymplecticGeometry.Geometry.Symplectic.CompatibleSpace.Curvature
public import SymplecticGeometry.Geometry.Symplectic.CompatibleSpace.Geodesic
import SymplecticGeometry.Analysis.CStarAlgebra.Matrix
import SymplecticGeometry.Topology.Instances.Matrix

/-!
# The Siegel upper half space and the Kähler manifold of compatible complex structures

This file identifies the manifold of `ω₀`-compatible complex structures on `StdSpace ι` with the
Siegel upper half space, and collects the results on the space of compatible complex structures
into one theorem.

For `Z = X + iY` the bijection `SiegelUpperHalfSpace.compatibleEquiv` sends `Z` to the structure
with matrix `J(Z) = !![X Y⁻¹, -Y - X Y⁻¹ X; Y⁻¹, -Y⁻¹ X]`. With `P = !![Y, X; 0, 1]` one has
`J(Z) = P J₀ P⁻¹` (`complexStructureMatrix_eq_mul_J_mul`), so the derivative of `J` at `Z` is the
commutator `Ẑ ↦ K J(Z) - J(Z) K` with `K = Ṗ P⁻¹` and `Ṗ = !![Ẏ, Ẋ; 0, 0]`. Since
`Ṗ(iẐ) = Ṗ(Ẑ) J₀`, this gives `K(iẐ) = K(Ẑ) J(Z)`, and with `J(Z)² = -1` the derivative is complex
linear: `dJ(iẐ) = -J(Z) dJ(Ẑ)`. Its square has half trace `tr((Y⁻¹ Ẋ)² + (Y⁻¹ Ẏ)²)`, Siegel's
metric, by a computation of block traces. Both identities are proved at a general `Z`, without
reduction to `Z = i𝟙`.

## Main definitions

* `SiegelUpperHalfSpace.complexStructureMatrixDeriv Z`: the derivative `Ẑ ↦ K J(Z) - J(Z) K`.
* `SiegelUpperHalfSpace.compatibleDiffeomorph ι`: `compatibleEquiv` as a diffeomorphism from the
  Siegel upper half space, with its manifold structure of
  `Geometry/Manifold/Instances/SiegelUpperHalfSpace.lean`, onto the manifold of compatible
  complex structures of `Geometry/Manifold/Instances/CompatibleComplexStructures.lean`.

## Main results

* `SiegelUpperHalfSpace.hasFDerivAt_complexStructureMatrix`: the derivative of `J(Z)` at every
  complex matrix with invertible imaginary part.
* `SiegelUpperHalfSpace.complexStructureMatrixDeriv_I_smul` and
  `SiegelUpperHalfSpace.trace_complexStructureMatrixDeriv_mul_self`: the two matrix identities.
* `SiegelUpperHalfSpace.isPseudoholomorphic_compatibleDiffeomorph`: the diffeomorphism is
  holomorphic, for the complex structure of the Siegel upper half space (Tau Ceti's
  `ofComplexManifold`) and the structure `Ĵ ↦ -J Ĵ`.
* `SiegelUpperHalfSpace.inner_mfderiv_compatibleDiffeomorph`: the pulled-back metric is Siegel's.
* `TauCeti.SymplecticForm.isKahler_compatibleSpaceForm_and_compatibleDiffeomorph`: the
  submanifold, its dimension and tangent spaces, the Kähler structure and its invariance, the
  Levi-Civita connection, the geodesics and completeness, the curvature, and the Siegel upper half
  space, in one statement.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third
  edition][McDuffSalamon2017], §2.5, Example 4.3.6 and Exercise 4.3.7.
* C. L. Siegel, *Symplectic geometry*, Amer. J. Math. 65 (1943), 1–86, for the metric on the
  Siegel upper half space.
-/


public section

noncomputable section

open Matrix
open scoped Matrix.Norms.Operator

attribute [local instance] Matrix.linftyOpTopologicalSpace

namespace SymplecticGeometry

namespace SiegelUpperHalfSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The derivative of `J(Z)` -/

/-- The real linear map `dZ ↦ !![Ẏ, Ẋ; 0, 0]` from complex matrices `dZ = Ẋ + iẎ` to real block
matrices: the derivative of `Z ↦ !![Y, X; 0, 1]`. -/
def imReBlocks : Matrix ι ι ℂ →L[ℝ] Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun W ↦ fromBlocks (W.map Complex.im) (W.map Complex.re) 0 0
      map_add' := fun W W' ↦ by rw [fromBlocks_add]; simp [Matrix.map_add]
      map_smul' := fun c W ↦ by rw [fromBlocks_smul]; congr 1 <;> ext <;> simp }

/-- The value of `imReBlocks`: `!![Im W, Re W; 0, 0]`. -/
theorem imReBlocks_apply (W : Matrix ι ι ℂ) :
    imReBlocks W = fromBlocks (W.map Complex.im) (W.map Complex.re) 0 0 :=
  (rfl)

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
  have hR := (hasFDerivAt_ringInverse (𝕜 := ℝ) hPu.unit).comp Z hP
  have h := (hP.mul_const' (J ι ℝ)).mul' hR
  refine (h.congr_of_eventuallyEq ?_).congr_fderiv ?_
  · filter_upwards [Matrix.isOpen_setOf_isUnit_det_map_im.mem_nhds hZ] with W hW
    simp only [Pi.mul_apply, Function.comp_apply, ← nonsing_inv_eq_ringInverse]
    exact complexStructureMatrix_eq_mul_J_mul hW
  · ext1 dZ
    have hu : ((hPu.unit⁻¹ : (Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ)ˣ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) = P⁻¹ := by
      rw [← Ring.inverse_unit, IsUnit.unit_spec, nonsing_inv_eq_ringInverse]
    simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply, neg_apply,
      ContinuousLinearMap.mulLeftRight_apply, complexStructureMatrixDeriv_apply,
      Function.comp_apply, hu, ← nonsing_inv_eq_ringInverse, MulOpposite.smul_eq_mul_unop,
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

/-! ### The diffeomorphism -/

open scoped Manifold ContDiff RealInnerProductSpace
open TauCeti _root_.Bundle

/-- The model space of the Siegel upper half space: the complex symmetric matrices. -/
local notation "𝒮" ι:max => selfAdjointMatricesSubmodule (1 : Matrix ι ι ℂ)

local notation "𝒥₀" ι:max =>
  {J : AlmostComplexStructure (StdSpace ι) // SymplecticForm.Compatible (stdForm ι) J}

/-- The endomorphism of `StdSpace ι` of the compatible structure `J(Z)` is the map of the matrix
`J(Z)`. -/
theorem compatibleCLM_compatibleEquiv (Z : SiegelUpperHalfSpace ι) :
    (stdForm ι).compatibleCLM (compatibleEquiv Z) =
      Matrix.toEuclideanCLM (n := ι ⊕ ι) (𝕜 := ℝ) (complexStructureMatrix (Z : Matrix ι ι ℂ)) := by
  refine ContinuousLinearMap.coe_injective ?_
  rw [SymplecticForm.toLinearMap_compatibleCLM, coe_compatibleEquiv_apply,
    complexStructure_toLinearMap, coe_toEuclideanCLM_eq_toEuclideanLin]

/-- `Z ↦ J(Z)` is smooth from the Siegel upper half space to the compatible complex structures. -/
theorem contMDiff_compatibleEquiv :
    ContMDiff 𝓘(ℝ, 𝒮 ι) 𝓘(ℝ, (stdForm ι).compatibleModel) ∞
      (compatibleEquiv : SiegelUpperHalfSpace ι → 𝒥₀ ι) := by
  rw [SymplecticForm.contMDiff_compatibleCLM_comp_iff]
  have h : ContMDiff 𝓘(ℝ, 𝒮 ι) 𝓘(ℝ, Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) ∞
      (fun Z : SiegelUpperHalfSpace ι ↦ complexStructureMatrix (Z : Matrix ι ι ℂ)) :=
    contDiffOn_complexStructureMatrix.contMDiffOn.comp_contMDiff contMDiff_coe
      fun Z ↦ isUnit_det_map_im Z
  convert (LinearMap.toContinuousLinearMap
    (Matrix.toEuclideanCLM (n := ι ⊕ ι) (𝕜 := ℝ)).toAlgEquiv.toLinearMap).contDiff.comp_contMDiff h
    using 1
  funext Z
  exact compatibleCLM_compatibleEquiv Z

/-- The inverse `J ↦ M₁₁ M₂₁⁻¹ + i M₂₁⁻¹` of `compatibleEquiv` is smooth. -/
theorem contMDiff_compatibleEquiv_symm :
    ContMDiff 𝓘(ℝ, (stdForm ι).compatibleModel) 𝓘(ℝ, 𝒮 ι) ∞
      (compatibleEquiv.symm : 𝒥₀ ι → SiegelUpperHalfSpace ι) := by
  rw [contMDiff_iff_coe_comp]
  have h : ContMDiff 𝓘(ℝ, (stdForm ι).compatibleModel) 𝓘(ℝ, Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) ∞
      (fun J : 𝒥₀ ι ↦ (Matrix.toEuclideanCLM (n := ι ⊕ ι) (𝕜 := ℝ)).symm
        ((stdForm ι).compatibleCLM J)) :=
    (LinearMap.toContinuousLinearMap
      (Matrix.toEuclideanCLM (n := ι ⊕ ι) (𝕜 := ℝ)).symm.toAlgEquiv.toLinearMap).contDiff
      |>.comp_contMDiff SymplecticForm.contMDiff_compatibleCLM
  convert contDiffOn_ofComplexStructureMatrix.contMDiffOn.comp_contMDiff h
    (fun J ↦ by
      simpa [SymplecticForm.compatibleCLM_def,
        Matrix.toEuclideanCLM_symm_toContinuousLinearMap] using
        isUnit_det_toBlocks₂₁_of_compatible J.property) using 1
  funext J
  rw [coe_compatibleEquiv_symm_apply, Function.comp_apply, SymplecticForm.compatibleCLM_def,
    Matrix.toEuclideanCLM_symm_toContinuousLinearMap]

variable (ι) in
/-- The bijection `Z ↦ J(Z)` of the Siegel upper half space onto the `ω₀`-compatible complex
structures on `StdSpace ι` (`compatibleEquiv`), as a diffeomorphism. -/
def compatibleDiffeomorph :
    SiegelUpperHalfSpace ι ≃ₘ⟮𝓘(ℝ, 𝒮 ι), 𝓘(ℝ, (stdForm ι).compatibleModel)⟯ 𝒥₀ ι where
  toEquiv := compatibleEquiv
  contMDiff_toFun := contMDiff_compatibleEquiv
  contMDiff_invFun := contMDiff_compatibleEquiv_symm

@[simp]
theorem coe_compatibleDiffeomorph :
    ⇑(compatibleDiffeomorph ι) = compatibleEquiv :=
  (rfl)

@[simp]
theorem coe_compatibleDiffeomorph_symm :
    ⇑(compatibleDiffeomorph ι).symm = compatibleEquiv.symm :=
  (rfl)

/-- The differential of `compatibleDiffeomorph` at `Z`, read in the endomorphisms of
`StdSpace ι`, is the derivative of the block formula: `Ẑ ↦ dJ_Z(Ẑ)`. -/
theorem mfderiv_compatibleCLM_mfderiv_compatibleDiffeomorph (Z : SiegelUpperHalfSpace ι)
    (dZ : TangentSpace 𝓘(ℝ, 𝒮 ι) Z) :
    mfderiv 𝓘(ℝ, (stdForm ι).compatibleModel) 𝓘(ℝ, StdSpace ι →L[ℝ] StdSpace ι)
        (stdForm ι).compatibleCLM (compatibleDiffeomorph ι Z)
        (mfderiv 𝓘(ℝ, 𝒮 ι) 𝓘(ℝ, (stdForm ι).compatibleModel) (compatibleDiffeomorph ι) Z dZ) =
      Matrix.toEuclideanCLM (n := ι ⊕ ι) (𝕜 := ℝ)
        (complexStructureMatrixDeriv (Z : Matrix ι ι ℂ) (Subtype.val dZ)) := by
  have hZ : IsUnit ((Z : Matrix ι ι ℂ).map Complex.im).det := isUnit_det_map_im Z
  have h : HasMFDerivAt 𝓘(ℝ, 𝒮 ι) 𝓘(ℝ, StdSpace ι →L[ℝ] StdSpace ι)
      ((stdForm ι).compatibleCLM ∘ compatibleDiffeomorph ι) Z
      ((LinearMap.toContinuousLinearMap
        (Matrix.toEuclideanCLM (n := ι ⊕ ι) (𝕜 := ℝ)).toAlgEquiv.toLinearMap) ∘L
        complexStructureMatrixDeriv (Z : Matrix ι ι ℂ) ∘L
        (Submodule.subtypeL (𝒮 ι)).restrictScalars ℝ) := by
    have hfun : (stdForm ι).compatibleCLM ∘ compatibleDiffeomorph ι =
        (LinearMap.toContinuousLinearMap
          (Matrix.toEuclideanCLM (n := ι ⊕ ι) (𝕜 := ℝ)).toAlgEquiv.toLinearMap) ∘
        complexStructureMatrix ∘ ((↑) : SiegelUpperHalfSpace ι → Matrix ι ι ℂ) :=
      funext fun Z ↦ compatibleCLM_compatibleEquiv Z
    rw [hfun]
    exact (((LinearMap.toContinuousLinearMap
      (Matrix.toEuclideanCLM (n := ι ⊕ ι) (𝕜 := ℝ)).toAlgEquiv.toLinearMap).hasFDerivAt.comp _
        (hasFDerivAt_complexStructureMatrix hZ)).hasMFDerivAt.comp Z (hasMFDerivAt_coe Z))
  have hc := (SymplecticForm.contMDiff_compatibleCLM («ω» := stdForm ι) (n := 1)
    (compatibleDiffeomorph ι Z)).mdifferentiableAt one_ne_zero
  have hf := ((compatibleDiffeomorph ι).contMDiff Z).mdifferentiableAt (by simp)
  rw [← mfderiv_comp_apply Z hc hf, h.mfderiv]
  -- The tangent space at `Z` is the model `𝒮 ι` by definition; `simp` does not see
  -- through it to apply `ContinuousLinearMap.comp_apply`, so the composite is unfolded.
  rfl

/-- The diffeomorphism `Z ↦ J(Z)` is holomorphic: it intertwines multiplication by `i` on the
symmetric matrices, the complex structure of the Siegel upper half space, with the complex
structure `Ĵ ↦ -J Ĵ` of the compatible complex structures. -/
theorem isPseudoholomorphic_compatibleDiffeomorph :
    IsPseudoholomorphic (SmoothAlmostComplexStructure.ofComplexManifold (𝒮 ι) _)
      (stdForm ι).compatibleSpaceComplexStructure (compatibleDiffeomorph ι) := by
  rw [isPseudoholomorphic_iff]
  intro Z
  refine isPseudoholomorphicAt_iff_mfderiv.2
    ⟨(compatibleDiffeomorph ι).mdifferentiable (by simp) Z, fun dZ ↦ ?_⟩
  have hI := congrArg Subtype.val
    (SmoothAlmostComplexStructure.ofComplexManifold_apply (E := 𝒮 ι) Z dZ) |>.trans
      (Submodule.coe_smul_of_tower Complex.I (show 𝒮 ι from dZ))
  apply SymplecticForm.injective_mfderiv_compatibleCLM
  rw [SymplecticForm.mfderiv_compatibleCLM_compatibleSpaceComplexStructure,
    mfderiv_compatibleCLM_mfderiv_compatibleDiffeomorph,
    mfderiv_compatibleCLM_mfderiv_compatibleDiffeomorph, hI,
    complexStructureMatrixDeriv_I_smul (isUnit_det_map_im Z), map_neg, map_mul,
    coe_compatibleDiffeomorph, compatibleCLM_compatibleEquiv, ContinuousLinearMap.mul_def]

/-- The metric of the compatible complex structures pulled back to the Siegel upper half space
is Siegel's metric: at `Z = X + iY`, the square length of `Ẑ = Ẋ + iẎ` is
`tr((Y⁻¹ Ẋ)² + (Y⁻¹ Ẏ)²)`. -/
theorem inner_mfderiv_compatibleDiffeomorph (Z : SiegelUpperHalfSpace ι)
    (dZ : TangentSpace 𝓘(ℝ, 𝒮 ι) Z) :
    ⟪mfderiv 𝓘(ℝ, 𝒮 ι) 𝓘(ℝ, (stdForm ι).compatibleModel) (compatibleDiffeomorph ι) Z dZ,
      mfderiv 𝓘(ℝ, 𝒮 ι) 𝓘(ℝ, (stdForm ι).compatibleModel) (compatibleDiffeomorph ι) Z dZ⟫ =
      trace ((Z.im⁻¹ * (Subtype.val dZ).map Complex.re) ^ 2 +
        (Z.im⁻¹ * (Subtype.val dZ).map Complex.im) ^ 2) := by
  rw [SymplecticForm.inner_compatibleSpace, mfderiv_compatibleCLM_mfderiv_compatibleDiffeomorph,
    ← ContinuousLinearMap.mul_def, ← map_mul, Matrix.trace_toEuclideanCLM, im_def,
    trace_complexStructureMatrixDeriv_mul_self (isUnit_det_map_im Z)]

end SiegelUpperHalfSpace

end SymplecticGeometry

namespace TauCeti.SymplecticForm

open SymplecticGeometry Set _root_.Bundle CovariantDerivative TauCeti.Manifold
open scoped _root_.Manifold RealInnerProductSpace

attribute [local instance] TauCeti.normedAlgebraRatOfReal

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (ω : SymplecticForm V)

local notation "𝒥" => {J : AlmostComplexStructure V // ω.Compatible J}

/-- The ambient reading of tangent vectors: the differential of the inclusion `ω.compatibleCLM`. -/
local notation "dι" => mfderiv 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V) ω.compatibleCLM

local notation "∇" => leviCivitaConnection 𝓘(ℝ, ω.compatibleModel) 𝒥

/-- **The space of compatible complex structures is a Kähler manifold.** For a symplectic vector
space `(V, ω)` of dimension `2n`, the `ω`-compatible complex structures form a submanifold of
`V →L[ℝ] V` of dimension `n(n + 1)` whose tangent space at `J` is the space of `Ĵ` with
`J Ĵ + Ĵ J = 0` that are `ω`-skew-adjoint. With the complex structure `Ĵ ↦ -J Ĵ`, the closed form
`Ω(Ĵ₁, Ĵ₂) = ½ tr(Ĵ₁ J Ĵ₂)` and the metric `⟪Ĵ₁, Ĵ₂⟫ = ½ tr(Ĵ₁ Ĵ₂)`, it is a Kähler manifold whose
complex structure is integrable, and the linear symplectomorphisms act on it holomorphically,
preserving `Ω` and the metric. Its Levi-Civita connection is
`∇_t W = ∂_t W - ½ J (W J̇ + J̇ W)` along a curve; its geodesics are the curves
`t ↦ J exp(-t J Ĵ)`, defined for all time, so that it is geodesically complete and complete for
the Riemannian distance; its curvature is `R(Ĵ₁, Ĵ₂) Ĵ₃ = -¼ [[Ĵ₁, Ĵ₂], Ĵ₃]`, of nonpositive
sectional curvature. For `ω₀` on `StdSpace ι`, `Z ↦ J(Z)` is a holomorphic diffeomorphism from
the Siegel upper half space, which pulls the metric back to Siegel's metric
`tr((Y⁻¹ Ẋ)² + (Y⁻¹ Ẏ)²)`.

Milestone: *Kähler structure on the space of compatible linear complex structures*. -/
theorem isKahler_compatibleSpaceForm_and_compatibleDiffeomorph {n : ℕ}
    (hn : Module.finrank ℝ V = 2 * n) :
    Manifold.IsSmoothEmbedding 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V)
      ((⊤ : ℕ∞) : WithTop ℕ∞) ω.compatibleCLM ∧
    Module.finrank ℝ ω.compatibleModel = n * (n + 1) ∧
    (∀ J : 𝒥, LinearMap.range (dι J).toLinearMap = ω.compatibleTangentSpaceCLM J.val) ∧
    (∀ (J : 𝒥) (a : TangentSpace 𝓘(ℝ, ω.compatibleModel) J),
      dι J (ω.compatibleSpaceComplexStructure J a) = -(ω.compatibleCLM J ∘L dι J a)) ∧
    (∀ (J : 𝒥) (a b : TangentSpace 𝓘(ℝ, ω.compatibleModel) J),
      ω.compatibleSpaceForm.bilinFormAt J a b =
        2⁻¹ * LinearMap.trace ℝ V ↑(dι J a ∘L ω.compatibleCLM J ∘L dι J b)) ∧
    (∀ (J : 𝒥) (a b : TangentSpace 𝓘(ℝ, ω.compatibleModel) J),
      ⟪a, b⟫ = 2⁻¹ * LinearMap.trace ℝ V ↑(dι J a ∘L dι J b)) ∧
    ω.compatibleSpaceForm.IsKahler ω.compatibleSpaceComplexStructure ∧
    ω.compatibleSpaceComplexStructure.IsIntegrable ∧
    (∀ (Ψ : V ≃L[ℝ] V) (hΨ : ω.IsSymplectomorphism ω Ψ.toLinearEquiv),
      IsPseudoholomorphic ω.compatibleSpaceComplexStructure ω.compatibleSpaceComplexStructure
        (ω.compatibleTransport hΨ) ∧
      SmoothForm.mpullback (ω.compatibleTransport hΨ) (ω.compatibleTransport hΨ).contMDiff
        ω.compatibleSpaceForm = ω.compatibleSpaceForm ∧
      ∀ (J : 𝒥) (a b : TangentSpace 𝓘(ℝ, ω.compatibleModel) J),
        ⟪mfderiv 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, ω.compatibleModel) (ω.compatibleTransport hΨ) J a,
          mfderiv 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, ω.compatibleModel) (ω.compatibleTransport hΨ)
            J b⟫ = ⟪a, b⟫) ∧
    (∀ (γ : ℝ → 𝒥) (W : ∀ t, TangentSpace 𝓘(ℝ, ω.compatibleModel) (γ t)) (t : ℝ),
      MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ, ω.compatibleModel).tangent
        (fun r ↦ TotalSpace.mk' ω.compatibleModel (γ r) (W r)) t →
      dι (γ t) (alongCurve ∇ γ W t) =
        deriv (fun r ↦ (dι (γ r) (W r) : V →L[ℝ] V)) t -
          (2⁻¹ : ℝ) • (ω.compatibleCLM (γ t) ∘L
            (dι (γ t) (W t) ∘L deriv (ω.compatibleCLM ∘ γ) t +
              deriv (ω.compatibleCLM ∘ γ) t ∘L dι (γ t) (W t)))) ∧
    (∀ (J : 𝒥) (a : TangentSpace 𝓘(ℝ, ω.compatibleModel) J),
      IsGeodesicCurveOnFrom 𝓘(ℝ, ω.compatibleModel) (ω.compatibleGeodesic J a) univ J a ∧
      ∀ t, ω.compatibleCLM (ω.compatibleGeodesic J a t) =
        ω.compatibleCLM J * NormedSpace.exp (-(t • (ω.compatibleCLM J ∘L dι J a)))) ∧
    (∀ (J : 𝒥) (a : TangentSpace 𝓘(ℝ, ω.compatibleModel) J) (γ : ℝ → 𝒥) (s t : ℝ),
      IsGeodesicCurveOnFrom 𝓘(ℝ, ω.compatibleModel) γ (Ioo s t) J a →
        EqOn γ (ω.compatibleGeodesic J a) (Ioo s t)) ∧
    (∀ J : 𝒥, IsGeodesicallyCompleteAt 𝓘(ℝ, ω.compatibleModel) 𝒥 J) ∧
    (letI := EMetricSpace.ofRiemannianMetric 𝓘(ℝ, ω.compatibleModel) 𝒥; CompleteSpace 𝒥) ∧
    (∀ (J : 𝒥) (a b c : TangentSpace 𝓘(ℝ, ω.compatibleModel) J),
      dι J (∇.curvatureTensor J a b c) = -(4⁻¹ : ℝ) •
        ⁅⁅mvfderiv 𝓘(ℝ, ω.compatibleModel) ω.compatibleCLM J a,
          mvfderiv 𝓘(ℝ, ω.compatibleModel) ω.compatibleCLM J b⁆,
          mvfderiv 𝓘(ℝ, ω.compatibleModel) ω.compatibleCLM J c⁆) ∧
    (∀ (hcov : IsMetricCompatible (V := fun J : 𝒥 ↦ TangentSpace 𝓘(ℝ, ω.compatibleModel) J) ∇)
      (J : 𝒥) (u v : TangentSpace 𝓘(ℝ, ω.compatibleModel) J), ∇.sectionalCurvature hcov J u v ≤ 0) ∧
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι],
      (∀ Z, SiegelUpperHalfSpace.compatibleDiffeomorph ι Z =
        SiegelUpperHalfSpace.compatibleEquiv Z) ∧
      IsPseudoholomorphic (SmoothAlmostComplexStructure.ofComplexManifold
          (selfAdjointMatricesSubmodule (1 : Matrix ι ι ℂ)) _)
        (stdForm ι).compatibleSpaceComplexStructure
        (SiegelUpperHalfSpace.compatibleDiffeomorph ι) ∧
      ∀ (Z : SiegelUpperHalfSpace ι)
        (dZ : TangentSpace 𝓘(ℝ, selfAdjointMatricesSubmodule (1 : Matrix ι ι ℂ)) Z),
        ⟪mfderiv 𝓘(ℝ, selfAdjointMatricesSubmodule (1 : Matrix ι ι ℂ))
            𝓘(ℝ, (stdForm ι).compatibleModel) (SiegelUpperHalfSpace.compatibleDiffeomorph ι) Z dZ,
          mfderiv 𝓘(ℝ, selfAdjointMatricesSubmodule (1 : Matrix ι ι ℂ))
            𝓘(ℝ, (stdForm ι).compatibleModel) (SiegelUpperHalfSpace.compatibleDiffeomorph ι)
              Z dZ⟫ =
          Matrix.trace ((Z.im⁻¹ * (Subtype.val dZ).map Complex.re) ^ 2 +
            (Z.im⁻¹ * (Subtype.val dZ).map Complex.im) ^ 2) :=
  ⟨isSmoothEmbedding_compatibleCLM, finrank_compatibleModel hn, range_mfderiv_compatibleCLM,
    mfderiv_compatibleCLM_compatibleSpaceComplexStructure, compatibleSpaceForm_apply,
    inner_compatibleSpace, isKahler_compatibleSpaceForm,
    isIntegrable_compatibleSpaceComplexStructure,
    fun _ hΨ ↦ ⟨isPseudoholomorphic_compatibleTransport hΨ,
      mpullback_compatibleTransport_compatibleSpaceForm hΨ,
      fun J a b ↦ coe_compatibleTransportIsometry hΨ ▸
        (ω.compatibleTransportIsometry hΨ).inner_mfderiv J a b⟩,
    fun _ _ _ hW ↦ alongCurve_leviCivitaConnection_compatibleSpace hW,
    fun J a ↦ ⟨isGeodesicCurveOnFrom_compatibleGeodesic J a, compatibleCLM_compatibleGeodesic J a⟩,
    fun _ _ _ _ _ hγ ↦ eqOn_compatibleGeodesic hγ isPreconnected_Ioo,
    isGeodesicallyCompleteAt_compatibleSpace, completeSpace_compatibleSpace,
    curvatureTensor_leviCivitaConnection_compatibleSpace,
    sectionalCurvature_compatibleSpace_nonpos,
    fun _ _ _ ↦ ⟨fun _ ↦ rfl, SiegelUpperHalfSpace.isPseudoholomorphic_compatibleDiffeomorph,
      SiegelUpperHalfSpace.inner_mfderiv_compatibleDiffeomorph⟩⟩

end TauCeti.SymplecticForm

end
