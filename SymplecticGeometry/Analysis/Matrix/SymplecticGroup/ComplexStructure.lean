/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.LinearAlgebra.ComplexStructure.Action
public import TauCeti.Analysis.Matrix.Polar.GLSymplectic
public import TauCeti.Topology.Algebra.SymplecticGroup
public import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Basic
import SymplecticGeometry.Analysis.Matrix.Polar.Deformation
import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Matrix

/-!
# Continuous families of compatible complex structures on the standard model

Every complex structure `J` on `StdSpace ι` compatible with `ω₀ = stdForm ι` is `P • J₀` for a
symplectic matrix `P` (`exists_symplecticGroup_smul_stdComplexStructure_eq`). This file shows that
`P` can be chosen to depend continuously on `J`.

The choice is explicit. Let `M` be the matrix of `J` and `S = -J₀ M` the Gram matrix of the metric
`ω₀(·, J ·)`. Then `S` is positive definite and symplectic, and `P = S^{-1/2}` works: the
symmetric symplectic matrix `Φ = S^{1/2}` satisfies `Φ J₀ Φ = J₀`, so
`Φ⁻¹ J₀ Φ = J₀ Φ² = J₀ S = M`. The square root is the polar deformation of `S` at time `1/2`,
Tau Ceti's `TauCeti.GLSymplectic.polarHomotopy`, which is continuous and stays in the symplectic
group.

## Main results

* `SymplecticGeometry.inv_smul_stdComplexStructure_eq_of_mul_self_eq`: if a symmetric symplectic
  matrix `Φ` squares to the Gram matrix `-J₀ M` of a complex structure `J`, then `Φ⁻¹ • J₀ = J`.
* `SymplecticGeometry.exists_continuous_GLSymplectic_smul_stdComplexStructure_eq`: a family of
  `ω₀`-compatible complex structures `K x` on `StdSpace ι`, for which `ω₀(v, K x w)` depends
  continuously on `x` for all `v, w`, is `P x • J₀` for a continuous map `P` into the symplectic
  group.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.5
-/

public section

namespace SymplecticGeometry

open TauCeti Matrix
open scoped MatrixOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Let `J` be a complex structure on `StdSpace ι` with matrix `M`, and `Φ` an invertible symmetric
symplectic matrix whose square is the Gram matrix `-J₀ M` of `ω₀(·, J ·)`. Then `Φ⁻¹ • J₀ = J`,
that is, `J = Φ⁻¹ ∘ J₀ ∘ Φ`. -/
theorem inv_smul_stdComplexStructure_eq_of_mul_self_eq {Φ : GL (ι ⊕ ι) ℝ}
    (hΦ : (Φ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) ∈ symplecticGroup ι ℝ)
    (hs : (Φ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ).IsSymm) {J : AlmostComplexStructure (StdSpace ι)}
    (hJ : (Φ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) * Φ =
      -Matrix.J ι ℝ * toEuclideanLin.symm J.toLinearMap) :
    Φ⁻¹ • stdComplexStructure ι = J := by
  -- `Φ J₀ Φ = Φᵀ J₀ Φ = J₀`, hence `Φ⁻¹ J₀ Φ = J₀ Φ² = M`.
  have hΦJ : (Φ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) * Matrix.J ι ℝ * Φ = Matrix.J ι ℝ := by
    nth_rw 1 [← hs.eq]
    exact SymplecticGroup.mem_iff'.1 hΦ
  have hkey : ((Φ⁻¹ : GL (ι ⊕ ι) ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) * Matrix.J ι ℝ * Φ =
      toEuclideanLin.symm J.toLinearMap := by
    calc ((Φ⁻¹ : GL (ι ⊕ ι) ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) * Matrix.J ι ℝ * Φ
        = ((Φ⁻¹ : GL (ι ⊕ ι) ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) * (Φ * Matrix.J ι ℝ * Φ) * Φ := by
          rw [hΦJ]
      _ = Matrix.J ι ℝ * (Φ * Φ) := by
          simp only [Matrix.mul_assoc, ← Matrix.mul_assoc (Φ⁻¹ : GL (ι ⊕ ι) ℝ).val Φ.val,
            Units.inv_mul, Matrix.one_mul]
      _ = toEuclideanLin.symm J.toLinearMap := by
          rw [hJ, ← Matrix.mul_assoc, Matrix.mul_neg, J_squared, neg_neg, Matrix.one_mul]
  apply AlmostComplexStructure.ext
  rw [AlmostComplexStructure.toLinearMap_generalLinearGroup_smul,
    stdComplexStructure_eq_toEuclideanLin_J, ← LinearEquiv.apply_symm_apply toEuclideanLin
      J.toLinearMap, ← hkey]
  simp only [← coe_units_inv, inv_inv, ← toLpLin_mul_same, Matrix.mul_assoc, implies_true]

/-- **Continuous symplectic frames for compatible complex structures.** Let `K x`, for `x` in a
topological space `X`, be complex structures on `StdSpace ι` compatible with `ω₀ = stdForm ι`,
such that `ω₀(v, K x w)` depends continuously on `x` for all `v, w`. Then there is a continuous
map `P` from `X` to the symplectic group with `P x • J₀ = K x`, that is,
`K x = P x ∘ J₀ ∘ (P x)⁻¹`. -/
theorem exists_continuous_GLSymplectic_smul_stdComplexStructure_eq {X : Type*}
    [TopologicalSpace X] {K : X → AlmostComplexStructure (StdSpace ι)}
    (hK : ∀ x, (stdForm ι).Compatible (K x))
    (hcont : ∀ v w, Continuous fun x ↦ stdForm ι v (K x w)) :
    ∃ P : X → GLSymplectic ι ℝ, Continuous P ∧
      ∀ x, ((P x : GL (ι ⊕ ι) ℝ)) • stdComplexStructure ι = K x := by
  set S : X → Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ :=
    fun x ↦ -Matrix.J ι ℝ * toEuclideanLin.symm (K x).toLinearMap
  have hSpos (x : X) : (S x).PosDef := compatible_stdForm_iff_posDef.1 (hK x)
  have hSsymp (x : X) : S x ∈ symplecticGroup ι ℝ :=
    neg_J_mul_mem_symplecticGroup_of_invariant (hK x).invariant
  have hScont : Continuous S := by
    refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
    have h (x : X) : S x i j = stdForm ι (EuclideanSpace.single i 1)
        (K x (EuclideanSpace.single j 1)) := by
      rw [show S x = _ from (toMatrix_associatedBilinForm_stdForm (K x)).symm,
        LinearMap.BilinForm.toMatrix_apply, SymplecticForm.associatedBilinForm_apply]
      simp [PiLp.basisFun_apply]
    simpa only [h] using hcont _ _
  -- `S` as a continuous map into `GLSymplectic`.
  let Ss : X → GLSymplectic ι ℝ := fun x ↦
    GLSymplectic.symplecticGroupContinuousMulEquiv ι ℝ ⟨S x, hSsymp x⟩
  have hSscont : Continuous Ss :=
    (GLSymplectic.symplecticGroupContinuousMulEquiv ι ℝ).continuous.comp
      (hScont.subtype_mk hSsymp)
  have hval (x : X) : ((Ss x : GL (ι ⊕ ι) ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) = S x := by simp [Ss]
  let half : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩
  let Φ : X → GLSymplectic ι ℝ := fun x ↦ GLSymplectic.polarHomotopy (half, Ss x)
  refine ⟨fun x ↦ (Φ x)⁻¹,
    ((GLSymplectic.polarHomotopy (n := ι)).continuous.comp
      (continuous_const.prodMk hSscont)).inv, fun x ↦ ?_⟩
  -- The matrix `Φ x` is `S x ^ (1 / 2)`, which is symmetric with square `S x`.
  have hS0 : 0 ≤ S x := nonneg_iff_posSemidef.2 (hSpos x).posSemidef
  have hΦ : ((Φ x : GL (ι ⊕ ι) ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) = CFC.sqrt (S x) := by
    rw [GLSymplectic.coe_polarHomotopy_apply,
      Matrix.GeneralLinearGroup.coe_polarDeformation_of_nonneg (hval x ▸ hS0), hval,
      CFC.sqrt_eq_rpow]
    norm_num
  have hΦsymm : ((Φ x : GL (ι ⊕ ι) ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ).IsSymm := by
    rw [hΦ, ← isHermitian_iff_isSymm]
    exact (CFC.sqrt_nonneg (S x)).isSelfAdjoint
  have hΦsq : ((Φ x : GL (ι ⊕ ι) ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) *
      ((Φ x : GL (ι ⊕ ι) ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) = S x := by
    rw [hΦ, CFC.sqrt_mul_sqrt_self (S x) hS0]
  exact inv_smul_stdComplexStructure_eq_of_mul_self_eq
    (GLSymplectic.mem_iff_mem_symplecticGroup.1 (Φ x).property) hΦsymm hΦsq

end SymplecticGeometry

end
