/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.LocalModel.MomentMap
public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.NormSq
public import SymplecticGeometry.LinearAlgebra.Dual.PolynomialFunctions

/-!
# The norm square of the local model's moment map

Let `D : SymplecticGeometry.LocalModelData K V A` be the data of the Marle–Guillemin–Sternberg
local model `Y = G ×_K (A × V)`, with moment map `μ_Y [g, p] = Ad*_g (ν p)`
(`TauCeti.CotangentBundle.balancedProductInducedMomentMap`), where
`ν (η, v) = τ + ι𝔪 η + ι𝔥 (μ_V v)` are the covectors `SymplecticGeometry.LocalModelData.covector`.
Fix a nondegenerate bilinear form `B` on `𝔤` and write `B^∨ = B.dualForm hB` for the form it
induces on `𝔤*`.

For an `Ad`-invariant `B`, the norm square `B^∨ (μ_Y [g, p]) (μ_Y [g, p])` does not depend on
`g`: it is `B^∨ (ν p) (ν p)`, by the `G`-invariance of the norm square of an equivariant map
(`SymplecticGeometry.momentNormSq_smul`). And for any `B`, the function
`p ↦ B^∨ (ν p) (ν p)` on `A × V` is a polynomial function (`Module.polynomialFunctions`), and
so a real polynomial in the coordinates of any finite basis of `A × V`: `ν` is the sum of a
constant, a linear map of `η` and the quadratic map `μ_V` of `v`, and `B^∨` is bilinear.
Together, the norm square of the moment map of the local model is a polynomial in the fibre
coordinates `(η, v)`.

## Main results

* `SymplecticGeometry.LocalModelData.dualForm_descendedMomentMap_mk`: for `Ad`-invariant `B`,
  `B^∨ (μ_Y [g, p]) (μ_Y [g, p]) = B^∨ (ν p) (ν p)`.
* `SymplecticGeometry.LocalModelData.dualForm_covector_mem_polynomialFunctions`: the function
  `p ↦ B^∨ (ν p) (ν p)` lies in `Module.polynomialFunctions ℝ (A × V)`.
* `SymplecticGeometry.LocalModelData.exists_mvPolynomial_eval_eq_dualForm_covector`:
  `p ↦ B^∨ (ν p) (ν p)` is a polynomial in the coordinates of any finite basis of `A × V`.

## References

* E. Lerman, *Gradient flow of the norm squared of a moment map*, Enseign. Math. 51 (2005),
  117–127, for the route through the local model.
* [V. Guillemin and S. Sternberg][GuilleminSternberg1990]
* C.-M. Marle, *Modèle d'action hamiltonienne d'un groupe de Lie sur une variété symplectique*,
  Rend. Sem. Mat. Univ. Politec. Torino 43 (1985), 227–251.
-/

public section

open TauCeti TauCeti.Lie TauCeti.CotangentBundle
open scoped Manifold ContDiff

noncomputable section

namespace SymplecticGeometry

namespace LocalModelData

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {K : Subgroup G} [IsClosed (K : Set G)] [CompactSpace K] [FiniteDimensional ℝ F]
  [ChartedSpace F K] [LieGroup 𝓘(ℝ, F) ∞ K] [ContMDiffSMul 𝓘(ℝ, F) I ∞ K G]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  (D : LocalModelData (I := I) K (F := F) V A)
  {B : LinearMap.BilinForm ℝ (GroupLieAlgebra I G)} (hB : B.Nondegenerate)

/-- For an `Ad`-invariant nondegenerate form `B` on `𝔤`, the norm square of the moment map of
the local model at `[g, p]` is that of the covector `D.covector p`:
`B^∨ (μ_Y [g, p]) (μ_Y [g, p]) = B^∨ (ν p) (ν p)`, with `B^∨ = B.dualForm hB`. -/
theorem dualForm_descendedMomentMap_mk
    (hBG : Representation.IsInvariantForm (adjointRepresentation ℝ I G) B) (g : G) (p : A × V) :
    letI := D.fiberDistribMulAction
    B.dualForm hB
        (balancedProductInducedMomentMap G D.covectorCLM_smul
          (BalancedProduct.mk K (K.toRightTranslation g) p))
        (balancedProductInducedMomentMap G D.covectorCLM_smul
          (BalancedProduct.mk K (K.toRightTranslation g) p)) =
      B.dualForm hB (D.covector p) (D.covector p) := by
  let := D.fiberDistribMulAction
  have h := momentNormSq_smul (hB := hB) hBG D.balancedProductInducedMomentMap_smul g
    (BalancedProduct.mk K (K.toRightTranslation 1) p)
  rw [BalancedProduct.smul_mk_toRightTranslation, mul_one, momentNormSq_def, momentNormSq_def,
    balancedProductInducedMomentMap_mk (g := 1), coe_covectorCLM, map_one, one_apply_eq_self] at h
  exact h

/-- The composite of the covectors `ν = D.covector` of the local model with any linear functional
on `𝔤*` is a polynomial function on `A × V`: it is the sum of a constant, a linear functional
and a quadratic form. -/
theorem apply_covector_mem_polynomialFunctions
    (ℓ : Module.Dual ℝ (Module.Dual ℝ (GroupLieAlgebra I G))) :
    (fun p ↦ ℓ (D.covector p)) ∈ Module.polynomialFunctions ℝ (A × V) := by
  -- `ν (η, v) = τ + ι𝔪 η + ι𝔥 (μ_V v)`, with `μ_V v = ½ (polarization of μ_V) v v`.
  have hν : (fun p ↦ ℓ (D.covector p)) = (algebraMap ℝ (A × V → ℝ) (ℓ D.τ) +
      ⇑(ℓ ∘ₗ D.ι𝔪 ∘ₗ LinearMap.fst ℝ A V)) +
        (1 / 2 : ℝ) • fun p ↦ ((D.σ.linearMomentMapCompPolar D.ρ).compr₂ (ℓ ∘ₗ D.ι𝔥))
          (LinearMap.snd ℝ A V p) (LinearMap.snd ℝ A V p) := by
    ext ⟨η, v⟩
    simp only [covector_def, localModelCovector_def, map_add, Pi.add_apply, Pi.smul_apply,
      Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, LinearMap.coe_comp,
      Function.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.compr₂_apply,
      SymplecticForm.linearMomentMapCompPolar_self, map_smul, smul_eq_mul]
    ring
  have hsnd (ℓ' : Module.Dual ℝ V) :
      (fun p ↦ ℓ' (LinearMap.snd ℝ A V p)) ∈ Module.polynomialFunctions ℝ (A × V) :=
    Module.comp_linearMap_mem_polynomialFunctions _ (Module.linearMap_mem_polynomialFunctions ℓ')
  rw [hν]
  exact Subalgebra.add_mem _ (Subalgebra.add_mem _ (Subalgebra.algebraMap_mem _ _)
      (Module.linearMap_mem_polynomialFunctions _))
    (Subalgebra.smul_mem _ (Module.bilin_apply_mem_polynomialFunctions _ hsnd hsnd) _)

/-- For a nondegenerate form `B` on `𝔤`, the function `p ↦ B^∨ (ν p) (ν p)` on `A × V`, with
`ν = D.covector` and `B^∨ = B.dualForm hB`, is a polynomial function on `A × V`. -/
theorem dualForm_covector_mem_polynomialFunctions :
    (fun p ↦ B.dualForm hB (D.covector p) (D.covector p)) ∈
      Module.polynomialFunctions ℝ (A × V) :=
  Module.bilin_apply_mem_polynomialFunctions _ D.apply_covector_mem_polynomialFunctions
    D.apply_covector_mem_polynomialFunctions

/-- For a nondegenerate form `B` on `𝔤` and any finite basis `b` of `A × V`, there is a real
polynomial `P` in the coordinates of `b` with `P (b.equivFun p) = B^∨ (ν p) (ν p)` for every
`p`, where `ν = D.covector` and `B^∨ = B.dualForm hB`. With
`SymplecticGeometry.LocalModelData.dualForm_descendedMomentMap_mk`, the norm square of the moment
map of the local model is this polynomial in the fibre coordinates. -/
theorem exists_mvPolynomial_eval_eq_dualForm_covector {ι : Type*} [Finite ι]
    (b : Module.Basis ι ℝ (A × V)) :
    ∃ P : MvPolynomial ι ℝ, ∀ p, MvPolynomial.eval (b.equivFun p) P =
      B.dualForm hB (D.covector p) (D.covector p) :=
  b.mem_polynomialFunctions_iff.1 (D.dualForm_covector_mem_polynomialFunctions hB)

end LocalModelData

end SymplecticGeometry

end
