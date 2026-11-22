/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.BoundaryDegree
public import SymplecticGeometry.Analysis.Matrix.SymplecticGroup.Maslov
public import SymplecticGeometry.Geometry.Manifold.ModelTransport.InteriorModel
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Smooth
public import TauCeti.Geometry.Manifold.Boundary.Collar.Topological

/-!
# The first Chern number through a splitting of the surface

We work in the setting of the boundary degree
(`TauCeti.HomologicalOrientation.boundaryDegree`): `X` is a compact Hausdorff space, `ι : M → X`
is an open embedding of a surface oriented by `o`, and the complement `∂X = X ∖ ι(M)` is the image
of a collared map.

The *boundary Maslov index* of a continuous map `Ψ : ∂X → Sp(2n)` is the boundary degree of
`ρ ∘ Ψ`, where `ρ = TauCeti.GLSymplectic.maslovPhase` is the complex determinant of the unitary
polar factor. When the components of `∂X` are parametrized by loops that represent the boundary
class, it adds up the Maslov indices of `Ψ` along these loops. It is additive under
pointwise products, although `ρ` is not multiplicative on `Sp(2n)`, because `ρ(A B)` and
`ρ(A) ρ(B)` are homotopic as functions of `(A, B)`
(`TauCeti.GLSymplectic.maslovPhase_mul_homotopic`). It vanishes on maps that extend continuously
over `X`, since the boundary class vanishes in the homology of `X`.

A compact surface `S` with boundary, modelled on the half-plane `EuclideanHalfSpace 2`, is a case
of this setting: `X = S`, `M` is the interior of `S` re-modelled on `ℝ²`
(`SymplecticGeometry.InteriorModel`), `ι` is its inclusion
(`SymplecticGeometry.InteriorModel.isOpenEmbedding_val`), whose range is the complement of the
boundary (`SymplecticGeometry.InteriorModel.range_val_interiorOpens`), the collared map is the
inclusion of the boundary (`TauCeti.isCollared_subtypeVal_boundary_of_compactSpace`), and the
homological orientation comes from a smooth orientation of the interior
(`TauCeti.Manifold.Orientation.toHomologicalOrientation`). In this case the boundary Maslov
index is defined for maps on the boundary `(𝓡∂ 2).boundary S` itself.

## Main definitions

* `TauCeti.HomologicalOrientation.boundaryMaslovIndex`: the boundary degree of `ρ ∘ Ψ` for
  `Ψ : ∂X → Sp(2n)`.
* `TauCeti.Manifold.Orientation.boundaryMaslovIndex`: the boundary Maslov index of a map
  `Ψ : ∂S → Sp(2n)` on a compact surface `S` with boundary, for an orientation of its interior.

## Main results

* `TauCeti.HomologicalOrientation.boundaryMaslovIndex_eq_sum`: along loops that represent the
  boundary class, the boundary Maslov index is the sum of the Maslov indices
  (`TauCeti.GLSymplectic.maslovIndex`) of `Ψ` along them.
* `TauCeti.HomologicalOrientation.boundaryMaslovIndex_mul`: the pointwise product of two maps has
  the sum of their boundary Maslov indices.
* `TauCeti.HomologicalOrientation.boundaryMaslovIndex_eq_zero_of_extend`: a map that extends
  continuously over `X` has boundary Maslov index `0`.
* `TauCeti.HomologicalOrientation.boundaryMaslovIndex_eq_of_homotopy`: homotopic maps have the
  same boundary Maslov index.
* `TauCeti.Manifold.Orientation.boundaryMaslovIndex_mul`,
  `TauCeti.Manifold.Orientation.boundaryMaslovIndex_eq_zero_of_extend`,
  `TauCeti.Manifold.Orientation.boundaryMaslovIndex_eq_of_homotopy`: the same properties for a
  compact surface with boundary.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], Section 2.7:
  Theorem 2.7.1 and Lemma 2.7.3, where the first Chern number of a bundle over a split surface is
  the degree of `ρ` along the transition map on the dividing curves.
-/

public section

noncomputable section

open Set Topology TauCeti.GLSymplectic
open scoped Manifold ContDiff

namespace TauCeti.HomologicalOrientation

variable {X M : Type} {N : Type*} [TopologicalSpace X] [TopologicalSpace N] [TopologicalSpace M]
  [T2Space X] [CompactSpace X] [T2Space M] {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [ChartedSpace E M] {ι : M → X} {f : N → X}
  {n : Type*} [Fintype n] [DecidableEq n]

variable (o : HomologicalOrientation M E 2) (hn : Module.finrank ℝ E = 2) (hι : IsOpenEmbedding ι)
  (hιf : range ι = (range f)ᶜ) (hf : IsCollared f)

/-- **The boundary Maslov index.** For a compact surface `X` with collared boundary `∂X`, the
complement of `ι(M)`, and a continuous map `Ψ : ∂X → Sp(2n)`: the boundary degree of the circle
map `ρ ∘ Ψ`, where `ρ = TauCeti.GLSymplectic.maslovPhaseMap`. -/
def boundaryMaslovIndex (Ψ : C(↥((range ι)ᶜ : Set X), GLSymplectic n ℝ)) : ℤ :=
  o.boundaryDegree hn hι hιf hf (maslovPhaseMap.comp Ψ)

theorem boundaryMaslovIndex_def (Ψ : C(↥((range ι)ᶜ : Set X), GLSymplectic n ℝ)) :
    o.boundaryMaslovIndex hn hι hιf hf Ψ =
      o.boundaryDegree hn hι hιf hf (maslovPhaseMap.comp Ψ) :=
  (rfl)

/-- Homotopic maps `∂X → Sp(2n)` have the same boundary Maslov index. -/
theorem boundaryMaslovIndex_eq_of_homotopy {Ψ Ψ' : C(↥((range ι)ᶜ : Set X), GLSymplectic n ℝ)}
    (F : Ψ.Homotopy Ψ') :
    o.boundaryMaslovIndex hn hι hιf hf Ψ = o.boundaryMaslovIndex hn hι hιf hf Ψ' := by
  obtain ⟨G⟩ := (ContinuousMap.Homotopic.refl maslovPhaseMap).comp ⟨F⟩
  rw [boundaryMaslovIndex_def, boundaryMaslovIndex_def]
  exact o.boundaryDegree_eq_of_homotopy hn hι hιf hf G

/-- Reversing the orientation negates the boundary Maslov index. -/
@[simp]
theorem boundaryMaslovIndex_neg_orientation (Ψ : C(↥((range ι)ᶜ : Set X), GLSymplectic n ℝ)) :
    (-o).boundaryMaslovIndex hn hι hιf hf Ψ = -o.boundaryMaslovIndex hn hι hιf hf Ψ := by
  simp [boundaryMaslovIndex_def]

/-- **The boundary Maslov index along loops.** Suppose that loops `γ i` in `∂X` represent the
boundary class: the sum of their classes in `H₁(∂X; ℤ)`, the push-forwards along
`(γ i).toCircle` of the generator of `Circle.singularHomologyOneIso`, is `∂[X, ∂X]`. Then the
boundary Maslov index of `Ψ` adds up the Maslov indices of the loops `Ψ ∘ γ i`. -/
theorem boundaryMaslovIndex_eq_sum {κ : Type*} [Fintype κ] {x : κ → ↥((range ι)ᶜ : Set X)}
    (γ : ∀ i, Path (x i) (x i))
    (hγ : ∑ i, (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
        (ModuleCat.of ℤ (ULift.{0} ℤ))).map (TopCat.ofHom (γ i).toCircle)).hom
          ((Circle.singularHomologyOneIso (ModuleCat.of ℤ (ULift.{0} ℤ))).inv.hom (ULift.up 1)) =
      o.boundaryClass hn hι hιf hf)
    (Ψ : C(↥((range ι)ᶜ : Set X), GLSymplectic n ℝ)) :
    o.boundaryMaslovIndex hn hι hιf hf Ψ = ∑ i, maslovIndex ((γ i).map Ψ.continuous) := by
  rw [boundaryMaslovIndex_def, o.boundaryDegree_eq_sum_degree hn hι hιf hf γ hγ]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [maslovIndex_def]
  exact Circle.degree_congr _ _ fun t ↦ by simp

/-- **The product formula.** The pointwise product of two maps `∂X → Sp(2n)` has the sum of their
boundary Maslov indices. -/
theorem boundaryMaslovIndex_mul (Ψ Ψ' : C(↥((range ι)ᶜ : Set X), GLSymplectic n ℝ)) :
    o.boundaryMaslovIndex hn hι hιf hf (Ψ * Ψ') =
      o.boundaryMaslovIndex hn hι hιf hf Ψ + o.boundaryMaslovIndex hn hι hιf hf Ψ' := by
  rw [boundaryMaslovIndex_def, boundaryMaslovIndex_def, boundaryMaslovIndex_def,
    ← o.boundaryDegree_mul]
  obtain ⟨F⟩ := maslovPhaseMap_comp_mul_homotopic Ψ Ψ'
  exact o.boundaryDegree_eq_of_homotopy hn hι hιf hf F

/-- A map `∂X → Sp(2n)` that extends continuously over `X` has boundary Maslov index `0`. -/
theorem boundaryMaslovIndex_eq_zero_of_extend {Ψ : C(↥((range ι)ᶜ : Set X), GLSymplectic n ℝ)}
    (Φ : C(X, GLSymplectic n ℝ)) (hΦ : ∀ z : ↥((range ι)ᶜ : Set X), Φ z = Ψ z) :
    o.boundaryMaslovIndex hn hι hιf hf Ψ = 0 :=
  o.boundaryDegree_eq_zero_of_extend hn hι hιf hf (maslovPhaseMap.comp Φ)
    fun z ↦ by simp [hΦ z]

/-- The constant map `1 : ∂X → Sp(2n)` has boundary Maslov index `0`. -/
@[simp]
theorem boundaryMaslovIndex_one :
    o.boundaryMaslovIndex hn hι hιf hf (1 : C(↥((range ι)ᶜ : Set X), GLSymplectic n ℝ)) = 0 :=
  o.boundaryMaslovIndex_eq_zero_of_extend hn hι hιf hf 1 fun _ ↦ rfl

/-- The pointwise inverse of a map `∂X → Sp(2n)` has the negative of its boundary Maslov
index. -/
theorem boundaryMaslovIndex_inv (Ψ : C(↥((range ι)ᶜ : Set X), GLSymplectic n ℝ)) :
    o.boundaryMaslovIndex hn hι hιf hf Ψ⁻¹ = -o.boundaryMaslovIndex hn hι hιf hf Ψ := by
  have h := o.boundaryMaslovIndex_mul hn hι hιf hf Ψ⁻¹ Ψ
  rw [inv_mul_cancel, boundaryMaslovIndex_one] at h
  lia

end TauCeti.HomologicalOrientation

/-! ### Compact surfaces with boundary -/

namespace TauCeti.Manifold.Orientation

open SymplecticGeometry

variable {S : Type} [TopologicalSpace S] [ChartedSpace (EuclideanHalfSpace 2) S]
  [IsManifold (𝓡∂ 2) 1 S] [T2Space S] [CompactSpace S] {n : Type*} [Fintype n] [DecidableEq n]
  (o : Manifold.Orientation (𝓡 2) (InteriorModel (𝓡∂ 2) ((𝓡∂ 2).interiorOpens S)) (Fin 2))

/-- **The boundary Maslov index on a compact surface with boundary.** Let `S` be a compact surface
with boundary, modelled on the half-plane, and `o` an orientation of its interior, re-modelled on
`ℝ²`. For a continuous map `Ψ : ∂S → Sp(2n)`, this is the boundary Maslov index of `Ψ` in the
setting where `X = S`, `ι` is the inclusion of the interior, oriented by `o`, and the boundary is
collared by `TauCeti.isCollared_subtypeVal_boundary_of_compactSpace`. -/
def boundaryMaslovIndex (Ψ : C((𝓡∂ 2).boundary S, GLSymplectic n ℝ)) : ℤ :=
  (o.toHomologicalOrientation finrank_euclideanSpace_fin).boundaryMaslovIndex
    finrank_euclideanSpace_fin InteriorModel.isOpenEmbedding_val
    InteriorModel.range_val_interiorOpens isCollared_subtypeVal_boundary_of_compactSpace
    (Ψ.comp (.inclusion InteriorModel.compl_range_val_interiorOpens.subset))

theorem boundaryMaslovIndex_def (Ψ : C((𝓡∂ 2).boundary S, GLSymplectic n ℝ)) :
    o.boundaryMaslovIndex Ψ =
      (o.toHomologicalOrientation finrank_euclideanSpace_fin).boundaryMaslovIndex
        finrank_euclideanSpace_fin InteriorModel.isOpenEmbedding_val
        InteriorModel.range_val_interiorOpens isCollared_subtypeVal_boundary_of_compactSpace
        (Ψ.comp (.inclusion InteriorModel.compl_range_val_interiorOpens.subset)) :=
  (rfl)

/-- Homotopic maps `∂S → Sp(2n)` have the same boundary Maslov index. -/
theorem boundaryMaslovIndex_eq_of_homotopy {Ψ Ψ' : C((𝓡∂ 2).boundary S, GLSymplectic n ℝ)}
    (F : Ψ.Homotopy Ψ') : o.boundaryMaslovIndex Ψ = o.boundaryMaslovIndex Ψ' := by
  rw [boundaryMaslovIndex_def, boundaryMaslovIndex_def]
  exact HomologicalOrientation.boundaryMaslovIndex_eq_of_homotopy _ _ _ _ _
    (F.compContinuousMap _)

/-- Reversing the orientation negates the boundary Maslov index. -/
@[simp]
theorem boundaryMaslovIndex_neg_orientation (Ψ : C((𝓡∂ 2).boundary S, GLSymplectic n ℝ)) :
    (-o).boundaryMaslovIndex Ψ = -o.boundaryMaslovIndex Ψ := by
  simp [boundaryMaslovIndex_def]

/-- **The product formula on a surface with boundary.** The pointwise product of two maps
`∂S → Sp(2n)` has the sum of their boundary Maslov indices. -/
theorem boundaryMaslovIndex_mul (Ψ Ψ' : C((𝓡∂ 2).boundary S, GLSymplectic n ℝ)) :
    o.boundaryMaslovIndex (Ψ * Ψ') = o.boundaryMaslovIndex Ψ + o.boundaryMaslovIndex Ψ' := by
  simp only [boundaryMaslovIndex_def, ContinuousMap.mul_comp,
    HomologicalOrientation.boundaryMaslovIndex_mul]

/-- A map `∂S → Sp(2n)` that extends continuously over `S` has boundary Maslov index `0`. -/
theorem boundaryMaslovIndex_eq_zero_of_extend {Ψ : C((𝓡∂ 2).boundary S, GLSymplectic n ℝ)}
    (Φ : C(S, GLSymplectic n ℝ)) (hΦ : ∀ z : (𝓡∂ 2).boundary S, Φ z = Ψ z) :
    o.boundaryMaslovIndex Ψ = 0 :=
  HomologicalOrientation.boundaryMaslovIndex_eq_zero_of_extend _ _ _ _ _ Φ fun z ↦ by
    simpa using hΦ (ContinuousMap.inclusion InteriorModel.compl_range_val_interiorOpens.subset z)

/-- The constant map `1 : ∂S → Sp(2n)` has boundary Maslov index `0`. -/
@[simp]
theorem boundaryMaslovIndex_one :
    o.boundaryMaslovIndex (1 : C((𝓡∂ 2).boundary S, GLSymplectic n ℝ)) = 0 := by
  simp [boundaryMaslovIndex_def]

/-- The pointwise inverse of a map `∂S → Sp(2n)` has the negative of its boundary Maslov
index. -/
theorem boundaryMaslovIndex_inv (Ψ : C((𝓡∂ 2).boundary S, GLSymplectic n ℝ)) :
    o.boundaryMaslovIndex Ψ⁻¹ = -o.boundaryMaslovIndex Ψ := by
  simp only [boundaryMaslovIndex_def, ContinuousMap.inv_comp,
    HomologicalOrientation.boundaryMaslovIndex_inv]

end TauCeti.Manifold.Orientation

end
