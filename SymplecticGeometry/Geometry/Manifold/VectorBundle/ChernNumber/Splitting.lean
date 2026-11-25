/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.BoundaryDegree
public import SymplecticGeometry.Analysis.Matrix.SymplecticGroup.Maslov
public import SymplecticGeometry.Geometry.Manifold.Boundary.Interior
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.ChernNumber.Basic
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Section.ArgumentPrinciple
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Symplectic.ComplexStructure.UnitaryFrame
public import SymplecticGeometry.Topology.VectorBundle.Complex.FirstChernClass
public import SymplecticGeometry.Topology.VectorBundle.Determinant
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Smooth
public import TauCeti.Analysis.Complex.NormalizedDeterminant
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
of this setting: `X = S`, `M` is Tau Ceti's charted interior `(𝓡∂ 2).interior S` over `ℝ²`,
`ι` is its inclusion, an open embedding
(`ModelWithCorners.isOpen_interior_of_finiteDimensional`) whose range is the complement of the
boundary (`ModelWithCorners.range_subtypeVal_interior`), the collared map is the
inclusion of the boundary (`TauCeti.isCollared_subtypeVal_boundary_of_compactSpace`), and the
homological orientation comes from a smooth orientation of the interior
(`TauCeti.Manifold.Orientation.toHomologicalOrientation`). In this case the boundary Maslov
index is defined for maps on the boundary `(𝓡∂ 2).boundary S` itself.

A smooth `g : M → ℝ` with regular value `0` on a closed oriented surface `M` gives an instance of
this setting: `X = Σ₁ = {g ≤ 0}`, with interior `{g < 0}`
(`SymplecticGeometry.range_inclusion_preimage_Iio`) and collared boundary the level set `g⁻¹(0)`
(`SymplecticGeometry.isCollared_inclusion_levelSet`). For a complex vector bundle `E` over `M`
with a frame `Φ₁` over `Σ₁` and a frame `Φ₂` over `Σ₂ = {g ≥ 0}`, the first Chern number of `E`
is the boundary degree on `Σ₁` of the normalized complex determinant of the transition
`Φ₁⁻¹ ∘ Φ₂` (`SymplecticGeometry.Bundle.chernNumber_eq_boundaryDegree_normalizedDet`). Indeed the
determinant sections of the two frames (`SymplecticGeometry.Bundle.detCoreFrameSection`) are
nowhere-zero sections of the determinant line over `Σ₁` and over `Σ₂`, and on `g⁻¹(0)` the second
is the first times the determinant of the transition
(`SymplecticGeometry.Bundle.detCoreFrameSection_eq_det_smul`). The first Chern class is the Euler
class of the determinant line, so the argument principle on a split surface
(`TauCeti.VectorBundleOrientation.evalFundamentalClass_complexEulerClass_eq_boundaryDegree`)
gives the formula. The step on `g⁻¹(0)` follows the proof of the private lemma
`outSection_boundaryCircle` of `ChernNumber/Clutching.lean`, which does the same on the boundary
circles of coordinate discs.

For a two-form `σ` on a vector bundle `V`, with symplectic frames `Φ₁` over `Σ₁` and `Φ₂` over
`Σ₂` and a map `Ψ` from `g⁻¹(0)` to `Sp(2n)` with `Φ₂ = Φ₁ ∘ Ψ`, the first Chern number of
`(V, σ)` is the boundary Maslov index of `Ψ` on `Σ₁`
(`SymplecticGeometry.Bundle.symplecticChernNumber_eq_boundaryMaslovIndex`). The proof is that of
`SymplecticGeometry.Bundle.symplecticChernNumber_eq_sum_maslovIndex_clutching` in
`ChernNumber/Clutching.lean`, with the complex splitting formula in place of the clutching one.
The frames give a complex structure `J` compatible with `σ`, and changes of frame `P` over `Σ₁` and
`P'` over `Σ₂`, with values in `Sp(2n)`, turn them into complex frames of `(V, J)`, whose
transition on `g⁻¹(0)` has `ρ(P⁻¹ Ψ P')` as normalized determinant. By the product formula the
index of `P⁻¹ Ψ P'` is the sum of those of `P⁻¹`, `Ψ` and `P'`. The first vanishes as `P⁻¹` is
defined on all of `Σ₁`, and the last as `P'` is defined on all of `Σ₂`
(`TauCeti.HomologicalOrientation.sublevelBoundaryMaslovIndex_eq_zero_of_extend_Ici`, from the
argument principle for the trivial line bundle,
`TauCeti.HomologicalOrientation.sublevelBoundaryDegree_eq_zero_of_extend_Ici`).

## Main definitions

* `TauCeti.HomologicalOrientation.boundaryMaslovIndex`: the boundary degree of `ρ ∘ Ψ` for
  `Ψ : ∂X → Sp(2n)`.
* `TauCeti.Manifold.Orientation.boundaryMaslovIndex`: the boundary Maslov index of a map
  `Ψ : ∂S → Sp(2n)` on a compact surface `S` with boundary, for an orientation of its interior.
* `TauCeti.HomologicalOrientation.sublevelBoundaryMaslovIndex`: the boundary Maslov index on
  `Σ₁ = {g ≤ 0}` of a map from its boundary to `Sp(2n)`, for a smooth `g` with regular value `0`
  on a closed oriented surface.

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
* `TauCeti.HomologicalOrientation.boundaryMaslovIndex_comp_homeomorph`: invariance under a
  homeomorphism of the setting that restricts to a homeomorphism `φ` of the interiors, for the
  pulled-back orientation `o'.comap φ`.
* `TauCeti.HomologicalOrientation.boundaryMaslovIndex_reindex`: reindexing the matrices keeps the
  boundary Maslov index.
* `TauCeti.Manifold.Orientation.boundaryMaslovIndex_mul`,
  `TauCeti.Manifold.Orientation.boundaryMaslovIndex_eq_zero_of_extend`,
  `TauCeti.Manifold.Orientation.boundaryMaslovIndex_eq_of_homotopy`: the same properties for a
  compact surface with boundary; `TauCeti.Manifold.Orientation.boundaryMaslovIndex_reindex`:
  reindexing the matrices keeps the index.
* `TauCeti.HomologicalOrientation.sublevelBoundaryMaslovIndex_mul`,
  `TauCeti.HomologicalOrientation.sublevelBoundaryMaslovIndex_eq_of_homotopy`,
  `TauCeti.HomologicalOrientation.sublevelBoundaryMaslovIndex_eq_zero_of_extend_Iic`: the product
  formula, homotopy invariance and the vanishing for maps that extend over `Σ₁`, on a split closed
  surface.
* `TauCeti.HomologicalOrientation.sublevelBoundaryMaslovIndex_eq_zero_of_extend_Ici`: on a split
  closed surface, a map on `g⁻¹(0)` that extends continuously over `Σ₂` has boundary Maslov index
  `0` on `Σ₁`.
* `SymplecticGeometry.Bundle.chernNumber_eq_boundaryDegree_normalizedDet`: the first Chern number
  of a complex bundle with frames over the two sides of a splitting is the boundary degree of the
  normalized determinant of the transition.
* `SymplecticGeometry.Bundle.symplecticChernNumber_eq_boundaryMaslovIndex`: the first Chern number
  of a symplectic bundle with symplectic frames over the two sides of a splitting is the boundary
  Maslov index of the transition.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], Section 2.7:
  Theorem 2.7.1 and Lemma 2.7.3, where the first Chern number of a bundle over a split surface is
  the degree of `ρ` along the transition map on the dividing curves.
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §14: the first Chern class through the determinant line.
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

/-- Reindexing a map `∂X → Sp(2n)` along an equivalence of index types keeps its boundary Maslov
index. -/
@[simp]
theorem boundaryMaslovIndex_reindex {κ : Type*} [Fintype κ] [DecidableEq κ] (e : n ≃ κ)
    (Ψ : C(↥((range ι)ᶜ : Set X), GLSymplectic n ℝ)) :
    o.boundaryMaslovIndex hn hι hιf hf
        ((reindexContinuousMulEquiv ℝ e : C(GLSymplectic n ℝ, GLSymplectic κ ℝ)).comp Ψ) =
      o.boundaryMaslovIndex hn hι hιf hf Ψ := by
  rw [boundaryMaslovIndex_def, boundaryMaslovIndex_def]
  congr 1
  ext1 z
  simp

/-- **Boundary Maslov indices under homeomorphisms.** Let `h : X ≃ₜ X'` and `φ : M ≃ₜ M'` be
homeomorphisms with `h ∘ ι = ι' ∘ φ`, for two instances of the setting of the boundary Maslov
index, and let `g : ∂X → ∂X'` be the restriction of `h`. For an orientation `o'` of `M'` and every
`Ψ : ∂X' → Sp(2n)`, the boundary Maslov index of `Ψ ∘ g` for the pull-back `o'.comap φ` is the
boundary Maslov index of `Ψ` for `o'`. -/
theorem boundaryMaslovIndex_comp_homeomorph {X' M' : Type} {N' : Type*} [TopologicalSpace X']
    [TopologicalSpace N'] [TopologicalSpace M'] [T2Space X'] [CompactSpace X'] [T2Space M']
    [ChartedSpace E M'] {ι' : M' → X'} {f' : N' → X'} (o' : HomologicalOrientation M' E 2)
    (hι' : IsOpenEmbedding ι') (hιf' : range ι' = (range f')ᶜ) (hf' : IsCollared f')
    (h : X ≃ₜ X') (φ : M ≃ₜ M') (hφ : h ∘ ι = ι' ∘ φ)
    (g : C(↥((range ι)ᶜ : Set X), ↥((range ι')ᶜ : Set X'))) (hg : ∀ z, (g z : X') = h z)
    (Ψ : C(↥((range ι')ᶜ : Set X'), GLSymplectic n ℝ)) :
    (o'.comap φ.isOpenEmbedding).boundaryMaslovIndex hn hι hιf hf (Ψ.comp g) =
      o'.boundaryMaslovIndex hn hι' hιf' hf' Ψ := by
  rw [boundaryMaslovIndex_def, boundaryMaslovIndex_def, ← ContinuousMap.comp_assoc]
  exact boundaryDegree_comp_homeomorph hn hι hιf hf o' hι' hιf' hf' h φ hφ g hg _

end TauCeti.HomologicalOrientation

/-! ### Compact surfaces with boundary -/

namespace TauCeti.Manifold.Orientation

open SymplecticGeometry

variable {S : Type} [TopologicalSpace S] [ChartedSpace (EuclideanHalfSpace 2) S]
  [IsManifold (𝓡∂ 2) 1 S] [T2Space S] [CompactSpace S] {n : Type*} [Fintype n] [DecidableEq n]
  (o : Manifold.Orientation (𝓡 2) ((𝓡∂ 2).interior S) (Fin 2))

/-- **The boundary Maslov index on a compact surface with boundary.** Let `S` be a compact surface
with boundary, modelled on the half-plane, and `o` an orientation of its interior, re-modelled on
`ℝ²`. For a continuous map `Ψ : ∂S → Sp(2n)`, this is the boundary Maslov index of `Ψ` in the
setting where `X = S`, `ι` is the inclusion of the interior, oriented by `o`, and the boundary is
collared by `TauCeti.isCollared_subtypeVal_boundary_of_compactSpace`. -/
def boundaryMaslovIndex (Ψ : C((𝓡∂ 2).boundary S, GLSymplectic n ℝ)) : ℤ :=
  (o.toHomologicalOrientation finrank_euclideanSpace_fin).boundaryMaslovIndex
    finrank_euclideanSpace_fin
    ((𝓡∂ 2).isOpen_interior_of_finiteDimensional S).isOpenEmbedding_subtypeVal
    (𝓡∂ 2).range_subtypeVal_interior isCollared_subtypeVal_boundary_of_compactSpace
    (Ψ.comp (.inclusion (𝓡∂ 2).compl_range_subtypeVal_interior.subset))

theorem boundaryMaslovIndex_def (Ψ : C((𝓡∂ 2).boundary S, GLSymplectic n ℝ)) :
    o.boundaryMaslovIndex Ψ =
      (o.toHomologicalOrientation finrank_euclideanSpace_fin).boundaryMaslovIndex
        finrank_euclideanSpace_fin
        ((𝓡∂ 2).isOpen_interior_of_finiteDimensional S).isOpenEmbedding_subtypeVal
        (𝓡∂ 2).range_subtypeVal_interior isCollared_subtypeVal_boundary_of_compactSpace
        (Ψ.comp (.inclusion (𝓡∂ 2).compl_range_subtypeVal_interior.subset)) :=
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
    simpa using hΦ (ContinuousMap.inclusion (𝓡∂ 2).compl_range_subtypeVal_interior.subset z)

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

/-- Reindexing a map `∂S → Sp(2n)` along an equivalence of index types keeps its boundary Maslov
index. -/
@[simp]
theorem boundaryMaslovIndex_reindex {κ : Type*} [Fintype κ] [DecidableEq κ] (e : n ≃ κ)
    (Ψ : C((𝓡∂ 2).boundary S, GLSymplectic n ℝ)) :
    o.boundaryMaslovIndex
        ((reindexContinuousMulEquiv ℝ e : C(GLSymplectic n ℝ, GLSymplectic κ ℝ)).comp Ψ) =
      o.boundaryMaslovIndex Ψ := by
  simp only [boundaryMaslovIndex_def, ContinuousMap.comp_assoc,
    HomologicalOrientation.boundaryMaslovIndex_reindex]

end TauCeti.Manifold.Orientation

/-! ### Split surfaces -/

namespace TauCeti.HomologicalOrientation

open SymplecticGeometry

variable {EM : Type} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [FiniteDimensional ℝ EM]
  {M : Type} [TopologicalSpace M] [ChartedSpace EM M] [T2Space M] [CompactSpace M]
  [IsManifold 𝓘(ℝ, EM) ∞ M] {g : M → ℝ} {n : Type*} [Fintype n] [DecidableEq n]
  (oM : HomologicalOrientation M EM 2) (hn : Module.finrank ℝ EM = 2)
  (hg : ContMDiff 𝓘(ℝ, EM) 𝓘(ℝ) ∞ g) (h0 : IsRegularValue 𝓘(ℝ, EM) 𝓘(ℝ) g 0)

/-- **The boundary Maslov index on a sublevel set.** Let `M` be a closed smooth surface oriented
by `oM`, and `g : M → ℝ` smooth with regular value `0`. For a continuous `Ψ` from the boundary
`sublevelBoundary` of `{g ≤ 0}` to `Sp(2n)`, this is the boundary Maslov index of `Ψ` on the
compact surface `{g ≤ 0}`, whose interior `{g < 0}` carries the orientation restricted from `oM`
and whose boundary is collared by `SymplecticGeometry.isCollared_inclusion_levelSet`. -/
def sublevelBoundaryMaslovIndex (Ψ : C(↥(sublevelBoundary hg.continuous), GLSymplectic n ℝ)) :
    ℤ :=
  haveI := compactSpace_preimage_Iic hg.continuous
  (oM.comap (TopologicalSpace.Opens.isOpenEmbedding' _)).boundaryMaslovIndex hn
    (isOpenEmbedding_inclusion_preimage_Iio hg.continuous)
    (range_inclusion_preimage_Iio hg.continuous) (isCollared_inclusion_levelSet hg h0) Ψ

theorem sublevelBoundaryMaslovIndex_def
    (Ψ : C(↥(sublevelBoundary hg.continuous), GLSymplectic n ℝ)) :
    haveI := compactSpace_preimage_Iic hg.continuous
    oM.sublevelBoundaryMaslovIndex hn hg h0 Ψ =
      (oM.comap (TopologicalSpace.Opens.isOpenEmbedding' _)).boundaryMaslovIndex hn
        (isOpenEmbedding_inclusion_preimage_Iio hg.continuous)
        (range_inclusion_preimage_Iio hg.continuous) (isCollared_inclusion_levelSet hg h0) Ψ :=
  (rfl)

/-- The boundary Maslov index of `Ψ` on `{g ≤ 0}` is the boundary degree there of `ρ ∘ Ψ`, where
`ρ = TauCeti.GLSymplectic.maslovPhase`. -/
theorem sublevelBoundaryMaslovIndex_eq_sublevelBoundaryDegree
    (Ψ : C(↥(sublevelBoundary hg.continuous), GLSymplectic n ℝ)) :
    oM.sublevelBoundaryMaslovIndex hn hg h0 Ψ =
      oM.sublevelBoundaryDegree hn hg h0 (maslovPhaseMap.comp Ψ) := by
  have := compactSpace_preimage_Iic hg.continuous
  rw [sublevelBoundaryMaslovIndex_def, sublevelBoundaryDegree_def, boundaryMaslovIndex_def]

/-- The pointwise product of two maps from the boundary of `{g ≤ 0}` to `Sp(2n)` has the sum of
their boundary Maslov indices on `{g ≤ 0}`. -/
theorem sublevelBoundaryMaslovIndex_mul
    (Ψ Ψ' : C(↥(sublevelBoundary hg.continuous), GLSymplectic n ℝ)) :
    oM.sublevelBoundaryMaslovIndex hn hg h0 (Ψ * Ψ') =
      oM.sublevelBoundaryMaslovIndex hn hg h0 Ψ + oM.sublevelBoundaryMaslovIndex hn hg h0 Ψ' := by
  have := compactSpace_preimage_Iic hg.continuous
  simp only [sublevelBoundaryMaslovIndex_def, boundaryMaslovIndex_mul]

/-- Homotopic maps from the boundary of `{g ≤ 0}` to `Sp(2n)` have the same boundary Maslov
index on `{g ≤ 0}`. -/
theorem sublevelBoundaryMaslovIndex_eq_of_homotopy
    {Ψ Ψ' : C(↥(sublevelBoundary hg.continuous), GLSymplectic n ℝ)} (F : Ψ.Homotopy Ψ') :
    oM.sublevelBoundaryMaslovIndex hn hg h0 Ψ = oM.sublevelBoundaryMaslovIndex hn hg h0 Ψ' := by
  have := compactSpace_preimage_Iic hg.continuous
  rw [sublevelBoundaryMaslovIndex_def, sublevelBoundaryMaslovIndex_def]
  exact boundaryMaslovIndex_eq_of_homotopy _ _ _ _ _ F

/-- A map from the boundary of `{g ≤ 0}` to `Sp(2n)` that is the restriction of a continuous map
`Φ : {g ≤ 0} → Sp(2n)` has boundary Maslov index `0` on `{g ≤ 0}`. -/
theorem sublevelBoundaryMaslovIndex_eq_zero_of_extend_Iic
    {Ψ : C(↥(sublevelBoundary hg.continuous), GLSymplectic n ℝ)}
    (Φ : C(g ⁻¹' Iic 0, GLSymplectic n ℝ))
    (hΦ : ∀ z : ↥(sublevelBoundary hg.continuous), Φ z = Ψ z) :
    oM.sublevelBoundaryMaslovIndex hn hg h0 Ψ = 0 := by
  rw [sublevelBoundaryMaslovIndex_eq_sublevelBoundaryDegree]
  exact oM.sublevelBoundaryDegree_eq_zero_of_extend_Iic hn hg h0 (maslovPhaseMap.comp Φ)
    fun z ↦ by rw [ContinuousMap.comp_apply, ContinuousMap.comp_apply, hΦ]

/-- Let `M` be a closed smooth surface oriented by `oM`, and `g : M → ℝ` smooth with regular
value `0`, splitting `M` into `Σ₁ = {g ≤ 0}` and `Σ₂ = {g ≥ 0}`. A map `Ψ` from the boundary of
`Σ₁` to `Sp(2n)` that is the restriction of a continuous map `Φ : Σ₂ → Sp(2n)` has boundary
Maslov index `0` on `Σ₁`, whose interior `{g < 0}` carries the orientation restricted from
`oM`. -/
theorem sublevelBoundaryMaslovIndex_eq_zero_of_extend_Ici
    {Ψ : C(↥(sublevelBoundary hg.continuous), GLSymplectic n ℝ)}
    (Φ : C(g ⁻¹' Ici 0, GLSymplectic n ℝ))
    (hΦ : ∀ z, Φ ⟨_, mem_preimage_Ici_of_mem_sublevelBoundary z.property⟩ = Ψ z) :
    oM.sublevelBoundaryMaslovIndex hn hg h0 Ψ = 0 := by
  rw [sublevelBoundaryMaslovIndex_eq_sublevelBoundaryDegree]
  exact oM.sublevelBoundaryDegree_eq_zero_of_extend_Ici hn hg h0 (maslovPhaseMap.comp Φ)
    fun z ↦ by rw [ContinuousMap.comp_apply, ContinuousMap.comp_apply, hΦ]

end TauCeti.HomologicalOrientation

/-! ### The splitting formula for complex frames -/

namespace SymplecticGeometry.Bundle

open _root_.Bundle Module TauCeti
open scoped Manifold ContDiff

variable {EM : Type} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [FiniteDimensional ℝ EM]
  {M : Type} [TopologicalSpace M] [ChartedSpace EM M] [T2Space M] [CompactSpace M]
  [IsManifold 𝓘(ℝ, EM) ∞ M] {g : M → ℝ}
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)] [∀ x, TopologicalSpace (E x)]
  [TopologicalSpace (TotalSpace G E)] [FiberBundle G E] [VectorBundle ℂ G E]

/-- **The splitting formula for the first Chern number.** Let `M` be a closed smooth surface
oriented by `oM`, and `g : M → ℝ` smooth with regular value `0`, splitting `M` into
`Σ₁ = {g ≤ 0}` and `Σ₂ = {g ≥ 0}`. Let `E` be a complex vector bundle over `M` with model `G`,
`Φ₁` a frame of `E` over `Σ₁` and `Φ₂` a frame over `Σ₂` (continuous families of isomorphisms
`G ≃L[ℂ] E x`). Then the first Chern number of `E` is the boundary degree on `Σ₁`, whose interior
`{g < 0}` carries the orientation restricted from `oM`, of any continuous `u` from the boundary
`Σ₁ ∖ {g < 0}` of `Σ₁` to the circle equal there to the normalized complex determinant of the
transition `(Φ₁ x)⁻¹ ∘ Φ₂ x`. -/
theorem chernNumber_eq_boundaryDegree_normalizedDet
    (oM : HomologicalOrientation M EM 2) (hn : finrank ℝ EM = 2)
    (hg : ContMDiff 𝓘(ℝ, EM) 𝓘(ℝ) ∞ g) (h0 : IsRegularValue 𝓘(ℝ, EM) 𝓘(ℝ) g 0)
    {Φ₁ : ∀ x : g ⁻¹' Iic 0, G ≃L[ℂ] E x}
    (hΦ₁ : Continuous fun q : g ⁻¹' Iic 0 × G ↦ TotalSpace.mk' G (q.1 : M) (Φ₁ q.1 q.2))
    {Φ₂ : ∀ x : g ⁻¹' Ici 0, G ≃L[ℂ] E x}
    (hΦ₂ : Continuous fun q : g ⁻¹' Ici 0 × G ↦ TotalSpace.mk' G (q.1 : M) (Φ₂ q.1 q.2))
    {u : C(↥(sublevelBoundary hg.continuous), Circle)}
    (hu : ∀ (z : ↥(sublevelBoundary hg.continuous))
      (hz : ((z : g ⁻¹' Iic 0) : M) ∈ g ⁻¹' Ici 0),
      u z = ((Φ₂ ⟨_, hz⟩).trans (Φ₁ z).symm).normalizedDet) :
    chernNumber oM hn G E = oM.sublevelBoundaryDegree hn hg h0 u := by
  let i₁ : C(g ⁻¹' Iic 0, M) := ⟨Subtype.val, continuous_subtypeVal⟩
  let i₂ : C(g ⁻¹' Ici 0, M) := ⟨Subtype.val, continuous_subtypeVal⟩
  let j₁ : C(↥(sublevelBoundary hg.continuous), g ⁻¹' Iic 0) :=
    ⟨Subtype.val, continuous_subtypeVal⟩
  let j₂ : C(↥(sublevelBoundary hg.continuous), g ⁻¹' Ici 0) :=
    ⟨fun z ↦ ⟨_, mem_preimage_Ici_of_mem_sublevelBoundary z.property⟩,
      (continuous_subtypeVal.comp continuous_subtypeVal).subtype_mk _⟩
  have hΦ₁j : Continuous fun q : _ × G ↦ TotalSpace.mk' G (i₁ (j₁ q.1)) (Φ₁ (j₁ q.1) q.2) :=
    hΦ₁.comp ((j₁.continuous.comp continuous_fst).prodMk continuous_snd)
  have hΦ₂j : Continuous fun q : _ × G ↦ TotalSpace.mk' G (i₂ (j₂ q.1)) (Φ₂ (j₂ q.1) q.2) :=
    hΦ₂.comp ((j₂.continuous.comp continuous_fst).prodMk continuous_snd)
  -- On the boundary, the determinant section of `Φ₂` is that of `Φ₁` times the determinant of
  -- the transition.
  have hsc : ∀ z : ↥(sublevelBoundary hg.continuous),
      detCoreFrameSection i₂ Φ₂ hΦ₂ (j₂ z) =
        LinearMap.det ((Φ₁ (j₁ z)).symm.trans (Φ₂ (j₂ z)) : E (z : M) →ₗ[ℂ] E (z : M)) •
          detCoreFrameSection i₁ Φ₁ hΦ₁ (j₁ z) := by
    intro z
    have h1 := detCoreFrameSection_comp i₁ hΦ₁ j₁ hΦ₁j z
    have h2 := detCoreFrameSection_comp i₂ hΦ₂ j₂ hΦ₂j z
    have h3 := detCoreFrameSection_eq_det_smul (i₁.comp j₁) (Φ := fun z ↦ Φ₁ (j₁ z))
      (Ψ := fun z ↦ Φ₂ (j₂ z)) hΦ₁j hΦ₂j z
    -- The restrictions of `Φ₁` and `Φ₂` to the boundary are frames along the same map, read
    -- once through `{g ≤ 0}` and once through `{g ≥ 0}`: `i₂ ∘ j₂` and `i₁ ∘ j₁` agree by
    -- definition.
    exact h2.symm.trans (h3.trans (congrArg _ h1))
  rw [chernNumber_def, firstChernClass_def]
  refine VectorBundleOrientation.evalFundamentalClass_complexEulerClass_eq_boundaryDegree
    (finrank_detCore ℂ G E) oM hn hg h0
    (σ := detCoreFrameSection i₁ Φ₁ hΦ₁) (continuous_totalSpaceMk_detCoreFrameSection i₁ hΦ₁)
    (detCoreFrameSection_ne_zero i₁ hΦ₁)
    (s := detCoreFrameSection i₂ Φ₂ hΦ₂) (continuous_totalSpaceMk_detCoreFrameSection i₂ hΦ₂)
    (detCoreFrameSection_ne_zero i₂ hΦ₂) (fun z _ ↦ hsc z) fun z ↦ ?_
  rw [hu z (mem_preimage_Ici_of_mem_sublevelBoundary z.property),
    ContinuousLinearEquiv.coe_normalizedDet, ← ContinuousLinearEquiv.det_coe_trans_symm]
  simp only [j₁, j₂, ContinuousMap.coe_mk]

/-! ### The splitting formula for symplectic frames -/

section Symplectic

open Matrix

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V] {n : ℕ∞}
  [ContMDiffVectorBundle n F V 𝓘(ℝ, EM)] {σ : ContMDiffTwoForm 𝓘(ℝ, EM) n F V}
  {κ : Type*} [Fintype κ] [DecidableEq κ]

variable (G) in
/-- **The splitting formula for symplectic frames.** Let `M` be a closed smooth surface oriented
by `oM`, and `g : M → ℝ` smooth with regular value `0`, splitting `M` into `Σ₁ = {g ≤ 0}` and
`Σ₂ = {g ≥ 0}`. Let `σ` be a two-form on a smooth vector bundle `V` over `M`, and `Φ₁`, `Φ₂`
symplectic frames of `V` over `Σ₁` and over `Σ₂`: linear isomorphisms `StdSpace κ ≃ V x`,
continuous as maps to the total space, with `σ(Φ v, Φ w) = σ₀(v, w)` for the standard form
`σ₀ = stdForm κ`. Let `Ψ` be a continuous map from the boundary of `Σ₁` to the symplectic group
with `Φ₂ = Φ₁ ∘ Ψ` there. Then the first Chern number of `(V, σ)` is the boundary Maslov index
of `Ψ` on `Σ₁`, whose interior `{g < 0}` carries the orientation restricted from `oM`.

Milestone: *First Chern number of symplectic vector bundles over surfaces*. -/
theorem symplecticChernNumber_eq_boundaryMaslovIndex
    [Fact (finrank ℝ F = 2 * finrank ℂ G)]
    (oM : HomologicalOrientation M EM 2) (hn : finrank ℝ EM = 2)
    (hg : ContMDiff 𝓘(ℝ, EM) 𝓘(ℝ) ∞ g) (h0 : IsRegularValue 𝓘(ℝ, EM) 𝓘(ℝ) g 0)
    {Φ₁ : ∀ x : g ⁻¹' Iic 0, StdSpace κ ≃L[ℝ] V x}
    (hΦ₁ : Continuous fun q : g ⁻¹' Iic 0 × StdSpace κ ↦
      TotalSpace.mk' F (q.1 : M) (Φ₁ q.1 q.2))
    (hΦ₁σ : ∀ (x : g ⁻¹' Iic 0) v w, σ.bilinFormAt x (Φ₁ x v) (Φ₁ x w) = stdForm κ v w)
    {Φ₂ : ∀ x : g ⁻¹' Ici 0, StdSpace κ ≃L[ℝ] V x}
    (hΦ₂ : Continuous fun q : g ⁻¹' Ici 0 × StdSpace κ ↦
      TotalSpace.mk' F (q.1 : M) (Φ₂ q.1 q.2))
    (hΦ₂σ : ∀ (x : g ⁻¹' Ici 0) v w, σ.bilinFormAt x (Φ₂ x v) (Φ₂ x w) = stdForm κ v w)
    (Ψ : C(↥(sublevelBoundary hg.continuous), GLSymplectic κ ℝ))
    (hΨ : ∀ (z : ↥(sublevelBoundary hg.continuous)) v,
      Φ₂ ⟨_, mem_preimage_Ici_of_mem_sublevelBoundary z.property⟩ v =
      Φ₁ z (toEuclideanLin (Ψ z : GL (κ ⊕ κ) ℝ) v)) :
    symplecticChernNumber oM hn G σ = oM.sublevelBoundaryMaslovIndex hn hg h0 Ψ := by
  -- Every fibre carries one of the symplectic frames.
  have hframe (x : M) : ∃ Θ : StdSpace κ ≃L[ℝ] V x,
      ∀ v w, σ.bilinFormAt x (Θ v) (Θ w) = stdForm κ v w := by
    by_cases hx : g x ≤ 0
    · exact ⟨Φ₁ ⟨x, hx⟩, hΦ₁σ ⟨x, hx⟩⟩
    · exact ⟨Φ₂ ⟨x, (not_le.1 hx).le⟩, hΦ₂σ ⟨x, (not_le.1 hx).le⟩⟩
  rcases isEmpty_or_nonempty M with hM | hM
  · -- Over the empty surface any frames will do.
    obtain ⟨J, hJ⟩ := (ContMDiffTwoForm.isNondegenerate_of_forall_exists (stdForm κ)
      fun x ↦ (hframe x).elim fun Θ hΘ ↦ ⟨Θ.toLinearEquiv, hΘ⟩).exists_compatible
    rw [HomologicalOrientation.sublevelBoundaryMaslovIndex_eq_sublevelBoundaryDegree,
      symplecticChernNumber_eq_chernNumber oM hn G hJ.tames]
    exact chernNumber_eq_boundaryDegree_normalizedDet oM hn hg h0
      (Φ₁ := fun x ↦ isEmptyElim (x : M)) (Φ₂ := fun x ↦ isEmptyElim (x : M))
      continuous_of_discreteTopology continuous_of_discreteTopology
      fun z ↦ isEmptyElim ((z : g ⁻¹' Iic 0) : M)
  -- Otherwise `σ` is compatible with some `J`, and `κ → ℂ` is a complex model of `(V, J)`.
  obtain ⟨J, _, hJ, hJσ⟩ := exists_compatible_symplecticChernNumber_eq_chernNumber oM hn G hframe
  -- Complex frames of `(V, J)` from the symplectic frames, by changes of frame `P` and `P'`.
  obtain ⟨P, Θ₁, hP, hΘ₁, hΘ₁Φ⟩ :=
    hJ.exists_continuous_GLSymplectic_complexFrame (f := ((↑) : g ⁻¹' Iic 0 → M)) hΦ₁ hΦ₁σ
  obtain ⟨P', Θ₂, hP', hΘ₂, hΘ₂Φ⟩ :=
    hJ.exists_continuous_GLSymplectic_complexFrame (f := ((↑) : g ⁻¹' Ici 0 → M)) hΦ₂ hΦ₂σ
  -- On the boundary the new transition is `P⁻¹ Ψ P'`.
  let Pinv : C(↥(sublevelBoundary hg.continuous), GLSymplectic κ ℝ) :=
    ((⟨P, hP⟩ : C(g ⁻¹' Iic 0, GLSymplectic κ ℝ))⁻¹).comp
      ⟨Subtype.val, continuous_subtypeVal⟩
  let Pout : C(↥(sublevelBoundary hg.continuous), GLSymplectic κ ℝ) :=
    (⟨P', hP'⟩ : C(g ⁻¹' Ici 0, GLSymplectic κ ℝ)).comp
      ⟨fun z ↦ ⟨_, mem_preimage_Ici_of_mem_sublevelBoundary z.property⟩,
        (continuous_subtypeVal.comp continuous_subtypeVal).subtype_mk _⟩
  -- By the complex formula, the number is the boundary Maslov index of `P⁻¹ Ψ P'`. The term of
  -- `P⁻¹` vanishes since `P⁻¹` is defined on all of `Σ₁`, and that of `P'` since `P'` is defined
  -- on all of `Σ₂`.
  rw [hJσ, chernNumber_eq_boundaryDegree_normalizedDet oM hn hg h0 hΘ₁ hΘ₂
      (u := maslovPhaseMap.comp (Pinv * Ψ * Pout)) fun z hz ↦ ?_,
    ← HomologicalOrientation.sublevelBoundaryMaslovIndex_eq_sublevelBoundaryDegree,
    HomologicalOrientation.sublevelBoundaryMaslovIndex_mul,
    HomologicalOrientation.sublevelBoundaryMaslovIndex_mul,
    oM.sublevelBoundaryMaslovIndex_eq_zero_of_extend_Iic hn hg h0
      ((⟨P, hP⟩ : C(g ⁻¹' Iic 0, GLSymplectic κ ℝ))⁻¹) fun _ ↦ by
        simp only [Pinv, ContinuousMap.comp_apply, ContinuousMap.coe_mk],
    oM.sublevelBoundaryMaslovIndex_eq_zero_of_extend_Ici hn hg h0 (Ψ := Pout) ⟨P', hP'⟩ fun _ ↦ by
      simp only [Pout, ContinuousMap.comp_apply, ContinuousMap.coe_mk],
    zero_add, add_zero]
  -- The Maslov phase of the transition is the normalized determinant of the complex transition.
  simp only [Pinv, Pout, ContinuousMap.comp_apply, maslovPhaseMap_apply, ContinuousMap.mul_apply,
    ContinuousMap.inv_apply, ContinuousMap.coe_mk]
  exact J.toContinuousComplexStructure.maslovPhase_inv_mul_mul_eq_normalizedDet (hΘ₁Φ z)
    (hΘ₂Φ ⟨_, hz⟩) (hΨ z)

end Symplectic

end SymplecticGeometry.Bundle

end
