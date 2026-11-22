/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.BoundaryDegree
public import SymplecticGeometry.Analysis.Matrix.SymplecticGroup.Maslov
public import SymplecticGeometry.Geometry.Manifold.ModelTransport.InteriorModel
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Section.ArgumentPrinciple
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
of this setting: `X = S`, `M` is the interior of `S` re-modelled on `ℝ²`
(`SymplecticGeometry.InteriorModel`), `ι` is its inclusion
(`SymplecticGeometry.InteriorModel.isOpenEmbedding_val`), whose range is the complement of the
boundary (`SymplecticGeometry.InteriorModel.range_val_interiorOpens`), the collared map is the
inclusion of the boundary (`TauCeti.isCollared_subtypeVal_boundary_of_compactSpace`), and the
homological orientation comes from a smooth orientation of the interior
(`TauCeti.Manifold.Orientation.toHomologicalOrientation`). In this case the boundary Maslov
index is defined for maps on the boundary `(𝓡∂ 2).boundary S` itself.

A smooth `g : M → ℝ` with regular value `0` on a closed oriented surface `M` gives an instance of
this setting: `X = Σ₁ = {g ≤ 0}`, with interior `{g < 0}` and boundary the level set `g⁻¹(0)`
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
* `SymplecticGeometry.Bundle.chernNumber_eq_boundaryDegree_normalizedDet`: the first Chern number
  of a complex bundle with frames over the two sides of a splitting is the boundary degree of the
  normalized determinant of the transition.

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
    haveI := compactSpace_preimage_Iic hg.continuous
    chernNumber oM hn G E =
      (oM.comap (TopologicalSpace.Opens.isOpenEmbedding' _)).boundaryDegree hn
        (isOpenEmbedding_inclusion_preimage_Iio hg.continuous)
        (range_inclusion_preimage_Iio hg.continuous)
        (SymplecticGeometry.isCollared_inclusion_levelSet hg h0).1 u := by
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

end SymplecticGeometry.Bundle

end
