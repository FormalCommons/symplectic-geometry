/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.BoundaryDegree
public import SymplecticGeometry.Analysis.Matrix.SymplecticGroup.Maslov
public import SymplecticGeometry.Geometry.Manifold.ModelTransport.InteriorModel
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.ChernNumber.Basic
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Symplectic.ComplexStructure.UnitaryFrame
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Section.ArgumentPrinciple
public import SymplecticGeometry.Topology.VectorBundle.Complex.FirstChernClass
public import SymplecticGeometry.Topology.VectorBundle.Complex.Structure
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

For a symplectic vector bundle `(V, σ)` with symplectic frames `Φ₁` over `Σ₁` and `Φ₂` over `Σ₂`,
and the map `Ψ : g⁻¹(0) → Sp(2k)` with `Φ₂ = Φ₁ ∘ Ψ`, the first Chern number of `(V, σ)` is the
boundary Maslov index of `Ψ` on `Σ₁`
(`SymplecticGeometry.Bundle.symplecticChernNumber_eq_boundaryMaslovIndex`). The proof follows that
of `SymplecticGeometry.Bundle.symplecticChernNumber_eq_sum_maslovIndex_clutching` in
`ChernNumber/Clutching.lean`. Continuous changes of frame `P` over `Σ₁` and `P'` over `Σ₂`, with
values in `Sp(2k)`, make the frames unitary for a complex structure `J` compatible with `σ`
(`SymplecticGeometry.Bundle.ContMDiffTwoForm.Compatible.exists_continuous_GLSymplectic_unitary`).
Read on `ℂᵏ`, they are complex frames of `(V, J)`, with transition `P⁻¹ Ψ P'` on `g⁻¹(0)`, whose
Maslov phase is its normalized complex determinant
(`TauCeti.GLSymplectic.maslovPhase_eq_normalizedDet`). By the complex formula and the product
formula, the number is the sum of the boundary Maslov indices of `P⁻¹`, `Ψ` and `P'`. That of
`P⁻¹` vanishes because `P⁻¹` is defined on all of `Σ₁`, and that of `P'` because a circle map
defined on all of `Σ₂` has boundary degree `0` on `Σ₁`
(`SymplecticGeometry.boundaryDegree_eq_zero_of_extend_Ici`: by the argument principle on a split
surface, this degree is the Euler number of the trivial line bundle).

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
* `SymplecticGeometry.boundaryDegree_eq_zero_of_extend_Ici`: a circle map on `Σ₂` has boundary
  degree `0` on `Σ₁`.
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

/-! ### Circle maps on the far side of a splitting -/

namespace SymplecticGeometry

open _root_.Bundle Module TauCeti

variable {EM : Type} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [FiniteDimensional ℝ EM]
  {M : Type} [TopologicalSpace M] [ChartedSpace EM M] [T2Space M] [CompactSpace M]
  [IsManifold 𝓘(ℝ, EM) ∞ M] {g : M → ℝ}

/-- **The boundary degree of a map that extends over the other side.** Let `M` be a closed
smooth surface oriented by `oM`, and `g : M → ℝ` smooth with regular value `0`, splitting `M` into
`Σ₁ = {g ≤ 0}` and `Σ₂ = {g ≥ 0}`. A continuous `u` from the boundary `Σ₁ ∖ {g < 0}` of `Σ₁` to
the circle that is the restriction of a continuous map `v : Σ₂ → S¹` has boundary degree `0` on
`Σ₁`, whose interior `{g < 0}` carries the orientation restricted from `oM`. -/
theorem boundaryDegree_eq_zero_of_extend_Ici
    (oM : HomologicalOrientation M EM 2) (hn : finrank ℝ EM = 2)
    (hg : ContMDiff 𝓘(ℝ, EM) 𝓘(ℝ) ∞ g) (h0 : IsRegularValue 𝓘(ℝ, EM) 𝓘(ℝ) g 0)
    (v : C(g ⁻¹' Ici 0, Circle))
    {u : C(↥(range (inclusion (s := ((⟨g ⁻¹' Iio 0, isOpen_Iio.preimage hg.continuous⟩ :
      TopologicalSpace.Opens M) : Set M)) (preimage_mono Iio_subset_Iic_self)))ᶜ, Circle)}
    (hu : ∀ (z : ↥(range (inclusion (s := ((⟨g ⁻¹' Iio 0, isOpen_Iio.preimage hg.continuous⟩ :
      TopologicalSpace.Opens M) : Set M)) (preimage_mono Iio_subset_Iic_self)))ᶜ)
      (hz : ((z : g ⁻¹' Iic 0) : M) ∈ g ⁻¹' Ici 0), u z = v ⟨_, hz⟩) :
    haveI : CompactSpace (g ⁻¹' Iic 0) :=
      isCompact_iff_compactSpace.1 (isClosed_Iic.preimage hg.continuous).isCompact
    (oM.comap (TopologicalSpace.Opens.isOpenEmbedding' _)).boundaryDegree hn
        (IsOpenEmbedding.inclusion _
          ((isOpen_Iio.preimage hg.continuous).preimage continuous_subtypeVal))
        ((range_inclusion _).trans (SymplecticGeometry.isCollared_inclusion_levelSet hg h0).2.symm)
        (SymplecticGeometry.isCollared_inclusion_levelSet hg h0).1 u = 0 := by
  -- A point of `{g ≤ 0}` off the interior `{g < 0}` lies in `{g ≥ 0}`.
  have hlt (z : ↥(range (inclusion (s := ((⟨g ⁻¹' Iio 0, isOpen_Iio.preimage hg.continuous⟩ :
      TopologicalSpace.Opens M) : Set M)) (preimage_mono Iio_subset_Iic_self)))ᶜ) :
      ((z : g ⁻¹' Iic 0) : M) ∈ g ⁻¹' Ici 0 :=
    mem_preimage.2 (mem_Ici.2 (not_lt.1 fun h' ↦ z.property ⟨⟨_, h'⟩, rfl⟩))
  -- The argument principle for the trivial line bundle, with the section `1` over `{g ≤ 0}` and
  -- the section `v` over `{g ≥ 0}`; the Euler class of the trivial bundle vanishes.
  have h := VectorBundleOrientation.evalFundamentalClass_complexEulerClass_eq_boundaryDegree
    (G := ℂ) (L := Bundle.Trivial M ℂ) (by simp) oM hn hg h0
    (σ := fun _ ↦ (1 : ℂ))
    ((Bundle.Trivial.homeomorphProd M ℂ).symm.continuous.comp
      (continuous_subtypeVal.prodMk continuous_const)) (fun _ ↦ one_ne_zero)
    (s := fun x ↦ (v x : ℂ))
    ((Bundle.Trivial.homeomorphProd M ℂ).symm.continuous.comp
      (continuous_subtypeVal.prodMk (continuous_subtypeVal.comp v.continuous)))
    (fun x ↦ Circle.coe_ne_zero _) (c := fun z ↦ (v ⟨_, hlt z⟩ : ℂ))
    (fun z hz ↦ by simp) (u := u) fun z ↦ by
      rw [Circle.norm_coe, Complex.ofReal_one, div_one, hu z (hlt z)]
  rw [complexEulerClass_trivial, map_zero] at h
  exact h.symm

end SymplecticGeometry

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
    {u : C(↥(range (inclusion (s := ((⟨g ⁻¹' Iio 0, isOpen_Iio.preimage hg.continuous⟩ :
      TopologicalSpace.Opens M) : Set M)) (preimage_mono Iio_subset_Iic_self)))ᶜ, Circle)}
    (hu : ∀ (z : ↥(range (inclusion (s := ((⟨g ⁻¹' Iio 0, isOpen_Iio.preimage hg.continuous⟩ :
      TopologicalSpace.Opens M) : Set M)) (preimage_mono Iio_subset_Iic_self)))ᶜ)
      (hz : ((z : g ⁻¹' Iic 0) : M) ∈ g ⁻¹' Ici 0),
      u z = ((Φ₂ ⟨_, hz⟩).trans (Φ₁ z).symm).normalizedDet) :
    haveI : CompactSpace (g ⁻¹' Iic 0) :=
      isCompact_iff_compactSpace.1 (isClosed_Iic.preimage hg.continuous).isCompact
    chernNumber oM hn G E =
      (oM.comap (TopologicalSpace.Opens.isOpenEmbedding' _)).boundaryDegree hn
        (IsOpenEmbedding.inclusion _
          ((isOpen_Iio.preimage hg.continuous).preimage continuous_subtypeVal))
        ((range_inclusion _).trans (SymplecticGeometry.isCollared_inclusion_levelSet hg h0).2.symm)
        (SymplecticGeometry.isCollared_inclusion_levelSet hg h0).1 u := by
  let i₁ : C(g ⁻¹' Iic 0, M) := ⟨Subtype.val, continuous_subtypeVal⟩
  let i₂ : C(g ⁻¹' Ici 0, M) := ⟨Subtype.val, continuous_subtypeVal⟩
  -- A point of `{g ≤ 0}` off the interior `{g < 0}` lies in `{g ≥ 0}`.
  have hlt (z : ↥(range (inclusion (s := ((⟨g ⁻¹' Iio 0, isOpen_Iio.preimage hg.continuous⟩ :
      TopologicalSpace.Opens M) : Set M)) (preimage_mono Iio_subset_Iic_self)))ᶜ) :
      ((z : g ⁻¹' Iic 0) : M) ∈ g ⁻¹' Ici 0 :=
    mem_preimage.2 (mem_Ici.2 (not_lt.1 fun h' ↦ z.property ⟨⟨_, h'⟩, rfl⟩))
  let j₁ : C(↥(range (inclusion (s := ((⟨g ⁻¹' Iio 0, isOpen_Iio.preimage hg.continuous⟩ :
      TopologicalSpace.Opens M) : Set M)) (preimage_mono Iio_subset_Iic_self)))ᶜ, g ⁻¹' Iic 0) :=
    ⟨Subtype.val, continuous_subtypeVal⟩
  let j₂ : C(↥(range (inclusion (s := ((⟨g ⁻¹' Iio 0, isOpen_Iio.preimage hg.continuous⟩ :
      TopologicalSpace.Opens M) : Set M)) (preimage_mono Iio_subset_Iic_self)))ᶜ, g ⁻¹' Ici 0) :=
    ⟨fun z ↦ ⟨_, hlt z⟩, (continuous_subtypeVal.comp continuous_subtypeVal).subtype_mk _⟩
  have hΦ₁j : Continuous fun q : _ × G ↦ TotalSpace.mk' G (i₁ (j₁ q.1)) (Φ₁ (j₁ q.1) q.2) :=
    hΦ₁.comp ((j₁.continuous.comp continuous_fst).prodMk continuous_snd)
  have hΦ₂j : Continuous fun q : _ × G ↦ TotalSpace.mk' G (i₂ (j₂ q.1)) (Φ₂ (j₂ q.1) q.2) :=
    hΦ₂.comp ((j₂.continuous.comp continuous_fst).prodMk continuous_snd)
  -- On the boundary, the determinant section of `Φ₂` is that of `Φ₁` times the determinant of
  -- the transition.
  have hsc : ∀ z : ↥(range (inclusion (s := ((⟨g ⁻¹' Iio 0, isOpen_Iio.preimage hg.continuous⟩ :
      TopologicalSpace.Opens M) : Set M)) (preimage_mono Iio_subset_Iic_self)))ᶜ,
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
  rw [hu z (hlt z), ContinuousLinearEquiv.coe_normalizedDet,
    ← ContinuousLinearEquiv.det_coe_trans_symm]
  simp only [j₁, j₂, ContinuousMap.coe_mk]

/-! ### The splitting formula for symplectic frames -/

section Symplectic

open Matrix TauCeti.GLSymplectic

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V] {k : ℕ} {n : ℕ∞}
  [ContMDiffVectorBundle n F V 𝓘(ℝ, EM)] {σ : ContMDiffTwoForm 𝓘(ℝ, EM) n F V}

variable (G) in
/-- **The splitting formula for symplectic frames.** Let `M` be a closed smooth surface oriented
by `oM`, and `g : M → ℝ` smooth with regular value `0`, splitting `M` into `Σ₁ = {g ≤ 0}` and
`Σ₂ = {g ≥ 0}`. Let `σ` be a two-form on a smooth vector bundle `V` over `M`, and `Φ₁`, `Φ₂`
symplectic frames of `V` over `Σ₁` and over `Σ₂`: linear isomorphisms `StdSpace (Fin k) ≃ V x`,
continuous as maps to the total space, with `σ(Φ v, Φ w) = σ₀(v, w)` for the standard form
`σ₀ = stdForm (Fin k)`. Let `Ψ` be a continuous map from the boundary `Σ₁ ∖ {g < 0}` of `Σ₁` to
the symplectic group with `Φ₂ = Φ₁ ∘ Ψ` there. Then the first Chern number of `(V, σ)` is the
boundary Maslov index of `Ψ` on `Σ₁`, whose interior `{g < 0}` carries the orientation restricted
from `oM`.

Milestone: *First Chern number of symplectic vector bundles over surfaces*. -/
theorem symplecticChernNumber_eq_boundaryMaslovIndex
    [Fact (finrank ℝ F = 2 * finrank ℂ G)]
    (oM : HomologicalOrientation M EM 2) (hn : finrank ℝ EM = 2)
    (hg : ContMDiff 𝓘(ℝ, EM) 𝓘(ℝ) ∞ g) (h0 : IsRegularValue 𝓘(ℝ, EM) 𝓘(ℝ) g 0)
    {Φ₁ : ∀ x : g ⁻¹' Iic 0, StdSpace (Fin k) ≃L[ℝ] V x}
    (hΦ₁ : Continuous fun q : g ⁻¹' Iic 0 × StdSpace (Fin k) ↦
      TotalSpace.mk' F (q.1 : M) (Φ₁ q.1 q.2))
    (hΦ₁σ : ∀ (x : g ⁻¹' Iic 0) v w, σ.bilinFormAt x (Φ₁ x v) (Φ₁ x w) = stdForm (Fin k) v w)
    {Φ₂ : ∀ x : g ⁻¹' Ici 0, StdSpace (Fin k) ≃L[ℝ] V x}
    (hΦ₂ : Continuous fun q : g ⁻¹' Ici 0 × StdSpace (Fin k) ↦
      TotalSpace.mk' F (q.1 : M) (Φ₂ q.1 q.2))
    (hΦ₂σ : ∀ (x : g ⁻¹' Ici 0) v w, σ.bilinFormAt x (Φ₂ x v) (Φ₂ x w) = stdForm (Fin k) v w)
    (Ψ : C(↥(range (inclusion (s := ((⟨g ⁻¹' Iio 0, isOpen_Iio.preimage hg.continuous⟩ :
      TopologicalSpace.Opens M) : Set M)) (preimage_mono Iio_subset_Iic_self)))ᶜ,
        GLSymplectic (Fin k) ℝ))
    (hΨ : ∀ (z : ↥(range (inclusion (s := ((⟨g ⁻¹' Iio 0, isOpen_Iio.preimage hg.continuous⟩ :
      TopologicalSpace.Opens M) : Set M)) (preimage_mono Iio_subset_Iic_self)))ᶜ)
      (hz : ((z : g ⁻¹' Iic 0) : M) ∈ g ⁻¹' Ici 0) v,
      Φ₂ ⟨_, hz⟩ v = Φ₁ z (toEuclideanLin (Ψ z : GL (Fin k ⊕ Fin k) ℝ) v)) :
    haveI : CompactSpace (g ⁻¹' Iic 0) :=
      isCompact_iff_compactSpace.1 (isClosed_Iic.preimage hg.continuous).isCompact
    symplecticChernNumber oM hn G σ =
      (oM.comap (TopologicalSpace.Opens.isOpenEmbedding' _)).boundaryMaslovIndex hn
        (IsOpenEmbedding.inclusion _
          ((isOpen_Iio.preimage hg.continuous).preimage continuous_subtypeVal))
        ((range_inclusion _).trans (SymplecticGeometry.isCollared_inclusion_levelSet hg h0).2.symm)
        (SymplecticGeometry.isCollared_inclusion_levelSet hg h0).1 Ψ := by
  have : CompactSpace (g ⁻¹' Iic 0) :=
    isCompact_iff_compactSpace.1 (isClosed_Iic.preimage hg.continuous).isCompact
  -- A point of `{g ≤ 0}` off the interior `{g < 0}` lies in `{g ≥ 0}`.
  have hlt (z : ↥(range (inclusion (s := ((⟨g ⁻¹' Iio 0, isOpen_Iio.preimage hg.continuous⟩ :
      TopologicalSpace.Opens M) : Set M)) (preimage_mono Iio_subset_Iic_self)))ᶜ) :
      ((z : g ⁻¹' Iic 0) : M) ∈ g ⁻¹' Ici 0 :=
    mem_preimage.2 (mem_Ici.2 (not_lt.1 fun h' ↦ z.property ⟨⟨_, h'⟩, rfl⟩))
  -- Every fibre carries one of the symplectic frames, so `σ` is nondegenerate.
  have hframe (x : M) : ∃ Θ : StdSpace (Fin k) ≃L[ℝ] V x,
      ∀ v w, σ.bilinFormAt x (Θ v) (Θ w) = stdForm (Fin k) v w := by
    by_cases hx : g x ≤ 0
    · exact ⟨Φ₁ ⟨x, hx⟩, hΦ₁σ ⟨x, hx⟩⟩
    · exact ⟨Φ₂ ⟨x, (not_le.1 hx).le⟩, hΦ₂σ ⟨x, (not_le.1 hx).le⟩⟩
  obtain ⟨J, hJ⟩ := (ContMDiffTwoForm.isNondegenerate_of_forall_exists (stdForm (Fin k))
    fun x ↦ (hframe x).elim fun Θ hΘ ↦ ⟨Θ.toLinearEquiv, hΘ⟩).exists_compatible
  rcases isEmpty_or_nonempty M with hM | ⟨⟨x₀⟩⟩
  · -- Over the empty surface any frames will do.
    rw [HomologicalOrientation.boundaryMaslovIndex_def,
      symplecticChernNumber_eq_chernNumber oM hn G hJ.tames]
    exact chernNumber_eq_boundaryDegree_normalizedDet oM hn hg h0
      (Φ₁ := fun x ↦ isEmptyElim (x : M)) (Φ₂ := fun x ↦ isEmptyElim (x : M))
      continuous_of_discreteTopology continuous_of_discreteTopology
      fun z ↦ isEmptyElim ((z : g ⁻¹' Iic 0) : M)
  -- Otherwise the rank of `V` is `2 k`, and `ℂᵏ` is a complex model of `(V, J)`.
  have : Fact (finrank ℝ F = 2 * finrank ℂ (Fin k → ℂ)) := by
    obtain ⟨Θ, -⟩ := hframe x₀
    refine ⟨?_⟩
    rw [← ((trivializationAt F V x₀).continuousLinearEquivAt ℝ x₀
        (FiberBundle.mem_baseSet_trivializationAt' x₀)).toLinearEquiv.finrank_eq,
      ← Θ.toLinearEquiv.finrank_eq, finrank_euclideanSpace, Fintype.card_sum, Fintype.card_fin,
      Module.finrank_fin_fun]
    ring
  rw [← symplecticChernNumber_congr_model oM hn G (Fin k → ℂ) σ,
    symplecticChernNumber_eq_chernNumber oM hn (Fin k → ℂ) hJ.tames]
  -- Make the frames unitary for `J` by continuous changes of frame `P` and `P'`.
  obtain ⟨P, hP, hPJ⟩ :=
    hJ.exists_continuous_GLSymplectic_unitary (f := ((↑) : g ⁻¹' Iic 0 → M)) hΦ₁ hΦ₁σ
  obtain ⟨P', hP', hP'J⟩ :=
    hJ.exists_continuous_GLSymplectic_unitary (f := ((↑) : g ⁻¹' Ici 0 → M)) hΦ₂ hΦ₂σ
  -- The products of matrices act by composition.
  have hmul (A B : GLSymplectic (Fin k) ℝ) (v : StdSpace (Fin k)) :
      toEuclideanLin ((A * B : GLSymplectic (Fin k) ℝ) : GL (Fin k ⊕ Fin k) ℝ) v =
        toEuclideanLin ((A : GL (Fin k ⊕ Fin k) ℝ) : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) ℝ)
          (toEuclideanLin ((B : GL (Fin k ⊕ Fin k) ℝ) :
            Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) ℝ) v) := by
    rw [Subgroup.coe_mul, Units.val_mul, toLpLin_mul_same, LinearMap.comp_apply]
  have hcont {X : Type} [TopologicalSpace X] {Q : X → GLSymplectic (Fin k) ℝ}
      (hQ : Continuous Q) : Continuous fun q : X × StdSpace (Fin k) ↦
        toEuclideanLin (Q q.1 : GL (Fin k ⊕ Fin k) ℝ) q.2 :=
    (((continuous_toEuclideanCLM.comp (Units.continuous_val.comp
      (continuous_subtypeVal.comp hQ))).comp continuous_fst).clm_apply continuous_snd).congr
        fun q ↦ toEuclideanCLM_apply _ _
  -- The unitary frames `Φ₁ ∘ P` and `Φ₂ ∘ P'`, read on `ℂᵏ`, are complex frames of `(V, J)`.
  let Θ₁ : ∀ x : g ⁻¹' Iic 0, (Fin k → ℂ) ≃L[ℝ] V x := fun x ↦
    (complexToRealEuclidean (Fin k)).trans
      ((toEuclideanCLE _ (P x : GL (Fin k ⊕ Fin k) ℝ).det_ne_zero).trans (Φ₁ x))
  let Θ₂ : ∀ x : g ⁻¹' Ici 0, (Fin k → ℂ) ≃L[ℝ] V x := fun x ↦
    (complexToRealEuclidean (Fin k)).trans
      ((toEuclideanCLE _ (P' x : GL (Fin k ⊕ Fin k) ℝ).det_ne_zero).trans (Φ₂ x))
  have hΘ₁ (x : g ⁻¹' Iic 0) (v : Fin k → ℂ) : Θ₁ x v =
      Φ₁ x (toEuclideanLin (P x : GL (Fin k ⊕ Fin k) ℝ) (complexToRealEuclidean (Fin k) v)) := by
    rw [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.trans_apply,
      toEuclideanCLE_apply]
  have hΘ₂ (x : g ⁻¹' Ici 0) (v : Fin k → ℂ) : Θ₂ x v =
      Φ₂ x (toEuclideanLin (P' x : GL (Fin k ⊕ Fin k) ℝ) (complexToRealEuclidean (Fin k) v)) := by
    rw [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.trans_apply,
      toEuclideanCLE_apply]
  have hΘ₁I (x : g ⁻¹' Iic 0) (v : Fin k → ℂ) :
      Θ₁ x (Complex.I • v) = J.toContinuousComplexStructure x (Θ₁ x v) := by
    rw [hΘ₁, hΘ₁, ContMDiffComplexStructure.toContinuousComplexStructure_apply, hPJ,
      stdComplexStructure_complexToRealEuclidean]
  have hΘ₂I (x : g ⁻¹' Ici 0) (v : Fin k → ℂ) :
      Θ₂ x (Complex.I • v) = J.toContinuousComplexStructure x (Θ₂ x v) := by
    rw [hΘ₂, hΘ₂, ContMDiffComplexStructure.toContinuousComplexStructure_apply, hP'J,
      stdComplexStructure_complexToRealEuclidean]
  have hc₁ := J.toContinuousComplexStructure.continuous_frameOfCommute Θ₁ hΘ₁I (Fin k → ℂ)
    ((hΦ₁.comp (continuous_fst.prodMk ((hcont hP).comp (continuous_fst.prodMk
      ((complexToRealEuclidean (Fin k)).continuous.comp continuous_snd))))).congr fun q ↦ by
        simp only [Function.comp_apply, hΘ₁])
  have hc₂ := J.toContinuousComplexStructure.continuous_frameOfCommute Θ₂ hΘ₂I (Fin k → ℂ)
    ((hΦ₂.comp (continuous_fst.prodMk ((hcont hP').comp (continuous_fst.prodMk
      ((complexToRealEuclidean (Fin k)).continuous.comp continuous_snd))))).congr fun q ↦ by
        simp only [Function.comp_apply, hΘ₂])
  -- On the boundary the new transition is `P⁻¹ Ψ P'`.
  let Pinv := ((⟨P, hP⟩ : C(g ⁻¹' Iic 0, GLSymplectic (Fin k) ℝ))⁻¹).comp
    (⟨Subtype.val, continuous_subtypeVal⟩ : C(↥(range (inclusion
      (s := ((⟨g ⁻¹' Iio 0, isOpen_Iio.preimage hg.continuous⟩ : TopologicalSpace.Opens M) :
        Set M)) (preimage_mono Iio_subset_Iic_self)))ᶜ, g ⁻¹' Iic 0))
  let Pout := (⟨P', hP'⟩ : C(g ⁻¹' Ici 0, GLSymplectic (Fin k) ℝ)).comp
    (⟨fun z ↦ ⟨_, hlt z⟩, (continuous_subtypeVal.comp continuous_subtypeVal).subtype_mk _⟩ :
      C(↥(range (inclusion
        (s := ((⟨g ⁻¹' Iio 0, isOpen_Iio.preimage hg.continuous⟩ : TopologicalSpace.Opens M) :
          Set M)) (preimage_mono Iio_subset_Iic_self)))ᶜ, g ⁻¹' Ici 0))
  -- By the complex formula, the number is the boundary Maslov index of `P⁻¹ Ψ P'`. The term of
  -- `P⁻¹` vanishes since `P⁻¹` is defined on all of `Σ₁`, and that of `P'` since `P'` is defined
  -- on all of `Σ₂`.
  rw [chernNumber_eq_boundaryDegree_normalizedDet oM hn hg h0 hc₁ hc₂
      (u := maslovPhaseMap.comp (Pinv * Ψ * Pout)) fun z hz ↦ ?_,
    ← HomologicalOrientation.boundaryMaslovIndex_def,
    HomologicalOrientation.boundaryMaslovIndex_mul, HomologicalOrientation.boundaryMaslovIndex_mul,
    HomologicalOrientation.boundaryMaslovIndex_eq_zero_of_extend _ _ _ _ _
      ((⟨P, hP⟩ : C(g ⁻¹' Iic 0, GLSymplectic (Fin k) ℝ))⁻¹) fun _ ↦ rfl, zero_add]
  · simp only [HomologicalOrientation.boundaryMaslovIndex_def]
    rw [boundaryDegree_eq_zero_of_extend_Ici oM hn hg h0 (maslovPhaseMap.comp ⟨P', hP'⟩)
      (u := maslovPhaseMap.comp Pout) fun _ _ ↦ rfl, add_zero]
  · -- The Maslov phase of the transition is the normalized determinant of the complex
    -- transition, which acts on `ℝ²ᵏ = ℂᵏ` as `P⁻¹ Ψ P'`.
    rw [ContinuousMap.comp_apply, maslovPhaseMap_apply]
    refine maslovPhase_eq_normalizedDet _ fun v ↦ ?_
    refine ((toEuclideanCLE _ (P z : GL (Fin k ⊕ Fin k) ℝ).det_ne_zero).trans (Φ₁ z)).injective ?_
    have h₁ := J.toContinuousComplexStructure.fiberEquiv_frameOfCommute Θ₁ hΘ₁I z
    have h₂ := J.toContinuousComplexStructure.fiberEquiv_frameOfCommute Θ₂ hΘ₂I ⟨_, hz⟩
    simp only [ContinuousLinearEquiv.trans_apply, toEuclideanCLE_apply]
    rw [← hΘ₁, ← h₁, ContinuousLinearEquiv.apply_symm_apply, h₂, hΘ₂, hΨ, ContinuousMap.mul_apply,
      ContinuousMap.mul_apply, hmul, hmul, ← hmul (P z)]
    simp only [Pinv, Pout, ContinuousMap.comp_apply, ContinuousMap.inv_apply, ContinuousMap.coe_mk,
      mul_inv_cancel, OneMemClass.coe_one, Units.val_one, toLpLin_one, LinearMap.id_apply]

end Symplectic

end SymplecticGeometry.Bundle

end
