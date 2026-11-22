/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.BoundaryDegree
public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.CoordinateDisc
public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.LocalIndex
public import TauCeti.Analysis.Complex.Conformal.LocalIndex

/-!
# A map to `ℂ` with one simple holomorphic zero

Let `M` be a surface with a homological orientation `o`, and `ψ` a coordinate disc of `M`
(`SymplecticGeometry.CoordinateDisc`). A map `H : M → ℂ` which, read in `ψ`, is complex
differentiable at a point `w₀` with nonzero derivative, and which takes the value `y` only at
`ψ w₀`, sends the local orientation of `o` at `ψ w₀` to the local orientation of `ℂ` at `y`
(`SymplecticGeometry.CoordinateDisc.localHomologyMap_orientation_of_hasDerivAt`): near a simple
holomorphic zero a map has local degree `1`.

In the setting of the boundary degree (`TauCeti.HomologicalOrientation.boundaryDegree`), with `X`
compact Hausdorff and `ι : M → X` an open embedding whose complement `∂X` is collared, a map
`G : X → ℂ` whose only zero is such a simple holomorphic zero in a coordinate disc therefore has
boundary degree `1`: the normalization `G / |G|` on `∂X` winds once around the origin
(`SymplecticGeometry.boundaryDegree_eq_one_of_hasDerivAt`). This is the argument principle with
one zero; the general form for sections of plane bundles is
`TauCeti.VectorBundleOrientation.sum_sectionIndex_eq_boundaryDegree`.

## Proof

The image of the relative fundamental class `[X, ∂X]` in the local homology of `X` at the zero is
the local orientation of `o` there
(`TauCeti.HomologicalOrientation.localHomologyRestriction_fundamentalClassRel`), so by
`TauCeti.HomologicalOrientation.boundaryDegree_eq_of_localHomologyMap_eq_zsmul` it suffices to see
that `G ∘ ι` sends that local orientation to the one of `ℂ` at the origin. The coordinate
disc carries the canonical local orientation of its ball to the one of `o`
(`SymplecticGeometry.CoordinateDisc.localOrientationEquiv_apply`), so this is a statement about the
map `G ∘ ι ∘ ψ` on the ball, whose local index at `w₀` is `1` by Tau Ceti's
`TauCeti.HomologicalOrientation.localIndex_comap_eq_one_of_hasDerivAt`: its real derivative is
multiplication by the complex derivative, of positive determinant.

## Main results

* `SymplecticGeometry.CoordinateDisc.localHomologyMap_orientation_of_hasDerivAt`: a map with one
  simple holomorphic preimage of `y` in a coordinate disc sends the local orientation there to that
  of `ℂ` at `y`.
* `SymplecticGeometry.boundaryDegree_eq_one_of_hasDerivAt`: a map to `ℂ` whose only zero is simple
  and holomorphic in a coordinate disc has boundary degree `1`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.7: degrees
  of circle-valued maps on the boundary of a surface.
* L. Ahlfors, *Complex Analysis*, 3rd ed., McGraw-Hill, 1979, Chapter 4, §3.3 (the local mapping
  theorem and the argument principle).
-/

public section

noncomputable section

open CategoryTheory Set Topology Module TauCeti

namespace SymplecticGeometry

variable {M : Type} [TopologicalSpace M] [T2Space M] {E : Type} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M] {o : HomologicalOrientation M E 2}

namespace CoordinateDisc

/-- **A simple holomorphic preimage has local degree `1`.** Let `ψ` be a coordinate disc of `M`
and `H : M → ℂ` a map taking the value `y` only at `ψ w₀`. If `H ∘ ψ` agrees near `w₀` with a map
`g : ℂ → ℂ` that is complex differentiable at `w₀` with nonzero derivative, then `H` sends the
local orientation of `o` at `ψ w₀` to the local orientation of `ℂ` at `y`. -/
theorem localHomologyMap_orientation_of_hasDerivAt (ψ : CoordinateDisc o) {w₀ : ball}
    {H : C(M, ℂ)} {y : ℂ} (hy : H (ψ w₀) = y) (hH : H ⁻¹' {y} ⊆ {ψ w₀}) {g : ℂ → ℂ} {g' : ℂ}
    (hg : HasDerivAt g g' w₀) (hg' : g' ≠ 0) (hHg : ∀ᶠ w in 𝓝 w₀, H (ψ w) = g w) :
    localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) H hH 2 (o (ψ w₀)).val =
      (complexHomologicalOrientation ℂ y).val := by
  have hψ : (⟨ψ, ψ.continuous⟩ : C(ball, M)) ⁻¹' {ψ w₀} ⊆ {w₀} := fun w hw ↦ ψ.injective hw
  have hHψ : H.comp ⟨ψ, ψ.continuous⟩ ⁻¹' {y} ⊆ {w₀} := (preimage_mono hH).trans hψ
  -- On the ball, `H ∘ ψ` has local index `1` at `w₀`, for the canonical orientations.
  have hind : (complexHomologicalOrientation ball).localIndex (complexHomologicalOrientation ℂ)
      (H.comp ⟨ψ, ψ.continuous⟩) w₀ = 1 := by
    have h := (complexHomologicalOrientation ℂ).localIndex_comap_eq_one_of_hasDerivAt
      ball.isOpenEmbedding' IsOpenEmbedding.id (f := H.comp ⟨ψ, ψ.continuous⟩)
      (hHg.mono fun w hw ↦ hw.symm) hg hg'
    rwa [comap_subtypeVal_complexHomologicalOrientation,
      HomologicalOrientation.comap_id] at h
  have hloc := ((complexHomologicalOrientation ball).localIndex_eq_iff_of_preimage_subset
    (complexHomologicalOrientation ℂ) Complex.finrank_real_complex _ hy hHψ).1 hind
  rw [one_smul, ← localHomologyMap_comp _ _ _ hψ hH] at hloc
  rw [← hloc, ConcreteCategory.comp_apply, ← ψ.localOrientationEquiv_apply,
    IsOpenEmbedding.coe_localOrientationEquiv, localHomologyIsoOfIsOpenEmbedding_hom]

end CoordinateDisc

open HomologicalOrientation in
/-- **Boundary degree one at a simple holomorphic zero.** Let `X` be compact Hausdorff, `ι : M → X`
an open embedding of a surface oriented by `o`, with collared complement `∂X`, and `ψ` a coordinate
disc of `M`. Let `G : X → ℂ` vanish only at `ι (ψ w₀)`, and agree near `w₀` with a map
`g : ℂ → ℂ`, read through `ι ∘ ψ`, that is complex differentiable at `w₀` with nonzero derivative.
Then `u = G / |G|` has boundary degree `1` on `∂X`. -/
theorem boundaryDegree_eq_one_of_hasDerivAt {X : Type} {N : Type*} [TopologicalSpace X]
    [TopologicalSpace N] [CompactSpace X] [T2Space X] {ι : M → X} {f : N → X}
    (hn : finrank ℝ E = 2) (hι : IsOpenEmbedding ι) (hιf : range ι = (range f)ᶜ)
    (hf : IsCollared f) (ψ : CoordinateDisc o) {w₀ : CoordinateDisc.ball} {g : ℂ → ℂ} {g' : ℂ}
    (hg : HasDerivAt g g' w₀) (hg' : g' ≠ 0) {G : C(X, ℂ)} (hG : G ⁻¹' {0} = {ι (ψ w₀)})
    (hGg : ∀ᶠ w in 𝓝 w₀, G (ι (ψ w)) = g w) {u : C(↥((range ι)ᶜ : Set X), Circle)}
    (hu : ∀ z, (u z : ℂ) = ‖G z‖⁻¹ • G z) :
    o.boundaryDegree hn hι hιf hf u = 1 := by
  set H : C(M, ℂ) := G.comp ⟨ι, hι.continuous⟩
  have hGι : G ⁻¹' {0} ⊆ range ι := hG.subset.trans (singleton_subset_iff.2 (mem_range_self _))
  have hH : H ⁻¹' {0} ⊆ {ψ w₀} := fun x hx ↦ hι.injective (hG.subset hx)
  have hι₀ : (⟨ι, hι.continuous⟩ : C(M, X)) ⁻¹' {ι (ψ w₀)} ⊆ {ψ w₀} :=
    fun x hx ↦ hι.injective hx
  refine o.boundaryDegree_eq_of_localHomologyMap_eq_zsmul hn hι hιf hf hGι hu ?_
  -- Restrict `[X, ∂X]` to the zero, where it is the local orientation of `o`, read through `ι`.
  rw [one_smul, ← complexHomologicalOrientation_apply_zero,
    ← localHomologyRestriction_comp_localHomologyMap _ G (singleton_subset_iff.2 (mem_range_self _))
      hG.subset, ConcreteCategory.comp_apply, localHomologyRestriction_fundamentalClassRel,
    localHomologyIsoOfIsOpenEmbedding_hom, ← ConcreteCategory.comp_apply,
    localHomologyMap_comp _ _ _ hι₀ hG.subset]
  exact ψ.localHomologyMap_orientation_of_hasDerivAt (H := H) (hG.symm.subset rfl) hH hg hg' hGg

end SymplecticGeometry

end
