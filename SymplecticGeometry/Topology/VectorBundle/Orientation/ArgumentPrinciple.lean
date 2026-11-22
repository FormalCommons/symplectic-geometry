/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.BoundaryDegree
public import SymplecticGeometry.Topology.VectorBundle.Orientation.Basic
public import SymplecticGeometry.Topology.VectorBundle.Orientation.SectionIndex.FiberwiseEquiv
public import TauCeti.Topology.FiberBundle.Pullback
public import TauCeti.Topology.VectorBundle.Orientation.SectionIndex.Degree

/-!
# The argument principle on a surface with boundary

We work in the setting of the boundary degree
(`TauCeti.HomologicalOrientation.boundaryDegree`): `X` is compact Hausdorff, `ι : M → X` is an
open embedding of a surface oriented by `o`, and `∂X = X ∖ ι(M)` is the image of a collared map.
Let `L` be a real plane bundle over `X`, with any model fibre `F` of real dimension `2`, and with an
orientation `oL`, and let `τ` be a frame of `L` over
the whole of `X`: a family of linear isomorphisms `τ x : L_x ≃ ℂ`, continuous on the total space,
carrying `oL` to `Complex.orientation`. Let `t` be a continuous section of `L` whose zeros are
finitely many and lie in `ι(M)`.

Then the local indices (`TauCeti.VectorBundleOrientation.sectionIndex`) of the pull-back of `t`
along `ι` at its zeros add up to the boundary degree of `τ t / |τ t|` on `∂X`
(`TauCeti.VectorBundleOrientation.sum_sectionIndex_eq_boundaryDegree`).

The frame has to be defined on all of `X`. With a frame over `∂X` only, the statement fails: on the
closed unit disc, twisting a boundary frame by `e^{iθ}` changes the boundary degree by one but
leaves the zeros and their indices as they were.

## Proof

Write `G = τ t : X → ℂ` and `Z` for the zero set of `t ∘ ι`. Then `G` is a map of pairs
`(X, ∂X) ⟶ (ℂ, ℂ ∖ {0})`, and on `∂X`, followed by radial projection, it is the map `u`.

* *Near the boundary.* If `G_*[X, ∂X] ∈ H₂(ℂ, ℂ ∖ {0})` is `c` times the local orientation of `ℂ`
  at the origin selected by `Complex.orientation`, then the boundary degree of `u` is `c`
  (`TauCeti.HomologicalOrientation.boundaryDegree_eq_of_localHomologyMap_eq_zsmul`, by
  naturality of the connecting morphism and the computation of the generator).
* *Near the zeros.* The image of `[X, ∂X]` in `H₂(X, X ∖ ι(Z))` is the fundamental class of `M`
  along `Z`
  (`TauCeti.HomologicalOrientation.localHomologyRestriction_fundamentalClassRel_image`), which is
  the sum of the local orientations at the points of `Z`
  (`TauCeti.HomologicalOrientation.fundamentalClassOn_eq_sum_localOrientationAlong`). The frame
  identifies the pull-back of `L` along `ι` with the trivial bundle `M × ℂ` and `t ∘ ι` with
  `G ∘ ι`, preserving local indices
  (`TauCeti.VectorBundleOrientation.sectionIndex_eq_of_fiberwise`), and in the trivial bundle
  the local index at `z` is the factor by which `G` sends the local orientation at `z` to the one
  of `ℂ` at the origin selected by `Complex.orientation`
  (`TauCeti.VectorBundleOrientation.localHomologyMap_eq_sectionIndex_smul`). So `G_*[X, ∂X]` is
  the sum of the local indices times that local orientation.

The step near the zeros and the final summation adapt the proof of Tau Ceti's
`TauCeti.VectorBundleOrientation.evalFundamentalClass_eulerClass_eq_sum_sectionIndex`, the same
argument on a closed manifold, to the relative fundamental class of `(X, ∂X)`.

## Main results

* `TauCeti.VectorBundleOrientation.sum_sectionIndex_eq_boundaryDegree`: for a framed plane bundle,
  adding up the local indices of a section at its zeros gives the boundary degree of the section
  read in the frame.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.7: the
  Maslov index and the first Chern number of bundles over surfaces, computed by degrees of
  circle-valued maps on the boundary.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.3: fundamental
  classes along compact sets and of manifolds with boundary.
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §11: the Euler class evaluated through the zeros of a section.
-/

public section

noncomputable section

open Bundle CategoryTheory Module Set

namespace TauCeti.VectorBundleOrientation

section ArgumentPrinciple

open AlgebraicTopology Topology

variable {X M : Type} {N : Type*} [TopologicalSpace X] [TopologicalSpace N] [TopologicalSpace M]
  [T2Space X] [CompactSpace X] [T2Space M] {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [ChartedSpace E M] {ι : M → X} {f : N → X}
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {L : X → Type}
  [TopologicalSpace (TotalSpace F L)] [∀ x, AddCommMonoid (L x)]
  [∀ x, Module ℝ (L x)] [∀ x, TopologicalSpace (L x)] [FiberBundle F L] [VectorBundle ℝ F L]

/-- The interior side. Read in the frame `τ`, the section `t` is a map `G : X → ℂ`, and
`G_*[X, ∂X] ∈ H₂(ℂ, ℂ ∖ {0})` is the sum over the zeros of `t ∘ ι` of their local indices times the
local orientation of `ℂ` at the origin selected by `Complex.orientation`. -/
private theorem localHomologyMap_fundamentalClassRel_eq_sum
    (oL : VectorBundleOrientation F L (Fin 2)) (hF : finrank ℝ F = 2)
    (o : HomologicalOrientation M E 2)
    (hn : finrank ℝ E = 2) (hι : IsOpenEmbedding ι) (hιf : range ι = (range f)ᶜ) (hf : IsCollared f)
    {τ : ∀ x, L x ≃L[ℝ] ℂ} (hτ : Continuous fun v : TotalSpace F L ↦ τ v.proj v.snd)
    (hτo : ∀ x, Orientation.map (Fin 2) (τ x).toLinearEquiv (oL x) = Complex.orientation)
    {t : ∀ x, L x} (ht : Continuous fun x ↦ TotalSpace.mk' F x (t x))
    (hZ : {x : M | t (ι x) = 0}.Finite) (hZι : ∀ x, t x = 0 → x ∈ range ι)
    (hG : (⟨fun x ↦ τ x (t x), hτ.comp ht⟩ : C(X, ℂ)) ⁻¹' {0} ⊆ range ι)
    {s : ∀ x, ((⟨ι, hι.continuous⟩ : C(M, X)) *ᵖ L) x} (hst : ∀ x, s x = t (ι x))
    (hs : Continuous fun x ↦ TotalSpace.mk' F x (s x)) :
    localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) ⟨fun x ↦ τ x (t x), hτ.comp ht⟩ hG 2
        (o.fundamentalClassRel hn hι hιf hf) =
      ∑ z ∈ hZ.toFinset,
        (oL.pullback ⟨ι, hι.continuous⟩).sectionIndex hF o hs z •
          (Complex.orientation.localOrientation Complex.finrank_real_complex).val := by
  set g : C(M, X) := ⟨ι, hι.continuous⟩
  set G : C(X, ℂ) := ⟨fun x ↦ τ x (t x), hτ.comp ht⟩
  set Z := {x : M | t (ι x) = 0}
  have hGι : G ⁻¹' {0} ⊆ ι '' Z := fun x hx ↦ by
    have h0 : t x = 0 := (τ x).map_eq_zero_iff.1 hx
    obtain ⟨y, rfl⟩ := hZι x h0
    exact ⟨y, h0, rfl⟩
  -- The frame identifies `ι^* L` with the trivial bundle `M × ℂ`, preserving local indices.
  have hφ : Continuous fun v : TotalSpace F ((⇑g) *ᵖ L) ↦
      TotalSpace.mk' ℂ (E := Bundle.Trivial M ℂ) v.proj (τ (ι v.proj) v.snd) :=
    (Bundle.Trivial.isInducing_toProd M ℂ).continuous_iff.2
      ((Pullback.continuous_proj F L g).prodMk (hτ.comp (Pullback.continuous_lift F L g)))
  have hind (z : M) : (oL.pullback g).sectionIndex hF o hs z =
      (trivial M Complex.orientation).sectionIndex Complex.finrank_real_complex o
        (hφ.comp hs) z :=
    sectionIndex_eq_of_fiberwise _ _ o _ _ hφ (fun x ↦ by
      rw [pullback_apply, trivial_apply]
      exact hτo (ι x)) hs z
  -- Each zero `z` is the only zero in its open neighbourhood `(Z ∖ {z})ᶜ`.
  have hU : ∀ z, IsOpen (Z \ {z})ᶜ := fun _ ↦ hZ.sdiff.isClosed.isOpen_compl
  have hzU : ∀ z, z ∈ (Z \ {z})ᶜ := fun _ h ↦ h.2 rfl
  have hUz : ∀ z, ∀ x ∈ (Z \ {z})ᶜ, x ∈ Z → x = z :=
    fun _ _ hx h0 ↦ by_contra fun hxz ↦ hx ⟨h0, hxz⟩
  -- `[X, ∂X]` restricts to the fundamental class of `M` along `Z`, the sum of the local
  -- orientations at the zeros.
  rw [← localHomologyRestriction_comp_localHomologyMap _ G (image_subset_range ι Z) hGι 2,
    ConcreteCategory.comp_apply,
    HomologicalOrientation.localHomologyRestriction_fundamentalClassRel_image o hn hι hιf hf
      hZ.isCompact, ← ConcreteCategory.comp_apply, localHomologyMap_comp,
    o.fundamentalClassOn_eq_sum_localOrientationAlong hn hZ hU hzU hUz, map_sum]
  refine Finset.sum_congr rfl fun z _ ↦ ?_
  rw [HomologicalOrientation.localOrientationAlong_def, ← ConcreteCategory.comp_apply]
  -- The coefficient modules of the two maps are written differently.
  erw [localHomologyMap_comp]
  rw [← IsOpenEmbedding.coe_localOrientationEquiv_symm, hind z]
  exact localHomologyMap_eq_sectionIndex_smul (trivial M Complex.orientation)
    Complex.finrank_real_complex o (hφ.comp hs) (Bundle.Trivial.trivialization M ℂ) (hU z)
    (hzU z) (fun x hx h0 ↦ hUz z x hx ((τ (ι x)).map_eq_zero_iff.1 (hst x ▸ h0)))
    (fun _ _ ↦ by simp) (fun _ _ ↦ by simp) _ (fun x ↦ by simp [G, hst]) _

/-- **The argument principle on a surface with boundary.** Let `X` be compact Hausdorff, let
`ι : M → X` be an open embedding of a surface oriented by `o`, and let the complement `∂X` of
`ι(M)` be collared. Let `L` be a real plane bundle over `X`, with a model fibre `F` of real
dimension `2`, oriented by `oL`, with a frame over all
of `X`: linear isomorphisms `τ x : L_x ≃ ℂ`, continuous on the total space, that carry `oL` to
`Complex.orientation`. Let `t` be a continuous section of `L` whose zeros lie in `ι(M)`, finitely
many. Then the sum over the zeros of `t ∘ ι` of the local indices of the pull-back of `t` along `ι`
is the boundary degree of `u = τ t / |τ t|` on `∂X`. -/
theorem sum_sectionIndex_eq_boundaryDegree (oL : VectorBundleOrientation F L (Fin 2))
    (hF : finrank ℝ F = 2)
    (o : HomologicalOrientation M E 2) (hn : finrank ℝ E = 2) (hι : IsOpenEmbedding ι)
    (hιf : range ι = (range f)ᶜ) (hf : IsCollared f)
    {τ : ∀ x, L x ≃L[ℝ] ℂ} (hτ : Continuous fun v : TotalSpace F L ↦ τ v.proj v.snd)
    (hτo : ∀ x, Orientation.map (Fin 2) (τ x).toLinearEquiv (oL x) = Complex.orientation)
    {t : ∀ x, L x} (ht : Continuous fun x ↦ TotalSpace.mk' F x (t x))
    (hZ : {x : M | t (ι x) = 0}.Finite) (hZι : ∀ x, t x = 0 → x ∈ range ι)
    {u : C(↥((range ι)ᶜ : Set X), Circle)}
    (hu : ∀ z, (u z : ℂ) = ‖τ z (t z)‖⁻¹ • τ z (t z)) :
    ∑ z ∈ hZ.toFinset, (oL.pullback ⟨ι, hι.continuous⟩).sectionIndex hF o
        (s := fun x ↦ t (ι x)) (Pullback.continuous_iff.2 ⟨continuous_id, ht.comp hι.continuous⟩)
        z =
      o.boundaryDegree hn hι hιf hf u := by
  set G : C(X, ℂ) := ⟨fun x ↦ τ x (t x), hτ.comp ht⟩
  have hG : G ⁻¹' {0} ⊆ range ι := fun x hx ↦ hZι x ((τ x).map_eq_zero_iff.1 hx)
  -- The section is named, with the fibres of the pull-back, so that every term is type-correct.
  set s : ∀ x, ((⟨ι, hι.continuous⟩ : C(M, X)) *ᵖ L) x := fun x ↦ t (ι x)
  have hs : Continuous fun x ↦ TotalSpace.mk' F x (s x) :=
    Pullback.continuous_iff.2 ⟨continuous_id, ht.comp hι.continuous⟩
  suffices key : o.boundaryDegree hn hι hιf hf u = ∑ z ∈ hZ.toFinset,
      (oL.pullback ⟨ι, hι.continuous⟩).sectionIndex hF o hs z from
    key.symm
  refine HomologicalOrientation.boundaryDegree_eq_of_localHomologyMap_eq_zsmul o hn hι hιf hf hG
    hu ?_
  rw [localHomologyMap_fundamentalClassRel_eq_sum oL hF o hn hι hιf hf hτ hτo ht hZ hZι hG
    (fun _ ↦ rfl) hs]
  -- Both sides scale by `ℤ` through `zsmul`, the action of `AddCommGroup.toIntModule`, not
  -- through the module structure of the homology that instance search finds.
  exact (@Finset.sum_smul _ ℤ _ _ _ (AddCommGroup.toIntModule _) _ _ _).symm

end ArgumentPrinciple

end TauCeti.VectorBundleOrientation

end
