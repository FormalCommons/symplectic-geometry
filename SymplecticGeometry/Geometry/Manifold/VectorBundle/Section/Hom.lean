/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.FrameCover
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
import SymplecticGeometry.Geometry.Manifold.ContMDiffMap.Chart.CodRestrict
import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Comp
import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.WithSeminorms

/-!
# Sections of a Hom bundle, read on the total space

A section `A` of the bundle `Hom(V, W)` of continuous linear maps acts on the total space of `V`
by the `C^n` map `v ↦ ⟨v.proj, A v.proj v.snd⟩` (`ContMDiffSection.totalSpaceMap`). When `V` has
finite rank, the frame topology on sections of `Hom(V, W)` is controlled by these maps of total
spaces: a family of sections is continuous for Tau Ceti's `ContMDiffSection.frameTopology`, for
any frame system, as soon as the family of maps of total spaces is continuous for the weak Whitney
topology (`ContMDiffSection.continuous_frameTopology_of_continuous_totalSpaceMap`).

By `ContMDiffSection.frameTopology_le_of_cover`, the topology of the covering frames of
`Hom(V, W)` induced by the frames `trivializationAt` of `V` and of `W` is finer than that of any
frame system, so it suffices to prove continuity for those frames. In such a frame, the coefficient
of `A` at `y`, evaluated on a basis vector `b j` of the fibre model of `V`, is the fibre
coordinate in `W` of the image of the point of `V` over `y` with coordinate `b j`. It is thus a
fixed `C^n` map composed with the map of total spaces and with a fixed `C^n` section of `V`, and
the frame coefficient is a finite sum of such maps tensored with the dual basis. Tau Ceti's
continuity of composition in the weak Whitney topology concludes.

## Main definitions and results

* `Bundle.Trivialization.frameCoordinates_continuousLinearMap_apply`: the frame coefficient of a
  section of `Hom(V, W)`, in the trivialization induced by trivializations of `V` and `W`,
  applied to a vector.
* `ContMDiffSection.totalSpaceMap`, with `ContMDiffSection.totalSpaceMap_apply`
* `ContMDiffSection.continuous_frameTopology_of_continuous_totalSpaceMap`

## References

* [M. W. Hirsch, *Differential Topology*][Hirsch1976], Chapter 2, §1 (the weak topology on
  spaces of `C^r` maps, as Tau Ceti builds it)
-/

public section

open Bundle Set TopologicalSpace
open scoped ContDiff Manifold TauCeti.ManifoldWeakWhitney

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F₁ V)]
  [FiberBundle F₁ V] [VectorBundle 𝕜 F₁ V]
  {W : M → Type*} [∀ x, AddCommGroup (W x)] [∀ x, Module 𝕜 (W x)]
  [∀ x, TopologicalSpace (W x)] [∀ x, IsTopologicalAddGroup (W x)]
  [∀ x, ContinuousSMul 𝕜 (W x)] [TopologicalSpace (TotalSpace F₂ W)]
  [FiberBundle F₂ W] [VectorBundle 𝕜 F₂ W]
  {n : ℕ∞ω} [ContMDiffVectorBundle n F₁ V I] [ContMDiffVectorBundle n F₂ W I] [IsManifold I n M]

namespace Bundle.Trivialization

omit [IsManifold I n M] in
/-- The coefficient of a section of `Hom(V, W)` in the trivialization induced by trivializations
`e₁` of `V` and `e₂` of `W`, applied to a vector `w` of the fibre model of `V`, is the coordinate
in `e₂` of the section applied to the point of `V` with coordinate `w` in `e₁`. -/
theorem frameCoordinates_continuousLinearMap_apply
    (e₁ : Trivialization F₁ (π F₁ V)) [MemTrivializationAtlas e₁]
    (e₂ : Trivialization F₂ (π F₂ W)) [MemTrivializationAtlas e₂] {U : Opens M}
    (hU : (U : Set M) ⊆ (e₁.continuousLinearMap (RingHom.id 𝕜) e₂).baseSet)
    (A : Cₛ^n⟮I; F₁ →L[𝕜] F₂, fun x ↦ V x →L[𝕜] W x⟯) (y : U) (w : F₁) :
    (e₁.continuousLinearMap (RingHom.id 𝕜) e₂).frameCoordinates hU A y w =
      (e₂ ⟨(y : M), A y (e₁.symm (y : M) w)⟩).2 := by
  have hy : (y : M) ∈ e₁.baseSet ∩ e₂.baseSet := hU y.property
  rw [frameCoordinates_apply, continuousLinearMap_apply]
  simp [continuousLinearMapAt_apply, symmL_apply, hy.1, hy.2, coe_linearMapAt_of_mem]

end Bundle.Trivialization

namespace ContMDiffSection

omit [IsManifold I n M] in
/-- A section `A` of `Hom(V, W)`, as the `C^n` map `v ↦ ⟨v.proj, A v.proj v.snd⟩` from the total
space of `V` to that of `W`. -/
noncomputable def totalSpaceMap (A : Cₛ^n⟮I; F₁ →L[𝕜] F₂, fun x ↦ V x →L[𝕜] W x⟯) :
    C^n⟮I.prod 𝓘(𝕜, F₁), TotalSpace F₁ V; I.prod 𝓘(𝕜, F₂), TotalSpace F₂ W⟯ :=
  ⟨fun v ↦ ⟨v.proj, A v.proj v.snd⟩,
    (A.contMDiff.comp (contMDiff_proj V)).clm_bundle_apply contMDiff_id⟩

omit [ContMDiffVectorBundle n F₁ V I] [ContMDiffVectorBundle n F₂ W I] [IsManifold I n M] in
/-- The map of total spaces of a section `A` of `Hom(V, W)` sends `v` to `A v` in the fibre of
`W` over the same point. -/
@[simp]
theorem totalSpaceMap_apply (A : Cₛ^n⟮I; F₁ →L[𝕜] F₂, fun x ↦ V x →L[𝕜] W x⟯)
    (v : TotalSpace F₁ V) : A.totalSpaceMap v = ⟨v.proj, A v.proj v.snd⟩ :=
  (rfl)

/-- A family of sections `A p` of `Hom(V, W)`, with `V` of finite rank, is continuous for the
frame topology of any frame system as soon as their maps of total spaces
`v ↦ ⟨v.proj, A p v.proj v.snd⟩` depend continuously on `p` for the weak Whitney topology. The
model `E` of the base and the fibre model `F₁` of `V` are locally compact, as finite-dimensional
real models are. -/
theorem continuous_frameTopology_of_continuous_totalSpaceMap [CompleteSpace 𝕜]
    [FiniteDimensional 𝕜 F₁]
    [LocallyCompactSpace E] [LocallyCompactSpace F₁] {ι : Type*}
    (e : ι → Trivialization (F₁ →L[𝕜] F₂) (π (F₁ →L[𝕜] F₂) (fun x ↦ V x →L[𝕜] W x)))
    [∀ i, MemTrivializationAtlas (e i)]
    (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)
    {P : Type*} [TopologicalSpace P] {A : P → Cₛ^n⟮I; F₁ →L[𝕜] F₂, fun x ↦ V x →L[𝕜] W x⟯}
    (hA : Continuous fun p ↦ (A p).totalSpaceMap) :
    letI := frameTopology (I := I) (n := n) e U hU
    Continuous A := by
  let e' : M → Trivialization (F₁ →L[𝕜] F₂) (π (F₁ →L[𝕜] F₂) (fun x ↦ V x →L[𝕜] W x)) :=
    fun x₀ ↦ (trivializationAt F₁ V x₀).continuousLinearMap (RingHom.id 𝕜)
      (trivializationAt F₂ W x₀)
  let U' : M → Opens M := fun x₀ ↦ ⟨_, (e' x₀).open_baseSet⟩
  have hU' : ∀ x₀, (U' x₀ : Set M) ⊆ (e' x₀).baseSet := fun _ ↦ subset_rfl
  have hcover' : ∀ x, ∃ x₀, x ∈ U' x₀ := fun x ↦
    ⟨x, FiberBundle.mem_baseSet_trivializationAt F₁ V x,
      FiberBundle.mem_baseSet_trivializationAt F₂ W x⟩
  refine @Continuous.comp _ _ _ _ (frameTopology (I := I) (n := n) e' U' hU')
    (frameTopology (I := I) (n := n) e U hU) _ _
    (continuous_id_of_le (frameTopology_le_of_cover e' U' hU' hcover' e U hU)) ?_
  refine (continuous_frameTopology_iff_frameCoordinates e' U' hU').mpr fun x₀ ↦ ?_
  let b := Module.finBasis 𝕜 F₁
  let tV := trivializationAt F₁ V x₀
  let tW := trivializationAt F₂ W x₀
  have hy : ∀ y : U' x₀, (y : M) ∈ tV.baseSet ∩ tW.baseSet := fun y ↦ y.property
  -- The point of `V` over `y` with coordinate `b j`, as a `C^n` map on the frame domain.
  let σ : Fin (Module.finrank 𝕜 F₁) → C^n⟮I, U' x₀; I.prod 𝓘(𝕜, F₁), TotalSpace F₁ V⟯ :=
    fun j ↦ ⟨fun y ↦ tV.toOpenPartialHomeomorph.symm ((y : M), b j),
      tV.contMDiffOn_symm.comp_contMDiff (contMDiff_subtypeVal.prodMk contMDiff_const)
        fun y ↦ tV.mem_target.mpr (hy y).1⟩
  have hσ : ∀ j y, σ j y = ⟨(y : M), tV.symm y (b j)⟩ := fun j y ↦ (tV.mk_symm (hy y).1 _).symm
  -- The points of `W` over the base set of `tW`, and their coordinates in `tW`.
  let N : Opens (TotalSpace F₂ W) :=
    ⟨π F₂ W ⁻¹' tW.baseSet, tW.open_baseSet.preimage (FiberBundle.continuous_proj F₂ W)⟩
  let g : C^n⟮I.prod 𝓘(𝕜, F₂), N; 𝓘(𝕜, F₂), F₂⟯ :=
    ⟨fun v ↦ (tW v).2, (contMDiff_snd.comp_contMDiffOn tW.contMDiffOn).comp_contMDiff
      contMDiff_subtypeVal fun v ↦ tW.mem_source.mpr v.property⟩
  let L : Fin (Module.finrank 𝕜 F₁) → C^n⟮𝓘(𝕜, F₂), F₂; 𝓘(𝕜, F₁ →L[𝕜] F₂), F₁ →L[𝕜] F₂⟯ :=
    fun j ↦ ⟨_, (ContinuousLinearMap.smulRightL 𝕜 𝕜 𝕜 F₁ F₂
      (LinearMap.toContinuousLinearMap (b.coord j))).contMDiff⟩
  have hN : ∀ p j y, (A p).totalSpaceMap.comp (σ j) y ∈ N := fun p j y ↦ by
    simp only [ContMDiffMap.comp_apply, totalSpaceMap_apply, hσ]
    exact (hy y).2
  have hc : ∀ j, Continuous fun p ↦
      (L j).comp (g.comp (((A p).totalSpaceMap.comp (σ j)).codRestrict N (hN p j))) := fun j ↦
    (ContMDiffMap.continuous_postcomp_manifoldWeakWhitney (L j)).comp
      ((ContMDiffMap.continuous_postcomp_manifoldWeakWhitney g).comp
        ((ContMDiffMap.continuous_comp_manifoldWeakWhitney.comp
          (hA.prodMk continuous_const)).codRestrict_manifoldWeakWhitney N
            (fun p ↦ hN p j)))
  refine (continuous_finsetSum Finset.univ fun j _ ↦ hc j).congr fun p ↦ ?_
  ext y w
  rw [ContMDiffMap.coe_sum, Finset.sum_apply, FunLike.coe_sum, Finset.sum_apply]
  conv_rhs => rw [← b.sum_repr w, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_smul]
  rw [Bundle.Trivialization.frameCoordinates_continuousLinearMap_apply tV tW (hU' x₀) (A p) y]
  rw [ContMDiffMap.comp_apply, ContMDiffMap.comp_apply]
  simp only [L, g, ContMDiffMap.coeFn_mk, ContMDiffMap.coe_codRestrict_apply,
    ContMDiffMap.comp_apply, hσ, totalSpaceMap_apply]
  simp [tV, tW]

end ContMDiffSection

end
