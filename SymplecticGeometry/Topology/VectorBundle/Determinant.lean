/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Topology.Algebra.Module.Determinant
public import SymplecticGeometry.Topology.FiberBundle.Pullback
public import SymplecticGeometry.Topology.VectorBundle.FiniteRank.Basic
public import SymplecticGeometry.Topology.VectorBundle.FiniteRank.Conjugate
public import SymplecticGeometry.Topology.VectorBundle.FiniteRank.ConjugateExteriorPower
public import SymplecticGeometry.Topology.VectorBundle.FiniteRank.FiniteTrivializingCover
public import SymplecticGeometry.Topology.VectorBundle.FiniteRank.OfBundle
public import SymplecticGeometry.Topology.VectorBundle.FiniteRank.Tensor
public import SymplecticGeometry.Topology.VectorBundle.OfTrivializationAt

/-!
# The determinant line of a vector bundle

For a vector bundle `E` over `B` with finite-dimensional model `G` over `𝕜`,
`SymplecticGeometry.Bundle.detCore 𝕜 G E` is its determinant line `Λ^top E`, as a finite-rank core
of rank one: Tau Ceti's `TauCeti.FiniteRankBundleCore.det` of the core
`TauCeti.FiniteRankBundleCore.ofBundleOfFinrankEq 𝕜 G E rfl` of `E`.

## Main definitions and results

* `detCoreMap`: a fibrewise isomorphism of bundles, continuous on total spaces, induces an
  isomorphism of their determinant lines;
* `detCore_pullback`: the determinant line of a pull-back is the pull-back of the determinant line;
* `detCoreTrivialIso`: the trivial bundle has the trivial determinant line;
* `detCoreIsoOfFinrankEqOne`: the determinant line of a line bundle is the bundle itself;
* `detCoreConjugateIso`: over `ℂ`, the determinant line of the conjugate bundle
  `TauCeti.ConjugateBundle E` is the conjugate of the determinant line of `E`;
* `detCoreConjugateFiberwise` and `continuous_detCoreConjugateFiberwise`: the resulting
  conjugate-linear fibrewise isomorphism between the two determinant lines, continuous on total
  spaces, in the form taken by
  `TauCeti.complexEulerClass_eq_neg_of_finrank_eq_one_of_conjugateFiberwise`;
* `HasFiniteTrivializingCover.detCore`: the determinant line of a bundle with a finite trivializing
  cover has one. Its charts are those of the preferred trivializations of `E`, so the proof first
  makes the members of the given cover the preferred trivializations of `E`
  (`VectorBundle.ofTrivializationAt`), and then carries the cover of the resulting determinant
  line back along `detCoreMap` of the identity (`HasFiniteTrivializingCover.of_iso`);
* `detCoreProdIso`: the determinant line of the direct sum `E₁ ×ᵇ E₂` is the tensor product
  `TauCeti.FiniteRankBundleCore.tensor` of the determinant lines of `E₁` and `E₂`;
* `detCoreProdFiberEquiv` and `continuous_detCoreProdFiberEquiv`: the resulting linear isomorphism
  from the fibres of the determinant line of `E₁ ×ᵇ E₂` to the tensor products of the fibres of the
  determinant lines, continuous from its total space to that of Tau Ceti's tensor product bundle,
  in the form taken by `TauCeti.complexEulerClass_eq_of_fiberwise`;
* `fiberMap_detCoreMap_trans_symm_hom`: for two fibrewise isomorphisms `Φ` and `Ψ` of bundles
  with the same model, `detCoreMap Ψ ≪≫ (detCoreMap Φ)⁻¹` acts on each fibre as multiplication by
  the determinant of `Φ⁻¹ ∘ Ψ`;
* `fiberMap_detCoreMap_hom_apply`: for bundles with the same model `G`, `detCoreMap Φ` acts on
  each fibre as the compound matrix in degree `finrank 𝕜 G` of the fibre map of the induced
  isomorphism of cores;
* `fiberMap_detCoreTrivialIso_inv_const`: the inverse of `detCoreTrivialIso` preserves constant
  sections.

## The determinant section of a frame

A frame of `E` along a continuous map `f : X → B`, in the sense of Tau Ceti's
`Topology/VectorBundle/Complex/Clutching.lean`, is a family `Φ y : G ≃ E (f y)` that is continuous
from `X × G` to the total space of `E`. It trivializes the pull-back of the determinant line
(`detCoreFrameIso`), and so gives the section `detCoreFrameSection f Φ hΦ` of that pull-back, the
top wedge of the frame. This section is continuous on total spaces
(`continuous_detCoreFrameSection`), also when read in the determinant line of `E` itself
(`continuous_totalSpaceMk_detCoreFrameSection`), and vanishes nowhere
(`detCoreFrameSection_ne_zero`). For a second frame `Ψ`, the section of `Ψ` at `y` is that of `Φ`
times the determinant of `Ψ y ∘ (Φ y)⁻¹` (`detCoreFrameSection_eq_det_smul`). This change-of-frame
rule follows Tau Ceti's `TauCeti.clutchingFunction_eq_mul_normalizedDet_inv`, which compares the
clutching functions of two frames through the automorphism `(φ y)⁻¹ ∘ ψ y` of the model fibre.
The same factor is the determinant of `(Φ y)⁻¹ ∘ Ψ y` on the model `G`
(`ContinuousLinearEquiv.det_coe_trans_symm`). It depends continuously on `y`, since
`(Φ y)⁻¹ ∘ Ψ y` does (Tau Ceti's `TauCeti.continuous_trans_symm_of_continuous_frame`) and the
determinant is continuous (`ContinuousLinearMap.continuous_det`).

In coordinates, the value of the section at `y` is the top compound matrix of `Φ y` read in the
preferred trivialization of `E` at `f y` (`detCoreFrameSection_apply`); each of its coordinates
is the determinant of `Φ y` followed by the preferred chart of `E` at `f y`, an automorphism of
`G` (`detCoreFrameSection_apply_eq_det`). It depends only on `f y` and `Φ y`, so the section is
natural under reparametrization of the frame (`detCoreFrameSection_comp`).

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §14 (the first Chern class through the determinant line).
* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.7.
-/

public section

open Bundle CategoryTheory Module TauCeti TauCeti.FiniteRankBundleCore TauCeti.Conjugate
open scoped TensorProduct

namespace TauCeti.CoordinateFunctor

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {𝕜' : Type*} [NontriviallyNormedField 𝕜']
  (Φ : CoordinateFunctor 𝕜 𝕜') {B : Type*} [TopologicalSpace B]

/-- The inverse of `mapCoreTrivialIso`, preceded by the identification of trivial cores of equal
ranks `Φ.rank n = m`, acts on each fibre by reindexing the coordinates along that equality. -/
theorem fiberMap_mapCoreTrivialIso_trans_eqToIso_inv_apply {n m : ℕ} (h : Φ.rank n = m) (x : B)
    (v : Fin (FiniteRankBundleCore.trivial 𝕜' B m).rank → 𝕜') :
    (Φ.mapCoreTrivialIso B n ≪≫
      eqToIso (congrArg (FiniteRankBundleCore.trivial 𝕜' B) h)).inv.fiberMap x v =
      fun i ↦ v (Fin.cast h i) := by
  rw [Iso.trans_inv, FiniteRankBundleCore.fiberMap_comp, ContinuousLinearMap.comp_apply,
    fiberMap_mapCoreTrivialIso_inv, eqToIso.inv]
  funext i
  exact FiniteRankBundleCore.fiberMap_eqToHom_apply
    (congrArg (FiniteRankBundleCore.trivial 𝕜' B) h).symm x v i

end TauCeti.CoordinateFunctor

namespace SymplecticGeometry

namespace Bundle

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {B : Type*} [TopologicalSpace B]

section Basic

variable (G : Type*) [NormedAddCommGroup G] [NormedSpace 𝕜 G] [FiniteDimensional 𝕜 G]
  (E : B → Type*) [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
  [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace G E)]
  [FiberBundle G E] [VectorBundle 𝕜 G E]

/-- The determinant line `Λ^top E` of a vector bundle `E` with finite-dimensional model `G`: the
top exterior power of its finite-rank core. -/
noncomputable def detCore : FiniteRankBundleCore 𝕜 B :=
  (ofBundleOfFinrankEq 𝕜 G E rfl).det

theorem detCore_def : detCore 𝕜 G E = (ofBundleOfFinrankEq 𝕜 G E rfl).det := (rfl)

/-- The determinant line is a line bundle. -/
@[simp] theorem rank_detCore : (detCore 𝕜 G E).rank = 1 :=
  rank_det _

/-- The model of the determinant line has dimension `0 + 1`, the form in which Tau Ceti's Euler
classes take the rank. -/
theorem finrank_detCore : finrank 𝕜 (Fin (detCore 𝕜 G E).rank → 𝕜) = 0 + 1 := by
  simp

/-- The determinant line is the exterior power of `E` in the degree of its rank. -/
theorem detCore_eq_exteriorPower :
    detCore 𝕜 G E = (exteriorPower 𝕜 B (finrank 𝕜 G)).obj (ofBundleOfFinrankEq 𝕜 G E rfl) :=
  det_def _

/-- The determinant line is the exterior power of the core `ofBundleOfFinrankEq 𝕜 G E h` in
degree `n`, for any proof `h` that `G` has dimension `n`. -/
theorem detCore_eq_exteriorPower_of_finrank_eq {n : ℕ} (h : finrank 𝕜 G = n) :
    detCore 𝕜 G E = (exteriorPower 𝕜 B n).obj (ofBundleOfFinrankEq 𝕜 G E h) := by
  subst h
  exact detCore_eq_exteriorPower 𝕜 G E

end Basic

section Map

variable {G₀ : Type*} [NormedAddCommGroup G₀] [NormedSpace 𝕜 G₀] [FiniteDimensional 𝕜 G₀]
  {E₀ : B → Type*} [∀ x, AddCommMonoid (E₀ x)] [∀ x, Module 𝕜 (E₀ x)]
  [∀ x, TopologicalSpace (E₀ x)] [TopologicalSpace (TotalSpace G₀ E₀)]
  [FiberBundle G₀ E₀] [VectorBundle 𝕜 G₀ E₀]
  {G₁ : Type*} [NormedAddCommGroup G₁] [NormedSpace 𝕜 G₁] [FiniteDimensional 𝕜 G₁]
  {E₁ : B → Type*} [∀ x, AddCommMonoid (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [∀ x, TopologicalSpace (E₁ x)] [TopologicalSpace (TotalSpace G₁ E₁)]
  [FiberBundle G₁ E₁] [VectorBundle 𝕜 G₁ E₁]
  (hG : finrank 𝕜 G₁ = finrank 𝕜 G₀) (Φ : ∀ x, E₀ x ≃L[𝕜] E₁ x)
  (hΦ : Continuous fun p : TotalSpace G₀ E₀ ↦ TotalSpace.mk' G₁ (E := E₁) p.proj (Φ p.proj p.snd))

variable {𝕜} in
/-- A fibrewise continuous linear equivalence of bundles, continuous on total spaces, induces an
isomorphism of their determinant lines: the top exterior power of the induced isomorphism of
cores. The two bundles may have different models `G₀` and `G₁`, of the same dimension. -/
noncomputable def detCoreMap : detCore 𝕜 G₀ E₀ ≅ detCore 𝕜 G₁ E₁ :=
  eqToIso (detCore_eq_exteriorPower 𝕜 G₀ E₀) ≪≫
    (exteriorPower 𝕜 B (finrank 𝕜 G₀)).mapIso (ofBundleOfFinrankEqIso rfl hG Φ hΦ) ≪≫
    eqToIso (detCore_eq_exteriorPower_of_finrank_eq 𝕜 G₁ E₁ hG).symm

theorem detCoreMap_def :
    detCoreMap hG Φ hΦ = eqToIso (detCore_eq_exteriorPower 𝕜 G₀ E₀) ≪≫
      (exteriorPower 𝕜 B (finrank 𝕜 G₀)).mapIso (ofBundleOfFinrankEqIso rfl hG Φ hΦ) ≪≫
      eqToIso (detCore_eq_exteriorPower_of_finrank_eq 𝕜 G₁ E₁ hG).symm := (rfl)

end Map

section SameModel

variable {𝕜} {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [FiniteDimensional 𝕜 G]
  {E : B → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)]
  [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace G E)]
  [FiberBundle G E] [VectorBundle 𝕜 G E]
  {E₁ : B → Type*} [∀ x, AddCommMonoid (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [∀ x, TopologicalSpace (E₁ x)] [TopologicalSpace (TotalSpace G E₁)]
  [FiberBundle G E₁] [VectorBundle 𝕜 G E₁]

/-- **Change of fibrewise isomorphism on the determinant line.** For two fibrewise isomorphisms
`Φ Ψ : E x ≃ E₁ x` of bundles with the same model, continuous on total spaces, the automorphism
`detCoreMap Ψ ≪≫ (detCoreMap Φ)⁻¹` of the determinant line of `E` acts on the fibre over `x` as
multiplication by the determinant of `(Φ x)⁻¹ ∘ Ψ x`. -/
theorem fiberMap_detCoreMap_trans_symm_hom (Φ Ψ : ∀ x, E x ≃L[𝕜] E₁ x)
    (hΦ : Continuous fun p : TotalSpace G E ↦ TotalSpace.mk' G (E := E₁) p.proj (Φ p.proj p.snd))
    (hΨ : Continuous fun p : TotalSpace G E ↦ TotalSpace.mk' G (E := E₁) p.proj (Ψ p.proj p.snd))
    (x : B) :
    (detCoreMap rfl Ψ hΨ ≪≫ (detCoreMap rfl Φ hΦ).symm).hom.fiberMap x =
      LinearMap.det ((Ψ x).trans (Φ x).symm : E x →ₗ[𝕜] E x) • ContinuousLinearMap.id 𝕜 _ := by
  rw [detCoreMap_def, detCoreMap_def]
  refine fiberMap_trans_trans_symm_hom _ _ _ _ ?_
  rw [← Functor.mapIso_symm, ← Functor.mapIso_trans, Functor.mapIso_hom]
  refine (fiberMap_exteriorPower_map _ _ x).trans ?_
  refine (ContinuousLinearMap.exteriorPowerCoords_self _).trans ?_
  congr 1
  rw [Iso.trans_hom, Iso.symm_hom, fiberMap_comp, fiberMap_ofBundleOfFinrankEqIso_inv,
    fiberMap_ofBundleOfFinrankEqIso_hom, ← ContinuousLinearEquiv.det_coe_symm_trans_trans
      (ofBundleOfFinrankEqFiberEquiv 𝕜 G E rfl x).symm ((Ψ x).trans (Φ x).symm)]
  refine congrArg LinearMap.det (LinearMap.ext fun v ↦ ?_)
  exact congrArg (fun w ↦ (ofBundleOfFinrankEqFiberEquiv 𝕜 G E rfl x).symm ((Φ x).symm w))
    ((ofBundleOfFinrankEqFiberEquiv 𝕜 G E₁ rfl x).apply_symm_apply
      (Ψ x (ofBundleOfFinrankEqFiberEquiv 𝕜 G E rfl x v)))

/-- On each fibre, `detCoreMap` of a fibrewise isomorphism `Φ` of bundles with the same model `G`
is the compound matrix, in degree `finrank 𝕜 G`, of the fibre map of the induced isomorphism of
cores `ofBundleOfFinrankEqIso`, read through the identifications of the determinant lines with
exterior powers (`detCore_eq_exteriorPower`). -/
theorem fiberMap_detCoreMap_hom_apply (Φ : ∀ x, E x ≃L[𝕜] E₁ x)
    (hΦ : Continuous fun p : TotalSpace G E ↦ TotalSpace.mk' G (E := E₁) p.proj (Φ p.proj p.snd))
    (x : B) (v : Fin (detCore 𝕜 G E).rank → 𝕜) (i : Fin (detCore 𝕜 G E₁).rank) :
    (detCoreMap rfl Φ hΦ).hom.fiberMap x v i =
      ((ofBundleOfFinrankEqIso rfl rfl Φ hΦ).hom.fiberMap x).exteriorPowerCoords (finrank 𝕜 G)
        (fun j ↦ v (Fin.cast (congrArg rank (detCore_eq_exteriorPower 𝕜 G E)).symm j))
        (Fin.cast (congrArg rank (detCore_eq_exteriorPower 𝕜 G E₁)) i) := by
  rw [detCoreMap_def, Iso.trans_hom, Iso.trans_hom, fiberMap_comp, fiberMap_comp,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, Functor.mapIso_hom,
    fiberMap_exteriorPower_map, eqToIso.hom, eqToIso.hom, fiberMap_eqToHom_apply]
  exact congrArg (fun w ↦ ((ofBundleOfFinrankEqIso rfl rfl Φ hΦ).hom.fiberMap x).exteriorPowerCoords
    (finrank 𝕜 G) w (Fin.cast (congrArg rank (detCore_eq_exteriorPower 𝕜 G E₁)) i))
    (funext (fiberMap_eqToHom_apply _ x v))

end SameModel

section FiniteTrivializingCover

open Set

variable {𝕜} {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [FiniteDimensional 𝕜 G]
  {E : B → Type*} [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
  [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace G E)]
  [FiberBundle G E] [VectorBundle 𝕜 G E]

/-- If the preferred trivializations `trivializationAt G E x` of a vector bundle are finitely
many, its determinant line has a finite trivializing cover. -/
theorem hasFiniteTrivializingCover_detCore_of_finite_range
    (h : (range (trivializationAt G E)).Finite) :
    HasFiniteTrivializingCover 𝕜 (Fin (detCore 𝕜 G E).rank → 𝕜) (detCore 𝕜 G E).core.Fiber := by
  have := h.to_subtype
  -- A point of `B` at which each trivialization of the range is the preferred one.
  choose y hy using fun t : range (trivializationAt G E) ↦ t.property
  refine .of_finite (fun t ↦ (detCore 𝕜 G E).core.localTriv (y t))
    (eq_univ_of_forall fun x ↦ mem_iUnion.2 ⟨⟨_, mem_range_self x⟩, ?_⟩)
  rw [detCore_def, localTriv_baseSet_det, VectorBundleCore.baseSet_at,
    localTriv_baseSet_ofBundleOfFinrankEq, hy]
  exact mem_baseSet_trivializationAt G E x

/-- If a vector bundle with finite-dimensional model has a finite trivializing cover, so does its
determinant line. -/
theorem HasFiniteTrivializingCover.detCore (h : HasFiniteTrivializingCover 𝕜 G E) :
    HasFiniteTrivializingCover 𝕜 (Fin (detCore 𝕜 G E).rank → 𝕜) (detCore 𝕜 G E).core.Fiber := by
  obtain ⟨s, hlin, hcover⟩ := (hasFiniteTrivializingCover_def 𝕜 G E).1 h
  have hc : ∀ x, ∃ e : s, x ∈ (e : Trivialization G (π G E)).baseSet := fun x ↦ by
    simpa using (hcover ▸ mem_univ x : x ∈ ⋃ e ∈ s, e.baseSet)
  choose c hc using hc
  have : ∀ x, (c x : Trivialization G (π G E)).IsLinear 𝕜 := fun x ↦ hlin _ (c x).property
  -- The vector bundle structure on `E` with preferred trivializations `c x`, taken from `s`. It is
  -- passed explicitly below, since instance search would find the given structure instead.
  have VB := VectorBundle.ofTrivializationAt (𝕜 := 𝕜) (fun x ↦ (c x : Trivialization G (π G E))) hc
  have hfin : (range fun x ↦ (c x : Trivialization G (π G E))).Finite :=
    s.finite_toSet.subset (range_subset_iff.2 fun x ↦ (c x).property)
  rw [← funext (FiberBundle.trivializationAt_ofTrivializationAt _ hc)] at hfin
  -- The identity of `E` identifies the determinant lines of the two structures.
  exact (@hasFiniteTrivializingCover_detCore_of_finite_range 𝕜 _ _ B _ G _ _ _ E _ _ _ _
    (FiberBundle.ofTrivializationAt _ hc) VB hfin).of_iso
    (@detCoreMap 𝕜 _ _ B _ G _ _ _ E _ _ _ _ (FiberBundle.ofTrivializationAt _ hc) VB
      G _ _ _ E _ _ _ _ _ _ rfl (fun x ↦ ContinuousLinearEquiv.refl 𝕜 (E x)) continuous_id)

end FiniteTrivializingCover

section Pullback

variable {X : Type*} [TopologicalSpace X]
  (G : Type*) [NormedAddCommGroup G] [NormedSpace 𝕜 G] [FiniteDimensional 𝕜 G]
  (E : B → Type*) [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
  [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace G E)]
  [FiberBundle G E] [VectorBundle 𝕜 G E]

/-- The determinant line of the pull-back `f *ᵖ E` is, strictly, the pull-back of the determinant
line of `E`. -/
theorem detCore_pullback (f : C(X, B)) :
    detCore 𝕜 G ((⇑f) *ᵖ E) = (detCore 𝕜 G E).pullback f := by
  rw [detCore_eq_exteriorPower, detCore_eq_exteriorPower, ← pullback_ofBundleOfFinrankEq]
  exact congrArg (fun F ↦ F.obj (ofBundleOfFinrankEq 𝕜 G E rfl))
    (CoordinateFunctor.functor_comp_pullbackFunctor (CoordinateFunctor.exteriorPower 𝕜 _) f).symm

end Pullback

section Trivial

variable (B) (G : Type*) [NormedAddCommGroup G] [NormedSpace 𝕜 G] [FiniteDimensional 𝕜 G]

/-- The determinant line of the trivial bundle `B × G` is the trivial line bundle. -/
noncomputable def detCoreTrivialIso : detCore 𝕜 G (Bundle.Trivial B G) ≅ trivial 𝕜 B 1 :=
  eqToIso ((detCore_eq_exteriorPower 𝕜 G _).trans
      (congrArg (exteriorPower 𝕜 B (finrank 𝕜 G)).obj (ofBundleOfFinrankEq_trivial B rfl))) ≪≫
    (CoordinateFunctor.exteriorPower 𝕜 (finrank 𝕜 G)).mapCoreTrivialIso B (finrank 𝕜 G) ≪≫
    eqToIso (congrArg (trivial 𝕜 B) (Nat.choose_self _))

theorem detCoreTrivialIso_def :
    detCoreTrivialIso 𝕜 B G = eqToIso ((detCore_eq_exteriorPower 𝕜 G _).trans
        (congrArg (exteriorPower 𝕜 B (finrank 𝕜 G)).obj (ofBundleOfFinrankEq_trivial B rfl))) ≪≫
      (CoordinateFunctor.exteriorPower 𝕜 (finrank 𝕜 G)).mapCoreTrivialIso B (finrank 𝕜 G) ≪≫
      eqToIso (congrArg (trivial 𝕜 B) (Nat.choose_self _)) := (rfl)

/-- The inverse of `detCoreTrivialIso` carries a constant section of the trivial line to the same
constant, read in the coordinates of the determinant line of `B × G`. -/
theorem fiberMap_detCoreTrivialIso_inv_const (x : B) (c : 𝕜) :
    (detCoreTrivialIso 𝕜 B G).inv.fiberMap x (fun _ ↦ c) = fun _ ↦ c := by
  rw [detCoreTrivialIso_def]
  simp only [Iso.trans_inv, fiberMap_comp, eqToIso.inv, ContinuousLinearMap.comp_apply]
  funext i
  rw [fiberMap_eqToHom_apply]
  exact congrFun (CoordinateFunctor.fiberMap_mapCoreTrivialIso_trans_eqToIso_inv_apply _
    (Nat.choose_self _) x _) _

end Trivial

section Line

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [FiniteDimensional 𝕜 G]
  (E : B → Type*) [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
  [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace G E)]
  [FiberBundle G E] [VectorBundle 𝕜 G E]

/-- The determinant line of a line bundle is the bundle itself: in rank one the top exterior power
is the first one (`TauCeti.FiniteRankBundleCore.exteriorPowerOneIso`). -/
noncomputable def detCoreIsoOfFinrankEqOne (h : finrank 𝕜 G = 1) :
    detCore 𝕜 G E ≅ ofBundleOfFinrankEq 𝕜 G E rfl :=
  eqToIso ((detCore_eq_exteriorPower 𝕜 G E).trans
      (congrArg (fun k ↦ (exteriorPower 𝕜 B k).obj (ofBundleOfFinrankEq 𝕜 G E rfl)) h)) ≪≫
    exteriorPowerOneIso _

theorem detCoreIsoOfFinrankEqOne_def (h : finrank 𝕜 G = 1) :
    detCoreIsoOfFinrankEqOne 𝕜 E h = eqToIso ((detCore_eq_exteriorPower 𝕜 G E).trans
        (congrArg (fun k ↦ (exteriorPower 𝕜 B k).obj (ofBundleOfFinrankEq 𝕜 G E rfl)) h)) ≪≫
      exteriorPowerOneIso _ := (rfl)

end Line

section Conjugate

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  (E : B → Type*) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)] [∀ x, TopologicalSpace (E x)]
  [TopologicalSpace (TotalSpace G E)] [FiberBundle G E] [VectorBundle ℂ G E]

/-- The determinant line of the conjugate bundle is the conjugate of the determinant line. -/
noncomputable def detCoreConjugateIso :
    detCore ℂ (Conjugate G) (ConjugateBundle E) ≅ (conjugate B).obj (detCore ℂ G E) :=
  eqToIso (detCore_eq_exteriorPower ℂ (Conjugate G) (ConjugateBundle E)) ≪≫
    (exteriorPower ℂ B (finrank ℂ (Conjugate G))).mapIso
      (ofBundleOfFinrankEqConjugateIso E rfl rfl) ≪≫
    eqToIso ((congrArg (fun k ↦ (exteriorPower ℂ B k).obj
      ((conjugate B).obj (ofBundleOfFinrankEq ℂ G E rfl)))
      (finrank_complex (V := G))).trans
        (det_def _).symm) ≪≫
    detConjugateIso _ ≪≫ eqToIso (congrArg (conjugate B).obj (detCore_def ℂ G E).symm)

theorem detCoreConjugateIso_def :
    detCoreConjugateIso E =
      eqToIso (detCore_eq_exteriorPower ℂ (Conjugate G) (ConjugateBundle E)) ≪≫
        (exteriorPower ℂ B (finrank ℂ (Conjugate G))).mapIso
          (ofBundleOfFinrankEqConjugateIso E rfl rfl) ≪≫
        eqToIso ((congrArg (fun k ↦ (exteriorPower ℂ B k).obj
          ((conjugate B).obj (ofBundleOfFinrankEq ℂ G E rfl)))
      (finrank_complex (V := G))).trans
            (det_def _).symm) ≪≫
        detConjugateIso _ ≪≫ eqToIso (congrArg (conjugate B).obj (detCore_def ℂ G E).symm) :=
  (rfl)

/-- The conjugate-linear fibrewise isomorphism from the determinant line of the conjugate bundle
to the determinant line of `E`: `detCoreConjugateIso` on each fibre, followed by complex
conjugation of the coordinate. -/
noncomputable def detCoreConjugateFiberwise (x : B) :
    (detCore ℂ (Conjugate G) (ConjugateBundle E)).core.Fiber x ≃L⋆[ℂ]
      (detCore ℂ G E).core.Fiber x :=
  (isoFiberEquiv (detCoreConjugateIso E) x).trans
    (starL ℂ : (Fin (detCore ℂ G E).rank → ℂ) ≃L⋆[ℂ] (Fin (detCore ℂ G E).rank → ℂ))

@[simp] theorem detCoreConjugateFiberwise_apply (x : B)
    (v : (detCore ℂ (Conjugate G) (ConjugateBundle E)).core.Fiber x) :
    detCoreConjugateFiberwise E x v = star ((detCoreConjugateIso E).hom.fiberMap x v) := by
  exact congrArg star (isoFiberEquiv_apply (detCoreConjugateIso E) x v)

/-- The conjugate-linear isomorphism `detCoreConjugateFiberwise` is continuous on total spaces. -/
theorem continuous_detCoreConjugateFiberwise :
    Continuous fun p : TotalSpace (Fin (detCore ℂ (Conjugate G) (ConjugateBundle E)).rank → ℂ)
        (detCore ℂ (Conjugate G) (ConjugateBundle E)).core.Fiber ↦
      TotalSpace.mk' (Fin (detCore ℂ G E).rank → ℂ) (E := (detCore ℂ G E).core.Fiber) p.proj
        (detCoreConjugateFiberwise E p.proj p.snd) :=
  ((continuous_star_conjugate (detCore ℂ G E)).comp
    (continuous_isoFiberEquiv (detCoreConjugateIso E))).congr fun p ↦ by
      rw [detCoreConjugateFiberwise_apply]
      -- The two sides agree up to the projections of `TotalSpace.mk'`, the coercion of `starL`,
      -- and the definitional equality of the ranks of `detCore` and of its conjugate.
      exact congrArg (fun v : Fin (detCore ℂ G E).rank → ℂ ↦
        TotalSpace.mk' (Fin (detCore ℂ G E).rank → ℂ) (E := (detCore ℂ G E).core.Fiber) p.proj
          (star v : Fin (detCore ℂ G E).rank → ℂ))
        (isoFiberEquiv_apply (detCoreConjugateIso E) p.proj p.snd)

end Conjugate

section Prod

variable {G₁ : Type*} [NormedAddCommGroup G₁] [NormedSpace 𝕜 G₁] [FiniteDimensional 𝕜 G₁]
  (E₁ : B → Type*) [∀ x, AddCommMonoid (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [∀ x, TopologicalSpace (E₁ x)] [TopologicalSpace (TotalSpace G₁ E₁)]
  [FiberBundle G₁ E₁] [VectorBundle 𝕜 G₁ E₁]
  {G₂ : Type*} [NormedAddCommGroup G₂] [NormedSpace 𝕜 G₂] [FiniteDimensional 𝕜 G₂]
  (E₂ : B → Type*) [∀ x, AddCommMonoid (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [∀ x, TopologicalSpace (E₂ x)] [TopologicalSpace (TotalSpace G₂ E₂)]
  [FiberBundle G₂ E₂] [VectorBundle 𝕜 G₂ E₂]

/-- The determinant line of a direct sum is the tensor product of the determinant lines,
`Λ^top (E₁ ⊕ E₂) ≅ Λ^top E₁ ⊗ Λ^top E₂`: the top exterior power of the identification of the
core of `E₁ ×ᵇ E₂` with the Whitney sum of the cores (`ofBundleOfFinrankEqProdIso`), followed by
`TauCeti.FiniteRankBundleCore.detWhitneySumIso`. -/
noncomputable def detCoreProdIso :
    detCore 𝕜 (G₁ × G₂) (E₁ ×ᵇ E₂) ≅ tensor (detCore 𝕜 G₁ E₁) (detCore 𝕜 G₂ E₂) :=
  eqToIso (detCore_eq_exteriorPower_of_finrank_eq 𝕜 _ _
      (finrank_prod (R := 𝕜) (M := G₁) (M' := G₂))) ≪≫
    (exteriorPower 𝕜 B _).mapIso (ofBundleOfFinrankEqProdIso E₁ E₂ rfl rfl _) ≪≫
    eqToIso (det_def _).symm ≪≫ detWhitneySumIso _ _ ≪≫
    eqToIso (by rw [detCore_def, detCore_def])

theorem detCoreProdIso_def :
    detCoreProdIso 𝕜 E₁ E₂ =
      eqToIso (detCore_eq_exteriorPower_of_finrank_eq 𝕜 _ _
          (finrank_prod (R := 𝕜) (M := G₁) (M' := G₂))) ≪≫
        (exteriorPower 𝕜 B _).mapIso (ofBundleOfFinrankEqProdIso E₁ E₂ rfl rfl _) ≪≫
        eqToIso (det_def _).symm ≪≫ detWhitneySumIso _ _ ≪≫
        eqToIso (by rw [detCore_def, detCore_def]) := (rfl)

variable
  [∀ x, TopologicalSpace ((detCore 𝕜 G₁ E₁).core.Fiber x ⊗[𝕜] (detCore 𝕜 G₂ E₂).core.Fiber x)]
  [∀ x, IsModuleTopology 𝕜 ((detCore 𝕜 G₁ E₁).core.Fiber x ⊗[𝕜] (detCore 𝕜 G₂ E₂).core.Fiber x)]

/-- `detCoreProdIso` read on fibres: the linear isomorphism from the fibre of the determinant line
of `E₁ ×ᵇ E₂` to the tensor product of the fibres of the determinant lines of `E₁` and `E₂`. -/
noncomputable def detCoreProdFiberEquiv (x : B) :
    (detCore 𝕜 (G₁ × G₂) (E₁ ×ᵇ E₂)).core.Fiber x ≃L[𝕜]
      (detCore 𝕜 G₁ E₁).core.Fiber x ⊗[𝕜] (detCore 𝕜 G₂ E₂).core.Fiber x :=
  (isoFiberEquiv (detCoreProdIso 𝕜 E₁ E₂) x).trans (tensorFiberEquiv _ _ x)

@[simp] theorem detCoreProdFiberEquiv_apply (x : B)
    (v : (detCore 𝕜 (G₁ × G₂) (E₁ ×ᵇ E₂)).core.Fiber x) :
    detCoreProdFiberEquiv 𝕜 E₁ E₂ x v =
      tensorFiberEquiv _ _ x ((detCoreProdIso 𝕜 E₁ E₂).hom.fiberMap x v) := by
  -- The fibres of the cores are their coordinate spaces by definition, which `exact` sees.
  exact (ContinuousLinearEquiv.trans_apply _ _ v).trans (congrArg _ (isoFiberEquiv_apply _ x v))

/-- The fibrewise isomorphism `detCoreProdFiberEquiv` is continuous from the total space of the
determinant line of `E₁ ×ᵇ E₂` to that of Tau Ceti's tensor product of the determinant lines of
`E₁` and `E₂`. Over `ℂ`, this is the form taken by `TauCeti.complexEulerClass_eq_of_fiberwise`. -/
theorem continuous_detCoreProdFiberEquiv :
    Continuous fun p : TotalSpace (Fin (detCore 𝕜 (G₁ × G₂) (E₁ ×ᵇ E₂)).rank → 𝕜)
        (detCore 𝕜 (G₁ × G₂) (E₁ ×ᵇ E₂)).core.Fiber ↦
      TotalSpace.mk'
        (ProjectiveTensor 𝕜 (Fin (detCore 𝕜 G₁ E₁).rank → 𝕜) (Fin (detCore 𝕜 G₂ E₂).rank → 𝕜))
        (E := fun x ↦ (detCore 𝕜 G₁ E₁).core.Fiber x ⊗[𝕜] (detCore 𝕜 G₂ E₂).core.Fiber x)
        p.proj (detCoreProdFiberEquiv 𝕜 E₁ E₂ p.proj p.snd) :=
  (continuous_tensorFiberEquiv _ _).comp (continuous_isoFiberEquiv (detCoreProdIso 𝕜 E₁ E₂))

end Prod

section Frame

/-! ### The determinant section of a frame -/

variable {𝕜} {X : Type*} [TopologicalSpace X]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [FiniteDimensional 𝕜 G]
  {E : B → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)]
  [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace G E)]
  [FiberBundle G E] [VectorBundle 𝕜 G E]
  (f : C(X, B)) {Φ Ψ : ∀ y, G ≃L[𝕜] E (f y)}
  (hΦ : Continuous fun q : X × G ↦ TotalSpace.mk' G (f q.1) (Φ q.1 q.2))
  (hΨ : Continuous fun q : X × G ↦ TotalSpace.mk' G (f q.1) (Ψ q.1 q.2))

/-- The trivialization of the pull-back of the determinant line along `f` given by a frame `Φ` of
`E` along `f`, a family `Φ y : G ≃ E (f y)` continuous from `X × G` to the total space of `E`:
the trivial line `X × 𝕜` is the determinant line of `X × G` (`detCoreTrivialIso`), which `Φ`
carries to that of `f *ᵖ E` (`detCoreMap`), the pull-back of the determinant line of `E`
(`detCore_pullback`). -/
noncomputable def detCoreFrameIso (Φ : ∀ y, G ≃L[𝕜] E (f y))
    (hΦ : Continuous fun q : X × G ↦ TotalSpace.mk' G (f q.1) (Φ q.1 q.2)) :
    trivial 𝕜 X 1 ≅ (detCore 𝕜 G E).pullback f :=
  (detCoreTrivialIso 𝕜 X G).symm ≪≫
    detCoreMap (E₀ := Trivial X G) (E₁ := (⇑f) *ᵖ E) rfl Φ
      (Pullback.continuous_totalSpaceMk_trivial (φ := fun y ↦ Φ y) hΦ) ≪≫
    eqToIso (detCore_pullback 𝕜 G E f)

theorem detCoreFrameIso_def :
    detCoreFrameIso f Φ hΦ = (detCoreTrivialIso 𝕜 X G).symm ≪≫
      detCoreMap (E₀ := Trivial X G) (E₁ := (⇑f) *ᵖ E) rfl Φ
        (Pullback.continuous_totalSpaceMk_trivial (φ := fun y ↦ Φ y) hΦ) ≪≫
      eqToIso (detCore_pullback 𝕜 G E f) := (rfl)

/-- The **determinant section of a frame**: for a frame `Φ` of `E` along `f`, the section of the
pull-back along `f` of the determinant line `Λ^top E` whose value at `y` is the top wedge of the
images under `Φ y` of the basis of `G` that the determinant line uses, read in the coordinates of
the fibre. It is the image under `detCoreFrameIso` of the constant section `1` of `X × 𝕜`. -/
noncomputable def detCoreFrameSection (Φ : ∀ y, G ≃L[𝕜] E (f y))
    (hΦ : Continuous fun q : X × G ↦ TotalSpace.mk' G (f q.1) (Φ q.1 q.2)) (y : X) :
    Fin ((detCore 𝕜 G E).pullback f).rank → 𝕜 :=
  isoFiberEquiv (detCoreFrameIso f Φ hΦ) y fun _ ↦ 1

theorem detCoreFrameSection_def (y : X) :
    detCoreFrameSection f Φ hΦ y = isoFiberEquiv (detCoreFrameIso f Φ hΦ) y fun _ ↦ 1 := (rfl)

/-- The determinant section of a frame is continuous on total spaces. -/
theorem continuous_detCoreFrameSection :
    Continuous fun y ↦ TotalSpace.mk' (Fin ((detCore 𝕜 G E).pullback f).rank → 𝕜)
      (E := ((detCore 𝕜 G E).pullback f).core.Fiber) y (detCoreFrameSection f Φ hΦ y) :=
  continuous_isoFiberEquiv_const (detCoreFrameIso f Φ hΦ) _

/-- The determinant section of a frame along `f`, read in the determinant line of `E` itself: the
map `y ↦ (f y, detCoreFrameSection f Φ hΦ y)` to the total space of `Λ^top E` is continuous. -/
theorem continuous_totalSpaceMk_detCoreFrameSection :
    Continuous fun y ↦ TotalSpace.mk' (Fin (detCore 𝕜 G E).rank → 𝕜)
      (E := (detCore 𝕜 G E).core.Fiber) (f y) (detCoreFrameSection f Φ hΦ y) :=
  ((continuous_core_pullback_iff _ f).1 (continuous_detCoreFrameSection f hΦ)).2.congr fun y ↦
    pullbackLift_mk _ f y _

/-- The determinant section of a frame vanishes nowhere. -/
theorem detCoreFrameSection_ne_zero (y : X) : detCoreFrameSection f Φ hΦ y ≠ 0 := by
  intro h
  rw [detCoreFrameSection_def] at h
  exact one_ne_zero (congrFun ((isoFiberEquiv _ y).map_eq_zero_iff.1 h) ⟨0, Nat.one_pos⟩)

/-- The trivializations of the determinant line given by two frames `Φ` and `Ψ` along `f`
differ over `y` by the determinant of the automorphism `Ψ y ∘ (Φ y)⁻¹` of `E (f y)`. -/
theorem fiberMap_detCoreFrameIso_trans_symm_hom (y : X) :
    (detCoreFrameIso f Ψ hΨ ≪≫ (detCoreFrameIso f Φ hΦ).symm).hom.fiberMap y =
      LinearMap.det ((Φ y).symm.trans (Ψ y) : E (f y) →ₗ[𝕜] E (f y)) •
        ContinuousLinearMap.id 𝕜 _ := by
  -- `detCoreMap` reads `Φ y` and `Ψ y` as maps from the fibre of `Trivial X G` to that of
  -- `f *ᵖ E`, so its factor is the determinant of `(Φ y)⁻¹ ∘ Ψ y` on `G`; conjugate by `Φ y`.
  have hc : LinearMap.det (((Ψ y : Trivial X G y ≃L[𝕜] ((⇑f) *ᵖ E) y).trans
        (Φ y : Trivial X G y ≃L[𝕜] ((⇑f) *ᵖ E) y).symm : Trivial X G y →ₗ[𝕜] Trivial X G y)) =
      LinearMap.det ((Φ y).symm.trans (Ψ y) : E (f y) →ₗ[𝕜] E (f y)) :=
    ContinuousLinearEquiv.det_coe_trans_symm (Φ y : G ≃L[𝕜] E (f y)) (Ψ y)
  rw [detCoreFrameIso_def, detCoreFrameIso_def, ← hc]
  exact fiberMap_trans_trans_symm_hom _ _ _ _
    (fiberMap_detCoreMap_trans_symm_hom (E := Trivial X G) (E₁ := (⇑f) *ᵖ E) Φ Ψ _ _ y)

/-- **Change of frame.** For two frames `Φ` and `Ψ` of `E` along `f`, the determinant section of
`Ψ` is that of `Φ` times the determinant of the automorphism `Ψ y ∘ (Φ y)⁻¹` of `E (f y)`. -/
theorem detCoreFrameSection_eq_det_smul (y : X) :
    detCoreFrameSection f Ψ hΨ y =
      LinearMap.det ((Φ y).symm.trans (Ψ y) : E (f y) →ₗ[𝕜] E (f y)) •
        detCoreFrameSection f Φ hΦ y :=
  isoFiberEquiv_apply_eq_smul _ _ (fiberMap_detCoreFrameIso_trans_symm_hom f hΦ hΨ y) _

/-- **The determinant section of a frame in coordinates.** The value at `y` of the determinant
section of a frame `Φ` along `f` is the top compound matrix of the automorphism of
`Fin (finrank 𝕜 G) → 𝕜` that reads `Φ y` in the preferred trivialization of `E` at `f y`,
applied to the coordinate `1`. In particular it depends only on `f y` and `Φ y`. -/
theorem detCoreFrameSection_apply (y : X) (i : Fin ((detCore 𝕜 G E).pullback f).rank) :
    detCoreFrameSection f Φ hΦ y i =
      (((ContinuousLinearEquiv.ofFinrankEq (finrank_fin_fun 𝕜).symm).symm.trans ((Φ y).trans
        ((VectorBundle.continuousLinearEquivAt 𝕜 G E (f y)).trans
          (ContinuousLinearEquiv.ofFinrankEq (finrank_fin_fun 𝕜).symm)))) :
        (Fin (finrank 𝕜 G) → 𝕜) →L[𝕜] Fin (finrank 𝕜 G) → 𝕜).exteriorPowerCoords (finrank 𝕜 G)
          (fun _ ↦ 1) (Fin.cast (by simp) i) := by
  rw [detCoreFrameSection_def, detCoreFrameIso_def, isoFiberEquiv_apply, Iso.trans_hom,
    Iso.trans_hom, fiberMap_comp, fiberMap_comp, Iso.symm_hom, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, eqToIso.hom, fiberMap_eqToHom_apply,
    fiberMap_detCoreMap_hom_apply (E := Trivial X G) (E₁ := (⇑f) *ᵖ E) Φ,
    fiberMap_detCoreTrivialIso_inv_const]
  -- The fibre map of the isomorphism of cores is `Φ y` read through the identifications of the
  -- fibres of the cores, which are the preferred trivializations at `y` and at `f y`.
  have hA : (ofBundleOfFinrankEqIso (E₀ := Trivial X G) (E₁ := (⇑f) *ᵖ E) rfl rfl Φ
        (Pullback.continuous_totalSpaceMk_trivial (φ := fun y ↦ Φ y) hΦ)).hom.fiberMap y =
      ((ContinuousLinearEquiv.ofFinrankEq (finrank_fin_fun 𝕜).symm).symm.trans ((Φ y).trans
        ((VectorBundle.continuousLinearEquivAt 𝕜 G E (f y)).trans
          (ContinuousLinearEquiv.ofFinrankEq (finrank_fin_fun 𝕜).symm))) :
        (Fin (finrank 𝕜 G) → 𝕜) →L[𝕜] Fin (finrank 𝕜 G) → 𝕜) := by
    rw [fiberMap_ofBundleOfFinrankEqIso_hom (E₀ := Trivial X G) (E₁ := (⇑f) *ᵖ E) rfl rfl Φ]
    refine ContinuousLinearMap.ext fun v ↦ ?_
    refine (ofBundleOfFinrankEqFiberEquiv_pullback_symm_apply E rfl f y
      (Φ y (ofBundleOfFinrankEqFiberEquiv 𝕜 G (Trivial X G) rfl y v))).trans ?_
    refine (congrArg (fun u ↦ (ofBundleOfFinrankEqFiberEquiv 𝕜 G E rfl (f y)).symm (Φ y u))
      (ofBundleOfFinrankEqFiberEquiv_trivial_apply X rfl y v)).trans ?_
    rw [ofBundleOfFinrankEqFiberEquiv_symm_apply, pointIndexedCoreFiberEquiv_symm_apply]
    -- What remains is the preferred chart at `f y` applied to `Φ y`, which is how
    -- `VectorBundle.continuousLinearEquivAt` acts; `v` is typed as a fibre of the core, so the
    -- rewriting lemmas for compositions of equivalences do not apply.
    rfl
  rw [hA]
  -- The two sides differ only in the proofs inside `Fin.cast`, and in how the rank of the
  -- determinant line is written in its implicit arguments.
  rfl

/-- **The determinant section of a frame as a determinant.** Each coordinate of the value at `y`
of the determinant section of a frame `Φ` along `f` is the determinant of the automorphism of `G`
that reads `Φ y` in the preferred chart of `E` at `f y`. -/
theorem detCoreFrameSection_apply_eq_det (y : X) (i : Fin ((detCore 𝕜 G E).pullback f).rank) :
    detCoreFrameSection f Φ hΦ y i =
      LinearMap.det ((Φ y).trans (VectorBundle.continuousLinearEquivAt 𝕜 G E (f y)) :
        G →ₗ[𝕜] G) := by
  rw [detCoreFrameSection_apply, ← ContinuousLinearEquiv.det_coe_symm_trans_trans
    (ContinuousLinearEquiv.ofFinrankEq (finrank_fin_fun 𝕜).symm)]
  simp only [ContinuousLinearMap.exteriorPowerCoords_self, ContinuousLinearMap.det,
    ContinuousLinearEquiv.toLinearMap_toContinuousLinearMap,
    ContinuousLinearEquiv.trans_toLinearEquiv, ContinuousLinearEquiv.toLinearEquiv_symm,
    smul_apply, ContinuousLinearMap.id_apply, Pi.smul_apply, smul_eq_mul, mul_one]
  -- The two composites differ only in their bracketing.
  rw [LinearEquiv.trans_assoc]

/-- **Naturality of the determinant section of a frame.** Reparametrizing a frame `Φ` along `f`
by a continuous map `g : Y → X` reparametrizes its determinant section by `g`. -/
theorem detCoreFrameSection_comp {Y : Type*} [TopologicalSpace Y] (g : C(Y, X))
    (hΦg : Continuous fun q : Y × G ↦ TotalSpace.mk' G (f (g q.1)) (Φ (g q.1) q.2)) (y : Y) :
    detCoreFrameSection (f.comp g) (fun y ↦ Φ (g y)) hΦg y =
      detCoreFrameSection f Φ hΦ (g y) := by
  funext i
  rw [detCoreFrameSection_apply, detCoreFrameSection_apply]
  -- `(f.comp g) y` is `f (g y)` by definition, and the two casts of `i` have the same value.
  rfl

end Frame

end Bundle

end SymplecticGeometry
