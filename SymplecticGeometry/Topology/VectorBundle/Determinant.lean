/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Topology.FiberBundle.Pullback
public import SymplecticGeometry.Topology.VectorBundle.FiniteRank.Basic
public import SymplecticGeometry.Topology.VectorBundle.FiniteRank.Conjugate
public import SymplecticGeometry.Topology.VectorBundle.FiniteRank.ConjugateExteriorPower
public import SymplecticGeometry.Topology.VectorBundle.FiniteRank.OfBundle
public import SymplecticGeometry.Topology.VectorBundle.FiniteRank.Tensor
public import TauCeti.LinearAlgebra.Complex.Finrank

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
* `detCoreProdIso`: the determinant line of the direct sum `E₁ ×ᵇ E₂` is the tensor product
  `TauCeti.FiniteRankBundleCore.tensor` of the determinant lines of `E₁` and `E₂`;
* `detCoreProdFiberEquiv` and `continuous_detCoreProdFiberEquiv`: the resulting linear isomorphism
  from the fibres of the determinant line of `E₁ ×ᵇ E₂` to the tensor products of the fibres of the
  determinant lines, continuous from its total space to that of Tau Ceti's tensor product bundle,
  in the form taken by `TauCeti.complexEulerClass_eq_of_fiberwise`;
* `fiberMap_detCoreMap_trans_symm_hom`: for two fibrewise isomorphisms `Φ` and `Ψ` of bundles
  with the same model, `detCoreMap Ψ ≪≫ (detCoreMap Φ)⁻¹` acts on each fibre as multiplication by
  the determinant of `Φ⁻¹ ∘ Ψ`.

## The determinant section of a frame

A frame of `E` along a continuous map `f : X → B`, in the sense of Tau Ceti's
`Topology/VectorBundle/Complex/Clutching.lean`, is a family `Φ y : G ≃ E (f y)` that is continuous
from `X × G` to the total space of `E`. It trivializes the pull-back of the determinant line
(`detCoreFrameIso`), and so gives the section `detCoreFrameSection f Φ hΦ` of that pull-back, the
top wedge of the frame. This section is continuous on total spaces
(`continuous_detCoreFrameSection`) and vanishes nowhere (`detCoreFrameSection_ne_zero`). For a
second frame `Ψ`, the section of `Ψ` at `y` is that of `Φ` times the determinant of
`Ψ y ∘ (Φ y)⁻¹` (`detCoreFrameSection_eq_det_smul`). This change-of-frame rule follows Tau
Ceti's `TauCeti.clutchingFunction_eq_mul_normalizedDet_inv`, which compares the clutching
functions of two frames through the automorphism `(φ y)⁻¹ ∘ ψ y` of the model fibre.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §14 (the first Chern class through the determinant line).
* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.7.
-/

public section

open Bundle CategoryTheory Module TauCeti TauCeti.FiniteRankBundleCore TauCeti.Conjugate
open scoped TensorProduct

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
    fiberMap_ofBundleOfFinrankEqIso_hom, ← LinearMap.det_conj
      ((Ψ x).trans (Φ x).symm : E x →ₗ[𝕜] E x)
      (ofBundleOfFinrankEqFiberEquiv 𝕜 G E rfl x).symm.toLinearEquiv]
  refine congrArg LinearMap.det (LinearMap.ext fun v ↦ ?_)
  exact congrArg (fun w ↦ (ofBundleOfFinrankEqFiberEquiv 𝕜 G E rfl x).symm ((Φ x).symm w))
    ((ofBundleOfFinrankEqFiberEquiv 𝕜 G E₁ rfl x).apply_symm_apply
      (Ψ x (ofBundleOfFinrankEqFiberEquiv 𝕜 G E rfl x v)))

end SameModel

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
      (LinearEquiv.finrank_complex_eq (toConjₗ' (V := G))).symm).trans
        (det_def _).symm) ≪≫
    detConjugateIso _ ≪≫ eqToIso (congrArg (conjugate B).obj (detCore_def ℂ G E).symm)

theorem detCoreConjugateIso_def :
    detCoreConjugateIso E =
      eqToIso (detCore_eq_exteriorPower ℂ (Conjugate G) (ConjugateBundle E)) ≪≫
        (exteriorPower ℂ B (finrank ℂ (Conjugate G))).mapIso
          (ofBundleOfFinrankEqConjugateIso E rfl rfl) ≪≫
        eqToIso ((congrArg (fun k ↦ (exteriorPower ℂ B k).obj
          ((conjugate B).obj (ofBundleOfFinrankEq ℂ G E rfl)))
      (LinearEquiv.finrank_complex_eq (toConjₗ' (V := G))).symm).trans
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
      LinearMap.det ((Φ y).symm.trans (Ψ y) : E (f y) →ₗ[𝕜] E (f y)) := by
    rw [← LinearMap.det_conj _ (Φ y : G ≃L[𝕜] E (f y)).toLinearEquiv]
    congr 1
    ext v
    simp
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

end Frame

end Bundle

end SymplecticGeometry
