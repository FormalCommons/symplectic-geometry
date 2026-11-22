/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

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
  in the form taken by `TauCeti.complexEulerClass_eq_of_fiberwise`.

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

end Bundle

end SymplecticGeometry
