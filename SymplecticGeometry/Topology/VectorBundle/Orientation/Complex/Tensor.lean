/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.VectorBundle.Orientation.Complex.FiberwiseEquiv
public import SymplecticGeometry.Topology.VectorBundle.TensorProduct.External
public import TauCeti.Topology.VectorBundle.TensorProduct.Operations
public import SymplecticGeometry.Topology.VectorBundle.FiniteTrivializingCover
public import TauCeti.Geometry.Manifold.Projectivization.LineBundle
public import SymplecticGeometry.Topology.VectorBundle.Complex.ChernClass.ProjectiveSpace
import SymplecticGeometry.AlgebraicTopology.Cohomology.LerayHirsch.ProjectiveSpace
import SymplecticGeometry.Analysis.Normed.Module.TensorProduct.ProjectiveSeminorm
import SymplecticGeometry.Topology.VectorBundle.TensorProduct.Pullback
import SymplecticGeometry.Topology.VectorBundle.ProjectiveBundle.ClassifyingMap
import SymplecticGeometry.Geometry.Manifold.Projectivization.Tautological
import SymplecticGeometry.Geometry.Manifold.Projectivization.TwistCore
import SymplecticGeometry.AlgebraicTopology.Singular.Nullhomotopic

/-!
# The Euler class of a tensor product of complex line bundles

Let `T` and `T'` be the tautological lines of the complex projective spaces `ℙ ℂ V` and `ℙ ℂ W`
(`Projectivization.Tautological`), and let `T ⊠ T'` be their external tensor product over
`ℙ ℂ V × ℙ ℂ W`: Tau Ceti's tensor product bundle of the pull-backs of `T` and `T'` along the two
projections, with model fibre `TauCeti.ProjectiveTensor ℂ ℂ ℂ`, a complex line
(`TauCeti.ProjectiveTensor.finrank_eq_mul`). This file computes its Euler class: it is
`pr₁^* e(T) + pr₂^* e(T')` (`Projectivization.complexEulerClass_tensorProduct_tautological`), and
so `-(pr₁^* h + pr₂^* h')` in integral cohomology, `h` and `h'` being the hyperplane classes
(`Projectivization.uliftIntegralCohomologyIso_complexEulerClass_tensorProduct_tautological`).

Two consequences follow.

* `TauCeti.complexEulerClass_tensorProduct`: for complex line bundles `L` and `L'` over a normal
  base, each with a finite trivializing cover
  (`SymplecticGeometry.Bundle.HasFiniteTrivializingCover`; over a compact base every bundle has
  one), the Euler class of Tau Ceti's tensor product bundle `L ⊗ L'` is `e(L) + e(L')`.
* `Projectivization.complexEulerClass_twistCore_one`: on `ℙ ℂ (Fin (n + 1) → ℂ)`, the Euler class
  of Tau Ceti's `twistCore 1`, the bundle `𝒪(1)`, read in integral cohomology, is the hyperplane
  class.

`TauCeti.complexEulerClass` asks for a real structure on the model fibre and on the fibres,
compatible with the complex one. Here it is the restriction of scalars from `ℂ` to `ℝ`, which
Mathlib provides as instances on every complex vector space (`Module.complexToReal`,
`NormedSpace.complexToReal`, with `IsScalarTower.complexToReal`); on the fibres
`T x ⊗[ℂ] T' y` instance search finds the action of `ℝ` on the left factor
(`TensorProduct.leftModule`), which agrees with the restriction of scalars. No choice is made in
this file: any statement about complex line bundles whose model fibre or fibres are such tensor
products gets the same structure from the same instances.

## Proof

Both sides are classes in `H²(ℙ ℂ V × ℙ ℂ W; ULift ℤ)`. By the vanishing criterion
`Projectivization.eq_zero_of_singularCohomologyMap_prodMk_eq_zero` (Leray–Hirsch for the product,
with `W` finite-dimensional and `ℙ ℂ V` path-connected), it suffices that they agree on the two axes
`ℙ ℂ V × {y₀}` and `{x₀} × ℙ ℂ W`. On the first, a nonzero `w₀ ∈ y₀` gives the fibrewise
isomorphism `v ↦ v ⊗ w₀` from `T` to `T ⊠ T'`, continuous on total spaces, so naturality
(`TauCeti.complexEulerClass_eq_singularCohomologyMap_of_fiberwise`) pulls `e(T ⊠ T')` back to
`e(T)`; the class `pr₂^* e(T')` pulls back through a point, so to zero. The second axis is the same,
with `w ↦ v₀ ⊗ w`.

For line bundles `L` and `L'` with finite trivializing covers over a normal base `B`, the
classifying maps `g : B → ℙ ℂ (Fin N → ℂ)` and `g' : B → ℙ ℂ (Fin M → ℂ)` of
`SymplecticGeometry.Bundle.exists_fiberwise_tautological_fin` come with fibrewise isomorphisms
`L b ≃ T (g b)` and `L' b ≃ T' (g' b)`. Their tensor product (Tau Ceti's
`TauCeti.bundleTensorCongrHomeomorph`), followed by the map of
`TauCeti.continuous_tensorProduct_pullback` from the tensor product of pull-backs along
`(g, g')` to `T ⊠ T'`, is a fibrewise isomorphism from `L ⊗ L'` to `T ⊠ T'` over `(g, g')`,
continuous on total spaces. Naturality then gives `e(L ⊗ L') = (g, g')^* e(T ⊠ T')`, which is
`g^* e(T) + g'^* e(T') = e(L) + e(L')`.

For `𝒪(1)`: the Euler class of Tau Ceti's `twistCore 0` is zero
(`Projectivization.complexEulerClass_twistCore_zero`). Through
`Projectivization.twistCoreTensorEquiv 1 (-1)`, `twistCore 1 ⊗ twistCore (-1)` is isomorphic to it,
so `e(𝒪(1)) = -e(𝒪(-1))`, which is the hyperplane class by
`Projectivization.complexEulerClass_twistCore_neg_one`.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press (1974), §14 (the orientation that the complex structure gives the
  underlying real bundle, and the top Chern class as its Euler class).
* [R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §20 (the
  tautological line of a projective space and the class `x = -e(S)`).
* A. Hatcher, *Vector Bundles and K-Theory*, §3.1 (the proof of Proposition 3.10: the first
  Chern class of a tensor product of line bundles, through the external tensor product of the
  tautological lines of two projective spaces and the restriction to the two axes).
* [P. Griffiths, J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978], Chapter 1,
  §1 (the line bundles `𝒪(k)` on projective space and their tensor products).
-/

public section

noncomputable section

open Bundle Module TauCeti CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped LinearAlgebra.Projectivization TensorProduct TauCeti.ModuleTopology

namespace Projectivization

variable {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W]

/-- The fibres `T x ⊗[ℂ] T' y` of the external tensor product of the tautological lines `T` and
`T'` of `ℙ ℂ V` and `ℙ ℂ W`. -/
local notation "TT" => fun x : ℙ ℂ V × ℙ ℂ W ↦
  ((ContinuousMap.fst : C(ℙ ℂ V × ℙ ℂ W, ℙ ℂ V)) *ᵖ (Tautological ℂ V)) x ⊗[ℂ]
    ((ContinuousMap.snd : C(ℙ ℂ V × ℙ ℂ W, ℙ ℂ W)) *ᵖ (Tautological ℂ W)) x

/-- On `ℙ ℂ V × {y₀}`, the Euler class of the external tensor product of the tautological lines
pulls back to that of the tautological line of `ℙ ℂ V`. -/
private theorem complexEulerClass_tensorProduct_tautological_left (y₀ : ℙ ℂ W) :
    complexEulerClass (r := 0) ℂ (Tautological ℂ V) (finrank_self ℂ) =
      TopCat.singularCohomologyMap (TopCat.ofHom (.prodMk (.id _) (.const _ y₀))) 2
        (complexEulerClass (r := 0) (ProjectiveTensor ℂ ℂ ℂ) TT
          (by simp)) := by
  -- `c ↦ c • y₀.rep`, from `ℂ` to the line `y₀`.
  let e : ℂ ≃ₗ[ℂ] Tautological ℂ W y₀ :=
    LinearEquiv.toSpanNonzeroSingleton ℂ W y₀.rep y₀.rep_ne_zero ≪≫ₗ
      LinearEquiv.ofEq _ _ (submodule_eq y₀).symm
  let φ : ∀ x : ℙ ℂ V, Tautological ℂ V x ≃L[ℂ] TT (x, y₀) := fun x ↦
    letI : IsModuleTopology ℂ (Tautological ℂ V x) := isModuleTopologyOfFiniteDimensional
    LinearEquiv.toContinuousLinearEquivOfIsModuleTopology
      ((TensorProduct.rid ℂ (Tautological ℂ V x)).symm ≪≫ₗ
        TensorProduct.congr (LinearEquiv.refl ℂ (Tautological ℂ V x)) e)
  have hφ : ∀ x v, φ x v = v ⊗ₜ[ℂ] e 1 := fun x v ↦ by
    simp only [φ, LinearEquiv.coe_toContinuousLinearEquivOfIsModuleTopology,
      LinearEquiv.trans_apply, TensorProduct.rid_symm_apply]
    -- The fibres of `T ⊠ T'` are tensor products of fibres of pull-backs, which `simp` does not
    -- identify with the fibres of `T` and `T'`; `exact` does.
    exact TensorProduct.congr_tmul _ _ _ _
  have hc : Continuous fun p : TotalSpace ℂ (Tautological ℂ V) ↦
      TotalSpace.mk' (ProjectiveTensor ℂ ℂ ℂ) (E := TT) (p.proj, y₀) (p.snd ⊗ₜ[ℂ] e 1) := by
    refine Continuous.tmul_section (F₁ := ℂ) (F₂ := ℂ)
      (b := fun p : TotalSpace ℂ (Tautological ℂ V) ↦ (p.proj, y₀)) ?_ ?_
    · exact Pullback.continuous_iff.2
        ⟨(continuous_proj_tautological ℂ V).prodMk continuous_const, continuous_id⟩
    · exact Pullback.continuous_iff.2
        ⟨(continuous_proj_tautological ℂ V).prodMk continuous_const,
          continuous_const (y := (⟨y₀, e 1⟩ : TotalSpace ℂ (Tautological ℂ W)))⟩
  refine complexEulerClass_eq_singularCohomologyMap_of_fiberwise _ _ (φ := φ) ?_
  convert hc using 3 with p
  exacts [by simp, heq_of_eq (hφ _ _)]

/-- On `{x₀} × ℙ ℂ W`, the Euler class of the external tensor product of the tautological lines
pulls back to that of the tautological line of `ℙ ℂ W`. -/
private theorem complexEulerClass_tensorProduct_tautological_right (x₀ : ℙ ℂ V) :
    complexEulerClass (r := 0) ℂ (Tautological ℂ W) (finrank_self ℂ) =
      TopCat.singularCohomologyMap (TopCat.ofHom (.prodMk (.const _ x₀) (.id _))) 2
        (complexEulerClass (r := 0) (ProjectiveTensor ℂ ℂ ℂ) TT
          (by simp)) := by
  -- `c ↦ c • x₀.rep`, from `ℂ` to the line `x₀`.
  let e : ℂ ≃ₗ[ℂ] Tautological ℂ V x₀ :=
    LinearEquiv.toSpanNonzeroSingleton ℂ V x₀.rep x₀.rep_ne_zero ≪≫ₗ
      LinearEquiv.ofEq _ _ (submodule_eq x₀).symm
  let φ : ∀ y : ℙ ℂ W, Tautological ℂ W y ≃L[ℂ] TT (x₀, y) := fun y ↦
    letI : IsModuleTopology ℂ (Tautological ℂ W y) := isModuleTopologyOfFiniteDimensional
    LinearEquiv.toContinuousLinearEquivOfIsModuleTopology
      ((TensorProduct.lid ℂ (Tautological ℂ W y)).symm ≪≫ₗ
        TensorProduct.congr e (LinearEquiv.refl ℂ (Tautological ℂ W y)))
  have hφ : ∀ y w, φ y w = e 1 ⊗ₜ[ℂ] w := fun y w ↦ by
    simp only [φ, LinearEquiv.coe_toContinuousLinearEquivOfIsModuleTopology,
      LinearEquiv.trans_apply, TensorProduct.lid_symm_apply]
    -- As in `complexEulerClass_tensorProduct_tautological_left`.
    exact TensorProduct.congr_tmul _ _ _ _
  have hc : Continuous fun p : TotalSpace ℂ (Tautological ℂ W) ↦
      TotalSpace.mk' (ProjectiveTensor ℂ ℂ ℂ) (E := TT) (x₀, p.proj) (e 1 ⊗ₜ[ℂ] p.snd) := by
    refine Continuous.tmul_section (F₁ := ℂ) (F₂ := ℂ)
      (b := fun p : TotalSpace ℂ (Tautological ℂ W) ↦ (x₀, p.proj)) ?_ ?_
    · exact Pullback.continuous_iff.2
        ⟨continuous_const.prodMk (continuous_proj_tautological ℂ W),
          continuous_const (y := (⟨x₀, e 1⟩ : TotalSpace ℂ (Tautological ℂ V)))⟩
    · exact Pullback.continuous_iff.2
        ⟨continuous_const.prodMk (continuous_proj_tautological ℂ W), continuous_id⟩
  refine complexEulerClass_eq_singularCohomologyMap_of_fiberwise _ _ (φ := φ) ?_
  convert hc using 3 with p
  exacts [by simp, heq_of_eq (hφ _ _)]

/-- **The Euler class of the external tensor product of two tautological lines.** Let `T` and
`T'` be the tautological lines of the complex projective spaces `ℙ ℂ V` and `ℙ ℂ W`, with `W`
finite-dimensional. The Euler class of the tensor product of their pull-backs to
`ℙ ℂ V × ℙ ℂ W` along the two projections is `pr₁^* e(T) + pr₂^* e(T')`. -/
theorem complexEulerClass_tensorProduct_tautological [FiniteDimensional ℂ W] :
    complexEulerClass (r := 0) (ProjectiveTensor ℂ ℂ ℂ) TT
        (by simp) =
      TopCat.singularCohomologyMap (TopCat.ofHom ContinuousMap.fst) 2
          (complexEulerClass (r := 0) ℂ (Tautological ℂ V) (finrank_self ℂ)) +
        TopCat.singularCohomologyMap (TopCat.ofHom ContinuousMap.snd) 2
          (complexEulerClass (r := 0) ℂ (Tautological ℂ W) (finrank_self ℂ)) := by
  rcases isEmpty_or_nonempty (ℙ ℂ V × ℙ ℂ W) with h | ⟨x₀, y₀⟩
  · exact (ModuleCat.subsingleton_of_isZero
      (isZero_singularCohomology_of_isEmpty _ ℤ _ (TopCat.of (ℙ ℂ V × ℙ ℂ W)) _)).elim _ _
  have : Nontrivial V := nontrivial_of_ne _ _ x₀.rep_ne_zero
  have : Nontrivial W := nontrivial_of_ne _ _ y₀.rep_ne_zero
  obtain ⟨m, hW⟩ : ∃ m, finrank ℂ W = m + 1 :=
    ⟨finrank ℂ W - 1, (Nat.sub_add_cancel finrank_pos).symm⟩
  rw [← sub_eq_zero]
  refine eq_zero_of_singularCohomologyMap_prodMk_eq_zero hW x₀ y₀ ?_ ?_
  · have h₁ : TopCat.ofHom (.prodMk (.id _) (.const _ y₀)) ≫ TopCat.ofHom ContinuousMap.fst =
        𝟙 (TopCat.of (ℙ ℂ V)) :=
      TopCat.ext fun _ ↦ by simp
    have h₂ : TopCat.ofHom (.prodMk (.id _) (.const _ y₀)) ≫ TopCat.ofHom ContinuousMap.snd =
        TopCat.const (X := TopCat.of (ℙ ℂ V)) (y₀ : TopCat.of (ℙ ℂ W)) :=
      -- `TopCat.const_apply` does not match points of `TopCat.of (ℙ ℂ V × ℙ ℂ W)`; both sides
      -- send `x` to `y₀` by definition.
      TopCat.ext fun _ ↦ rfl
    rw [map_sub, map_add, ← complexEulerClass_tensorProduct_tautological_left,
      ← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp, h₁,
      ← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp, h₂,
      TopCat.singularCohomologyMap_const_eq_zero _ two_ne_zero, TopCat.singularCohomologyMap_id]
    simp
  · have h₁ : TopCat.ofHom (.prodMk (.const _ x₀) (.id _)) ≫ TopCat.ofHom ContinuousMap.fst =
        TopCat.const (X := TopCat.of (ℙ ℂ W)) (x₀ : TopCat.of (ℙ ℂ V)) :=
      -- As for `h₂` on the other axis.
      TopCat.ext fun _ ↦ rfl
    have h₂ : TopCat.ofHom (.prodMk (.const _ x₀) (.id _)) ≫ TopCat.ofHom ContinuousMap.snd =
        𝟙 (TopCat.of (ℙ ℂ W)) :=
      TopCat.ext fun _ ↦ by simp
    rw [map_sub, map_add, ← complexEulerClass_tensorProduct_tautological_right,
      ← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp, h₁,
      ← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp, h₂,
      TopCat.singularCohomologyMap_const_eq_zero _ two_ne_zero, TopCat.singularCohomologyMap_id]
    simp

/-- **The Euler class of the external tensor product of two tautological lines, in integral
cohomology.** Read in `H²(ℙ ℂ V × ℙ ℂ W; ℤ)` through `TopCat.uliftIntegralCohomologyIso`, the Euler
class of `complexEulerClass_tensorProduct_tautological` is `-(pr₁^* h + pr₂^* h')`, where `h` and
`h'` are the hyperplane classes of `ℙ ℂ V` and `ℙ ℂ W`. -/
theorem uliftIntegralCohomologyIso_complexEulerClass_tensorProduct_tautological
    [FiniteDimensional ℂ W] :
    ((TopCat.of (ℙ ℂ V × ℙ ℂ W)).uliftIntegralCohomologyIso 2).hom
        (complexEulerClass (r := 0) (ProjectiveTensor ℂ ℂ ℂ) TT
          (by simp)) =
      -(TopCat.singularCohomologyMap (TopCat.ofHom ContinuousMap.fst) 2 (hyperplaneClass V) +
        TopCat.singularCohomologyMap (TopCat.ofHom ContinuousMap.snd) 2 (hyperplaneClass W)) := by
  rw [complexEulerClass_tensorProduct_tautological, map_add, hyperplaneClass_def,
    hyperplaneClass_def, map_neg, map_neg, neg_add, neg_neg, neg_neg]
  rw [TopCat.uliftIntegralCohomologyIso_naturality_apply,
    TopCat.uliftIntegralCohomologyIso_naturality_apply]

end Projectivization

/-! ### Complex line bundles with finite trivializing covers -/

namespace TauCeti

open Projectivization SymplecticGeometry.Bundle

variable {B : Type} [TopologicalSpace B] [NormalSpace B]
  {G : Type} [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  {L : B → Type} [TopologicalSpace (TotalSpace G L)] [∀ b, AddCommGroup (L b)]
  [∀ b, Module ℝ (L b)] [∀ b, Module ℂ (L b)] [∀ b, IsScalarTower ℝ ℂ (L b)]
  [∀ b, TopologicalSpace (L b)] [FiberBundle G L] [VectorBundle ℂ G L]
  {G' : Type} [NormedAddCommGroup G'] [NormedSpace ℂ G'] [FiniteDimensional ℂ G']
  {L' : B → Type} [TopologicalSpace (TotalSpace G' L')] [∀ b, AddCommGroup (L' b)]
  [∀ b, Module ℝ (L' b)] [∀ b, Module ℂ (L' b)] [∀ b, IsScalarTower ℝ ℂ (L' b)]
  [∀ b, TopologicalSpace (L' b)] [FiberBundle G' L'] [VectorBundle ℂ G' L']

/-- **The Euler class of a tensor product of complex line bundles.** For complex line bundles `L`
and `L'` over a normal base, each with a finite trivializing cover (as over a compact base, by
`HasFiniteTrivializingCover.of_compactSpace`), the Euler class of Tau Ceti's tensor product
bundle `L ⊗ L'` is the sum of the Euler classes of `L` and `L'`. -/
theorem complexEulerClass_tensorProduct (hG : finrank ℂ G = 1)
    (hG' : finrank ℂ G' = 1) (hL : HasFiniteTrivializingCover ℂ G L)
    (hL' : HasFiniteTrivializingCover ℂ G' L') :
    complexEulerClass (r := 0) (ProjectiveTensor ℂ G G') (fun b ↦ L b ⊗[ℂ] L' b)
        (by simp [hG, hG']) =
      complexEulerClass (r := 0) G L hG + complexEulerClass (r := 0) G' L' hG' := by
  obtain ⟨N, g, φ, hφ⟩ := exists_fiberwise_tautological_fin hG hL
  obtain ⟨M, g', φ', hφ'⟩ := exists_fiberwise_tautological_fin hG' hL'
  set P := ℙ ℂ (Fin N → ℂ) × ℙ ℂ (Fin M → ℂ)
  -- The classifying map of `L ⊗ L'` to the product of the projective spaces.
  let γ : C(B, P) := g.prodMk g'
  -- `φ` and `φ'` read as isomorphisms onto the pull-backs along `γ` of the two factors of the
  -- external tensor product, whose fibres are those of the tautological lines.
  let ψ : ∀ b, L b ≃L[ℂ]
      ((γ : B → P) *ᵖ ((ContinuousMap.fst : C(P, ℙ ℂ (Fin N → ℂ))) *ᵖ
        (Tautological ℂ (Fin N → ℂ)))) b := φ
  let ψ' : ∀ b, L' b ≃L[ℂ]
      ((γ : B → P) *ᵖ ((ContinuousMap.snd : C(P, ℙ ℂ (Fin M → ℂ))) *ᵖ
        (Tautological ℂ (Fin M → ℂ)))) b := φ'
  have hψ : Continuous fun v : TotalSpace G L ↦ TotalSpace.mk' ℂ v.proj (ψ v.proj v.snd) := by
    refine (inducing_pullbackTotalSpaceEmbedding _ _ _).continuous_iff.2 <|
      (FiberBundle.continuous_proj G L).prodMk <|
        (inducing_pullbackTotalSpaceEmbedding _ _ _).continuous_iff.2 <|
          (γ.continuous.comp (FiberBundle.continuous_proj G L)).prodMk hφ
  have hψ' : Continuous fun v : TotalSpace G' L' ↦ TotalSpace.mk' ℂ v.proj (ψ' v.proj v.snd) := by
    refine (inducing_pullbackTotalSpaceEmbedding _ _ _).continuous_iff.2 <|
      (FiberBundle.continuous_proj G' L').prodMk <|
        (inducing_pullbackTotalSpaceEmbedding _ _ _).continuous_iff.2 <|
          (γ.continuous.comp (FiberBundle.continuous_proj G' L')).prodMk hφ'
  set A₁ := (ContinuousMap.fst : C(P, ℙ ℂ (Fin N → ℂ))) *ᵖ (Tautological ℂ (Fin N → ℂ))
  set A₂ := (ContinuousMap.snd : C(P, ℙ ℂ (Fin M → ℂ))) *ᵖ (Tautological ℂ (Fin M → ℂ))
  -- Instance search does not find the tensor product structure on these nested pull-backs, as
  -- for the instances of `TensorProduct/External.lean`, so it is given here.
  let := Bundle.TensorProduct.topologicalSpaceTotalSpace ℂ ℂ ((γ : B → P) *ᵖ A₁) ℂ
    ((γ : B → P) *ᵖ A₂)
  let := Bundle.TensorProduct.fiberBundle ℂ ℂ ((γ : B → P) *ᵖ A₁) ℂ ((γ : B → P) *ᵖ A₂)
  let := Bundle.TensorProduct.vectorBundle ℂ ℂ ((γ : B → P) *ᵖ A₁) ℂ ((γ : B → P) *ᵖ A₂)
  have hΦ : Continuous fun v : TotalSpace (ProjectiveTensor ℂ G G') (fun b ↦ L b ⊗[ℂ] L' b) ↦
      TotalSpace.mk' (ProjectiveTensor ℂ ℂ ℂ) (E := fun x ↦ A₁ x ⊗[ℂ] A₂ x) (γ v.proj)
        (bundleTensorCongr ψ ψ' v.proj v.snd) := by
    refine ((continuous_tensorProduct_pullback (F₁ := ℂ) (F₂ := ℂ) (E₁ := A₁) (E₂ := A₂) γ).comp
      (bundleTensorCongrHomeomorph ψ ψ' hψ hψ').continuous).congr fun v ↦ ?_
    rw [Function.comp_apply, bundleTensorCongrHomeomorph_apply]
  rw [complexEulerClass_eq_singularCohomologyMap_of_fiberwise (g := γ)
      (F := ProjectiveTensor ℂ ℂ ℂ) (E := fun x ↦ A₁ x ⊗[ℂ] A₂ x)
      (φ := bundleTensorCongr ψ ψ') (by simp) _ hΦ,
    complexEulerClass_tensorProduct_tautological, map_add,
    complexEulerClass_eq_singularCohomologyMap_of_fiberwise _ hG hφ,
    complexEulerClass_eq_singularCohomologyMap_of_fiberwise _ hG' hφ',
    ← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp,
    ← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp]
  rw [← TopCat.ofHom_comp, ← TopCat.ofHom_comp,
    show ContinuousMap.fst.comp γ = g from ContinuousMap.ext fun _ ↦ by simp [γ],
    show ContinuousMap.snd.comp γ = g' from ContinuousMap.ext fun _ ↦ by simp [γ]]

end TauCeti

/-! ### The Euler class of `𝒪(1)` -/

namespace Projectivization

variable {n : ℕ}

/-- **The Euler class of `𝒪(1)`.** On `ℙ ℂ (Fin (n + 1) → ℂ)`, the Euler class of Tau Ceti's
`twistCore 1`, read in integral cohomology through `TopCat.uliftIntegralCohomologyIso`, is the
hyperplane class. -/
theorem complexEulerClass_twistCore_one :
    ((TopCat.of (ℙ ℂ (Fin (n + 1) → ℂ))).uliftIntegralCohomologyIso 2).hom
        (complexEulerClass (r := 0) ℂ (twistCore (𝕜 := ℂ) (n := n) 1).Fiber
          (finrank_self ℂ)) =
      hyperplaneClass (Fin (n + 1) → ℂ) := by
  -- `𝒪(1 + (-1))` is `𝒪(0)`, whose Euler class vanishes.
  have h₀ : complexEulerClass (r := 0) ℂ (twistCore (𝕜 := ℂ) (n := n) (1 + -1)).Fiber
      (finrank_self ℂ) = 0 := by
    rw [show (1 : ℤ) + -1 = 0 by norm_num]
    exact complexEulerClass_twistCore_zero
  have h := complexEulerClass_eq_of_fiberwise (by simp) (finrank_self ℂ)
    (φ := twistCoreTensorEquiv (𝕜 := ℂ) (n := n) 1 (-1))
    (continuous_twistCoreTensorEquiv (𝕜 := ℂ) (n := n) 1 (-1))
  rw [h₀, complexEulerClass_tensorProduct (finrank_self ℂ) (finrank_self ℂ)
      .of_compactSpace .of_compactSpace, eq_comm,
    add_eq_zero_iff_eq_neg] at h
  rw [h, map_neg, complexEulerClass_twistCore_neg_one, neg_neg]

end Projectivization

end
