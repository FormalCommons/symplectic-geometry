/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.VectorBundle.Orientation.Complex.FiberwiseEquiv
public import SymplecticGeometry.AlgebraicTopology.Cohomology.LerayHirsch.ProjectiveSpace
public import SymplecticGeometry.Analysis.Normed.Module.TensorProduct.ProjectiveSeminorm
public import SymplecticGeometry.Topology.VectorBundle.TensorProduct.External

/-!
# The Euler class of a tensor product of complex line bundles

Let `T` and `T'` be the tautological lines of the complex projective spaces `ℙ ℂ V` and `ℙ ℂ W`
(`Projectivization.Tautological`), and let `T ⊠ T'` be their external tensor product over
`ℙ ℂ V × ℙ ℂ W`: Tau Ceti's tensor product bundle of the pull-backs of `T` and `T'` along the two
projections, with model fibre `TauCeti.ProjectiveTensor ℂ ℂ ℂ`, a complex line
(`TauCeti.ProjectiveTensor.finrank_eq_mul`). This file computes its Euler class: it is
`pr₁^* e(T) + pr₂^* e(T')` (`Projectivization.complexEulerClass_tensorProduct_tautological`), and
so `-(pr₁^* h + pr₂^* h')` in integral cohomology, `h` and `h'` being the hyperplane classes
(`Projectivization.uliftIntegralCohomologyIso_complexEulerClass_tensorProduct_tautological`). The
Euler class of the tensor product of two complex line bundles over a compact base is pulled back
from this case by classifying maps.

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

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press (1974), §14 (the orientation that the complex structure gives the
  underlying real bundle, and the top Chern class as its Euler class).
* [R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §20 (the
  tautological line of a projective space and the class `x = -e(S)`).
* A. Hatcher, *Vector Bundles and K-Theory*, §3.1 (the proof of Proposition 3.10: the first
  Chern class of a tensor product of line bundles, through the external tensor product of the
  tautological lines of two projective spaces and the restriction to the two axes).
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
  exact congrArg₂ (· + ·)
    (ConcreteCategory.congr_hom (TopCat.uliftIntegralCohomologyIso_naturality _ 2) _)
    (ConcreteCategory.congr_hom (TopCat.uliftIntegralCohomologyIso_naturality _ 2) _)

end Projectivization

end
