/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Cohomology.EvenIntegralCohomology
public import SymplecticGeometry.AlgebraicTopology.Cohomology.Sphere.Generator
public import SymplecticGeometry.Topology.ComplexProjectiveSpace.Sphere
public import SymplecticGeometry.Topology.VectorBundle.Complex.ChernClass.Naturality
public import SymplecticGeometry.Topology.VectorBundle.Complex.ChernClass.ProjectiveSpace

/-!
# The top product of first Chern classes on `(ℂP¹)ᵐ`

Write `P = ℙ ℂ (Fin 2 → ℂ)` for the complex projective line and `h ∈ H²(P; ℤ)` for its hyperplane
class. This file shows that on the product `Pᵐ = Fin m → P` the cup product of the first Chern
classes `yᵢ = c₁(prᵢ^* 𝒪(-1))` of the tautological lines pulled back along the projections is a
class of infinite order in `H^{2m}(Pᵐ; ℤ)`.

## Main results

* `Projectivization.singularCohomologyMap_sphereGenerator_eq_hyperplaneClass_or_eq_neg_…`:
  under any homeomorphism `e : P ≃ₜ S²`, the generator `θ ∈ H²(S²; ℤ)` of
  `SymplecticGeometry/AlgebraicTopology/Cohomology/Sphere/Generator.lean` pulls back to `h` or to
  `-h`. Since `c₁(𝒪(-1)) = -h` (by `SymplecticGeometry.Bundle.chernClass_one_eq_complexEulerClass`
  and the definition of `h`), it pulls back to `±c₁` of the tautological line.
* `Projectivization.not_isOfFinAddOrder_prod_singularCohomologyMap`: for nonzero classes
  `bᵢ ∈ H²(P; ℤ)`, the product of the pull-backs `prᵢ^* bᵢ`, the component of degree `2m` of a
  product in the even integral cohomology ring of `Pᵐ`, has infinite order.
* `Projectivization.not_isOfFinAddOrder_prod_chernClass`: the product of the classes `yᵢ` has
  infinite order in `H^{2m}(Pᵐ; ℤ)`.

The proof is by induction on `m`. For the step, the inverse of the homeomorphism
`Projectivization.homeomorphTopCatSphere : P ≃ₜ S²` gives a map `S² × Pᵐ → Pᵐ⁺¹`; it pulls
the product on `Pᵐ⁺¹` back to a nonzero multiple of `pr₁^* θ ⌣ pr₂^* c`, with `c` the product on
`Pᵐ`, and `TopCat.not_isOfFinAddOrder_integralCup_sphereGenerator` applies.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Theorem 3.15 (the Künneth
  formula).
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory

namespace Projectivization

open Bundle TauCeti
open scoped LinearAlgebra.Projectivization

/-- **The hyperplane class of `ℂP¹` generates `H²(ℂP¹; ℤ)` as the sphere generator does.** Under
any homeomorphism `e : ℙ ℂ (Fin 2 → ℂ) ≃ₜ S²`, the integral class `θ` dual to the standard
generator of `H₂(S²)` pulls back to the hyperplane class `h` or to `-h`. -/
theorem singularCohomologyMap_sphereGenerator_eq_hyperplaneClass_or_eq_neg_hyperplaneClass
    (e : ℙ ℂ (Fin 2 → ℂ) ≃ₜ TopCat.sphere.{0} 2) :
    TopCat.singularCohomologyMap (TopCat.isoOfHomeo (X := TopCat.of (ℙ ℂ (Fin 2 → ℂ))) e).hom 2
        (TopCat.integralSphereGenerator 1) = hyperplaneClass (Fin 2 → ℂ) ∨
      TopCat.singularCohomologyMap (TopCat.isoOfHomeo (X := TopCat.of (ℙ ℂ (Fin 2 → ℂ))) e).hom 2
        (TopCat.integralSphereGenerator 1) = -hyperplaneClass (Fin 2 → ℂ) := by
  set φ := TopCat.isoOfHomeo (X := TopCat.of (ℙ ℂ (Fin 2 → ℂ))) e
  have hV : Module.finrank ℂ (Fin 2 → ℂ) = 1 + 1 := by simp
  obtain ⟨a, ha⟩ := exists_eq_zsmul_hyperplaneClass hV
    (TopCat.singularCohomologyMap φ.hom 2 (TopCat.integralSphereGenerator 1))
  obtain ⟨b, hb⟩ := TopCat.exists_eq_zsmul_sphereGenerator (d := 1)
    (TopCat.singularCohomologyMap φ.inv 2 (hyperplaneClass (Fin 2 → ℂ)))
  have hba : (b * a) • hyperplaneClass (Fin 2 → ℂ) = (1 : ℤ) • hyperplaneClass (Fin 2 → ℂ) := by
    rw [one_smul, mul_smul, ← ha, ← map_zsmul, ← hb, ← ConcreteCategory.comp_apply,
      ← TopCat.singularCohomologyMap_comp, φ.hom_inv_id, TopCat.singularCohomologyMap_id,
      ConcreteCategory.id_apply]
  rcases Int.eq_one_or_neg_one_of_mul_eq_one'
    ((bijective_zsmul_hyperplaneClass hV one_pos).1 hba) with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · exact .inl (ha.trans (one_smul _ _))
  · exact .inr (ha.trans (neg_one_zsmul _))

/-- A nonzero class of `H²(ℂP¹; ℤ)` pulls back to a nonzero multiple of the sphere generator along
the inverse of `homeomorphTopCatSphere`. -/
private theorem exists_singularCohomologyMap_homeomorphTopCatSphere_symm
    {b : (TopCat.of (ℙ ℂ (Fin 2 → ℂ))).integralCohomology 2} (hb : b ≠ 0) :
    ∃ k : ℤ, k ≠ 0 ∧
      TopCat.singularCohomologyMap
        (TopCat.isoOfHomeo (X := TopCat.of (ℙ ℂ (Fin 2 → ℂ))) homeomorphTopCatSphere.{0}).inv 2 b =
        k • TopCat.integralSphereGenerator 1 := by
  set φ := TopCat.isoOfHomeo (X := TopCat.of (ℙ ℂ (Fin 2 → ℂ))) homeomorphTopCatSphere.{0}
  set θ := TopCat.integralSphereGenerator 1
  have hV : Module.finrank ℂ (Fin 2 → ℂ) = 1 + 1 := by simp
  obtain ⟨j, rfl⟩ := exists_eq_zsmul_hyperplaneClass hV b
  have hj : j ≠ 0 := by rintro rfl; exact hb (zero_smul _ _)
  have hback : TopCat.singularCohomologyMap φ.inv 2 (TopCat.singularCohomologyMap φ.hom 2 θ) =
      θ := by
    rw [← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp, φ.inv_hom_id,
      TopCat.singularCohomologyMap_id, ConcreteCategory.id_apply]
  rcases singularCohomologyMap_sphereGenerator_eq_hyperplaneClass_or_eq_neg_hyperplaneClass
    homeomorphTopCatSphere with h | h
  · exact ⟨j, hj, by rw [map_zsmul, ← h, hback]⟩
  · have h' : hyperplaneClass (Fin 2 → ℂ) = -TopCat.singularCohomologyMap φ.hom 2 θ := by
      rw [h, neg_neg]
    exact ⟨-j, neg_ne_zero.2 hj, by rw [map_zsmul, h', map_neg, hback, zsmul_neg, neg_zsmul]⟩

/-- **The product of pulled-back degree-two classes on `(ℂP¹)ᵐ` has infinite order.** For nonzero
classes `bᵢ ∈ H²(ℂP¹; ℤ)`, `i < m`, the product of their pull-backs along the projections
`(ℂP¹)ᵐ → ℂP¹`, a class of degree `2m` of the even integral cohomology ring, has infinite order. -/
theorem not_isOfFinAddOrder_prod_singularCohomologyMap (m : ℕ)
    (b : Fin m → (TopCat.of (ℙ ℂ (Fin 2 → ℂ))).integralCohomology (2 * 1)) (hb : ∀ i, b i ≠ 0) :
    ¬IsOfFinAddOrder ((∏ i, (TopCat.of (Fin m → ℙ ℂ (Fin 2 → ℂ))).evenIntegralCohomologyOf 1
      (TopCat.singularCohomologyMap (TopCat.ofHom (ContinuousMap.eval i)) (2 * 1)
        (b i))) m) := by
  induction m with
  | zero =>
    have : PathConnectedSpace (Fin 0 → ℙ ℂ (Fin 2 → ℂ)) :=
      @Pi.instPathConnectedSpace _ _ _ fun i ↦ i.elim0
    rw [Finset.univ_eq_empty, Finset.prod_empty, ← TopCat.evenIntegralCohomologyOf_one,
      DirectSum.of_eq_same, ← injective_zsmul_iff_not_isOfFinAddOrder]
    exact (TopCat.bijective_zsmul_integralCohomologyOne _).1
  | succ m ih =>
    let P := ℙ ℂ (Fin 2 → ℂ)
    let Y := TopCat.of (Fin m → P)
    -- Set-up: `g : S² → P` is the inverse of `homeomorphTopCatSphere`.
    let g : TopCat.sphere.{0} 2 ⟶ TopCat.of P :=
      (TopCat.isoOfHomeo (X := TopCat.of (ℙ ℂ (Fin 2 → ℂ))) homeomorphTopCatSphere.{0}).inv
    -- the map `S² × Pᵐ → Pᵐ⁺¹`, `(s, x) ↦ (g s, x)`
    let Ψ : TopCat.sphere.{0} 2 ⊗ Y ⟶ TopCat.of (Fin (m + 1) → P) :=
      TopCat.ofHom ⟨fun p ↦ Fin.cons (g (fst _ Y p)) (snd _ Y p),
        ((g.hom.continuous.comp (fst _ Y).hom.continuous).finCons (snd _ Y).hom.continuous)⟩
    have hΨ₀ : Ψ ≫ TopCat.ofHom (ContinuousMap.eval 0) = fst _ Y ≫ g := by
      ext p
      rfl
    have hΨ (i : Fin m) : Ψ ≫ TopCat.ofHom (ContinuousMap.eval i.succ) =
        snd _ Y ≫ TopCat.ofHom (ContinuousMap.eval i) := by
      ext p
      rfl
    obtain ⟨k, hk, hgk⟩ := exists_singularCohomologyMap_homeomorphTopCatSphere_symm (hb 0)
    -- By induction, `pr₁^* θ ⌣ pr₂^* x'` has infinite order on `S² × Pᵐ`.
    have key := TopCat.not_isOfFinAddOrder_integralCup_sphereGenerator Y (d := 1)
      (show 1 + 1 + 2 * m = 2 * (1 + m) by ring) (ih (fun i ↦ b i.succ) fun i ↦ hb i.succ)
    rw [← injective_zsmul_iff_not_isOfFinAddOrder] at key ⊢
    set x' := ∏ i : Fin m, Y.evenIntegralCohomologyOf 1
      (TopCat.singularCohomologyMap (TopCat.ofHom (ContinuousMap.eval i)) (2 * 1)
        (b i.succ))
    set x := ∏ i, (TopCat.of (Fin (m + 1) → P)).evenIntegralCohomologyOf 1
      (TopCat.singularCohomologyMap (TopCat.ofHom (ContinuousMap.eval i)) (2 * 1) (b i))
    -- Step 1: `Ψ` pulls the product `x` on `Pᵐ⁺¹` back to `pr₁^* (g^* b₀) ⌣ pr₂^* x'`, which is
    -- `k • (pr₁^* θ ⌣ pr₂^* x')` with `k ≠ 0`.
    have hx : TopCat.evenIntegralCohomologyMap Ψ x =
        (TopCat.sphere.{0} 2 ⊗ Y).evenIntegralCohomologyOf 1
          (TopCat.singularCohomologyMap (fst _ Y) (2 * 1)
            (TopCat.singularCohomologyMap g (2 * 1) (b 0))) *
        TopCat.evenIntegralCohomologyMap (snd _ Y) x' := by
      simp only [x, x', map_prod, map_mul, TopCat.evenIntegralCohomologyMap_of, Fin.prod_univ_succ]
      simp only [← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp, hΨ₀, hΨ]
    have hgk' : TopCat.singularCohomologyMap g (2 * 1) (b 0) =
        k • TopCat.integralSphereGenerator 1 := hgk
    have hx' := congrArg (· (1 + m)) hx
    rw [TopCat.evenIntegralCohomologyMap_apply, TopCat.evenIntegralCohomologyOf_mul_apply,
      TopCat.evenIntegralCohomologyMap_apply, hgk', map_zsmul,
      TopCat.integralCup_zsmul_left] at hx'
    -- Step 2: so `n • x ↦ (n * k) • (pr₁^* θ ⌣ pr₂^* x')` under `Ψ^*`, and cancelling `k`
    -- shows that `n ↦ n • x` is injective.
    have h3 : Function.Injective fun n : ℤ ↦ n • x (1 + m) := by
      intro n n' hnn
      refine mul_right_cancel₀ hk (key ?_)
      have := congrArg (TopCat.singularCohomologyMap Ψ (2 * (1 + m))) hnn
      rw [map_zsmul, map_zsmul, hx', smul_smul, smul_smul] at this
      exact this
    rwa [Nat.add_comm 1 m] at h3

/-- **The product of the first Chern classes on `(ℂP¹)ᵐ` has infinite order.** Let
`yᵢ ∈ H²((ℂP¹)ᵐ; ℤ)` be the first Chern class of the tautological line of `ℂP¹ = ℙ ℂ (Fin 2 → ℂ)`
pulled back along the `i`-th projection. Then the product `y₀ ⋯ y_{m-1}`, of degree `2m` in the
even integral cohomology ring, has infinite order. -/
theorem not_isOfFinAddOrder_prod_chernClass (m : ℕ) :
    ¬IsOfFinAddOrder ((∏ i : Fin m, (TopCat.of (Fin m → ℙ ℂ (Fin 2 → ℂ))).evenIntegralCohomologyOf 1
      (SymplecticGeometry.Bundle.chernClass ℂ
        (ContinuousMap.eval (X := fun _ : Fin m ↦ ℙ ℂ (Fin 2 → ℂ)) i *ᵖ
          (Tautological ℂ (Fin 2 → ℂ))) 1)) m) := by
  have hV : Module.finrank ℂ (Fin 2 → ℂ) = 1 + 1 := by simp
  -- `c₁(𝒪(-1)) = -h`: on a line the first Chern class is the Euler class, and `h` is minus it
  have hc : SymplecticGeometry.Bundle.chernClass ℂ (Tautological ℂ (Fin 2 → ℂ)) 1 =
      -hyperplaneClass (Fin 2 → ℂ) := by
    rw [SymplecticGeometry.Bundle.chernClass_one_eq_complexEulerClass _ _ (Module.finrank_self ℂ),
      hyperplaneClass_def, neg_neg]
  simp_rw [SymplecticGeometry.Bundle.chernClass_pullback, hc]
  have hh : hyperplaneClass (Fin 2 → ℂ) ≠ 0 := by
    simpa using (bijective_zsmul_hyperplaneClass hV one_pos).1.ne (one_ne_zero (α := ℤ))
  exact not_isOfFinAddOrder_prod_singularCohomologyMap m _ fun _ ↦ neg_ne_zero.2 hh

end Projectivization

end
