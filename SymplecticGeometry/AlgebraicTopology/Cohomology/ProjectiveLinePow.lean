/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Cohomology.IntegralCohomologyULift
public import SymplecticGeometry.AlgebraicTopology.Cohomology.EvenIntegralCohomology
public import SymplecticGeometry.Topology.VectorBundle.Complex.ChernClass.Naturality
public import SymplecticGeometry.Topology.VectorBundle.Complex.ChernClass.ProjectiveSpace
public import TauCeti.AlgebraicTopology.Cohomology.Sphere.Product
public import TauCeti.AlgebraicTopology.Disk
public import TauCeti.Topology.ComplexProjectiveSpace.Projectivization
public import TauCeti.Topology.ComplexProjectiveSpace.Sphere2

/-!
# The top product of first Chern classes on `(ℂP¹)ᵐ`

Write `P = ℙ ℂ (Fin 2 → ℂ)` for the complex projective line and `h ∈ H²(P; ℤ)` for its hyperplane
class. This file shows that on the product `Pᵐ = Fin m → P` the cup product of the first Chern
classes `yᵢ = c₁(prᵢ^* 𝒪(-1))` of the tautological lines pulled back along the projections is a
class of infinite order in `H^{2m}(Pᵐ; ℤ)`.

## Main results

* `TopCat.not_isOfFinAddOrder_integralCup_sphereGenerator`: for a space `Y` and a class `c` of
  infinite order in `Hⁿ(Y; ℤ)`, the class `pr₁^* θ ⌣ pr₂^* c` of `Sᵈ⁺¹ × Y` has infinite order,
  where `θ ∈ Hᵈ⁺¹(Sᵈ⁺¹; ℤ)` is dual to the standard generator of the homology of the sphere. It is
  read off Tau Ceti's decomposition `TopCat.singularCohomologySphereProdSlantEquiv` of the
  cohomology of `Sᵈ⁺¹ × Y`, whose inverse sends `(0, c)` to `pr₁^* θ ⌣ pr₂^* c`.
* `TopCat.exists_eq_zsmul_sphereGenerator`: `θ` generates `Hᵈ⁺¹(Sᵈ⁺¹; ℤ)`.
* `Projectivization.singularCohomologyMap_sphereGenerator_eq_hyperplaneClass_or`: under any
  homeomorphism `e : P ≃ₜ S²`, `θ` pulls back to `h` or to `-h`. Since `c₁(𝒪(-1)) = -h`
  (by `SymplecticGeometry.Bundle.chernClass_one_eq_complexEulerClass` and the definition of `h`),
  it pulls back to `±c₁` of the tautological line.
* `Projectivization.not_isOfFinAddOrder_prod_singularCohomologyMap`: for nonzero classes
  `bᵢ ∈ H²(P; ℤ)`, the product of the pull-backs `prᵢ^* bᵢ`, the component of degree `2m` of a
  product in the even integral cohomology ring of `Pᵐ`, has infinite order.
* `Projectivization.not_isOfFinAddOrder_prod_chernClass`: the product of the classes `yᵢ` has
  infinite order in `H^{2m}(Pᵐ; ℤ)`.

The proof is by induction on `m`. For the step, a homeomorphism `S² ≃ₜ P`, assembled from Tau
Ceti's `TauCeti.ComplexProjectiveSpace.homeomorphSphere2`, gives a map `S² × Pᵐ → Pᵐ⁺¹`; it pulls
the product on `Pᵐ⁺¹` back to a nonzero multiple of `pr₁^* θ ⌣ pr₂^* c`, with `c` the product on
`Pᵐ`, and the first result applies.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Theorem 3.15 (the Künneth
  formula).
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory

namespace TopCat

open TauCeti

/-- **Products with the sphere generator keep infinite order.** Let `θ ∈ Hᵈ⁺¹(Sᵈ⁺¹; ℤ)` be the
integral class dual to the standard generator of `H_{d+1}(Sᵈ⁺¹)`. If `c ∈ Hⁿ(Y; ℤ)` has infinite
order, then so has `pr₁^* θ ⌣ pr₂^* c ∈ H^N(Sᵈ⁺¹ × Y; ℤ)`, `N = d + 1 + n`. -/
theorem not_isOfFinAddOrder_integralCup_sphereGenerator (Y : TopCat.{0}) {d n N : ℕ}
    (h : d + 1 + n = N) {c : Y.integralCohomology n} (hc : ¬IsOfFinAddOrder c) :
    ¬IsOfFinAddOrder ((sphere.{0} (d + 1) ⊗ Y).integralCup (d + 1) n N h
      (TopCat.singularCohomologyMap (fst _ Y) (d + 1)
        (((sphere.{0} (d + 1)).integralCohomologyEquiv (d + 1)).symm
          (singularCohomologyTopCatSphereGenerator ℤ d)))
      (TopCat.singularCohomologyMap (snd _ Y) n c)) := by
  obtain rfl : N = n + (d + 1) := by omega
  -- the class is the image of `(0, c)` under the decomposition of the cohomology of `Sᵈ⁺¹ × Y`
  set e₁ := (sphere.{0} (d + 1) ⊗ Y).integralCohomologyEquiv (n + (d + 1))
  set S := singularCohomologySphereProdSlantEquiv (𝟙_ (ModuleCat.{0} ℤ)) Y (sphereBasePoint d) n
  have hFc : (sphere.{0} (d + 1) ⊗ Y).integralCup (d + 1) n (n + (d + 1)) h
      (TopCat.singularCohomologyMap (fst _ Y) (d + 1)
        (((sphere.{0} (d + 1)).integralCohomologyEquiv (d + 1)).symm
          (singularCohomologyTopCatSphereGenerator ℤ d)))
      (TopCat.singularCohomologyMap (snd _ Y) n c) =
        e₁.symm (S.symm (0, Y.integralCohomologyEquiv n c)) := by
    rw [singularCohomologySphereProdSlantEquiv_symm_apply, map_zero, zero_add,
      integralCohomologyEquiv_symm_singularCup, integralCohomologyEquiv_symm_naturality,
      integralCohomologyEquiv_symm_naturality, LinearEquiv.symm_apply_apply]
  rw [hFc]
  refine fun hfin ↦ hc ?_
  rw [isOfFinAddOrder_iff_nsmul_eq_zero] at hfin ⊢
  obtain ⟨k, hk, hkc⟩ := hfin
  refine ⟨k, hk, (Y.integralCohomologyEquiv n).injective ?_⟩
  have := congrArg (fun x ↦ (S (e₁ x)).2) hkc
  simpa using this

/-- Every class of `Hᵈ⁺¹(Sᵈ⁺¹; ℤ)` is an integer multiple of the generator `θ`, the integral
class dual to the standard generator of `H_{d+1}(Sᵈ⁺¹)`. -/
theorem exists_eq_zsmul_sphereGenerator {d : ℕ}
    (x : (sphere.{0} (d + 1)).integralCohomology (d + 1)) :
    ∃ r : ℤ, x = r • ((sphere.{0} (d + 1)).integralCohomologyEquiv (d + 1)).symm
      (singularCohomologyTopCatSphereGenerator ℤ d) := by
  set e := (sphere.{0} (d + 1)).integralCohomologyEquiv (d + 1)
  set s := singularCohomologyTopCatSphereEquiv ℤ (𝟙_ (ModuleCat.{0} ℤ)) d
  have hθ : s (singularCohomologyTopCatSphereGenerator ℤ d) = 1 :=
    (singularCohomologyTopCatSphereEquiv_apply _ _ _ _).trans
      (singularKronecker_singularCohomologyTopCatSphereGenerator ℤ d)
  refine ⟨s (e x), e.injective (s.injective ?_)⟩
  rw [map_zsmul, map_zsmul, LinearEquiv.apply_symm_apply, hθ, smul_eq_mul, mul_one]

end TopCat

namespace Projectivization

open Bundle TauCeti
open scoped LinearAlgebra.Projectivization

/-- **The hyperplane class of `ℂP¹` generates `H²(ℂP¹; ℤ)` as the sphere generator does.** Under
any homeomorphism `e : ℙ ℂ (Fin 2 → ℂ) ≃ₜ S²`, the integral class `θ` dual to the standard
generator of `H₂(S²)` pulls back to the hyperplane class `h` or to `-h`. -/
theorem singularCohomologyMap_sphereGenerator_eq_hyperplaneClass_or
    (e : ℙ ℂ (Fin 2 → ℂ) ≃ₜ TopCat.sphere.{0} 2) :
    TopCat.singularCohomologyMap (TopCat.ofHom ⟨e, e.continuous⟩) 2
        (((TopCat.sphere.{0} 2).integralCohomologyEquiv 2).symm
          (singularCohomologyTopCatSphereGenerator ℤ 1)) = hyperplaneClass (Fin 2 → ℂ) ∨
      TopCat.singularCohomologyMap (TopCat.ofHom ⟨e, e.continuous⟩) 2
        (((TopCat.sphere.{0} 2).integralCohomologyEquiv 2).symm
          (singularCohomologyTopCatSphereGenerator ℤ 1)) = -hyperplaneClass (Fin 2 → ℂ) := by
  have hV : Module.finrank ℂ (Fin 2 → ℂ) = 1 + 1 := by simp
  obtain ⟨a, ha⟩ := exists_eq_zsmul_hyperplaneClass hV
    (TopCat.singularCohomologyMap (TopCat.ofHom ⟨e, e.continuous⟩) 2
      (((TopCat.sphere.{0} 2).integralCohomologyEquiv 2).symm
        (singularCohomologyTopCatSphereGenerator ℤ 1)))
  obtain ⟨b, hb⟩ := TopCat.exists_eq_zsmul_sphereGenerator (d := 1)
    (TopCat.singularCohomologyMap (TopCat.ofHom ⟨e.symm, e.symm.continuous⟩) 2
      (hyperplaneClass (Fin 2 → ℂ)))
  have hcomp : TopCat.ofHom ⟨e, e.continuous⟩ ≫ TopCat.ofHom ⟨e.symm, e.symm.continuous⟩ = 𝟙 _ := by
    ext x
    exact e.symm_apply_apply x
  have hba : (b * a) • hyperplaneClass (Fin 2 → ℂ) = (1 : ℤ) • hyperplaneClass (Fin 2 → ℂ) := by
    rw [one_smul, mul_smul, ← ha, ← map_zsmul, ← hb, ← ConcreteCategory.comp_apply,
      ← TopCat.singularCohomologyMap_comp, hcomp, TopCat.singularCohomologyMap_id,
      ConcreteCategory.id_apply]
  rcases Int.eq_one_or_neg_one_of_mul_eq_one'
    ((bijective_zsmul_hyperplaneClass hV one_pos).1 hba) with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · exact .inl (ha.trans (one_smul _ _))
  · exact .inr (ha.trans (neg_one_zsmul _))

/-- A homeomorphism `ℙ ℂ (Fin 2 → ℂ) ≃ₜ S²`: Tau Ceti's homeomorphisms of `ℂP¹` with the sphere
quotient model, of that with the unit sphere of `ℝ³`, and of that with `TopCat.sphere 2`. -/
private def homeomorphSphere : ℙ ℂ (Fin 2 → ℂ) ≃ₜ TopCat.sphere.{0} 2 :=
  (ComplexProjectiveSpace.homeomorphProjectivization 1).symm.trans
    (ComplexProjectiveSpace.homeomorphSphere2.trans
      (sphereHomeomorphTopCatSphere (by simp)))

/-- A nonzero class of `H²(ℂP¹; ℤ)` pulls back to a nonzero multiple of the sphere generator along
the inverse of `homeomorphSphere`. -/
private theorem exists_singularCohomologyMap_homeomorphSphere_symm
    {b : (TopCat.of (ℙ ℂ (Fin 2 → ℂ))).integralCohomology 2} (hb : b ≠ 0) :
    ∃ k : ℤ, k ≠ 0 ∧
      TopCat.singularCohomologyMap (TopCat.ofHom ⟨homeomorphSphere.symm,
        homeomorphSphere.symm.continuous⟩) 2 b =
        k • ((TopCat.sphere.{0} 2).integralCohomologyEquiv 2).symm
          (singularCohomologyTopCatSphereGenerator ℤ 1) := by
  have hV : Module.finrank ℂ (Fin 2 → ℂ) = 1 + 1 := by simp
  obtain ⟨j, rfl⟩ := exists_eq_zsmul_hyperplaneClass hV b
  have hj : j ≠ 0 := by rintro rfl; exact hb (zero_smul _ _)
  have hcomp : TopCat.ofHom ⟨homeomorphSphere.symm, homeomorphSphere.symm.continuous⟩ ≫
      TopCat.ofHom ⟨homeomorphSphere, homeomorphSphere.continuous⟩ = 𝟙 (TopCat.sphere.{0} 2) := by
    ext x
    exact homeomorphSphere.apply_symm_apply x
  have hback : TopCat.singularCohomologyMap
      (TopCat.ofHom ⟨homeomorphSphere.symm, homeomorphSphere.symm.continuous⟩) 2
      (TopCat.singularCohomologyMap
        (TopCat.ofHom ⟨homeomorphSphere, homeomorphSphere.continuous⟩) 2
          (((TopCat.sphere.{0} 2).integralCohomologyEquiv 2).symm
            (singularCohomologyTopCatSphereGenerator ℤ 1))) =
      ((TopCat.sphere.{0} 2).integralCohomologyEquiv 2).symm
        (singularCohomologyTopCatSphereGenerator ℤ 1) := by
    rw [← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp, hcomp,
      TopCat.singularCohomologyMap_id, ConcreteCategory.id_apply]
  rcases singularCohomologyMap_sphereGenerator_eq_hyperplaneClass_or homeomorphSphere with h | h
  · exact ⟨j, hj, by rw [map_zsmul, ← h, hback]⟩
  · have h' : hyperplaneClass (Fin 2 → ℂ) = -TopCat.singularCohomologyMap
        (TopCat.ofHom ⟨homeomorphSphere, homeomorphSphere.continuous⟩) 2
          (((TopCat.sphere.{0} 2).integralCohomologyEquiv 2).symm
            (singularCohomologyTopCatSphereGenerator ℤ 1)) := by
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
    let g : TopCat.sphere.{0} 2 ⟶ TopCat.of P :=
      TopCat.ofHom ⟨homeomorphSphere.symm, homeomorphSphere.symm.continuous⟩
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
    obtain ⟨k, hk, hgk⟩ := exists_singularCohomologyMap_homeomorphSphere_symm (hb 0)
    have key := TopCat.not_isOfFinAddOrder_integralCup_sphereGenerator Y (d := 1)
      (show 1 + 1 + 2 * m = 2 * (1 + m) by ring) (ih (fun i ↦ b i.succ) fun i ↦ hb i.succ)
    rw [← injective_zsmul_iff_not_isOfFinAddOrder] at key ⊢
    set x' := ∏ i : Fin m, Y.evenIntegralCohomologyOf 1
      (TopCat.singularCohomologyMap (TopCat.ofHom (ContinuousMap.eval i)) (2 * 1)
        (b i.succ))
    set x := ∏ i, (TopCat.of (Fin (m + 1) → P)).evenIntegralCohomologyOf 1
      (TopCat.singularCohomologyMap (TopCat.ofHom (ContinuousMap.eval i)) (2 * 1) (b i))
    have hx : TopCat.evenIntegralCohomologyMap Ψ x =
        (TopCat.sphere.{0} 2 ⊗ Y).evenIntegralCohomologyOf 1
          (TopCat.singularCohomologyMap (fst _ Y) (2 * 1)
            (TopCat.singularCohomologyMap g (2 * 1) (b 0))) *
        TopCat.evenIntegralCohomologyMap (snd _ Y) x' := by
      simp only [x, x', map_prod, map_mul, TopCat.evenIntegralCohomologyMap_of, Fin.prod_univ_succ]
      simp only [← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp, hΨ₀, hΨ]
    have hgk' : TopCat.singularCohomologyMap g (2 * 1) (b 0) =
        k • ((TopCat.sphere.{0} 2).integralCohomologyEquiv 2).symm
          (singularCohomologyTopCatSphereGenerator ℤ 1) := hgk
    have hx' := congrArg (· (1 + m)) hx
    rw [TopCat.evenIntegralCohomologyMap_apply, TopCat.evenIntegralCohomologyOf_mul_apply,
      TopCat.evenIntegralCohomologyMap_apply, hgk', map_zsmul,
      TopCat.integralCup_zsmul_left] at hx'
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
