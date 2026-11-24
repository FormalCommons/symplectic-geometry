/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Circle
public import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance
public import TauCeti.AlgebraicTopology.Singular.ModuleChains.Basic
public import TauCeti.AlgebraicTopology.Singular.Torus.FirstHomology
public import TauCeti.AlgebraicTopology.UniversalCover.Circle.FreeLoop.Basic
public import TauCeti.Topology.Homotopy.Homotopic.With

/-!
# Circle-valued maps on first singular homology

For a space `Y`, the continuous maps `Y → S¹` into Mathlib's unit circle `Circle` form a group
under pointwise multiplication. This file shows that the map they induce on first singular
homology with integer coefficients is a homomorphism of this group into the additive group of
linear maps: `(u * v)_* = u_* + v_*` on `H₁(Y; ℤ)` (`ContinuousMap.singularHomologyMap_mul`). The
proof reduces to the universal case, the multiplication `S¹ × S¹ → S¹`, and checks it on the two
coordinate loops of the torus, which generate `H₁(S¹ × S¹; ℤ)` (`TauCeti.torusClass_eq`).

As a consequence, a self-map `w` of the circle acts on `H₁(S¹; ℤ)` as multiplication by its degree
`w.circleDegree` (`ContinuousMap.singularHomologyMap_eq_circleDegree_smul`): `w` is homotopic to
`z ↦ zⁿ` for `n` its degree (`Circle.joined_iff_circleDegree_eq`), which is the `n`-th power of the
identity in the group `C(S¹, S¹)`.

Both statements are also given for singular homology with coefficients
`ModuleCat.of ℤ (ULift ℤ)`, those of Tau Ceti's fundamental classes, by transporting them along the
isomorphism of coefficients `ULift ℤ ≅ ℤ` and comparing Mathlib's singular homology functor with
Tau Ceti's induced maps (`ContinuousMap.singularHomologyMap_eq_singularHomologyFunctor_map`). In
that form, reading `H₁(S¹)` in `ℤ` through `Circle.singularHomologyOneIso`, the image under
`u : Y → S¹` of the class of a free loop `ℓ : S¹ → Y` is the degree of `u ∘ ℓ`
(`ContinuousMap.singularHomologyOneIso_hom_map_map_inv_one`).

## Main results

* `ContinuousMap.singularHomologyMap_mul`, `ContinuousMap.singularHomologyFunctor_map_mul`: the
  pointwise product of two maps to the circle induces the sum of their maps on `H₁`.
* `ContinuousMap.singularHomologyMap_eq_circleDegree_smul`,
  `ContinuousMap.singularHomologyFunctor_map_eq_circleDegree_smul`,
  `ContinuousMap.singularHomologyOneIso_inv_map_hom`: a self-map of the circle acts on `H₁(S¹)` by
  its degree.
* `ContinuousMap.singularHomologyOneIso_hom_map_map_inv_one`: the image under `u` of the class of a
  free loop `ℓ` is the degree of `u ∘ ℓ`.
* `Circle.eq_zsmul_singularHomologyOneIso_inv_one`: every class of `H₁(S¹)` is the integer that
  `Circle.singularHomologyOneIso` gives it times the generator.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §2.2 (degree of a map
  of spheres) and §2.A, Theorem 2A.1 (`H₁` as the abelianization of `π₁`).
-/

public section

noncomputable section

open CategoryTheory AlgebraicTopology TauCeti TauCeti.HurewiczOne

namespace ContinuousMap

/-! ### Integer coefficients -/

/-- The multiplication `S¹ × S¹ → S¹` induces on `H₁(S¹ × S¹; ℤ)` the sum of the maps induced by
the two projections. -/
private theorem singularHomologyMap_fst_mul_snd :
    singularHomologyMap ℤ 1 (fst * snd : C(Circle × Circle, Circle)) =
      singularHomologyMap ℤ 1 (fst : C(Circle × Circle, Circle)) +
        singularHomologyMap ℤ 1 (snd : C(Circle × Circle, Circle)) := by
  ext x
  obtain ⟨p, q, rfl⟩ := exists_eq_torusClass x
  rw [torusClass_eq]
  simp only [map_add, map_zsmul, LinearMap.add_apply, singularHomologyMap_torusClass]
  -- On each coordinate loop, the product is the nonconstant factor, and the other factor is the
  -- constant loop at `1`, of class zero.
  have h₁₀ : loopClass ℤ (X := .of Circle)
        ((torusCurve 1 0).map (fst * snd : C(Circle × Circle, Circle)).continuous) =
      loopClass ℤ (X := .of Circle)
          ((torusCurve 1 0).map (fst : C(Circle × Circle, Circle)).continuous) +
        loopClass ℤ (X := .of Circle)
          ((torusCurve 1 0).map (snd : C(Circle × Circle, Circle)).continuous) := by
    rw [loopClass_eq_of_apply_eq (R := ℤ) (X := .of Circle)
        ((torusCurve 1 0).map (snd : C(Circle × Circle, Circle)).continuous)
        (Path.refl 1) fun t ↦ by simp [torusCurve_apply], loopClass_refl, add_zero]
    exact loopClass_eq_of_apply_eq _ _ fun t ↦ by simp [torusCurve_apply]
  have h₀₁ : loopClass ℤ (X := .of Circle)
        ((torusCurve 0 1).map (fst * snd : C(Circle × Circle, Circle)).continuous) =
      loopClass ℤ (X := .of Circle)
          ((torusCurve 0 1).map (fst : C(Circle × Circle, Circle)).continuous) +
        loopClass ℤ (X := .of Circle)
          ((torusCurve 0 1).map (snd : C(Circle × Circle, Circle)).continuous) := by
    rw [loopClass_eq_of_apply_eq (R := ℤ) (X := .of Circle)
        ((torusCurve 0 1).map (fst : C(Circle × Circle, Circle)).continuous)
        (Path.refl 1) fun t ↦ by simp [torusCurve_apply], loopClass_refl, zero_add]
    exact loopClass_eq_of_apply_eq _ _ fun t ↦ by simp [torusCurve_apply]
  rw [h₁₀, h₀₁, map_add, map_add]

variable {Y : Type} [TopologicalSpace Y]

/-- **Products of maps to the circle add on first homology.** The pointwise product `u * v` of two
maps `Y → S¹` induces on `H₁(Y; ℤ)` the sum of the maps induced by `u` and `v`. -/
theorem singularHomologyMap_mul (u v : C(Y, Circle)) :
    singularHomologyMap ℤ 1 (u * v) = singularHomologyMap ℤ 1 u + singularHomologyMap ℤ 1 v := by
  have h : u * v = (fst * snd : C(Circle × Circle, Circle)).comp (u.prodMk v) := ext fun _ ↦ rfl
  rw [h, singularHomologyMap_comp', singularHomologyMap_fst_mul_snd, LinearMap.add_comp,
    ← singularHomologyMap_comp', ← singularHomologyMap_comp',
    show (fst : C(Circle × Circle, Circle)).comp (u.prodMk v) = u from ext fun _ ↦ rfl,
    show (snd : C(Circle × Circle, Circle)).comp (u.prodMk v) = v from ext fun _ ↦ rfl]

/-- The map induced on `H₁(Y; ℤ)`, as an additive homomorphism from the group of maps `Y → S¹`
under pointwise multiplication. -/
private def singularHomologyMapAddHom :
    Additive C(Y, Circle) →+ (((singularChains ℤ).obj (TopCat.of Y)).homology 1 →ₗ[ℤ]
      ((singularChains ℤ).obj (TopCat.of Circle)).homology 1) :=
  AddMonoidHom.mk' (fun u ↦ singularHomologyMap ℤ 1 u.toMul) fun u v ↦
    singularHomologyMap_mul u.toMul v.toMul

/-- **A self-map of the circle acts on `H₁(S¹; ℤ)` by its degree.** -/
theorem singularHomologyMap_eq_circleDegree_smul (w : C(Circle, Circle)) :
    singularHomologyMap ℤ 1 w = w.circleDegree • LinearMap.id := by
  -- `w` is homotopic to `z ↦ zⁿ`, `n` its degree, since the two are joined in `C(S¹, S¹)`.
  obtain ⟨γ⟩ := Circle.joined_iff_circleDegree_eq.2 (circleDegree_zpow w.circleDegree).symm
  have hw : w.Homotopic (ContinuousMap.id Circle ^ w.circleDegree) := by
    have hpow : (⟨(· ^ w.circleDegree), continuous_zpow _⟩ : C(Circle, Circle)) =
        ContinuousMap.id Circle ^ w.circleDegree := by
      ext z
      simp
    rw [← hpow]
    exact homotopic_iff_joined.2 ⟨γ⟩
  have h := map_zsmul singularHomologyMapAddHom w.circleDegree
    (Additive.ofMul (ContinuousMap.id Circle))
  simp only [singularHomologyMapAddHom, AddMonoidHom.mk'_apply, ← ofMul_zpow, toMul_ofMul,
    singularHomologyMap_id'] at h
  rw [singularHomologyMap_eq_of_homotopic ℤ 1 hw, h]

end ContinuousMap

/-! ### Coefficients `ULift ℤ` -/

namespace ContinuousMap

variable {Y : Type} [TopologicalSpace Y]

/-- **Products of maps to the circle add on first homology**, with coefficients `ULift ℤ`. -/
theorem singularHomologyFunctor_map_mul (u v : C(Y, Circle)) :
    ((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ (ULift.{0} ℤ))).map
        (TopCat.ofHom (u * v)) =
      ((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ (ULift.{0} ℤ))).map
          (TopCat.ofHom u) +
        ((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ (ULift.{0} ℤ))).map
          (TopCat.ofHom v) := by
  -- Transport from coefficients `ℤ` along the isomorphism of coefficients `ULift ℤ ≅ ℤ`.
  let α := (singularHomologyFunctor (ModuleCat.{0} ℤ) 1).mapIso
    (ULift.moduleEquiv (R := ℤ) (M := ℤ)).toModuleIso
  have h : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ ℤ)).map
        (TopCat.ofHom (u * v)) =
      ((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ ℤ)).map
          (TopCat.ofHom u) +
        ((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ ℤ)).map
          (TopCat.ofHom v) := by
    ext1
    rw [ModuleCat.hom_add, ← singularHomologyMap_eq_singularHomologyFunctor_map,
      ← singularHomologyMap_eq_singularHomologyFunctor_map,
      ← singularHomologyMap_eq_singularHomologyFunctor_map]
    -- The two sides differ only in how the homology modules are written.
    exact singularHomologyMap_mul u v
  rw [← NatIso.naturality_2 α, ← NatIso.naturality_2 α, ← NatIso.naturality_2 α, h,
    Preadditive.add_comp, Preadditive.comp_add]

/-- **A self-map of the circle acts on `H₁(S¹)` by its degree**, with coefficients `ULift ℤ`. -/
theorem singularHomologyFunctor_map_eq_circleDegree_smul (w : C(Circle, Circle)) :
    ((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ (ULift.{0} ℤ))).map
        (TopCat.ofHom w) = w.circleDegree • 𝟙 _ := by
  -- Transport from coefficients `ℤ` along the isomorphism of coefficients `ULift ℤ ≅ ℤ`.
  let α := (singularHomologyFunctor (ModuleCat.{0} ℤ) 1).mapIso
    (ULift.moduleEquiv (R := ℤ) (M := ℤ)).toModuleIso
  have h : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ ℤ)).map
      (TopCat.ofHom w) = w.circleDegree • 𝟙 _ := by
    ext1
    rw [ModuleCat.hom_zsmul, ModuleCat.hom_id,
      ← singularHomologyMap_eq_singularHomologyFunctor_map]
    -- The two sides differ only in how the homology modules are written.
    exact singularHomologyMap_eq_circleDegree_smul w
  rw [← NatIso.naturality_2 α, h, Preadditive.zsmul_comp,
    Preadditive.comp_zsmul, Category.id_comp, Iso.hom_inv_id_app]

/-- **A self-map of the circle acts by its degree**, read in `ℤ` through
`Circle.singularHomologyOneIso`: on `ULift ℤ`, the map induced by `w` is multiplication by
`w.circleDegree`. -/
theorem singularHomologyOneIso_inv_map_hom (w : C(Circle, Circle)) :
    (Circle.singularHomologyOneIso (ModuleCat.of ℤ (ULift.{0} ℤ))).inv ≫
        ((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ (ULift.{0} ℤ))).map
          (TopCat.ofHom w) ≫ (Circle.singularHomologyOneIso (ModuleCat.of ℤ (ULift.{0} ℤ))).hom =
      w.circleDegree • 𝟙 _ := by
  rw [singularHomologyFunctor_map_eq_circleDegree_smul, Preadditive.zsmul_comp,
    Preadditive.comp_zsmul, Category.id_comp, Iso.inv_hom_id]

/-- **Maps to the circle on loops.** For a free loop `ℓ : S¹ → Y` and `u : Y → S¹`, read in `ℤ`
through `Circle.singularHomologyOneIso`, the image under `u` of the class of `ℓ` (the
push-forward along `ℓ` of the generator of `H₁(S¹)`) is the degree of `u ∘ ℓ`. -/
theorem singularHomologyOneIso_hom_map_map_inv_one (ℓ : C(Circle, Y)) (u : C(Y, Circle)) :
    (Circle.singularHomologyOneIso (ModuleCat.of ℤ (ULift.{0} ℤ))).hom.hom
        ((((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ (ULift.{0} ℤ))).map
          (TopCat.ofHom u)).hom
          ((((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
            (ModuleCat.of ℤ (ULift.{0} ℤ))).map (TopCat.ofHom ℓ)).hom
            ((Circle.singularHomologyOneIso (ModuleCat.of ℤ (ULift.{0} ℤ))).inv.hom
              (ULift.up 1)))) =
      ULift.up (u.comp ℓ).circleDegree := by
  have h := congrArg (fun f ↦ f.hom (ULift.up 1)) (singularHomologyOneIso_inv_map_hom (u.comp ℓ))
  simp only [TopCat.ofHom_comp, Functor.map_comp, ModuleCat.hom_comp, ModuleCat.hom_zsmul,
    ModuleCat.hom_id, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply] at h
  rw [h]
  ext
  simp

end ContinuousMap

namespace Circle

/-- A class `x` of `H₁(Circle)` is `n • g`, for `g` the generator and `n` the integer that
`Circle.singularHomologyOneIso` gives to `x`. -/
theorem eq_zsmul_singularHomologyOneIso_inv_one
    (x : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ (ULift.{0} ℤ))).obj
      (TopCat.of Circle)) :
    x = ((singularHomologyOneIso (ModuleCat.of ℤ (ULift.{0} ℤ))).hom.hom x).down •
      (singularHomologyOneIso (ModuleCat.of ℤ (ULift.{0} ℤ))).inv.hom (ULift.up 1) := by
  have h : (singularHomologyOneIso (ModuleCat.of ℤ (ULift.{0} ℤ))).hom.hom x =
      ((singularHomologyOneIso (ModuleCat.of ℤ (ULift.{0} ℤ))).hom.hom x).down • ULift.up 1 := by
    ext
    simp
  rw [← map_zsmul, ← h]
  simp

end Circle

end
