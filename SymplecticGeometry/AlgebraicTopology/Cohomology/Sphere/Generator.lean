/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Cohomology.IntegralKronecker
public import TauCeti.AlgebraicTopology.Cohomology.FundamentalClass
public import TauCeti.AlgebraicTopology.Cohomology.Sphere.Product
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Sphere

/-!
# Generators of the top cohomology of spheres and of products of two spheres

Let `θ ∈ Hᵈ⁺¹(Sᵈ⁺¹; ℤ)` be Tau Ceti's class `singularCohomologyTopCatSphereGenerator`, dual to the
standard generator of `H_{d+1}(Sᵈ⁺¹)`, carried into the library's integral cohomology by
`TopCat.integralCohomologyEquiv`, which this file names `TopCat.integralSphereGenerator`. It
shows that `θ` generates `Hᵈ⁺¹(Sᵈ⁺¹; ℤ)`, and that cup product with its pull-back to `Sᵈ⁺¹ × Y`
keeps classes of infinite order, and that on a compact connected oriented manifold homeomorphic to
`Sᵈ⁺¹`, evaluation on the fundamental class agrees with evaluation on the standard generator up to
one sign. It also shows
that, over any commutative ring `k`, the class `pr₁^* θ_a ⌣ pr₂^* θ_b` spans `Hᵃ⁺ᵇ(Sᵃ × Sᵇ; k)`
and takes the value `1` on the cross product `γ_a × γ_b` of the homology generators.

## Main results

* `TauCeti.singularCohomologyTopCatSphereEquiv_singularCohomologyTopCatSphereGenerator`: over
  any commutative ring, `θ` evaluates to `1` on the standard homology generator.
* `TopCat.exists_eq_zsmul_sphereGenerator`: every class of `Hᵈ⁺¹(Sᵈ⁺¹; ℤ)` is an integer
  multiple of `θ`.
* `HomologicalOrientation.exists_singularCohomologyTopCatSphereEquiv_eq_mul_evalFundamentalClass`:
  for a compact connected manifold `M` with an orientation `o` and a homeomorphism
  `e : M ≃ₜ Sᵈ⁺¹`, there is one sign `s = ±1` such that every class `u` of `Hᵈ⁺¹(Sᵈ⁺¹; ℤ)` has
  `⟨u, γ⟩ = s * ⟨u, e_*[M]⟩`. The image of the standard generator `γ` in homology with the
  coefficients `ULift ℤ` of Tau Ceti's fundamental classes is a fundamental class
  (`TauCeti.isFundamentalClass_singularHomologyTopCatSphereGenerator`), so it is `±e_*[M]`
  (`TauCeti.HomologicalOrientation.exists_eq_smul_mapFundamentalClass_of_isFundamentalClass`).
* `TopCat.not_isOfFinAddOrder_integralCup_sphereGenerator`: for a space `Y` and a class `c` of
  infinite order in `Hⁿ(Y; ℤ)`, the class `pr₁^* θ ⌣ pr₂^* c` of `Sᵈ⁺¹ × Y` has infinite order.
  It is read off Tau Ceti's decomposition `TopCat.singularCohomologySphereProdSlantEquiv` of the
  cohomology of `Sᵈ⁺¹ × Y`, whose inverse sends `(0, c)` to `pr₁^* θ ⌣ pr₂^* c`.

For two spheres, over any commutative ring `k`, with `θ_a`, `θ_b` the dual generators of the
top cohomology of `Sᵃ` and `Sᵇ`, `a, b ≥ 1`, and `γ_a`, `γ_b` the standard homology generators:

* `TopCat.exists_eq_smul_singularCup_sphereGenerator`: every class of `Hᵃ⁺ᵇ(Sᵃ × Sᵇ; k)` is a
  multiple of `pr₁^* θ_a ⌣ pr₂^* θ_b`. The decomposition above, with `Y = Sᵇ`, has a first
  summand `Hᵃ⁺ᵇ(Sᵇ; k) = 0` and a second summand `Hᵇ(Sᵇ; k)`, spanned by `θ_b`.
* `TopCat.singularKronecker_singularCup_sphereGenerator_singularHomologyCross`: the class
  `pr₁^* θ_a ⌣ pr₂^* θ_b` takes the value `1` on the cross product `γ_a × γ_b`, by Tau Ceti's
  `TopCat.singularKronecker_singularCup_fst_snd_singularHomologyCross`.
* `TopCat.eq_singularKronecker_smul_singularCup_sphereGenerator`: so every class `x` of
  `Hᵃ⁺ᵇ(Sᵃ × Sᵇ; k)` is `⟨x, γ_a × γ_b⟩ • (pr₁^* θ_a ⌣ pr₂^* θ_b)`.
* `TopCat.singularCohomologyMap_eq_singularKronecker_smul_singularCup_sphereGenerator`: for a
  map `f : Sᵃ × Sᵇ ⟶ Z` and a class `u` of `Hᵃ⁺ᵇ(Z; k)`,
  `f^* u = ⟨u, f_*(γ_a × γ_b)⟩ • (pr₁^* θ_a ⌣ pr₂^* θ_b)`, by the naturality
  `TopCat.singularKronecker_naturality` of the Kronecker pairing.
* `TopCat.eq_integralKronecker_zsmul_integralCup_sphereGenerator`: in the integral cohomology
  `TopCat.integralCohomology`, every class `x` of degree `a + b` of `Sᵃ × Sᵇ` is
  `⟨x, γ_a × γ_b⟩ • (pr₁^* θ_a ⌣ pr₂^* θ_b)`, an integer multiple of the integral cup product,
  the pairing being the integral Kronecker pairing `TopCat.integralKronecker`. Hence
  `TopCat.exists_eq_zsmul_integralCup_sphereGenerator`. The passage between the two cohomologies
  is `TopCat.integralCohomologyEquiv_symm_singularCup_sphereGenerator`, stated on `Sᵃ × Y` for
  any space `Y`.
* `TopCat.integralKronecker_integralCup_sphereGenerator` and
  `TopCat.singularCohomologyMap_eq_integralKronecker_zsmul_integralCup_sphereGenerator`: the
  integral forms of the value `1` on `γ_a × γ_b` and of the formula for `f^* u`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Theorem 3.15 (the Künneth
  formula) and Section 3.3 (fundamental classes).
-/

public section

universe w

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace TauCeti

/-- Over a commutative ring `k`, the generator `θ ∈ Hⁿ⁺¹(Sⁿ⁺¹; k)` dual to the standard homology
generator is sent to `1` by the evaluation `TauCeti.singularCohomologyTopCatSphereEquiv` on that
generator. -/
theorem singularCohomologyTopCatSphereEquiv_singularCohomologyTopCatSphereGenerator
    (k : Type w) [CommRing k] (n : ℕ) :
    singularCohomologyTopCatSphereEquiv k (𝟙_ (ModuleCat.{w} k)) n
      (singularCohomologyTopCatSphereGenerator k n) = 1 :=
  (singularCohomologyTopCatSphereEquiv_apply _ _ _ _).trans
    (singularKronecker_singularCohomologyTopCatSphereGenerator k n)

namespace HomologicalOrientation

variable {M E : Type} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  [CompactSpace M] {d : ℕ} (o : HomologicalOrientation M E (d + 1))
  (hn : Module.finrank ℝ E = d + 1)

/-- **Fundamental classes of a sphere and the standard generator.** Let `M` be a compact
`(d + 1)`-manifold with an orientation `o`, and `e : M ≃ₜ Sᵈ⁺¹` a homeomorphism. There is a sign
`s = ±1` such that for every class `u ∈ Hᵈ⁺¹(Sᵈ⁺¹; ℤ)` of the integral cohomology
`TopCat.integralCohomology`, the value of `u` on the standard generator, read through
`TopCat.integralCohomologyEquiv` and `TauCeti.singularCohomologyTopCatSphereEquiv`, is `s` times
its value `TauCeti.HomologicalOrientation.evalFundamentalClass` on the image `e_*[M]` of the
fundamental class. -/
theorem exists_singularCohomologyTopCatSphereEquiv_eq_mul_evalFundamentalClass
    (e : M ≃ₜ TopCat.sphere.{0} (d + 1)) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ ∀ u : (TopCat.sphere.{0} (d + 1)).integralCohomology (d + 1),
      singularCohomologyTopCatSphereEquiv ℤ (𝟙_ (ModuleCat.{0} ℤ)) d
          ((TopCat.sphere.{0} (d + 1)).integralCohomologyEquiv (d + 1) u) =
        s * o.evalFundamentalClass hn (ModuleCat.of ℤ ℤ)
          (e : C(M, TopCat.sphere.{0} (d + 1))) u := by
  have : ConnectedSpace M := e.symm.surjective.connectedSpace e.symm.continuous
  -- the standard generator, with the coefficients `ULift ℤ` of `[M]`, is `±e_*[M]`
  have hγ := (isFundamentalClass_singularHomologyFunctor_map_app_iff integralCoeffIso.symm
    (singularHomologyTopCatSphereGenerator ℤ d)).2
    (isFundamentalClass_singularHomologyTopCatSphereGenerator ℤ d)
  obtain ⟨s, hs, h⟩ := o.exists_eq_smul_mapFundamentalClass_of_isFundamentalClass hn e hγ
  refine ⟨s, hs, fun u ↦ ?_⟩
  rw [singularCohomologyTopCatSphereEquiv_apply, TopCat.singularKronecker_integralCohomologyEquiv,
    ConcreteCategory.comp_apply]
  rw [Iso.symm_hom] at h
  -- `h` is stated on `TopCat.of` of the carrier of `TopCat.sphere (d + 1)`, so it is applied
  -- through `congrArg` rather than used in a rewrite
  refine (congrArg ((TopCat.sphere.{0} (d + 1)).singularKronecker ℤ (d + 1) u).hom h).trans ?_
  rw [map_zsmul, evalFundamentalClass_apply, smul_eq_mul]

end HomologicalOrientation

end TauCeti

namespace TopCat

open TauCeti

/-- The generator `θ ∈ Hᵈ⁺¹(Sᵈ⁺¹; ℤ)` of integral cohomology: Tau Ceti's class
`TauCeti.singularCohomologyTopCatSphereGenerator` with coefficients `ℤ`, dual to the standard
generator of `H_{d+1}(Sᵈ⁺¹)`, carried into `TopCat.integralCohomology` by the inverse of
`TopCat.integralCohomologyEquiv`. -/
noncomputable def integralSphereGenerator (d : ℕ) :
    (sphere.{0} (d + 1)).integralCohomology (d + 1) :=
  ((sphere.{0} (d + 1)).integralCohomologyEquiv (d + 1)).symm
    (singularCohomologyTopCatSphereGenerator ℤ d)

theorem integralSphereGenerator_def (d : ℕ) :
    integralSphereGenerator d = ((sphere.{0} (d + 1)).integralCohomologyEquiv (d + 1)).symm
      (singularCohomologyTopCatSphereGenerator ℤ d) :=
  (rfl)

@[simp]
theorem integralCohomologyEquiv_integralSphereGenerator (d : ℕ) :
    (sphere.{0} (d + 1)).integralCohomologyEquiv (d + 1) (integralSphereGenerator d) =
      singularCohomologyTopCatSphereGenerator ℤ d := by
  rw [integralSphereGenerator_def, LinearEquiv.apply_symm_apply]

section IntegerCoefficients

/- The cup product with coefficients `ℤ` below carries the `ℤ`-linear structure
`ModuleCat.instLinear`, the one of `TopCat.integralCohomologyEquiv_symm_singularCup`. Instance
search would otherwise find `CategoryTheory.Linear.preadditiveIntLinear`, which integral
cohomology uses; the pull-backs in integral cohomology name that structure. -/
attribute [local instance high] ModuleCat.instLinear

/-- **Cup products with the sphere generator in integral cohomology.** On `Sᵈ⁺¹ × Y`, the
inverse of `TopCat.integralCohomologyEquiv` carries the cup product `pr₁^* θ ⌣ pr₂^* c` with
coefficients `ℤ`, `θ` being Tau Ceti's generator, to the integral cup product
`pr₁^* θ ⌣ pr₂^* c'` of the integral generator `TopCat.integralSphereGenerator` and the image `c'`
of `c` in integral cohomology. -/
theorem integralCohomologyEquiv_symm_singularCup_sphereGenerator (Y : TopCat.{0}) {d n N : ℕ}
    (h : d + 1 + n = N)
    (c : Y.singularCohomology (𝟙_ (ModuleCat.{0} ℤ)) ℤ (𝟙_ (ModuleCat.{0} ℤ)) n) :
    ((sphere.{0} (d + 1) ⊗ Y).integralCohomologyEquiv N).symm
      ((sphere.{0} (d + 1) ⊗ Y).singularCup ℤ (λ_ _).inv (λ_ _).hom (d + 1) n N h
        (TopCat.singularCohomologyMap (fst _ Y) (d + 1)
          (singularCohomologyTopCatSphereGenerator ℤ d))
        (TopCat.singularCohomologyMap (snd _ Y) n c)) =
      (sphere.{0} (d + 1) ⊗ Y).integralCup (d + 1) n N h
        (@TopCat.singularCohomologyMap _ _ _ _ (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ _
          Linear.preadditiveIntLinear (ModuleCat.of ℤ ℤ) _ _ (fst _ Y) (d + 1)
          (integralSphereGenerator d))
        (@TopCat.singularCohomologyMap _ _ _ _ (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ _
          Linear.preadditiveIntLinear (ModuleCat.of ℤ ℤ) _ _ (snd _ Y) n
          ((Y.integralCohomologyEquiv n).symm c)) := by
  rw [integralCohomologyEquiv_symm_singularCup, integralCohomologyEquiv_symm_naturality,
    integralCohomologyEquiv_symm_naturality, integralSphereGenerator_def]

end IntegerCoefficients

/-- Every class of `Hᵈ⁺¹(Sᵈ⁺¹; ℤ)` is an integer multiple of the generator `θ`, the integral
class dual to the standard generator of `H_{d+1}(Sᵈ⁺¹)`. -/
theorem exists_eq_zsmul_sphereGenerator {d : ℕ}
    (x : (sphere.{0} (d + 1)).integralCohomology (d + 1)) :
    ∃ r : ℤ, x = r • integralSphereGenerator d := by
  set e := (sphere.{0} (d + 1)).integralCohomologyEquiv (d + 1)
  set s := singularCohomologyTopCatSphereEquiv ℤ (𝟙_ (ModuleCat.{0} ℤ)) d
  refine ⟨s (e x), e.injective (s.injective ?_)⟩
  rw [map_zsmul, map_zsmul, integralCohomologyEquiv_integralSphereGenerator,
    singularCohomologyTopCatSphereEquiv_singularCohomologyTopCatSphereGenerator, smul_eq_mul,
    mul_one]

/-- **Products with the sphere generator keep infinite order.** Let `θ ∈ Hᵈ⁺¹(Sᵈ⁺¹; ℤ)` be the
integral class dual to the standard generator of `H_{d+1}(Sᵈ⁺¹)`. If `c ∈ Hⁿ(Y; ℤ)` has infinite
order, then so has `pr₁^* θ ⌣ pr₂^* c ∈ H^N(Sᵈ⁺¹ × Y; ℤ)`, `N = d + 1 + n`. -/
theorem not_isOfFinAddOrder_integralCup_sphereGenerator (Y : TopCat.{0}) {d n N : ℕ}
    (h : d + 1 + n = N) {c : Y.integralCohomology n} (hc : ¬IsOfFinAddOrder c) :
    ¬IsOfFinAddOrder ((sphere.{0} (d + 1) ⊗ Y).integralCup (d + 1) n N h
      (TopCat.singularCohomologyMap (fst _ Y) (d + 1) (integralSphereGenerator d))
      (TopCat.singularCohomologyMap (snd _ Y) n c)) := by
  obtain rfl : N = n + (d + 1) := by omega
  -- the class is the image of `(0, c)` under the decomposition of the cohomology of `Sᵈ⁺¹ × Y`
  set e₁ := (sphere.{0} (d + 1) ⊗ Y).integralCohomologyEquiv (n + (d + 1))
  set S := singularCohomologySphereProdSlantEquiv (𝟙_ (ModuleCat.{0} ℤ)) Y (sphereBasePoint d) n
  have hFc : (sphere.{0} (d + 1) ⊗ Y).integralCup (d + 1) n (n + (d + 1)) h
      (TopCat.singularCohomologyMap (fst _ Y) (d + 1) (integralSphereGenerator d))
      (TopCat.singularCohomologyMap (snd _ Y) n c) =
        e₁.symm (S.symm (0, Y.integralCohomologyEquiv n c)) := by
    rw [singularCohomologySphereProdSlantEquiv_symm_apply, map_zero, zero_add,
      integralCohomologyEquiv_symm_singularCup_sphereGenerator, LinearEquiv.symm_apply_apply]
  rw [hFc]
  refine fun hfin ↦ hc ?_
  rw [isOfFinAddOrder_iff_nsmul_eq_zero] at hfin ⊢
  obtain ⟨k, hk, hkc⟩ := hfin
  refine ⟨k, hk, (Y.integralCohomologyEquiv n).injective ?_⟩
  have := congrArg (fun x ↦ (S (e₁ x)).2) hkc
  simpa using this

section SphereProdSphere

variable (k : Type w) [CommRing k]

/-- **The top cohomology of a product of two spheres.** Over a commutative ring `k`, every class
of `Hᵃ⁺ᵇ(Sᵃ × Sᵇ; k)`, `a = d + 1`, `b = e + 1`, is a multiple of `pr₁^* θ_a ⌣ pr₂^* θ_b`, where
`θ_a`, `θ_b` are the generators of the top cohomology of the two spheres dual to their standard
homology generators. -/
theorem exists_eq_smul_singularCup_sphereGenerator {d e N : ℕ} (h : d + 1 + (e + 1) = N)
    (x : (sphere.{w} (d + 1) ⊗ sphere.{w} (e + 1)).singularCohomology (𝟙_ (ModuleCat.{w} k)) k
      (𝟙_ (ModuleCat.{w} k)) N) :
    ∃ r : k, x = r • (sphere.{w} (d + 1) ⊗ sphere.{w} (e + 1)).singularCup k (λ_ _).inv
      (λ_ _).hom (d + 1) (e + 1) N h
      (TopCat.singularCohomologyMap (fst _ _) (d + 1) (singularCohomologyTopCatSphereGenerator k d))
      (TopCat.singularCohomologyMap (snd _ _) (e + 1)
        (singularCohomologyTopCatSphereGenerator k e)) := by
  obtain rfl : N = e + 1 + (d + 1) := by omega
  set S := singularCohomologySphereProdSlantEquiv (𝟙_ (ModuleCat.{w} k)) (sphere.{w} (e + 1))
    (sphereBasePoint d) (e + 1)
  -- the first component lies in `Hᵃ⁺ᵇ(Sᵇ; k)`, which vanishes
  have hz : IsZero ((sphere.{w} (e + 1)).singularCohomology (𝟙_ (ModuleCat.{w} k)) k
      (𝟙_ (ModuleCat.{w} k)) (e + 1 + d + 1)) :=
    isZero_singularCohomology_topCatSphere_of_ne k _ (e + 1) (e + 1 + d) (by omega)
  have h₁ : (S x).1 = 0 := (ModuleCat.subsingleton_of_isZero hz).elim _ _
  set s := singularCohomologyTopCatSphereEquiv k (𝟙_ (ModuleCat.{w} k)) e
  refine ⟨s (S x).2, ?_⟩
  have h₂ : (S x).2 = s (S x).2 • singularCohomologyTopCatSphereGenerator k e :=
    (s.symm_apply_apply _).symm.trans (singularCohomologyTopCatSphereEquiv_symm_eq_smul k e _)
  conv_lhs => rw [← S.symm_apply_apply x, ← Prod.mk.eta (p := S x), h₁, h₂]
  rw [singularCohomologySphereProdSlantEquiv_symm_apply, map_zero, zero_add, map_smul,
    map_smul]

/-- The class `pr₁^* θ_a ⌣ pr₂^* θ_b` of `Sᵃ × Sᵇ`, `a = d + 1`, `b = e + 1`, takes the value
`1` on the cross product `γ_a × γ_b` of the standard homology generators, read with coefficients
`k` through the unitor `k ⊗ k ≅ k`. -/
@[simp]
theorem singularKronecker_singularCup_sphereGenerator_singularHomologyCross {d e N : ℕ}
    (h : d + 1 + (e + 1) = N) :
    (sphere.{w} (d + 1) ⊗ sphere.{w} (e + 1)).singularKronecker k N
      ((sphere.{w} (d + 1) ⊗ sphere.{w} (e + 1)).singularCup k (λ_ _).inv (λ_ _).hom
        (d + 1) (e + 1) N h
        (TopCat.singularCohomologyMap (fst _ _) (d + 1)
          (singularCohomologyTopCatSphereGenerator k d))
        (TopCat.singularCohomologyMap (snd _ _) (e + 1)
          (singularCohomologyTopCatSphereGenerator k e)))
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} k) N).map
          (λ_ (𝟙_ (ModuleCat.{w} k))).hom).app (sphere.{w} (d + 1) ⊗ sphere.{w} (e + 1))
        (singularHomologyCross _ _ (𝟙_ (ModuleCat.{w} k)) (𝟙_ (ModuleCat.{w} k))
          (d + 1) (e + 1) N h
          (singularHomologyTopCatSphereGenerator k d ⊗ₜ singularHomologyTopCatSphereGenerator k e)))
      = 1 := by
  rw [singularKronecker_singularCup_fst_snd_singularHomologyCross,
    singularKronecker_singularCohomologyTopCatSphereGenerator,
    singularKronecker_singularCohomologyTopCatSphereGenerator, mul_one]

/-- A class `x` of `Hᵃ⁺ᵇ(Sᵃ × Sᵇ; k)`, `a = d + 1`, `b = e + 1`, is determined by its value on
the cross product `γ_a × γ_b` of the standard homology generators:
`x = ⟨x, γ_a × γ_b⟩ • (pr₁^* θ_a ⌣ pr₂^* θ_b)`. -/
theorem eq_singularKronecker_smul_singularCup_sphereGenerator {d e N : ℕ}
    (h : d + 1 + (e + 1) = N)
    (x : (sphere.{w} (d + 1) ⊗ sphere.{w} (e + 1)).singularCohomology (𝟙_ (ModuleCat.{w} k)) k
      (𝟙_ (ModuleCat.{w} k)) N) :
    x = (sphere.{w} (d + 1) ⊗ sphere.{w} (e + 1)).singularKronecker k N x
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} k) N).map
          (λ_ (𝟙_ (ModuleCat.{w} k))).hom).app (sphere.{w} (d + 1) ⊗ sphere.{w} (e + 1))
        (singularHomologyCross _ _ (𝟙_ (ModuleCat.{w} k)) (𝟙_ (ModuleCat.{w} k))
          (d + 1) (e + 1) N h
          (singularHomologyTopCatSphereGenerator k d ⊗ₜ singularHomologyTopCatSphereGenerator k e)))
      • (sphere.{w} (d + 1) ⊗ sphere.{w} (e + 1)).singularCup k (λ_ _).inv (λ_ _).hom
        (d + 1) (e + 1) N h
        (TopCat.singularCohomologyMap (fst _ _) (d + 1)
          (singularCohomologyTopCatSphereGenerator k d))
        (TopCat.singularCohomologyMap (snd _ _) (e + 1)
          (singularCohomologyTopCatSphereGenerator k e)) := by
  obtain ⟨r, rfl⟩ := exists_eq_smul_singularCup_sphereGenerator k h x
  simp

/-- **Pull-backs to a product of two spheres.** For a map `f : Sᵃ × Sᵇ ⟶ Z`, `a = d + 1`,
`b = e + 1`, every class `u` of `Hᵃ⁺ᵇ(Z; k)` pulls back to
`f^* u = ⟨u, f_*(γ_a × γ_b)⟩ • (pr₁^* θ_a ⌣ pr₂^* θ_b)`, with `γ_a × γ_b` the cross product of
the standard homology generators and `θ_a`, `θ_b` the dual generators of the top cohomology of
the two spheres. -/
theorem singularCohomologyMap_eq_singularKronecker_smul_singularCup_sphereGenerator
    {d e N : ℕ} (h : d + 1 + (e + 1) = N) {Z : TopCat.{w}}
    (f : sphere.{w} (d + 1) ⊗ sphere.{w} (e + 1) ⟶ Z)
    (u : Z.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) N) :
    TopCat.singularCohomologyMap f N u = Z.singularKronecker k N u
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} k) N).obj
          (𝟙_ (ModuleCat.{w} k))).map f
        (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} k) N).map
            (λ_ (𝟙_ (ModuleCat.{w} k))).hom).app (sphere.{w} (d + 1) ⊗ sphere.{w} (e + 1))
          (singularHomologyCross _ _ (𝟙_ (ModuleCat.{w} k)) (𝟙_ (ModuleCat.{w} k))
            (d + 1) (e + 1) N h
            (singularHomologyTopCatSphereGenerator k d ⊗ₜ
              singularHomologyTopCatSphereGenerator k e))))
      • (sphere.{w} (d + 1) ⊗ sphere.{w} (e + 1)).singularCup k (λ_ _).inv (λ_ _).hom
        (d + 1) (e + 1) N h
        (TopCat.singularCohomologyMap (fst _ _) (d + 1)
          (singularCohomologyTopCatSphereGenerator k d))
        (TopCat.singularCohomologyMap (snd _ _) (e + 1)
          (singularCohomologyTopCatSphereGenerator k e)) := by
  rw [eq_singularKronecker_smul_singularCup_sphereGenerator k h
    (TopCat.singularCohomologyMap f N u), singularKronecker_naturality, ConcreteCategory.comp_apply]

end SphereProdSphere

/-- **Integral classes of a product of two spheres.** A class `x` of the integral cohomology
`Hᵃ⁺ᵇ(Sᵃ × Sᵇ; ℤ)`, `a = d + 1`, `b = e + 1`, is
`x = ⟨x, γ_a × γ_b⟩ • (pr₁^* θ_a ⌣ pr₂^* θ_b)`, an integer multiple of the integral cup product
of the integral generators `TopCat.integralSphereGenerator`. The integer `⟨x, γ_a × γ_b⟩` is the
value of `x`, read with coefficients `ℤ` through `TopCat.integralCohomologyEquiv`, on the cross
product of the standard homology generators, the integral Kronecker pairing
`TopCat.integralKronecker`. -/
theorem eq_integralKronecker_zsmul_integralCup_sphereGenerator {d e N : ℕ}
    (h : d + 1 + (e + 1) = N)
    (x : (sphere.{0} (d + 1) ⊗ sphere.{0} (e + 1)).integralCohomology N) :
    x = (sphere.{0} (d + 1) ⊗ sphere.{0} (e + 1)).integralKronecker N x
        (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) N).map
            (λ_ (𝟙_ (ModuleCat.{0} ℤ))).hom).app (sphere.{0} (d + 1) ⊗ sphere.{0} (e + 1))
          (singularHomologyCross _ _ (𝟙_ (ModuleCat.{0} ℤ)) (𝟙_ (ModuleCat.{0} ℤ))
            (d + 1) (e + 1) N h
            (singularHomologyTopCatSphereGenerator ℤ d ⊗ₜ
              singularHomologyTopCatSphereGenerator ℤ e))) •
      (sphere.{0} (d + 1) ⊗ sphere.{0} (e + 1)).integralCup (d + 1) (e + 1) N h
        (TopCat.singularCohomologyMap (fst _ _) (d + 1) (integralSphereGenerator d))
        (TopCat.singularCohomologyMap (snd _ _) (e + 1) (integralSphereGenerator e)) := by
  obtain ⟨v, rfl⟩ :=
    ((sphere.{0} (d + 1) ⊗ sphere.{0} (e + 1)).integralCohomologyEquiv N).symm.surjective x
  rw [integralKronecker_integralCohomologyEquiv_symm]
  conv_lhs => rw [eq_singularKronecker_smul_singularCup_sphereGenerator ℤ h v]
  -- the module action over `ℤ` of `eq_singularKronecker_smul_singularCup_sphereGenerator` is
  -- the action of `ℤ` on an additive group by `Int.cast_smul_eq_zsmul`
  rw [← Int.cast_smul_eq_zsmul ℤ, Int.cast_id, LinearEquiv.map_smul,
    integralCohomologyEquiv_symm_singularCup_sphereGenerator, ← integralSphereGenerator_def]

/-- **The top integral cohomology of a product of two spheres.** Every class of the integral
cohomology `Hᵃ⁺ᵇ(Sᵃ × Sᵇ; ℤ)`, `a = d + 1`, `b = e + 1`, is an integer multiple of the integral
cup product `pr₁^* θ_a ⌣ pr₂^* θ_b`, where `θ_a`, `θ_b` are the integral generators
`TopCat.integralSphereGenerator` of the top cohomology of the two spheres. -/
theorem exists_eq_zsmul_integralCup_sphereGenerator {d e N : ℕ} (h : d + 1 + (e + 1) = N)
    (x : (sphere.{0} (d + 1) ⊗ sphere.{0} (e + 1)).integralCohomology N) :
    ∃ r : ℤ, x = r • (sphere.{0} (d + 1) ⊗ sphere.{0} (e + 1)).integralCup (d + 1) (e + 1) N h
      (TopCat.singularCohomologyMap (fst _ _) (d + 1) (integralSphereGenerator d))
      (TopCat.singularCohomologyMap (snd _ _) (e + 1) (integralSphereGenerator e)) :=
  ⟨_, eq_integralKronecker_zsmul_integralCup_sphereGenerator h x⟩

/-- The integral cup product `pr₁^* θ_a ⌣ pr₂^* θ_b` of `Sᵃ × Sᵇ`, `a = d + 1`, `b = e + 1`, of
the integral generators `TopCat.integralSphereGenerator`, takes the value `1` under the integral
Kronecker pairing `TopCat.integralKronecker` on the cross product `γ_a × γ_b` of the standard
homology generators. -/
@[simp]
theorem integralKronecker_integralCup_sphereGenerator {d e N : ℕ} (h : d + 1 + (e + 1) = N) :
    (sphere.{0} (d + 1) ⊗ sphere.{0} (e + 1)).integralKronecker N
        ((sphere.{0} (d + 1) ⊗ sphere.{0} (e + 1)).integralCup (d + 1) (e + 1) N h
          (TopCat.singularCohomologyMap (fst _ _) (d + 1) (integralSphereGenerator d))
          (TopCat.singularCohomologyMap (snd _ _) (e + 1) (integralSphereGenerator e)))
        (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) N).map
            (λ_ (𝟙_ (ModuleCat.{0} ℤ))).hom).app (sphere.{0} (d + 1) ⊗ sphere.{0} (e + 1))
          (singularHomologyCross _ _ (𝟙_ (ModuleCat.{0} ℤ)) (𝟙_ (ModuleCat.{0} ℤ))
            (d + 1) (e + 1) N h
            (singularHomologyTopCatSphereGenerator ℤ d ⊗ₜ
              singularHomologyTopCatSphereGenerator ℤ e))) = 1 := by
  rw [integralSphereGenerator_def e, ← integralCohomologyEquiv_symm_singularCup_sphereGenerator,
    integralKronecker_integralCohomologyEquiv_symm]
  exact singularKronecker_singularCup_sphereGenerator_singularHomologyCross ℤ h

/-- **Integral pull-backs to a product of two spheres.** For a map `f : Sᵃ × Sᵇ ⟶ Z`,
`a = d + 1`, `b = e + 1`, every class `u` of the integral cohomology `Hᵃ⁺ᵇ(Z; ℤ)` pulls back to
`f^* u = ⟨u, f_*(γ_a × γ_b)⟩ • (pr₁^* θ_a ⌣ pr₂^* θ_b)`, an integer multiple of the integral cup
product of the integral generators `TopCat.integralSphereGenerator`. The integer
`⟨u, f_*(γ_a × γ_b)⟩` is the integral Kronecker pairing `TopCat.integralKronecker` of `u` with the
image under `f` of the cross product of the standard homology generators. -/
theorem singularCohomologyMap_eq_integralKronecker_zsmul_integralCup_sphereGenerator
    {d e N : ℕ} (h : d + 1 + (e + 1) = N) {Z : TopCat.{0}}
    (f : sphere.{0} (d + 1) ⊗ sphere.{0} (e + 1) ⟶ Z) (u : Z.integralCohomology N) :
    TopCat.singularCohomologyMap f N u =
      Z.integralKronecker N u
          (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) N).obj
              (𝟙_ (ModuleCat.{0} ℤ))).map f
            (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) N).map
                (λ_ (𝟙_ (ModuleCat.{0} ℤ))).hom).app (sphere.{0} (d + 1) ⊗ sphere.{0} (e + 1))
              (singularHomologyCross _ _ (𝟙_ (ModuleCat.{0} ℤ)) (𝟙_ (ModuleCat.{0} ℤ))
                (d + 1) (e + 1) N h
                (singularHomologyTopCatSphereGenerator ℤ d ⊗ₜ
                  singularHomologyTopCatSphereGenerator ℤ e)))) •
        (sphere.{0} (d + 1) ⊗ sphere.{0} (e + 1)).integralCup (d + 1) (e + 1) N h
          (TopCat.singularCohomologyMap (fst _ _) (d + 1) (integralSphereGenerator d))
          (TopCat.singularCohomologyMap (snd _ _) (e + 1) (integralSphereGenerator e)) := by
  rw [eq_integralKronecker_zsmul_integralCup_sphereGenerator h (TopCat.singularCohomologyMap f N u),
    integralKronecker_naturality]

end TopCat

end
