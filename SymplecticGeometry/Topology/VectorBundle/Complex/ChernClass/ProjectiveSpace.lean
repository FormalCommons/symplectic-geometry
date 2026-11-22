/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Cohomology.ComplSingleton
public import SymplecticGeometry.AlgebraicTopology.Cohomology.EvenIntegralCohomology
public import SymplecticGeometry.AlgebraicTopology.Cohomology.IntegralCohomologyULift
public import SymplecticGeometry.Topology.VectorBundle.ProjectiveBundle.Tautological
public import SymplecticGeometry.Topology.VectorBundle.Thom.CupEulerClass
public import TauCeti.AlgebraicTopology.Cellular.ComplexProjective.Cohomology
public import TauCeti.Topology.ComplexProjectiveSpace.Projectivization
public import TauCeti.Topology.VectorBundle.Orientation.Complex.FiberwiseEquiv

/-!
# The hyperplane class and the cohomology ring of a complex projective space

For a complex normed space `V`, the hyperplane class `h ∈ H²(ℙ ℂ V; ℤ)` is minus the Euler class
of the tautological line `Projectivization.Tautological ℂ V`, read in integral cohomology through
`TopCat.uliftIntegralCohomologyIso`: it is the first Chern class of the dual of the tautological
line, in the normalization of Bott–Tu, §20. When `finrank ℂ V = n + 1`, the even integral
cohomology ring of `ℙ ℂ V` is `ℤ[X] ⧸ (X ^ (n + 1))`, with `X` going to `h`.

## Main definitions and results

* `Projectivization.hyperplaneClass V`: the hyperplane class, with `hyperplaneClass_def`.
* `Projectivization.hyperplaneClass_map`: the map of projective spaces induced by an injective
  linear map `f : V →ₗ[ℂ] W`, with `V` finite-dimensional, pulls the hyperplane class of `W` back
  to that of `V`. The tautological line of `V` is the pull-back of that of `W` by the fibrewise
  isomorphisms `Projectivization.tautologicalMapEquiv`, so this is the naturality of the Euler
  class, `TauCeti.complexEulerClass_eq_singularCohomologyMap_of_fiberwise`, together with that of
  `TopCat.uliftIntegralCohomologyIso`.
* `Projectivization.isZero_integralCohomology_of_lt`: `Hᵐ(ℙ ℂ V; ℤ) = 0` for `m > 2n`.
* `Projectivization.bijective_zsmul_hyperplaneClass_pow`: for `k ≤ n`, `m ↦ m • h ^ k` is a
  bijection `ℤ → H^{2k}(ℙ ℂ V; ℤ)`.
* `Projectivization.hyperplaneClass_pow_eq_zero`: `h ^ (n + 1) = 0`.
* `Projectivization.aeval_hyperplaneClass_eq_zero_iff` and
  `Projectivization.surjective_aeval_hyperplaneClass`: a polynomial `p ∈ ℤ[X]` has `p(h) = 0`
  exactly when `X ^ (n + 1)` divides it, and every even class is some `p(h)`.
* `Projectivization.evenIntegralCohomologyEquiv`: the ring isomorphism
  `ℤ[X] ⧸ (X ^ (n + 1)) ≃+* ⨁ k, H^{2k}(ℙ ℂ V; ℤ)`, with `evenIntegralCohomologyEquiv_mk` and
  `evenIntegralCohomologyEquiv_mk_X`.

The powers of `h` are taken in `TopCat.EvenIntegralCohomology`, with `h` in the summand of index
`1`, and `h ^ k` read in the summand of index `k`, of degree `2k`.

## Proof

The argument is that of Milnor–Stasheff, §14, with the Gysin step in the form of
`TauCeti.bijective_integralCup_complexEulerClass`. The complement of the zero section of the
tautological line is the space of nonzero vectors of `V`
(`Projectivization.tautologicalComplZeroHomeomorph`), whose integral cohomology vanishes in the
degrees `1, …, 2n` (`TauCeti.isZero_singularCohomology_complSingleton_subtype_of_ne`). So cup
product with the Euler class `e`, and so with `h = -e`, is a bijection
`H^{2k}(ℙ ℂ V; ℤ) → H^{2k+2}(ℙ ℂ V; ℤ)` for `k < n`, and induction from `H⁰(ℙ ℂ V; ℤ) = ℤ`
(`TopCat.bijective_zsmul_integralCohomologyOne`) gives the classes `h ^ k`. Above degree `2n`
the cohomology vanishes by Tau Ceti's `ComplexProjectiveSpace.isZero_singularCohomology_of_lt`,
carried along `ComplexProjectiveSpace.homeomorphProjectivization` and a linear equivalence
`(Fin (n + 1) → ℂ) ≃ V`.

## Implementation notes

The Euler class is that of a line, `r = 0`, of degree `2 * 0 + 2`, which is `2` by computation;
as in `SymplecticGeometry.Bundle.firstChernClass`, `r := 0` is given explicitly.

## References

* [R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §20 (the
  tautological line of a projective space and the class `x = -e(S)`).
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press (1974), §14 (the cohomology of complex projective space).
-/

public section

noncomputable section

open Bundle Module TauCeti
open scoped LinearAlgebra.Projectivization

namespace Projectivization

variable (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- The **hyperplane class** `h ∈ H²(ℙ ℂ V; ℤ)` of a complex projective space: minus the Euler
class of the tautological line, in integral cohomology. -/
def hyperplaneClass : (TopCat.of (ℙ ℂ V)).integralCohomology 2 :=
  -((TopCat.of (ℙ ℂ V)).uliftIntegralCohomologyIso 2).hom
    (complexEulerClass (r := 0) ℂ (Tautological ℂ V) (finrank_self ℂ))

theorem hyperplaneClass_def :
    hyperplaneClass V = -((TopCat.of (ℙ ℂ V)).uliftIntegralCohomologyIso 2).hom
      (complexEulerClass (r := 0) ℂ (Tautological ℂ V) (finrank_self ℂ)) :=
  (rfl)

variable {V} {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ V]

/-- **Naturality of the hyperplane class.** The continuous map `ℙ ℂ V → ℙ ℂ W` induced by an
injective linear map `f : V →ₗ[ℂ] W` pulls the hyperplane class of `W` back to that of `V`. -/
theorem hyperplaneClass_map (f : V →ₗ[ℂ] W) (hf : Function.Injective f) :
    TopCat.singularCohomologyMap
        (TopCat.ofHom ⟨map f hf, continuous_map hf (LinearMap.continuous_of_finiteDimensional f)⟩)
        2 (hyperplaneClass W) = hyperplaneClass V := by
  have hfc := LinearMap.continuous_of_finiteDimensional f
  have h := complexEulerClass_eq_singularCohomologyMap_of_fiberwise (r := 0) (finrank_self ℂ)
    (finrank_self ℂ) (g := ⟨map f hf, continuous_map hf hfc⟩)
    (continuous_tautologicalMapEquiv f hf hfc)
  rw [hyperplaneClass_def, hyperplaneClass_def, map_neg, h]
  exact congrArg _ (CategoryTheory.ConcreteCategory.congr_hom
    (TopCat.uliftIntegralCohomologyIso_naturality _ 2) _).symm

/-! ### The cohomology ring -/

section Ring

open CategoryTheory Limits Polynomial

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {n : ℕ}

/-- The integral cohomology of `ℙ ℂ V`, for `finrank ℂ V = n + 1`, vanishes above degree `2n`. -/
theorem isZero_integralCohomology_of_lt (hV : finrank ℂ V = n + 1) {m : ℕ} (hm : 2 * n < m) :
    IsZero ((TopCat.of (ℙ ℂ V)).integralCohomology m) := by
  have : FiniteDimensional ℂ V := Module.finite_of_finrank_eq_succ hV
  let e : ComplexProjectiveSpace n ≃ₜ ℙ ℂ V :=
    (ComplexProjectiveSpace.homeomorphProjectivization n).trans
      (ContinuousLinearEquiv.ofFinrankEq (E := Fin (n + 1) → ℂ) (F := V)
        (by rw [finrank_fin_fun, hV])).mapProjectivization
  exact (ComplexProjectiveSpace.isZero_singularCohomology_of_lt _ _ hm).of_iso
    ((singularCohomologyFunctor _ ℤ _ m).mapIso (TopCat.isoOfHomeo e).op)

/-- The integral cohomology of the nonzero vectors of the tautological line of `ℙ ℂ V`, for
`finrank ℂ V = n + 1`, vanishes in the degrees `m ≠ 0` with `m + 1 ≠ 2n + 2`. -/
private lemma isZero_integralCohomology_zeroSectionCompl (hV : finrank ℂ V = n + 1) {m : ℕ}
    (hm : m ≠ 0) (hmn : m + 1 ≠ 2 * n + 2) :
    IsZero ((TopCat.of (zeroSectionCompl ℂ (Tautological ℂ V))).integralCohomology m) := by
  have : FiniteDimensional ℂ V := Module.finite_of_finrank_eq_succ hV
  have : FiniteDimensional ℝ V := .complexToReal V
  let e : zeroSectionCompl ℂ (Tautological ℂ V) ≃ₜ ({0}ᶜ : Set V) :=
    (Homeomorph.subtype (.refl _) fun _ ↦ mem_zeroSectionCompl).trans
      (tautologicalComplZeroHomeomorph ℂ V)
  exact (isZero_singularCohomology_complSingleton_subtype_of_ne _ _ (0 : V)
    (by rw [finrank_real_of_complex, hV]; ring) hm hmn).of_iso
    ((singularCohomologyFunctor _ ℤ _ m).mapIso (TopCat.isoOfHomeo e.symm).op)

/-- **The integral cohomology of `ℙ ℂ V` in degree `2k ≤ 2n`** is free on the `k`-th power of
the hyperplane class, for `finrank ℂ V = n + 1`: `m ↦ m • h ^ k` is a bijection from `ℤ` onto
`H^{2k}(ℙ ℂ V; ℤ)`, the power taken in the even integral cohomology ring and read in degree
`2k`. -/
theorem bijective_zsmul_hyperplaneClass_pow (hV : finrank ℂ V = n + 1) {k : ℕ} (hk : k ≤ n) :
    Function.Bijective fun m : ℤ ↦
      m • ((TopCat.of (ℙ ℂ V)).evenIntegralCohomologyOf 1 (hyperplaneClass V) ^ k) k := by
  have : FiniteDimensional ℂ V := Module.finite_of_finrank_eq_succ hV
  have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hV
  induction k with
  | zero =>
    simp only [pow_zero, ← TopCat.evenIntegralCohomologyOf_one, DirectSum.of_eq_same]
    exact TopCat.bijective_zsmul_integralCohomologyOne _
  | succ k ih =>
    -- Cup product with `h = -e` is bijective by the Gysin step for the tautological line.
    have hcup : Function.Bijective fun a : (TopCat.of (ℙ ℂ V)).integralCohomology (2 * k) ↦
        (TopCat.of (ℙ ℂ V)).integralCup (2 * k) (2 * 1) (2 * (k + 1)) (by ring) a
          (hyperplaneClass V) := by
      have he := bijective_integralCup_complexEulerClass (r := 0) (E := Tautological ℂ V)
        (finrank_self ℂ) (p := 2 * k) (l := 2 * k + 1) (m := 2 * (k + 1)) (by ring) (by ring)
        (isZero_integralCohomology_zeroSectionCompl hV (by omega) (by omega))
        (isZero_integralCohomology_zeroSectionCompl hV (by omega) (by omega))
      simp only [hyperplaneClass_def, map_neg]
      exact (Equiv.neg _).bijective.comp he
    simp only [TopCat.evenIntegralCohomologyOf_pow_succ_apply]
    convert hcup.comp (ih (by omega)) using 1
    funext m
    -- `a ↦ a ⌣ h` as an additive map, since the bilinear map has no `flip` over `ℤ` here.
    exact (map_zsmul (AddMonoidHom.mk' (fun a ↦ (TopCat.of (ℙ ℂ V)).integralCup (2 * k) (2 * 1)
      (2 * (k + 1)) (by ring) a (hyperplaneClass V)) fun a b ↦ by
        rw [map_add, LinearMap.add_apply]) m _).symm

/-- **The hyperplane class of `ℙ ℂ V` is nilpotent**: `h ^ (n + 1) = 0` in the even integral
cohomology ring, for `finrank ℂ V = n + 1`. -/
theorem hyperplaneClass_pow_eq_zero (hV : finrank ℂ V = n + 1) :
    (TopCat.of (ℙ ℂ V)).evenIntegralCohomologyOf 1 (hyperplaneClass V) ^ (n + 1) = 0 := by
  have := ModuleCat.subsingleton_of_isZero (isZero_integralCohomology_of_lt hV (m := 2 * (n + 1))
    (by omega))
  rw [TopCat.evenIntegralCohomologyOf_pow_eq_of, Subsingleton.elim
    (((TopCat.of (ℙ ℂ V)).evenIntegralCohomologyOf 1 (hyperplaneClass V) ^ (n + 1)) (n + 1)) 0,
    map_zero]

/-- A polynomial with integer coefficients vanishes at the hyperplane class exactly when it is a
multiple of `X ^ (n + 1)`. -/
theorem aeval_hyperplaneClass_eq_zero_iff (hV : finrank ℂ V = n + 1) (p : ℤ[X]) :
    aeval ((TopCat.of (ℙ ℂ V)).evenIntegralCohomologyOf 1 (hyperplaneClass V)) p = 0 ↔
      X ^ (n + 1) ∣ p := by
  set x := (TopCat.of (ℙ ℂ V)).evenIntegralCohomologyOf 1 (hyperplaneClass V)
  refine ⟨fun hp ↦ ?_, fun ⟨q, hq⟩ ↦ by rw [hq, map_mul, map_pow, aeval_X,
    hyperplaneClass_pow_eq_zero hV, zero_mul]⟩
  set r := p %ₘ X ^ (n + 1)
  have hr : aeval x r = 0 := by
    rw [← modByMonic_add_div p (X ^ (n + 1)), map_add, map_mul, map_pow, aeval_X,
      hyperplaneClass_pow_eq_zero hV, zero_mul, add_zero] at hp
    exact hp
  rw [← modByMonic_eq_zero_iff_dvd (monic_X_pow (n + 1))]
  ext i
  rw [coeff_zero]
  rcases le_or_gt i n with hi | hi
  · -- The component of degree `2i` of `r(h)` is `rᵢ • h ^ i`.
    have hri := congrArg (fun y : (TopCat.of (ℙ ℂ V)).EvenIntegralCohomology ↦ y i) hr
    rw [aeval_def, algebraMap_int_eq, eval₂_eq_sum_range] at hri
    simp only [eq_intCast, ← zsmul_eq_mul, DirectSum.sum_apply, DirectSum.zero_apply] at hri
    rw [Finset.sum_eq_single i] at hri
    · rw [DFinsupp.zsmul_apply] at hri
      exact (bijective_zsmul_hyperplaneClass_pow hV hi).1 (hri.trans (zero_smul ℤ _).symm)
    · intro j _ hj
      rw [DFinsupp.zsmul_apply, TopCat.evenIntegralCohomologyOf_pow_apply_of_ne _ _ (Ne.symm hj),
        zsmul_zero]
    · intro h
      rw [coeff_eq_zero_of_natDegree_lt (by simpa using h), zero_smul, DirectSum.zero_apply]
  · exact coeff_eq_zero_of_degree_lt ((degree_modByMonic_lt p (monic_X_pow (n + 1))).trans_le
      (by rw [degree_X_pow]; exact_mod_cast hi))

/-- Every class in the even integral cohomology ring of `ℙ ℂ V` is a polynomial in the hyperplane
class, for `finrank ℂ V = n + 1`. -/
theorem surjective_aeval_hyperplaneClass (hV : finrank ℂ V = n + 1) :
    Function.Surjective
      (aeval (R := ℤ) ((TopCat.of (ℙ ℂ V)).evenIntegralCohomologyOf 1 (hyperplaneClass V))) := by
  intro y
  induction y using DirectSum.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | of k a =>
    rcases le_or_gt k n with hk | hk
    · obtain ⟨m, rfl⟩ := (bijective_zsmul_hyperplaneClass_pow hV hk).2 a
      refine ⟨m • X ^ k, ?_⟩
      rw [map_zsmul, map_pow, aeval_X]
      conv_lhs => rw [TopCat.evenIntegralCohomologyOf_pow_eq_of]
      exact (map_zsmul _ _ _).symm
    · have := ModuleCat.subsingleton_of_isZero (isZero_integralCohomology_of_lt hV (m := 2 * k)
        (by omega))
      exact ⟨0, by rw [map_zero, Subsingleton.elim a 0, map_zero]⟩
  | add y z hy hz =>
    obtain ⟨p, rfl⟩ := hy
    obtain ⟨q, rfl⟩ := hz
    exact ⟨p + q, map_add _ p q⟩

/-- Evaluation at the hyperplane class, on `ℤ[X] ⧸ (X ^ (n + 1))`, is bijective. -/
private lemma bijective_quotientLift_aeval (hV : finrank ℂ V = n + 1) :
    Function.Bijective (Ideal.Quotient.lift (Ideal.span {(X ^ (n + 1) : ℤ[X])})
      (aeval ((TopCat.of (ℙ ℂ V)).evenIntegralCohomologyOf 1 (hyperplaneClass V))).toRingHom
      fun p hp ↦ (aeval_hyperplaneClass_eq_zero_iff hV p).2 (Ideal.mem_span_singleton.1 hp)) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun a ha ↦ ?_, fun y ↦ ?_⟩
  · obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [Ideal.Quotient.lift_mk, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at ha
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton.2
      ((aeval_hyperplaneClass_eq_zero_iff hV p).1 ha))
  · obtain ⟨p, rfl⟩ := surjective_aeval_hyperplaneClass hV y
    exact ⟨Ideal.Quotient.mk _ p, Ideal.Quotient.lift_mk _ _ _⟩

/-- **The integral cohomology ring of `ℂPⁿ`.** For `finrank ℂ V = n + 1`, the even integral
cohomology ring of `ℙ ℂ V` is `ℤ[X] ⧸ (X ^ (n + 1))`, with `X` sent to the hyperplane class. -/
def evenIntegralCohomologyEquiv (hV : finrank ℂ V = n + 1) :
    ℤ[X] ⧸ Ideal.span {(X ^ (n + 1) : ℤ[X])} ≃+* (TopCat.of (ℙ ℂ V)).EvenIntegralCohomology :=
  RingEquiv.ofBijective _ (bijective_quotientLift_aeval hV)

/-- `Projectivization.evenIntegralCohomologyEquiv` sends the class of a polynomial `p` to `p`
evaluated at the hyperplane class. -/
@[simp]
theorem evenIntegralCohomologyEquiv_mk (hV : finrank ℂ V = n + 1) (p : ℤ[X]) :
    evenIntegralCohomologyEquiv hV (Ideal.Quotient.mk (Ideal.span {(X ^ (n + 1) : ℤ[X])}) p) =
      aeval ((TopCat.of (ℙ ℂ V)).evenIntegralCohomologyOf 1 (hyperplaneClass V)) p := by
  rw [evenIntegralCohomologyEquiv, RingEquiv.ofBijective_apply, Ideal.Quotient.lift_mk,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe]

/-- `Projectivization.evenIntegralCohomologyEquiv` sends `X` to the hyperplane class. -/
theorem evenIntegralCohomologyEquiv_mk_X (hV : finrank ℂ V = n + 1) :
    evenIntegralCohomologyEquiv hV (Ideal.Quotient.mk (Ideal.span {(X ^ (n + 1) : ℤ[X])}) X) =
      (TopCat.of (ℙ ℂ V)).evenIntegralCohomologyOf 1 (hyperplaneClass V) := by
  rw [evenIntegralCohomologyEquiv_mk, aeval_X]

end Ring

end Projectivization
