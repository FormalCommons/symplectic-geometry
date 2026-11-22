/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.IntegralCup
public import Mathlib.Algebra.DirectSum.Ring
public import Mathlib.Algebra.Polynomial.AlgebraMap
import all TauCeti.AlgebraicTopology.Cohomology.IntegralCup

/-!
# The ring of even-degree integral cohomology classes

For a space `X`, the integral cup product `TopCat.integralCup` of Tau Ceti is associative,
unital and graded commutative with the sign `(-1) ^ (p * q)`. In even degrees the sign is `1`, so
the direct sum `⨁ k, H^{2k}(X; ℤ)` is a commutative ring. This file builds it, as Mathlib's
`DirectSum.GCommRing` structure on the family `k ↦ H^{2k}(X; ℤ)`, indexed by half the degree.

## Main definitions

* `TopCat.EvenIntegralCohomology X`: the commutative ring `⨁ k : ℕ, H^{2k}(X; ℤ)`, whose product
  is the cup product and whose unit is the class of the constant cocycle `1`.
* `TopCat.evenIntegralCohomologyOf X k`: the inclusion of `H^{2k}(X; ℤ)`, with
  `evenIntegralCohomologyOf_mul` (and `evenIntegralCohomologyOf_mul_of_add_eq`, with a prescribed
  target degree) and `evenIntegralCohomologyOf_one`.
* `TopCat.evenIntegralCohomologyOf_pow_eq_of`, `TopCat.evenIntegralCohomologyOf_pow_apply_of_ne`
  and `TopCat.evenIntegralCohomologyOf_pow_succ_apply`: the powers of a class of degree two are
  homogeneous, `a ^ (k + 1)` being `a ^ k ⌣ a` in degree `2(k + 1)`.
* `TopCat.aeval_evenIntegralCohomologyOf_apply`: for a class `a` of degree two and `p ∈ ℤ[X]`,
  the component of degree `2i` of `p(a)` is `pᵢ • a ^ i`.
* `TopCat.evenIntegralCohomologyMap f`: the ring map induced by a continuous map `f : X ⟶ Y`,
  the pull-back in each degree, with `evenIntegralCohomologyMap_of`,
  `evenIntegralCohomologyMap_toAddMonoidHom` (as an additive map, the direct sum of the
  pull-backs), `evenIntegralCohomologyMap_apply` (its degree-`k` component),
  `evenIntegralCohomologyMap_id` and `evenIntegralCohomologyMap_comp`.

Two lemmas on Tau Ceti's `TopCat.integralCup` come first: `TopCat.integralCup_heq`, which says
that the product does not depend on the proof that the degrees add up, and
`TopCat.integralCup_zsmul_left`, which pulls an integer out of the left factor.

The ring map preserves the unit by `TopCat.singularCohomologyMap_integralCohomologyOne`, the
pull-back of the unit class, which Tau Ceti does not state; its proof reads the definition of
`TopCat.integralCohomologyOne` through `import all`.

The graded structures and the lemmas on the inclusions follow Tau Ceti's
`TauCeti.NormalizedCubicalChain.gRing` and `TauCeti.cubicalChainLof_mul`,
`TauCeti.cubicalChainLof_one`.

## References

* [R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §20
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §3.2
-/

public section

noncomputable section

open CategoryTheory DirectSum

namespace TopCat

variable (X : TopCat.{0})

/-- The integral cup product of two classes does not depend on the proof of the equality of
degrees, up to the identification of the target degrees: the two products are heterogeneously
equal. -/
theorem integralCup_heq {p q n n' : ℕ} (h : p + q = n) (h' : p + q = n')
    (a : X.integralCohomology p) (b : X.integralCohomology q) :
    X.integralCup p q n h a b ≍ X.integralCup p q n' h' a b := by
  subst h h'
  rfl

/-- The integral cup product is `ℤ`-linear in its left factor: `(m • a) ⌣ b = m • (a ⌣ b)`. -/
theorem integralCup_zsmul_left {p q n : ℕ} (h : p + q = n) (m : ℤ)
    (a : X.integralCohomology p) (b : X.integralCohomology q) :
    X.integralCup p q n h (m • a) b = m • X.integralCup p q n h a b := by
  -- `a ↦ a ⌣ b` as an additive map: the `ℤ`-action on the space of linear maps that `integralCup`
  -- lands in is not syntactically `LinearMap.module`, so `LinearMap.smul_apply` does not apply.
  exact map_zsmul (AddMonoidHom.mk' (fun a ↦ X.integralCup p q n h a b) fun a a' ↦ by
    rw [map_add, LinearMap.add_apply]) m a

namespace EvenIntegralCohomology

/-- The unit of the graded structure: the unit class in degree `0`. -/
instance gOne : GradedMonoid.GOne fun k : ℕ ↦ ↥(X.integralCohomology (2 * k)) where
  one := X.integralCohomologyOne

/-- The multiplication of the graded structure: the integral cup product. -/
instance gMul : GradedMonoid.GMul fun k : ℕ ↦ ↥(X.integralCohomology (2 * k)) where
  mul := fun {i j} a b ↦ X.integralCup (2 * i) (2 * j) (2 * (i + j)) (by ring) a b

/-- The unit of the graded structure is the unit class. -/
@[simp]
theorem gOne_one :
    (GradedMonoid.GOne.one (A := fun k : ℕ ↦ ↥(X.integralCohomology (2 * k)))) =
      X.integralCohomologyOne :=
  (rfl)

/-- The multiplication of the graded structure is the integral cup product. -/
@[simp]
theorem gMul_mul {i j : ℕ} (a : X.integralCohomology (2 * i)) (b : X.integralCohomology (2 * j)) :
    GradedMonoid.GMul.mul (A := fun k : ℕ ↦ ↥(X.integralCohomology (2 * k))) a b =
      X.integralCup (2 * i) (2 * j) (2 * (i + j)) (by ring) a b :=
  (rfl)

/-- The integral cup product makes the even-degree classes a graded commutative ring. -/
instance gCommRing : DirectSum.GCommRing fun k : ℕ ↦ ↥(X.integralCohomology (2 * k)) where
  one_mul := fun ⟨n, b⟩ ↦ Sigma.ext (Nat.zero_add n) <|
    (X.integralCup_heq (p := 0) (q := 2 * n) (n := 2 * (0 + n)) (by ring) (zero_add _) _ b).trans
      (heq_of_eq (X.integralCup_integralCohomologyOne (2 * n) b))
  mul_one := fun ⟨n, a⟩ ↦ Sigma.ext (Nat.add_zero n) <|
    (X.integralCup_heq (p := 2 * n) (q := 0) (n := 2 * (n + 0)) (by ring) (add_zero _) a _).trans
      (heq_of_eq (X.integralCup_integralCohomologyOne_right (2 * n) a))
  mul_assoc := fun ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩ ↦ Sigma.ext (Nat.add_assoc i j k) <|
    (heq_of_eq (X.integralCup_assoc (p := 2 * i) (q := 2 * j) (r := 2 * k) (m := 2 * (i + j))
      (m' := 2 * (j + k)) (n := 2 * (i + j + k)) (by ring) (by ring) (by ring) (by ring)
      a b c)).trans (X.integralCup_heq _ _ _ _)
  mul_zero := fun {_ _} a ↦ map_zero (X.integralCup _ _ _ _ a)
  zero_mul := fun {_ _} b ↦ by rw [gMul_mul, map_zero, LinearMap.zero_apply]
  mul_add := fun {_ _} a b c ↦ map_add (X.integralCup _ _ _ _ a) b c
  add_mul := fun {_ _} a b c ↦ by rw [gMul_mul, gMul_mul, gMul_mul, map_add, LinearMap.add_apply]
  natCast := fun n ↦ n • X.integralCohomologyOne
  natCast_zero := zero_nsmul _
  natCast_succ := fun n ↦ succ_nsmul _ n
  intCast := fun n ↦ n • X.integralCohomologyOne
  intCast_ofNat := fun n ↦ natCast_zsmul _ n
  intCast_negSucc_ofNat := fun n ↦ negSucc_zsmul _ n
  mul_comm := fun ⟨i, a⟩ ⟨j, b⟩ ↦ Sigma.ext (Nat.add_comm i j) <| by
    have h := X.integralCup_gradedComm (p := 2 * j) (q := 2 * i) (n := 2 * (i + j))
      (by ring) (by ring) b a
    rw [Even.neg_one_pow ⟨2 * j * i, by ring⟩, one_smul] at h
    exact (heq_of_eq h).trans (X.integralCup_heq _ _ _ _)

end EvenIntegralCohomology

/-- The **even integral cohomology ring** `⨁ k, H^{2k}(X; ℤ)` of a space `X`, indexed by half the
degree. With the integral cup product it is a commutative ring, by Mathlib's instance
`DirectSum.commRing` for the graded structure `EvenIntegralCohomology.gCommRing`. -/
abbrev EvenIntegralCohomology : Type :=
  ⨁ k : ℕ, ↥(X.integralCohomology (2 * k))

/-- The inclusion of `H^{2k}(X; ℤ)` into the even integral cohomology ring. -/
abbrev evenIntegralCohomologyOf (k : ℕ) :
    X.integralCohomology (2 * k) →+ X.EvenIntegralCohomology :=
  DirectSum.of (fun k : ℕ ↦ ↥(X.integralCohomology (2 * k))) k

/-- The product of two homogeneous classes in the even integral cohomology ring is their cup
product. -/
theorem evenIntegralCohomologyOf_mul {i j : ℕ} (a : X.integralCohomology (2 * i))
    (b : X.integralCohomology (2 * j)) :
    X.evenIntegralCohomologyOf i a * X.evenIntegralCohomologyOf j b =
      X.evenIntegralCohomologyOf (i + j)
        (X.integralCup (2 * i) (2 * j) (2 * (i + j)) (by ring) a b) := by
  simp [DirectSum.of_mul_of]

/-- The product of two homogeneous classes of degrees `2i` and `2j` in the even integral cohomology
ring is their cup product, placed in degree `2k` for any `k` with `i + j = k`. -/
theorem evenIntegralCohomologyOf_mul_of_add_eq {i j k : ℕ} (h : i + j = k)
    (a : X.integralCohomology (2 * i)) (b : X.integralCohomology (2 * j)) :
    X.evenIntegralCohomologyOf i a * X.evenIntegralCohomologyOf j b =
      X.evenIntegralCohomologyOf k (X.integralCup (2 * i) (2 * j) (2 * k) (by omega) a b) := by
  subst h
  exact X.evenIntegralCohomologyOf_mul a b

/-- The unit class in degree `0` is the unit of the even integral cohomology ring. -/
theorem evenIntegralCohomologyOf_one :
    X.evenIntegralCohomologyOf 0 X.integralCohomologyOne = 1 := by
  rw [← EvenIntegralCohomology.gOne_one, DirectSum.one_def]

/-- A power of a class `a` of degree two is homogeneous: in the even integral cohomology ring,
`a ^ k` is the image of its component of degree `2k`. -/
theorem evenIntegralCohomologyOf_pow_eq_of (a : X.integralCohomology 2) (k : ℕ) :
    X.evenIntegralCohomologyOf 1 a ^ k =
      X.evenIntegralCohomologyOf k ((X.evenIntegralCohomologyOf 1 a ^ k) k) := by
  induction k with
  | zero => rw [pow_zero, ← evenIntegralCohomologyOf_one, DirectSum.of_eq_same]
  | succ k ih => rw [pow_succ, ih, evenIntegralCohomologyOf_mul, DirectSum.of_eq_same]

/-- The power `a ^ k` of a class `a` of degree two has no component outside degree `2k`. -/
theorem evenIntegralCohomologyOf_pow_apply_of_ne (a : X.integralCohomology 2) {j k : ℕ}
    (h : j ≠ k) : (X.evenIntegralCohomologyOf 1 a ^ k) j = 0 := by
  conv_lhs => rw [evenIntegralCohomologyOf_pow_eq_of]
  exact DirectSum.of_eq_of_ne _ _ _ h

/-- For a class `a` of degree two, the component of degree `2(k + 1)` of `a ^ (k + 1)` is the cup
product of the component of degree `2k` of `a ^ k` with `a`. -/
theorem evenIntegralCohomologyOf_pow_succ_apply (a : X.integralCohomology 2) (k : ℕ) :
    (X.evenIntegralCohomologyOf 1 a ^ (k + 1)) (k + 1) =
      X.integralCup (2 * k) (2 * 1) (2 * (k + 1)) (by ring)
        ((X.evenIntegralCohomologyOf 1 a ^ k) k) a := by
  conv_lhs => rw [pow_succ, evenIntegralCohomologyOf_pow_eq_of, evenIntegralCohomologyOf_mul]
  exact DirectSum.of_eq_same _ _

/-- For a class `a` of degree two and a polynomial `p ∈ ℤ[X]`, the component of degree `2i` of
`p(a)` is the `i`-th coefficient of `p` times the component of degree `2i` of `a ^ i`. -/
theorem aeval_evenIntegralCohomologyOf_apply (a : X.integralCohomology 2) (p : Polynomial ℤ)
    (i : ℕ) : (Polynomial.aeval (X.evenIntegralCohomologyOf 1 a) p) i =
      p.coeff i • (X.evenIntegralCohomologyOf 1 a ^ i) i := by
  rw [Polynomial.aeval_def, algebraMap_int_eq, Polynomial.eval₂_eq_sum_range]
  simp only [eq_intCast, ← zsmul_eq_mul, DirectSum.sum_apply]
  rw [Finset.sum_eq_single i]
  · rw [DFinsupp.zsmul_apply]
  · intro j _ hj
    rw [DFinsupp.zsmul_apply, evenIntegralCohomologyOf_pow_apply_of_ne _ _ (Ne.symm hj),
      zsmul_zero]
  · intro h
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa using h), zero_smul,
      DirectSum.zero_apply]

variable {X} {Y Z : TopCat.{0}}

/-- Pulling back along a continuous map sends the unit class to the unit class. -/
@[simp]
theorem singularCohomologyMap_integralCohomologyOne (f : X ⟶ Y) :
    TopCat.singularCohomologyMap f 0 Y.integralCohomologyOne = X.integralCohomologyOne :=
  -- Tau Ceti states no equation for `integralCohomologyOne`, the class of a constant cocycle;
  -- its body, seen through `import all`, is the class that this lemma of Tau Ceti pulls back.
  singularCohomologyMap_homologyπ_constSingularCocycle f ℤ _

/-- The ring map `⨁ k, H^{2k}(Y; ℤ) → ⨁ k, H^{2k}(X; ℤ)` induced by a continuous map
`f : X ⟶ Y`: the pull-back along `f` in each degree. -/
def evenIntegralCohomologyMap (f : X ⟶ Y) :
    Y.EvenIntegralCohomology →+* X.EvenIntegralCohomology :=
  DirectSum.toSemiring
    (fun k ↦ (X.evenIntegralCohomologyOf k).comp
      (TopCat.singularCohomologyMap f (2 * k)).hom.toAddMonoidHom)
    (by
      rw [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, EvenIntegralCohomology.gOne_one]
      exact (congrArg _ (singularCohomologyMap_integralCohomologyOne f)).trans
        (evenIntegralCohomologyOf_one X))
    (fun {i j} a b ↦ by
      simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
        EvenIntegralCohomology.gMul_mul, evenIntegralCohomologyOf_mul]
      rw [integralCup_naturality])

/-- The ring map induced by `f` sends a homogeneous class to the image of its pull-back. -/
@[simp]
theorem evenIntegralCohomologyMap_of (f : X ⟶ Y) (k : ℕ) (a : Y.integralCohomology (2 * k)) :
    evenIntegralCohomologyMap f (Y.evenIntegralCohomologyOf k a) =
      X.evenIntegralCohomologyOf k (TopCat.singularCohomologyMap f (2 * k) a) := by
  simp only [evenIntegralCohomologyMap, DirectSum.toSemiring_of, AddMonoidHom.comp_apply,
    LinearMap.toAddMonoidHom_coe]

/-- As an additive map, the ring map induced by `f` is the direct sum of the pull-backs along `f`
in each degree. -/
theorem evenIntegralCohomologyMap_toAddMonoidHom (f : X ⟶ Y) :
    (evenIntegralCohomologyMap f).toAddMonoidHom =
      DirectSum.map fun k ↦ (TopCat.singularCohomologyMap f (2 * k)).hom.toAddMonoidHom :=
  DirectSum.addHom_ext fun k a ↦ by simp

/-- The degree-`k` component of the image of a class under the ring map induced by `f` is the
pull-back of its degree-`k` component. -/
@[simp]
theorem evenIntegralCohomologyMap_apply (f : X ⟶ Y) (x : Y.EvenIntegralCohomology) (k : ℕ) :
    evenIntegralCohomologyMap f x k = TopCat.singularCohomologyMap f (2 * k) (x k) :=
  congr($(evenIntegralCohomologyMap_toAddMonoidHom f) x k)

/-- The ring map induced by the identity is the identity. -/
@[simp]
theorem evenIntegralCohomologyMap_id :
    evenIntegralCohomologyMap (𝟙 X) = RingHom.id X.EvenIntegralCohomology :=
  DirectSum.ringHom_ext fun k a ↦ by simp

/-- The ring map induced by a composite is the composite of the ring maps, in the reverse
order. -/
theorem evenIntegralCohomologyMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    evenIntegralCohomologyMap (f ≫ g) =
      (evenIntegralCohomologyMap f).comp (evenIntegralCohomologyMap g) :=
  DirectSum.ringHom_ext fun k a ↦ by
    simp [TopCat.singularCohomologyMap_comp]

end TopCat

end
