/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.DirectSum.Algebra
public import SymplecticGeometry.Algebra.GradedMonoid
public import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Wedge.Smooth.Pow
import TauCeti.Geometry.Manifold.ContMDiffMap.Basic
import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Smooth.Assoc
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Smooth

/-!
# The graded algebra of smooth forms

The smooth real differential forms of all degrees, `⨁ k, TauCeti.SmoothForm I M ℝ k`, form an
associative unital real algebra whose product is the wedge and whose unit is the constant
function `1`. The structure is given through Mathlib's `DirectSum.GRing` and
`DirectSum.GAlgebra ℝ` on the family `fun k ↦ SmoothForm I M ℝ k`, so the ring laws of the
direct sum come from Mathlib, and `DirectSum.of _ k φ` is the form `φ` of degree `k`.
Homogeneous forms commute up to the Koszul sign `(-1) ^ (k * l)`, so forms of even degree
commute with all forms.

The construction follows Tau Ceti's graded de Rham algebra
(`TauCeti.deRhamAlgebra.gMonoid`, `TauCeti.deRhamAlgebra.gRing`,
`TauCeti.deRhamAlgebra.gAlgebra` and `TauCeti.deRhamAlgebra.of_mul_of_comm` in
`TauCeti/Geometry/Manifold/DeRham/Algebra.lean`), with smooth forms in place of their
cohomology classes. The laws come from Tau Ceti's associativity
(`TauCeti.SmoothForm.wedge_assoc_apply`) and graded commutativity
(`TauCeti.SmoothForm.wedge_eq_smul_cast_wedge_comm`) of the wedge of smooth forms.

## Main definitions

* `TauCeti.SmoothForm.gRing`: the smooth forms of all degrees are a graded ring under the wedge.
* `TauCeti.SmoothForm.gAlgebra`: they are a graded real algebra; a real number `r` acts as the
  constant function `r`.

## Main results

* `TauCeti.SmoothForm.of_mul_of_eq_of_wedge`: the product of homogeneous forms is their wedge.
* `TauCeti.SmoothForm.algebraMap_apply_eq_of_ofFunction`: the image of `r : ℝ` is the constant
  function `r`, in degree `0`.
* `TauCeti.SmoothForm.of_pow_eq_of_wedgePow`: powers of a homogeneous form are its wedge powers.
* `TauCeti.SmoothForm.of_mul_of_comm` and `TauCeti.SmoothForm.commute_of_of_of_even`: graded
  commutativity.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 14.
-/

public section

noncomputable section

open scoped ContDiff Manifold DirectSum

namespace TauCeti

namespace SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H} [IsManifold I 1 M]
  {k l : ℕ}

/-- Smooth forms of equal degrees that agree once the tangent tuples are transported along the
equality of degrees are the same element of the graded monoid of smooth forms. -/
theorem gradedMonoid_mk_eq_mk {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {i j : ℕ}
    (h : i = j) {φ : SmoothForm I M F i} {ψ : SmoothForm I M F j}
    (hφψ : ∀ x (v : Fin j → TangentSpace I x), φ.val x (v ∘ Fin.cast h) = ψ.val x v) :
    GradedMonoid.mk (A := fun q ↦ SmoothForm I M F q) i φ = GradedMonoid.mk j ψ := by
  rw [← GradedMonoid.mk_linearEquivCast (R := ℝ) h φ]
  congr 1
  ext x v
  rw [cast_apply, hφψ]

/-- The wedge with the `0`-form of a smooth function on the right multiplies by the function. -/
theorem wedge_ofFunction (φ : SmoothForm I M ℝ k) (f : C^∞⟮I, M; ℝ⟯) :
    wedge φ (ofFunction f) = funSMulₗ f φ :=
  Subtype.ext <| by
    rw [coe_wedge, coe_ofFunction, RoughForm.wedge_ofFunction, coe_funSMulₗ]

/-- The wedge with the `0`-form of a smooth function on the left multiplies by the function,
read in degree `0 + l`. -/
theorem ofFunction_wedge (f : C^∞⟮I, M; ℝ⟯) (φ : SmoothForm I M ℝ l) :
    wedge (ofFunction f) φ =
      LinearEquiv.cast (R := ℝ) (M := fun q : ℕ ↦ SmoothForm I M ℝ q) (zero_add l).symm
        (funSMulₗ f φ) := by
  ext x v
  rw [cast_apply, coe_wedge, coe_ofFunction, RoughForm.ofFunction_wedge_apply, coe_funSMulₗ]
  simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul, Function.comp_def]

/-- A real multiple `r` of the `0`-form `1` is the `0`-form of the constant function `r`. -/
theorem smul_ofFunction_one (r : ℝ) :
    r • ofFunction (I := I) (M := M) 1 =
      ofFunction (ContMDiffMap.const r) := by
  ext x v
  simp [RoughForm.ofFunction_apply, ContMDiffMap.const_apply]

/-- The graded multiplication of smooth forms is the wedge. -/
instance gMul : GradedMonoid.GMul (fun k ↦ SmoothForm I M ℝ k) where
  mul φ ψ := wedge φ ψ

/-- The graded unit of smooth forms is the constant function `1`. -/
instance gOne : GradedMonoid.GOne (fun k ↦ SmoothForm I M ℝ k) where
  one := ofFunction 1

/-- The graded multiplication of smooth forms is the wedge. -/
@[simp]
theorem gMul_mul (φ : SmoothForm I M ℝ k) (ψ : SmoothForm I M ℝ l) :
    GradedMonoid.GMul.mul (A := fun k ↦ SmoothForm I M ℝ k) φ ψ = wedge φ ψ := (rfl)

/-- The graded unit of smooth forms is the constant function `1`. -/
@[simp]
theorem gOne_one : GradedMonoid.GOne.one (A := fun k : ℕ ↦ SmoothForm I M ℝ k) =
    ofFunction 1 := (rfl)

-- A `GradedMonoid` element taken apart as a sigma pair fails the instance checks at implicit
-- transparency, so each law is restated by `change` in terms of the components of its elements.
/-- The wedge and the constant function `1` make smooth forms a graded monoid. -/
instance gMonoid : GradedMonoid.GMonoid (fun k ↦ SmoothForm I M ℝ k) where
  one_mul a := by
    change GradedMonoid.mk _ (wedge (ofFunction 1) a.2) =
      GradedMonoid.mk a.1 a.2
    rw [ofFunction_wedge, funSMulₗ_one, GradedMonoid.mk_linearEquivCast]
  mul_one a := by
    change GradedMonoid.mk _ (wedge a.2 (ofFunction 1)) =
      GradedMonoid.mk a.1 a.2
    -- The degree `a.1 + 0` of the wedge reduces to `a.1`.
    rw [wedge_ofFunction, funSMulₗ_one]
    rfl
  mul_assoc a b c := by
    change GradedMonoid.mk _ (wedge (wedge a.2 b.2) c.2) =
      GradedMonoid.mk _ (wedge a.2 (wedge b.2 c.2))
    exact gradedMonoid_mk_eq_mk (Nat.add_assoc a.1 b.1 c.1) fun x v ↦ wedge_assoc_apply _ _ _ x _

/-- The bilinearity of the wedge makes smooth forms a graded ring. The integer `n` is the
constant function `n`. -/
instance gRing : DirectSum.GRing (fun k ↦ SmoothForm I M ℝ k) where
  mul_zero _ := map_zero _
  zero_mul _ := LinearMap.map_zero₂ _ _
  mul_add _ _ _ := map_add _ _ _
  add_mul _ _ _ := LinearMap.map_add₂ _ _ _ _
  natCast n := (n : ℝ) • ofFunction 1
  natCast_zero := by simp
  natCast_succ n := by simp [add_smul]
  intCast n := (n : ℝ) • ofFunction 1
  intCast_ofNat n := by simp
  intCast_negSucc_ofNat n := by
    rw [Int.cast_negSucc, Nat.cast_succ]
    exact neg_smul ((n : ℝ) + 1) (ofFunction (1 : C^∞⟮I, M; ℝ⟯))

/-- The wedge with the `0`-form of the constant function `r` on the right is multiplication by
the scalar `r`. -/
theorem wedge_smul_ofFunction_one (φ : SmoothForm I M ℝ k) (r : ℝ) :
    wedge φ (r • ofFunction 1) = r • φ := by
  rw [map_smul, wedge_ofFunction, funSMulₗ_one]

/-- The wedge with the `0`-form of the constant function `r` on the left is multiplication by
the scalar `r`, as an element of the graded monoid of smooth forms. -/
theorem gradedMonoid_mk_smul_ofFunction_one_wedge (r : ℝ) (φ : SmoothForm I M ℝ k) :
    GradedMonoid.mk (A := fun q ↦ SmoothForm I M ℝ q) _
        (wedge (r • ofFunction 1) φ) = GradedMonoid.mk k (r • φ) := by
  rw [map_smul, LinearMap.smul_apply, ofFunction_wedge, funSMulₗ_one, ← map_smul,
    GradedMonoid.mk_linearEquivCast]

/-- Smooth forms are a graded real algebra; a real number `r` acts as the constant
function `r`. -/
instance gAlgebra : DirectSum.GAlgebra ℝ (fun k ↦ SmoothForm I M ℝ k) where
  toFun := (LinearMap.toSpanSingleton ℝ _ (ofFunction 1)).toAddMonoidHom
  map_one := by
    rw [LinearMap.toAddMonoidHom_coe, LinearMap.toSpanSingleton_apply, one_smul, gOne_one]
  map_mul r s := by
    change GradedMonoid.mk 0 ((r * s) • ofFunction 1) =
      GradedMonoid.mk 0 (wedge (r • ofFunction 1)
        (s • ofFunction 1))
    rw [wedge_smul_ofFunction_one, smul_smul, mul_comm]
  commutes r a := by
    change GradedMonoid.mk (0 + a.1) (wedge (r • ofFunction 1) a.2) =
      GradedMonoid.mk _ (wedge a.2 (r • ofFunction 1))
    -- The degree `a.1 + 0` of the right side reduces to `a.1`.
    rw [gradedMonoid_mk_smul_ofFunction_one_wedge, wedge_smul_ofFunction_one]
    rfl
  smul_def r a := by
    change GradedMonoid.mk a.1 (r • a.2) =
      GradedMonoid.mk (0 + a.1) (wedge (r • ofFunction 1) a.2)
    rw [gradedMonoid_mk_smul_ofFunction_one_wedge]

-- Instance search finds `DirectSum.ring (SmoothForm I M ℝ)`, with the family eta-reduced, and that
-- does not unify with the `fun k ↦ SmoothForm I M ℝ k` of the statements: `algebraMap ℝ` into the
-- direct sum then fails to elaborate, and ring lemmas such as `mul_sub` do not rewrite. Stating
-- the ring structure for the family as written makes both work.
/-- The ring structure of the smooth forms of all degrees. -/
instance ring : Ring (⨁ k : ℕ, SmoothForm I M ℝ k) := DirectSum.ring _

/-- The scalar map of the graded algebra of smooth forms sends `r` to the constant
function `r`. -/
@[simp]
theorem gAlgebra_toFun (r : ℝ) :
    DirectSum.GAlgebra.toFun (self := gAlgebra (I := I) (M := M)) r =
      ofFunction (ContMDiffMap.const r) :=
  smul_ofFunction_one r

/-- The product of two homogeneous smooth forms is their wedge. -/
@[simp]
theorem of_mul_of_eq_of_wedge (φ : SmoothForm I M ℝ k) (ψ : SmoothForm I M ℝ l) :
    DirectSum.of (fun k ↦ SmoothForm I M ℝ k) k φ * DirectSum.of _ l ψ =
      DirectSum.of _ (k + l) (wedge φ ψ) := by
  rw [DirectSum.of_mul_of, gMul_mul]

/-- The product of a homogeneous smooth form `φ` with the `0`-form of a smooth function `g`
on the right is the form `g φ`, of the degree of `φ`. -/
theorem of_mul_of_zero_ofFunction (φ : SmoothForm I M ℝ k) (g : C^∞⟮I, M; ℝ⟯) :
    DirectSum.of (fun k ↦ SmoothForm I M ℝ k) k φ * DirectSum.of _ 0 (ofFunction g) =
      DirectSum.of _ k (funSMulₗ g φ) := by
  rw [of_mul_of_eq_of_wedge, wedge_ofFunction]
  -- The degree `k + 0` of the product reduces to `k`.
  rfl

/-- The unit of the algebra of smooth forms is the constant function `1`, in degree `0`. -/
@[simp]
theorem of_zero_ofFunction_one :
    DirectSum.of (fun k ↦ SmoothForm I M ℝ k) 0 (ofFunction 1) = 1 :=
  DirectSum.of_zero_one _

/-- The image of a real number `r` in the algebra of smooth forms is the constant function `r`,
in degree `0`. -/
theorem algebraMap_apply_eq_of_ofFunction (r : ℝ) :
    algebraMap ℝ (⨁ k : ℕ, SmoothForm I M ℝ k) r =
      DirectSum.of (fun k : ℕ ↦ SmoothForm I M ℝ k) 0 (ofFunction (ContMDiffMap.const r)) := by
  rw [DirectSum.algebraMap_apply, gAlgebra_toFun]

/-- The `m`-th power of a homogeneous smooth form of degree `k` is its `m`-th wedge power, of
degree `k * m`. -/
theorem of_pow_eq_of_wedgePow (φ : SmoothForm I M ℝ k) (m : ℕ) :
    DirectSum.of (fun k ↦ SmoothForm I M ℝ k) k φ ^ m =
      DirectSum.of _ (k * m) (wedgePow φ m) := by
  induction m with
  | zero => rw [pow_zero, wedgePow_zero]; exact of_zero_ofFunction_one.symm
  -- The degree `k * m + k` of the product reduces to `k * (m + 1)`.
  | succ m ih => rw [pow_succ, ih, of_mul_of_eq_of_wedge, wedgePow_succ]; rfl

/-- Homogeneous smooth forms of degrees `k` and `l` commute up to the sign `(-1) ^ (k * l)`. -/
theorem of_mul_of_comm (φ : SmoothForm I M ℝ k) (ψ : SmoothForm I M ℝ l) :
    DirectSum.of (fun k ↦ SmoothForm I M ℝ k) k φ * DirectSum.of _ l ψ =
      (-1 : ℝ) ^ (k * l) • (DirectSum.of _ l ψ * DirectSum.of _ k φ) := by
  rw [of_mul_of_eq_of_wedge, of_mul_of_eq_of_wedge, ← DirectSum.of_smul]
  refine DirectSum.of_eq_of_gradedMonoid_eq ?_
  rw [wedge_eq_smul_cast_wedge_comm, ← map_smul, GradedMonoid.mk_linearEquivCast]

/-- A homogeneous smooth form of even degree commutes with every homogeneous smooth form. -/
theorem commute_of_of_of_even (hk : Even k) (φ : SmoothForm I M ℝ k) (ψ : SmoothForm I M ℝ l) :
    Commute (DirectSum.of (fun k ↦ SmoothForm I M ℝ k) k φ) (DirectSum.of _ l ψ) := by
  rw [Commute, SemiconjBy, of_mul_of_comm, (hk.mul_right l).neg_one_pow, one_smul]

end SmoothForm

end TauCeti
