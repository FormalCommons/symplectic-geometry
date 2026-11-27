/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.FundamentalClass
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Smooth
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import SymplecticGeometry.Topology.VectorBundle.Complex.ChernClass.Newton
import SymplecticGeometry.AlgebraicTopology.Cohomology.ProjectiveLinePow
import SymplecticGeometry.AlgebraicTopology.Cohomology.Sphere.Basic
import SymplecticGeometry.AlgebraicTopology.Cohomology.Sphere.Collapse
import SymplecticGeometry.Topology.VectorBundle.Complex.KTheory.Basic
import SymplecticGeometry.Topology.VectorBundle.Complex.KTheory.ProjectiveLinePow

/-!
# Bott's integrality theorem on even spheres

Let `E` be a real inner product space of dimension `2 m + 1` with `m ≠ 0`, so that its unit
sphere `S^{2m}` is a smooth manifold, and let `V` be a complex vector bundle over `S^{2m}`. For
every orientation of `S^{2m}`, the evaluation of the Chern class `c_m(V)` on the fundamental
class is divisible by `(m - 1)!`. This is
`SymplecticGeometry.Bundle.factorial_dvd_evalFundamentalClass_chernClass_sphere`, stated with
`m = r + 1`.

The proof follows Hatcher [Hatcher2017, Chapter 4]:

* The cohomology of `S^{2m}` vanishes in the degrees strictly between `0` and `2m`
  (`TopCat.isZero_integralCohomology_sphere_of_ne`), so Newton's identity
  `SymplecticGeometry.Bundle.newtonClass_eq_of_cup_eq_zero` gives
  `s_m(V) = (-1)^(m-1) m c_m(V)`.
* Let `κ : (ℂP¹)^m → S^{2m}` be the iterated collapse map and `y_i` the pulled-back first Chern
  classes of the tautological lines. By
  `exists_singularCohomologyMap_projectiveLinePowCollapse_eq_evalFundamentalClass_smul`,
  `κ^* s_m(V) = ± ⟨s_m(V), [S^{2m}]⟩ • y_1 ⋯ y_m`.
* By naturality, `κ^* s_m(V)` is the Newton class of the class of `κ^* V` in
  `K((ℂP¹)^m)`, which is a multiple of `m! y_1 ⋯ y_m`
  (`SymplecticGeometry.Bundle.newtonClassHom_mem_zmultiples`).
* The class `y_1 ⋯ y_m` has infinite order
  (`Projectivization.not_isOfFinAddOrder_prod_chernClass`),
  so `m!` divides `± m ⟨c_m(V), [S^{2m}]⟩`, and `(m - 1)!` divides `⟨c_m(V), [S^{2m}]⟩`.

## Main results

* `SymplecticGeometry.Bundle.factorial_dvd_evalFundamentalClass_chernClass_sphere`: for a
  complex vector bundle `V` over `S^{2(r+1)}` and an orientation `o` of the sphere, `r!` divides
  the evaluation of `c_{r+1}(V)` on the fundamental class of `o`.

## References

* [A. Hatcher, *Vector Bundles and K-Theory*, version 2.2 (2017)][Hatcher2017], Chapter 4
  (Bott's integrality theorem on spheres).
* M. F. Atiyah, R. Bott, *On the periodicity theorem for complex vector bundles*, Acta Math. 112
  (1964), 229–247.
-/

public section

open Bundle Module Metric TauCeti
open scoped Manifold Nat LinearAlgebra.Projectivization

namespace SymplecticGeometry.Bundle

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {n : ℕ} [Fact (finrank ℝ E = n + 1)]
  (G : Type) [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  (V : sphere (0 : E) 1 → Type) [∀ b, AddCommGroup (V b)] [∀ b, Module ℂ (V b)]
  [∀ b, Module ℝ (V b)] [∀ b, IsScalarTower ℝ ℂ (V b)] [∀ b, TopologicalSpace (V b)]
  [TopologicalSpace (TotalSpace G V)] [FiberBundle G V] [VectorBundle ℂ G V]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℂ G] in
/-- **Newton's identity on an even sphere.** For a complex vector bundle `V` over the unit
sphere `S^{2m}` of a real inner product space of dimension `2 m + 1`, with `m ≠ 0`,
`s_m(V) = (-1)^(m-1) m c_m(V)`. -/
theorem newtonClass_sphere {m : ℕ} (hE : finrank ℝ E = 2 * m + 1) (hm : m ≠ 0) :
    newtonClass G V m = ((-1) ^ (m - 1) * m : ℤ) • chernClass G V m := by
  refine newtonClass_eq_of_cup_eq_zero G V hm fun a b hab ha hb x y ↦ ?_
  have := ModuleCat.subsingleton_of_isZero
    (TopCat.isZero_integralCohomology_sphere_of_ne hE (q := 2 * a) (by omega) (by omega))
  rw [Subsingleton.elim x 0, map_zero, LinearMap.zero_apply]

/-- **Bott's integrality theorem on even spheres.** Let `V` be a complex vector bundle over the
unit sphere `S^{2(r+1)}` of a real inner product space `E` of dimension `2 (r + 1) + 1`, and let
`o` be an orientation of the sphere. Then `r!` divides the evaluation of the Chern class
`c_{r+1}(V)` on the fundamental class of `o`. -/
theorem factorial_dvd_evalFundamentalClass_chernClass_sphere {r : ℕ}
    (hn : finrank ℝ (EuclideanSpace ℝ (Fin n)) = 2 * r + 2)
    (o : Manifold.Orientation (𝓡 n) (sphere (0 : E) 1) (Fin (2 * r + 2))) :
    (r ! : ℤ) ∣ (o.toHomologicalOrientation hn).evalFundamentalClass hn (ModuleCat.of ℤ ℤ)
      (ContinuousMap.id _) (chernClass G V (r + 1)) := by
  obtain rfl : n = 2 * r + 2 := by simpa using hn
  have : Fact (finrank ℝ E = 2 * r + 1 + 1 + 1) := ⟨Fact.out⟩
  obtain ⟨ε, hε, hκ⟩ :=
    exists_singularCohomologyMap_projectiveLinePowCollapse_eq_evalFundamentalClass_smul r o
  set e := (o.toHomologicalOrientation hn).evalFundamentalClass hn (ModuleCat.of ℤ ℤ)
    (ContinuousMap.id _)
  set Y := (∏ i : Fin (r + 1),
    (TopCat.of (Fin (r + 1) → ℙ ℂ (Fin 2 → ℂ))).evenIntegralCohomologyOf 1
      (Bundle.chernClass ℂ (ContinuousMap.eval (X := fun _ : Fin (r + 1) ↦ ℙ ℂ (Fin 2 → ℂ)) i *ᵖ
        (Projectivization.Tautological ℂ (Fin 2 → ℂ))) 1)) (r + 1)
  -- the Newton class `s_{r+1}` of the class of `κ^* V` in `K((ℂP¹)^(r+1))`
  obtain ⟨k, hk⟩ := newtonClassHom_mem_zmultiples (m := r + 1)
    (SplitK0.of ((FiniteRankBundleCore.ofBundleOfFinrankEq ℂ G V rfl).pullback
      (((sphereHomeomorphTopCatSphere.{0} (F := E) (n := 2 * r + 1 + 1) Fact.out).symm :
        C(TopCat.sphere.{0} (2 * r + 1 + 1), sphere (0 : E) 1)).comp
          (projectiveLinePowCollapse r))))
  rw [newtonClassHom_of, FiniteRankBundleCore.newtonClass_pullback,
    FiniteRankBundleCore.newtonClass_ofBundleOfFinrankEq] at hk
  have hk' : k • ((r + 1)! • Y) = (ε * e (newtonClass G V (r + 1))) • Y := hk.trans (hκ _)
  rw [newtonClass_sphere G V (by have : finrank ℝ E = 2 * r + 2 + 1 := Fact.out; omega)
    (by omega), map_zsmul, smul_eq_mul, Nat.add_sub_cancel] at hk'
  -- since `Y` has infinite order, the coefficients agree
  have hcoeff : k * ((r + 1)! : ℤ) =
      ε * ((-1) ^ r * ((r + 1 : ℕ) : ℤ) * e (chernClass G V (r + 1))) := by
    by_contra hne
    have hz : (k * ((r + 1)! : ℤ) -
        ε * ((-1) ^ r * ((r + 1 : ℕ) : ℤ) * e (chernClass G V (r + 1)))) • Y = 0 := by
      rw [sub_zsmul, ← hk', mul_zsmul, natCast_zsmul, add_neg_cancel]
    exact Projectivization.not_isOfFinAddOrder_prod_chernClass (r + 1)
      (isOfFinAddOrder_iff_zsmul_eq_zero.2 ⟨_, sub_ne_zero.2 hne, hz⟩)
  have hunit : IsUnit (ε * (-1) ^ r : ℤ) := by
    refine IsUnit.mul ?_ (isUnit_neg_one.pow r)
    rcases hε with rfl | rfl <;> simp
  refine hunit.dvd_mul_left.1 ⟨k, mul_left_cancel₀ (by positivity : ((r + 1 : ℕ) : ℤ) ≠ 0) ?_⟩
  rw [Nat.factorial_succ, Nat.cast_mul] at hcoeff
  linear_combination -hcoeff

end SymplecticGeometry.Bundle

end
