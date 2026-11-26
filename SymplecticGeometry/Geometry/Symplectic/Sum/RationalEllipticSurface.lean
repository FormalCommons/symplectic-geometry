/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import SymplecticGeometry.Geometry.Manifold.Projectivization.FubiniStudy.Basic
public import SymplecticGeometry.Geometry.Manifold.Projectivization.ProdZeroLocus.Manifold
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Basic
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Prod
public import TauCeti.LinearAlgebra.Projectivization.ZeroLocus
public import TauCeti.RingTheory.MvPolynomial.Jacobian.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.LocalAtTarget
import SymplecticGeometry.AlgebraicTopology.FundamentalGroup.ComplFinite
import SymplecticGeometry.Geometry.Manifold.Projectivization.FubiniStudy.Kahler
import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.RestrictScalars
import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.Prod
import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.Submanifold
import SymplecticGeometry.RingTheory.MvPolynomial.WeightedHomogeneous
import SymplecticGeometry.Topology.ComplexProjectiveSpace.SimplyConnected
import TauCeti.Geometry.Manifold.MFDeriv.RestrictScalars

/-!
# The rational elliptic surface

The rational elliptic surface `E(1)` is the total space of the Hesse pencil of plane cubics: the
hypersurface `s (x³ + y³ + z³) + t x y z = 0` of `ℂℙ² × ℂℙ¹`. This file starts with the algebra of
its equation, which does not depend on any manifold structure, and then makes the zero set a
compact complex surface by specializing the atlas of bihomogeneous zero sets in a product of two
projective spaces (`SymplecticGeometry.complexProjectiveProdZeroLocusChartedSpace`) to one
equation of bidegree `(3, 1)` in `ℙ ℂ (Fin 3 → ℂ) × ℙ ℂ (Fin 2 → ℂ)`. The regularity it needs is
`SymplecticGeometry.exists_eval_pderiv_hessePencil_ne_zero`, read as surjectivity of the Jacobian
through Tau Ceti's `TauCeti.mulVec_surjective_jacobiMatrixAt_iff_exists_eval_pderiv_ne_zero`.

The last section regards the surface as a real submanifold of `ℂℙ² × ℂℙ¹`, the form in which
the results on complex submanifolds of almost complex manifolds take it
(`TauCeti.SmoothAlmostComplexStructure.restrict`,
`TauCeti.SmoothTwoForm.Tames.isSymplectic_mpullback`). The analytic embedding is a smooth
embedding over `ℝ` (`Manifold.IsSmoothEmbedding.restrictScalars_prod`), its real derivative is
its complex derivative (`MDifferentiableAt.mfderiv_restrictScalars`), and multiplication
by `i` on the tangent spaces of the product is the product of the complex structures of the two
factors (`TauCeti.SmoothAlmostComplexStructure.prod_ofComplexManifold_apply`). So the image of
each real derivative is a complex subspace, invariant under that product structure.

The symplectic form of the surface is the pull-back along this real embedding of the product
`ω_FS ⊕ ω_FS` of the Fubini–Study forms of `ℂℙ²` and `ℂℙ¹` (`TauCeti.SmoothTwoForm.prod`). The
product form is symplectic (`TauCeti.SmoothTwoForm.IsSymplectic.prod`) and tames the product of
the complex structures (`TauCeti.SmoothAlmostComplexStructure.tames_prod`), since each
Fubini–Study form is compatible with the complex structure of its factor
(`SymplecticGeometry.compatible_fubiniStudyForm`). A symplectic form that tames an almost complex
structure pulls back to a symplectic form on a submanifold with invariant tangent spaces
(`TauCeti.SmoothTwoForm.Tames.isSymplectic_mpullback`). No Kähler condition is used.

The variables are indexed by `Fin 3 ⊕ Fin 2`: `Sum.inl 0`, `Sum.inl 1`, `Sum.inl 2` are the
homogeneous coordinates `x, y, z` of the plane, and `Sum.inr 0`, `Sum.inr 1` are the homogeneous
coordinates `s, t` of the line. A point of the cone `K³ × K²` is written `Sum.elim v w`.

## Main declarations

* `SymplecticGeometry.hessePencil R`: the polynomial `s (x³ + y³ + z³) + t x y z`.
* `SymplecticGeometry.eval_hessePencil` and the lemmas `pderiv_inl_zero_hessePencil`, …,
  `pderiv_inr_one_hessePencil`: its evaluation and its five partial derivatives.
* `SymplecticGeometry.isWeightedHomogeneous_hessePencil`: it is weighted homogeneous of degree
  `3 a + b` for the weights `a` on `x, y, z` and `b` on `s, t`; the special cases
  `SymplecticGeometry.isWeightedHomogeneous_hessePencil_inl` and
  `SymplecticGeometry.isWeightedHomogeneous_hessePencil_inr` say that it is bihomogeneous of
  bidegree `(3, 1)`.
* `SymplecticGeometry.sum_mul_eval_pderiv_inl_hessePencil` and
  `SymplecticGeometry.sum_mul_eval_pderiv_inr_hessePencil`: the two Euler relations.
* `SymplecticGeometry.exists_eval_pderiv_hessePencil_ne_zero`: over a field in which `3 ≠ 0`, at
  every point `(v, w)` with `v ≠ 0` and `w ≠ 0` some partial derivative is nonzero; in particular
  the hypersurface is smooth.
* `SymplecticGeometry.exists_eval_pderiv_hessePencil_ne_zero_of_ne_zero`: in the affine chart
  where `v i ≠ 0` and `w j ≠ 0`, the nonzero partial derivative can be taken in a variable other
  than `Sum.inl i` and `Sum.inr j`, that is, in a coordinate of the chart. The step from the cone
  to the chart is `MvPolynomial.IsWeightedHomogeneous.eval_pderiv_eq_zero_of_eval_eq_zero`,
  applied to each of the two blocks of coordinates.
* `SymplecticGeometry.rationalEllipticSurface`: the zero set of `hessePencil ℂ` in
  `ℙ ℂ (Fin 3 → ℂ) × ℙ ℂ (Fin 2 → ℂ)`, with the membership tests
  `SymplecticGeometry.mem_rationalEllipticSurface_iff` (on the chosen representatives) and
  `SymplecticGeometry.mk_mem_rationalEllipticSurface_iff` (on any nonzero ones).
* The instances `ChartedSpace`, `IsManifold 𝓘(ℂ, _) ω` and `CompactSpace` on it, on the
  model `Fin 2 → ℂ`: the general atlas is taken with `k := 2`, and its dimension hypothesis
  `2 + Fintype.card Unit = 2 + 1` holds by `simp`.
* `SymplecticGeometry.rationalEllipticSurface.embedding`: the inclusion into the product as an
  analytic embedding, for the model `𝓘(ℂ, Fin 2 → ℂ).prod 𝓘(ℂ, Fin 1 → ℂ)`.
* `SymplecticGeometry.rationalEllipticSurface.contMDiff_fst` and
  `SymplecticGeometry.rationalEllipticSurface.contMDiff_snd`: the projections to `ℂℙ²` and `ℂℙ¹`
  are analytic.
* `SymplecticGeometry.rationalEllipticSurface.realEmbedding`: the inclusion as a smooth embedding
  over `ℝ`, for the model `𝓘(ℝ, Fin 2 → ℂ).prod 𝓘(ℝ, Fin 1 → ℂ)`, and
  `SymplecticGeometry.rationalEllipticSurface.coe_mfderiv_realEmbedding`: its real derivative is
  the complex derivative of `SymplecticGeometry.rationalEllipticSurface.embedding`.
* `SymplecticGeometry.rationalEllipticSurface.prod_ofComplexManifold_mem_tangentRange`: the
  tangent images of `realEmbedding` are invariant under the product of the complex structures of
  `ℂℙ²` and `ℂℙ¹`.
* `SymplecticGeometry.rationalEllipticSurface.symplecticForm`: the pull-back of the product of
  the Fubini–Study forms, and
  `SymplecticGeometry.rationalEllipticSurface.isSymplectic_symplecticForm`: it is symplectic.
* `SymplecticGeometry.hesseCubics R`: the two cubics `x³ + y³ + z³` and `x y z` of the plane
  that span the pencil, both homogeneous of degree three
  (`SymplecticGeometry.isHomogeneous_hesseCubics`).
* `SymplecticGeometry.rationalEllipticSurface.baseLocus`: the common zeros in `ℂℙ²` of
  `x³ + y³ + z³` and `x y z`, through which every curve of the pencil passes, as Tau Ceti's
  zero locus `TauCeti.complexProjectiveZeroLocus (hesseCubics ℂ)`, and
  `SymplecticGeometry.rationalEllipticSurface.finite_baseLocus`: there are finitely many.
* `SymplecticGeometry.rationalEllipticSurface.mk_mem_of_mem_baseLocus` and
  `SymplecticGeometry.rationalEllipticSurface.mk_mem_iff_eq_pencilMember`: the fibre of the
  projection to `ℂℙ²` is the whole line `ℂℙ¹` over a base point, and the single point
  `pencilMember p _ = [pencilVector v]`, with `pencilVector v = (x y z, -(x³ + y³ + z³))` at a
  representative `v`, over any other point `p = [v]`.
* `SymplecticGeometry.rationalEllipticSurface.complBaseLocusHomeomorph`: the projection is a
  homeomorphism from the open set `complBaseLocus` of points over the complement of the base
  locus onto that complement; it is a closed map since the surface is compact
  (`Equiv.toHomeomorphOfContinuousClosed`).
* `SymplecticGeometry.rationalEllipticSurface.simplyConnectedSpace_complBaseLocus`: that open set
  is simply connected, since `ℂℙ²` is and deleting finitely many points from a manifold of real
  dimension four does not change this
  (`SymplecticGeometry.simplyConnectedSpace_compl_iff_of_finite`).

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §7.2.
* [R. E. Gompf, *A new construction of symplectic manifolds*][Gompf1995].
-/

public section

open MvPolynomial Set TauCeti
open scoped ContDiff Manifold LinearAlgebra.Projectivization

namespace SymplecticGeometry

variable (R : Type*) [CommSemiring R]

/-- The equation of the Hesse pencil, `s (x³ + y³ + z³) + t x y z`, in the variables
`x, y, z = Sum.inl 0, Sum.inl 1, Sum.inl 2` and `s, t = Sum.inr 0, Sum.inr 1`. -/
noncomputable def hessePencil : MvPolynomial (Fin 3 ⊕ Fin 2) R :=
  X (.inr 0) * (X (.inl 0) ^ 3 + X (.inl 1) ^ 3 + X (.inl 2) ^ 3) +
    X (.inr 1) * (X (.inl 0) * X (.inl 1) * X (.inl 2))

theorem hessePencil_def : hessePencil R =
    X (.inr 0) * (X (.inl 0) ^ 3 + X (.inl 1) ^ 3 + X (.inl 2) ^ 3) +
      X (.inr 1) * (X (.inl 0) * X (.inl 1) * X (.inl 2)) :=
  (rfl)

/-- The two plane cubics `x³ + y³ + z³` and `x y z` that span the Hesse pencil, in the variables
`x, y, z = 0, 1, 2`. -/
noncomputable def hesseCubics : Fin 2 → MvPolynomial (Fin 3) R :=
  ![X 0 ^ 3 + X 1 ^ 3 + X 2 ^ 3, X 0 * X 1 * X 2]

@[simp]
theorem hesseCubics_zero : hesseCubics R 0 = X 0 ^ 3 + X 1 ^ 3 + X 2 ^ 3 :=
  (rfl)

@[simp]
theorem hesseCubics_one : hesseCubics R 1 = X 0 * X 1 * X 2 :=
  (rfl)

variable {R}

/-- Both cubics spanning the Hesse pencil are homogeneous of degree three. -/
theorem isHomogeneous_hesseCubics (i : Fin 2) : (hesseCubics R i).IsHomogeneous 3 := by
  fin_cases i
  · simp only [Fin.zero_eta, hesseCubics_zero]
    exact (((isHomogeneous_X_pow _ _).add (isHomogeneous_X_pow _ _)).add (isHomogeneous_X_pow _ _))
  · simp only [Fin.mk_one, hesseCubics_one]
    exact ((isHomogeneous_X _ _).mul (isHomogeneous_X _ _)).mul (isHomogeneous_X _ _)

@[simp]
theorem eval_hessePencil (p : Fin 3 ⊕ Fin 2 → R) :
    eval p (hessePencil R) = p (.inr 0) * (p (.inl 0) ^ 3 + p (.inl 1) ^ 3 + p (.inl 2) ^ 3) +
      p (.inr 1) * (p (.inl 0) * p (.inl 1) * p (.inl 2)) := by
  simp [hessePencil_def]

@[simp]
theorem pderiv_inl_zero_hessePencil :
    pderiv (.inl 0) (hessePencil R) =
      3 * X (.inr 0) * X (.inl 0) ^ 2 + X (.inr 1) * (X (.inl 1) * X (.inl 2)) := by
  simp [hessePencil_def, pderiv_X]
  ring

@[simp]
theorem pderiv_inl_one_hessePencil :
    pderiv (.inl 1) (hessePencil R) =
      3 * X (.inr 0) * X (.inl 1) ^ 2 + X (.inr 1) * (X (.inl 0) * X (.inl 2)) := by
  simp [hessePencil_def, pderiv_X]
  ring

@[simp]
theorem pderiv_inl_two_hessePencil :
    pderiv (.inl 2) (hessePencil R) =
      3 * X (.inr 0) * X (.inl 2) ^ 2 + X (.inr 1) * (X (.inl 0) * X (.inl 1)) := by
  simp [hessePencil_def, pderiv_X]
  ring

@[simp]
theorem pderiv_inr_zero_hessePencil :
    pderiv (.inr 0) (hessePencil R) = X (.inl 0) ^ 3 + X (.inl 1) ^ 3 + X (.inl 2) ^ 3 := by
  simp [hessePencil_def, pderiv_X]

@[simp]
theorem pderiv_inr_one_hessePencil :
    pderiv (.inr 1) (hessePencil R) = X (.inl 0) * X (.inl 1) * X (.inl 2) := by
  simp [hessePencil_def, pderiv_X]

/-- The Hesse pencil is weighted homogeneous of degree `3 a + b` when `x, y, z` have weight `a`
and `s, t` have weight `b`. -/
theorem isWeightedHomogeneous_hessePencil (a b : ℕ) :
    (hessePencil R).IsWeightedHomogeneous (Sum.elim (fun _ ↦ a) (fun _ ↦ b)) (3 * a + b) := by
  have hX (i : Fin 3) :=
    isWeightedHomogeneous_X R (Sum.elim (fun _ : Fin 3 ↦ a) (fun _ : Fin 2 ↦ b)) (.inl i)
  have hY (j : Fin 2) :=
    isWeightedHomogeneous_X R (Sum.elim (fun _ : Fin 3 ↦ a) (fun _ : Fin 2 ↦ b)) (.inr j)
  simp only [Sum.elim_inl, Sum.elim_inr] at hX hY
  have hxyz := ((hX 0).mul (hX 1)).mul (hX 2)
  rw [show a + a + a = 3 • a by rw [smul_eq_mul]; ring] at hxyz
  rw [hessePencil_def]
  convert ((hY 0).mul (((hX 0).pow 3).add ((hX 1).pow 3) |>.add ((hX 2).pow 3))).add
    ((hY 1).mul hxyz) using 1
  rw [smul_eq_mul, add_comm]

/-- The Hesse pencil is homogeneous of degree `3` in the coordinates `x, y, z` of the plane. -/
theorem isWeightedHomogeneous_hessePencil_inl :
    (hessePencil R).IsWeightedHomogeneous (Sum.elim (1 : Fin 3 → ℕ) 0) 3 :=
  isWeightedHomogeneous_hessePencil 1 0

/-- The Hesse pencil is homogeneous of degree `1` in the coordinates `s, t` of the line. -/
theorem isWeightedHomogeneous_hessePencil_inr :
    (hessePencil R).IsWeightedHomogeneous (Sum.elim 0 (1 : Fin 2 → ℕ)) 1 :=
  isWeightedHomogeneous_hessePencil 0 1

/-- Euler's relation for the plane coordinates: `x ∂ₓP + y ∂ᵧP + z ∂_zP = 3 P`. -/
theorem sum_mul_eval_pderiv_inl_hessePencil (p : Fin 3 ⊕ Fin 2 → R) :
    ∑ k : Fin 3, p (.inl k) * eval p (pderiv (.inl k) (hessePencil R)) =
      3 * eval p (hessePencil R) := by
  simpa [Fintype.sum_sum_type] using
    isWeightedHomogeneous_hessePencil_inl.sum_weight_mul_eval_pderiv p

/-- Euler's relation for the line coordinates: `s ∂ₛP + t ∂ₜP = P`. -/
theorem sum_mul_eval_pderiv_inr_hessePencil (p : Fin 3 ⊕ Fin 2 → R) :
    ∑ k : Fin 2, p (.inr k) * eval p (pderiv (.inr k) (hessePencil R)) =
      eval p (hessePencil R) := by
  simp

variable {K : Type*} [Field K]

/-- **The Hesse pencil is smooth.** Over a field in which `3 ≠ 0`, the partial derivatives of the
Hesse pencil have no common zero `(v, w)` with `v ≠ 0` and `w ≠ 0`; in particular none on its
zero set. The hypothesis `3 ≠ 0` is needed: in characteristic `3` they all vanish at
`v = (1, -1, 0)`, `w = (1, 0)`. -/
theorem exists_eval_pderiv_hessePencil_ne_zero (h3 : (3 : K) ≠ 0) {v : Fin 3 → K}
    (hv : v ≠ 0) {w : Fin 2 → K} (hw : w ≠ 0) :
    ∃ k, eval (Sum.elim v w) (pderiv k (hessePencil K)) ≠ 0 := by
  by_contra! H
  have h00 := H (.inl 0)
  have h01 := H (.inl 1)
  have h02 := H (.inl 2)
  have h10 := H (.inr 0)
  have h11 := H (.inr 1)
  simp only [pderiv_inl_zero_hessePencil, pderiv_inl_one_hessePencil,
    pderiv_inl_two_hessePencil, pderiv_inr_zero_hessePencil, pderiv_inr_one_hessePencil, map_add,
    map_mul, map_pow, eval_X, Sum.elim_inl, Sum.elim_inr, map_ofNat] at h00 h01 h02 h10 h11
  have key : (v 0 = 0 ∧ v 1 = 0 ∧ v 2 = 0) ∨ (w 0 = 0 ∧ w 1 = 0) := by grind
  rcases key with ⟨h0, h1, h2⟩ | ⟨h0, h1⟩
  · exact hv (funext fun k ↦ by fin_cases k <;> assumption)
  · exact hw (funext fun k ↦ by fin_cases k <;> assumption)

/-- In the affine chart of `ℙ² × ℙ¹` where `v i ≠ 0` and `w j ≠ 0`, a zero of the Hesse pencil has
a nonzero partial derivative in a variable other than `Sum.inl i` and `Sum.inr j`, that is, in a
coordinate of the chart. -/
theorem exists_eval_pderiv_hessePencil_ne_zero_of_ne_zero (h3 : (3 : K) ≠ 0) {v : Fin 3 → K}
    {w : Fin 2 → K} {i : Fin 3} {j : Fin 2} (hi : v i ≠ 0) (hj : w j ≠ 0)
    (h : eval (Sum.elim v w) (hessePencil K) = 0) :
    ∃ k, k ≠ .inl i ∧ k ≠ .inr j ∧ eval (Sum.elim v w) (pderiv k (hessePencil K)) ≠ 0 := by
  by_contra! H
  obtain ⟨k, hk⟩ := exists_eval_pderiv_hessePencil_ne_zero h3 (v := v) (w := w)
    (fun hv ↦ hi (congrFun hv i)) (fun hw ↦ hj (congrFun hw j))
  refine hk ?_
  rcases k with l | l
  · obtain rfl | hl := eq_or_ne l i
    · refine isWeightedHomogeneous_hessePencil_inl.eval_pderiv_eq_zero_of_eval_eq_zero h
        (by simpa using hi) (by simp) fun k hk hwk ↦ ?_
      rcases k with k | k
      · exact H _ hk (by simp)
      · simp at hwk
    · exact H _ (by simpa using hl) (by simp)
  · obtain rfl | hl := eq_or_ne l j
    · refine isWeightedHomogeneous_hessePencil_inr.eval_pderiv_eq_zero_of_eval_eq_zero h
        (by simpa using hj) (by simp) fun k hk hwk ↦ ?_
      rcases k with k | k
      · simp at hwk
      · exact H _ (by simp) hk
    · exact H _ (by simp) (by simpa using hl)

/-! ### The surface -/

/-- The **rational elliptic surface** `E(1)`: the zero set of the Hesse pencil
`s (x³ + y³ + z³) + t x y z` in `ℙ ℂ (Fin 3 → ℂ) × ℙ ℂ (Fin 2 → ℂ)`, that is in `ℂℙ² × ℂℙ¹`. -/
noncomputable def rationalEllipticSurface : Set (ℙ ℂ (Fin 3 → ℂ) × ℙ ℂ (Fin 2 → ℂ)) :=
  complexProjectiveProdZeroLocus (m := 2) (n := 1) fun _ : Unit ↦ hessePencil ℂ

theorem rationalEllipticSurface_def :
    rationalEllipticSurface =
      complexProjectiveProdZeroLocus (m := 2) (n := 1) fun _ : Unit ↦ hessePencil ℂ :=
  (rfl)

/-- A pair of points of `ℂℙ²` and `ℂℙ¹` lies on the rational elliptic surface when the Hesse
pencil vanishes at their chosen representatives. -/
theorem mem_rationalEllipticSurface_iff {x : ℙ ℂ (Fin 3 → ℂ) × ℙ ℂ (Fin 2 → ℂ)} :
    x ∈ rationalEllipticSurface ↔ eval (Sum.elim x.1.rep x.2.rep) (hessePencil ℂ) = 0 := by
  rw [rationalEllipticSurface_def, mem_complexProjectiveProdZeroLocus_iff_eval_rep
    (fun _ ↦ isWeightedHomogeneous_hessePencil_inl) (fun _ ↦ isWeightedHomogeneous_hessePencil_inr)]
  simp

/-- The pair of points spanned by nonzero vectors `v` and `w` lies on the rational elliptic
surface exactly when the Hesse pencil vanishes at `Sum.elim v w`. -/
@[simp]
theorem mk_mem_rationalEllipticSurface_iff {v : Fin 3 → ℂ} (hv : v ≠ 0) {w : Fin 2 → ℂ}
    (hw : w ≠ 0) :
    (Projectivization.mk ℂ v hv, Projectivization.mk ℂ w hw) ∈ rationalEllipticSurface ↔
      eval (Sum.elim v w) (hessePencil ℂ) = 0 := by
  rw [rationalEllipticSurface_def, mk_mem_complexProjectiveProdZeroLocus_iff
    (fun _ ↦ isWeightedHomogeneous_hessePencil_inl) (fun _ ↦ isWeightedHomogeneous_hessePencil_inr)]
  simp

namespace rationalEllipticSurface

/-- The rational elliptic surface is the zero set of the Hesse pencil cut by the open set `univ`,
the form in which the zero-set atlas takes it. -/
theorem eq_inter_univ :
    rationalEllipticSurface =
      complexProjectiveProdZeroLocus (m := 2) (n := 1) (fun _ : Unit ↦ hessePencil ℂ) ∩ univ := by
  rw [rationalEllipticSurface_def, inter_univ]

/-- The cone Jacobian of the Hesse pencil is surjective at the chosen representatives of every
point of `ℂℙ² × ℂℙ¹`, whether or not it lies on the rational elliptic surface. -/
theorem surjective_jacobiMatrixAt (x : ℙ ℂ (Fin 3 → ℂ) × ℙ ℂ (Fin 2 → ℂ)) :
    Function.Surjective
      (jacobiMatrixAt (fun _ : Unit ↦ hessePencil ℂ) (Sum.elim x.1.rep x.2.rep)).mulVec :=
  mulVec_surjective_jacobiMatrixAt_iff_exists_eval_pderiv_ne_zero.2
    (exists_eval_pderiv_hessePencil_ne_zero three_ne_zero x.1.rep_ne_zero x.2.rep_ne_zero)

/-- The atlas of the rational elliptic surface, induced by the slice charts of bihomogeneous zero
sets in `ℂℙ² × ℂℙ¹`. -/
noncomputable instance instChartedSpace : ChartedSpace (Fin 2 → ℂ) rationalEllipticSurface :=
  complexProjectiveProdZeroLocusChartedSpace (k := 2) (by simp)
    (fun _ ↦ isWeightedHomogeneous_hessePencil_inl)
    (fun _ ↦ isWeightedHomogeneous_hessePencil_inr) isOpen_univ eq_inter_univ
    fun x _ ↦ surjective_jacobiMatrixAt x

/-- The rational elliptic surface is a complex analytic manifold. -/
instance instIsManifold : IsManifold 𝓘(ℂ, Fin 2 → ℂ) ω rationalEllipticSurface :=
  isManifold_complexProjectiveProdZeroLocus (k := 2) (by simp)
    (fun _ ↦ isWeightedHomogeneous_hessePencil_inl)
    (fun _ ↦ isWeightedHomogeneous_hessePencil_inr) isOpen_univ eq_inter_univ
    (fun x _ ↦ surjective_jacobiMatrixAt x) ω

/-- The rational elliptic surface is compact, as every zero set in `ℂℙ² × ℂℙ¹` is. -/
instance instCompactSpace : CompactSpace rationalEllipticSurface :=
  inferInstanceAs (CompactSpace (complexProjectiveProdZeroLocus _))

/-- The inclusion of the rational elliptic surface into `ℂℙ² × ℂℙ¹`, as an analytic embedding:
`SymplecticGeometry.complexProjectiveProdZeroLocusEmbedding`. -/
noncomputable def embedding :
    SmoothEmbedding 𝓘(ℂ, Fin 2 → ℂ)
      (𝓘(ℂ, Fin 2 → ℂ).prod 𝓘(ℂ, Fin 1 → ℂ)) ω rationalEllipticSurface
      (ℙ ℂ (Fin 3 → ℂ) × ℙ ℂ (Fin 2 → ℂ)) :=
  complexProjectiveProdZeroLocusEmbedding (k := 2) (by simp)
    (fun _ ↦ isWeightedHomogeneous_hessePencil_inl)
    (fun _ ↦ isWeightedHomogeneous_hessePencil_inr) isOpen_univ eq_inter_univ
    (fun x _ ↦ surjective_jacobiMatrixAt x) ω

/-- The embedding of the rational elliptic surface is the embedding of a bihomogeneous zero set,
specialized to the Hesse pencil. -/
theorem embedding_def :
    embedding = complexProjectiveProdZeroLocusEmbedding (k := 2) (by simp)
      (fun _ ↦ isWeightedHomogeneous_hessePencil_inl)
      (fun _ ↦ isWeightedHomogeneous_hessePencil_inr) isOpen_univ eq_inter_univ
      (fun x _ ↦ surjective_jacobiMatrixAt x) ω :=
  (rfl)

/-- The embedding of the rational elliptic surface is the inclusion. -/
@[simp]
theorem coe_embedding : ⇑embedding = Subtype.val := by
  rw [embedding_def, coe_complexProjectiveProdZeroLocusEmbedding]

/-- The projection of the rational elliptic surface to `ℂℙ²` is analytic. -/
theorem contMDiff_fst :
    ContMDiff 𝓘(ℂ, Fin 2 → ℂ) 𝓘(ℂ, Fin 2 → ℂ) ω
      (fun x : rationalEllipticSurface ↦ (x : ℙ ℂ (Fin 3 → ℂ) × ℙ ℂ (Fin 2 → ℂ)).1) :=
  _root_.contMDiff_fst.comp (coe_embedding ▸ embedding.contMDiff)

/-- The projection of the rational elliptic surface to `ℂℙ¹` is analytic. -/
theorem contMDiff_snd :
    ContMDiff 𝓘(ℂ, Fin 2 → ℂ) 𝓘(ℂ, Fin 1 → ℂ) ω
      (fun x : rationalEllipticSurface ↦ (x : ℙ ℂ (Fin 3 → ℂ) × ℙ ℂ (Fin 2 → ℂ)).2) :=
  _root_.contMDiff_snd.comp (coe_embedding ▸ embedding.contMDiff)

/-! ### The underlying real submanifold -/

open scoped ComplexManifold

/-- The inclusion of the rational elliptic surface into `ℂℙ² × ℂℙ¹`, as a smooth embedding of
the underlying real manifolds, for the real model `𝓘(ℝ, Fin 2 → ℂ).prod 𝓘(ℝ, Fin 1 → ℂ)` of the
product. -/
noncomputable def realEmbedding :
    SmoothEmbedding 𝓘(ℝ, Fin 2 → ℂ)
      (𝓘(ℝ, Fin 2 → ℂ).prod 𝓘(ℝ, Fin 1 → ℂ)) ∞ rationalEllipticSurface
      (ℙ ℂ (Fin 3 → ℂ) × ℙ ℂ (Fin 2 → ℂ)) :=
  .ofIsSmoothEmbedding Subtype.val <|
    ((coe_embedding ▸ embedding.isSmoothEmbedding).of_le le_top).restrictScalars_prod ℝ
      (by simp)

/-- The real embedding of the rational elliptic surface is the inclusion. -/
@[simp]
theorem coe_realEmbedding : ⇑realEmbedding = Subtype.val :=
  SmoothEmbedding.coe_ofIsSmoothEmbedding _ _

/-- The real derivative of the inclusion of the rational elliptic surface is its complex
derivative, as a map of tangent vectors. -/
theorem coe_mfderiv_realEmbedding (x : rationalEllipticSurface) :
    ⇑(mfderiv 𝓘(ℝ, Fin 2 → ℂ)
        (𝓘(ℝ, Fin 2 → ℂ).prod 𝓘(ℝ, Fin 1 → ℂ)) realEmbedding x) =
      mfderiv 𝓘(ℂ, Fin 2 → ℂ)
        (𝓘(ℂ, Fin 2 → ℂ).prod 𝓘(ℂ, Fin 1 → ℂ)) embedding x := by
  have hd := (embedding.contMDiff x).mdifferentiableAt (by simp)
  have h := congrArg DFunLike.coe (hd.mfderiv_restrictScalars ℝ)
  rw [ModelWithCorners.restrictScalars_prod, modelWithCornersSelf_restrictScalars,
    modelWithCornersSelf_restrictScalars] at h
  rw [coe_realEmbedding, ← coe_embedding, h]
  exact funext (ContinuousLinearMap.restrictScalarsTangent_apply _)

/-- The tangent spaces of the rational elliptic surface, as a real submanifold of `ℂℙ² × ℂℙ¹`,
are invariant under the product of the complex structures of `ℂℙ²` and `ℂℙ¹`. -/
theorem prod_ofComplexManifold_mem_tangentRange {hn : (∞ : ℕ∞ω) ≠ 0}
    (x : rationalEllipticSurface) (v) (hv : v ∈ realEmbedding.tangentRange x hn) :
    (SmoothAlmostComplexStructure.ofComplexManifold (Fin 2 → ℂ) (ℙ ℂ (Fin 3 → ℂ))).prod
        (SmoothAlmostComplexStructure.ofComplexManifold (Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ)))
          (realEmbedding x) v ∈
      realEmbedding.tangentRange x hn := by
  rw [SmoothEmbedding.mem_tangentRange_iff] at hv ⊢
  obtain ⟨u, rfl⟩ := hv
  -- `prod_ofComplexManifold_apply` states `v` in `E × F`, so it does not rewrite directly.
  have h := SmoothAlmostComplexStructure.prod_ofComplexManifold_apply (realEmbedding x)
    (mfderiv _ (𝓘(ℝ, Fin 2 → ℂ).prod 𝓘(ℝ, Fin 1 → ℂ)) realEmbedding x u)
  rw [h, coe_mfderiv_realEmbedding]
  -- The real and the complex tangent spaces of the surface at `x` are both its model space.
  exact ⟨_, (mfderiv _ _ embedding x).map_smul Complex.I u⟩

/-! ### The symplectic form -/

/-- The symplectic form of the rational elliptic surface: the pull-back along the inclusion of
the product `pr₁^* ω_FS + pr₂^* ω_FS` of the Fubini–Study forms of `ℂℙ²` and `ℂℙ¹`. -/
noncomputable def symplecticForm :
    SmoothTwoForm 𝓘(ℝ, Fin 2 → ℂ) rationalEllipticSurface :=
  SmoothForm.mpullback realEmbedding realEmbedding.contMDiff
    ((fubiniStudyForm 2).prod (fubiniStudyForm 1))

theorem symplecticForm_def :
    symplecticForm = SmoothForm.mpullback realEmbedding realEmbedding.contMDiff
      ((fubiniStudyForm 2).prod (fubiniStudyForm 1)) :=
  (rfl)

/-- The symplectic form of the rational elliptic surface is symplectic: closed and
nondegenerate. -/
theorem isSymplectic_symplecticForm : symplecticForm.IsSymplectic := by
  rw [symplecticForm_def]
  exact (SmoothAlmostComplexStructure.tames_prod (compatible_fubiniStudyForm (n := 2)).tames
    (compatible_fubiniStudyForm (n := 1)).tames).isSymplectic_mpullback
      (hn := by simp) prod_ofComplexManifold_mem_tangentRange
      ((isSymplectic_fubiniStudyForm 2).prod (isSymplectic_fubiniStudyForm 1))

/-! ### The base locus of the pencil and its complement -/

/-- The **base locus** of the Hesse pencil: the points of `ℂℙ²` at which both cubics
`hesseCubics ℂ`, that is `x³ + y³ + z³` and `x y z`, vanish, so that every member
`s (x³ + y³ + z³) + t x y z` of the pencil passes through them. -/
noncomputable def baseLocus : Set (ℙ ℂ (Fin 3 → ℂ)) :=
  complexProjectiveZeroLocus (hesseCubics ℂ)

theorem baseLocus_def : baseLocus = complexProjectiveZeroLocus (hesseCubics ℂ) :=
  (rfl)

/-- The point spanned by a nonzero vector `v` lies in the base locus of the Hesse pencil exactly
when `x³ + y³ + z³` and `x y z` both vanish at `v`. -/
@[simp]
theorem mk_mem_baseLocus_iff {v : Fin 3 → ℂ} (hv : v ≠ 0) :
    Projectivization.mk ℂ v hv ∈ baseLocus ↔
      v 0 ^ 3 + v 1 ^ 3 + v 2 ^ 3 = 0 ∧ v 0 * v 1 * v 2 = 0 := by
  rw [baseLocus_def, complexProjectiveZeroLocus_mk_iff isHomogeneous_hesseCubics,
    Fin.forall_fin_two]
  simp

theorem mem_baseLocus_iff {p : ℙ ℂ (Fin 3 → ℂ)} :
    p ∈ baseLocus ↔
      p.rep 0 ^ 3 + p.rep 1 ^ 3 + p.rep 2 ^ 3 = 0 ∧ p.rep 0 * p.rep 1 * p.rep 2 = 0 := by
  conv_lhs => rw [← p.mk_rep]
  exact mk_mem_baseLocus_iff _

/-- The base locus of the Hesse pencil is finite. At a point of it one coordinate vanishes and
the other two `a`, `b` satisfy `a³ = -b³`, so they are both nonzero and the point is
`[0 : 1 : c]`, `[1 : 0 : c]` or `[1 : c : 0]` with `c³ = -1`. -/
theorem finite_baseLocus : baseLocus.Finite := by
  have hc : {c : ℂ | c ^ 3 = -1}.Finite :=
    ((Polynomial.nthRoots 3 (-1 : ℂ)).toFinset.finite_toSet).subset fun c hc ↦ by
      simpa [Polynomial.mem_nthRoots] using hc
  have h0 (c : ℂ) : ![0, 1, c] ≠ 0 := fun h ↦ one_ne_zero (congrFun h 1)
  have h1 (c : ℂ) : ![1, 0, c] ≠ 0 := fun h ↦ one_ne_zero (congrFun h 0)
  have h2 (c : ℂ) : ![1, c, 0] ≠ 0 := fun h ↦ one_ne_zero (congrFun h 0)
  refine (((hc.image fun c ↦ Projectivization.mk ℂ _ (h0 c)).union
    (hc.image fun c ↦ Projectivization.mk ℂ _ (h1 c))).union
      (hc.image fun c ↦ Projectivization.mk ℂ _ (h2 c))).subset ?_
  intro p hp
  induction p using Projectivization.ind with | h v hv => ?_
  rw [mk_mem_baseLocus_iff] at hp
  obtain ⟨hf, hg⟩ := hp
  have hv' : ¬(v 0 = 0 ∧ v 1 = 0 ∧ v 2 = 0) := fun h ↦
    hv (funext fun k ↦ by fin_cases k <;> simp [h.1, h.2.1, h.2.2])
  simp only [Set.mem_union, Set.mem_image, Set.mem_ofPred_eq]
  rcases mul_eq_zero.1 hg with hg | hg
  · rcases mul_eq_zero.1 hg with hg | hg
    · -- `v = (0, a, b)` with `a ≠ 0`, and `p = [0 : 1 : b / a]`.
      have ha : v 1 ≠ 0 := by grind
      refine .inl (.inl ⟨v 2 / v 1, ?_, ?_⟩)
      · rw [div_pow]; field_simp; linear_combination hf - (v 0) ^ 2 * hg
      · rw [Projectivization.mk_eq_mk_iff']
        refine ⟨(v 1)⁻¹, funext fun k ↦ ?_⟩
        fin_cases k <;> simp [hg, ha, div_eq_inv_mul]
    · -- `v = (a, 0, b)` with `a ≠ 0`, and `p = [1 : 0 : b / a]`.
      have ha : v 0 ≠ 0 := by grind
      refine .inl (.inr ⟨v 2 / v 0, ?_, ?_⟩)
      · rw [div_pow]; field_simp; linear_combination hf - (v 1) ^ 2 * hg
      · rw [Projectivization.mk_eq_mk_iff']
        refine ⟨(v 0)⁻¹, funext fun k ↦ ?_⟩
        fin_cases k <;> simp [hg, ha, div_eq_inv_mul]
  · -- `v = (a, b, 0)` with `a ≠ 0`, and `p = [1 : b / a : 0]`.
    have ha : v 0 ≠ 0 := by grind
    refine .inr ⟨v 1 / v 0, ?_, ?_⟩
    · rw [div_pow]; field_simp; linear_combination hf - (v 2) ^ 2 * hg
    · rw [Projectivization.mk_eq_mk_iff']
      refine ⟨(v 0)⁻¹, funext fun k ↦ ?_⟩
      fin_cases k <;> simp [hg, ha, div_eq_inv_mul]

/-- Over a point of the base locus, the fibre of the projection of the rational elliptic surface
to `ℂℙ²` is the whole line `{p} × ℂℙ¹`. -/
theorem mk_mem_of_mem_baseLocus {p : ℙ ℂ (Fin 3 → ℂ)} (hp : p ∈ baseLocus)
    (q : ℙ ℂ (Fin 2 → ℂ)) : (p, q) ∈ rationalEllipticSurface := by
  rw [mem_baseLocus_iff] at hp
  rw [mem_rationalEllipticSurface_iff]
  simp [hp.1, hp.2]

/-- The vector `(x y z, -(x³ + y³ + z³))` of `ℂ²`, evaluated at `v`: the coordinates `[s : t]` of
the member `s (x³ + y³ + z³) + t x y z` of the Hesse pencil through `[v]`. -/
noncomputable def pencilVector (v : Fin 3 → ℂ) : Fin 2 → ℂ :=
  ![eval v (hesseCubics ℂ 1), -eval v (hesseCubics ℂ 0)]

@[simp]
theorem pencilVector_zero (v : Fin 3 → ℂ) : pencilVector v 0 = v 0 * v 1 * v 2 := by
  simp [pencilVector]

@[simp]
theorem pencilVector_one (v : Fin 3 → ℂ) :
    pencilVector v 1 = -(v 0 ^ 3 + v 1 ^ 3 + v 2 ^ 3) := by
  simp [pencilVector]

/-- Both entries of `pencilVector` are homogeneous of degree three. -/
theorem pencilVector_smul (c : ℂ) (v : Fin 3 → ℂ) :
    pencilVector (c • v) = c ^ 3 • pencilVector v := by
  ext k
  fin_cases k <;>
    simp [pencilVector, (isHomogeneous_hesseCubics _).eval_smul, -hesseCubics_zero,
      -hesseCubics_one]

/-- Off the base locus, `x y z` and `x³ + y³ + z³` do not both vanish, so `pencilVector` is
nonzero. -/
theorem pencilVector_ne_zero {v : Fin 3 → ℂ} (hv : v ≠ 0)
    (hp : Projectivization.mk ℂ v hv ∉ baseLocus) : pencilVector v ≠ 0 := by
  intro h
  refine hp ((mk_mem_baseLocus_iff hv).2 ⟨?_, ?_⟩)
  · rw [← neg_eq_zero, ← pencilVector_one]; exact congrFun h 1
  · rw [← pencilVector_zero]; exact congrFun h 0

/-- The member of the Hesse pencil through a point `p` of `ℂℙ²` off the base locus: the point
`[x y z : -(x³ + y³ + z³)]` of `ℂℙ¹`, evaluated at the chosen representative of `p`. By
`pencilVector_smul`, any representative gives the same point (`pencilMember_mk`). -/
noncomputable def pencilMember (p : ℙ ℂ (Fin 3 → ℂ)) (hp : p ∉ baseLocus) : ℙ ℂ (Fin 2 → ℂ) :=
  Projectivization.mk ℂ (pencilVector p.rep)
    (pencilVector_ne_zero p.rep_ne_zero (by rwa [p.mk_rep]))

theorem pencilMember_def (p : ℙ ℂ (Fin 3 → ℂ)) (hp : p ∉ baseLocus) :
    pencilMember p hp = Projectivization.mk ℂ (pencilVector p.rep)
      (pencilVector_ne_zero p.rep_ne_zero (by rwa [p.mk_rep])) :=
  (rfl)

/-- The member of the Hesse pencil through `[v]` is `[x y z : -(x³ + y³ + z³)]` evaluated at any
nonzero representative `v`. -/
theorem pencilMember_mk {v : Fin 3 → ℂ} (hv : v ≠ 0)
    (hp : Projectivization.mk ℂ v hv ∉ baseLocus) :
    pencilMember _ hp = Projectivization.mk ℂ (pencilVector v) (pencilVector_ne_zero hv hp) := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v hv
  rw [pencilMember_def]
  refine (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2 ⟨(a : ℂ) ^ 3, ?_⟩
  rw [← ha, Units.smul_def, pencilVector_smul]

/-- Away from the base locus, the fibre of the projection of the rational elliptic surface to
`ℂℙ²` is the single point given by the member of the pencil through it. -/
theorem mk_mem_iff_eq_pencilMember {p : ℙ ℂ (Fin 3 → ℂ)} (hp : p ∉ baseLocus)
    {q : ℙ ℂ (Fin 2 → ℂ)} : (p, q) ∈ rationalEllipticSurface ↔ q = pencilMember p hp := by
  have hfg' : p.rep 0 ^ 3 + p.rep 1 ^ 3 + p.rep 2 ^ 3 ≠ 0 ∨ p.rep 0 * p.rep 1 * p.rep 2 ≠ 0 := by
    by_contra! h
    exact hp (mem_baseLocus_iff.2 h)
  rw [mem_rationalEllipticSurface_iff, ← q.mk_rep, pencilMember_def,
    Projectivization.mk_eq_mk_iff', Projectivization.mk_rep]
  simp only [eval_hessePencil, Sum.elim_inl, Sum.elim_inr]
  constructor
  · intro h
    rcases hfg' with hf | hg
    · refine ⟨-q.rep 1 / (p.rep 0 ^ 3 + p.rep 1 ^ 3 + p.rep 2 ^ 3), funext fun k ↦ ?_⟩
      fin_cases k
      · simp only [Fin.zero_eta, pencilVector_zero, smul_eq_mul, Pi.smul_apply]
        rw [div_mul_eq_mul_div, div_eq_iff hf]
        linear_combination -h
      · simp only [Fin.mk_one, pencilVector_one, smul_eq_mul, Pi.smul_apply]
        rw [div_mul_eq_mul_div, div_eq_iff hf]
        ring
    · refine ⟨q.rep 0 / (p.rep 0 * p.rep 1 * p.rep 2), funext fun k ↦ ?_⟩
      fin_cases k
      · simp only [Fin.zero_eta, pencilVector_zero, smul_eq_mul, Pi.smul_apply]
        rw [div_mul_eq_mul_div, div_eq_iff hg]
      · simp only [Fin.mk_one, pencilVector_one, smul_eq_mul, Pi.smul_apply]
        rw [div_mul_eq_mul_div, div_eq_iff hg]
        linear_combination -h
  · rintro ⟨a, ha⟩
    rw [← congrFun ha 0, ← congrFun ha 1]
    simp only [Pi.smul_apply, pencilVector_zero, pencilVector_one, smul_eq_mul]
    ring

/-- The part of the rational elliptic surface over the complement of the base locus. -/
noncomputable def complBaseLocus : Set rationalEllipticSurface :=
  (fun x : rationalEllipticSurface ↦ (x : ℙ ℂ (Fin 3 → ℂ) × ℙ ℂ (Fin 2 → ℂ)).1) ⁻¹' baseLocusᶜ

theorem mem_complBaseLocus_iff {x : rationalEllipticSurface} :
    x ∈ complBaseLocus ↔ (x : ℙ ℂ (Fin 3 → ℂ) × ℙ ℂ (Fin 2 → ℂ)).1 ∉ baseLocus :=
  Iff.rfl

/-- The part of the rational elliptic surface over the complement of the base locus is open. -/
theorem isOpen_complBaseLocus : IsOpen complBaseLocus :=
  finite_baseLocus.isClosed.isOpen_compl.preimage (continuous_fst.comp continuous_subtypeVal)

/-- The projection to `ℂℙ²`, from the part of the rational elliptic surface over the complement
of the base locus onto that complement, as an equivalence. Its inverse sends `p` to
`(p, pencilMember p _)`. -/
noncomputable def complBaseLocusEquiv : complBaseLocus ≃ (baseLocusᶜ : Set (ℙ ℂ (Fin 3 → ℂ))) where
  toFun := baseLocusᶜ.restrictPreimage _
  invFun p := ⟨⟨(p, pencilMember p p.property), (mk_mem_iff_eq_pencilMember p.property).2 rfl⟩,
    p.property⟩
  left_inv := by
    rintro ⟨⟨⟨p, q⟩, hx⟩, hp⟩
    have hq := ((mk_mem_iff_eq_pencilMember hp).1 hx).symm
    exact Subtype.ext (Subtype.ext (Prod.ext rfl hq))
  right_inv _ := rfl

/-- The projection of the rational elliptic surface to `ℂℙ²` restricts to a homeomorphism from the
part over the complement of the base locus onto that complement. It is a continuous bijection,
and a closed map because the surface is compact. -/
noncomputable def complBaseLocusHomeomorph :
    complBaseLocus ≃ₜ (baseLocusᶜ : Set (ℙ ℂ (Fin 3 → ℂ))) :=
  complBaseLocusEquiv.toHomeomorphOfContinuousClosed
    contMDiff_fst.continuous.restrictPreimage
    (IsClosedMap.restrictPreimage contMDiff_fst.continuous.isClosedMap _)

@[simp]
theorem coe_complBaseLocusHomeomorph_apply (x : complBaseLocus) :
    (complBaseLocusHomeomorph x : ℙ ℂ (Fin 3 → ℂ)) =
      ((x : rationalEllipticSurface) : ℙ ℂ (Fin 3 → ℂ) × ℙ ℂ (Fin 2 → ℂ)).1 :=
  (rfl)

@[simp]
theorem coe_coe_complBaseLocusHomeomorph_symm_apply (p : (baseLocusᶜ : Set (ℙ ℂ (Fin 3 → ℂ)))) :
    ((complBaseLocusHomeomorph.symm p : rationalEllipticSurface) :
      ℙ ℂ (Fin 3 → ℂ) × ℙ ℂ (Fin 2 → ℂ)) = ((p : ℙ ℂ (Fin 3 → ℂ)), pencilMember p p.property) :=
  (rfl)

/-- The part of the rational elliptic surface over the complement of the base locus of the pencil
is simply connected: it is homeomorphic to `ℂℙ²` minus finitely many points, and deleting
finitely many points from the simply connected four-manifold `ℂℙ²` keeps it simply connected. -/
instance simplyConnectedSpace_complBaseLocus : SimplyConnectedSpace complBaseLocus := by
  have h : 2 < Module.rank ℝ (Fin 2 → ℂ) := by
    rw [← Module.finrank_eq_rank, Module.finrank_pi_fintype]
    simp only [Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul]
    norm_num
  have := (simplyConnectedSpace_compl_iff_of_finite (X := ℙ ℂ (Fin 3 → ℂ)) h
    finite_baseLocus).2 inferInstance
  exact complBaseLocusHomeomorph.toHomotopyEquiv.simplyConnectedSpace_iff.2 this

end rationalEllipticSurface

end SymplecticGeometry

end
