/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import SymplecticGeometry.Geometry.Manifold.Projectivization.FubiniStudy.Basic
public import SymplecticGeometry.Geometry.Manifold.Projectivization.Hypersurface.Basic
public import SymplecticGeometry.Geometry.Manifold.Projectivization.ProdZeroLocus.Manifold
public import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.RestrictScalars
public import SymplecticGeometry.Geometry.Symplectic.Blowup.PencilIncidence
public import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.HolomorphicEmbedding
public import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.Submanifold
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Basic
public import TauCeti.Geometry.Symplectic.Lagrangian.SymplecticTangent
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Prod
public import TauCeti.LinearAlgebra.Projectivization.ZeroLocus
public import TauCeti.RingTheory.MvPolynomial.Jacobian.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.LocalAtTarget
import TauCeti.RingTheory.MvPolynomial.Symmetric.PowerSum.Basic
import SymplecticGeometry.AlgebraicTopology.FundamentalGroup.ComplFinite
import SymplecticGeometry.Geometry.Manifold.Projectivization.FubiniStudy.Kahler
import SymplecticGeometry.Geometry.Symplectic.Blowup.SimplyConnected
import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.Prod
import SymplecticGeometry.RingTheory.MvPolynomial.WeightedHomogeneous
import SymplecticGeometry.Topology.ComplexProjectiveSpace.SimplyConnected

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

The section on the underlying real submanifold regards the surface as a real submanifold of
`ℂℙ² × ℂℙ¹`, the form in which the results on complex submanifolds of almost complex manifolds
take it (`TauCeti.SmoothAlmostComplexStructure.restrict`,
`TauCeti.SmoothTwoForm.Tames.isSymplectic_mpullback`). The analytic embedding is a smooth
embedding over `ℝ` (`TauCeti.SmoothEmbedding.restrictScalarsProd`), whose tangent images are
invariant under the product of the complex structures of the two factors, and the structure that
this product restricts to on the surface is the surface's own complex structure, as for every
holomorphic embedding into a product
(`TauCeti.SmoothEmbedding.mapsTo_prod_ofComplexManifold_tangentRange_restrictScalarsProd`,
`TauCeti.SmoothEmbedding.restrict_prod_ofComplexManifold`).

The symplectic form of the surface is the pull-back along this real embedding of the product
`ω_FS ⊕ ω_FS` of the Fubini–Study forms of `ℂℙ²` and `ℂℙ¹` (`TauCeti.SmoothTwoForm.prod`). The
product form is symplectic (`TauCeti.SmoothTwoForm.IsSymplectic.prod`) and tames the product of
the complex structures (`TauCeti.SmoothAlmostComplexStructure.tames_prod`), since each
Fubini–Study form is compatible with the complex structure of its factor
(`SymplecticGeometry.compatible_fubiniStudyForm`). A symplectic form that tames an almost complex
structure pulls back to a symplectic form on a submanifold with invariant tangent spaces
(`TauCeti.SmoothTwoForm.Tames.isSymplectic_mpullback`). No Kähler condition is used.

Over the point `[1 : 0]` of `ℂℙ¹` the Hesse pencil is `x³ + y³ + z³`, so the fibre there is the
Fermat cubic `SymplecticGeometry.SmoothProjectiveHypersurface.fermat 1 3`, and `x ↦ (x, [1 : 0])`
embeds it in the surface. It is an analytic embedding, since its composite with the inclusion of
the surface is the product of the inclusion of the cubic with a constant
(`Manifold.IsSmoothEmbedding.isImmersion_of_isImmersion_comp`). Its real form
(`TauCeti.SmoothEmbedding.restrictScalars`) is a smooth embedding over `ℝ` whose tangent images
are invariant under the complex structure of the surface
(`TauCeti.SmoothEmbedding.mapsTo_ofComplexManifold_tangentRange_restrictScalars`). The symplectic
form of the surface tames that structure (`TauCeti.SmoothTwoForm.Tames.restrict`), so the cubic
is a symplectic submanifold (`TauCeti.SmoothTwoForm.Tames.isSymplecticSubmanifoldEmbedding`).

The variables are indexed by `Fin 3 ⊕ Fin 2`: `Sum.inl 0`, `Sum.inl 1`, `Sum.inl 2` are the
homogeneous coordinates `x, y, z` of the plane, and `Sum.inr 0`, `Sum.inr 1` are the homogeneous
coordinates `s, t` of the line. A point of the cone `K³ × K²` is written `Sum.elim v w`.

## Main declarations

* `SymplecticGeometry.hesseCubics R`: the two cubics `x³ + y³ + z³` and `x y z` of the plane
  that span the pencil, both homogeneous of degree three
  (`SymplecticGeometry.isHomogeneous_hesseCubics`). The first is Mathlib's power sum
  `psum (Fin 3) R 3`, the polynomial of the Fermat cubic (`SymplecticGeometry.hesseCubics_zero`);
  `SymplecticGeometry.hesseCubics_zero'` writes it out as `X 0 ^ 3 + X 1 ^ 3 + X 2 ^ 3`.
* `SymplecticGeometry.hessePencil R`: the polynomial `s (x³ + y³ + z³) + t x y z`, defined as
  the combination with coefficients `s, t` of the two cubics `hesseCubics R`, renamed into the
  plane coordinates `Sum.inl`.
* `SymplecticGeometry.eval_hessePencil` and the lemmas `pderiv_inl_zero_hessePencil`, …,
  `pderiv_inr_one_hessePencil`: its evaluation and its five partial derivatives.
* `SymplecticGeometry.isWeightedHomogeneous_hessePencil_inl` and
  `SymplecticGeometry.isWeightedHomogeneous_hessePencil_inr`: it is bihomogeneous of bidegree
  `(3, 1)`. Both are cases of `SymplecticGeometry.isWeightedHomogeneous_hessePencil`, which
  derives weighted homogeneity of the pencil from that of the cubics, since renaming variables
  keeps weighted homogeneity (`MvPolynomial.IsWeightedHomogeneous.rename`).
* `SymplecticGeometry.sum_mul_eval_pderiv_inl_hessePencil` and
  `SymplecticGeometry.sum_mul_eval_pderiv_inr_hessePencil`: the two Euler relations.
* `SymplecticGeometry.eval_pderiv_inl_hessePencil`: a partial derivative of the pencil in a
  plane coordinate is `s ∂f + t ∂g` for the two cubics `f`, `g` that span it.
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
  `SymplecticGeometry.rationalEllipticSurface.restrict_prod_ofComplexManifold`: the structure
  that the product of the complex structures of `ℂℙ²` and `ℂℙ¹` restricts to along it is the
  complex structure of the surface.
* `SymplecticGeometry.rationalEllipticSurface.symplecticForm`: the pull-back of the product of
  the Fubini–Study forms, and
  `SymplecticGeometry.rationalEllipticSurface.isSymplectic_symplecticForm`: it is symplectic.
* `SymplecticGeometry.rationalEllipticSurface.analyticFibreEmbedding`: the Fermat cubic as the
  fibre over `[1 : 0]`, an analytic embedding for the models `𝓘(ℂ, Fin 1 → ℂ)` and
  `𝓘(ℂ, Fin 2 → ℂ)`, and `SymplecticGeometry.rationalEllipticSurface.fibreEmbedding`: its real
  form, a smooth embedding over `ℝ` for the models `𝓘(ℝ, Fin 1 → ℂ)` and `𝓘(ℝ, Fin 2 → ℂ)`,
  with `coe_fibreEmbedding_apply` and `range_fibreEmbedding` (its image is the fibre of the
  projection to `ℂℙ¹`).
* `SymplecticGeometry.rationalEllipticSurface.hasSymplecticTangentImages_fibreEmbedding`: its
  tangent images are symplectic, and
  `SymplecticGeometry.rationalEllipticSurface.isSymplectic_mpullback_fibreEmbedding`: the form
  pulls back to a symplectic form on the cubic.
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
* `SymplecticGeometry.rationalEllipticSurface.exists_openPartialHomeomorph_of_mem_baseLocus`:
  coordinates at a base point `p`. Inside any neighbourhood of `p` there is an open partial
  homeomorphism `φ` of `ℂℙ²` onto a round ball of `ℂ²` with `φ p = 0`, whose source contains no
  other base point, and over whose source the surface is the incidence set
  `{(x, [w]) | w₀ φ(x)₀ + w₁ φ(x)₁ = 0}`. In the standard affine chart `i` at `p`, `φ` reads `z ↦`
  the two cubics dehomogenized at coordinate `i` (Tau Ceti's `TauCeti.dehomogenize`) and
  evaluated at `z`. Their Jacobian matrix there is the cone Jacobian with column `i` deleted
  (`TauCeti.jacobiMatrixAt_dehomogenize`), whose determinant is nonzero at `p` by
  `exists_eval_pderiv_hessePencil_ne_zero_of_ne_zero`. So the cone Jacobian is surjective at `p`,
  and Tau Ceti's slice chart `TauCeti.complexProjectiveZeroLocusSliceChart` of the base locus,
  whose slice factor `Fin 0 → ℂ` is trivial, gives `φ` near `p`; cutting its target down to a
  small ball gives the rest.
* `SymplecticGeometry.rationalEllipticSurface.exists_homeomorph_openNbhd_of_mem_baseLocus`: the
  neighbourhoods of the exceptional curves. For a base point `p` and a neighbourhood `U` of `p`,
  the part `N` of the surface over the source of such coordinates is an open set containing
  `{p} × ℂℙ¹`, lying over `U` and over no other base point, and homeomorphic to the neighbourhood
  `BlowupModel.openNbhd 1 r` of the exceptional divisor of the model blowup, the curve going onto
  the divisor. The homeomorphism is `(x, ℓ) ↦ (φ x, ℓ)` onto the incidence set
  `BlowupModel.pencilNbhd r`, followed by `BlowupModel.pencilNbhdHomeomorph r`.
* `SymplecticGeometry.rationalEllipticSurface.exists_isSimplyConnected_of_mem_baseLocus`: such an
  `N` is simply connected and stays path connected once the curve is removed
  (`BlowupModel.isSimplyConnected_openNbhd`,
  `BlowupModel.isPathConnected_openNbhd_sdiff_exceptionalDivisor`).

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §7.2.
* [R. E. Gompf, *A new construction of symplectic manifolds*][Gompf1995].
-/

public section

open MvPolynomial Set TauCeti Topology
open scoped ContDiff Manifold LinearAlgebra.Projectivization

namespace SymplecticGeometry

variable (R : Type*) [CommSemiring R]

/-- The two plane cubics `x³ + y³ + z³` and `x y z` that span the Hesse pencil, in the variables
`x, y, z = 0, 1, 2`. The first is Mathlib's power sum `psum (Fin 3) R 3`, the polynomial of the
Fermat cubic `SmoothProjectiveHypersurface.fermat 1 3`. -/
noncomputable def hesseCubics : Fin 2 → MvPolynomial (Fin 3) R :=
  ![psum (Fin 3) R 3, X 0 * X 1 * X 2]

theorem hesseCubics_zero : hesseCubics R 0 = psum (Fin 3) R 3 :=
  (rfl)

/-- The first cubic of the Hesse pencil written out: `x³ + y³ + z³`. -/
theorem hesseCubics_zero' : hesseCubics R 0 = X 0 ^ 3 + X 1 ^ 3 + X 2 ^ 3 := by
  simp [hesseCubics_zero, psum, Fin.sum_univ_three]

theorem hesseCubics_one : hesseCubics R 1 = X 0 * X 1 * X 2 :=
  (rfl)

/-- The equation of the Hesse pencil, `s (x³ + y³ + z³) + t x y z`, in the variables
`x, y, z = Sum.inl 0, Sum.inl 1, Sum.inl 2` and `s, t = Sum.inr 0, Sum.inr 1`: the combination
with coefficients `s, t` of the two cubics `hesseCubics R`. -/
noncomputable def hessePencil : MvPolynomial (Fin 3 ⊕ Fin 2) R :=
  X (.inr 0) * rename Sum.inl (hesseCubics R 0) + X (.inr 1) * rename Sum.inl (hesseCubics R 1)

theorem hessePencil_def : hessePencil R =
    X (.inr 0) * rename Sum.inl (hesseCubics R 0) +
      X (.inr 1) * rename Sum.inl (hesseCubics R 1) :=
  (rfl)

variable {R}

/-- The value of the first cubic `x³ + y³ + z³` at `v`. -/
@[simp]
theorem eval_hesseCubics_zero (v : Fin 3 → R) :
    eval v (hesseCubics R 0) = v 0 ^ 3 + v 1 ^ 3 + v 2 ^ 3 := by
  simp [hesseCubics_zero']

/-- The value of the second cubic `x y z` at `v`. -/
@[simp]
theorem eval_hesseCubics_one (v : Fin 3 → R) : eval v (hesseCubics R 1) = v 0 * v 1 * v 2 := by
  simp [hesseCubics_one]

/-- Both cubics spanning the Hesse pencil are homogeneous of degree three. -/
theorem isHomogeneous_hesseCubics (i : Fin 2) : (hesseCubics R i).IsHomogeneous 3 := by
  fin_cases i
  · exact TauCeti.isHomogeneous_psum R 3
  · simp only [Fin.mk_one, hesseCubics_one]
    exact ((isHomogeneous_X _ _).mul (isHomogeneous_X _ _)).mul (isHomogeneous_X _ _)

@[simp]
theorem eval_hessePencil (p : Fin 3 ⊕ Fin 2 → R) :
    eval p (hessePencil R) = p (.inr 0) * (p (.inl 0) ^ 3 + p (.inl 1) ^ 3 + p (.inl 2) ^ 3) +
      p (.inr 1) * (p (.inl 0) * p (.inl 1) * p (.inl 2)) := by
  simp [hessePencil_def, eval_rename, Function.comp_def]

@[simp]
theorem pderiv_inl_zero_hessePencil :
    pderiv (.inl 0) (hessePencil R) =
      3 * X (.inr 0) * X (.inl 0) ^ 2 + X (.inr 1) * (X (.inl 1) * X (.inl 2)) := by
  simp [hessePencil_def, hesseCubics_zero', hesseCubics_one, pderiv_X]
  ring

@[simp]
theorem pderiv_inl_one_hessePencil :
    pderiv (.inl 1) (hessePencil R) =
      3 * X (.inr 0) * X (.inl 1) ^ 2 + X (.inr 1) * (X (.inl 0) * X (.inl 2)) := by
  simp [hessePencil_def, hesseCubics_zero', hesseCubics_one, pderiv_X]
  ring

@[simp]
theorem pderiv_inl_two_hessePencil :
    pderiv (.inl 2) (hessePencil R) =
      3 * X (.inr 0) * X (.inl 2) ^ 2 + X (.inr 1) * (X (.inl 0) * X (.inl 1)) := by
  simp [hessePencil_def, hesseCubics_zero', hesseCubics_one, pderiv_X]
  ring

@[simp]
theorem pderiv_inr_zero_hessePencil :
    pderiv (.inr 0) (hessePencil R) = X (.inl 0) ^ 3 + X (.inl 1) ^ 3 + X (.inl 2) ^ 3 := by
  simp [hessePencil_def, hesseCubics_zero', hesseCubics_one, pderiv_X]

@[simp]
theorem pderiv_inr_one_hessePencil :
    pderiv (.inr 1) (hessePencil R) = X (.inl 0) * X (.inl 1) * X (.inl 2) := by
  simp [hessePencil_def, hesseCubics_zero', hesseCubics_one, pderiv_X]

/-- A partial derivative of the Hesse pencil in a plane coordinate is the same combination of the
partial derivatives of the two cubics `hesseCubics R` as the pencil is of the cubics:
`∂ₗ(s f + t g) = s ∂ₗf + t ∂ₗg`. -/
theorem eval_pderiv_inl_hessePencil (v : Fin 3 → R) (w : Fin 2 → R) (l : Fin 3) :
    eval (Sum.elim v w) (pderiv (.inl l) (hessePencil R)) =
      w 0 * eval v (pderiv l (hesseCubics R 0)) + w 1 * eval v (pderiv l (hesseCubics R 1)) := by
  fin_cases l <;> simp [hesseCubics_zero', hesseCubics_one, pderiv_X] <;> ring

/-- The Hesse pencil is weighted homogeneous of degree `n + m` for weights `w` that give each
line coordinate `s, t` the weight `n` and for which both cubics are weighted homogeneous of degree
`m` in the plane coordinates. -/
theorem isWeightedHomogeneous_hessePencil {w : Fin 3 ⊕ Fin 2 → ℕ} {m n : ℕ}
    (hc : ∀ i, (hesseCubics R i).IsWeightedHomogeneous (w ∘ Sum.inl) m)
    (hw : ∀ i, w (.inr i) = n) : (hessePencil R).IsWeightedHomogeneous w (n + m) := by
  have h (i : Fin 2) : (X (Sum.inr i) * rename Sum.inl (hesseCubics R i)).IsWeightedHomogeneous
      w (n + m) := hw i ▸ (isWeightedHomogeneous_X R w (.inr i)).mul (hc i).rename
  exact hessePencil_def R ▸ (h 0).add (h 1)

/-- The Hesse pencil is homogeneous of degree `3` in the coordinates `x, y, z` of the plane. -/
theorem isWeightedHomogeneous_hessePencil_inl :
    (hessePencil R).IsWeightedHomogeneous (Sum.elim (1 : Fin 3 → ℕ) 0) 3 :=
  isWeightedHomogeneous_hessePencil (n := 0) (m := 3)
    (fun i ↦ by rw [Sum.elim_comp_inl]; exact isHomogeneous_hesseCubics i) (fun _ ↦ rfl)

/-- The Hesse pencil is homogeneous of degree `1` in the coordinates `s, t` of the line. -/
theorem isWeightedHomogeneous_hessePencil_inr :
    (hessePencil R).IsWeightedHomogeneous (Sum.elim 0 (1 : Fin 2 → ℕ)) 1 :=
  isWeightedHomogeneous_hessePencil (n := 1) (m := 0)
    (fun _ ↦ by rw [Sum.elim_comp_inl]; exact isWeightedHomogeneous_zero_weight _) (fun _ ↦ rfl)

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
  embedding.restrictScalarsProd ℝ le_top (by simp)

theorem realEmbedding_def : realEmbedding = embedding.restrictScalarsProd ℝ le_top (by simp) :=
  (rfl)

/-- The real embedding of the rational elliptic surface is the inclusion. -/
@[simp]
theorem coe_realEmbedding : ⇑realEmbedding = Subtype.val := by
  rw [realEmbedding_def, SmoothEmbedding.coe_restrictScalarsProd, coe_embedding]

/-- The almost complex structure that the product of the complex structures of `ℂℙ²` and `ℂℙ¹`
restricts to on the rational elliptic surface is the surface's own complex structure. -/
theorem restrict_prod_ofComplexManifold {hn : (∞ : ℕ∞ω) ≠ 0} :
    ((SmoothAlmostComplexStructure.ofComplexManifold (Fin 2 → ℂ) (ℙ ℂ (Fin 3 → ℂ))).prod
        (SmoothAlmostComplexStructure.ofComplexManifold (Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ)))).restrict
          realEmbedding (hn := hn) (realEmbedding_def ▸
            embedding.mapsTo_prod_ofComplexManifold_tangentRange_restrictScalarsProd le_top
              (by simp) hn) =
      SmoothAlmostComplexStructure.ofComplexManifold (Fin 2 → ℂ) rationalEllipticSurface := by
  simp only [realEmbedding_def]
  exact embedding.restrict_prod_ofComplexManifold le_top

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
  rw [symplecticForm_def, realEmbedding_def]
  exact (SmoothAlmostComplexStructure.tames_prod (compatible_fubiniStudyForm (n := 2)).tames
    (compatible_fubiniStudyForm (n := 1)).tames).isSymplectic_mpullback
      (hn := by simp)
      (embedding.mapsTo_prod_ofComplexManifold_tangentRange_restrictScalarsProd le_top (by simp) _)
      ((isSymplectic_fubiniStudyForm 2).prod (isSymplectic_fubiniStudyForm 1))

/-! ### The fibre over `[1 : 0]` -/

open SmoothProjectiveHypersurface

/-- A point `L` of `ℂℙ²`, paired with the point `[1 : 0]` of `ℂℙ¹`, lies on the rational
elliptic surface exactly when it lies on the Fermat cubic `x³ + y³ + z³ = 0`: over `[1 : 0]` the
Hesse pencil is `x³ + y³ + z³`. -/
theorem mk_mem_iff_mem_fermat {L : ℙ ℂ (Fin 3 → ℂ)} :
    (L, Projectivization.mk ℂ ![(1 : ℂ), 0] (by simp)) ∈ rationalEllipticSurface ↔
      L ∈ (fermat 1 3).carrier := by
  conv_lhs => rw [← L.mk_rep]
  rw [mk_mem_rationalEllipticSurface_iff, mem_carrier_iff, fermat_poly]
  simp [Fin.sum_univ_three]

/-- The inclusion of the Fermat cubic as the fibre over `[1 : 0]` is an analytic embedding. -/
private theorem isSmoothEmbedding_fibre :
    Manifold.IsSmoothEmbedding 𝓘(ℂ, Fin 1 → ℂ) 𝓘(ℂ, Fin 2 → ℂ) ω
      (fun x : fermat 1 3 ↦ (⟨(x, Projectivization.mk ℂ ![(1 : ℂ), 0] (by simp)),
        mk_mem_iff_mem_fermat.2 x.property⟩ : rationalEllipticSurface)) := by
  have hc : Manifold.IsImmersion 𝓘(ℂ, Fin 1 → ℂ) (𝓘(ℂ, Fin 2 → ℂ).prod 𝓘(ℂ, Fin 1 → ℂ)) ω
      (fun x : fermat 1 3 ↦ ((x : ℙ ℂ (Fin 3 → ℂ)),
        Projectivization.mk ℂ ![(1 : ℂ), 0] (by simp))) := by
    simpa using (fermat 1 3).embedding.isImmersion.prodMk contMDiff_const (by simp)
  have hi := embedding.isSmoothEmbedding.isImmersion_of_isImmersion_comp (by simp)
    (f := fun x : fermat 1 3 ↦ (⟨(x, Projectivization.mk ℂ ![(1 : ℂ), 0] (by simp)),
      mk_mem_iff_mem_fermat.2 x.property⟩ : rationalEllipticSurface)) (by simpa [Function.comp_def])
  refine ⟨hi, (hi.contMDiff.continuous.isClosedEmbedding fun x y h ↦ ?_).isEmbedding⟩
  exact Subtype.ext congr(($h : ℙ ℂ (Fin 3 → ℂ) × ℙ ℂ (Fin 2 → ℂ)).1)

/-- The inclusion `x ↦ (x, [1 : 0])` of the Fermat cubic `SmoothProjectiveHypersurface.fermat 1 3`
into the rational elliptic surface, as the fibre over `[1 : 0] ∈ ℂℙ¹`, as an analytic embedding
of complex manifolds. -/
noncomputable def analyticFibreEmbedding :
    SmoothEmbedding 𝓘(ℂ, Fin 1 → ℂ) 𝓘(ℂ, Fin 2 → ℂ) ω (fermat 1 3) rationalEllipticSurface :=
  .ofIsSmoothEmbedding _ isSmoothEmbedding_fibre

/-- The analytic fibre embedding is the map `x ↦ (x, [1 : 0])` into the rational elliptic
surface. -/
theorem coe_analyticFibreEmbedding :
    ⇑analyticFibreEmbedding = fun x : fermat 1 3 ↦
      (⟨(x, Projectivization.mk ℂ ![(1 : ℂ), 0] (by simp)), mk_mem_iff_mem_fermat.2 x.property⟩ :
        rationalEllipticSurface) :=
  SmoothEmbedding.coe_ofIsSmoothEmbedding _ _

/-- The Fermat cubic `SmoothProjectiveHypersurface.fermat 1 3` as the fibre of the rational
elliptic surface over `[1 : 0] ∈ ℂℙ¹`: the inclusion `x ↦ (x, [1 : 0])`, as a smooth embedding
of the underlying real manifolds, the real form of `analyticFibreEmbedding`. -/
noncomputable def fibreEmbedding :
    SmoothEmbedding 𝓘(ℝ, Fin 1 → ℂ) 𝓘(ℝ, Fin 2 → ℂ) ∞ (fermat 1 3) rationalEllipticSurface :=
  analyticFibreEmbedding.restrictScalars ℝ le_top (by simp)

theorem fibreEmbedding_def :
    fibreEmbedding = analyticFibreEmbedding.restrictScalars ℝ le_top (by simp) :=
  (rfl)

/-- The fibre embedding is the map `x ↦ (x, [1 : 0])` into the rational elliptic surface. -/
theorem coe_fibreEmbedding :
    ⇑fibreEmbedding = fun x : fermat 1 3 ↦
      (⟨(x, Projectivization.mk ℂ ![(1 : ℂ), 0] (by simp)), mk_mem_iff_mem_fermat.2 x.property⟩ :
        rationalEllipticSurface) := by
  rw [fibreEmbedding_def, SmoothEmbedding.coe_restrictScalars, coe_analyticFibreEmbedding]

/-- The fibre embedding sends a point `x` of the Fermat cubic to `(x, [1 : 0])`. -/
@[simp]
theorem coe_fibreEmbedding_apply (x : fermat 1 3) :
    (fibreEmbedding x : ℙ ℂ (Fin 3 → ℂ) × ℙ ℂ (Fin 2 → ℂ)) =
      ((x : ℙ ℂ (Fin 3 → ℂ)), Projectivization.mk ℂ ![(1 : ℂ), 0] (by simp)) :=
  congrArg Subtype.val (congrFun coe_fibreEmbedding x)

/-- The image of the fibre embedding is the fibre of the projection to `ℂℙ¹` over `[1 : 0]`. -/
theorem range_fibreEmbedding :
    range fibreEmbedding = {p : rationalEllipticSurface |
      (p : ℙ ℂ (Fin 3 → ℂ) × ℙ ℂ (Fin 2 → ℂ)).2 =
        Projectivization.mk ℂ ![(1 : ℂ), 0] (by simp)} := by
  refine Set.ext fun ⟨⟨L, w⟩, hp⟩ ↦ ⟨?_, fun hw ↦ ?_⟩
  · rintro ⟨x, hx⟩
    rw [← hx, mem_ofPred_eq, coe_fibreEmbedding_apply]
  · simp only [mem_ofPred_eq] at hw
    subst hw
    exact ⟨⟨L, mk_mem_iff_mem_fermat.1 hp⟩, Subtype.ext (coe_fibreEmbedding_apply _)⟩

/-- The fibre embedding has symplectic tangent images for the symplectic form of the rational
elliptic surface: the Fermat cubic over `[1 : 0]` is a symplectic submanifold. -/
theorem hasSymplecticTangentImages_fibreEmbedding :
    isSymplectic_symplecticForm.isNondegenerate.HasSymplecticTangentImages 𝓘(ℝ, Fin 1 → ℂ)
      fibreEmbedding :=
  (restrict_prod_ofComplexManifold ▸
    (SmoothAlmostComplexStructure.tames_prod (compatible_fubiniStudyForm (n := 2)).tames
      (compatible_fubiniStudyForm (n := 1)).tames).restrict (f := realEmbedding) (hn := by simp)
        (realEmbedding_def ▸
          embedding.mapsTo_prod_ofComplexManifold_tangentRange_restrictScalarsProd le_top
            (by simp) _)).isSymplecticSubmanifoldEmbedding
          (fibreEmbedding_def ▸
            SmoothEmbedding.mapsTo_ofComplexManifold_tangentRange_restrictScalars
              analyticFibreEmbedding le_top (by simp) (by simp))
    |>.hasSymplecticTangentImages

/-- The symplectic form of the rational elliptic surface pulls back along the fibre embedding to a
symplectic form on the Fermat cubic. -/
theorem isSymplectic_mpullback_fibreEmbedding :
    SmoothTwoForm.IsSymplectic
      (SmoothForm.mpullback fibreEmbedding fibreEmbedding.contMDiff symplecticForm) :=
  hasSymplecticTangentImages_fibreEmbedding.isSymplectic_mpullback isSymplectic_symplecticForm _
    (fibreEmbedding.isImmersion.mfderiv_injective (by simp))

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
  rw [baseLocus_def, mem_complexProjectiveZeroLocus_iff_eval_rep isHomogeneous_hesseCubics,
    Fin.forall_fin_two]
  simp

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
    simp [pencilVector, (isHomogeneous_hesseCubics _).eval_smul, -eval_hesseCubics_zero,
      -eval_hesseCubics_one]

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

/-! ### Coordinates at a base point of the pencil -/

/-- At a base point, the two cubics have independent differentials in the coordinates of the
standard chart `i`: the Jacobian matrix of `hesseCubics ℂ` with column `i` deleted is invertible.
A vanishing combination `s ∂f + t ∂g` of its rows would make every partial derivative of the
member `s f + t g` of the pencil vanish in the chart, against
`exists_eval_pderiv_hessePencil_ne_zero_of_ne_zero`. -/
private theorem det_jacobiMatrixAt_hesseCubics_submatrix_ne_zero {i : Fin 3} {z : Fin 2 → ℂ}
    (hz : (Projectivization.affineChart (K := ℂ) i).symm z ∈ baseLocus) :
    ((jacobiMatrixAt (hesseCubics ℂ) (i.insertNth 1 z)).submatrix id i.succAbove).det ≠ 0 := by
  classical
  rw [Projectivization.affineChart_symm_apply, mk_mem_baseLocus_iff] at hz
  set V := Fin.insertNth (α := fun _ ↦ ℂ) i 1 z
  rw [Ne, ← Matrix.exists_vecMul_eq_zero_iff]
  rintro ⟨w, hw, hM⟩
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hw
  have hV : V i ≠ 0 := by simp [V]
  obtain ⟨k, hki, hkj, hk⟩ := exists_eval_pderiv_hessePencil_ne_zero_of_ne_zero (three_ne_zero)
    hV hj (by simp [hz.1, hz.2])
  rcases k with l | l
  · obtain ⟨m, rfl⟩ := Fin.exists_succAbove_eq (x := l) (y := i) (by simpa using hki)
    refine hk ?_
    have := congrFun hM m
    simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.submatrix_apply, id,
      jacobiMatrixAt_apply, Pi.zero_apply] at this
    rw [eval_pderiv_inl_hessePencil]
    linear_combination this
  · fin_cases l <;> simp at hk <;> simp_all

/-- Near a base point `p`, the two cubics dehomogenized in a standard chart at `p` form an open
partial homeomorphism to `ℂ²`: Tau Ceti's slice chart
`TauCeti.complexProjectiveZeroLocusSliceChart` of the base locus, whose slice factor is trivial.
It sends `p` to `0`, its zeros are the base points, and over its source the rational elliptic
surface is the incidence set `s u + t v = 0`. -/
private theorem exists_chart_of_mem_baseLocus {p : ℙ ℂ (Fin 3 → ℂ)} (hp : p ∈ baseLocus) :
    ∃ Φ : OpenPartialHomeomorph (ℙ ℂ (Fin 3 → ℂ)) (Fin 2 → ℂ), p ∈ Φ.source ∧ Φ p = 0 ∧
      (∀ x ∈ Φ.source, x ∈ baseLocus ↔ Φ x = 0) ∧
      ∀ x ∈ Φ.source, ∀ (w : Fin 2 → ℂ) (hw : w ≠ 0),
        (x, Projectivization.mk ℂ w hw) ∈ rationalEllipticSurface ↔
          w 0 * Φ x 0 + w 1 * Φ x 1 = 0 := by
  obtain ⟨i, hi⟩ := Projectivization.exists_mem_affineOpen p
  have hsymm {x : ℙ ℂ (Fin 3 → ℂ)} (hx : x ∈ Projectivization.affineOpen i) :
      (Projectivization.affineChart (K := ℂ) i).symm (Projectivization.affineChart i x) = x :=
    (Projectivization.affineChart i).left_inv (by simpa using hx)
  have hL : p ∈ complexProjectiveZeroLocus (hesseCubics ℂ) := baseLocus_def ▸ hp
  have hrank : Function.Surjective (jacobiMatrixAt (hesseCubics ℂ) p.rep).mulVec := by
    rw [← surjective_fderiv_eval_dehomogenize_affineChart_iff i isHomogeneous_hesseCubics hL hi,
      ← ContinuousLinearMap.coe_coe, fderiv_eval_dehomogenize, Matrix.coe_mulVecLin,
      Matrix.mulVec_surjective_iff_isUnit, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    exact det_jacobiMatrixAt_hesseCubics_submatrix_ne_zero (by rwa [hsymm hi])
  have : IsEmpty (Fin (2 - Fintype.card (Fin 2))) := by
    rw [Fintype.card_fin]
    exact Fin.isEmpty'
  set Φ := (complexProjectiveZeroLocusSliceChart isHomogeneous_hesseCubics hL hi
    hrank).transHomeomorph (Homeomorph.uniqueProd _ _)
  have hΦ (x : ℙ ℂ (Fin 3 → ℂ)) :
      Φ x = fun k ↦ eval (Projectivization.affineChart i x) (dehomogenize i (hesseCubics ℂ k)) := by
    simp [Φ, Homeomorph.uniqueProd]
  have hsrc {x : ℙ ℂ (Fin 3 → ℂ)} (hx : x ∈ Φ.source) : x ∈ Projectivization.affineOpen i :=
    complexProjectiveZeroLocusSliceChart_source_subset _ _ _ _ hx
  have hzero {x : ℙ ℂ (Fin 3 → ℂ)} (hx : x ∈ Projectivization.affineOpen i) :
      x ∈ baseLocus ↔ Φ x = 0 := by
    rw [baseLocus_def, mem_complexProjectiveZeroLocus_iff_eval_affineChart isHomogeneous_hesseCubics
      hx, hΦ, _root_.funext_iff]
    simp only [Pi.zero_apply]
  refine ⟨Φ, mem_complexProjectiveZeroLocusSliceChart_source _ _ _ _, (hzero hi).1 hp,
    fun x hx ↦ hzero (hsrc hx), fun x hx w hw ↦ ?_⟩
  conv_lhs => rw [← hsymm (hsrc hx), Projectivization.affineChart_symm_apply,
    mk_mem_rationalEllipticSurface_iff]
  simp only [hΦ, eval_dehomogenize]
  simp

/-- **Coordinates of `E(1)` at a base point of the Hesse pencil.** For a base point `p` and a
neighbourhood `U` of `p` in `ℂℙ²`, there is an open partial homeomorphism `φ` from `ℂℙ²` to `ℂ²`
whose source contains `p` and lies in `U`, whose target is the ball of some radius `r > 0` for the
norm of `ℂ² ≅ ℝ⁴` (`complexToRealEuclidean`), and with `φ p = 0`, such that over its source the
rational elliptic surface is the incidence set `{(x, [w]) | w₀ φ(x)₀ + w₁ φ(x)₁ = 0}` and `p` is
the only base point in its source. Its source is homeomorphic to the ball by
`φ.toHomeomorphSourceTarget`. -/
theorem exists_openPartialHomeomorph_of_mem_baseLocus {p : ℙ ℂ (Fin 3 → ℂ)}
    (hp : p ∈ baseLocus) {U : Set (ℙ ℂ (Fin 3 → ℂ))} (hU : U ∈ 𝓝 p) :
    ∃ (φ : OpenPartialHomeomorph (ℙ ℂ (Fin 3 → ℂ)) (Fin 2 → ℂ)) (r : ℝ), 0 < r ∧
      p ∈ φ.source ∧ φ.source ⊆ U ∧
      φ.target = {z | ‖complexToRealEuclidean (Fin 2) z‖ < r} ∧ φ p = 0 ∧
      (∀ x ∈ φ.source, ∀ (w : Fin 2 → ℂ) (hw : w ≠ 0),
        (x, Projectivization.mk ℂ w hw) ∈ rationalEllipticSurface ↔
          w 0 * φ x 0 + w 1 * φ x 1 = 0) ∧
      φ.source ∩ baseLocus = {p} := by
  obtain ⟨Φ, hpΦ, h0, hzero, hmem⟩ := exists_chart_of_mem_baseLocus hp
  -- A ball `B` around `0 = Φ p` inside the target of `Φ` whose points come from `U`.
  have hN : (complexToRealEuclidean (Fin 2)).symm ⁻¹' (Φ.target ∩ Φ.symm ⁻¹' U) ∈ 𝓝 0 := by
    refine (complexToRealEuclidean (Fin 2)).symm.continuous.continuousAt.preimage_mem_nhds ?_
    rw [map_zero, ← h0]
    refine Filter.inter_mem (Φ.open_target.mem_nhds (Φ.map_source hpΦ)) ?_
    exact (Φ.continuousAt_symm (Φ.map_source hpΦ)).preimage_mem_nhds (by rwa [Φ.left_inv hpΦ])
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hN
  set B := {z : Fin 2 → ℂ | ‖complexToRealEuclidean (Fin 2) z‖ < r}
  have hB : B ⊆ Φ.target ∩ Φ.symm ⁻¹' U := fun z hz ↦ by
    simpa using hball
      (show complexToRealEuclidean (Fin 2) z ∈ Metric.ball 0 r by simpa [B] using hz)
  have hBo : IsOpen B :=
    isOpen_lt (continuous_norm.comp (complexToRealEuclidean (Fin 2)).continuous) continuous_const
  -- `φ` is `Φ` with its target cut down to `B`.
  set φ := (Φ.symm.restrOpen B hBo).symm
  have hφ : ⇑φ = ⇑Φ := by simp [φ]
  have hsrc : φ.source = Φ.source ∩ Φ ⁻¹' B := by simp [φ]
  have hpφ : p ∈ φ.source := by
    rw [hsrc]
    exact ⟨hpΦ, by simp [B, h0, hr]⟩
  refine ⟨φ, r, hr, hpφ, fun x hx ↦ ?_, ?_, hφ ▸ h0, fun x hx ↦ hφ ▸ hmem x (hsrc ▸ hx).1, ?_⟩
  · rw [hsrc] at hx
    simpa [Φ.left_inv hx.1] using (hB hx.2).2
  · rw [OpenPartialHomeomorph.symm_target, OpenPartialHomeomorph.restrOpen_source,
      OpenPartialHomeomorph.symm_source]
    exact inter_eq_right.2 (hB.trans inter_subset_left)
  · refine Subset.antisymm (fun x ⟨hx, hxb⟩ ↦ φ.injOn hx hpφ ?_) (singleton_subset_iff.2 ⟨hpφ, hp⟩)
    rw [hφ, ((hzero x (hsrc ▸ hx).1).1 hxb), h0]

/-! ### Neighbourhoods of the exceptional curves -/

/-- For coordinates `φ` at a base point as in `exists_openPartialHomeomorph_of_mem_baseLocus`, the
part of the surface over the source of `φ` is homeomorphic to the incidence set
`BlowupModel.pencilNbhd r` of the pencil over the ball of radius `r`, by `(x, ℓ) ↦ (φ x, ℓ)`. -/
private noncomputable def homeomorphPencilNbhd
    (φ : OpenPartialHomeomorph (ℙ ℂ (Fin 3 → ℂ)) (Fin 2 → ℂ)) {r : ℝ}
    (hφt : φ.target = {z | ‖complexToRealEuclidean (Fin 2) z‖ < r})
    (hφ : ∀ x ∈ φ.source, ∀ (w : Fin 2 → ℂ) (hw : w ≠ 0),
      (x, Projectivization.mk ℂ w hw) ∈ rationalEllipticSurface ↔
        w 0 * φ x 0 + w 1 * φ x 1 = 0) :
    {x : rationalEllipticSurface | x.val.1 ∈ φ.source} ≃ₜ BlowupModel.pencilNbhd r where
  toFun x := ⟨(φ x.val.val.1, x.val.val.2), BlowupModel.mem_pencilNbhd_iff.2
    ⟨BlowupModel.mem_pencilIncidence_iff.2 <| (hφ _ x.property _ x.val.val.2.rep_ne_zero).1 <| by
        rw [Projectivization.mk_rep]
        exact x.val.property,
      by simpa [hφt] using φ.map_source x.property⟩⟩
  invFun y :=
    have ht : y.val.1 ∈ φ.target := hφt ▸ (BlowupModel.mem_pencilNbhd_iff.1 y.property).2
    ⟨⟨(φ.symm y.val.1, y.val.2), by
      have h := (hφ _ (φ.map_target ht) _ y.val.2.rep_ne_zero).2 <| by
        rw [φ.right_inv ht]
        exact BlowupModel.mem_pencilIncidence_iff.1 (BlowupModel.mem_pencilNbhd_iff.1 y.property).1
      rwa [Projectivization.mk_rep] at h⟩, φ.map_target ht⟩
  left_inv x := Subtype.ext <| Subtype.ext <| Prod.ext (φ.left_inv x.property) rfl
  right_inv y :=
    have ht : y.val.1 ∈ φ.target := hφt ▸ (BlowupModel.mem_pencilNbhd_iff.1 y.property).2
    Subtype.ext <| Prod.ext (φ.right_inv ht) rfl
  continuous_toFun := by
    refine Continuous.subtype_mk (Continuous.prodMk ?_ (by fun_prop)) _
    exact φ.continuousOn.comp_continuous (by fun_prop) fun x ↦ x.property
  continuous_invFun := by
    refine Continuous.subtype_mk (Continuous.subtype_mk (Continuous.prodMk ?_ (by fun_prop)) _) _
    exact φ.continuousOn_symm.comp_continuous (by fun_prop) fun y ↦
      hφt ▸ (BlowupModel.mem_pencilNbhd_iff.1 y.property).2

private theorem fst_coe_coe_homeomorphPencilNbhd_symm_apply
    {φ : OpenPartialHomeomorph (ℙ ℂ (Fin 3 → ℂ)) (Fin 2 → ℂ)} {r : ℝ}
    (hφt : φ.target = {z | ‖complexToRealEuclidean (Fin 2) z‖ < r})
    (hφ : ∀ x ∈ φ.source, ∀ (w : Fin 2 → ℂ) (hw : w ≠ 0),
      (x, Projectivization.mk ℂ w hw) ∈ rationalEllipticSurface ↔
        w 0 * φ x 0 + w 1 * φ x 1 = 0)
    (y : BlowupModel.pencilNbhd r) :
    ((homeomorphPencilNbhd φ hφt hφ).symm y).val.val.1 = φ.symm y.val.1 :=
  (rfl)

/-- **The neighbourhoods of the exceptional curves of `E(1)`.** For a base point `p` of the pencil
and a neighbourhood `U` of `p` in `ℂℙ²`, there is an open set `N` of the rational elliptic surface
containing the exceptional curve `{p} × ℂℙ¹`, lying over `U`, over no other base point, and
homeomorphic to the neighbourhood `BlowupModel.openNbhd 1 r` of the exceptional divisor of the
model blowup of `ℂ²`, for some `r > 0`, by a homeomorphism that maps the curve onto the divisor.
-/
theorem exists_homeomorph_openNbhd_of_mem_baseLocus {p : ℙ ℂ (Fin 3 → ℂ)} (hp : p ∈ baseLocus)
    {U : Set (ℙ ℂ (Fin 3 → ℂ))} (hU : U ∈ 𝓝 p) :
    ∃ (N : Set rationalEllipticSurface) (r : ℝ) (e : N ≃ₜ BlowupModel.openNbhd 1 r), 0 < r ∧
      IsOpen N ∧ {x | x.val.1 = p} ⊆ N ∧ (∀ x ∈ N, x.val.1 ∈ U) ∧
      (∀ x ∈ N, x.val.1 ∈ baseLocus → x.val.1 = p) ∧
      e '' {x | x.val.val.1 = p} = Subtype.val ⁻¹' BlowupModel.exceptionalDivisor 1 := by
  obtain ⟨φ, r, hr, hpφ, hφU, hφt, hφ0, hφ, hbase⟩ :=
    exists_openPartialHomeomorph_of_mem_baseLocus hp hU
  set h := homeomorphPencilNbhd φ hφt hφ
  refine ⟨_, r, h.trans (BlowupModel.pencilNbhdHomeomorph r), hr,
    φ.open_source.preimage (by fun_prop),
    fun x hx ↦ by rw [mem_ofPred_eq] at hx ⊢; rw [hx]; exact hpφ, fun x hx ↦ hφU hx,
    fun x hx hb ↦ ?_, ?_⟩
  · have hx' : x.val.1 ∈ φ.source ∩ baseLocus := ⟨hx, hb⟩
    rwa [hbase] at hx'
  rw [show ⇑(h.trans _) = _ ∘ ⇑h from funext (h.trans_apply _), image_comp,
    ← BlowupModel.image_pencilNbhdHomeomorph_setOf_fst_eq_zero, h.image_eq_preimage_symm]
  congr 1
  ext y
  have ht : y.val.1 ∈ φ.target := hφt ▸ (BlowupModel.mem_pencilNbhd_iff.1 y.property).2
  rw [mem_preimage, mem_ofPred_eq, mem_ofPred_eq, fst_coe_coe_homeomorphPencilNbhd_symm_apply]
  constructor
  · intro hy
    rw [← φ.right_inv ht, hy, hφ0]
  · intro hy
    rw [hy, ← hφ0, φ.left_inv hpφ]

/-- For a base point `p` of the pencil and a neighbourhood `U` of `p` in `ℂℙ²`, there is a simply
connected open set `N` of the rational elliptic surface containing the exceptional curve
`{p} × ℂℙ¹`, lying over `U` and over no other base point, that stays path connected once the
curve is removed. -/
theorem exists_isSimplyConnected_of_mem_baseLocus {p : ℙ ℂ (Fin 3 → ℂ)} (hp : p ∈ baseLocus)
    {U : Set (ℙ ℂ (Fin 3 → ℂ))} (hU : U ∈ 𝓝 p) :
    ∃ N : Set rationalEllipticSurface, IsOpen N ∧ {x | x.val.1 = p} ⊆ N ∧ (∀ x ∈ N, x.val.1 ∈ U) ∧
      (∀ x ∈ N, x.val.1 ∈ baseLocus → x.val.1 = p) ∧ IsSimplyConnected N ∧
      IsPathConnected (N \ {x | x.val.1 = p}) := by
  obtain ⟨N, r, e, hr, hN, hpN, hNU, hNb, he⟩ := exists_homeomorph_openNbhd_of_mem_baseLocus hp hU
  refine ⟨N, hN, hpN, hNU, hNb,
    e.toHomotopyEquiv.simplyConnectedSpace_iff.2 (BlowupModel.isSimplyConnected_openNbhd hr), ?_⟩
  -- Inside `N`, the complement of the curve is the image under `e.symm` of the complement of the
  -- divisor in `openNbhd 1 r`.
  have hD : IsPathConnected ((Subtype.val ⁻¹' BlowupModel.exceptionalDivisor 1)ᶜ :
      Set (BlowupModel.openNbhd 1 r)) := by
    rw [Topology.IsInducing.subtypeVal.isPathConnected_iff, ← preimage_compl,
      Subtype.image_preimage_coe, ← sdiff_eq]
    exact BlowupModel.isPathConnected_openNbhd_sdiff_exceptionalDivisor hr
  have hC := hD.image e.symm.continuous
  rw [← he, ← image_compl_eq e.bijective, e.image_symm, e.preimage_image,
    Topology.IsInducing.subtypeVal.isPathConnected_iff] at hC
  convert hC using 1
  ext x
  simp only [mem_sdiff, mem_ofPred_eq, mem_image, mem_compl_iff, Subtype.exists,
    exists_and_right, exists_eq_right]
  tauto

end rationalEllipticSurface

end SymplecticGeometry

end
