/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Diffeomorph.Basic
public import SymplecticGeometry.Geometry.Manifold.Diffeomorph.RestrictScalars
public import SymplecticGeometry.Geometry.Manifold.Projectivization.Hypersurface.Basic
public import SymplecticGeometry.Geometry.Symplectic.Manifold.ComplexTorus
public import TauCeti.Analysis.SpecialFunctions.Elliptic.Holomorphic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.ComplexManifold
public import TauCeti.AlgebraicGeometry.EllipticCurve.ShortWeierstrass
public import TauCeti.Geometry.Manifold.Projectivization.Map
public import TauCeti.LinearAlgebra.Projectivization.Basic
import SymplecticGeometry.Algebra.Module.ZLattice.Complex

/-!
# The Fermat cubic as a Weierstrass curve

The plane Fermat cubic `x³ + y³ + z³ = 0`, the smooth projective hypersurface
`SymplecticGeometry.SmoothProjectiveHypersurface.fermat 1 3`, is carried onto the Weierstrass
cubic `Y² Z = X³ - 432 Z³` by the linear automorphism `(x, y, z) ↦ (-12 z, 36 (x - y), x + y)`
of `ℂ³`. Indeed that map has determinant `-864` and
`(36 (x - y))² (x + y) - (-12 z)³ + 432 (x + y)³ = 1728 (x³ + y³ + z³)`.
Both curves are complex submanifolds of `ℂℙ²`: the Fermat cubic through the slice charts of
`SymplecticGeometry.SmoothProjectiveHypersurface.instChartedSpace`, the points of the Weierstrass
curve through Tau Ceti's `WeierstrassCurve.Projective.Point.instChartedSpace`. The linear map
induces a biholomorphism of `ℂℙ²`, Tau Ceti's `Projectivization.mapDiffeomorph`, and maps into
either curve are holomorphic exactly when their composites into `ℂℙ²` are
(`WeierstrassCurve.Projective.Point.contMDiff_iff_contMDiff_toProjectivization_comp` and
`Manifold.IsSmoothEmbedding.contMDiff_iff_comp`), so the projective transformation
restricts to a biholomorphism of the two curves.

The Fermat cubic is the fibre of `E(1)` over `[1 : 0]`; to compare that fibre with a standard
torus, Tau Ceti's uniformization
`WeierstrassCurve.exists_continuousAddEquiv_periodLattice_contMDiff` then identifies the
Weierstrass curve with a complex torus `ℂ / Λ`, where `Λ` is the period lattice of
`fermatWeierstrassCurve`. A positively oriented `ℤ`-basis of `Λ` then identifies `ℂ / Λ` with
Tau Ceti's standard torus `∀ i : Unit ⊕ Unit, AddCircle (p i)` by
`SymplecticGeometry.latticeTorusDiffeomorph`. Forgetting the complex structure, the three maps
compose to a smooth diffeomorphism of real manifolds from the Fermat cubic onto the standard torus.

## Main declarations

* `SymplecticGeometry.fermatWeierstrassCurve`: the Weierstrass curve `Y² Z = X³ - 432 Z³`, which is
  Tau Ceti's `WeierstrassCurve.shortCurve 0 (-432)`, with its instance `IsElliptic`.
* `SymplecticGeometry.fermatCubicLinearEquiv`: the linear automorphism
  `(x, y, z) ↦ (-12 z, 36 (x - y), x + y)` of `ℂ³`, of determinant `-864`
  (`SymplecticGeometry.det_fermatCubicLinearEquiv`), and
  `SymplecticGeometry.eval_polynomial_fermatCubicLinearEquiv`: it pulls the Weierstrass cubic back
  to `1728 (x³ + y³ + z³)`.
* `SymplecticGeometry.mapProjectivization_fermatCubicLinearEquiv_mem_iff`: the induced projective
  transformation maps the Fermat cubic onto the Weierstrass cubic.
* `SymplecticGeometry.fermatCubicDiffeomorph`: the biholomorphism from the Fermat cubic to the
  points of `fermatWeierstrassCurve`, with `toProjectivization_fermatCubicDiffeomorph_mk` giving
  its value on a representative and `coe_fermatCubicDiffeomorph_symm_apply` its inverse.
* `SymplecticGeometry.fermatUniformizationAddEquiv`: an isomorphism of topological groups from
  `ℂ / Λ` onto the points of `fermatWeierstrassCurve`, chosen from Tau Ceti's
  `WeierstrassCurve.exists_continuousAddEquiv_periodLattice_contMDiff`.
* `SymplecticGeometry.fermatUniformization`: the same map as a biholomorphism. The `simp` lemmas
  `SymplecticGeometry.coe_fermatUniformization` and
  `SymplecticGeometry.coe_fermatUniformization_symm` rewrite it and its inverse to
  `fermatUniformizationAddEquiv` and its inverse, so that the lemmas on additive maps apply.
* `SymplecticGeometry.fermatPeriodBasis`: a `ℤ`-basis `b₀, b₁` of `Λ` with
  `0 < Im (conj b₀ * b₁)` (`SymplecticGeometry.zero_lt_im_conj_mul_fermatPeriodBasis`).
* `SymplecticGeometry.fermatCubicTorusDiffeomorph p`: the smooth diffeomorphism of real manifolds
  from the Fermat cubic onto `∀ i, AddCircle (p i)`, the composite of `fermatCubicDiffeomorph`,
  the inverse of `fermatUniformization` and `latticeTorusDiffeomorph p fermatPeriodBasis`
  (`SymplecticGeometry.fermatCubicTorusDiffeomorph_def`).

## References

* J. H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., Graduate Texts in Mathematics
  106, Springer, 2009, Chapter III, §1 (Weierstrass equations and their discriminant), and
  Proposition VI.3.6 (the uniformization of a complex elliptic curve).
* [P. Griffiths and J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978],
  Chapter 0, §1.
* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §7.2 (the
  fibre of the rational elliptic surface as a torus).
-/

public section

open ComplexConjugate MvPolynomial Projectivization TauCeti WeierstrassCurve
open scoped Manifold ContDiff LinearAlgebra.Projectivization

namespace SymplecticGeometry

/-- The Weierstrass curve `Y² Z = X³ - 432 Z³` over `ℂ`, that is Tau Ceti's short Weierstrass
curve `WeierstrassCurve.shortCurve 0 (-432)`: all coefficients vanish except `a₆ = -432`. It is
the image of the Fermat cubic under `fermatCubicLinearEquiv`. -/
noncomputable abbrev fermatWeierstrassCurve : WeierstrassCurve ℂ :=
  shortCurve 0 (-432)

/-- The discriminant of `Y² Z = X³ - 432 Z³` is `-16 · 27 · 432²`. -/
theorem fermatWeierstrassCurve_Δ : fermatWeierstrassCurve.Δ = -80621568 := by
  rw [Δ_of_isShortNF, shortCurve_a₄, shortCurve_a₆]
  norm_num

instance fermatWeierstrassCurve.instIsElliptic : fermatWeierstrassCurve.IsElliptic :=
  ⟨isUnit_iff_ne_zero.2 (by rw [fermatWeierstrassCurve_Δ]; norm_num)⟩

/-- The linear automorphism `(x, y, z) ↦ (-12 z, 36 (x - y), x + y)` of `ℂ³`, of determinant
`-864`, which carries the Fermat cubic onto the Weierstrass cubic of `fermatWeierstrassCurve`. -/
noncomputable def fermatCubicLinearEquiv : (Fin 3 → ℂ) ≃ₗ[ℂ] Fin 3 → ℂ where
  toFun v := ![-12 * v 2, 36 * (v 0 - v 1), v 0 + v 1]
  invFun w := ![(w 2 + w 1 / 36) / 2, (w 2 - w 1 / 36) / 2, -(w 0 / 12)]
  map_add' v w := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' c v := by
    ext i
    fin_cases i <;> simp <;> ring
  left_inv v := by
    ext i
    fin_cases i <;> simp [neg_div]
  right_inv w := by
    ext i
    fin_cases i <;> simp <;> ring

@[simp]
theorem fermatCubicLinearEquiv_apply (v : Fin 3 → ℂ) :
    fermatCubicLinearEquiv v = ![-12 * v 2, 36 * (v 0 - v 1), v 0 + v 1] :=
  (rfl)

@[simp]
theorem fermatCubicLinearEquiv_symm_apply (w : Fin 3 → ℂ) :
    fermatCubicLinearEquiv.symm w = ![(w 2 + w 1 / 36) / 2, (w 2 - w 1 / 36) / 2, -(w 0 / 12)] :=
  (rfl)

/-- The determinant of `fermatCubicLinearEquiv` is `-864`. -/
theorem det_fermatCubicLinearEquiv :
    LinearMap.det (fermatCubicLinearEquiv : (Fin 3 → ℂ) →ₗ[ℂ] Fin 3 → ℂ) = -864 := by
  rw [← LinearMap.det_toMatrix', Matrix.det_fin_three]
  simp [LinearMap.toMatrix'_apply, fermatCubicLinearEquiv_apply]
  norm_num

/-- The linear map `fermatCubicLinearEquiv` pulls the Weierstrass cubic `Y² Z - X³ + 432 Z³`
back to `1728 (x³ + y³ + z³)`. -/
theorem eval_polynomial_fermatCubicLinearEquiv (v : Fin 3 → ℂ) :
    eval (fermatCubicLinearEquiv v) fermatWeierstrassCurve.toProjective.polynomial =
      1728 * eval v (SmoothProjectiveHypersurface.fermat 1 3).poly := by
  simp only [Projective.eval_polynomial, SmoothProjectiveHypersurface.fermat_poly,
    fermatCubicLinearEquiv_apply, map_sum, map_pow, eval_X]
  simp [Fin.sum_univ_three]
  ring

/-- A point of `ℂℙ²` lies on the Fermat cubic exactly when its image under the projective
transformation induced by `fermatCubicLinearEquiv` lies on the Weierstrass cubic. -/
theorem mapProjectivization_fermatCubicLinearEquiv_mem_iff {L : ℙ ℂ (Fin 3 → ℂ)} :
    fermatCubicLinearEquiv.mapProjectivization L ∈
        complexProjectiveZeroLocus (fun _ : Unit ↦ fermatWeierstrassCurve.toProjective.polynomial) ↔
      L ∈ (SmoothProjectiveHypersurface.fermat 1 3).carrier := by
  induction L using Projectivization.ind with
  | h v hv =>
    rw [LinearEquiv.mapProjectivization_mk, complexProjectiveZeroLocus_mk_iff
      (fun _ ↦ fermatWeierstrassCurve.toProjective.isHomogeneous_polynomial),
      SmoothProjectiveHypersurface.mem_carrier_mk_iff]
    rw [eval_polynomial_fermatCubicLinearEquiv]
    simp

/-- **The Fermat cubic is biholomorphic to the Weierstrass curve `Y² Z = X³ - 432 Z³`.** The
biholomorphism from the plane Fermat cubic `x³ + y³ + z³ = 0` to the points of
`fermatWeierstrassCurve` sends `[x : y : z]` to `[-12 z : 36 (x - y) : x + y]`; it is the
restriction of the projective transformation of `ℂℙ²` induced by `fermatCubicLinearEquiv`. -/
noncomputable def fermatCubicDiffeomorph :
    SmoothProjectiveHypersurface.fermat 1 3 ≃ₘ^ω⟮𝓘(ℂ, Fin 1 → ℂ), 𝓘(ℂ)⟯
      fermatWeierstrassCurve.toProjective.Point where
  toFun p := (Projective.Point.homeomorphZeroLocus _).symm
    ⟨fermatCubicLinearEquiv.mapProjectivization p.val,
      mapProjectivization_fermatCubicLinearEquiv_mem_iff.2 p.property⟩
  invFun P := ⟨fermatCubicLinearEquiv.mapProjectivization.symm P.toProjectivization, by
    rw [← mapProjectivization_fermatCubicLinearEquiv_mem_iff, Equiv.apply_symm_apply,
      ← Projective.Point.range_toProjectivization]
    exact Set.mem_range_self P⟩
  left_inv p := by
    apply Subtype.ext
    dsimp only
    rw [← Projective.Point.coe_homeomorphZeroLocus_apply, Homeomorph.apply_symm_apply,
      Equiv.symm_apply_apply]
  right_inv P := by
    apply Projective.Point.toProjectivization_injective
    dsimp only
    rw [← Projective.Point.coe_homeomorphZeroLocus_apply, Homeomorph.apply_symm_apply]
    exact Equiv.apply_symm_apply _ _
  contMDiff_toFun := by
    rw [Projective.Point.contMDiff_iff_contMDiff_toProjectivization_comp]
    convert (mapDiffeomorph fermatCubicLinearEquiv ω).contMDiff.comp
      (SmoothProjectiveHypersurface.fermat 1 3).embedding.contMDiff using 1
    funext p
    rw [Function.comp_apply, Equiv.coe_fn_mk, ← Projective.Point.coe_homeomorphZeroLocus_apply,
      Homeomorph.apply_symm_apply, Function.comp_apply,
      SmoothProjectiveHypersurface.coe_embedding, coe_mapDiffeomorph]
    exact LinearEquiv.mapProjectivization_apply _ _
  contMDiff_invFun := by
    rw [(SmoothProjectiveHypersurface.fermat 1 3).embedding.isSmoothEmbedding.contMDiff_iff_comp,
      SmoothProjectiveHypersurface.coe_embedding]
    convert (mapDiffeomorph fermatCubicLinearEquiv ω).symm.contMDiff.comp
      (Projective.Point.isSmoothEmbedding_toProjectivization _ ω).contMDiff using 1
    funext P
    rw [Function.comp_apply, Function.comp_apply, Equiv.coe_fn_symm_mk, mapDiffeomorph_symm,
      coe_mapDiffeomorph]
    exact (congrArg (· P.toProjectivization)
      (LinearEquiv.mapProjectivization_symm fermatCubicLinearEquiv)).trans
        (fermatCubicLinearEquiv.symm.mapProjectivization_apply _)

/-- The image under `fermatCubicDiffeomorph` of a point `p` of the Fermat cubic is, as a point
of `ℂℙ²`, the image of `p` under the projective transformation induced by
`fermatCubicLinearEquiv`. -/
@[simp]
theorem toProjectivization_fermatCubicDiffeomorph (p : SmoothProjectiveHypersurface.fermat 1 3) :
    (fermatCubicDiffeomorph p).toProjectivization =
      fermatCubicLinearEquiv.mapProjectivization p.val := by
  rw [← Projective.Point.coe_homeomorphZeroLocus_apply]
  exact congrArg Subtype.val (Homeomorph.apply_symm_apply _ _)

/-- **The biholomorphism on representatives.** The point `[v]` of the Fermat cubic is sent by
`fermatCubicDiffeomorph` to the point of `fermatWeierstrassCurve` with homogeneous coordinates
`fermatCubicLinearEquiv v`, that is `[-12 z : 36 (x - y) : x + y]` for `v = (x, y, z)`. -/
theorem toProjectivization_fermatCubicDiffeomorph_mk {v : Fin 3 → ℂ} (hv : v ≠ 0)
    (h : Projectivization.mk ℂ v hv ∈ (SmoothProjectiveHypersurface.fermat 1 3).carrier) :
    (fermatCubicDiffeomorph ⟨Projectivization.mk ℂ v hv, h⟩).toProjectivization =
      Projectivization.mk ℂ (fermatCubicLinearEquiv v)
        (fermatCubicLinearEquiv.map_ne_zero_iff.2 hv) := by
  rw [toProjectivization_fermatCubicDiffeomorph, LinearEquiv.mapProjectivization_mk]

/-- The inverse of `fermatCubicDiffeomorph` sends a point of `fermatWeierstrassCurve` to the image
of its point of `ℂℙ²` under the projective transformation induced by the inverse of
`fermatCubicLinearEquiv`. -/
@[simp]
theorem coe_fermatCubicDiffeomorph_symm_apply (P : fermatWeierstrassCurve.toProjective.Point) :
    (fermatCubicDiffeomorph.symm P : ℙ ℂ (Fin 3 → ℂ)) =
      fermatCubicLinearEquiv.symm.mapProjectivization P.toProjectivization :=
  congrArg (· P.toProjectivization) (LinearEquiv.mapProjectivization_symm fermatCubicLinearEquiv)

/-- The isomorphism of topological groups from `ℂ / Λ`, for the period lattice `Λ` of
`fermatWeierstrassCurve`, onto the group of points of `fermatWeierstrassCurve` that underlies
`fermatUniformization`: one of the isomorphisms given by Tau Ceti's uniformization theorem
`WeierstrassCurve.exists_continuousAddEquiv_periodLattice_contMDiff`, chosen once and for all.
As a function it is `fermatUniformization` (`coe_fermatUniformization`). -/
noncomputable def fermatUniformizationAddEquiv :
    (ℂ ⧸ fermatWeierstrassCurve.periodLattice.toAddSubgroup) ≃ₜ+
      fermatWeierstrassCurve.toProjective.Point :=
  (exists_continuousAddEquiv_periodLattice_contMDiff fermatWeierstrassCurve).choose

theorem fermatUniformizationAddEquiv_def :
    fermatUniformizationAddEquiv =
      (exists_continuousAddEquiv_periodLattice_contMDiff fermatWeierstrassCurve).choose :=
  (rfl)

/-- **The Weierstrass curve `Y² Z = X³ - 432 Z³` as a complex torus.** A biholomorphism from
`ℂ / Λ`, for the period lattice `Λ` of `fermatWeierstrassCurve`, onto the points of
`fermatWeierstrassCurve`, which is also an isomorphism of groups: as a function it is the
additive equivalence `fermatUniformizationAddEquiv` (`coe_fermatUniformization`). -/
noncomputable def fermatUniformization :
    (ℂ ⧸ fermatWeierstrassCurve.periodLattice.toAddSubgroup) ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯
      fermatWeierstrassCurve.toProjective.Point where
  toEquiv := fermatUniformizationAddEquiv.toEquiv
  contMDiff_toFun := by
    rw [fermatUniformizationAddEquiv_def]
    exact (exists_continuousAddEquiv_periodLattice_contMDiff fermatWeierstrassCurve).choose_spec.1
  contMDiff_invFun := by
    rw [fermatUniformizationAddEquiv_def]
    exact (exists_continuousAddEquiv_periodLattice_contMDiff fermatWeierstrassCurve).choose_spec.2

/-- The biholomorphism `fermatUniformization` and the additive equivalence
`fermatUniformizationAddEquiv` are the same function. Read from left to right, this lets the
lemmas on additive maps, such as `map_zero`, `map_neg` and `map_nsmul`, apply to it. -/
@[simp]
theorem coe_fermatUniformization :
    ⇑fermatUniformization = ⇑fermatUniformizationAddEquiv :=
  (rfl)

/-- The inverses of the biholomorphism `fermatUniformization` and of the additive equivalence
`fermatUniformizationAddEquiv` are the same function. -/
@[simp]
theorem coe_fermatUniformization_symm :
    ⇑fermatUniformization.symm = ⇑fermatUniformizationAddEquiv.symm :=
  (rfl)

/-- A positively oriented `ℤ`-basis `b₀, b₁` of the period lattice of `fermatWeierstrassCurve`:
one with `0 < Im (conj b₀ * b₁)`, chosen by `ZLattice.exists_basis_zero_lt_im_conj_mul`. -/
noncomputable def fermatPeriodBasis : Module.Basis (Fin 2) ℤ fermatWeierstrassCurve.periodLattice :=
  (ZLattice.exists_basis_zero_lt_im_conj_mul fermatWeierstrassCurve.periodLattice).choose

/-- The basis `fermatPeriodBasis` is positively oriented. -/
theorem zero_lt_im_conj_mul_fermatPeriodBasis :
    0 < (conj (fermatPeriodBasis 0 : ℂ) * fermatPeriodBasis 1).im :=
  (ZLattice.exists_basis_zero_lt_im_conj_mul fermatWeierstrassCurve.periodLattice).choose_spec

variable (p : Unit ⊕ Unit → ℝ) [∀ i, Fact (0 < p i)]

/-- **The Fermat cubic is diffeomorphic to the standard torus.** The smooth diffeomorphism of real
manifolds from the Fermat cubic `x³ + y³ + z³ = 0`, with the real structure of its complex charts,
onto Tau Ceti's standard torus `∀ i : Unit ⊕ Unit, AddCircle (p i)`. It is the composite of the
biholomorphism `fermatCubicDiffeomorph` onto the Weierstrass curve `Y² Z = X³ - 432 Z³`, the
inverse of its uniformization `fermatUniformization` by `ℂ / Λ`, and the diffeomorphism
`latticeTorusDiffeomorph p fermatPeriodBasis` from `ℂ / Λ` onto the standard torus. -/
noncomputable def fermatCubicTorusDiffeomorph :
    SmoothProjectiveHypersurface.fermat 1 3 ≃ₘ^∞⟮𝓘(ℝ, Fin 1 → ℂ),
      ModelWithCorners.pi fun _ : Unit ⊕ Unit ↦ 𝓘(ℝ)⟯ ∀ i, AddCircle (p i) :=
  (((fermatCubicDiffeomorph.restrictScalars' ℝ).trans
    (fermatUniformization.symm.restrictScalars' ℝ)).ofLE le_top).trans
      (latticeTorusDiffeomorph p fermatPeriodBasis)

/-- `fermatCubicTorusDiffeomorph p` is the composite of `fermatCubicDiffeomorph` and the inverse
of `fermatUniformization`, both with scalars restricted to `ℝ`, and
`latticeTorusDiffeomorph p fermatPeriodBasis`. -/
theorem fermatCubicTorusDiffeomorph_def :
    fermatCubicTorusDiffeomorph p =
      (((fermatCubicDiffeomorph.restrictScalars' ℝ).trans
        (fermatUniformization.symm.restrictScalars' ℝ)).ofLE le_top).trans
          (latticeTorusDiffeomorph p fermatPeriodBasis) :=
  (rfl)

/-- `fermatCubicTorusDiffeomorph p` sends a point `x` of the Fermat cubic to the image under
`latticeTorusDiffeomorph p fermatPeriodBasis` of the point of `ℂ / Λ` that
`fermatUniformizationAddEquiv` sends to `fermatCubicDiffeomorph x`. -/
@[simp]
theorem fermatCubicTorusDiffeomorph_apply (x : SmoothProjectiveHypersurface.fermat 1 3) :
    fermatCubicTorusDiffeomorph p x =
      latticeTorusDiffeomorph p fermatPeriodBasis
        (fermatUniformizationAddEquiv.symm (fermatCubicDiffeomorph x)) := by
  simp only [fermatCubicTorusDiffeomorph_def, Diffeomorph.coe_trans, Diffeomorph.coe_ofLE,
    Diffeomorph.coe_restrictScalars', Function.comp_apply, coe_fermatUniformization_symm]

/-- The inverse of `fermatCubicTorusDiffeomorph p` sends a point `y` of the standard torus to the
point of the Fermat cubic whose image under `fermatCubicDiffeomorph` is the image under
`fermatUniformizationAddEquiv` of `(latticeTorusDiffeomorph p fermatPeriodBasis).symm y`. -/
@[simp]
theorem fermatCubicTorusDiffeomorph_symm_apply (y : ∀ i, AddCircle (p i)) :
    (fermatCubicTorusDiffeomorph p).symm y =
      fermatCubicDiffeomorph.symm
        (fermatUniformizationAddEquiv ((latticeTorusDiffeomorph p fermatPeriodBasis).symm y)) := by
  simp [fermatCubicTorusDiffeomorph_def]

end SymplecticGeometry

end
