/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Projectivization.Hypersurface.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.ComplexManifold
public import TauCeti.Geometry.Manifold.Projectivization.Map
public import TauCeti.LinearAlgebra.Projectivization.Basic

/-!
# The Fermat cubic as a Weierstrass curve

The plane Fermat cubic `x³ + y³ + z³ = 0`, the smooth projective hypersurface
`SymplecticGeometry.SmoothProjectiveHypersurface.fermat 1 3`, is carried onto the Weierstrass
cubic `Y² Z = X³ - 432 Z³` by the linear automorphism `(x, y, z) ↦ (-12 z, 36 (x - y), x + y)`
of `ℂ³`. Indeed that map has determinant `-864` and
`(36 (x - y))² (x + y) - (-12 z)³ + 432 (x + y)³ = 1728 (x³ + y³ + z³)`.
Both curves are complex submanifolds of `ℂℙ²`: the Fermat cubic through the slice charts of
`SymplecticGeometry.SmoothProjectiveHypersurface.instChartedSpace`, the points of the Weierstrass
curve through Tau Ceti's `WeierstrassCurve.Projective.Point.instChartedSpace`. The projective
transformations of `ℂℙ²` induced by the linear map and by its inverse are holomorphic
(`Projectivization.contMDiff_map`), and maps into either curve are holomorphic exactly when
their composites into `ℂℙ²` are
(`WeierstrassCurve.Projective.Point.contMDiff_iff_contMDiff_toProjectivization_comp` and
`Manifold.IsSmoothEmbedding.contMDiff_iff_comp`), so the projective transformation
restricts to a biholomorphism of the two curves.

The Fermat cubic is the fibre of `E(1)` over `[1 : 0]`; to compare that fibre with a standard
torus, Tau Ceti's uniformization
`WeierstrassCurve.exists_continuousAddEquiv_periodLattice_contMDiff` then identifies the
Weierstrass curve with a complex torus `ℂ / Λ`.

## Main declarations

* `SymplecticGeometry.fermatWeierstrassCurve`: the Weierstrass curve `Y² Z = X³ - 432 Z³`, that is
  `a₁ = a₂ = a₃ = a₄ = 0` and `a₆ = -432`, with its instance `IsElliptic`.
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

## References

* J. H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., Graduate Texts in Mathematics
  106, Springer, 2009, Chapter III, §1 (Weierstrass equations and their discriminant).
* [P. Griffiths and J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978],
  Chapter 0, §1.
-/

public section

open MvPolynomial Projectivization TauCeti WeierstrassCurve
open scoped Manifold ContDiff LinearAlgebra.Projectivization

namespace SymplecticGeometry

/-- The Weierstrass curve `Y² Z = X³ - 432 Z³` over `ℂ`: all coefficients vanish except
`a₆ = -432`. It is the image of the Fermat cubic under `fermatCubicLinearEquiv`. -/
noncomputable def fermatWeierstrassCurve : WeierstrassCurve ℂ where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := 0
  a₆ := -432

@[simp] theorem fermatWeierstrassCurve_a₁ : fermatWeierstrassCurve.a₁ = 0 := (rfl)
@[simp] theorem fermatWeierstrassCurve_a₂ : fermatWeierstrassCurve.a₂ = 0 := (rfl)
@[simp] theorem fermatWeierstrassCurve_a₃ : fermatWeierstrassCurve.a₃ = 0 := (rfl)
@[simp] theorem fermatWeierstrassCurve_a₄ : fermatWeierstrassCurve.a₄ = 0 := (rfl)
@[simp] theorem fermatWeierstrassCurve_a₆ : fermatWeierstrassCurve.a₆ = -432 := (rfl)

/-- The discriminant of `Y² Z = X³ - 432 Z³` is `-16 · 27 · 432²`. -/
theorem fermatWeierstrassCurve_Δ : fermatWeierstrassCurve.Δ = -80621568 := by
  simp [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
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
    fin_cases i <;> simp; ring
  right_inv w := by
    ext i
    fin_cases i <;> simp <;> ring

theorem fermatCubicLinearEquiv_apply (v : Fin 3 → ℂ) :
    fermatCubicLinearEquiv v = ![-12 * v 2, 36 * (v 0 - v 1), v 0 + v 1] :=
  (rfl)

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
    simp [eval_polynomial_fermatCubicLinearEquiv]

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
    convert (contMDiff_map _ fermatCubicLinearEquiv.injective ω).comp
      (SmoothProjectiveHypersurface.fermat 1 3).embedding.contMDiff using 1
    funext p
    rw [Function.comp_apply, Equiv.coe_fn_mk, ← Projective.Point.coe_homeomorphZeroLocus_apply,
      Homeomorph.apply_symm_apply, Function.comp_apply,
      SmoothProjectiveHypersurface.coe_embedding]
    exact LinearEquiv.mapProjectivization_apply _ _
  contMDiff_invFun := by
    rw [(SmoothProjectiveHypersurface.fermat 1 3).embedding.isSmoothEmbedding.contMDiff_iff_comp,
      SmoothProjectiveHypersurface.coe_embedding]
    convert (contMDiff_map _ fermatCubicLinearEquiv.symm.injective ω).comp
      (Projective.Point.isSmoothEmbedding_toProjectivization _ ω).contMDiff using 1
    funext P
    rw [Function.comp_apply, Function.comp_apply, Equiv.coe_fn_symm_mk]
    have h : fermatCubicLinearEquiv.mapProjectivization.symm P.toProjectivization =
        map (fermatCubicLinearEquiv.symm : (Fin 3 → ℂ) →ₗ[ℂ] Fin 3 → ℂ)
          fermatCubicLinearEquiv.symm.injective P.toProjectivization := by
      rw [LinearEquiv.mapProjectivization_symm, LinearEquiv.mapProjectivization_apply]
    exact h

/-- The image under `fermatCubicDiffeomorph` of a point `p` of the Fermat cubic is, as a point
of `ℂℙ²`, the image of `p` under the projective transformation induced by
`fermatCubicLinearEquiv`. -/
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
theorem coe_fermatCubicDiffeomorph_symm_apply (P : fermatWeierstrassCurve.toProjective.Point) :
    (fermatCubicDiffeomorph.symm P : ℙ ℂ (Fin 3 → ℂ)) =
      fermatCubicLinearEquiv.symm.mapProjectivization P.toProjectivization :=
  congrArg (· P.toProjectivization) (LinearEquiv.mapProjectivization_symm fermatCubicLinearEquiv)

end SymplecticGeometry

end
