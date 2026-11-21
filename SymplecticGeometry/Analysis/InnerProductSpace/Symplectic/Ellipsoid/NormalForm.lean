/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Analysis.InnerProductSpace.Symplectic.Ellipsoid.Basic
public import SymplecticGeometry.LinearAlgebra.QuadraticForm.PosDef
public import TauCeti.Geometry.Symplectic.Darboux.EuclideanBasis
public import TauCeti.Geometry.Symplectic.Hamiltonian.Williamson

/-!
# The normal form of an ellipsoid

Every ellipsoid `{z | Q z ≤ 1}` centred at `0` in `(ℝ²ⁿ, ω₀)`, with `Q` positive definite, is
carried by a linear symplectic map onto a standard ellipsoid `E(r)` with positive radii. The
proof applies Williamson's theorem (Tau Ceti's
`TauCeti.SymplecticForm.exists_isDarbouxBasis_eq_sum_smul_elliptic_of_posDef`) to `Q`: in a
Darboux basis, `Q = ∑ₖ νₖ (xₖ² + yₖ²) / 2` with `νₖ > 0`, so the radii are `rₖ = √(2 / νₖ)`.

## Main results

* `SymplecticGeometry.isSymplectomorphism_piLpCongrLeft_sumCongr`: reindexing the coordinate
  pairs of the standard model is symplectic.
* `SymplecticGeometry.stdDarbouxBasisOf`: the standard Darboux basis of `StdSpace ι` after a
  labelling `Fin m ≃ ι` of the coordinate pairs, and
  `SymplecticGeometry.stdEllipsoidForm_eq_sum_smul_elliptic`, the form of a standard ellipsoid
  in that basis.
* `SymplecticGeometry.exists_isSymplectomorphism_image_eq_stdEllipsoid`: the normal form of an
  ellipsoid centred at `0`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Lemma 2.4.6
-/

public section

namespace SymplecticGeometry

open TauCeti TauCeti.SymplecticForm StdSpace Module

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The reindexing `σ : ι ≃ κ` of the coordinate pairs `(xᵢ, yᵢ)`, which sends the coordinates
of index `i` to those of index `σ i`, is a symplectomorphism from `ω₀` on `StdSpace ι` to `ω₀`
on `StdSpace κ`. -/
theorem isSymplectomorphism_piLpCongrLeft_sumCongr (σ : ι ≃ κ) :
    IsSymplectomorphism (stdForm ι) (stdForm κ)
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (σ.sumCongr σ)).toLinearEquiv := by
  rw [isSymplectomorphism_iff]
  intro z w
  simp only [stdForm_apply, x_apply, y_apply, LinearIsometryEquiv.coe_toLinearEquiv,
    LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'_apply, Equiv.sumCongr_symm,
    Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr]
  exact Equiv.sum_comp σ.symm fun i ↦ z (Sum.inl i) * w (Sum.inr i) - z (Sum.inr i) * w (Sum.inl i)

/-- The standard Darboux basis of `StdSpace ι`, after a labelling `τ : Fin m ≃ ι` of the
coordinate pairs: Tau Ceti's `stdDarbouxBasis m`, carried to `StdSpace ι` along
`EuclideanSpace.sumEquivProd` and the relabelling `τ`. It sends `(k, 0)` to the unit vector of
`x_{τ k}` and `(k, 1)` to that of `y_{τ k}`. -/
noncomputable def stdDarbouxBasisOf {m : ℕ} (τ : Fin m ≃ ι) :
    Basis (Fin m × Fin 2) ℝ (StdSpace ι) :=
  (stdDarbouxBasis m).map
    ((EuclideanSpace.sumEquivProd (𝕜 := ℝ) (ι := Fin m) (κ := Fin m)).toLinearEquiv.symm.trans
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (τ.sumCongr τ)).toLinearEquiv)

theorem stdDarbouxBasisOf_def {m : ℕ} (τ : Fin m ≃ ι) :
    stdDarbouxBasisOf τ = (stdDarbouxBasis m).map
      ((EuclideanSpace.sumEquivProd (𝕜 := ℝ) (ι := Fin m) (κ := Fin m)).toLinearEquiv.symm.trans
        (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (τ.sumCongr τ)).toLinearEquiv) :=
  (rfl)

/-- The coordinate of index `(k, 0)` in `stdDarbouxBasisOf τ` is `x_{τ k}`. -/
@[simp]
theorem stdDarbouxBasisOf_repr_zero {m : ℕ} (τ : Fin m ≃ ι) (z : StdSpace ι) (k : Fin m) :
    (stdDarbouxBasisOf τ).repr z (k, 0) = z.x (τ k) := by
  simp [stdDarbouxBasisOf_def, Basis.map_repr]

/-- The coordinate of index `(k, 1)` in `stdDarbouxBasisOf τ` is `y_{τ k}`. -/
@[simp]
theorem stdDarbouxBasisOf_repr_one {m : ℕ} (τ : Fin m ≃ ι) (z : StdSpace ι) (k : Fin m) :
    (stdDarbouxBasisOf τ).repr z (k, 1) = z.y (τ k) := by
  simp [stdDarbouxBasisOf_def, Basis.map_repr]

/-- The relabelled standard Darboux basis is a Darboux basis of `ω₀`. -/
theorem isDarbouxBasis_stdDarbouxBasisOf {m : ℕ} (τ : Fin m ≃ ι) :
    (stdForm ι).IsDarbouxBasis (stdDarbouxBasisOf τ) :=
  (isDarbouxBasis_stdDarbouxBasis m).map
    (isSymplectomorphism_sumEquivProd.symm.trans (isSymplectomorphism_piLpCongrLeft_sumCongr τ))

/-- In the relabelled standard Darboux basis, the form `∑ⱼ (xⱼ² + yⱼ²) / rⱼ²` of the standard
ellipsoid is `∑ₖ (2 / r_{τ k}²) Iₖ`, `Iₖ` the elliptic blocks. -/
theorem stdEllipsoidForm_eq_sum_smul_elliptic {m : ℕ} (τ : Fin m ≃ ι) (r : ι → ℝ) :
    stdEllipsoidForm r = ∑ k, (2 / r (τ k) ^ 2) • elliptic (stdDarbouxBasisOf τ) k := by
  ext z
  rw [stdEllipsoidForm_apply, ← Equiv.sum_comp τ]
  simp only [sum_apply, smul_apply, elliptic_apply, smul_eq_mul, stdDarbouxBasisOf_repr_zero,
    stdDarbouxBasisOf_repr_one]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  ring

/-- The normal form of an ellipsoid centred at `0`: for a positive definite quadratic form `Q`
on `StdSpace ι`, there are positive radii `r` and a linear symplectic map `e` of `(ℝ²ⁿ, ω₀)`
carrying the ellipsoid `{z | Q z ≤ 1}` onto the standard ellipsoid `E(r)`. -/
theorem exists_isSymplectomorphism_image_eq_stdEllipsoid
    {Q : QuadraticForm ℝ (StdSpace ι)} (hQ : Q.PosDef) :
    ∃ (r : ι → ℝ) (e : StdSpace ι ≃ₗ[ℝ] StdSpace ι), (∀ j, 0 < r j) ∧
      IsSymplectomorphism (stdForm ι) (stdForm ι) e ∧
      e '' {z | Q z ≤ 1} = stdEllipsoid r := by
  obtain ⟨m, b, ν, hb, hν, rfl⟩ :=
    (stdForm ι).exists_isDarbouxBasis_eq_sum_smul_elliptic_of_posDef hQ
  have hcard : Fintype.card (Fin m) = Fintype.card ι := by
    have h := (Module.finrank_eq_card_basis b).symm
    simp only [finrank_euclideanSpace, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
      at h
    simpa using (by omega : m = Fintype.card ι)
  let σ : Fin m ≃ ι := Fintype.equivOfCardEq hcard
  -- `e` carries the Williamson basis `b` to the relabelled standard Darboux basis `d`.
  let d := stdDarbouxBasisOf σ
  let e : StdSpace ι ≃ₗ[ℝ] StdSpace ι := b.darbouxBasisEquiv.trans d.darbouxBasisEquiv.symm
  have he : IsSymplectomorphism (stdForm ι) (stdForm ι) e :=
    hb.isSymplectomorphism_darbouxBasisEquiv.trans
      (isDarbouxBasis_stdDarbouxBasisOf σ).isSymplectomorphism_darbouxBasisEquiv.symm
  have hrepr (v : StdSpace ι) (p : Fin m × Fin 2) : d.repr (e v) p = b.repr v p := by
    have hev : d.darbouxBasisEquiv (e v) = b.darbouxBasisEquiv v := by simp [e]
    match p with
    | (k, 0) => rw [← d.darbouxBasisEquiv_fst_apply, hev, b.darbouxBasisEquiv_fst_apply]
    | (k, 1) => rw [← d.darbouxBasisEquiv_snd_apply, hev, b.darbouxBasisEquiv_snd_apply]
  let r : ι → ℝ := fun j ↦ √(2 / ν (σ.symm j))
  have hr (j : ι) : 0 < r j := Real.sqrt_pos.2 (div_pos two_pos (hν _))
  refine ⟨r, e, hr, he, ?_⟩
  have hform (v : StdSpace ι) : stdEllipsoidForm r (e v) = (∑ k, ν k • elliptic b k) v := by
    simp only [stdEllipsoidForm_eq_sum_smul_elliptic σ, sum_apply, smul_apply, elliptic_apply,
      smul_eq_mul, d, hrepr, r, Equiv.symm_apply_apply]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [Real.sq_sqrt (div_pos two_pos (hν k)).le, div_div_cancel₀ two_ne_zero]
  rw [QuadraticMap.image_setOf_le_one, stdEllipsoid_def]
  ext z
  simp only [Set.mem_ofPred_eq, QuadraticMap.comp_apply, LinearEquiv.coe_coe, ← hform,
    LinearEquiv.apply_symm_apply]

end SymplecticGeometry

end
