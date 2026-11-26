/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Analysis.InnerProductSpace.Symplectic.Ellipsoid.Basic
public import TauCeti.Geometry.Symplectic.Hamiltonian.Williamson
import SymplecticGeometry.LinearAlgebra.QuadraticForm.PosDef

/-!
# The normal form of an ellipsoid

Every ellipsoid `{z | Q z ≤ 1}` centred at `0` in `(ℝ²ⁿ, ω₀)`, with `Q` positive definite, is
carried by a linear symplectic map onto a standard ellipsoid `E(r)` with positive radii. The
proof applies Williamson's theorem (Tau Ceti's
`TauCeti.SymplecticForm.exists_isDarbouxBasis_eq_sum_smul_elliptic_of_posDef`) to `Q`: in a
Darboux basis, `Q = ∑ₖ νₖ (xₖ² + yₖ²) / 2` with `νₖ > 0`, so the radii are `rₖ = √(2 / νₖ)`.

## Main results

* `SymplecticGeometry.stdEllipsoidForm_eq_sum_smul_elliptic`: the form of a standard ellipsoid
  in the relabelled standard Darboux basis `SymplecticGeometry.stdDarbouxBasisOf` of
  `SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Basic`.
* `SymplecticGeometry.exists_isSymplectomorphism_image_eq_stdEllipsoid`: the normal form of an
  ellipsoid centred at `0`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Lemma 2.4.6
-/

public section

namespace SymplecticGeometry

open TauCeti TauCeti.SymplecticForm StdSpace Module

variable {ι : Type*} [Fintype ι]

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
    rw [finrank_stdSpace, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at h
    rw [Fintype.card_fin]
    omega
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
  rw [QuadraticMap.image_setOfPred_le_one, stdEllipsoid_def]
  ext z
  simp only [Set.mem_ofPred_eq, QuadraticMap.comp_apply, LinearEquiv.coe_coe, ← hform,
    LinearEquiv.apply_symm_apply]

end SymplecticGeometry

end
