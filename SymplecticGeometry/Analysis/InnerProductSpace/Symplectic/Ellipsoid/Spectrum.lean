/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import SymplecticGeometry.Analysis.InnerProductSpace.Symplectic.Ellipsoid.NormalForm
import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.Williamson
import SymplecticGeometry.LinearAlgebra.QuadraticForm.PosDef
import TauCeti.Data.Multiset.Fintype

/-!
# The symplectic spectrum of an ellipsoid

An ellipsoid `{z | Q z ≤ 1}` centred at `0` in `(ℝ²ⁿ, ω₀)`, with `Q` positive definite, is
carried by a linear symplectic map onto a standard ellipsoid `E(r)`
(`SymplecticGeometry.exists_isSymplectomorphism_image_eq_stdEllipsoid`). The radii `r` are
unique up to order: if a linear symplectic map carries `E(r)` onto `E(r')`, then `r'` is a
permutation of `r`. Indeed `E(r')` determines the form `∑ⱼ (xⱼ² + yⱼ²) / r'ⱼ²`, which in the
standard Darboux basis is `∑ⱼ (2 / r'ⱼ²) Iⱼ`, `Iⱼ` the elliptic blocks; so the frequencies
`2 / rⱼ²` and `2 / r'ⱼ²` are Williamson frequencies of the same form, in two Darboux bases, and
these are unique up to a permutation
(`TauCeti.SymplecticForm.IsDarbouxBasis.exists_perm_eq_of_sum_smul_elliptic_eq`).

The multiset of these radii is the symplectic spectrum of `Q`. Since linear symplectic maps
have determinant `1`, the volume of the ellipsoid is that of `E(r)`, namely
`πⁿ / n! · ∏ⱼ rⱼ²`.

## Main definitions

* `SymplecticGeometry.symplecticSpectrum Q`: the multiset of the radii of the normal form of the
  ellipsoid `{z | Q z ≤ 1}`, for `Q` positive definite, and `0` otherwise.

## Main results

* `SymplecticGeometry.exists_perm_eq_of_image_stdEllipsoid_eq`: the radii of a standard
  ellipsoid are a linear symplectic invariant, up to order.
* `SymplecticGeometry.symplecticSpectrum_eq`: any normal form of the ellipsoid of `Q` has the
  radii `symplecticSpectrum Q`.
* `SymplecticGeometry.exists_isSymplectomorphism_image_eq_stdEllipsoid_of_mem_symplecticSpectrum`:
  each element of the spectrum is a radius of some normal form.
* `SymplecticGeometry.symplecticSpectrum_comp`: the spectrum is invariant under linear
  symplectic maps.
* `SymplecticGeometry.volume_setOfPred_le_one`: the volume of the ellipsoid of `Q` in terms of its
  spectrum.
* `SymplecticGeometry.exists_isDarbouxBasis_orthogonal_and_stdEllipsoid_normalForm`: the
  orthogonal Darboux bases for an inner product, together with the normal form of ellipsoids,
  the uniqueness of their radii and their volume.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.4
  (Lemmas 2.4.5 and 2.4.6, and the volume of an ellipsoid on p. 60)
-/

public section

namespace SymplecticGeometry

open TauCeti TauCeti.SymplecticForm StdSpace Module Real

variable {ι : Type*} [Fintype ι]

section Uniqueness

/-- **The radii of a standard ellipsoid are a symplectic invariant.** If a linear symplectic
map of `(ℝ²ⁿ, ω₀)` carries the standard ellipsoid `E(r)` onto `E(r')`, for positive radii `r`
and `r'`, then `r'` is a permutation of `r`. -/
theorem exists_perm_eq_of_image_stdEllipsoid_eq {r r' : ι → ℝ} (hr : ∀ j, 0 < r j)
    (hr' : ∀ j, 0 < r' j) {e : StdSpace ι ≃ₗ[ℝ] StdSpace ι}
    (he : IsSymplectomorphism (stdForm ι) (stdForm ι) e)
    (h : e '' stdEllipsoid r = stdEllipsoid r') :
    ∃ σ : Equiv.Perm ι, r' = r ∘ σ := by
  let τ : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let d := stdDarbouxBasisOf τ
  have hd : (stdForm ι).IsDarbouxBasis d := isDarbouxBasis_stdDarbouxBasisOf τ
  -- The ellipsoid `E(r')` determines its form, which is therefore `stdEllipsoidForm r ∘ e⁻¹`.
  have hQ : (stdEllipsoidForm r).comp (e.symm : StdSpace ι →ₗ[ℝ] StdSpace ι) =
      stdEllipsoidForm r' := by
    refine ((stdEllipsoidForm_posDef fun j ↦ (hr' j).ne').eq_of_setOfPred_le_one_eq ?_).symm
    rw [← stdEllipsoid_def, ← h, stdEllipsoid_def, QuadraticMap.image_setOfPred_le_one]
  have hsum : ∑ k, (2 / r (τ k) ^ 2) • elliptic (d.map e) k =
      ∑ k, (2 / r' (τ k) ^ 2) • elliptic d k := by
    rw [← stdEllipsoidForm_eq_sum_smul_elliptic τ, ← hQ, stdEllipsoidForm_eq_sum_smul_elliptic τ]
    ext z
    simp [d, sum_apply, Basis.map_repr]
  obtain ⟨σ, hσ⟩ := (hd.map he).exists_perm_eq_of_sum_smul_elliptic_eq hd
    (fun k ↦ div_pos two_pos (pow_pos (hr _) 2)) (fun k ↦ div_pos two_pos (pow_pos (hr' _) 2))
    hsum
  refine ⟨τ.symm.trans (σ.trans τ), funext fun j ↦ ?_⟩
  have hk := congrFun hσ (τ.symm j)
  simp only [Function.comp_apply, Equiv.apply_symm_apply] at hk
  have hsq : r' j ^ 2 = r (τ (σ (τ.symm j))) ^ 2 := by
    have h₁ := (pow_pos (hr' j) 2).ne'
    have h₂ := (pow_pos (hr (τ (σ (τ.symm j)))) 2).ne'
    rw [div_eq_div_iff h₁ h₂] at hk
    linarith
  simpa using (sq_eq_sq₀ (hr' j).le (hr _).le).1 hsq

/-- For `ι = Fin m`, the monotone radii of a standard ellipsoid are a symplectic invariant: if a
linear symplectic map carries `E(r)` onto `E(r')`, for positive monotone `r` and `r'`, then
`r = r'`. -/
theorem eq_of_image_stdEllipsoid_eq_of_monotone {m : ℕ} {r r' : Fin m → ℝ}
    (hr : ∀ j, 0 < r j) (hr' : ∀ j, 0 < r' j) (hrm : Monotone r) (hrm' : Monotone r')
    {e : StdSpace (Fin m) ≃ₗ[ℝ] StdSpace (Fin m)}
    (he : IsSymplectomorphism (stdForm (Fin m)) (stdForm (Fin m)) e)
    (h : e '' stdEllipsoid r = stdEllipsoid r') :
    r = r' := by
  obtain ⟨σ, rfl⟩ := exists_perm_eq_of_image_stdEllipsoid_eq hr hr' he h
  exact Tuple.unique_monotone (σ := 1) (τ := σ) hrm hrm'

end Uniqueness

section Spectrum

open scoped Classical in
/-- The **symplectic spectrum** of a positive definite quadratic form `Q` on `(ℝ²ⁿ, ω₀)`: the
multiset of the radii `r₁, …, rₙ` of a standard ellipsoid `E(r)` onto which a linear symplectic
map carries the ellipsoid `{z | Q z ≤ 1}`. These radii do not depend on the choices
(`SymplecticGeometry.symplecticSpectrum_eq`). By convention, the spectrum of a form that is not
positive definite is empty. -/
noncomputable def symplecticSpectrum (Q : QuadraticForm ℝ (StdSpace ι)) : Multiset ℝ :=
  if hQ : Q.PosDef then
    Finset.univ.val.map (exists_isSymplectomorphism_image_eq_stdEllipsoid hQ).choose
  else 0

open scoped Classical in
theorem symplecticSpectrum_def (Q : QuadraticForm ℝ (StdSpace ι)) :
    symplecticSpectrum Q =
      if hQ : Q.PosDef then
        Finset.univ.val.map (exists_isSymplectomorphism_image_eq_stdEllipsoid hQ).choose
      else 0 :=
  (rfl)

theorem symplecticSpectrum_of_not_posDef {Q : QuadraticForm ℝ (StdSpace ι)} (hQ : ¬Q.PosDef) :
    symplecticSpectrum Q = 0 := by
  simp only [symplecticSpectrum_def, hQ, ↓reduceDIte]

/-- A quadratic form whose symplectic spectrum is nonempty is positive definite. -/
theorem posDef_of_mem_symplecticSpectrum {Q : QuadraticForm ℝ (StdSpace ι)} {s : ℝ}
    (hs : s ∈ symplecticSpectrum Q) : Q.PosDef := by
  by_contra hQ
  simp [symplecticSpectrum_of_not_posDef hQ] at hs

/-- The **characterization of the symplectic spectrum**: if a linear symplectic map `e` carries
the ellipsoid of a positive definite form `Q` onto the standard ellipsoid `E(r)`, with positive
radii `r`, then the spectrum of `Q` is the multiset of the `rⱼ`. -/
theorem symplecticSpectrum_eq {Q : QuadraticForm ℝ (StdSpace ι)} (hQ : Q.PosDef) {r : ι → ℝ}
    (hr : ∀ j, 0 < r j) {e : StdSpace ι ≃ₗ[ℝ] StdSpace ι}
    (he : IsSymplectomorphism (stdForm ι) (stdForm ι) e)
    (h : e '' {z | Q z ≤ 1} = stdEllipsoid r) :
    symplecticSpectrum Q = Finset.univ.val.map r := by
  obtain ⟨e₀, hr₀, he₀, h₀⟩ := (exists_isSymplectomorphism_image_eq_stdEllipsoid hQ).choose_spec
  simp only [symplecticSpectrum_def, hQ, ↓reduceDIte]
  set r₀ := (exists_isSymplectomorphism_image_eq_stdEllipsoid hQ).choose
  have himage : (e.symm.trans e₀) '' stdEllipsoid r = stdEllipsoid r₀ := by
    rw [← h, Set.image_image]
    simpa using h₀
  obtain ⟨σ, hσ⟩ := exists_perm_eq_of_image_stdEllipsoid_eq hr hr₀ (he.symm.trans he₀) himage
  exact Multiset.map_univ_val_eq_of_equiv σ (congrFun hσ)

/-- Every element `s` of the symplectic spectrum of `Q` is a radius of a normal form of the
ellipsoid of `Q`: a linear symplectic map carries `{z | Q z ≤ 1}` onto `E(r)`, with positive
radii `r`, such that the spectrum of `Q` is the multiset of the `rⱼ` and `rᵢ = s`. -/
theorem exists_isSymplectomorphism_image_eq_stdEllipsoid_of_mem_symplecticSpectrum
    {Q : QuadraticForm ℝ (StdSpace ι)} {s : ℝ} (hs : s ∈ symplecticSpectrum Q) :
    ∃ (r : ι → ℝ) (e : StdSpace ι ≃ₗ[ℝ] StdSpace ι) (i : ι), (∀ j, 0 < r j) ∧
      IsSymplectomorphism (stdForm ι) (stdForm ι) e ∧ e '' {z | Q z ≤ 1} = stdEllipsoid r ∧
      symplecticSpectrum Q = Finset.univ.val.map r ∧ r i = s := by
  have hQ := posDef_of_mem_symplecticSpectrum hs
  obtain ⟨r, e, hr, he, h⟩ := exists_isSymplectomorphism_image_eq_stdEllipsoid hQ
  have hspec := symplecticSpectrum_eq hQ hr he h
  obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 (hspec ▸ hs)
  exact ⟨r, e, i, hr, he, h, hspec, rfl⟩

/-- The symplectic spectrum of a positive definite form has `n` elements. -/
theorem card_symplecticSpectrum {Q : QuadraticForm ℝ (StdSpace ι)} (hQ : Q.PosDef) :
    Multiset.card (symplecticSpectrum Q) = Fintype.card ι := by
  simp only [symplecticSpectrum_def, hQ, ↓reduceDIte]
  rw [Multiset.card_map, Finset.card_val, Finset.card_univ]

/-- The elements of a symplectic spectrum are positive. -/
theorem pos_of_mem_symplecticSpectrum {Q : QuadraticForm ℝ (StdSpace ι)} {s : ℝ}
    (hs : s ∈ symplecticSpectrum Q) : 0 < s := by
  obtain ⟨r, -, i, hr, -, -, -, rfl⟩ :=
    exists_isSymplectomorphism_image_eq_stdEllipsoid_of_mem_symplecticSpectrum hs
  exact hr i

/-- The symplectic spectrum is invariant under linear symplectic maps: `Q ∘ e` has the same
spectrum as `Q` for a linear symplectic map `e` of `(ℝ²ⁿ, ω₀)`. -/
theorem symplecticSpectrum_comp (Q : QuadraticForm ℝ (StdSpace ι))
    {e : StdSpace ι ≃ₗ[ℝ] StdSpace ι} (he : IsSymplectomorphism (stdForm ι) (stdForm ι) e) :
    symplecticSpectrum (Q.comp (e : StdSpace ι →ₗ[ℝ] StdSpace ι)) = symplecticSpectrum Q := by
  have hback : (Q.comp (e : StdSpace ι →ₗ[ℝ] StdSpace ι)).comp
      (e.symm : StdSpace ι →ₗ[ℝ] StdSpace ι) = Q := by
    ext z
    simp
  by_cases hQ : Q.PosDef
  · obtain ⟨r, e₀, hr, he₀, h₀⟩ := exists_isSymplectomorphism_image_eq_stdEllipsoid hQ
    rw [symplecticSpectrum_eq hQ hr he₀ h₀]
    refine symplecticSpectrum_eq (hQ.comp _ e.injective) hr (he.trans he₀) ?_
    have hpre : e '' {z | Q.comp (e : StdSpace ι →ₗ[ℝ] StdSpace ι) z ≤ 1} = {z | Q z ≤ 1} := by
      rw [QuadraticMap.image_setOfPred_le_one, hback]
    rw [← h₀, ← hpre, Set.image_image]
    rfl
  · have hQe : ¬(Q.comp (e : StdSpace ι →ₗ[ℝ] StdSpace ι)).PosDef := fun h ↦
      hQ (hback ▸ h.comp _ e.symm.injective)
    rw [symplecticSpectrum_of_not_posDef hQ, symplecticSpectrum_of_not_posDef hQe]

/-- The symplectic spectrum of the standard ellipsoid `E(r)`, for positive radii `r`, is the
multiset of the `rⱼ`. -/
@[simp]
theorem symplecticSpectrum_stdEllipsoidForm {r : ι → ℝ} (hr : ∀ j, 0 < r j) :
    symplecticSpectrum (stdEllipsoidForm r) = Finset.univ.val.map r :=
  symplecticSpectrum_eq (stdEllipsoidForm_posDef fun j ↦ (hr j).ne') hr
    (IsSymplectomorphism.refl (stdForm ι)) (by rw [stdEllipsoid_def]; exact Set.image_id _)

end Spectrum

section Volume

/-- The volume of the standard ellipsoid `E(r)`, for positive radii `r`, is
`πⁿ / n! · ∏ⱼ rⱼ²`. -/
theorem volume_stdEllipsoid {r : ι → ℝ} (hr : ∀ j, 0 < r j) :
    MeasureTheory.volume (stdEllipsoid r) =
      ENNReal.ofReal (π ^ Fintype.card ι / (Fintype.card ι).factorial * ∏ j, r j ^ 2) := by
  classical
  rw [stdEllipsoid_eq_image_closedBall fun j ↦ (hr j).ne',
    MeasureTheory.Measure.addHaar_image_linearMap]
  have hdet : |LinearMap.det (Matrix.toEuclideanLin (Matrix.diagonal (Sum.elim r r)))| =
      ∏ j, r j ^ 2 := by
    rw [LinearMap.det_toLpLin, Matrix.det_diagonal, Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, ← pow_two, Finset.prod_pow, abs_pow, sq_abs]
  rw [hdet]
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp [volume_euclideanSpace_eq_dirac]
  rw [InnerProductSpace.volume_closedBall_of_dim_even (finrank_stdSpace (ι := ι)),
    ENNReal.ofReal_one, one_pow, one_mul, ENNReal.ofReal_mul (by positivity), mul_comm]

/-- **The volume of an ellipsoid.** For a positive definite form `Q` on `(ℝ²ⁿ, ω₀)` with
symplectic spectrum `r₁, …, rₙ`, the ellipsoid `{z | Q z ≤ 1}` has volume
`πⁿ / n! · ∏ⱼ rⱼ²`. -/
theorem volume_setOfPred_le_one {Q : QuadraticForm ℝ (StdSpace ι)} (hQ : Q.PosDef) :
    MeasureTheory.volume {z | Q z ≤ 1} =
      ENNReal.ofReal (π ^ Fintype.card ι / (Fintype.card ι).factorial *
        ((symplecticSpectrum Q).map (· ^ 2)).prod) := by
  obtain ⟨r, e, hr, he, h⟩ := exists_isSymplectomorphism_image_eq_stdEllipsoid hQ
  have hvol : MeasureTheory.volume (e '' {z | Q z ≤ 1}) = MeasureTheory.volume {z | Q z ≤ 1} := by
    rw [← LinearEquiv.coe_coe, MeasureTheory.Measure.addHaar_image_linearMap, he.det_eq_one]
    simp
  rw [← hvol, h, volume_stdEllipsoid hr, symplecticSpectrum_eq hQ hr he h, Multiset.map_map,
    Finset.prod_map_val]
  rfl

end Volume

section NormalForm

open scoped RealInnerProductSpace

/-- **Normal forms for a symplectic form and a Euclidean structure.**

* On a real inner product space `V` of finite dimension, every symplectic form `ω` has a Darboux
  basis `(q₁, p₁, …, qₘ, pₘ)` whose vectors are pairwise orthogonal, with `‖qₖ‖ = ‖pₖ‖`.
* In `(ℝ²ⁿ, ω₀)`, for every positive definite quadratic form `Q`, a linear symplectic map
  carries the ellipsoid `{z | Q z ≤ 1}` onto a standard ellipsoid `E(r)` with positive radii;
  the radii of every such normal form are, up to order, the symplectic spectrum of `Q`; and the
  ellipsoid has volume `πⁿ / n! · ∏ⱼ rⱼ²`.

Milestone: *Simultaneous normal form of a symplectic form and an inner product*. -/
theorem exists_isDarbouxBasis_orthogonal_and_stdEllipsoid_normalForm
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (ω : SymplecticForm V) (ι : Type*) [Fintype ι] :
    (∃ (m : ℕ) (b : Basis (Fin m × Fin 2) ℝ V), ω.IsDarbouxBasis b ∧
      (Pairwise fun k l ↦ ⟪b k, b l⟫ = 0) ∧ ∀ k, ‖b (k, 0)‖ = ‖b (k, 1)‖) ∧
    ∀ Q : QuadraticForm ℝ (StdSpace ι), Q.PosDef →
      (∃ (r : ι → ℝ) (e : StdSpace ι ≃ₗ[ℝ] StdSpace ι), (∀ j, 0 < r j) ∧
        IsSymplectomorphism (stdForm ι) (stdForm ι) e ∧
        e '' {z | Q z ≤ 1} = stdEllipsoid r) ∧
      (∀ (r : ι → ℝ) (e : StdSpace ι ≃ₗ[ℝ] StdSpace ι), (∀ j, 0 < r j) →
        IsSymplectomorphism (stdForm ι) (stdForm ι) e →
        e '' {z | Q z ≤ 1} = stdEllipsoid r →
        symplecticSpectrum Q = Finset.univ.val.map r) ∧
      MeasureTheory.volume {z | Q z ≤ 1} = ENNReal.ofReal
        (π ^ Fintype.card ι / (Fintype.card ι).factorial *
          ((symplecticSpectrum Q).map (· ^ 2)).prod) :=
  ⟨ω.exists_isDarbouxBasis_orthogonal, fun _ hQ ↦
    ⟨exists_isSymplectomorphism_image_eq_stdEllipsoid hQ,
      fun _ _ hr he h ↦ symplecticSpectrum_eq hQ hr he h, volume_setOfPred_le_one hQ⟩⟩

end NormalForm

end SymplecticGeometry

end
