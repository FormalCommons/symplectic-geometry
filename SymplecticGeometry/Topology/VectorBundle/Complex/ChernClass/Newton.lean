/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.ChernCharacter
public import TauCeti.RingTheory.PowerSeries.Derivative
public import SymplecticGeometry.Topology.VectorBundle.Complex.ChernClass.Basic
import SymplecticGeometry.Topology.VectorBundle.Complex.ChernClass.Whitney
import SymplecticGeometry.Topology.VectorBundle.Complex.ChernClass.Naturality
import SymplecticGeometry.Topology.VectorBundle.ModelEquiv
import SymplecticGeometry.AlgebraicTopology.Cohomology.Empty

/-!
# Newton classes of complex vector bundles

For a complex vector bundle `E` of rank `n` with Chern classes `c₁, …, cₙ`, the Newton class
`s_j(E) ∈ H^{2j}(B; ℤ)` is the Newton polynomial `s_j` (Tau Ceti's `TauCeti.newtonMvPolynomial`,
the polynomial expressing the power sum `∑ xᵢʲ` in the elementary symmetric functions) evaluated
at `c₁, …, cₙ` in the even integral cohomology ring, and read in degree `2j`. For Chern roots
`xᵢ` it is `∑ xᵢʲ`: unlike the Chern classes it is additive on direct sums. These classes are
the integral form of the Chern character, `s_j = j! ch_j`, as in Milnor–Stasheff, §16.

## Main definitions

* `SymplecticGeometry.Bundle.newtonClass G E j`: the Newton class `s_j(E)`, with
  `newtonClass_def`.

## Main results

* `newtonClass_zero`: `s₀(E)` is the rank of `E`.
* `newtonClass_pullback`, `newtonClass_congr`: Newton classes are natural and depend only on the
  isomorphism class of the bundle.
* `newtonClass_trivial`: the Newton classes of a trivial bundle vanish in positive degree.
* `newtonClass_of_finrank_eq_one`: for a line bundle, `s_j(L) = c₁(L) ^ j`.
* `newtonClass_prod`: over a compact base, `s_j(E₁ ⊕ E₂) = s_j(E₁) + s_j(E₂)`. The total Chern
  series `c(t) = ∑ c_k tᵏ` is multiplicative by the Whitney sum formula
  (`mk_evenIntegralCohomologyOf_chernClass_prod`), and the generating series of the
  `(-1)^(k-1) s_k` is its logarithmic derivative `t c'(t) / c(t)`
  (`TauCeti.X_mul_derivative_chernSeries`), which Tau Ceti's `PowerSeries.xLogDeriv` shows
  turns products into sums.
* `newtonClass_eq_of_cup_eq_zero`: if every cup product of two classes of positive even degrees
  adding up to `2j` vanishes, then `s_j(E) = (-1)^(j-1) j c_j(E)` for `j ≥ 1`, by Newton's
  identity, the degree-`j` coefficient of the same logarithmic derivative.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §16
-/

public section

noncomputable section

open Bundle Module TauCeti

namespace SymplecticGeometry.Bundle

variable {B : Type} [TopologicalSpace B]
  (G : Type) [NormedAddCommGroup G] [NormedSpace ℂ G]
  (E : B → Type) [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)] [∀ b, Module ℝ (E b)]
  [∀ b, IsScalarTower ℝ ℂ (E b)] [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace G E)]
  [FiberBundle G E] [VectorBundle ℂ G E]

/-- The **Newton class** `s_j(E) ∈ H^{2j}(B; ℤ)` of a complex vector bundle `E` of rank
`n = finrank ℂ G`: the component of degree `2j` of the Newton polynomial
`TauCeti.newtonMvPolynomial ℤ n j` evaluated at the Chern classes `c₁(E), …, cₙ(E)` in the even
integral cohomology ring. For Chern roots `xᵢ` it is the power sum `∑ xᵢʲ`. -/
def newtonClass (j : ℕ) : (TopCat.of B).integralCohomology (2 * j) :=
  MvPolynomial.aeval (fun i : Fin (finrank ℂ G) ↦
      (TopCat.of B).evenIntegralCohomologyOf (i + 1) (chernClass G E (i + 1)))
    (newtonMvPolynomial ℤ (finrank ℂ G) j) j

theorem newtonClass_def (j : ℕ) :
    newtonClass G E j =
      MvPolynomial.aeval (fun i : Fin (finrank ℂ G) ↦
          (TopCat.of B).evenIntegralCohomologyOf (i + 1) (chernClass G E (i + 1)))
        (newtonMvPolynomial ℤ (finrank ℂ G) j) j :=
  (rfl)

/-- The Chern classes `c₁, …, cₙ` in the even integral cohomology ring, where `i : Fin n` stands
for `c_{i+1}`. -/
private abbrev chernClassVec : Fin (finrank ℂ G) → (TopCat.of B).EvenIntegralCohomology :=
  fun i ↦ (TopCat.of B).evenIntegralCohomologyOf (i + 1) (chernClass G E (i + 1))

/-- The Newton polynomial evaluated at the Chern classes, in all degrees. -/
private abbrev newtonSum (j : ℕ) : (TopCat.of B).EvenIntegralCohomology :=
  MvPolynomial.aeval (chernClassVec G E) (newtonMvPolynomial ℤ (finrank ℂ G) j)

private theorem newtonClass_eq_newtonSum (j : ℕ) : newtonClass G E j = newtonSum G E j j :=
  newtonClass_def G E j

/-- `t c'(t) = c(t) ∑_{k ≥ 1} (-1)^(k+1) s_k tᵏ` for the total Chern series of `E`. -/
private theorem X_mul_derivative_chernSeries_chernClassVec :
    PowerSeries.X * PowerSeries.derivative (chernSeries (chernClassVec G E)) =
      chernSeries (chernClassVec G E) * PowerSeries.mk fun k ↦
        if k = 0 then 0 else (-1) ^ (k + 1) * newtonSum G E k :=
  X_mul_derivative_chernSeries ℤ _

/-- **The Newton class of degree zero is the rank.** -/
@[simp]
theorem newtonClass_zero :
    newtonClass G E 0 = finrank ℂ G • (TopCat.of B).integralCohomologyOne := by
  rw [newtonClass_def, newtonMvPolynomial_zero_right, map_natCast, ← nsmul_one,
    ← TopCat.evenIntegralCohomologyOf_one, ← map_nsmul, DirectSum.of_eq_same]

/-! ### Naturality and invariance -/

section Naturality

variable {G E}

/-- **Naturality of the Newton classes.** For a continuous map `f : B' → B` of compact spaces,
`s_j(f *ᵖ E) = f^* s_j(E)`. -/
theorem newtonClass_pullback [FiniteDimensional ℂ G] [CompactSpace B] {B' : Type}
    [TopologicalSpace B'] [CompactSpace B'] (f : C(B', B)) (j : ℕ) :
    newtonClass G (f *ᵖ E) j =
      TopCat.singularCohomologyMap (TopCat.ofHom f) (2 * j) (newtonClass G E j) := by
  rw [newtonClass_eq_newtonSum, newtonClass_eq_newtonSum,
    ← TopCat.evenIntegralCohomologyMap_apply, newtonSum, newtonSum,
    MvPolynomial.map_aeval_eq_aeval_map (RingHom.id ℤ) _ (RingHom.ext_int _ _),
    MvPolynomial.map_id]
  congr 3
  funext i
  simp only [chernClassVec, TopCat.evenIntegralCohomologyMap_of, chernClass_pullback]

/-- **Isomorphic complex bundles have the same Newton classes.** The isomorphism is a family of
complex-linear equivalences of the fibres, continuous on total spaces; the two models may
differ. -/
theorem newtonClass_congr [FiniteDimensional ℂ G] [CompactSpace B]
    {G' : Type} [NormedAddCommGroup G'] [NormedSpace ℂ G']
    {E' : B → Type} [∀ b, AddCommGroup (E' b)] [∀ b, Module ℂ (E' b)] [∀ b, Module ℝ (E' b)]
    [∀ b, IsScalarTower ℝ ℂ (E' b)] [∀ b, TopologicalSpace (E' b)]
    [TopologicalSpace (TotalSpace G' E')] [FiberBundle G' E'] [VectorBundle ℂ G' E']
    (φ : ∀ b, E b ≃L[ℂ] E' b)
    (hφ : Continuous fun v : TotalSpace G E ↦ TotalSpace.mk' G' v.proj (φ v.proj v.snd))
    (j : ℕ) : newtonClass G E j = newtonClass G' E' j := by
  rcases isEmpty_or_nonempty B with hB | hB
  · exact Subsingleton.elim _ _
  rw [newtonClass_def, newtonClass_def]
  have hc : ∀ k, chernClass G E k = chernClass G' E' k := chernClass_congr φ hφ
  simp only [hc]
  rw [← VectorBundle.finrank_model_eq (F := G) (F' := G') φ]

end Naturality

/-! ### Trivial bundles and line bundles -/

variable (B) in
/-- **The Newton classes of a trivial bundle vanish in positive degree**, over a compact
base. -/
@[simp]
theorem newtonClass_trivial [FiniteDimensional ℂ G] [CompactSpace B] {j : ℕ} (hj : j ≠ 0) :
    newtonClass G (Bundle.Trivial B G) j = 0 := by
  -- The Chern classes of positive degree vanish, so `s_j` is evaluated at zero.
  have hc : chernClassVec G (Bundle.Trivial B G) = 0 := by
    funext i
    rw [chernClassVec, chernClass_trivial B G (Nat.add_one_ne_zero _), map_zero, Pi.zero_apply]
  rw [newtonClass_eq_newtonSum, newtonSum, hc, MvPolynomial.aeval_zero,
    constantCoeff_newtonMvPolynomial hj, map_zero, DirectSum.zero_apply]

/-- **The Newton classes of a line bundle** are the powers of its first Chern class:
`s_j(L) = c₁(L) ^ j`, the power taken in the even integral cohomology ring. -/
theorem newtonClass_of_finrank_eq_one (hG : finrank ℂ G = 1) (j : ℕ) :
    newtonClass G E j =
      ((TopCat.of B).evenIntegralCohomologyOf 1 (chernClass G E 1) ^ j) j := by
  -- The Chern classes are the elementary symmetric functions of the single root `c₁(L)`.
  have hc : chernClassVec G E =
      fun i : Fin (finrank ℂ G) ↦ ({(TopCat.of B).evenIntegralCohomologyOf 1 (chernClass G E 1)} :
        Multiset _).esymm (i + 1) := by
    funext ⟨i, hi⟩
    obtain rfl : i = 0 := by omega
    rw [chernClassVec, Multiset.esymm_one, Multiset.sum_singleton]
  rw [newtonClass_eq_newtonSum, newtonSum, hc,
    Multiset.aeval_esymm_newtonMvPolynomial _ (by simp [hG])]
  simp

/-! ### Additivity -/

section Sum

variable {G₁ : Type} [NormedAddCommGroup G₁] [NormedSpace ℂ G₁]
  {E₁ : B → Type} [∀ b, AddCommGroup (E₁ b)] [∀ b, Module ℂ (E₁ b)] [∀ b, Module ℝ (E₁ b)]
  [∀ b, IsScalarTower ℝ ℂ (E₁ b)] [∀ b, TopologicalSpace (E₁ b)]
  [TopologicalSpace (TotalSpace G₁ E₁)] [FiberBundle G₁ E₁] [VectorBundle ℂ G₁ E₁]
  {G₂ : Type} [NormedAddCommGroup G₂] [NormedSpace ℂ G₂]
  {E₂ : B → Type} [∀ b, AddCommGroup (E₂ b)] [∀ b, Module ℂ (E₂ b)] [∀ b, Module ℝ (E₂ b)]
  [∀ b, IsScalarTower ℝ ℂ (E₂ b)] [∀ b, TopologicalSpace (E₂ b)]
  [TopologicalSpace (TotalSpace G₂ E₂)] [FiberBundle G₂ E₂] [VectorBundle ℂ G₂ E₂]
  [FiniteDimensional ℂ G₁] [FiniteDimensional ℂ G₂] [CompactSpace B]

/-- The Newton polynomials of the Chern classes are additive, in all degrees. -/
private theorem newtonSum_prod (k : ℕ) :
    newtonSum (G₁ × G₂) (E₁ ×ᵇ E₂) k = newtonSum G₁ E₁ k + newtonSum G₂ E₂ k := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp [newtonSum, newtonMvPolynomial_zero_right, Module.finrank_prod]
  have h₁ := X_mul_derivative_chernSeries_chernClassVec G₁ E₁
  have h₂ := X_mul_derivative_chernSeries_chernClassVec G₂ E₂
  have h := X_mul_derivative_chernSeries_chernClassVec (G₁ × G₂) (E₁ ×ᵇ E₂)
  rw [chernSeries_chernClass, mk_evenIntegralCohomologyOf_chernClass_prod,
    ← chernSeries_chernClass G₁ E₁, ← chernSeries_chernClass G₂ E₂] at h
  obtain ⟨u₁, hu₁⟩ : IsUnit (chernSeries (chernClassVec G₁ E₁)) :=
    PowerSeries.isUnit_iff_constantCoeff.2 (by simp)
  obtain ⟨u₂, hu₂⟩ : IsUnit (chernSeries (chernClassVec G₂ E₂)) :=
    PowerSeries.isUnit_iff_constantCoeff.2 (by simp)
  rw [← hu₁] at h₁
  rw [← hu₂] at h₂
  rw [← hu₁, ← hu₂, ← Units.val_mul] at h
  -- A series `S` with `X u' = u S` is `X u' u⁻¹`, which turns products into sums.
  have hlog : ∀ {u : (PowerSeries (TopCat.of B).EvenIntegralCohomology)ˣ}
      {S : PowerSeries (TopCat.of B).EvenIntegralCohomology},
      PowerSeries.X * PowerSeries.derivative u.val = u.val * S →
        S = (PowerSeries.xLogDeriv u).toAdd := fun {u S} h ↦ by
    rw [PowerSeries.toAdd_xLogDeriv, h, mul_comm u.val S, mul_assoc, Units.mul_inv, mul_one]
  have hsum := (hlog h).trans (by rw [map_mul, toAdd_mul, ← hlog h₁, ← hlog h₂])
  have hk' := congrArg (PowerSeries.coeff k) hsum
  simp only [map_add, PowerSeries.coeff_mk, hk, ↓reduceIte] at hk'
  rw [← mul_add] at hk'
  exact ((isUnit_neg_one.pow _).mul_left_cancel hk')

/-- **Additivity of the Newton classes.** Over a compact base,
`s_j(E₁ ⊕ E₂) = s_j(E₁) + s_j(E₂)`. -/
theorem newtonClass_prod (j : ℕ) :
    newtonClass (G₁ × G₂) (E₁ ×ᵇ E₂) j = newtonClass G₁ E₁ j + newtonClass G₂ E₂ j := by
  rw [newtonClass_eq_newtonSum, newtonClass_eq_newtonSum, newtonClass_eq_newtonSum,
    newtonSum_prod, DFinsupp.add_apply]

end Sum

/-! ### Newton's identity -/

/-- **Newton's identity for the Newton classes.** If every cup product of two classes of
positive even degrees `2a`, `2b` with `a + b = j` vanishes, then
`s_j(E) = (-1)^(j-1) j c_j(E)` for `j ≥ 1`. -/
theorem newtonClass_eq_of_cup_eq_zero {j : ℕ} (hj : j ≠ 0)
    (h : ∀ a b (hab : a + b = j), 0 < a → 0 < b →
      ∀ (x : (TopCat.of B).integralCohomology (2 * a))
        (y : (TopCat.of B).integralCohomology (2 * b)),
        (TopCat.of B).integralCup (2 * a) (2 * b) (2 * j) (by omega) x y = 0) :
    newtonClass G E j = ((-1) ^ (j - 1) * j : ℤ) • chernClass G E j := by
  have hX := congrArg
    (fun φ : PowerSeries (TopCat.of B).EvenIntegralCohomology ↦ PowerSeries.coeff (R := _) j φ j)
    (X_mul_derivative_chernSeries_chernClassVec G E)
  simp only at hX
  -- The left side is `j c_j`.
  have hL : (PowerSeries.coeff (R := (TopCat.of B).EvenIntegralCohomology) j (PowerSeries.X *
      PowerSeries.derivative (chernSeries (chernClassVec G E)))) j = j • chernClass G E j := by
    obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
    rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative, chernSeries_chernClass,
      PowerSeries.coeff_mk, ← Nat.cast_succ, ← nsmul_eq_mul', DFinsupp.smul_apply,
      DirectSum.of_eq_same]
  have hneg : ∀ (x : (TopCat.of B).EvenIntegralCohomology) (n : ℕ),
      ((-1) ^ n * x) j = ((-1 : ℤ) ^ n) • x j := fun x n ↦ by
    rw [show ((-1) ^ n : (TopCat.of B).EvenIntegralCohomology) = (((-1 : ℤ) ^ n : ℤ) : _) by simp,
      ← zsmul_eq_mul, DFinsupp.zsmul_apply]
  -- On the right side only the term `c₀ (-1)^(j+1) s_j` survives.
  rw [hL, PowerSeries.coeff_mul, DirectSum.sum_apply, Finset.sum_eq_single (0, j)] at hX
  · rw [chernSeries_chernClass, PowerSeries.coeff_mk, PowerSeries.coeff_mk] at hX
    simp only [hj, ↓reduceIte] at hX
    rw [chernClass_zero, TopCat.evenIntegralCohomologyOf_one, one_mul, hneg,
      ← newtonClass_eq_newtonSum] at hX
    rw [mul_smul, natCast_zsmul, hX, smul_smul, ← pow_add,
      show j - 1 + (j + 1) = 2 * j by omega, pow_mul, neg_one_sq, one_pow, one_smul]
  · rintro ⟨a, b⟩ hab hne
    rw [Finset.mem_antidiagonal] at hab
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp [PowerSeries.coeff_mk]
    have ha : 0 < a := by
      rcases Nat.eq_zero_or_pos a with rfl | ha
      · exact absurd (by simpa using hab) hne
      · exact ha
    subst hab
    rw [chernSeries_chernClass, PowerSeries.coeff_mk,
      TopCat.evenIntegralCohomologyOf_mul_apply]
    exact h a b rfl ha hb _ _
  · simp

end SymplecticGeometry.Bundle

end

end
