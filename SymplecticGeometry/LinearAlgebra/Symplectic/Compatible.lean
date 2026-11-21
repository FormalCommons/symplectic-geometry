/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hermitian
public import TauCeti.Geometry.Symplectic.WeightDecomposition

/-!
# Characterizations of compatible complex structures

For a symplectic form `ω` and a complex structure `J` on a real vector space `V`, Tau Ceti
defines compatibility (`TauCeti.SymplecticForm.Compatible`: `ω` is `J`-invariant and
`v ↦ ω(v, J v)` is positive definite), the metric `g_J(v, w) = ω(v, J w)`
(`TauCeti.SymplecticForm.associatedBilinForm`) and the Hermitian form
`H(v, w) = ω(v, J w) + i ω(v, w)` (`TauCeti.SymplecticForm.complexAssociatedForm`), and proves
that compatibility makes `g_J` symmetric and `H` a Hermitian inner product. This file proves the
converses.

## Main results

* `TauCeti.SymplecticForm.compatible_iff_exists_isDarbouxBasis`: in finite dimension, `J` is
  compatible with `ω` exactly when `ω` has a Darboux basis `(v₁, J v₁, …, vₙ, J vₙ)`.
* `TauCeti.SymplecticForm.invariant_iff_isSymm_associatedBilinForm`: `ω` is `J`-invariant
  exactly when `g_J` is symmetric.
* `TauCeti.SymplecticForm.compatible_iff_isSymm_and_posDef_associatedBilinForm`: `J` is
  compatible with `ω` exactly when `g_J` is symmetric and positive definite.
* `TauCeti.SymplecticForm.compatible_iff_associatedBilinForm`: `J` is compatible with `ω`
  exactly when `g_J` is a `J`-invariant inner product.
* `TauCeti.SymplecticForm.invariant_iff_complexAssociatedForm_conj_symm`: `ω` is `J`-invariant
  exactly when `H` is conjugate symmetric.
* `TauCeti.SymplecticForm.compatible_iff_exists_innerProductCore`: `J` is compatible with `ω`
  exactly when `H` is a Hermitian inner product on the complex vector space `(V, J)`.
* `TauCeti.SymplecticForm.Tames.lineMap`: the form `(1 - t) ω₀ + t ω₁`, for `t ∈ [0, 1]` and
  two forms that tame one `J`; it tames `J` too (`TauCeti.SymplecticForm.Tames.tames_lineMap`).

Apart from the Darboux-basis statement, nothing here assumes finite dimension.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Exercise 2.5.3 and Proposition 2.5.4.
-/

public section

namespace TauCeti.SymplecticForm

open Module

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

section Characterizations

variable {ω : SymplecticForm V} {J : AlmostComplexStructure V}

/-- If the metric `g_J(v, w) = ω(v, J w)` is symmetric, then `ω` is `J`-invariant. -/
theorem invariant_of_isSymm_associatedBilinForm (h : (ω.associatedBilinForm J).IsSymm) :
    ω.Invariant J := by
  refine (ω.invariant_iff J).2 fun v w ↦ ?_
  have h₁ := h.eq v (J w)
  have h₂ := ω.neg_eq (J w) (J v)
  simp only [associatedBilinForm_apply, AlmostComplexStructure.apply_apply, map_neg] at h₁ h₂ ⊢
  linarith

/-- A symplectic form is `J`-invariant exactly when its metric `g_J(v, w) = ω(v, J w)` is
symmetric. -/
theorem invariant_iff_isSymm_associatedBilinForm :
    ω.Invariant J ↔ (ω.associatedBilinForm J).IsSymm :=
  ⟨Invariant.associatedBilinForm_isSymm, invariant_of_isSymm_associatedBilinForm⟩

/-- `J` is compatible with `ω` exactly when `g_J(v, w) = ω(v, J w)` is symmetric and positive
definite. -/
theorem compatible_iff_isSymm_and_posDef_associatedBilinForm :
    ω.Compatible J ↔ (ω.associatedBilinForm J).IsSymm ∧
      (ω.associatedBilinForm J).toQuadraticMap.PosDef := by
  rw [compatible_iff, invariant_iff_isSymm_associatedBilinForm, tames_iff_associated_pos]

/-- `J` is compatible with `ω` exactly when `g_J(v, w) = ω(v, J w)` is a `J`-invariant inner
product: symmetric, positive definite, and unchanged when `J` is applied to both arguments. -/
theorem compatible_iff_associatedBilinForm :
    ω.Compatible J ↔ (ω.associatedBilinForm J).IsSymm ∧
      (ω.associatedBilinForm J).toQuadraticMap.PosDef ∧
      ∀ v w, ω.associatedBilinForm J (J v) (J w) = ω.associatedBilinForm J v w :=
  ⟨fun h ↦ ⟨h.associatedBilinForm_isSymm, h.positive, h.associatedBilinForm_invariant⟩,
    fun h ↦ compatible_iff_isSymm_and_posDef_associatedBilinForm.2 ⟨h.1, h.2.1⟩⟩

/-- A symplectic form is `J`-invariant exactly when its Hermitian form
`H(v, w) = ω(v, J w) + i ω(v, w)` is conjugate symmetric. -/
theorem invariant_iff_complexAssociatedForm_conj_symm :
    ω.Invariant J ↔ ∀ v w,
      starRingEnd ℂ (ω.complexAssociatedForm J w v) = ω.complexAssociatedForm J v w := by
  refine ⟨Invariant.complexAssociatedForm_conj_symm, fun h ↦ ?_⟩
  refine invariant_of_isSymm_associatedBilinForm ⟨fun v w ↦ ?_⟩
  have h₁ := congrArg Complex.re (h w v)
  rw [Complex.conj_re, complexAssociatedForm_re, complexAssociatedForm_re] at h₁
  simpa using h₁

/-- `J` is compatible with `ω` exactly when some `InnerProductSpace.Core ℂ V`, for the complex
structure `J.complexModule`, has `H(v, w) = ω(v, J w) + i ω(v, w)` as its inner product.
The forward direction is Tau Ceti's `TauCeti.SymplecticForm.Compatible.hermitianCore`. -/
theorem compatible_iff_exists_innerProductCore :
    ω.Compatible J ↔ ∃ c : (letI := J.complexModule; InnerProductSpace.Core ℂ V),
      ∀ v w, c.inner v w = ω.complexAssociatedForm J v w := by
  let := J.complexModule
  refine ⟨fun h ↦ ⟨h.hermitianCore, fun v w ↦ (h.hermitianCore_inner v w).trans
    (complexAssociatedForm_apply ω J v w).symm⟩, fun ⟨c, hc⟩ ↦ ?_⟩
  refine Compatible.of_tames (invariant_iff_complexAssociatedForm_conj_symm.2 fun v w ↦ ?_)
    fun v hv ↦ ?_
  · rw [← hc, ← hc]
    exact c.conj_inner_symm v w
  · have hre : 0 ≤ (ω.complexAssociatedForm J v v).re := by
      rw [← hc]
      exact c.re_inner_nonneg v
    have hne : ω.complexAssociatedForm J v v ≠ 0 := by
      rw [← hc]
      exact fun h ↦ hv (c.definite v h)
    rw [complexAssociatedForm_self, Complex.ofReal_ne_zero] at hne
    rw [complexAssociatedForm_self, Complex.ofReal_re] at hre
    exact lt_of_le_of_ne hre (Ne.symm hne)

/-- For a basis `b` indexed like a Darboux basis, with `b (k, 1) = J (b (k, 0))`, the metric
`ω(·, J ·)` is the Kronecker delta on `b` when `b` is a Darboux basis of `ω`. -/
theorem IsDarbouxBasis.apply_apply_eq_ite {n : ℕ} {b : Basis (Fin n × Fin 2) ℝ V}
    (hb : ω.IsDarbouxBasis b) (hbJ : ∀ k, b (k, 1) = J (b (k, 0))) (x y : Fin n × Fin 2) :
    ω (b x) (J (b y)) = if x = y then 1 else 0 := by
  obtain ⟨i, a⟩ := x
  obtain ⟨j, c⟩ := y
  have hJ₁ : J (b (j, 1)) = -b (j, 0) := by rw [hbJ, J.apply_apply]
  fin_cases a <;> fin_cases c
  · simp [← hbJ, hb.apply_fst_snd]
  · simp [hJ₁, hb.apply_fst_fst]
  · simp [← hbJ, hb.apply_snd_snd]
  · simp [hJ₁, hb.apply_snd_fst, apply_ite]

/-- A Darboux basis of the form `(v₁, J v₁, …, vₙ, J vₙ)` makes `J` compatible with `ω`. -/
theorem IsDarbouxBasis.compatible {n : ℕ} {b : Basis (Fin n × Fin 2) ℝ V}
    (hb : ω.IsDarbouxBasis b) (hbJ : ∀ k, b (k, 1) = J (b (k, 0))) : ω.Compatible J := by
  have hδ := hb.apply_apply_eq_ite hbJ
  have hsymm : (ω.associatedBilinForm J).IsSymm :=
    (LinearMap.BilinForm.isSymm_iff_basis b).2 fun x y ↦ by simp [hδ, eq_comm]
  refine compatible_iff_isSymm_and_posDef_associatedBilinForm.2 ⟨hsymm, ?_⟩
  have h1 : LinearMap.BilinForm.toMatrix b (ω.associatedBilinForm J) = 1 := by
    ext x y
    simp [LinearMap.BilinForm.toMatrix_apply, hδ, Matrix.one_apply]
  rw [LinearMap.BilinForm.posDef_toQuadraticMap_iff_matrix b _ hsymm, h1]
  exact Matrix.PosDef.one

/-- In finite dimension, `J` is compatible with `ω` exactly when `ω` has a Darboux basis
`(v₁, J v₁, …, vₙ, J vₙ)`, with `vₖ = b (k, 0)` and `J vₖ = b (k, 1)`. -/
theorem compatible_iff_exists_isDarbouxBasis [FiniteDimensional ℝ V] :
    ω.Compatible J ↔ ∃ (n : ℕ) (b : Basis (Fin n × Fin 2) ℝ V),
      ω.IsDarbouxBasis b ∧ ∀ k, b (k, 1) = J (b (k, 0)) := by
  refine ⟨fun h ↦ ?_, fun ⟨_, _, hb, hbJ⟩ ↦ hb.compatible hbJ⟩
  obtain ⟨n, b, -, hb, hbJ, -⟩ := exists_isDarbouxBasis_forall_apply_eq_of_pairwise_commute h
    (Empty.elim : Empty → V →ₗ[ℝ] V) (fun i ↦ i.elim) (fun i ↦ i.elim) (fun i ↦ i.elim)
  exact ⟨n, b, hb, hbJ⟩

end Characterizations

section LineMap

variable {ω₀ ω₁ : SymplecticForm V} {J : AlmostComplexStructure V} {t : ℝ}

private theorem Tames.lineMap_pos (h₀ : ω₀.Tames J) (h₁ : ω₁.Tames J)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) {v : V} (hv : v ≠ 0) :
    0 < ((1 - t) • ω₀.toBilinForm + t • ω₁.toBilinForm) v (J v) := by
  have a := h₀ v hv
  have b := h₁ v hv
  simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  rcases ht.2.lt_or_eq with ht' | rfl
  · nlinarith [mul_pos (sub_pos.2 ht') a, mul_nonneg ht.1 b.le]
  · simpa using b

/-- The straight line `(1 - t) ω₀ + t ω₁`, for `t ∈ [0, 1]`, between two symplectic forms that
tame the same complex structure `J`. It is a symplectic form, and it tames `J`
(`TauCeti.SymplecticForm.Tames.tames_lineMap`). The name follows Mathlib's `AffineMap.lineMap`,
whose value at `t` is the same combination. -/
def Tames.lineMap (h₀ : ω₀.Tames J) (h₁ : ω₁.Tames J) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    SymplecticForm V :=
  ofTames ((1 - t) • ω₀.toBilinForm + t • ω₁.toBilinForm)
    ((ω₀.isAlt.smul (1 - t)).add (ω₁.isAlt.smul t)) fun _ hv ↦ lineMap_pos h₀ h₁ ht hv

/-- The underlying bilinear form of `Tames.lineMap` is `(1 - t) ω₀ + t ω₁`. -/
@[simp]
theorem Tames.toBilinForm_lineMap (h₀ : ω₀.Tames J) (h₁ : ω₁.Tames J)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (h₀.lineMap h₁ ht).toBilinForm = (1 - t) • ω₀.toBilinForm + t • ω₁.toBilinForm :=
  ofTames_toBilinForm _ _

/-- The straight line between two forms that tame `J` consists of forms that tame `J`. -/
theorem Tames.tames_lineMap (h₀ : ω₀.Tames J) (h₁ : ω₁.Tames J)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : (h₀.lineMap h₁ ht).Tames J :=
  tames_ofTames _ _

/-- At `t = 0` the straight line `Tames.lineMap` starts at `ω₀`. -/
@[simp]
theorem Tames.lineMap_zero (h₀ : ω₀.Tames J) (h₁ : ω₁.Tames J)
    (ht : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1) : h₀.lineMap h₁ ht = ω₀ :=
  toBilinForm_injective (by simp)

/-- At `t = 1` the straight line `Tames.lineMap` ends at `ω₁`. -/
@[simp]
theorem Tames.lineMap_one (h₀ : ω₀.Tames J) (h₁ : ω₁.Tames J)
    (ht : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1) : h₀.lineMap h₁ ht = ω₁ :=
  toBilinForm_injective (by simp)

end LineMap

end TauCeti.SymplecticForm

end
