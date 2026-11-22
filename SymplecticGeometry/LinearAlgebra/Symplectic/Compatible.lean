/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Tactic.TFAE
public import SymplecticGeometry.Geometry.Symplectic.Darboux.EuclideanBasis
public import SymplecticGeometry.LinearAlgebra.ComplexStructure.Action
public import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Basic
public import SymplecticGeometry.LinearAlgebra.Symplectic.Subspace
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
* `TauCeti.SymplecticForm.isDarbouxBasis_iff_apply_apply_eq_ite`: a basis
  `(v₁, J v₁, …, vₙ, J vₙ)` is a Darboux basis of `ω` exactly when it is orthonormal for
  `ω(·, J ·)`.
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
* `TauCeti.SymplecticForm.compatible_iff_tames_and_isLagrangian_map`: `J` is compatible with
  `ω` exactly when `ω` tames `J` and the image under `J` of each Lagrangian is Lagrangian. The
  converse rests on `TauCeti.SymplecticForm.Tames.invariant_of_forall_isLagrangian_map`.
* `SymplecticGeometry.compatible_iff_exists_isSymplectomorphism_stdForm`: in dimension `2 n`,
  `J` is compatible with `ω` exactly when some linear isomorphism `Ψ : ℝ²ⁿ ≃ V` has
  `Ψ^* ω = ω₀` and `Ψ J₀ = J Ψ`. So two compatible structures are conjugate by a linear
  symplectomorphism (`TauCeti.SymplecticForm.Compatible.exists_isSymplectomorphism_transport_eq`).
* `SymplecticGeometry.compatible_tfae`: the six conditions above are equivalent.
* `TauCeti.SymplecticForm.Tames.lineMap`: the form `(1 - t) ω₀ + t ω₁`, for `t ∈ [0, 1]` and
  two forms that tame one `J`; it tames `J` too (`TauCeti.SymplecticForm.Tames.tames_lineMap`).

It also relates images under `J` to orthogonals for the metric `g_J`:

* `TauCeti.SymplecticForm.Invariant.orthogonal_map`: for `J`-invariant `ω`, the symplectic
  complement of `J U` is the `g_J`-orthogonal of `U`;
* `TauCeti.SymplecticForm.Invariant.isIsotropic_map`: for `J`-invariant `ω`, `J` maps isotropic
  subspaces to isotropic subspaces;
* `TauCeti.SymplecticForm.Compatible.isCompl_orthogonal_associatedBilinForm`: in finite
  dimension, for compatible `J`, each subspace is a complement of its `g_J`-orthogonal.

Only the Darboux-basis and standard-model statements, the list that collects them, and
`TauCeti.SymplecticForm.Compatible.isCompl_orthogonal_associatedBilinForm` assume finite
dimension.

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

/-- For a basis `b` indexed like a Darboux basis, with `b (k, 1) = J (b (k, 0))`, `b` is a
Darboux basis of `ω` exactly when the metric `ω(·, J ·)` is the Kronecker delta on `b`. -/
theorem isDarbouxBasis_iff_apply_apply_eq_ite {n : ℕ} {b : Basis (Fin n × Fin 2) ℝ V}
    (hbJ : ∀ k, b (k, 1) = J (b (k, 0))) :
    ω.IsDarbouxBasis b ↔ ∀ x y, ω (b x) (J (b y)) = if x = y then 1 else 0 := by
  refine ⟨fun hb ↦ hb.apply_apply_eq_ite hbJ, fun h ↦ ⟨fun i j ↦ ?_, fun i j ↦ ?_, fun i j ↦ ?_⟩⟩
  · have hJ₁ : J (b (j, 1)) = -b (j, 0) := by rw [hbJ, J.apply_apply]
    simpa [hJ₁] using h (i, 0) (j, 1)
  · simpa [← hbJ] using h (i, 1) (j, 0)
  · simpa [← hbJ] using h (i, 0) (j, 0)

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

section Lagrangian

variable {ω : SymplecticForm V} {J : AlmostComplexStructure V}

/-- A complex structure that leaves `ω` invariant maps Lagrangian subspaces to Lagrangian
subspaces. -/
theorem Invariant.isLagrangian_map (h : ω.Invariant J) {L : Submodule ℝ V}
    (hL : ω.IsLagrangian L) : ω.IsLagrangian (L.map J.toLinearMap) :=
  (isLagrangian_map_iff_of_apply_eq_mul J.linearEquiv one_ne_zero fun v w ↦ by
    rw [one_mul]
    exact (ω.invariant_iff J).1 h v w).2 hL

/-- If a linear map `f` sends the Lagrangian subspaces of `ω` to Lagrangian subspaces of `ω'`,
then it sends `ω`-orthogonal pairs to `ω'`-orthogonal pairs: `ω(v, w) = 0` implies
`ω'(f v, f w) = 0`. -/
theorem apply_apply_eq_zero_of_forall_isLagrangian_map {W : Type*} [AddCommGroup W]
    [Module ℝ W] {ω' : SymplecticForm W} {f : V →ₗ[ℝ] W}
    (h : ∀ L : Submodule ℝ V, ω.IsLagrangian L → ω'.IsLagrangian (L.map f))
    {v w : V} (hvw : ω v w = 0) : ω' (f v) (f w) = 0 := by
  have hwv : ω w v = 0 := ω.isRefl v w hvw
  have hiso : ω.IsIsotropic (Submodule.span ℝ {v, w}) := by
    refine isIsotropic_span_iff.2 ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro a (rfl | rfl) b (rfl | rfl) <;> simp [hvw, hwv, ω.isAlt.self_eq_zero]
  obtain ⟨L, hle, hL⟩ := hiso.exists_le_isLagrangian
  exact (h L hL).symplecticForm_apply_eq_zero
    (Submodule.mem_map_of_mem (hle (Submodule.subset_span (by simp))))
    (Submodule.mem_map_of_mem (hle (Submodule.subset_span (by simp))))

/-- A complex structure that is tamed by `ω` and maps Lagrangian subspaces to Lagrangian
subspaces leaves `ω` invariant. -/
theorem Tames.invariant_of_forall_isLagrangian_map (hJ : ω.Tames J)
    (h : ∀ L : Submodule ℝ V, ω.IsLagrangian L → ω.IsLagrangian (L.map J.toLinearMap)) :
    ω.Invariant J := by
  refine (ω.invariant_iff J).2 fun v w ↦ ?_
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  -- `ω(J v, J ·)` vanishes on the kernel of `ω(v, ·)`, so it is `c • ω(v, ·)`; its value at
  -- `J v`, with `ω(v, J v) > 0`, gives `c = 1`.
  have hker : ⨅ _ : Unit, LinearMap.ker (ω.toBilinForm v) ≤
      LinearMap.ker ((ω.toBilinForm (J v)).comp J.toLinearMap) := fun u hu ↦ by
    simpa using apply_apply_eq_zero_of_forall_isLagrangian_map (f := J.toLinearMap) h
      (by simpa using hu)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1
    (by simpa using mem_span_of_iInf_ker_le_ker hker)
  have hc' (u : V) : c * ω v u = ω (J v) (J u) := by
    simpa using LinearMap.congr_fun hc u
  have hc1 : c = 1 := by
    have h₁ : c * ω v (J v) = ω (J v) (J (J v)) := hc' (J v)
    have h₂ : ω (J v) (J (J v)) = ω v (J v) := by
      rw [J.apply_apply]
      exact (LinearMap.map_neg (ω.toBilinForm (J v)) v).trans (ω.neg_eq (J v) v)
    rw [h₂] at h₁
    exact mul_right_cancel₀ (hJ v hv).ne' (h₁.trans (one_mul _).symm)
  rw [← hc' w, hc1, one_mul]

/-- `J` is compatible with `ω` exactly when `ω` tames `J` and the image under `J` of each
Lagrangian subspace is Lagrangian. -/
theorem compatible_iff_tames_and_isLagrangian_map :
    ω.Compatible J ↔ ω.Tames J ∧
      ∀ L : Submodule ℝ V, ω.IsLagrangian L → ω.IsLagrangian (L.map J.toLinearMap) :=
  ⟨fun h ↦ ⟨h.tames, fun _ ↦ h.invariant.isLagrangian_map⟩,
    fun ⟨hJ, h⟩ ↦ .of_tames (hJ.invariant_of_forall_isLagrangian_map h) hJ⟩

end Lagrangian

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

section Orthogonal

variable {ω : SymplecticForm V} {J : AlmostComplexStructure V}

/-- For a `J`-invariant form, the symplectic complement of `J U` is the orthogonal of `U` for the
associated form `g = ω(·, J ·)`. -/
theorem Invariant.orthogonal_map (hJ : ω.Invariant J) (U : Submodule ℝ V) :
    ω.orthogonal (U.map J.toLinearMap) = (ω.associatedBilinForm J).orthogonal U := by
  ext x
  simp only [mem_orthogonal_iff, LinearMap.BilinForm.mem_orthogonal_iff,
    associatedBilinForm_apply, Submodule.mem_map]
  refine ⟨fun h u hu => ?_, ?_⟩
  · linarith [hJ.apply_add_apply_eq_zero u x, h _ ⟨u, hu, rfl⟩]
  · rintro h _ ⟨u, hu, rfl⟩
    linarith [hJ.apply_add_apply_eq_zero u x, h u hu]

/-- For a `J`-invariant form, the image under `J` of an isotropic subspace is isotropic. -/
theorem Invariant.isIsotropic_map (hJ : ω.Invariant J) {U : Submodule ℝ V}
    (hU : ω.IsIsotropic U) : ω.IsIsotropic (U.map J.toLinearMap) := by
  rw [isIsotropic_iff] at hU ⊢
  rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
  exact ((ω.invariant_iff J).1 hJ u v).trans (hU u hu v hv)

/-- For a compatible pair on a finite-dimensional space, every subspace is complementary to its
orthogonal for the associated inner product `g = ω(·, J ·)`. -/
theorem Compatible.isCompl_orthogonal_associatedBilinForm [FiniteDimensional ℝ V]
    (hJ : ω.Compatible J) (U : Submodule ℝ V) :
    IsCompl U ((ω.associatedBilinForm J).orthogonal U) := by
  refine (LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint
    (fun x y h => by rw [hJ.associatedBilinForm_isSymm.eq, h])).2 ?_
  rw [Submodule.disjoint_def]
  exact fun x hx hx' => hJ.associatedBilinForm_self_eq_zero.1
    (LinearMap.BilinForm.mem_orthogonal_iff.1 hx' x hx)

end Orthogonal

end TauCeti.SymplecticForm

namespace SymplecticGeometry

open TauCeti TauCeti.SymplecticForm Module

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {ω : SymplecticForm V}
  {J : AlmostComplexStructure V} {ι : Type*} [Fintype ι]

/-- A linear isomorphism `Ψ : ℝ²ⁿ ≃ V` with `Ψ^* ω = ω₀` and `Ψ J₀ = J Ψ` makes `J` compatible
with `ω`. -/
theorem compatible_of_isSymplectomorphism_stdForm {Ψ : StdSpace ι ≃ₗ[ℝ] V}
    (hΨ : IsSymplectomorphism (stdForm ι) ω Ψ)
    (hJ : IsComplexLinearMap (stdComplexStructure ι) J Ψ.toLinearMap) : ω.Compatible J := by
  rw [← isSymplectomorphism_iff_transport_eq.1 hΨ,
    ← (AlmostComplexStructure.transport_eq_iff_isComplexLinearMap Ψ).2 hJ]
  exact stdForm_compatible.transport Ψ

/-- In dimension `2 n`, with `n` the cardinality of `ι`, `J` is compatible with `ω` exactly
when some linear isomorphism `Ψ : ℝ²ⁿ ≃ V` from the standard model is a symplectomorphism from
`ω₀` to `ω` and complex linear from `J₀` to `J`: `Ψ^* ω = ω₀` and `Ψ^* J = J₀`. -/
theorem compatible_iff_exists_isSymplectomorphism_stdForm [FiniteDimensional ℝ V]
    (hι : finrank ℝ V = 2 * Fintype.card ι) :
    ω.Compatible J ↔ ∃ Ψ : StdSpace ι ≃ₗ[ℝ] V, IsSymplectomorphism (stdForm ι) ω Ψ ∧
      IsComplexLinearMap (stdComplexStructure ι) J Ψ.toLinearMap := by
  refine ⟨fun h ↦ ?_, fun ⟨Ψ, hΨ, hJ⟩ ↦ compatible_of_isSymplectomorphism_stdForm hΨ hJ⟩
  obtain ⟨n, b, hb, hbJ⟩ := compatible_iff_exists_isDarbouxBasis.1 h
  have hn : Fintype.card ι = n := by
    have := finrank_eq_card_basis b
    simp only [Fintype.card_prod, Fintype.card_fin] at this
    omega
  let σ : ι ≃ Fin n := Fintype.equivFinOfCardEq hn
  have hDs := (b.isComplexLinearMap_darbouxBasisEquiv hbJ).symm_linearEquiv
  refine ⟨(LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (σ.sumCongr σ)).toLinearEquiv.trans
      ((EuclideanSpace.sumEquivProd (𝕜 := ℝ)).toLinearEquiv.trans b.darbouxBasisEquiv.symm),
    (isSymplectomorphism_piLpCongrLeft_sumCongr σ).trans
      (isSymplectomorphism_sumEquivProd.trans hb.isSymplectomorphism_darbouxBasisEquiv.symm), ?_⟩
  exact (hDs.comp isComplexLinearMap_sumEquivProd).comp
    (isComplexLinearMap_piLpCongrLeft_sumCongr σ)

/-- In finite dimension, any two complex structures compatible with `ω` are conjugate by a linear
symplectomorphism of `(V, ω)`: some `Ψ` with `Ψ^* ω = ω` has `Ψ J Ψ⁻¹ = J'`. -/
theorem _root_.TauCeti.SymplecticForm.Compatible.exists_isSymplectomorphism_transport_eq
    [FiniteDimensional ℝ V] {J' : AlmostComplexStructure V} (hJ : ω.Compatible J)
    (hJ' : ω.Compatible J') :
    ∃ Ψ : V ≃ₗ[ℝ] V, ω.IsSymplectomorphism ω Ψ ∧ J.transport Ψ = J' := by
  obtain ⟨n, hn⟩ := J.even_finrank_real
  have hι : finrank ℝ V = 2 * Fintype.card (Fin n) := by
    rw [Fintype.card_fin]
    omega
  obtain ⟨Φ, hΦ, hΦJ⟩ := (compatible_iff_exists_isSymplectomorphism_stdForm hι).1 hJ
  obtain ⟨Φ', hΦ', hΦJ'⟩ := (compatible_iff_exists_isSymplectomorphism_stdForm hι).1 hJ'
  refine ⟨Φ.symm.trans Φ', hΦ.symm.trans hΦ', ?_⟩
  rw [← (AlmostComplexStructure.transport_eq_iff_isComplexLinearMap Φ).2 hΦJ,
    ← (AlmostComplexStructure.transport_eq_iff_isComplexLinearMap Φ').2 hΦJ',
    ← AlmostComplexStructure.transport_trans, AlmostComplexStructure.transport_symm_transport]

/-- **Characterizations of compatible complex structures.** Let `ω` be a symplectic form and `J`
a complex structure on a real vector space `V` of dimension `2 n`, with `n` the cardinality of
`ι`. The following are equivalent:
1. `J` is compatible with `ω`;
2. `ω` has a Darboux basis `(v₁, J v₁, …, vₙ, J vₙ)`;
3. some linear isomorphism `Ψ : ℝ²ⁿ ≃ V` has `Ψ^* ω = ω₀` and `Ψ^* J = J₀`;
4. `ω` tames `J` (`ω(v, J v) > 0` when `v ≠ 0`), and `J` sends each Lagrangian to a Lagrangian;
5. the bilinear form `g_J(v, w) = ω(v, J w)` is symmetric, positive definite and `J`-invariant;
6. `H(v, w) = ω(v, J w) + i ω(v, w)` is the inner product of an `InnerProductSpace.Core ℂ V`
   for the complex structure `J`.

Milestone: *Characterizations of compatible complex structures*. -/
theorem compatible_tfae [FiniteDimensional ℝ V] (hι : finrank ℝ V = 2 * Fintype.card ι) :
    List.TFAE [ω.Compatible J,
      ∃ (n : ℕ) (b : Basis (Fin n × Fin 2) ℝ V), ω.IsDarbouxBasis b ∧
        ∀ k, b (k, 1) = J (b (k, 0)),
      ∃ Ψ : StdSpace ι ≃ₗ[ℝ] V, IsSymplectomorphism (stdForm ι) ω Ψ ∧
        IsComplexLinearMap (stdComplexStructure ι) J Ψ.toLinearMap,
      ω.Tames J ∧
        ∀ L : Submodule ℝ V, ω.IsLagrangian L → ω.IsLagrangian (L.map J.toLinearMap),
      (ω.associatedBilinForm J).IsSymm ∧ (ω.associatedBilinForm J).toQuadraticMap.PosDef ∧
        ∀ v w, ω.associatedBilinForm J (J v) (J w) = ω.associatedBilinForm J v w,
      ∃ c : (letI := J.complexModule; InnerProductSpace.Core ℂ V),
        ∀ v w, c.inner v w = ω.complexAssociatedForm J v w] := by
  tfae_have 1 ↔ 2 := compatible_iff_exists_isDarbouxBasis
  tfae_have 1 ↔ 3 := compatible_iff_exists_isSymplectomorphism_stdForm hι
  tfae_have 1 ↔ 4 := compatible_iff_tames_and_isLagrangian_map
  tfae_have 1 ↔ 5 := compatible_iff_associatedBilinForm
  tfae_have 1 ↔ 6 := compatible_iff_exists_innerProductCore
  tfae_finish

end SymplecticGeometry

end
