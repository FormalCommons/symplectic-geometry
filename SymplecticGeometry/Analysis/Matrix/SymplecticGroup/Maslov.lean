/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Analysis.Matrix.Polar.Basic
public import SymplecticGeometry.Analysis.Matrix.SymplecticGroup.FundamentalGroup
public import SymplecticGeometry.LinearAlgebra.Matrix.Realify
public import SymplecticGeometry.Topology.Algebra.SymplecticGroup
public import SymplecticGeometry.Topology.Homotopy.Path
public import TauCeti.Topology.Homotopy.Path

/-!
# The Maslov index of loops of symplectic matrices: classification and uniqueness

Tau Ceti defines the Maslov index `μ(Ψ) = deg(ρ ∘ Ψ)` of a loop `Ψ` in
`Sp(2n) = TauCeti.GLSymplectic ι ℝ` (`TauCeti.GLSymplectic.maslovIndex`), where
`ρ = TauCeti.GLSymplectic.maslovPhase` is the complex determinant of the orthogonal polar factor,
and proves that it is invariant under homotopy and additive under products and direct sums. This
file proves the converse of homotopy invariance and the uniqueness of a function on loops with
these properties, following McDuff and Salamon, Theorem 2.2.12.

Loops are `Path A A`, and two loops `γ : Path A A`, `γ' : Path B B` are *freely homotopic* when
`(γ : C(I, X)).HomotopicWith γ' fun p ↦ p 0 = p 1`: homotopic through loops whose base point may
move.

* **Classification.** Two loops at the same point are homotopic with fixed ends exactly when they
  have the same Maslov index (`TauCeti.GLSymplectic.maslovIndex_eq_iff_homotopic`), since `ρ` is
  an isomorphism on fundamental groups (`TauCeti.GLSymplectic.fundamentalGroupMulEquiv_fromPath`).
  Conjugating along a path between the base points gives the same statement for free homotopy
  (`TauCeti.GLSymplectic.homotopicWith_iff_maslovIndex_eq`); it holds in every dimension,
  including `n = 0`, where `Sp(0)` is a point.
* **Uniqueness.** A family `μ n` of integer-valued functions on loops in `Sp(2n)`, `n : ℕ`,
  indexed by `Fin n`, satisfies the homotopy, product, direct-sum and normalization axioms
  (`SymplecticGeometry.IsMaslovIndex`) exactly when it is `Ψ ↦ deg(ρ ∘ Ψ)`
  (`SymplecticGeometry.isMaslovIndex_iff`). The direct sum of loops in dimensions `n` and `m` is
  read in dimension `n + m` through `TauCeti.GLSymplectic.reindex` along `finSumFinEquiv`, and the
  normalization uses the loop `t ↦ e^{2πit}` in `U(1) ⊆ Sp(2)`
  (`SymplecticGeometry.symplecticRotationLoop 1`). The axioms force `μ = 0` on the constant loop
  (it is its own square) and `μ = k` on `t ↦ e^{2πikt}`, and every loop in `Sp(2(n + 1))` is freely
  homotopic to the direct sum of a constant loop and one of these
  (`SymplecticGeometry.homotopicWith_reindex_sum_symplecticRotationLoop`).

## Main definitions

* `SymplecticGeometry.symplecticRotationLoop k`: the loop `t ↦ e^{2πikt}` in `U(1) ⊆ Sp(2)`.
* `SymplecticGeometry.IsMaslovIndex`: the axioms of the Maslov index of symplectic loops.

## Main results

* `TauCeti.GLSymplectic.maslovPhase_reindex`, `TauCeti.GLSymplectic.maslovIndex_reindex`:
  reindexing keeps `ρ` and the Maslov index.
* `TauCeti.GLSymplectic.maslovIndex_eq_iff_homotopic`,
  `TauCeti.GLSymplectic.homotopicWith_iff_maslovIndex_eq`: the Maslov index classifies loops up
  to homotopy with fixed ends and up to free homotopy.
* `SymplecticGeometry.isMaslovIndex_iff`: existence, uniqueness and the formula `μ = deg(ρ ∘ Ψ)`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Section 2.2, Theorem 2.2.12.
-/

public section

open Matrix Matrix.UnitaryGroup
open scoped unitInterval

namespace TauCeti.GLSymplectic

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-! ### Reindexing -/

/-- The orthogonal polar factor of a reindexed symplectic matrix is the realification of the
reindexed unitary matrix whose realification is the orthogonal polar factor of the matrix. -/
private theorem polarUnitary_reindex (e : ι ≃ κ) (A : GLSymplectic ι ℝ) :
    polarUnitary (reindex ℝ e A) = unitaryGroupEquivSymplecticInfOrthogonal
      (unitaryReindexContinuousMulEquiv ℂ e
        (unitaryGroupEquivSymplecticInfOrthogonal.symm (polarUnitary A))) := by
  have hV := congrArg Units.val
    (realify_toUnits_unitaryGroupEquivSymplecticInfOrthogonal_symm_apply (polarUnitary A))
  rw [GeneralLinearGroup.coe_realify, Unitary.val_toUnits_apply] at hV
  refine Subtype.ext (Units.ext ?_)
  rw [coe_polarUnitary, coe_reindex, GeneralLinearGroup.coe_polarUnitary_reindex,
    ← coe_polarUnitary, ← hV, unitaryGroupEquivSymplecticInfOrthogonal_apply,
    GeneralLinearGroup.coe_realify, Unitary.val_toUnits_apply,
    coe_unitaryReindexContinuousMulEquiv_apply, reindex_apply, reindex_apply, realify_submatrix]
  rfl

/-- Reindexing a symplectic matrix along an equivalence of index types keeps `ρ`. -/
@[simp]
theorem maslovPhase_reindex (e : ι ≃ κ) (A : GLSymplectic ι ℝ) :
    maslovPhase (reindex ℝ e A) = maslovPhase A := by
  rw [← maslovPhase_inclusion_polarUnitary, maslovPhase_inclusion, polarUnitary_reindex,
    ContinuousMulEquiv.symm_apply_apply, ← maslovPhase_inclusion_polarUnitary A,
    maslovPhase_inclusion]
  ext
  simp only [coe_detCircle, coe_unitaryReindexContinuousMulEquiv_apply, det_reindex_self]

/-- Reindexing a loop of symplectic matrices along an equivalence of index types keeps its Maslov
index. -/
@[simp]
theorem maslovIndex_reindex (e : ι ≃ κ) {A : GLSymplectic ι ℝ} (γ : Path A A) :
    maslovIndex (γ.map (continuous_reindex (R := ℝ) e)) = maslovIndex γ := by
  rw [maslovIndex_def, maslovIndex_def]
  exact Circle.degree_congr _ _ fun t ↦ by simp

/-! ### Classification of loops -/

/-- **The Maslov index classifies loops up to homotopy with fixed ends.** Two loops of symplectic
matrices at the same point are homotopic relative to their ends exactly when their Maslov indices
agree. -/
theorem maslovIndex_eq_iff_homotopic {A : GLSymplectic ι ℝ} {γ γ' : Path A A} :
    maslovIndex γ = maslovIndex γ' ↔ γ.Homotopic γ' := by
  refine ⟨fun h ↦ ?_, maslovIndex_eq_of_homotopic⟩
  cases isEmpty_or_nonempty ι
  · -- `Sp(0)` is a point, so there is only one loop.
    have hγ : γ = γ' := Path.ext (funext fun _ ↦ Subsingleton.elim _ _)
    exact hγ ▸ Path.Homotopic.refl γ
  · rw [← Path.Homotopic.Quotient.eq]
    have h' := (fundamentalGroupMulEquiv ι A).injective
      (a₁ := FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ))
      (a₂ := FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ'))
      (by rw [fundamentalGroupMulEquiv_fromPath, fundamentalGroupMulEquiv_fromPath, h])
    exact congrArg FundamentalGroup.toPath h'

/-- Loops that are freely homotopic have the same Maslov index. -/
theorem maslovIndex_eq_of_homotopicWith {A B : GLSymplectic ι ℝ} {γ : Path A A} {γ' : Path B B}
    (h : (γ : C(I, GLSymplectic ι ℝ)).HomotopicWith (γ' : C(I, GLSymplectic ι ℝ))
      fun p ↦ p 0 = p 1) :
    maslovIndex γ = maslovIndex γ' := by
  obtain ⟨F⟩ := h
  exact maslovIndex_eq_of_homotopy γ γ' F.toContinuousMap (fun t ↦ F.apply_zero t)
    (fun t ↦ F.apply_one t) fun s ↦ F.prop s

/-- **The homotopy axiom.** Two loops of symplectic matrices, at any base points, are freely
homotopic (homotopic through loops) exactly when their Maslov indices agree. -/
theorem homotopicWith_iff_maslovIndex_eq {A B : GLSymplectic ι ℝ} (γ : Path A A)
    (γ' : Path B B) :
    (γ : C(I, GLSymplectic ι ℝ)).HomotopicWith (γ' : C(I, GLSymplectic ι ℝ))
      (fun p ↦ p 0 = p 1) ↔ maslovIndex γ = maslovIndex γ' := by
  refine ⟨maslovIndex_eq_of_homotopicWith, fun h ↦ ?_⟩
  -- Conjugate `γ'` to a loop at `A` along a path from `A` to `B`.
  let χ : Path A B := PathConnectedSpace.somePath A B
  have hχ := Path.homotopicWith_trans_trans_symm χ γ'
  have hγ : γ.Homotopic ((χ.trans γ').trans χ.symm) :=
    maslovIndex_eq_iff_homotopic.1 (h.trans (maslovIndex_eq_of_homotopicWith hχ).symm)
  exact hγ.homotopicWith.trans hχ

end TauCeti.GLSymplectic

namespace SymplecticGeometry

open TauCeti TauCeti.GLSymplectic

/-! ### The rotation loops of `U(1) ⊆ Sp(2)` -/

/-- The scalar `e^{2πikt}`, as a unitary `1 × 1` matrix. -/
private noncomputable def rotationUnitary (k : ℤ) (t : ℝ) : unitaryGroup (Fin 1) ℂ :=
  ⟨(Circle.exp (2 * Real.pi * k * t) : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ),
    Unitary.smul_mem_of_mem (Circle.exp _).coe_mem_unitary (one_mem _)⟩

private theorem continuous_rotationUnitary (k : ℤ) : Continuous (rotationUnitary k) :=
  Continuous.subtype_mk (by fun_prop) _

private theorem rotationUnitary_of_int (k m : ℤ) : rotationUnitary k m = 1 := by
  refine Subtype.ext ?_
  have : Circle.exp (2 * Real.pi * k * m) = 1 := by
    rw [show 2 * Real.pi * k * m = ((k * m : ℤ) : ℝ) * (2 * Real.pi) by push_cast; ring]
    exact Circle.exp_int_mul_two_pi _
  simp [rotationUnitary, this]

/-- The loop `t ↦ e^{2πikt}` in `U(1) = Sp(2) ∩ O(2)`, as a loop of symplectic `2 × 2` matrices
at the identity. -/
noncomputable def symplecticRotationLoop (k : ℤ) : Path (1 : GLSymplectic (Fin 1) ℝ) 1 where
  toFun t := ofUnitary (rotationUnitary k t)
  continuous_toFun := continuous_ofUnitary.comp
    ((continuous_rotationUnitary k).comp continuous_subtypeVal)
  source' := by simpa using congrArg ofUnitary (rotationUnitary_of_int k 0)
  target' := by simpa using congrArg ofUnitary (rotationUnitary_of_int k 1)

/-- At time `t`, the rotation loop is the realification of the `1 × 1` matrix `e^{2πikt}`. -/
@[simp]
theorem coe_symplecticRotationLoop_apply (k : ℤ) (t : I) :
    ((symplecticRotationLoop k t : GL (Fin 1 ⊕ Fin 1) ℝ) : Matrix (Fin 1 ⊕ Fin 1) _ ℝ) =
      ((Circle.exp (2 * Real.pi * k * t) : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ)).realify :=
  coe_ofUnitary _

/-- The loop `t ↦ e^{2πikt}` in `U(1) ⊆ Sp(2)` has Maslov index `k`. -/
@[simp]
theorem maslovIndex_symplecticRotationLoop (k : ℤ) :
    maslovIndex (symplecticRotationLoop k) = k := by
  rw [maslovIndex_def]
  refine Circle.degree_eq_of_sub_eq _ (θ := fun t ↦ 2 * Real.pi * k * t) (by fun_prop)
    (fun t ↦ ?_) (by simp only [Set.Icc.coe_one, Set.Icc.coe_zero]; ring)
  apply Circle.ext
  change _ = (maslovPhase (ofUnitary (rotationUnitary k t)) : ℂ)
  simp [rotationUnitary, coe_detCircle]

/-! ### Uniqueness -/

/-- **Normal form of a loop.** A loop `γ` in `Sp(2(n + 1))` is freely homotopic to the direct sum
of the constant loop at the identity of `Sp(2n)` and the rotation loop `t ↦ e^{2πikt}` of
`U(1) ⊆ Sp(2)`, with `k` the Maslov index of `γ`, read in `Fin (n + 1)` along `finSumFinEquiv`. -/
theorem homotopicWith_reindex_sum_symplecticRotationLoop {n : ℕ}
    {A : GLSymplectic (Fin (n + 1)) ℝ} (γ : Path A A) :
    (γ : C(I, GLSymplectic (Fin (n + 1)) ℝ)).HomotopicWith
      ((((Path.refl (1 : GLSymplectic (Fin n) ℝ)).prod
        (symplecticRotationLoop (maslovIndex γ))).map continuous_sum).map
          (continuous_reindex finSumFinEquiv) : C(I, GLSymplectic (Fin (n + 1)) ℝ))
      fun p ↦ p 0 = p 1 :=
  (homotopicWith_iff_maslovIndex_eq _ _).2 (by
    rw [maslovIndex_reindex, maslovIndex_sum, maslovIndex_refl,
      maslovIndex_symplecticRotationLoop, zero_add])

/-- The axioms of the Maslov index of loops of symplectic matrices, for a family `μ n` of
integer-valued functions on loops in `Sp(2n) = GLSymplectic (Fin n) ℝ`, one for each `n : ℕ`:

* *homotopy*: two loops are freely homotopic exactly when they have the same value;
* *product*: the pointwise product of two loops has the sum of their values;
* *direct sum*: the direct sum of loops in `Sp(2n)` and `Sp(2m)`, read in `Sp(2(n + m))` along
  `finSumFinEquiv`, has the sum of their values;
* *normalization*: the loop `t ↦ e^{2πit}` in `U(1) ⊆ Sp(2)` has value `1`. -/
structure IsMaslovIndex (μ : (n : ℕ) → (A : GLSymplectic (Fin n) ℝ) → Path A A → ℤ) : Prop where
  homotopicWith_iff {n : ℕ} {A B : GLSymplectic (Fin n) ℝ} (γ : Path A A) (γ' : Path B B) :
    (γ : C(I, GLSymplectic (Fin n) ℝ)).HomotopicWith (γ' : C(I, GLSymplectic (Fin n) ℝ))
      (fun p ↦ p 0 = p 1) ↔ μ n A γ = μ n B γ'
  mul {n : ℕ} {A B : GLSymplectic (Fin n) ℝ} (γ : Path A A) (γ' : Path B B) :
    μ n (A * B) (γ.mul γ') = μ n A γ + μ n B γ'
  sum {n m : ℕ} {A : GLSymplectic (Fin n) ℝ} {B : GLSymplectic (Fin m) ℝ} (γ : Path A A)
    (γ' : Path B B) :
    μ (n + m) _ (((γ.prod γ').map continuous_sum).map (continuous_reindex finSumFinEquiv)) =
      μ n A γ + μ m B γ'
  normalization : μ 1 1 (symplecticRotationLoop 1) = 1

namespace IsMaslovIndex

variable {μ : (n : ℕ) → (A : GLSymplectic (Fin n) ℝ) → Path A A → ℤ} (hμ : IsMaslovIndex μ)
include hμ

/-- Loops with the same Maslov index have the same value. -/
theorem eq_of_maslovIndex_eq {n : ℕ} {A B : GLSymplectic (Fin n) ℝ} {γ : Path A A}
    {γ' : Path B B} (h : maslovIndex γ = maslovIndex γ') : μ n A γ = μ n B γ' :=
  (hμ.homotopicWith_iff γ γ').1 ((homotopicWith_iff_maslovIndex_eq γ γ').2 h)

/-- A loop of Maslov index zero has value zero: the constant loop at the identity is homotopic to
its own square. -/
theorem eq_zero_of_maslovIndex_eq_zero {n : ℕ} {A : GLSymplectic (Fin n) ℝ} {γ : Path A A}
    (h : maslovIndex γ = 0) : μ n A γ = 0 := by
  have h₁ := hμ.mul (Path.refl (1 : GLSymplectic (Fin n) ℝ)) (Path.refl 1)
  have h₂ : μ n (1 * 1) ((Path.refl (1 : GLSymplectic (Fin n) ℝ)).mul (Path.refl 1)) =
      μ n 1 (Path.refl 1) :=
    hμ.eq_of_maslovIndex_eq (by simp [maslovIndex_mul])
  rw [hμ.eq_of_maslovIndex_eq (γ' := Path.refl (1 : GLSymplectic (Fin n) ℝ)) (by simp [h])]
  omega

/-- The rotation loop `t ↦ e^{2πikt}` in `U(1) ⊆ Sp(2)` has value `k`. -/
theorem apply_symplecticRotationLoop (k : ℤ) : μ 1 1 (symplecticRotationLoop k) = k := by
  -- `t ↦ e^{2πi(k+1)t}` has the Maslov index of the product of the loops for `k` and for `1`.
  have step (k : ℤ) : μ 1 1 (symplecticRotationLoop (k + 1)) =
      μ 1 1 (symplecticRotationLoop k) + 1 := by
    rw [hμ.eq_of_maslovIndex_eq
      (γ' := (symplecticRotationLoop k).mul (symplecticRotationLoop 1)) (by simp [maslovIndex_mul]),
      hμ.mul, hμ.normalization]
  induction k using Int.induction_on with
  | zero => exact hμ.eq_zero_of_maslovIndex_eq_zero (by simp)
  | succ k ih => rw [step, ih]
  | pred k ih =>
    have := step (-k - 1)
    rw [sub_add_cancel, ih] at this
    omega

/-- A family satisfying the axioms agrees with the Maslov index on every loop. -/
theorem apply_eq_maslovIndex {n : ℕ} {A : GLSymplectic (Fin n) ℝ} (γ : Path A A) :
    μ n A γ = maslovIndex γ := by
  cases n with
  | zero =>
    -- `Sp(0)` is a point, so every loop is constant.
    have h : maslovIndex γ = 0 := by
      rw [← maslovIndex_refl (1 : GLSymplectic (Fin 0) ℝ)]
      refine maslovIndex_eq_of_homotopicWith ?_
      rw [show (γ : C(I, GLSymplectic (Fin 0) ℝ)) =
          ((Path.refl (1 : GLSymplectic (Fin 0) ℝ) : Path _ _) : C(I, GLSymplectic (Fin 0) ℝ)) from
        ContinuousMap.ext fun _ ↦ Subsingleton.elim _ _]
      exact ContinuousMap.HomotopicWith.refl _ (by simp)
    rw [h]
    exact hμ.eq_zero_of_maslovIndex_eq_zero h
  | succ n =>
    rw [(hμ.homotopicWith_iff _ _).1 (homotopicWith_reindex_sum_symplecticRotationLoop γ),
      hμ.sum, hμ.eq_zero_of_maslovIndex_eq_zero (maslovIndex_refl _),
      hμ.apply_symplecticRotationLoop, zero_add]

end IsMaslovIndex

/-- **The Maslov index of loops of symplectic matrices.** A family `μ n` of integer-valued
functions on loops in `Sp(2n)`, one for each `n`, satisfies the homotopy, product, direct-sum and
normalization axioms (`IsMaslovIndex`) if and only if it is `Ψ ↦ deg(ρ ∘ Ψ)`, the degree of the
circle loop `t ↦ ρ(Ψ t)` where `ρ = maslovPhase` is the complex determinant of the unitary polar
factor. So such a family exists, is unique, and is Tau Ceti's `maslovIndex` (`maslovIndex_def`).

Milestone: *Maslov index for loops of symplectic matrices*. -/
theorem isMaslovIndex_iff (μ : (n : ℕ) → (A : GLSymplectic (Fin n) ℝ) → Path A A → ℤ) :
    IsMaslovIndex μ ↔ μ = fun _ _ γ ↦ Circle.degree (γ.map continuous_maslovPhase) := by
  refine ⟨fun hμ ↦ funext fun n ↦ funext fun A ↦ funext fun γ ↦
    (hμ.apply_eq_maslovIndex γ).trans (maslovIndex_def γ), ?_⟩
  rintro rfl
  simp only [← maslovIndex_def]
  exact ⟨homotopicWith_iff_maslovIndex_eq, maslovIndex_mul,
    fun γ γ' ↦ by rw [maslovIndex_reindex, maslovIndex_sum],
    maslovIndex_symplecticRotationLoop 1⟩

end SymplecticGeometry

end
