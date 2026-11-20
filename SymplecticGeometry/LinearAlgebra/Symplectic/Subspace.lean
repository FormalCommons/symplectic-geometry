/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Darboux.Basis
public import TauCeti.Geometry.Symplectic.Lagrangian.Basic
public import TauCeti.LinearAlgebra.BilinearForm.LagrangianBasis
public import Mathlib.Order.Zorn

/-!
# Symplectic complements and Lagrangian extension

For a symplectic form `ω` on a real vector space `V` (Tau Ceti's `TauCeti.SymplecticForm`) and a
subspace `W`, this file adds to Tau Ceti's theory of the symplectic complement `W^ω`:

* `TauCeti.SymplecticForm.isIsotropic_iff_isCoisotropic_orthogonal`: `W` is isotropic exactly
  when `W^ω` is coisotropic, in any dimension;
* `TauCeti.SymplecticForm.IsIsotropic.exists_isLagrangian_le`: each isotropic `W` has a
  Lagrangian `L ⊇ W`, in any dimension (by Zorn's lemma, since Lagrangian subspaces are the
  maximal isotropic ones);
* `TauCeti.SymplecticForm.IsLagrangian.exists_isDarbouxBasis_apply_zero_eq`: a basis
  `u₁, …, uₙ` of a Lagrangian subspace is the first half of a Darboux basis
  `u₁, …, uₙ, v₁, …, vₙ`, with `ω(uᵢ, vⱼ) = δᵢⱼ`.

It then collects these with Tau Ceti's results into two theorems about a finite-dimensional
symplectic vector space: `TauCeti.SymplecticForm.orthogonal_properties` (dimension of the
complement, double complement, and how being symplectic, isotropic or Lagrangian passes to the
complement) and `TauCeti.SymplecticForm.isLagrangian_properties` (Lagrangian extension,
Lagrangian as maximal isotropic, extension of Lagrangian bases to Darboux bases).

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Lemma 2.1.1 and Lemma 2.1.5.
-/

public section

namespace TauCeti.SymplecticForm

open Module

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable {ω : SymplecticForm V} {L : Submodule ℝ V}

/-- A subspace is isotropic if and only if its symplectic complement is coisotropic. This holds
in any dimension: both sides say `L^ωω ≤ L^ω`, up to `L ≤ L^ωω`. -/
theorem isIsotropic_iff_isCoisotropic_orthogonal :
    ω.IsIsotropic L ↔ ω.IsCoisotropic (ω.orthogonal L) := by
  rw [isIsotropic_iff_le, isCoisotropic_iff_le]
  exact ⟨orthogonal_le, le_orthogonal_orthogonal.trans⟩

/-- The symplectic complement of an isotropic subspace is coisotropic. -/
theorem IsIsotropic.isCoisotropic_orthogonal (h : ω.IsIsotropic L) :
    ω.IsCoisotropic (ω.orthogonal L) :=
  isIsotropic_iff_isCoisotropic_orthogonal.1 h

/-- The supremum of a nonempty chain of isotropic subspaces is isotropic. -/
theorem isIsotropic_sSup_of_isChain {c : Set (Submodule ℝ V)} (hc : IsChain (· ≤ ·) c)
    (hne : c.Nonempty) (hiso : ∀ L ∈ c, ω.IsIsotropic L) : ω.IsIsotropic (sSup c) := by
  have hdir := hc.directedOn
  rw [isIsotropic_iff]
  intro v hv w hw
  obtain ⟨L₁, hL₁, hv₁⟩ := (Submodule.mem_sSup_of_directed hne hdir).1 hv
  obtain ⟨L₂, hL₂, hw₂⟩ := (Submodule.mem_sSup_of_directed hne hdir).1 hw
  obtain ⟨L₃, hL₃, h₁₃, h₂₃⟩ := hdir L₁ hL₁ L₂ hL₂
  exact isIsotropic_iff.1 (hiso L₃ hL₃) v (h₁₃ hv₁) w (h₂₃ hw₂)

/-- Every isotropic subspace lies in a maximal isotropic subspace. -/
theorem IsIsotropic.exists_maximal_isIsotropic_le (h : ω.IsIsotropic L) :
    ∃ L', L ≤ L' ∧ Maximal ω.IsIsotropic L' := by
  obtain ⟨L', hLL', hmax⟩ := zorn_le_nonempty₀ {L' | ω.IsIsotropic L'}
    (fun c hcs hc L' hL' => ⟨sSup c, isIsotropic_sSup_of_isChain hc ⟨L', hL'⟩ hcs,
      fun _ hz => le_sSup hz⟩) L h
  exact ⟨L', hLL', hmax⟩

/-- **Lagrangian extension.** Every isotropic subspace of a symplectic vector space lies in a
Lagrangian subspace. No finiteness of the dimension is needed. -/
theorem IsIsotropic.exists_isLagrangian_le (h : ω.IsIsotropic L) :
    ∃ L', L ≤ L' ∧ ω.IsLagrangian L' := by
  obtain ⟨L', hLL', hmax⟩ := h.exists_maximal_isIsotropic_le
  exact ⟨L', hLL', isLagrangian_iff_maximal_isIsotropic.2 hmax⟩

/-- A basis `u₁, …, uₙ` of a Lagrangian subspace of a finite-dimensional symplectic vector space
extends to a Darboux basis `u₁, …, uₙ, v₁, …, vₙ`, that is, one with `ω(uᵢ, uⱼ) = 0`,
`ω(vᵢ, vⱼ) = 0` and `ω(uᵢ, vⱼ) = δᵢⱼ`, where `uᵢ = b (i, 0)` and `vᵢ = b (i, 1)`. -/
theorem IsLagrangian.exists_isDarbouxBasis_apply_zero_eq [FiniteDimensional ℝ V]
    (h : ω.IsLagrangian L) {n : ℕ} (e : Basis (Fin n) ℝ L) :
    ∃ b : Basis (Fin n × Fin 2) ℝ V, ω.IsDarbouxBasis b ∧ ∀ i, b (i, 0) = e i := by
  obtain ⟨d, hd, hde⟩ :=
    ω.isAlt.exists_basis_toMatrix_eq_J_inl_eq ω.nondegenerate e
      (le_antisymm (isIsotropic_iff_le.1 h.isIsotropic) (isCoisotropic_iff_le.1 h.isCoisotropic))
  have hJ (x y : Fin n ⊕ Fin n) : ω (d x) (d y) = Matrix.J (Fin n) ℝ x y := by
    rw [← hd, LinearMap.BilinForm.toMatrix_apply]
  let v : Fin n × Fin 2 → V := fun p => if p.2 = 0 then d (.inl p.1) else -d (.inr p.1)
  have hdim : finrank ℝ V = n * 2 := by
    rw [finrank_eq_card_basis d]
    simp [mul_two]
  obtain ⟨b, hb, hbv⟩ := exists_isDarbouxBasis_coe_eq (ω := ω) hdim (v := v)
    (fun i j => by simp [v, hJ, Matrix.J])
    (fun i j => by simp [v, hJ, Matrix.J])
    (fun i j => by simp [v, hJ, Matrix.J, Matrix.one_apply])
  exact ⟨b, hb, fun i => by simp [hbv, v, hde]⟩

variable [FiniteDimensional ℝ V]

/-- **Symplectic complements.** For a subspace `W` of a finite-dimensional symplectic vector
space `(V, ω)`: `dim W + dim W^ω = dim V`; `W^ωω = W`; `W` and `W^ω` are symplectic together;
`W` is isotropic exactly when `W^ω` is coisotropic; and `W` is Lagrangian exactly when it is
isotropic with `2 · dim W = dim V`.

Milestone: *Symplectic complements*. -/
theorem orthogonal_properties (ω : SymplecticForm V) (W : Submodule ℝ V) :
    finrank ℝ W + finrank ℝ (ω.orthogonal W) = finrank ℝ V ∧
      ω.orthogonal (ω.orthogonal W) = W ∧
      (ω.IsSymplectic W ↔ ω.IsSymplectic (ω.orthogonal W)) ∧
      (ω.IsIsotropic W ↔ ω.IsCoisotropic (ω.orthogonal W)) ∧
      (ω.IsLagrangian W ↔ ω.IsIsotropic W ∧ 2 * finrank ℝ W = finrank ℝ V) :=
  ⟨ω.finrank_add_finrank_orthogonal W, ω.orthogonal_orthogonal W,
    isSymplectic_orthogonal_iff.symm, isIsotropic_iff_isCoisotropic_orthogonal,
    fun h => ⟨h.isIsotropic, h.two_mul_finrank⟩,
    fun h => h.1.isLagrangian_of_finrank h.2⟩

/-- **Lagrangian extension lemma.** In a finite-dimensional symplectic vector space `(V, ω)`,
each isotropic subspace has a Lagrangian subspace containing it; a subspace is Lagrangian iff
it is isotropic and no strictly larger subspace is; and every basis `u₁, …, uₙ` of a Lagrangian subspace extends to a
Darboux basis `u₁, …, uₙ, v₁, …, vₙ` (with `ω(uᵢ, vⱼ) = δᵢⱼ`), the `uᵢ` being `b (i, 0)`.

Milestone: *Lagrangian extension lemma*. -/
theorem isLagrangian_properties (ω : SymplecticForm V) :
    (∀ W : Submodule ℝ V, ω.IsIsotropic W → ∃ L, W ≤ L ∧ ω.IsLagrangian L) ∧
      (∀ L : Submodule ℝ V, ω.IsLagrangian L ↔ Maximal ω.IsIsotropic L) ∧
      ∀ L : Submodule ℝ V, ω.IsLagrangian L → ∀ {n : ℕ} (e : Basis (Fin n) ℝ L),
        ∃ b : Basis (Fin n × Fin 2) ℝ V, ω.IsDarbouxBasis b ∧ ∀ i, b (i, 0) = e i :=
  ⟨fun _ h => h.exists_isLagrangian_le, fun _ => isLagrangian_iff_maximal_isIsotropic,
    fun _ h _ e => h.exists_isDarbouxBasis_apply_zero_eq e⟩

end TauCeti.SymplecticForm

end
