/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.LinearReduction

/-!
# Linear symplectic reduction by a coisotropic subspace

Tau Ceti's `TauCeti.SymplecticForm.reduction ω W` is the symplectic form `[u], [v] ↦ ω(u, v)` on
the reduced space `TauCeti.SymplecticForm.ReducedSpace ω W`, the quotient of `W` by the kernel
of the restriction of `ω` to `W`, which is `W ∩ W^ω`. This file adds what the classical
statement for a coisotropic subspace `W` needs on top of it:

* for coisotropic `W` the kernel is `W^ω` itself, so the reduced space is `W ⧸ W^ω`;
* the bilinear form of the reduced form is the only bilinear form on the reduced space whose
  pullback to `W` is the restriction of `ω`, so the reduced form is the only such symplectic
  form; this holds for every subspace `W`;
* for coisotropic `W` and Lagrangian `Λ`, the image `((Λ ∩ W) + W^ω) ⧸ W^ω` of `Λ` in the
  reduced space is Lagrangian; it is the image of `Λ ∩ W`, for which Tau Ceti's
  `TauCeti.SymplecticForm.IsLagrangian.reduction_map` proves this.

## Main results

* `TauCeti.SymplecticForm.IsCoisotropic.map_subtype_ker_restrict`: for coisotropic `W`, the
  subspace divided out is `W^ω`.
* `TauCeti.SymplecticForm.eq_toBilinForm_reduction_of_apply_mk_mk`,
  `TauCeti.SymplecticForm.eq_reduction_of_apply_mk_mk`,
  `TauCeti.SymplecticForm.existsUnique_reduction`: uniqueness of the reduced form.
* `TauCeti.SymplecticForm.map_mkQ_comap_inf_sup`,
  `TauCeti.SymplecticForm.IsLagrangian.reduction_map_sup`: the image of a Lagrangian
  subspace `Λ`, as `((Λ ∩ W) + W^ω) ⧸ W^ω`, is Lagrangian.
* `TauCeti.SymplecticForm.IsCoisotropic.existsUnique_reduction_and_isLagrangian`: the three
  statements together.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Lemma 2.1.7.
-/

public section

namespace TauCeti.SymplecticForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {ω : SymplecticForm V} {W L : Submodule ℝ V}

/-- For a coisotropic subspace `W`, the kernel of the restriction of `ω` to `W`, viewed in `V`,
is the symplectic complement `W^ω`: the reduced space of `W` is `W ⧸ W^ω`. -/
theorem IsCoisotropic.map_subtype_ker_restrict (hW : ω.IsCoisotropic W) :
    (LinearMap.ker (ω.toBilinForm.restrict W)).map W.subtype = ω.orthogonal W := by
  rw [ω.map_subtype_ker_restrict W, inf_eq_right.2 (isCoisotropic_iff_le.1 hW)]

variable (ω W) in
/-- **Uniqueness of the reduced form.** A bilinear form `B` on the reduced space of `W` whose
pullback to `W` is the restriction of `ω`, that is `B([u], [v]) = ω(u, v)`, is the bilinear form
of the reduced form `TauCeti.SymplecticForm.reduction ω W`. -/
theorem eq_toBilinForm_reduction_of_apply_mk_mk (B : LinearMap.BilinForm ℝ (ω.ReducedSpace W))
    (hB : ∀ u v : W, B (Submodule.Quotient.mk u) (Submodule.Quotient.mk v) = ω u v) :
    B = (ω.reduction W).toBilinForm := by
  ext u v
  exact (hB u v).trans (reduction_mk ω W u v).symm

variable (ω W) in
/-- A symplectic form on the reduced space of `W` whose pullback to `W` is the restriction of
`ω`, that is `σ([u], [v]) = ω(u, v)`, is the reduced form `TauCeti.SymplecticForm.reduction ω W`.
-/
theorem eq_reduction_of_apply_mk_mk (σ : SymplecticForm (ω.ReducedSpace W))
    (hσ : ∀ u v : W, σ (Submodule.Quotient.mk u) (Submodule.Quotient.mk v) = ω u v) :
    σ = ω.reduction W :=
  toBilinForm_injective (eq_toBilinForm_reduction_of_apply_mk_mk ω W σ.toBilinForm hσ)

variable (ω W) in
/-- The reduced form is the unique symplectic form on the reduced space of `W` whose pullback to
`W` is the restriction of `ω`. -/
theorem existsUnique_reduction :
    ∃! σ : SymplecticForm (ω.ReducedSpace W),
      ∀ u v : W, σ (Submodule.Quotient.mk u) (Submodule.Quotient.mk v) = ω u v :=
  ⟨ω.reduction W, reduction_mk ω W, eq_reduction_of_apply_mk_mk ω W⟩

variable (ω W L) in
/-- For subspaces `W` and `L`, the vectors of `W` that lie in `(L ∩ W) + W^ω` have the same
image in the reduced space of `W` as `L ∩ W`. For coisotropic `W`, this says that the subspace
`((L ∩ W) + W^ω) ⧸ W^ω` of `W ⧸ W^ω` is the image of `L ∩ W`. -/
theorem map_mkQ_comap_inf_sup :
    (((L ⊓ W) ⊔ ω.orthogonal W).comap W.subtype).map
        (LinearMap.ker (ω.toBilinForm.restrict W)).mkQ =
      (L.comap W.subtype).map (LinearMap.ker (ω.toBilinForm.restrict W)).mkQ := by
  refine le_antisymm ?_ (Submodule.map_mono fun u hu => ?_)
  · rintro _ ⟨u, hu, rfl⟩
    obtain ⟨l, hl, c, hc, hlc⟩ := Submodule.mem_sup.1 hu
    refine ⟨⟨l, hl.2⟩, hl.1, ReducedSpace.mk_eq_mk_iff.2 ?_⟩
    have : l - (u : V) = -c := by
      rw [Submodule.subtype_apply] at hlc
      rw [← hlc]
      abel
    exact this ▸ (ω.orthogonal W).neg_mem hc
  · exact Submodule.mem_sup_left ⟨hu, u.property⟩

/-- **Reduction of a Lagrangian subspace.** For a coisotropic subspace `W` and a Lagrangian
subspace `Λ`, the image `((Λ ∩ W) + W^ω) ⧸ W^ω` of `Λ` in the reduced space is Lagrangian. -/
theorem IsLagrangian.reduction_map_sup [FiniteDimensional ℝ V]
    (hL : ω.IsLagrangian L) (hW : ω.IsCoisotropic W) :
    (ω.reduction W).IsLagrangian ((((L ⊓ W) ⊔ ω.orthogonal W).comap W.subtype).map
      (LinearMap.ker (ω.toBilinForm.restrict W)).mkQ) := by
  rw [map_mkQ_comap_inf_sup]
  exact hL.reduction_map hW

/-- **Linear symplectic reduction.** Let `W` be a coisotropic subspace of a finite-dimensional
symplectic vector space `(V, ω)`. Then the reduced space of `W` is `W ⧸ W^ω`; among all
symplectic forms on it, exactly one satisfies `σ([u], [v]) = ω(u, v)` for all `u, v ∈ W`, namely
`TauCeti.SymplecticForm.reduction ω W`; and this form makes `((Λ ∩ W) + W^ω) ⧸ W^ω` Lagrangian
for each Lagrangian subspace `Λ` of `V`.

Milestone: *Linear symplectic reduction*. -/
theorem IsCoisotropic.existsUnique_reduction_and_isLagrangian [FiniteDimensional ℝ V]
    (hW : ω.IsCoisotropic W) :
    (LinearMap.ker (ω.toBilinForm.restrict W)).map W.subtype = ω.orthogonal W ∧
      (∃! σ : SymplecticForm (ω.ReducedSpace W),
        ∀ u v : W, σ (Submodule.Quotient.mk u) (Submodule.Quotient.mk v) = ω u v) ∧
      ∀ L : Submodule ℝ V, ω.IsLagrangian L →
        (ω.reduction W).IsLagrangian ((((L ⊓ W) ⊔ ω.orthogonal W).comap W.subtype).map
          (LinearMap.ker (ω.toBilinForm.restrict W)).mkQ) :=
  ⟨hW.map_subtype_ker_restrict, existsUnique_reduction ω W,
    fun _ hL => hL.reduction_map_sup hW⟩

end TauCeti.SymplecticForm

end
