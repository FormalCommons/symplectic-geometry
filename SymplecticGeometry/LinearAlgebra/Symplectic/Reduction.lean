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
* `TauCeti.SymplecticForm.IsLagrangian.finrank_inf_add_finrank`: for coisotropic `W` and
  Lagrangian `Λ`, `2 dim (Λ ∩ W) + dim V = 2 dim (Λ ∩ W^ω) + 2 dim W`, since the image of
  `Λ ∩ W` in `W ⧸ W^ω` is half-dimensional and the kernel of `Λ ∩ W → W ⧸ W^ω` is `Λ ∩ W^ω`.
* `TauCeti.SymplecticForm.ker_restrict_orthogonal`: in finite dimension, the radical of `W^ω`
  is `W ∩ W^ω`.
* `TauCeti.SymplecticForm.ker_restrict_le_comap_of_forall_apply_eq`,
  `TauCeti.SymplecticForm.exists_isSymplectomorphism_reducedSpace_of_forall_apply_eq`: a linear
  map that sends `U₀` into `U₁` and preserves `ω` on `U₀`, when the reduced space of `U₁` has
  at most the dimension of that of `U₀`, sends the radical of `U₀` into that of `U₁` and
  induces a symplectomorphism of the reduced spaces.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Lemma 2.1.7, and §5.4 (the linear step of Proposition 5.4.7) for
  `TauCeti.SymplecticForm.IsLagrangian.finrank_inf_add_finrank`.
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

/-- **Dimension count for a reduced Lagrangian subspace.** For a Lagrangian subspace `Λ` and a
coisotropic subspace `W` of a finite-dimensional symplectic vector space `V`,
`2 dim (Λ ∩ W) + dim V = 2 dim (Λ ∩ W^ω) + 2 dim W`. -/
theorem IsLagrangian.finrank_inf_add_finrank [FiniteDimensional ℝ V] (hL : ω.IsLagrangian L)
    (hW : ω.IsCoisotropic W) :
    2 * Module.finrank ℝ ↥(L ⊓ W) + Module.finrank ℝ V =
      2 * Module.finrank ℝ ↥(L ⊓ ω.orthogonal W) + 2 * Module.finrank ℝ W := by
  -- rank-nullity for `Λ ∩ W → W → W ⧸ W^ω`: its range is the image of `Λ ∩ W`, its kernel
  -- is `Λ ∩ W^ω`
  have h₁ := LinearMap.finrank_range_add_finrank_ker
    ((LinearMap.ker (ω.toBilinForm.restrict W)).mkQ ∘ₗ (L.comap W.subtype).subtype)
  rw [LinearMap.range_comp, Submodule.range_subtype, LinearMap.ker_comp, Submodule.ker_mkQ] at h₁
  have h₂ : Module.finrank ℝ ↥(L.comap W.subtype) = Module.finrank ℝ ↥(L ⊓ W) := by
    rw [← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype, inf_comm]
  have h₃ : Module.finrank ℝ
      ↥((LinearMap.ker (ω.toBilinForm.restrict W)).comap (L.comap W.subtype).subtype) =
      Module.finrank ℝ ↥(L ⊓ ω.orthogonal W) := by
    rw [← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype,
      ← Submodule.finrank_map_subtype_eq, Submodule.map_inf _ W.injective_subtype,
      Submodule.map_comap_subtype, hW.map_subtype_ker_restrict, inf_comm W L, inf_assoc,
      inf_eq_right.2 (isCoisotropic_iff_le.1 hW)]
  have h₄ := (hL.reduction_map hW).two_mul_finrank
  have h₅ := hW.finrank_reducedSpace_add_finrank
  rw [← h₂, ← h₃, ← h₁, ← h₅, ← h₄]
  ring

section Orthogonal

variable [FiniteDimensional ℝ V]

variable (ω W) in
/-- In finite dimension, the kernel of the restriction of `ω` to `W^ω` is the radical
`W ∩ W^ω`, seen in `W^ω`. -/
theorem ker_restrict_orthogonal :
    LinearMap.ker (ω.toBilinForm.restrict (ω.orthogonal W)) =
      (W ⊓ ω.orthogonal W).comap (ω.orthogonal W).subtype := by
  ext u
  rw [mem_ker_restrict_iff, orthogonal_orthogonal, Submodule.mem_comap, Submodule.subtype_apply,
    Submodule.mem_inf, and_iff_left u.property]

end Orthogonal

section ReducedMap

open Module

variable {V₀ V₁ : Type*} [AddCommGroup V₀] [Module ℝ V₀] [AddCommGroup V₁] [Module ℝ V₁]
  [FiniteDimensional ℝ V₀] [FiniteDimensional ℝ V₁]
  {ω₀ : SymplecticForm V₀} {ω₁ : SymplecticForm V₁} {U₀ : Submodule ℝ V₀}
  {U₁ : Submodule ℝ V₁} {L : V₀ →ₗ[ℝ] V₁}

omit [FiniteDimensional ℝ V₀] [FiniteDimensional ℝ V₁] in
/-- A vector of `U₀` that `L`, followed by the quotient map, sends to zero in the reduced space
of `U₁` lies in the radical of `U₀`, when `L` preserves `ω` on `U₀`. -/
private theorem ker_mkQ_comp_restrict_le (hL : ∀ u ∈ U₀, L u ∈ U₁)
    (hLω : ∀ u ∈ U₀, ∀ v ∈ U₀, ω₁ (L u) (L v) = ω₀ u v) :
    LinearMap.ker ((LinearMap.ker (ω₁.toBilinForm.restrict U₁)).mkQ ∘ₗ L.restrict hL) ≤
      LinearMap.ker (ω₀.toBilinForm.restrict U₀) := by
  intro u hu
  rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply] at hu
  rw [mem_ker_restrict_iff, mem_orthogonal_iff']
  intro y hy
  have h := congrArg (fun z => ω₁.reduction U₁ z (Submodule.Quotient.mk ⟨L y, hL y hy⟩)) hu
  simp only [LinearMap.restrict_apply, reduction_mk, map_zero, LinearMap.zero_apply] at h
  rw [← hLω u u.property y hy]
  exact h

/-- **Radicals are preserved.** If `L` maps `U₀` into `U₁` and preserves `ω` on `U₀`, and the
reduced space of `U₁` has at most the dimension of that of `U₀`, then `L` maps the radical
`U₀ ∩ U₀^ω` into the radical `U₁ ∩ U₁^ω`, both seen as the kernels of the restricted forms. -/
theorem ker_restrict_le_comap_of_forall_apply_eq (hL : ∀ u ∈ U₀, L u ∈ U₁)
    (hLω : ∀ u ∈ U₀, ∀ v ∈ U₀, ω₁ (L u) (L v) = ω₀ u v)
    (hdim : finrank ℝ (ω₁.ReducedSpace U₁) ≤ finrank ℝ (ω₀.ReducedSpace U₀)) :
    LinearMap.ker (ω₀.toBilinForm.restrict U₀) ≤
      (LinearMap.ker (ω₁.toBilinForm.restrict U₁)).comap (L.restrict hL) := by
  have hle := ker_mkQ_comp_restrict_le hL hLω
  have h₁ := LinearMap.finrank_range_add_finrank_ker
    ((LinearMap.ker (ω₁.toBilinForm.restrict U₁)).mkQ ∘ₗ L.restrict hL)
  have h₂ : finrank ℝ (ω₀.ReducedSpace U₀) +
      finrank ℝ (LinearMap.ker (ω₀.toBilinForm.restrict U₀)) = finrank ℝ U₀ :=
    Submodule.finrank_quotient_add_finrank _
  have h₃ : finrank ℝ (LinearMap.range
      ((LinearMap.ker (ω₁.toBilinForm.restrict U₁)).mkQ ∘ₗ L.restrict hL)) ≤
      finrank ℝ (ω₁.ReducedSpace U₁) :=
    Submodule.finrank_le _
  have heq := Submodule.eq_of_le_of_finrank_le hle (by omega)
  intro u hu
  rw [← heq, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero] at hu
  exact hu

/-- **Reduction of a map preserving `ω`.** If `L` maps `U₀` into `U₁` and preserves `ω` on `U₀`,
and the reduced space of `U₁` has at most the dimension of that of `U₀`, then `[u] ↦ [L u]` is
a well-defined symplectomorphism of the reduced spaces. -/
theorem exists_isSymplectomorphism_reducedSpace_of_forall_apply_eq (hL : ∀ u ∈ U₀, L u ∈ U₁)
    (hLω : ∀ u ∈ U₀, ∀ v ∈ U₀, ω₁ (L u) (L v) = ω₀ u v)
    (hdim : finrank ℝ (ω₁.ReducedSpace U₁) ≤ finrank ℝ (ω₀.ReducedSpace U₀)) :
    ∃ e : ω₀.ReducedSpace U₀ ≃ₗ[ℝ] ω₁.ReducedSpace U₁,
      IsSymplectomorphism (ω₀.reduction U₀) (ω₁.reduction U₁) e ∧
        ∀ u : U₀, e (Submodule.Quotient.mk u) = Submodule.Quotient.mk ⟨L u, hL u u.property⟩ := by
  set g := Submodule.mapQ _ _ (L.restrict hL) (ker_restrict_le_comap_of_forall_apply_eq hL hLω hdim)
  have hg : ∀ x y, ω₁.reduction U₁ (g x) (g y) = ω₀.reduction U₀ x y := by
    intro x y
    induction x using Submodule.Quotient.induction_on with
    | H u =>
    induction y using Submodule.Quotient.induction_on with
    | H v =>
    simp only [g, Submodule.mapQ_apply, LinearMap.restrict_apply, reduction_mk]
    exact hLω u u.property v v.property
  have hinj : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    refine (ω₀.reduction U₀).separatingLeft x fun y => ?_
    have := hg x y
    rw [LinearMap.mem_ker.1 hx] at this
    simpa using this.symm
  exact ⟨LinearMap.linearEquivOfInjective g hinj
      (le_antisymm (LinearMap.finrank_le_finrank_of_injective hinj) hdim),
    isSymplectomorphism_iff.2 hg, fun u => rfl⟩

end ReducedMap

end TauCeti.SymplecticForm

end
