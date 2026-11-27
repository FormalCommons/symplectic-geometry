/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Orientation
public import TauCeti.Geometry.Symplectic.Restrict
public import TauCeti.Geometry.Symplectic.SymplecticTransport

/-!
# Symplectic orientations: transported structures and orthogonal splittings

If a symplectic form `ω` on `V` tames an almost complex structure `J`, and `e : V ≃ W` is a
linear equivalence, then every basis `(v₁, J' v₁, …, vₙ, J' vₙ)` of `W` adapted to the transport
`J' = e ∘ J ∘ e⁻¹` induces the image under `e` of the symplectic orientation of `ω`
(`TauCeti.SymplecticForm.Tames.orientation_reindex_transport`). This combines Tau Ceti's
`TauCeti.SymplecticForm.Tames.orientation_reindex`, applied to the transported form, with the
naturality `TauCeti.SymplecticForm.IsSymplectomorphism.map_orientation`.

If `V = H ⊕ L` is a splitting into `ω`-orthogonal subspaces, then `L` is the symplectic complement
of `H` (`TauCeti.SymplecticForm.orthogonal_eq_of_isCompl`), both summands are symplectic
(`TauCeti.SymplecticForm.isSymplectic_left_of_isCompl`,
`TauCeti.SymplecticForm.isSymplectic_right_of_isCompl`), and the symplectic orientation of `ω`
is the image under `H × L ≃ V` of the product of the symplectic orientations of the restrictions
of `ω` to `H` and to `L`
(`TauCeti.SymplecticForm.orientation_eq_map_prod_of_isCompl`). This combines Tau Ceti's
`TauCeti.SymplecticForm.isSymplectomorphism_prodEquivOfIsCompl`,
`TauCeti.SymplecticForm.IsSymplectomorphism.map_orientation` and
`TauCeti.SymplecticForm.orientation_prod`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017]
-/

public section

open Module

namespace TauCeti.SymplecticForm

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
  {ω : SymplecticForm V} {J : AlmostComplexStructure V} {n k : ℕ}
  {b : Basis (Fin n × Fin 2) ℝ W}

/-- If `ω` tames `J` and `e : V ≃ W` is a linear equivalence, every basis
`(v₁, J' v₁, …, vₙ, J' vₙ)` of `W` adapted to the transport `J' = e ∘ J ∘ e⁻¹` induces the
image under `e` of the symplectic orientation of `ω`. -/
theorem Tames.orientation_reindex_transport (hJ : ω.Tames J) (e : V ≃ₗ[ℝ] W)
    (hk : finrank ℝ V = k) (hb : ∀ i, b (i, 1) = J.transport e (b (i, 0))) (h : n * 2 = k) :
    (b.reindex (finProdFinEquiv.trans (finCongr h))).orientation =
      Orientation.map (Fin k) e (ω.orientation hk) := by
  rw [(hJ.transport e).orientation_reindex hb (e.finrank_eq.symm.trans hk) h,
    (isSymplectomorphism_iff_transport_eq.2 rfl).map_orientation hk]

section Splitting

variable {H L : Submodule ℝ V}

omit [FiniteDimensional ℝ V] in
/-- If `V = H ⊕ L` and `ω h l = 0` for all `h ∈ H` and `l ∈ L`, then `L` is the symplectic
complement of `H`. -/
theorem orthogonal_eq_of_isCompl (ω : SymplecticForm V) (hc : IsCompl H L)
    (hHL : ∀ h ∈ H, ∀ l ∈ L, ω h l = 0) : ω.orthogonal H = L := by
  refine le_antisymm (fun v hv ↦ ?_) fun l hl ↦ mem_orthogonal_iff.2 fun h hh ↦ hHL h hh l hl
  obtain ⟨h, l, hh, hl, rfl⟩ := Submodule.codisjoint_iff_exists_add_eq.1 hc.codisjoint v
  -- The component `h` pairs to zero with `H` (as `h + l` and `l` do) and with `L`, so it is zero.
  have hh0 : h = 0 := ω.separatingLeft h fun u ↦ by
    obtain ⟨a, b, ha, hb, rfl⟩ := Submodule.codisjoint_iff_exists_add_eq.1 hc.codisjoint u
    have h₁ : ω (h + l) a = 0 := mem_orthogonal_iff'.1 hv a ha
    have h₂ : ω l a = 0 := by rw [← ω.neg_eq, hHL a ha l hl, neg_zero]
    simp only [map_add, LinearMap.add_apply, hHL h hh b hb] at h₁ ⊢
    linarith
  simpa [hh0] using hl

omit [FiniteDimensional ℝ V] in
/-- If `V = H ⊕ L` with `H` and `L` orthogonal for `ω`, then `H` is a symplectic subspace. -/
theorem isSymplectic_left_of_isCompl (ω : SymplecticForm V) (hc : IsCompl H L)
    (hHL : ∀ h ∈ H, ∀ l ∈ L, ω h l = 0) : ω.IsSymplectic H := by
  rw [isSymplectic_iff_disjoint, ω.orthogonal_eq_of_isCompl hc hHL]
  exact hc.disjoint

omit [FiniteDimensional ℝ V] in
/-- If `V = H ⊕ L` with `H` and `L` orthogonal for `ω`, then `L` is a symplectic subspace. -/
theorem isSymplectic_right_of_isCompl (ω : SymplecticForm V) (hc : IsCompl H L)
    (hHL : ∀ h ∈ H, ∀ l ∈ L, ω h l = 0) : ω.IsSymplectic L :=
  ω.isSymplectic_left_of_isCompl hc.symm fun l hl h hh ↦ by
    rw [← ω.neg_eq, hHL h hh l hl, neg_zero]

/-- If `V = H ⊕ L` with `H` and `L` orthogonal for `ω`, the symplectic orientation of `ω` is the
image under `H × L ≃ V` of the product of the symplectic orientations of the restrictions of `ω`
to `H` and to `L`. -/
theorem orientation_eq_map_prod_of_isCompl (ω : SymplecticForm V) (hc : IsCompl H L)
    (hHL : ∀ h ∈ H, ∀ l ∈ L, ω h l = 0) {m n : ℕ} (hm : finrank ℝ H = m)
    (hn : finrank ℝ L = n) (hV : finrank ℝ V = m + n) :
    ω.orientation hV = Orientation.map (Fin (m + n)) (Submodule.prodEquivOfIsCompl H L hc)
      (((ω.restrict H (ω.isSymplectic_left_of_isCompl hc hHL).nondegenerate_restrict).orientation
          hm).prod
        ((ω.restrict L (ω.isSymplectic_right_of_isCompl hc hHL).nondegenerate_restrict).orientation
          hn) hm hn) := by
  obtain rfl := ω.orthogonal_eq_of_isCompl hc hHL
  rw [← orientation_prod _ _ hm hn (by rw [finrank_prod, hm, hn]),
    (ω.isSymplectomorphism_prodEquivOfIsCompl hc).map_orientation]

end Splitting

end TauCeti.SymplecticForm

end
