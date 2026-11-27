/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Orientation
public import TauCeti.Geometry.Symplectic.Restrict
public import TauCeti.Geometry.Symplectic.SymplecticTransport
public import SymplecticGeometry.LinearAlgebra.Symplectic.Subspace

/-!
# Symplectic orientations: transported structures and orthogonal splittings

If a symplectic form `ω` on `V` tames an almost complex structure `J`, and `e : V ≃ W` is a
linear equivalence, then every basis `(v₁, J' v₁, …, vₙ, J' vₙ)` of `W` adapted to the transport
`J' = e ∘ J ∘ e⁻¹` induces the image under `e` of the symplectic orientation of `ω`
(`TauCeti.SymplecticForm.Tames.orientation_reindex_transport`). This combines Tau Ceti's
`TauCeti.SymplecticForm.Tames.orientation_reindex`, applied to the transported form, with the
naturality `TauCeti.SymplecticForm.IsSymplectomorphism.map_orientation`.

If `V = H ⊕ L` is a splitting into `ω`-orthogonal subspaces, then the symplectic orientation of
`ω` is the image under `H × L ≃ V` of the product of the symplectic orientations of the
restrictions of `ω` to `H` and to `L`
(`TauCeti.SymplecticForm.orientation_eq_map_prod_of_isCompl`). The splitting gives `L = H^ω`
and makes both summands symplectic, by `TauCeti.SymplecticForm.orthogonal_eq_of_isCompl`,
`TauCeti.SymplecticForm.isSymplectic_left_of_isCompl` and
`TauCeti.SymplecticForm.isSymplectic_right_of_isCompl` of the library's
`LinearAlgebra/Symplectic/Subspace.lean`; the proof then combines Tau Ceti's
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
