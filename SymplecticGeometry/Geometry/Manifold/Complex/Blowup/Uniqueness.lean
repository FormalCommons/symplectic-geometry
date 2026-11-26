/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.Blowup.Basic
public import TauCeti.Geometry.Manifold.Gluing.Basic

/-!
# Uniqueness of the complex structure of the blowup

Let `c` be a holomorphic chart of a complex manifold `M` around `p₀`, and let `X` be a space
charted on `ℂⁿ⁺¹` together with a bijection `e : X ≃ Blowup c`. If the two maps
`e.symm ∘ inl c` and `e.symm ∘ inr c`, from the punctured manifold and from the part of the model
blowup over the target of `c`, are local biholomorphisms, then `e` is a biholomorphism
(`SymplecticGeometry.Blowup.diffeomorphOfEquiv`). So the complex structure of the blowup is the
only one for which the two pieces are open complex submanifolds; it is stated for a structure
carried by another type `X`, so that no two instances meet on one type.

The hypotheses are put on the two pieces, rather than on `blowdown c ∘ e` off the preimage of
the exceptional divisor and on `lift c ∘ e` near it, since the latter form would presuppose that
this preimage is closed in `X`. The construction is Tau Ceti's
`TauCeti.diffeomorphOfForallIsLocalDiffeomorphEquiv`, applied to the two canonical maps `inl c`
and `inr c`, which are jointly surjective and local biholomorphisms.

## Main results

* `SymplecticGeometry.Blowup.diffeomorphOfEquiv`: a bijection onto the blowup that is a local
  biholomorphism on each of the two pieces, as a biholomorphism; `coe_diffeomorphOfEquiv` and
  `coe_diffeomorphOfEquiv_symm` give its maps.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §7.1, Lemma 7.1.3.
-/

public section

open scoped Manifold ContDiff

namespace SymplecticGeometry

namespace Blowup

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Fin (n + 1) → ℂ) M]
  [IsManifold 𝓘(ℂ, Fin (n + 1) → ℂ) ω M] {p₀ : M} (c : BlowupChart (n := n) M p₀)
  [Fact (c.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin (n + 1) → ℂ) ω M)]

/-- **Uniqueness of the complex structure of the blowup.** Let `X` be charted on `ℂⁿ⁺¹` and let
`e : X ≃ Blowup c` be a bijection such that `e.symm ∘ inl c` and `e.symm ∘ inr c` are local
biholomorphisms. Then `e` is a biholomorphism `X ≃ Blowup c`. -/
noncomputable def diffeomorphOfEquiv {X : Type} [TopologicalSpace X]
    [ChartedSpace (Fin (n + 1) → ℂ) X] (e : X ≃ Blowup c)
    (hl : IsLocalDiffeomorph 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) ω (e.symm ∘ inl c))
    (hr : IsLocalDiffeomorph 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) ω (e.symm ∘ inr c)) :
    X ≃ₘ^ω⟮𝓘(ℂ, Fin (n + 1) → ℂ), 𝓘(ℂ, Fin (n + 1) → ℂ)⟯ Blowup c :=
  -- The family is `inl c` and `inr c`, indexed by the pieces of the gluing.
  TauCeti.diffeomorphOfForallIsLocalDiffeomorphEquiv
    (φ := (fun | ⟨false⟩ => inl c | ⟨true⟩ => inr c :
      ∀ i : (glueData c).J, (glueData c).U i → Blowup c))
    (fun z ↦ ((range_inl_union_range_inr c).ge (Set.mem_univ z)).elim
      (fun ⟨x, hx⟩ ↦ ⟨⟨false⟩, x, hx⟩) (fun ⟨y, hy⟩ ↦ ⟨⟨true⟩, y, hy⟩)) e
    (fun | ⟨false⟩ => isLocalDiffeomorph_inl c | ⟨true⟩ => isLocalDiffeomorph_inr c)
    (fun | ⟨false⟩ => hl | ⟨true⟩ => hr)

variable {X : Type} [TopologicalSpace X] [ChartedSpace (Fin (n + 1) → ℂ) X] (e : X ≃ Blowup c)
  (hl : IsLocalDiffeomorph 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) ω (e.symm ∘ inl c))
  (hr : IsLocalDiffeomorph 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) ω (e.symm ∘ inr c))

/-- The underlying equivalence of `diffeomorphOfEquiv c e hl hr` is `e`. -/
@[simp]
theorem diffeomorphOfEquiv_toEquiv : (diffeomorphOfEquiv c e hl hr).toEquiv = e := by
  simp [diffeomorphOfEquiv]

/-- The map underlying `diffeomorphOfEquiv c e hl hr` is `e`. -/
@[simp]
theorem coe_diffeomorphOfEquiv : ⇑(diffeomorphOfEquiv c e hl hr) = e := by
  simp [diffeomorphOfEquiv]

/-- The inverse map of `diffeomorphOfEquiv c e hl hr` is `e.symm`. -/
@[simp]
theorem coe_diffeomorphOfEquiv_symm : ⇑(diffeomorphOfEquiv c e hl hr).symm = e.symm := by
  simp [diffeomorphOfEquiv]

end Blowup

end SymplecticGeometry

end
