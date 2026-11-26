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
(`SymplecticGeometry.Blowup.exists_diffeomorph_coe_eq_of_blowdown`). So the complex structure of
the blowup is the only one for which the two pieces are open complex submanifolds; it is stated
for a structure carried by another type `X`, so that no two instances meet on one type.

The hypotheses are put on the two pieces, rather than on `blowdown c ∘ e` off the preimage of
the exceptional divisor and on `lift c ∘ e` near it, since the latter form would presuppose that
this preimage is closed in `X`. The proof is Tau Ceti's
`TauCeti.diffeomorphOfForallIsLocalDiffeomorphEquiv`, applied to the canonical maps of the
gluing, which are jointly surjective and local biholomorphisms.

## Main results

* `SymplecticGeometry.Blowup.exists_diffeomorph_coe_eq_of_blowdown`: a bijection onto the blowup
  that is a local biholomorphism on each of the two pieces is a biholomorphism.

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
biholomorphisms. Then there is a biholomorphism `X ≃ Blowup c` whose underlying map is `e`. -/
theorem exists_diffeomorph_coe_eq_of_blowdown {X : Type} [TopologicalSpace X]
    [ChartedSpace (Fin (n + 1) → ℂ) X] (e : X ≃ Blowup c)
    (hl : IsLocalDiffeomorph 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) ω (e.symm ∘ inl c))
    (hr : IsLocalDiffeomorph 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) ω (e.symm ∘ inr c)) :
    ∃ Φ : X ≃ₘ^ω⟮𝓘(ℂ, Fin (n + 1) → ℂ), 𝓘(ℂ, Fin (n + 1) → ℂ)⟯ Blowup c, ⇑Φ = e := by
  have hD := isCompatible_complex c Fact.out
  -- The canonical maps of the gluing, as maps into `Blowup c` with its own atlas.
  let φ : ∀ i, (glueData c).U i → Blowup c := fun i ↦ (glueData c).toGlueData.ι i
  have hφ : ∀ i, IsLocalDiffeomorph 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) ω (φ i) :=
    hD.isLocalDiffeomorph_ι
  have hφX : ∀ i, IsLocalDiffeomorph 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) ω
      (e.symm ∘ φ i)
    | ⟨false⟩ => by rwa [show φ ⟨false⟩ = inl c from (funext (inl_def c)).symm]
    | ⟨true⟩ => by rwa [show φ ⟨true⟩ = inr c from (funext (inr_def c)).symm]
  have hcover : ∀ z : Blowup c, ∃ i y, φ i y = z := (glueData c).ι_jointly_surjective
  exact ⟨_, TauCeti.coe_diffeomorphOfForallIsLocalDiffeomorphEquiv hcover e hφ hφX⟩

end Blowup

end SymplecticGeometry

end
