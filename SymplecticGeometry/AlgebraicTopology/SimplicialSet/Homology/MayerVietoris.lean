/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.MayerVietoris

/-!
# The Mayer–Vietoris connecting map from chain lifts

Consider a commutative square of simplicial sets with maps `t : X₁ ⟶ X₂`, `l : X₁ ⟶ X₃`,
`r : X₂ ⟶ X₄` and `b : X₃ ⟶ X₄`. Given chains `u` of `X₂` and `v` of `X₃` in degree `q + 1` whose
boundaries are the images of a common chain `w` of `X₁` under `t` and `l`, the difference
`r(u) - b(v)` is a cycle of `X₄` (`SSet.exists_cycle_of_chain_lifts`). When the square is a
pushout and `t` is a monomorphism, the Mayer–Vietoris connecting map `SSet.mayerVietorisδ` sends
the class of such a cycle `r(u) - b(v)` to the class of `w`
(`SSet.homologyπ_mayerVietorisδ_of_chain_lifts`). This is the usual description of the
connecting map: split a cycle of the union into chains on the two pieces, and take the boundary
of one of them.

These lemmas are from Tau Ceti's main branch
(`TauCeti/AlgebraicTopology/SimplicialSet/Homology/MayerVietoris.lean`, same names), as of the
commit `e48a7f81a81426270765022681d165be592a3231`, not yet in the pinned release; they are stated
here under their Tau Ceti names, so that moving Tau Ceti past them deletes this file without
renames. The proofs are Tau Ceti's, with one added step: outside its defining module,
`SSet.mayerVietorisδ` is unfolded by `SSet.mayerVietorisδ_def`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 2.2, the
  Mayer–Vietoris sequences.
-/

public section

noncomputable section

open CategoryTheory Limits

attribute [local instance] preservesBinaryBiproduct_of_preservesBiproduct

universe w v u

namespace SSet

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
  {X₁ X₂ X₃ X₄ : SSet.{w}} {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}

/-- Chain lifts with the same boundary determine a cycle in the union term. -/
lemma exists_cycle_of_chain_lifts (sq : CommSq t l r b) {A : C} (q : ℕ)
    (w : A ⟶ (X₁.chainComplex R).X q)
    (u : A ⟶ (X₂.chainComplex R).X (q + 1))
    (v : A ⟶ (X₃.chainComplex R).X (q + 1))
    (hu : u ≫ (X₂.chainComplex R).d (q + 1) q = w ≫ (SSet.chainComplexMap t R).f q)
    (hv : v ≫ (X₃.chainComplex R).d (q + 1) q = w ≫ (SSet.chainComplexMap l R).f q) :
    ∃ z : A ⟶ (X₄.chainComplex R).cycles (q + 1),
      u ≫ (SSet.chainComplexMap r R).f (q + 1) -
        v ≫ (SSet.chainComplexMap b R).f (q + 1) = z ≫ (X₄.chainComplex R).iCycles (q + 1) := by
  let x := u ≫ (SSet.chainComplexMap r R).f (q + 1) -
    v ≫ (SSet.chainComplexMap b R).f (q + 1)
  have hx : x ≫ (X₄.chainComplex R).d (q + 1) q = 0 := by
    dsimp only [x]
    rw [Preadditive.sub_comp, Category.assoc, Category.assoc,
      HomologicalComplex.Hom.comm, HomologicalComplex.Hom.comm,
      ← Category.assoc, ← Category.assoc, hu, hv]
    simp only [Category.assoc, ← HomologicalComplex.comp_f, ← Functor.map_comp,
      sq.w, sub_self]
  exact ⟨(X₄.chainComplex R).liftCycles x q (ChainComplex.next_nat_succ q) hx,
    ((X₄.chainComplex R).liftCycles_i x q (ChainComplex.next_nat_succ q) hx).symm⟩

variable [Mono t]

open HomologicalComplex

/-- Two chain lifts with a common boundary compute the native Mayer–Vietoris connecting map. -/
lemma homologyπ_mayerVietorisδ_of_chain_lifts (sq : IsPushout t l r b) {A : C} (q : ℕ)
    (z : A ⟶ (X₄.chainComplex R).cycles (q + 1))
    (w : A ⟶ (X₁.chainComplex R).cycles q)
    (u : A ⟶ (X₂.chainComplex R).X (q + 1))
    (v : A ⟶ (X₃.chainComplex R).X (q + 1))
    (huv : u ≫ (SSet.chainComplexMap r R).f (q + 1) -
        v ≫ (SSet.chainComplexMap b R).f (q + 1) = z ≫ (X₄.chainComplex R).iCycles (q + 1))
    (hu : u ≫ (X₂.chainComplex R).d (q + 1) q =
      w ≫ (X₁.chainComplex R).iCycles q ≫ (SSet.chainComplexMap t R).f q)
    (hv : v ≫ (X₃.chainComplex R).d (q + 1) q =
      w ≫ (X₁.chainComplex R).iCycles q ≫ (SSet.chainComplexMap l R).f q) :
    z ≫ (X₄.chainComplex R).homologyπ (q + 1) ≫ SSet.mayerVietorisδ R sq (q + 1) q rfl =
      w ≫ (X₁.chainComplex R).homologyπ q := by
  let SC := (sq.map ((SSet.chainComplexFunctor C).obj R)).shortComplex
  let x₂ : A ⟶ SC.X₂.X (q + 1) :=
    u ≫ (biprod.inl : X₂.chainComplex R ⟶ X₂.chainComplex R ⊞ X₃.chainComplex R).f (q + 1) -
      v ≫ (biprod.inr : X₃.chainComplex R ⟶ X₂.chainComplex R ⊞ X₃.chainComplex R).f (q + 1)
  have hx₂ : x₂ ≫ SC.g.f (q + 1) = z ≫ (X₄.chainComplex R).iCycles (q + 1) := by
    dsimp only [SC, x₂, CommSq.shortComplex_g]
    simpa only [Preadditive.sub_comp, Category.assoc,
      biprod_inl_desc_f, biprod_inr_desc_f] using huv
  have hx₁ : w ≫ (X₁.chainComplex R).iCycles q ≫ SC.f.f q =
      x₂ ≫ SC.X₂.d (q + 1) q := by
    dsimp only [SC, x₂, CommSq.shortComplex_f]
    apply HomologicalComplex.biprodX_ext_to
    · simp only [Category.assoc, biprod_lift_fst_f, Preadditive.sub_comp,
        ← HomologicalComplex.Hom.comm, HomologicalComplex.biprod_inl_fst_f_assoc,
        HomologicalComplex.biprod_inr_fst_f_assoc, zero_comp, comp_zero, sub_zero]
      exact hu.symm
    · simp only [Category.assoc, biprod_lift_snd_f, HomologicalComplex.neg_f_apply,
        Preadditive.comp_neg, Preadditive.sub_comp, ← HomologicalComplex.Hom.comm,
        HomologicalComplex.biprod_inl_snd_f_assoc, HomologicalComplex.biprod_inr_snd_f_assoc,
        zero_comp, comp_zero, zero_sub]
      exact congrArg Neg.neg hv.symm
  have he := (SSet.shortExact_mayerVietorisShortComplex R sq).δ_eq
    (q + 1) q rfl (z ≫ (X₄.chainComplex R).iCycles (q + 1)) (by simp)
    x₂ hx₂ (w ≫ (X₁.chainComplex R).iCycles q)
    (by simpa only [Category.assoc] using hx₁)
    ((ComplexShape.down ℕ).next q) rfl
  have hz : (X₄.chainComplex R).liftCycles
      (z ≫ (X₄.chainComplex R).iCycles (q + 1)) q (ChainComplex.next_nat_succ q)
      (by simp) = z := by
    rw [← cancel_mono ((X₄.chainComplex R).iCycles (q + 1)), liftCycles_i]
  have hw : (X₁.chainComplex R).liftCycles (w ≫ (X₁.chainComplex R).iCycles q)
      ((ComplexShape.down ℕ).next q) rfl (by simp) = w := by
    rw [← cancel_mono ((X₁.chainComplex R).iCycles q), liftCycles_i]
  erw [hz, hw] at he
  rw [mayerVietorisδ_def R sq (q + 1) q rfl]
  exact he

end SSet

end
