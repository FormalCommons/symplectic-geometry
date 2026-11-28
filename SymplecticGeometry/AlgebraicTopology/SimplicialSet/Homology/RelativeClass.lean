/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Relative.Class

/-!
# Relative classes of simplices

For a pair of simplicial sets `Q` (a monomorphism `Q.left ⟶ Q.right`) and an `(n + 1)`-simplex
`s` of `Q.right` whose faces are the images of `n`-simplices `t i` of `Q.left`, the simplex is a
relative cycle, and so has a class `SSetPair.relClass R Q s t ht : R ⟶ Q.homology R (n + 1)` in
relative homology with coefficients in `R`. This generalizes Tau Ceti's `SSetPair.relClass₁`,
the case `n = 0`, to every degree (`SSetPair.relClass_zero`).

The class is natural in maps of pairs (`SSetPair.relClass_homologyMap`), and the connecting
morphism of the pair sends it to the class of the cycle `∑ i, (-1) ^ i • t i` of `Q.left`
(`SSetPair.relClass_homologyδ`); for a `2`-simplex this is the cycle `t 0 - t 1 + t 2` of its
three edges (`SSetPair.relClass_homologyδ_two`). As in Tau Ceti's file, the class needs
preadditive coefficients with coproducts and homology, and the connecting morphism abelian ones.
The proofs adapt those of `SSetPair.relClass₁_cycle`, `SSetPair.relClass₁_homologyMap` and
`SSetPair.relClass₁_homologyδ` from one to every degree; the last is
`ShortComplex.ShortExact.δ_eq` for the short exact sequence of chain complexes of the pair.

## Main definitions and results

* `SSetPair.relClass`: the relative class of a simplex whose faces lie in the subcomplex.
* `SSetPair.relClass_homologyMap`: naturality in maps of pairs.
* `SSetPair.relClass_homologyδ`: its image under the connecting morphism.
* `SSetPair.relClass_zero`: in degree one it is `SSetPair.relClass₁`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 2.1, relative
  homology groups and the long exact sequence of a pair.
-/

public section

noncomputable section

open CategoryTheory Limits Simplicial

universe w v u

namespace SSetPair

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] (R : C) (Q : SSetPair.{w})

section Preadditive

variable [Preadditive C]

/-- The chain of a simplex of the subcomplex vanishes in relative chains. -/
@[reassoc (attr := simp)]
lemma ιChainComplex_hom_app_comp_chainComplexπ_f {n : ℕ} (v : Q.left _⦋n⦌) :
    Q.right.ιChainComplex (R := R) (Q.hom.app (F := Q.left) (G := Q.right) _ v) ≫
      (Q.chainComplexπ R).f n = 0 := by
  rw [← SSet.ι_chainComplexMap_f Q.left Q.right Q.hom R v, Category.assoc,
    chainComplex_condition_f, comp_zero]

variable {Q} {n : ℕ} (s : Q.right _⦋n + 1⦌) (t : Fin (n + 2) → Q.left _⦋n⦌)
  (ht : ∀ i, Q.right.δ i s = Q.hom.app _ (t i))

include ht in
/-- A simplex whose faces lie in the subcomplex defines a relative cycle. -/
lemma relClass_cycle :
    (Q.right.ιChainComplex (R := R) s ≫ (Q.chainComplexπ R).f (n + 1)) ≫
      (Q.chainComplex R).d (n + 1) n = 0 := by
  rw [Category.assoc, (Q.chainComplexπ R).comm, ← Category.assoc, SSet.ιChainComplex_d,
    Preadditive.sum_comp]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rw [ht, Preadditive.zsmul_comp, ιChainComplex_hom_app_comp_chainComplexπ_f, smul_zero]

include ht in
/-- The alternating sum of the faces of a simplex, read in the subcomplex, is carried to the
boundary of the simplex by the inclusion of chains. -/
@[elementwise]
lemma sum_ιChainComplex_comp_chainComplexMap_f :
    (∑ i, (-1 : ℤ) ^ i.val • Q.left.ιChainComplex (R := R) (t i)) ≫
        (SSet.chainComplexMap Q.hom R).f n =
      Q.right.ιChainComplex s ≫ (Q.right.chainComplex R).d (n + 1) n := by
  simp [SSet.ιChainComplex_d, Preadditive.sum_comp, ht]

include ht in
/-- The alternating sum of the faces of a simplex, read in the subcomplex, is a cycle. -/
lemma sum_ιChainComplex_comp_d (k : ℕ) :
    (∑ i, (-1 : ℤ) ^ i.val • Q.left.ιChainComplex (R := R) (t i)) ≫
      (Q.left.chainComplex R).d n k = 0 := by
  rw [← cancel_mono ((SSet.chainComplexMap Q.hom R).f k), Category.assoc,
    ← HomologicalComplex.Hom.comm, ← Category.assoc,
    sum_ιChainComplex_comp_chainComplexMap_f R s t ht, Category.assoc]
  -- The chain complex of `Q.right` appears here also as that of `(𝟭 SSet).obj Q.right`.
  simp only [Functor.id_obj, HomologicalComplex.d_comp_d, comp_zero, zero_comp]

/-- The alternating sum `t 0 - t 1 + t 2` of the three edges of a `2`-simplex, read in the
subcomplex, is a cycle. -/
lemma ιChainComplex_sub_add_comp_d (s : Q.right _⦋2⦌) (t : Fin 3 → Q.left _⦋1⦌)
    (ht : ∀ i, Q.right.δ i s = Q.hom.app _ (t i)) (k : ℕ) :
    (Q.left.ιChainComplex (R := R) (t 0) - Q.left.ιChainComplex (t 1) +
        Q.left.ιChainComplex (t 2)) ≫ (Q.left.chainComplex R).d 1 k = 0 := by
  simpa [Fin.sum_univ_three, sub_eq_add_neg] using sum_ιChainComplex_comp_d R s t ht k

variable [CategoryWithHomology C]

/-- The relative homology class of an `(n + 1)`-simplex `s` of the ambient simplicial set of a
pair whose faces `Q.right.δ i s` are the images of the simplices `t i` of the subcomplex. -/
def relClass : R ⟶ Q.homology R (n + 1) :=
  (Q.chainComplex R).liftCycles (Q.right.ιChainComplex s ≫ (Q.chainComplexπ R).f (n + 1)) n
    (by simp) (relClass_cycle R s t ht) ≫ (Q.chainComplex R).homologyπ (n + 1)

/-- The relative class of a simplex is the homology class of the relative cycle it defines. -/
lemma relClass_def :
    relClass R s t ht =
      (Q.chainComplex R).liftCycles (Q.right.ιChainComplex s ≫ (Q.chainComplexπ R).f (n + 1)) n
        (by simp) (relClass_cycle R s t ht) ≫ (Q.chainComplex R).homologyπ (n + 1) :=
  (rfl)

/-- A map of pairs carries a face of a simplex lying in the subcomplex to a face lying in the
subcomplex. -/
lemma δ_app_right_eq_hom_app {Q' : SSetPair.{w}} (f : Q ⟶ Q') {m : ℕ} (x : Q.right _⦋m + 1⦌)
    (i : Fin (m + 2)) (v : Q.left _⦋m⦌) (h : Q.right.δ i x = Q.hom.app _ v) :
    Q'.right.δ i (f.right.app _ x) = Q'.hom.app _ (f.left.app _ v) := by
  rw [← SSet.δ_naturality_apply, h]
  exact congr($(Arrow.w f.hom).app (Opposite.op ⦋m⦌) v).symm

/-- **Naturality of the relative class of a simplex** in maps of pairs. -/
@[reassoc (attr := simp)]
lemma relClass_homologyMap {Q' : SSetPair.{w}} (f : Q ⟶ Q') :
    relClass R s t ht ≫ SSetPair.homologyMap f R (n + 1) =
      relClass R (f.right.app _ s) (fun i ↦ f.left.app _ (t i))
        (fun i ↦ δ_app_right_eq_hom_app f s i (t i) (ht i)) := by
  rw [relClass_def, relClass_def, Category.assoc, SSetPair.homologyMap,
    HomologicalComplex.homologyπ_naturality, ← Category.assoc,
    HomologicalComplex.liftCycles_comp_cyclesMap]
  congr 2
  rw [Category.assoc, ← HomologicalComplex.comp_f, ← chainComplexπ_naturality,
    HomologicalComplex.comp_f, ← Category.assoc, SSet.ι_chainComplexMap_f]

/-- In degree one, the relative class of a `1`-simplex is Tau Ceti's `SSetPair.relClass₁`; the
face `δ 0` is the last vertex and `δ 1` the first. -/
lemma relClass_zero (s : Q.right _⦋1⦌) (v₀ v₁ : Q.left _⦋0⦌)
    (h₀ : Q.right.δ 1 s = Q.hom.app _ v₀) (h₁ : Q.right.δ 0 s = Q.hom.app _ v₁) :
    relClass R s ![v₁, v₀] (Fin.forall_fin_two.2 ⟨h₁, h₀⟩) = relClass₁ R Q s v₀ v₁ h₀ h₁ := by
  rw [relClass_def, relClass₁_eq]

end Preadditive

section Abelian

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A) {Q : SSetPair.{w}}
  {n : ℕ} (s : Q.right _⦋n + 1⦌) (t : Fin (n + 2) → Q.left _⦋n⦌)
  (ht : ∀ i, Q.right.δ i s = Q.hom.app _ (t i))

/-- **The connecting morphism on the relative class of a simplex** is the class of the
alternating sum `∑ i, (-1) ^ i • t i` of its faces, a cycle of the subcomplex. -/
@[reassoc]
lemma relClass_homologyδ (k : ℕ) (hk : (ComplexShape.down ℕ).next n = k) :
    relClass R s t ht ≫ Q.homologyδ R (n + 1) n =
      (Q.left.chainComplex R).liftCycles
          (∑ i, (-1 : ℤ) ^ i.val • Q.left.ιChainComplex (t i)) k hk
          (sum_ιChainComplex_comp_d R s t ht k) ≫
        (Q.left.chainComplex R).homologyπ n := by
  rw [relClass_def, Category.assoc]
  exact (Q.shortExact_chainComplexShortComplex R).δ_eq (n + 1) n (by simp)
    (Q.right.ιChainComplex s ≫ (Q.chainComplexπ R).f (n + 1)) (relClass_cycle R s t ht)
    (Q.right.ιChainComplex s) rfl _ (sum_ιChainComplex_comp_chainComplexMap_f R s t ht) k hk

/-- **The connecting morphism on the relative class of a `2`-simplex** is the class of the cycle
`t 0 - t 1 + t 2` of its three edges. -/
@[reassoc]
lemma relClass_homologyδ_two (s : Q.right _⦋2⦌) (t : Fin 3 → Q.left _⦋1⦌)
    (ht : ∀ i, Q.right.δ i s = Q.hom.app _ (t i)) :
    relClass R s t ht ≫ Q.homologyδ R 2 1 =
      (Q.left.chainComplex R).liftCycles
          (Q.left.ιChainComplex (t 0) - Q.left.ιChainComplex (t 1) + Q.left.ιChainComplex (t 2))
          0 (by simp)
          (ιChainComplex_sub_add_comp_d R s t ht 0) ≫
        (Q.left.chainComplex R).homologyπ 1 := by
  rw [relClass_homologyδ R s t ht 0 (by simp)]
  congr 2
  simp [Fin.sum_univ_three, sub_eq_add_neg]

end Abelian

end SSetPair

end
