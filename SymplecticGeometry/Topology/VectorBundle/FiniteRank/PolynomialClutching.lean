/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Topology.VectorBundle.FiniteRank.Clutching
import SymplecticGeometry.Topology.VectorBundle.FiniteRank.Biproduct
import SymplecticGeometry.Topology.VectorBundle.FiniteRank.ElementaryClutching
import SymplecticGeometry.Topology.VectorBundle.FiniteRank.SMul

/-!
# Polynomial clutchings become linear on a sum of copies

Let `E` be a finite-rank complex core over a paracompact R₁ space `X` (for instance a compact
Hausdorff one), and let `p` be an automorphism of the pullback of `E` to `X × Circle` whose fibre
map at `(x, u)` is the polynomial `∑_{i ≤ n} u ^ i • a_i(x)`. Then the Whitney sum of the
clutching of `E` by `p` with `n` copies of the pullback of `E` to `X × ℙ ℂ (Fin 2 → ℂ)` is
isomorphic to a clutching of `E ⊕ ⋯ ⊕ E` (`n + 1` copies) by an automorphism whose fibre map at
`(x, u)` is `u • A(x) + B(x)`, linear in `u`. This is the step of [Hatcher2017, §2.1] that turns
polynomial clutching functions into linear ones.

Hatcher writes down one `(n + 1) × (n + 1)` matrix. Here it is built one row and one column at a
time. If an automorphism `M` of the pullback of `G` is `A + r ≫ s`, then the block matrix
`[[A, s], [-r, 1]]` on `G ⊕ E` is the product of the upper unitriangular block matrix by `-r`, the
block-diagonal `M ⊕ 1`, and the lower unitriangular block matrix by `s`. By
`TauCeti.FiniteRankBundleCore.nonempty_iso_clutching_idAddIso_trans` and
`TauCeti.FiniteRankBundleCore.nonempty_iso_clutching_trans_idAddIso`, its clutching is that of
`M ⊕ 1`, which is the clutching by `M` plus a trivially clutched copy of `E`
(`exists_iso_clutching_whitneySum_of_hom_eq_add_comp`). Taking `r` to be `u` times a constant
morphism and `s` a polynomial of degree `m` followed by a constant morphism, the new block
matrix has the same form, with the constant term of the polynomial moved into its linear part and
a polynomial of degree `m - 1` left; so `m` steps make it linear
(`exists_linear_clutching_iso_of_hom_eq_polynomialHom`).

## Main definitions and results

* `TauCeti.FiniteRankBundleCore.polynomialHom n a`: the polynomial family `∑_{i < n} u^i a_i(x)`
  of morphisms between pullbacks to `X × Circle`;
* `TauCeti.FiniteRankBundleCore.exists_iso_clutching_whitneySum_of_hom_eq_add_comp`: one row
  and one column of Hatcher's matrix;
* `TauCeti.FiniteRankBundleCore.exists_linear_clutching_iso_of_fiberMap_eq_sum`: a polynomial
  clutching of degree `n`, plus `n` copies of the pullback of `E`, is a linear clutching of
  `n + 1` copies of `E`.

## References

* [A. Hatcher, *Vector Bundles and K-Theory*][Hatcher2017], §2.1 (the linearization of
  polynomial clutching functions).
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Preadditive CategoryTheory.Limits

open scoped LinearAlgebra.Projectivization

namespace TauCeti.FiniteRankBundleCore

/-! ### Polynomial families -/

section Polynomial

variable {X : Type*} [TopologicalSpace X]

/-- The pullback of `E` to `X × Circle`, on which the clutching functions live. -/
local notation "Q" E => (FiniteRankBundleCore.pullback E (ContinuousMap.fst : C(X × Circle, X)))

variable (X) in
/-- The coordinate `u` of the circle factor, as a scalar function on `X × Circle`. -/
def circleCoord : C(X × Circle, ℂ) :=
  ⟨fun w ↦ (w.2 : ℂ), by fun_prop⟩

@[simp]
theorem circleCoord_apply (w : X × Circle) : circleCoord X w = w.2 :=
  (rfl)

/-- The coordinate `u` of the circle, as a scalar function on `X × Circle`. -/
local notation "𝔲" => circleCoord X

variable {A D : FiniteRankBundleCore ℂ X}

/-- The polynomial family `∑_{i < n} a_i(x) u^i` of morphisms `a i : A ⟶ D`: the morphism between
the pullbacks of `A` and `D` to `X × Circle` whose fibre map at `(x, u)` is
`∑ i ∈ Finset.range n, u ^ i • (a i).fiberMap x`. -/
def polynomialHom (n : ℕ) (a : ℕ → (A ⟶ D)) : (Q A) ⟶ (Q D) :=
  ∑ i ∈ Finset.range n,
    (⟨fun w ↦ ((w.2 : Circle) : ℂ) ^ i, by fun_prop⟩ : C(X × Circle, ℂ)) •
      pullbackMap (a i) ContinuousMap.fst

theorem polynomialHom_def (n : ℕ) (a : ℕ → (A ⟶ D)) :
    polynomialHom n a = ∑ i ∈ Finset.range n,
      (⟨fun w ↦ ((w.2 : Circle) : ℂ) ^ i, by fun_prop⟩ : C(X × Circle, ℂ)) •
        pullbackMap (a i) ContinuousMap.fst :=
  (rfl)

@[simp]
theorem fiberMap_polynomialHom (n : ℕ) (a : ℕ → (A ⟶ D)) (w : X × Circle) :
    (polynomialHom n a).fiberMap w =
      ∑ i ∈ Finset.range n, (w.2 : ℂ) ^ i • (a i).fiberMap w.1 := by
  simp only [polynomialHom_def, fiberMap_sum, fiberMap_smul, ContinuousMap.coe_mk,
    fiberMap_pullbackMap, ContinuousMap.fst_apply]

@[simp]
theorem polynomialHom_zero (a : ℕ → (A ⟶ D)) : polynomialHom 0 a = 0 := by
  simp [polynomialHom_def]

/-- Horner's rule: a polynomial family is its constant term plus `u` times the polynomial family
of the remaining coefficients. -/
theorem polynomialHom_succ (n : ℕ) (a : ℕ → (A ⟶ D)) :
    polynomialHom (n + 1) a =
      pullbackMap (a 0) ContinuousMap.fst + 𝔲 • polynomialHom n (fun i ↦ a (i + 1)) :=
  hom_ext fun w ↦ by
    simp only [fiberMap_polynomialHom, fiberMap_add, fiberMap_smul, fiberMap_pullbackMap,
      circleCoord_apply, ContinuousMap.fst_apply, Finset.sum_range_succ', pow_succ', mul_smul,
      Finset.smul_sum, pow_zero, one_smul]
    abel

end Polynomial

/-! ### Hatcher's matrix -/

section Hatcher

variable {X : Type*} [TopologicalSpace X] [ParacompactSpace X] [R1Space X]

/-- The pullback of `E` to `X × Circle`, on which the clutching functions live. -/
local notation "Q" E => (FiniteRankBundleCore.pullback E (ContinuousMap.fst : C(X × Circle, X)))

/-- The coordinate `u` of the circle, as a scalar function on `X × Circle`. -/
local notation "𝔲" => circleCoord X

variable {E G : FiniteRankBundleCore ℂ X}

/-- **One row and one column of Hatcher's matrix.** Let `M` be an automorphism of the pullback of
`G` to `X × Circle` that is `A + r ≫ s` for morphisms `r` to and `s` from the pullback of `E`.
Then the block matrix `[[A, s], [-r, 1]]` on `G ⊕ E` is an automorphism, and its clutching is
isomorphic to the Whitney sum of the clutching of `G` by `M` with the pullback of `E` to
`X × ℙ ℂ (Fin 2 → ℂ)`. -/
theorem exists_iso_clutching_whitneySum_of_hom_eq_add_comp (M : (Q G) ≅ (Q G))
    (A : (Q G) ⟶ (Q G)) (r : (Q G) ⟶ (Q E)) (s : (Q E) ⟶ (Q G)) (hM : M.hom = A + r ≫ s) :
    ∃ N : (Q (whitneySum G E)) ≅ (Q (whitneySum G E)),
      N.hom = pullbackMap (whitneyFst G E) ContinuousMap.fst ≫ A ≫
            pullbackMap (whitneyInl G E) ContinuousMap.fst +
          pullbackMap (whitneySnd G E) ContinuousMap.fst ≫ s ≫
            pullbackMap (whitneyInl G E) ContinuousMap.fst -
          pullbackMap (whitneyFst G E) ContinuousMap.fst ≫ r ≫
            pullbackMap (whitneyInr G E) ContinuousMap.fst +
          pullbackMap (whitneySnd G E) ContinuousMap.fst ≫
            pullbackMap (whitneyInr G E) ContinuousMap.fst ∧
        Nonempty ((whitneySum G E).clutching N ≅
          whitneySum (G.clutching M)
            (E.pullback (ContinuousMap.fst : C(X × ℙ ℂ (Fin 2 → ℂ), X)))) := by
  have hl : (whitneySnd (Q G) (Q E) ≫ s ≫ whitneyInl (Q G) (Q E)) ≫
      whitneySnd (Q G) (Q E) ≫ s ≫ whitneyInl (Q G) (Q E) = 0 := by simp
  have hu : (whitneyFst (Q G) (Q E) ≫ (-r) ≫ whitneyInr (Q G) (Q E)) ≫
      whitneyFst (Q G) (Q E) ≫ (-r) ≫ whitneyInr (Q G) (Q E) = 0 := by simp
  let N₁ := whitneyMapIso M (Iso.refl (Q E))
  let N₂ := N₁ ≪≫ idAddIso _ hl
  have key : (idAddIso _ hu ≪≫ N₂).hom =
      whitneyFst (Q G) (Q E) ≫ A ≫ whitneyInl (Q G) (Q E) +
        whitneySnd (Q G) (Q E) ≫ s ≫ whitneyInl (Q G) (Q E) -
        whitneyFst (Q G) (Q E) ≫ r ≫ whitneyInr (Q G) (Q E) +
        whitneySnd (Q G) (Q E) ≫ whitneyInr (Q G) (Q E) := by
    refine whitneySum_hom_ext ?_ ?_ <;>
      simp [N₁, N₂, hM, whitneyMap_def, whitneyLift_def, add_comp, sub_comp, comp_add] <;>
      abel
  refine ⟨idAddIso _ hu ≪≫ N₂, ?_, ?_⟩
  · simp only [pullbackMap_whitneyFst, pullbackMap_whitneySnd, pullbackMap_whitneyInl,
      pullbackMap_whitneyInr]
    exact key
  · obtain ⟨e₁⟩ := nonempty_iso_clutching_idAddIso_trans (E := whitneySum G E) N₂ _ hu
    obtain ⟨e₂⟩ := nonempty_iso_clutching_trans_idAddIso (E := whitneySum G E) N₁ _ hl
    -- `clutchingWhitneySumIso` takes `N₁` read through `pullback_whitneySum`; both are block
    -- diagonal with blocks `M` and `𝟙` in each fibre.
    have hN : whitneyMapIsoPullback M (Iso.refl (Q E)) = N₁ :=
      Iso.ext <| hom_ext fun x ↦ by
        rw [fiberMap_whitneyMapIsoPullback_hom, whitneyMapIso_hom]
        exact (fiberMap_whitneyMap M.hom (Iso.refl (Q E)).hom x).symm
    exact ⟨e₁ ≪≫ e₂ ≪≫ eqToIso (congrArg _ hN.symm) ≪≫
      clutchingWhitneySumIso M (Iso.refl _) ≪≫ whitneyMapIso (Iso.refl _) E.clutchingOneIso⟩

/-- **Hatcher's matrix, by induction.** Let `M` be an automorphism of the pullback of `G` to
`X × Circle` of the form `A₀ + u A₁ + u (π ≫ P ≫ j)`, for constant morphisms `A₀`, `A₁`,
`π : G ⟶ E`, `j : E ⟶ G` and a polynomial family `P` of degree less than `m` in `u`. Then the
Whitney sum of the clutching of `G` by `M` with `m` copies of the pullback of `E` to
`X × ℙ ℂ (Fin 2 → ℂ)` is isomorphic to the clutching of `G ⊕ E ⊕ ⋯ ⊕ E` (`m` copies of `E`) by
an automorphism of the form `B + u A`, for constant endomorphisms `A` and `B`. -/
theorem exists_linear_clutching_iso_of_hom_eq_polynomialHom (m : ℕ) :
    ∀ {G : FiniteRankBundleCore ℂ X} (M : (Q G) ≅ (Q G)) (A₀ A₁ : G ⟶ G) (π : G ⟶ E)
      (j : E ⟶ G) (b : ℕ → (E ⟶ E)),
      M.hom = pullbackMap A₀ ContinuousMap.fst + 𝔲 • pullbackMap A₁ ContinuousMap.fst +
          𝔲 • (pullbackMap π ContinuousMap.fst ≫ polynomialHom m b ≫
            pullbackMap j ContinuousMap.fst) →
      ∃ (A B : whitneySumIter E m G ⟶ whitneySumIter E m G)
        (L : (Q (whitneySumIter E m G)) ≅ (Q (whitneySumIter E m G))),
        L.hom = pullbackMap B ContinuousMap.fst + 𝔲 • pullbackMap A ContinuousMap.fst ∧
          Nonempty (whitneySumIter (E.pullback (ContinuousMap.fst : C(X × ℙ ℂ (Fin 2 → ℂ), X)))
            m (G.clutching M) ≅ (whitneySumIter E m G).clutching L) := by
  induction m with
  | zero =>
    intro G M A₀ A₁ π j b hM
    refine ⟨A₁, A₀, M, hM.trans ?_, ⟨Iso.refl _⟩⟩
    simp only [polynomialHom_zero, Limits.zero_comp, Limits.comp_zero, smul_zero, add_zero]
    rfl
  | succ m ih =>
    intro G M A₀ A₁ π j b hM
    obtain ⟨N, hN, ⟨e⟩⟩ := exists_iso_clutching_whitneySum_of_hom_eq_add_comp (E := E) M
      (pullbackMap A₀ ContinuousMap.fst + 𝔲 • pullbackMap A₁ ContinuousMap.fst)
      (𝔲 • pullbackMap π ContinuousMap.fst)
      (polynomialHom (m + 1) b ≫ pullbackMap j ContinuousMap.fst) (by rw [hM, smul_comp])
    obtain ⟨A, B, L, hL, ⟨e'⟩⟩ := ih N
      (whitneyFst G E ≫ A₀ ≫ whitneyInl G E + whitneySnd G E ≫ b 0 ≫ j ≫ whitneyInl G E +
        whitneySnd G E ≫ whitneyInr G E)
      (whitneyFst G E ≫ A₁ ≫ whitneyInl G E + whitneyFst G E ≫ (-π) ≫ whitneyInr G E)
      (whitneySnd G E) (j ≫ whitneyInl G E) (fun i ↦ b (i + 1)) (by
        rw [hN, polynomialHom_succ]
        simp only [pullbackMap_add, pullbackMap_neg, pullbackMap_comp, add_comp,
          comp_add, smul_comp, comp_smul, Category.assoc, smul_add,
          neg_comp, comp_neg, smul_neg]
        module)
    exact ⟨A, B, L, hL, ⟨whitneySumIterMapIso _ m e.symm ≪≫ e'⟩⟩

/-- **Polynomial clutchings become linear (Hatcher's matrix).** Let `X` be paracompact and R₁, for
instance compact Hausdorff, `E` a finite-rank complex core over `X`, and `p` an automorphism of the
pullback of `E` to `X × Circle` whose fibre map at `(x, u)` is `∑_{i ≤ n} u ^ i • a_i(x)`. Then the
Whitney sum of the clutching of `E` by `p` with `n` copies of the pullback of `E` to
`X × ℙ ℂ (Fin 2 → ℂ)` is isomorphic to the clutching of the Whitney sum `E ⊕ ⋯ ⊕ E` of `n + 1`
copies of `E` by an automorphism whose fibre map at `(x, u)` is `u • A(x) + B(x)`, for
endomorphisms `A` and `B` of that sum. -/
theorem exists_linear_clutching_iso_of_fiberMap_eq_sum (n : ℕ) (a : ℕ → (E ⟶ E))
    (p : (Q E) ≅ (Q E))
    (hp : ∀ w : X × Circle,
      p.hom.fiberMap w = ∑ i ∈ Finset.range (n + 1), (w.2 : ℂ) ^ i • (a i).fiberMap w.1) :
    ∃ (A B : whitneySumIter E n E ⟶ whitneySumIter E n E)
      (L : (Q (whitneySumIter E n E)) ≅ (Q (whitneySumIter E n E))),
      (∀ w : X × Circle, L.hom.fiberMap w = (w.2 : ℂ) • A.fiberMap w.1 + B.fiberMap w.1) ∧
        Nonempty (whitneySumIter (E.pullback (ContinuousMap.fst : C(X × ℙ ℂ (Fin 2 → ℂ), X)))
          n (E.clutching p) ≅ (whitneySumIter E n E).clutching L) := by
  have hp' : p.hom = pullbackMap (a 0) ContinuousMap.fst + 𝔲 • pullbackMap 0 ContinuousMap.fst +
      𝔲 • (pullbackMap (𝟙 E) ContinuousMap.fst ≫ polynomialHom n (fun i ↦ a (i + 1)) ≫
        pullbackMap (𝟙 E) ContinuousMap.fst) := by
    have h : p.hom = polynomialHom (n + 1) a := hom_ext fun w ↦ by rw [hp, fiberMap_polynomialHom]
    rw [h, polynomialHom_succ]
    simp
  obtain ⟨A, B, L, hL, e⟩ :=
    exists_linear_clutching_iso_of_hom_eq_polynomialHom n p (a 0) 0 (𝟙 E) (𝟙 E) _ hp'
  refine ⟨A, B, L, fun w ↦ ?_, e⟩
  rw [hL]
  simp only [fiberMap_add, fiberMap_smul, fiberMap_pullbackMap, circleCoord_apply,
    ContinuousMap.fst_apply]
  exact add_comm _ _

end Hatcher

end TauCeti.FiniteRankBundleCore

end
