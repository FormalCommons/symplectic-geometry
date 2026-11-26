/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Complex.Circle
public import TauCeti.Topology.VectorBundle.FiniteRank.Pullback
public import SymplecticGeometry.Topology.VectorBundle.FiniteRank.Clutching
public import SymplecticGeometry.Topology.VectorBundle.FiniteRank.SMul

/-!
# Laurent families of bundle morphisms, and Laurent clutchings

Let `A` and `D` be finite-rank complex cores over `X`, and let `a i : A ⟶ D` be morphisms indexed
by `i : ℤ`. For `N : ℕ`, the Laurent family `∑_{|i| ≤ N} a_i(x) u^i` is a morphism between the
pullbacks of `A` and `D` to `X × Circle`, whose fibre map at `(x, u)` is
`∑ i ∈ Finset.Icc (-N) N, u ^ i • a_i(x)`. Such a family need not be invertible. Taking
`A = D = E`, the invertible ones are the Laurent clutching functions of [Hatcher2017, §2.1]:
clutching functions on the pullback of `E` to `X × Circle` that are Laurent polynomials in the
circle coordinate.

It is built from Tau Ceti's pullback of morphisms (`TauCeti.FiniteRankBundleCore.pullbackMap`),
the multiplication of morphisms by continuous scalar functions on the base
(`TauCeti.FiniteRankBundleCore.fiberMap_smul`), and Tau Ceti's sums of morphisms
(`TauCeti.FiniteRankBundleCore.fiberMap_sum`), so no continuity argument is needed beyond that of
`(x, u) ↦ u ^ i`.

Multiplying a clutching function `f` by `u ^ m` twists its clutching by a line: the right unitor
`ρ_ E` of the tensor product carries `f ⊗ u ^ m` to `u ^ m • f` fibre by fibre, clutchings by
families that an isomorphism of cores carries to one another are isomorphic, and
`TauCeti.FiniteRankBundleCore.clutchingTensorIso` splits the clutching by `f ⊗ u ^ m`. Since
`u ^ N` times a Laurent family of degree `N` is a polynomial family of degree `2N`, a Laurent
clutching is a polynomial clutching tensored with the clutching of the trivial line by
`u ^ (-N)`, as in [Hatcher2017, §2.1].

## Main definitions and results

* `TauCeti.FiniteRankBundleCore.laurentHom N a`: the Laurent family `∑_{|i| ≤ N} a_i(x) u^i`;
* `TauCeti.FiniteRankBundleCore.fiberMap_laurentHom`: its fibre map at `(x, u)`;
* `TauCeti.FiniteRankBundleCore.zpow_smul_fiberMap_laurentHom`: `u ^ N` times it is the
  polynomial family `∑_{0 ≤ j ≤ 2N} a_{j - N}(x) u^j`;
* `TauCeti.FiniteRankBundleCore.nonempty_iso_clutching_of_fiberMap_comp_eq`: an isomorphism
  `E ≅ E'` that carries `f` to `f'` fibre by fibre gives an isomorphism of the clutchings;
* `TauCeti.FiniteRankBundleCore.circleZPowSMul m f`: the family `u ^ m • f`, which on the trivial
  line by the identity is `circleZPowIso X m` (`circleZPowSMul_refl`);
* `TauCeti.FiniteRankBundleCore.clutching_circleZPowSMul`: the clutching by `u ^ m • f` is the
  clutching by `f` tensored with the clutching of the trivial line by `u ^ m`;
* `TauCeti.FiniteRankBundleCore.exists_clutching_iso_tensor_of_hom_eq_laurentHom`: the
  clutching by a Laurent family of degree `N` is the clutching by a polynomial family of degree
  `2N` tensored with the clutching of the trivial line by `u ^ (-N)`.

## References

* [A. Hatcher, *Vector Bundles and K-Theory*][Hatcher2017], §2.1 (Laurent clutching functions).
-/

public section

noncomputable section

open CategoryTheory

namespace TauCeti.FiniteRankBundleCore

variable {X : Type*} [TopologicalSpace X] {A D : FiniteRankBundleCore ℂ X}

/-- The Laurent family `∑_{|i| ≤ N} a_i(x) u^i` of morphisms `a i : A ⟶ D`: the morphism between
the pullbacks of `A` and `D` to `X × Circle` whose fibre map at `(x, u)` is
`∑ i ∈ Finset.Icc (-N) N, u ^ i • (a i).fiberMap x`. -/
def laurentHom (N : ℕ) (a : ℤ → (A ⟶ D)) :
    A.pullback (ContinuousMap.fst : C(X × Circle, X)) ⟶
      D.pullback (ContinuousMap.fst : C(X × Circle, X)) :=
  ∑ i ∈ Finset.Icc (-(N : ℤ)) N,
    (⟨fun w ↦ ((w.2 ^ i : Circle) : ℂ), by fun_prop⟩ : C(X × Circle, ℂ)) •
      pullbackMap (a i) ContinuousMap.fst

theorem laurentHom_def (N : ℕ) (a : ℤ → (A ⟶ D)) :
    laurentHom N a = ∑ i ∈ Finset.Icc (-(N : ℤ)) N,
      (⟨fun w ↦ ((w.2 ^ i : Circle) : ℂ), by fun_prop⟩ : C(X × Circle, ℂ)) •
        pullbackMap (a i) ContinuousMap.fst :=
  (rfl)

@[simp]
theorem fiberMap_laurentHom (N : ℕ) (a : ℤ → (A ⟶ D)) (w : X × Circle) :
    (laurentHom N a).fiberMap w =
      ∑ i ∈ Finset.Icc (-(N : ℤ)) N, (w.2 : ℂ) ^ i • (a i).fiberMap w.1 := by
  simp only [laurentHom_def, fiberMap_sum, fiberMap_smul, ContinuousMap.coe_mk,
    fiberMap_pullbackMap, ContinuousMap.fst_apply, Circle.coe_zpow]

/-- The Laurent family `∑_{|i| ≤ N} a_i(x) u^i`, multiplied by `u ^ N`, is the polynomial family
`∑_{0 ≤ j ≤ 2N} a_{j - N}(x) u^j`, fibre by fibre. -/
theorem zpow_smul_fiberMap_laurentHom (N : ℕ) (a : ℤ → (A ⟶ D)) (w : X × Circle) :
    (w.2 : ℂ) ^ (N : ℤ) • (laurentHom N a).fiberMap w =
      ∑ j ∈ Finset.range (2 * N + 1), (w.2 : ℂ) ^ j • (a (j - N)).fiberMap w.1 := by
  rw [fiberMap_laurentHom, Finset.smul_sum]
  refine Finset.sum_nbij' (fun i ↦ (i + N).toNat) (fun j ↦ (j : ℤ) - N) (fun i hi ↦ ?_)
    (fun j hj ↦ ?_) (fun i hi ↦ ?_) (fun j _ ↦ by simp) fun i hi ↦ ?_
  · simp only [Finset.mem_Icc] at hi
    simp only [Finset.mem_range]
    omega
  · simp only [Finset.mem_range] at hj
    simp only [Finset.mem_Icc]
    omega
  · simp only [Finset.mem_Icc] at hi
    omega
  · simp only [Finset.mem_Icc] at hi
    have hi' : (((i + N).toNat : ℕ) : ℤ) = i + N := Int.toNat_of_nonneg (by omega)
    rw [smul_smul, ← zpow_natCast, hi', ← zpow_add₀ (Circle.coe_ne_zero w.2), add_comm,
      add_sub_cancel_right]

/-! ### Clutchings by conjugate families -/

/-- **Clutchings by conjugate families are isomorphic.** If an isomorphism `Φ : E ≅ E'` carries
the automorphism `f` of the pullback of `E` to `X × Circle` to the automorphism `f'` of that of
`E'`, fibre by fibre, then the clutching of `E` by `f` is isomorphic to that of `E'` by `f'`. -/
theorem nonempty_iso_clutching_of_fiberMap_comp_eq {𝕜 X : Type*} [NontriviallyNormedField 𝕜]
    [TopologicalSpace X] {E E' : FiniteRankBundleCore 𝕜 X} (Φ : E ≅ E')
    {f : E.pullback (ContinuousMap.fst : C(X × Circle, X)) ≅
      E.pullback (ContinuousMap.fst : C(X × Circle, X))}
    {f' : E'.pullback (ContinuousMap.fst : C(X × Circle, X)) ≅
      E'.pullback (ContinuousMap.fst : C(X × Circle, X))}
    (h : ∀ w : X × Circle, (Φ.hom.fiberMap w.1).comp (f.hom.fiberMap w) =
      (f'.hom.fiberMap w).comp (Φ.hom.fiberMap w.1)) :
    Nonempty (E.clutching f ≅ E'.clutching f') := by
  rw [clutching_def, clutching_def]
  refine nonempty_iso_glue_of_fiberMap_comp_eq _ _ _
    ((pullbackFunctor ContinuousMap.fst).mapIso Φ) fun b ↦ ?_
  simp only [Functor.mapIso_hom, fiberMap_pullbackMap, fiberMap_clutchingAut_hom,
    ContinuousMap.fst_apply]
  have hb := h (SymplecticGeometry.ProjectiveLine.clutchingMap X b)
  rw [SymplecticGeometry.ProjectiveLine.clutchingMap_apply] at hb ⊢
  exact hb

/-! ### Twisting a clutching function by a power of the circle coordinate -/

section CircleZPowSMul

variable {E : FiniteRankBundleCore ℂ X}

/-- The family `u ^ m • f` for an automorphism `f` of the pullback of `E` to `X × Circle` and
`m : ℤ`: the automorphism whose fibre map at `(x, u)` is `u ^ m • f_{(x, u)}`. -/
def circleZPowSMul (m : ℤ)
    (f : E.pullback (ContinuousMap.fst : C(X × Circle, X)) ≅
      E.pullback (ContinuousMap.fst : C(X × Circle, X))) :
    E.pullback (ContinuousMap.fst : C(X × Circle, X)) ≅
      E.pullback (ContinuousMap.fst : C(X × Circle, X)) where
  hom := (⟨fun w ↦ ((w.2 ^ m : Circle) : ℂ), by fun_prop⟩ : C(X × Circle, ℂ)) • f.hom
  inv := (⟨fun w ↦ ((w.2 ^ (-m) : Circle) : ℂ), by fun_prop⟩ : C(X × Circle, ℂ)) • f.inv
  hom_inv_id := hom_ext fun w ↦ by
    simp only [fiberMap_comp, fiberMap_smul, ContinuousMap.coe_mk, Circle.coe_zpow,
      ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp, fiberMap_hom_inv_id, smul_smul,
      fiberMap_id, ← zpow_add₀ (Circle.coe_ne_zero w.2), add_neg_cancel, zpow_zero, one_smul]
  inv_hom_id := hom_ext fun w ↦ by
    simp only [fiberMap_comp, fiberMap_smul, ContinuousMap.coe_mk, Circle.coe_zpow,
      ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp, fiberMap_inv_hom_id, smul_smul,
      fiberMap_id, ← zpow_add₀ (Circle.coe_ne_zero w.2), neg_add_cancel, zpow_zero, one_smul]

@[simp]
theorem fiberMap_circleZPowSMul_hom (m : ℤ)
    (f : E.pullback (ContinuousMap.fst : C(X × Circle, X)) ≅
      E.pullback (ContinuousMap.fst : C(X × Circle, X))) (w : X × Circle) :
    (circleZPowSMul m f).hom.fiberMap w = (w.2 : ℂ) ^ m • f.hom.fiberMap w := by
  simp [circleZPowSMul]

@[simp]
theorem fiberMap_circleZPowSMul_inv (m : ℤ)
    (f : E.pullback (ContinuousMap.fst : C(X × Circle, X)) ≅
      E.pullback (ContinuousMap.fst : C(X × Circle, X))) (w : X × Circle) :
    (circleZPowSMul m f).inv.fiberMap w = ((w.2 : ℂ) ^ m)⁻¹ • f.inv.fiberMap w := by
  simp [circleZPowSMul]

@[simp]
theorem circleZPowSMul_zero
    (f : E.pullback (ContinuousMap.fst : C(X × Circle, X)) ≅
      E.pullback (ContinuousMap.fst : C(X × Circle, X))) :
    circleZPowSMul 0 f = f :=
  Iso.ext <| hom_ext fun w ↦ by simp

/-- On the trivial line, `u ^ m` times the identity is `circleZPowIso X m`. -/
@[simp]
theorem circleZPowSMul_refl (m : ℤ) :
    circleZPowSMul (E := trivial ℂ X 1) m (Iso.refl _) = circleZPowIso X m :=
  Iso.ext <| hom_ext fun w ↦ by simp

@[simp]
theorem circleZPowSMul_circleZPowSMul (m n : ℤ)
    (f : E.pullback (ContinuousMap.fst : C(X × Circle, X)) ≅
      E.pullback (ContinuousMap.fst : C(X × Circle, X))) :
    circleZPowSMul m (circleZPowSMul n f) = circleZPowSMul (m + n) f :=
  Iso.ext <| hom_ext fun w ↦ by
    simp [smul_smul, zpow_add₀ (Circle.coe_ne_zero w.2)]

open MonoidalCategory in
/-- **Twisting a clutching function by `u ^ m`.** The clutching of `E` by `u ^ m • f` is isomorphic
to the tensor product of the clutching of `E` by `f` with the clutching of the trivial line by
`u ^ m`. -/
theorem clutching_circleZPowSMul (m : ℤ)
    (f : E.pullback (ContinuousMap.fst : C(X × Circle, X)) ≅
      E.pullback (ContinuousMap.fst : C(X × Circle, X))) :
    Nonempty (E.clutching (circleZPowSMul m f) ≅
      tensor (E.clutching f) ((trivial ℂ X 1).clutching (circleZPowIso X m))) := by
  -- The right unitor of `E` carries `f ⊗ u ^ m` to `u ^ m • f`, fibre by fibre.
  obtain ⟨φ⟩ := nonempty_iso_clutching_of_fiberMap_comp_eq (E := E ⊗ trivial ℂ X 1) (ρ_ E)
    (f := eqToIso (pullback_tensorObj E (trivial ℂ X 1) _) ≪≫ (f ⊗ᵢ circleZPowIso X m) ≪≫
      eqToIso (pullback_tensorObj E (trivial ℂ X 1) _).symm)
    (f' := circleZPowSMul m f) fun w ↦ by
      rw [fiberMap_eqToIso_tensorIso_hom, fiberMap_circleZPowIso_hom,
        ContinuousLinearMap.kronecker_smul, fiberMap_circleZPowSMul_hom, fiberMap_rightUnitor_hom]
      have key (F : (Fin E.rank → ℂ) →L[ℂ] (Fin E.rank → ℂ)) (c : ℂ) :
          (ContinuousLinearEquiv.kroneckerRid ℂ E.rank : (Fin (E.rank * 1) → ℂ) →L[ℂ] _).comp
              (c • F.kronecker (ContinuousLinearMap.id ℂ (Fin 1 → ℂ))) =
            (c • F).comp
              (ContinuousLinearEquiv.kroneckerRid ℂ E.rank : (Fin (E.rank * 1) → ℂ) →L[ℂ] _) := by
        rw [ContinuousLinearMap.comp_smul, ContinuousLinearMap.kroneckerRid_comp_kronecker,
          ContinuousLinearMap.smul_comp]
      -- The ranks of the tensor product and of the trivial line, unfolded.
      exact key _ _
  exact ⟨φ.symm ≪≫ clutchingTensorIso f (circleZPowIso X m)⟩

/-- **Laurent clutchings are shifted polynomial clutchings.** If the automorphism `g` of the
pullback of `E` to `X × Circle` is the Laurent family `∑_{|i| ≤ N} a_i(x) u^i`, then the
clutching of `E` by `g` is isomorphic to the tensor product of the clutching of `E` by an
automorphism `p` with fibre maps `∑_{0 ≤ j ≤ 2N} a_{j - N}(x) u^j` with the clutching of the
trivial line by `u ^ (-N)`. -/
theorem exists_clutching_iso_tensor_of_hom_eq_laurentHom {N : ℕ} {a : ℤ → (E ⟶ E)}
    {g : E.pullback (ContinuousMap.fst : C(X × Circle, X)) ≅
      E.pullback (ContinuousMap.fst : C(X × Circle, X))} (hg : g.hom = laurentHom N a) :
    ∃ p : E.pullback (ContinuousMap.fst : C(X × Circle, X)) ≅
        E.pullback (ContinuousMap.fst : C(X × Circle, X)),
      (∀ w : X × Circle, p.hom.fiberMap w =
        ∑ j ∈ Finset.range (2 * N + 1), (w.2 : ℂ) ^ j • (a (j - N)).fiberMap w.1) ∧
      Nonempty (E.clutching g ≅
        tensor (E.clutching p) ((trivial ℂ X 1).clutching (circleZPowIso X (-N)))) := by
  refine ⟨circleZPowSMul N g, fun w ↦ ?_, ?_⟩
  · rw [fiberMap_circleZPowSMul_hom, hg, zpow_smul_fiberMap_laurentHom]
  · have h := clutching_circleZPowSMul (-N) (circleZPowSMul N g)
    rwa [circleZPowSMul_circleZPowSMul, neg_add_cancel, circleZPowSMul_zero] at h

end CircleZPowSMul

end TauCeti.FiniteRankBundleCore

end
