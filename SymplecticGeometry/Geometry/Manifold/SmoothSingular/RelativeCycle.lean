/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Singular.RelativeClass
public import TauCeti.Algebra.Category.ModuleCat.AB
public import TauCeti.Geometry.Manifold.SmoothSingular.Smoothing

import TauCeti.Algebra.Homology.ModuleCat.Basic
import TauCeti.Algebra.Homology.ModuleCat.QuasiIso
import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Relative.Basic
import TauCeti.Geometry.Manifold.SmoothSingular.Relative

/-!
# Smooth chains that vanish in relative singular homology

Let `M` be a Hausdorff `σ`-compact smooth manifold modelled on a finite-dimensional real model
with corners, `U` an open subset of `M`, and `R` a module of coefficients. A smooth singular chain
`w` of `M` whose boundary is a smooth chain of `U` is a relative cycle of the pair `(M, U)`. It
vanishes in the singular homology of `(M, U)` when, as a continuous singular chain,
`w = ∂ B + A` with `B` a singular chain of `M` and `A` a singular chain of `U`. This file proves
that `B` and `A` can then be taken smooth (`TauCeti.exists_smoothSingular_eq_d_add`).

The proof passes to Tau Ceti's smooth singular pair `TauCeti.smoothSingularPair I U` and its
inclusion `TauCeti.smoothSingularPairι I U` into the singular pair of `(M, U)`, which is a
quasi-isomorphism on relative chains by Tau Ceti's relative smoothing theorem
(`TauCeti.quasiIso_chainComplexMap_smoothSingularPairι`). Injectivity on homology, on elements
(`HomologicalComplex.moduleCat_quasiIsoAt_iff`), and the degreewise exactness of the sequence of
a pair then give the statement.

It follows that a smooth cycle `z` and a smooth `(n + 1)`-simplex `σ` whose faces lie in `U`, with
the same class in the singular homology of `(M, U)`, satisfy `z - σ = ∂ b + c` with `b` a smooth
chain of `M` and `c` a smooth chain of `U`
(`TauCeti.exists_smoothSingular_sub_eq_d_add_of_relClass`). The passage from equal classes to a
continuous decomposition is Tau Ceti's
`CategoryTheory.ShortComplex.ShortExact.moduleCat_exists_sub_eq_d_add`, for the sequence of the
pair.

## Main results

* `TauCeti.exists_smoothSingular_eq_d_add`: a smooth chain with boundary in `U` that is a
  continuous boundary modulo chains of `U` is a smooth boundary modulo smooth chains of `U`.
* `TauCeti.exists_smoothSingular_sub_eq_d_add_of_relClass`: a smooth cycle and a smooth simplex
  with faces in `U` that have the same class in the homology of `(M, U)` differ by a smooth
  boundary and a smooth chain of `U`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Theorem 18.7.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §2.1.
-/

public section

open CategoryTheory TopologicalSpace
open scoped Manifold ContDiff

universe u v

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M]
  {k : Type v} [Ring k] {R : ModuleCat.{u} k}

/-- **Smooth chains that vanish in relative homology.** Let `U` be an open subset of a Hausdorff
`σ`-compact manifold `M`, and `w` a smooth singular `n`-chain of `M` whose boundary `∂ w` is the
image of a smooth chain `z` of `U`. If, as a continuous singular chain, `w = ∂ B + A` for a
singular chain `B` of `M` and a singular chain `A` of `U` (on chains, this says that `w` vanishes
in the singular homology of the pair `(M, U)`), then `w = ∂ b + c` for a smooth singular chain `b`
of `M` and a smooth singular chain `c` of `U`. The degrees `p` and `m` are those above and below
`n` in the complex shape of chain complexes. -/
theorem exists_smoothSingular_eq_d_add (U : Opens M) {n p m : ℕ}
    (hp : (ComplexShape.down ℕ).prev n = p) (hm : (ComplexShape.down ℕ).next n = m)
    (w : ((smoothSingularSubcomplex I M : SSet).chainComplex R).X n)
    (z : ((smoothSingularSubcomplex I U : SSet).chainComplex R).X m)
    (hw : ((smoothSingularSubcomplex I M : SSet).chainComplex R).d n m w =
      (SSet.chainComplexMap (smoothSingularSubcomplexMap (Subtype.val : U → M)
        (contMDiff_subtypeVal (I := I))) R).f m z)
    (B : ((TopCat.toSSet.obj (TopCat.of M)).chainComplex R).X p)
    (A : ((TopCat.toSSet.obj (TopCat.of U)).chainComplex R).X n)
    (hwBA : (SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R).f n w =
      ((TopCat.toSSet.obj (TopCat.of M)).chainComplex R).d p n B +
        (SSet.chainComplexMap (TopCat.toSSet.map
          (TopCat.ofHom (ContinuousMap.subtypeVal (U : Set M)))) R).f n A) :
    ∃ (b : ((smoothSingularSubcomplex I M : SSet).chainComplex R).X p)
      (c : ((smoothSingularSubcomplex I U : SSet).chainComplex R).X n),
      w = ((smoothSingularSubcomplex I M : SSet).chainComplex R).d p n b +
        (SSet.chainComplexMap (smoothSingularSubcomplexMap (Subtype.val : U → M)
          (contMDiff_subtypeVal (I := I))) R).f n c := by
  -- Tau Ceti's smooth singular pair of `(M, U)`, the singular pair of `(M, U)`, and the inclusion
  -- of the first into the second, a quasi-isomorphism on relative chains by the relative
  -- smoothing theorem (`quasiIso_chainComplexMap_smoothSingularPairι`).
  let Ps := smoothSingularPair I U
  let Pc := TopPair.toSSetPair.obj (TopPair.ofSubset (U : Set (TopCat.of M)))
  let f : Ps ⟶ Pc := smoothSingularPairι I U
  -- Restate the claim through the pairs. The chain complexes of `Ps.right` and of the smooth
  -- simplices of `M` (and so on) agree only by unfolding `smoothSingularPair` and the pairs'
  -- constructions, so `rw` cannot pass from one to the other.
  rw [← sub_eq_iff_eq_add'] at hwBA
  simp only [← sub_eq_iff_eq_add']
  revert w z B A
  change ∀ (w : (Ps.right.chainComplex R).X n) (z : (Ps.left.chainComplex R).X m),
    (Ps.right.chainComplex R).d n m w = (SSet.chainComplexMap Ps.hom R).f m z →
    ∀ (B : (Pc.right.chainComplex R).X p) (A : (Pc.left.chainComplex R).X n),
      (show (Pc.right.chainComplex R).X n from
          (SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R).f n w) -
          (Pc.right.chainComplex R).d p n B =
        (SSet.chainComplexMap Pc.hom R).f n A →
      ∃ (b : (Ps.right.chainComplex R).X p) (c : (Ps.left.chainComplex R).X n),
        w - (Ps.right.chainComplex R).d p n b = (SSet.chainComplexMap Ps.hom R).f n c
  intro w z hw B A hwBA
  -- `f.right` is the inclusion of smooth simplices, but `smoothSingularPairι` is not exposed, so
  -- this needs Tau Ceti's lemma.
  replace hwBA : (SSet.chainComplexMap f.right R).f n w - (Pc.right.chainComplex R).d p n B =
      (SSet.chainComplexMap Pc.hom R).f n A := by
    rwa [show f.right = (smoothSingularSubcomplex I M).ι from smoothSingularPairι_right I U]
  -- The image of `w` in the smooth relative chains is a relative cycle, which bounds in the
  -- continuous relative chains, so it bounds a smooth relative chain, the image of some `b`.
  obtain ⟨β, hβ⟩ := ((HomologicalComplex.moduleCat_quasiIsoAt_iff
    (SSetPair.chainComplexMap f R) hp hm).1 inferInstance).2 ((Ps.chainComplexπ R).f n w)
    (by rw [HomologicalComplex.Hom.comm_apply, hw, ← ConcreteCategory.comp_apply]; simp)
    ((Pc.chainComplexπ R).f p B)
    (by
      rw [HomologicalComplex.Hom.comm_apply,
        ← ConcreteCategory.comp_apply ((Ps.chainComplexπ R).f n), ← HomologicalComplex.comp_f,
        ← SSetPair.chainComplexπ_naturality, HomologicalComplex.comp_f,
        ConcreteCategory.comp_apply, eq_comm, ← sub_eq_zero, ← map_sub, hwBA,
        ← ConcreteCategory.comp_apply]
      simp)
  obtain ⟨b, rfl⟩ :=
    (ModuleCat.epi_iff_surjective ((Ps.chainComplexπ R).f p)).1 inferInstance β
  -- Then `w - ∂ b` vanishes in the relative chains, so it is a smooth chain of `U`.
  obtain ⟨c, hc⟩ := (ShortComplex.moduleCat_exact_iff _).1
    (ShortComplex.exact_of_g_is_cokernel (ShortComplex.mk _ _ (Ps.chainComplex_condition_f R n))
      (Ps.isColimitCokernelCoforkChainComplexX R n))
    (w - (Ps.right.chainComplex R).d p n b)
    (by rw [map_sub, ← HomologicalComplex.Hom.comm_apply, hβ, sub_self])
  exact ⟨b, c, hc.symm⟩

omit [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M] in
/-- If the faces of a smooth `(n + 1)`-simplex `σ` lie in an open set `U`, the boundary of
`z - r • σ`, for a smooth cycle `z`, is the image of a smooth chain of `U`. -/
private lemma exists_d_sub_ιChainComplex_eq_chainComplexMap (U : Opens M) {n : ℕ}
    (z : ((smoothSingularSubcomplex I M : SSet).chainComplex R).cycles (n + 1))
    (σ : SmoothSimplex I M (n + 1)) (r : R)
    (hσ : ∀ i, Set.range ((TopCat.of M).toSSetObjEquiv _
      ((TopCat.toSSet.obj (TopCat.of M)).δ i σ.val)) ⊆
        Set.range (TopPair.ofSubset (X := TopCat.of M) (U : Set M)).map) :
    ∃ z' : ((smoothSingularSubcomplex I U : SSet).chainComplex R).X n,
      ((smoothSingularSubcomplex I M : SSet).chainComplex R).d (n + 1) n
          ((((smoothSingularSubcomplex I M : SSet).chainComplex R).iCycles (n + 1)).hom z -
          ((smoothSingularSubcomplex I M : SSet).ιChainComplex (R := R) σ).hom r) =
        (SSet.chainComplexMap (smoothSingularSubcomplexMap (Subtype.val : U → M)
          (contMDiff_subtypeVal (I := I))) R).f n z' := by
  let P := TopPair.ofSubset (X := TopCat.of M) (U : Set M)
  -- The faces of `σ`, as smooth simplices of `U`.
  have hτ (i : Fin (n + 2)) :
      P.liftSimplex _ (hσ i) ∈ (smoothSingularSubcomplex I U).obj _ := by
    rw [← smoothSingularSubcomplex_preimage_subtypeVal (I := I) U]
    -- The inclusion of `U` is the map of the pair `P`.
    change (TopCat.toSSet.map P.map).app _ (P.liftSimplex _ (hσ i)) ∈
      (smoothSingularSubcomplex I M).obj _
    exact Set.mem_of_eq_of_mem (P.toSSet_map_app_liftSimplex _ (hσ i))
      ((smoothSingularSubcomplex I M : SSet).δ i σ).property
  let τ (i : Fin (n + 2)) : SmoothSimplex I U n := ⟨P.liftSimplex _ (hσ i), hτ i⟩
  have hτσ (i : Fin (n + 2)) : (smoothSingularSubcomplexMap (Subtype.val : U → M)
      (contMDiff_subtypeVal (I := I))).app _ (τ i) =
      (smoothSingularSubcomplex I M : SSet).δ i σ :=
    -- The inclusion of `U` into `M` is the map of the pair `P`.
    Subtype.ext ((coe_smoothSingularSubcomplexMap_app _ _).trans
      (by exact P.toSSet_map_app_liftSimplex _ (hσ i)))
  have e : (smoothSingularSubcomplex I M : SSet).ιChainComplex (R := R) σ ≫
      ((smoothSingularSubcomplex I M : SSet).chainComplex R).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        ((smoothSingularSubcomplex I U : SSet).ιChainComplex (R := R) (τ i) ≫
        (SSet.chainComplexMap (smoothSingularSubcomplexMap (Subtype.val : U → M)
          (contMDiff_subtypeVal (I := I))) R).f n) := by
    simp [hτσ]
  refine ⟨-∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
    ((smoothSingularSubcomplex I U : SSet).ιChainComplex (R := R) (τ i)).hom r, ?_⟩
  simp only [map_sub, map_neg, map_sum, map_zsmul, HomologicalComplex.iCycles_d_apply, zero_sub]
  refine neg_inj.2 ((congrArg (fun f ↦ ModuleCat.Hom.hom f r) e).trans ?_)
  simp only [ModuleCat.hom_sum, ModuleCat.hom_zsmul, LinearMap.coe_sum, Finset.sum_apply,
    ModuleCat.hom_comp]
  -- Both sides are the same sum, one written with composites of linear maps.
  rfl

/-- **A smooth cycle and a smooth simplex with the same relative class.** Let `U` be an open
subset of a Hausdorff `σ`-compact manifold `M`, `z` a smooth singular `(n + 1)`-cycle of `M`, and
`σ` a smooth singular `(n + 1)`-simplex of `M` whose faces lie in `U`. If, for some `r : R`, the
image of `z` in the singular homology of the pair `(M, U)` is the class of `r • σ`, then
`z - r • σ = ∂ b + c` for a smooth singular `(n + 2)`-chain `b` of `M` and a smooth singular
`(n + 1)`-chain `c` of `U`. -/
theorem exists_smoothSingular_sub_eq_d_add_of_relClass (U : Opens M) {n : ℕ}
    (z : ((smoothSingularSubcomplex I M : SSet).chainComplex R).cycles (n + 1))
    (σ : SmoothSimplex I M (n + 1)) (r : R)
    (hσ : ∀ i, Set.range ((TopCat.of M).toSSetObjEquiv _
      ((TopCat.toSSet.obj (TopCat.of M)).δ i σ.val)) ⊆
        Set.range (TopPair.ofSubset (X := TopCat.of M) (U : Set M)).map)
    (hcl : ((TopPair.ofSubset (X := TopCat.of M) (U : Set M)).singularHomologyπ R (n + 1)).hom
        ((smoothSingularHomologyIso I M R (n + 1)).hom.hom
          ((((smoothSingularSubcomplex I M : SSet).chainComplex R).homologyπ (n + 1)).hom z)) =
      ((TopPair.ofSubset (X := TopCat.of M) (U : Set M)).relClass R σ.val hσ).hom r) :
    ∃ (b : ((smoothSingularSubcomplex I M : SSet).chainComplex R).X (n + 2))
      (c : ((smoothSingularSubcomplex I U : SSet).chainComplex R).X (n + 1)),
      (((smoothSingularSubcomplex I M : SSet).chainComplex R).iCycles (n + 1)).hom z -
          ((smoothSingularSubcomplex I M : SSet).ιChainComplex (R := R) σ).hom r =
        ((smoothSingularSubcomplex I M : SSet).chainComplex R).d (n + 2) (n + 1) b +
          (SSet.chainComplexMap (smoothSingularSubcomplexMap (Subtype.val : U → M)
            (contMDiff_subtypeVal (I := I))) R).f (n + 1) c := by
  let P := TopPair.ofSubset (X := TopCat.of M) (U : Set M)
  let Q := TopPair.toSSetPair.obj P
  -- The continuous cycle of `z`, and the relative cycle of `σ`.
  let zc : (Q.right.chainComplex R).cycles (n + 1) :=
    HomologicalComplex.cyclesMap (SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R) (n + 1)
      z
  let bc := (Q.chainComplex R).liftCycles
    (Q.right.ιChainComplex σ.val ≫ (Q.chainComplexπ R).f (n + 1)) n (by simp)
    (SSetPair.relClass_cycle (Q := Q) R σ.val _
      fun i ↦ (P.toSSet_map_app_liftSimplex _ (hσ i)).symm)
  have hb : (Q.chainComplex R).iCycles (n + 1) (bc.hom r) =
      (Q.chainComplexπ R).f (n + 1) ((Q.right.ιChainComplex (R := R) σ.val).hom r) := by
    rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, HomologicalComplex.liftCycles_i]
  have hzc : (Q.right.chainComplex R).homologyπ (n + 1) zc =
      (smoothSingularHomologyIso I M R (n + 1)).hom.hom
        ((((smoothSingularSubcomplex I M : SSet).chainComplex R).homologyπ (n + 1)).hom z) := by
    rw [smoothSingularHomologyIso_hom, SSet.homologyMap,
      HomologicalComplex.moduleCat_homologyMap_homologyπ]
    -- The singular simplicial set of `M` is `Q.right`, by unfolding `TopPair.toSSetPair`.
    rfl
  have hrel : (P.relClass R σ.val hσ).hom r = (Q.chainComplex R).homologyπ (n + 1) (bc.hom r) := by
    have h := congrArg (fun f ↦ ModuleCat.Hom.hom f r)
      ((TopPair.relClass_def P R σ.val hσ).trans (SSetPair.relClass_def (Q := Q) _ _ _ _))
    -- The right side of `h` is `bc` followed by `homologyπ`, applied to `r`.
    exact h
  -- In continuous chains, `z - r • σ = ∂ B + A` with `A` a chain of `U`.
  obtain ⟨B, A, -, hBA⟩ := (Q.shortExact_chainComplexShortComplex R).moduleCat_exists_sub_eq_d_add
    (n + 1) (n + 1) (n + 2) (by simp)
    ((Q.right.chainComplex R).iCycles (n + 1) zc) ((Q.right.ιChainComplex (R := R) σ.val).hom r)
    (by simp [HomologicalComplex.shape]) _ (bc.hom r)
    (HomologicalComplex.moduleCat_iCycles_cyclesMap_apply _ _ _ _).symm hb.symm
    ((HomologicalComplex.moduleCat_homologyMap_homologyπ _ (n + 1) zc).symm.trans
      ((congrArg (P.singularHomologyπ R (n + 1)).hom hzc).trans (hcl.trans hrel)))
  have hx : (SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R).f (n + 1)
        ((((smoothSingularSubcomplex I M : SSet).chainComplex R).iCycles (n + 1)).hom z -
        ((smoothSingularSubcomplex I M : SSet).ιChainComplex (R := R) σ).hom r) =
      (Q.right.chainComplex R).iCycles (n + 1) zc -
        (Q.right.ιChainComplex (R := R) σ.val).hom r := by
    rw [map_sub, ← HomologicalComplex.moduleCat_iCycles_cyclesMap_apply]
    congr 1
    exact congrArg (fun f ↦ ModuleCat.Hom.hom f r)
      (SSet.ι_chainComplexMap_f (f := (smoothSingularSubcomplex I M).ι) (R := R) (x := σ))
  obtain ⟨z', hz'⟩ := exists_d_sub_ιChainComplex_eq_chainComplexMap U z σ r hσ
  exact exists_smoothSingular_eq_d_add U (by simp) (by simp) _ z' hz' B A (hx.trans hBA)

end TauCeti
