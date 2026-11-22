/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.AB
public import TauCeti.Geometry.Manifold.SmoothSingular.Smoothing

import Mathlib.Topology.Category.TopCat.EpiMono
import TauCeti.Algebra.Homology.ModuleCat.QuasiIso
import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Relative.Basic

/-!
# Smooth chains that vanish in relative singular homology

Let `M` be a Hausdorff `σ`-compact smooth manifold modelled on a finite-dimensional real model
with corners, `U` an open subset of `M`, and `R` a module of coefficients. A smooth singular chain
`w` of `M` whose boundary is a smooth chain of `U` is a relative cycle of the pair `(M, U)`. It
vanishes in the singular homology of `(M, U)` when, as a continuous singular chain,
`w = ∂ B + A` with `B` a singular chain of `M` and `A` a singular chain of `U`. This file proves
that `B` and `A` can then be taken smooth (`TauCeti.exists_smoothSingular_eq_d_add`).

The proof passes to the pairs of simplicial sets formed by the smooth, and by the continuous,
singular simplices of `U` and of `M`. The inclusion of smooth into continuous simplices is a
morphism of pairs; by the smoothing theorem for `U` and for `M`
(`TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_opens` and
`TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι`) and the five lemma for
relative chains (`SSetPair.quasiIso_chainComplexMap`), it is a quasi-isomorphism on relative
chains. Injectivity on homology, on elements (`HomologicalComplex.moduleCat_quasiIsoAt_iff`), and
the degreewise exactness of the sequence of a pair then give the statement.

## Main results

* `TauCeti.exists_smoothSingular_eq_d_add`: a smooth chain with boundary in `U` that is a
  continuous boundary modulo chains of `U` is a smooth boundary modulo smooth chains of `U`.

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
  -- The pairs `(M, U)` of smooth and of continuous singular simplices, and the morphism of pairs
  -- given by the inclusions of smooth into continuous simplices; by smoothing for `U` and for `M`
  -- (`SSetPair.quasiIso_chainComplexMap`) it is a quasi-isomorphism on relative chains.
  have : Mono (TopCat.ofHom (ContinuousMap.subtypeVal (U : Set M))) :=
    (TopCat.mono_iff_injective _).2 Subtype.val_injective
  let Ps := SSetPair.of (smoothSingularSubcomplexMap (Subtype.val : U → M)
    (contMDiff_subtypeVal (I := I)))
  let Pc := SSetPair.of (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal (U : Set M))))
  let f : Ps ⟶ Pc := SSetPair.homMk (smoothSingularSubcomplex I U).ι
    (smoothSingularSubcomplex I M).ι (smoothSingularSubcomplexMap_subtypeVal_ι U).symm
  have : QuasiIso (SSet.chainComplexMap f.left R) :=
    quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_opens R U
  have : QuasiIso (SSet.chainComplexMap f.right R) :=
    quasiIso_chainComplexMap_smoothSingularSubcomplex_ι R
  have := SSetPair.quasiIso_chainComplexMap f R
  -- Restate the claim through the pairs. The chain complexes of `Ps.right` and of the smooth
  -- simplices of `M` (and so on) agree only by unfolding `SSetPair.of`, so `rw` cannot pass from
  -- one to the other.
  rw [← sub_eq_iff_eq_add'] at hwBA
  simp only [← sub_eq_iff_eq_add']
  revert w z B A
  change ∀ (w : (Ps.right.chainComplex R).X n) (z : (Ps.left.chainComplex R).X m),
    (Ps.right.chainComplex R).d n m w = (SSet.chainComplexMap Ps.hom R).f m z →
    ∀ (B : (Pc.right.chainComplex R).X p) (A : (Pc.left.chainComplex R).X n),
      (SSet.chainComplexMap f.right R).f n w - (Pc.right.chainComplex R).d p n B =
        (SSet.chainComplexMap Pc.hom R).f n A →
      ∃ (b : (Ps.right.chainComplex R).X p) (c : (Ps.left.chainComplex R).X n),
        w - (Ps.right.chainComplex R).d p n b = (SSet.chainComplexMap Ps.hom R).f n c
  intro w z hw B A hwBA
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

end TauCeti
