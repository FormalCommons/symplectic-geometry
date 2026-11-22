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
import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Coproduct

/-!
# Smooth chains that vanish in relative singular homology

Let `M` be a Hausdorff `σ`-compact smooth manifold modelled on a finite-dimensional real model
with corners, `U` an open subset of `M`, and `R` a module of coefficients. A smooth singular chain
`w` of `M` whose boundary is a smooth chain of `U` is a relative cycle of the pair `(M, U)`. It
vanishes in the singular homology of `(M, U)` when, as a continuous singular chain,
`w = ∂ B + A` with `B` a singular chain of `M` and `A` a singular chain of `U`. This file proves
that `B` and `A` can then be taken smooth (`TauCeti.exists_smoothSingular_eq_d_add`).

The proof is a diagram chase in the square formed by the inclusions of smooth into continuous
singular chains of `U` and of `M` and the maps induced by `U ⊆ M`, using only the absolute
smoothing theorem for `U` and for `M`
(`TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_opens`), on elements
(`HomologicalComplex.moduleCat_quasiIsoAt_iff`); no relative smooth chain complex is built.

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
  -- The four maps of the square, and its commutativity on elements.
  set jS := SSet.chainComplexMap (smoothSingularSubcomplexMap (Subtype.val : U → M)
    (contMDiff_subtypeVal (I := I))) R
  set jC := SSet.chainComplexMap (TopCat.toSSet.map
    (TopCat.ofHom (ContinuousMap.subtypeVal (U : Set M)))) R
  set ιM := SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R
  set ιU := SSet.chainComplexMap (smoothSingularSubcomplex I U).ι R
  have hsq (i : ℕ) (x) : ιM.f i (jS.f i x) = jC.f i (ιU.f i x) := by
    have h : jS ≫ ιM = ιU ≫ jC := by
      simp only [jS, ιM, ιU, jC, SSet.chainComplexMap, ← Functor.map_comp,
        smoothSingularSubcomplexMap_subtypeVal_ι]
    rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f, h,
      HomologicalComplex.comp_f, ConcreteCategory.comp_apply]
  have hmono : Mono (TopCat.ofHom (ContinuousMap.subtypeVal (U : Set M))) :=
    (TopCat.mono_iff_injective _).2 Subtype.val_injective
  have hjS (i : ℕ) : Function.Injective (jS.f i) :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have hjC (i : ℕ) : Function.Injective (jC.f i) :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have hqU := quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_opens (I := I) R U
  -- `z` is a cycle of `U`, and continuously it is the boundary of `A`.
  have hz : ∀ m', ((smoothSingularSubcomplex I U : SSet).chainComplex R).d m m' z = 0 :=
    fun m' ↦ hjS m' (by
      rw [← HomologicalComplex.Hom.comm_apply, ← hw, HomologicalComplex.d_comp_d_apply,
        map_zero])
  have hzA : ιU.f m z = ((TopCat.toSSet.obj (TopCat.of U)).chainComplex R).d n m A := by
    refine hjC m ?_
    rw [← hsq, ← hw, ← HomologicalComplex.Hom.comm_apply, hwBA, map_add,
      HomologicalComplex.d_comp_d_apply, zero_add]
    -- The domain of `jC` is the chain complex of `U` seen as a set, that of `A` of `U` seen as an
    -- open set: the two types agree by definition, but not syntactically, so `rw` cannot be used.
    exact HomologicalComplex.Hom.comm_apply jC n m A
  -- By smoothing for `U`, `z` is the boundary of a smooth chain `a` of `U`.
  obtain ⟨a, ha⟩ : ∃ a, ((smoothSingularSubcomplex I U : SSet).chainComplex R).d n m a = z := by
    by_cases hnm : (ComplexShape.down ℕ).Rel n m
    · exact ((HomologicalComplex.moduleCat_quasiIsoAt_iff ιU
        ((ComplexShape.down ℕ).prev_eq' hnm) rfl).1 inferInstance).2 z (hz _) A hzA.symm
    · refine ⟨0, hjS m ?_⟩
      rw [map_zero, map_zero, ← hw, HomologicalComplex.shape _ _ _ hnm]
      simp only [ModuleCat.hom_zero, LinearMap.zero_apply]
  -- `A - a` is a continuous cycle of `U`; by smoothing for `U` it is a smooth cycle `x` of `U`
  -- modulo the boundary of a continuous chain `e` of `U`.
  obtain ⟨x, hx, e, he⟩ := ((HomologicalComplex.moduleCat_quasiIsoAt_iff ιU hp hm).1
    inferInstance).1 (A - ιU.f n a) (by
      rw [map_sub, HomologicalComplex.Hom.comm_apply, ha, hzA, sub_self])
  -- `w - a - x` is a smooth cycle of `M` that bounds continuously; by smoothing for `M` it is
  -- the boundary of a smooth chain `b` of `M`.
  obtain ⟨b, hb⟩ := ((HomologicalComplex.moduleCat_quasiIsoAt_iff ιM hp hm).1
    inferInstance).2 (w - jS.f n a - jS.f n x)
    (by
      rw [map_sub, map_sub, hw, HomologicalComplex.Hom.comm_apply, ha,
        HomologicalComplex.Hom.comm_apply, hx, map_zero, sub_self, sub_zero])
    (B + jC.f p e)
    (by
      -- As in `hzA`, `he` must be restated in the domain of `jC` before `rw` can use it.
      have he' : jC.f n (((TopCat.toSSet.obj (TopCat.of (U : Set M))).chainComplex R).d p n e) =
          jC.f n (A - ιU.f n a - ιU.f n x) := congrArg (jC.f n) he
      rw [map_add, HomologicalComplex.Hom.comm_apply, he']
      simp only [map_sub, hsq, hwBA]
      abel)
  exact ⟨b, a + x, by rw [hb, map_add]; abel⟩

end TauCeti
