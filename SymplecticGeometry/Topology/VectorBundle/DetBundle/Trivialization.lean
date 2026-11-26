/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Topology.VectorBundle.FiniteTrivializingCover
public import TauCeti.Topology.VectorBundle.Determinant
import TauCeti.Topology.VectorBundle.Trivialization

/-!
# Trivializations of the determinant line from arbitrary linear trivializations

Tau Ceti's determinant line `TauCeti.DetBundle 𝕜 F E` of a vector bundle `E` with
finite-dimensional model `F` has, for every linear trivialization `e` of `E`, the
pretrivialization `TauCeti.DetBundle.pretrivialization e`, which reads the fibre over `x` in the
coordinate `TauCeti.DetBundle.chartCoord e`. Tau Ceti makes it a trivialization,
`TauCeti.DetBundle.trivialization e`, only when `e` is in the atlas of `E`. This file shows that
it is a trivialization for every linear `e`: read in the trivialization of the determinant line
at a point, it is multiplication by the determinant of the coordinate change of `E`, which is
continuous since the model is finite-dimensional
(`Bundle.Trivialization.continuousOn_coordChangeL`).

## Main definitions and results

* `TauCeti.DetBundle.trivializationOfIsLinear e`: the trivialization of `det E` over the base set
  of a linear trivialization `e` of `E`, whose pretrivialization is
  `TauCeti.DetBundle.pretrivialization e`. For `e` in the atlas it is Tau Ceti's
  `TauCeti.DetBundle.trivialization e`
  (`TauCeti.DetBundle.trivializationOfIsLinear_eq_trivialization`).
* `TauCeti.DetBundle.coordChangeL_trivializationOfIsLinear`: the coordinate changes of these
  trivializations are the determinants of those of `E`.
* `SymplecticGeometry.Bundle.HasFiniteTrivializingCover.detBundle`: if `E` has a finite
  trivializing cover, so does its determinant line, with model `𝕜`.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press, 1974, §3.
-/

public section

open Bundle Set

namespace TauCeti.DetBundle

variable {𝕜 B F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {E : B → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)] [∀ x, TopologicalSpace (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle 𝕜 F E]

/-- The pretrivialization of `det E` induced by a linear trivialization `e` of `E` is continuous
on its source. -/
theorem continuousOn_pretrivialization (e : Trivialization F (π F E)) [e.IsLinear 𝕜] :
    ContinuousOn (pretrivialization (𝕜 := 𝕜) e) (pretrivialization (𝕜 := 𝕜) e).source := by
  rw [(pretrivialization (𝕜 := 𝕜) e).source_eq, pretrivialization_baseSet]
  refine (vectorPrebundle 𝕜 F E).toFiberPrebundle.continuousOn_of_comp_right e.open_baseSet
    fun b _ ↦ ?_
  set t := trivializationAt F E b
  -- The prebundle's pretrivialization at `b` is that of the bundle's trivialization at `b`.
  -- Mathlib has no lemma for this; it holds by the definition of `FiberPrebundle.toFiberBundle`.
  have hat : (vectorPrebundle 𝕜 F E).toFiberPrebundle.pretrivializationAt b =
      pretrivialization t := by
    rw [← trivialization_toPretrivialization, ← trivializationAt_eq]
    rfl
  rw [hat, pretrivialization_baseSet]
  have hdet : ContinuousOn (fun y : B × 𝕜 ↦ (t.coordChangeL 𝕜 e y.1 : F →L[𝕜] F).det)
      ((e.baseSet ∩ t.baseSet) ×ˢ univ) :=
    ContinuousLinearMap.continuous_det.comp_continuousOn
      ((t.continuousOn_coordChangeL 𝕜 e).comp continuous_fst.continuousOn
        fun y hy ↦ ⟨hy.1.2, hy.1.1⟩)
  refine (continuous_fst.continuousOn.prodMk (hdet.mul continuous_snd.continuousOn)).congr ?_
  rintro ⟨x, c⟩ ⟨⟨hx, hb⟩, -⟩
  rw [Function.comp_apply, ← Pretrivialization.mk_symm _ (by simpa using hb),
    pretrivialization_symm_apply t hb, pretrivialization_apply_mk e hx, chartCoord_chartCoord_symm]
  simp only [Pi.mul_apply]

/-- The inverse of the pretrivialization of `det E` induced by a linear trivialization `e` of `E`
is continuous on its target. -/
theorem continuousOn_pretrivialization_symm (e : Trivialization F (π F E)) [e.IsLinear 𝕜] :
    ContinuousOn (pretrivialization (𝕜 := 𝕜) e).toPartialEquiv.symm
      (pretrivialization (𝕜 := 𝕜) e).target := by
  refine continuousOn_of_locally_continuousOn fun z _ ↦ ?_
  set b := trivializationAt F E z.1
  set t := trivializationAt 𝕜 (DetBundle 𝕜 F E) z.1
  have ht : t = trivialization b := trivializationAt_eq z.1
  refine ⟨b.baseSet ×ˢ univ, b.open_baseSet.prod isOpen_univ,
    ⟨mem_baseSet_trivializationAt F E z.1, mem_univ _⟩, ?_⟩
  have hdet : ContinuousOn (fun y : B × 𝕜 ↦ (e.coordChangeL 𝕜 b y.1 : F →L[𝕜] F).det)
      ((pretrivialization (𝕜 := 𝕜) e).target ∩ b.baseSet ×ˢ univ) :=
    ContinuousLinearMap.continuous_det.comp_continuousOn
      ((e.continuousOn_coordChangeL 𝕜 b).comp continuous_fst.continuousOn
        fun y hy ↦ ⟨pretrivialization_baseSet (𝕜 := 𝕜) e ▸
          (pretrivialization e).mem_target.1 hy.1, hy.2.1⟩)
  refine (t.continuousOn_symm.comp (continuous_fst.continuousOn.prodMk
    (hdet.mul continuous_snd.continuousOn)) fun y hy ↦ ⟨by simpa [ht] using hy.2.1,
      mem_univ _⟩).congr ?_
  rintro ⟨x, c⟩ ⟨hx, hb, -⟩
  replace hx := (pretrivialization (𝕜 := 𝕜) e).mem_target.1 hx
  rw [← Pretrivialization.mk_symm _ hx]
  replace hx : x ∈ e.baseSet := pretrivialization_baseSet (𝕜 := 𝕜) e ▸ hx
  rw [pretrivialization_symm_apply e hx]
  simp only [Function.comp_apply, Pi.mul_apply, ht, trivialization_symm_apply b hb]
  congr 1
  apply (chartCoord b hb).injective
  rw [LinearEquiv.apply_symm_apply, chartCoord_chartCoord_symm e b hx hb]

/-- The trivialization of the determinant line `det E` induced by any linear trivialization `e`
of `E`, over the base set of `e`. It reads the fibre over `x` in the coordinate
`TauCeti.DetBundle.chartCoord e`, and for `e` in the atlas of `E` it is
`TauCeti.DetBundle.trivialization e`. -/
noncomputable def trivializationOfIsLinear (e : Trivialization F (π F E)) [e.IsLinear 𝕜] :
    Trivialization 𝕜 (π 𝕜 (DetBundle 𝕜 F E)) where
  toPartialEquiv := (pretrivialization (𝕜 := 𝕜) e).toPartialEquiv
  open_source := (pretrivialization (𝕜 := 𝕜) e).source_eq ▸
    (pretrivialization (𝕜 := 𝕜) e).open_baseSet.preimage (FiberBundle.continuous_proj 𝕜 _)
  open_target := (pretrivialization e).open_target
  continuousOn_toFun := continuousOn_pretrivialization e
  continuousOn_invFun := continuousOn_pretrivialization_symm e
  baseSet := (pretrivialization e).baseSet
  open_baseSet := (pretrivialization e).open_baseSet
  source_eq := (pretrivialization e).source_eq
  target_eq := (pretrivialization e).target_eq
  proj_toFun := (pretrivialization e).proj_toFun

@[simp]
theorem trivializationOfIsLinear_toPretrivialization (e : Trivialization F (π F E))
    [e.IsLinear 𝕜] :
    (trivializationOfIsLinear (𝕜 := 𝕜) e).toPretrivialization = pretrivialization e := (rfl)

@[simp]
theorem trivializationOfIsLinear_baseSet (e : Trivialization F (π F E)) [e.IsLinear 𝕜] :
    (trivializationOfIsLinear (𝕜 := 𝕜) e).baseSet = e.baseSet :=
  pretrivialization_baseSet e

/-- Over its base set, the trivialization induced by a linear trivialization `e` reads the
determinant line in the chart coordinate of `e`. -/
theorem trivializationOfIsLinear_apply_mk (e : Trivialization F (π F E)) [e.IsLinear 𝕜] {x : B}
    (h : x ∈ e.baseSet) (v : DetBundle 𝕜 F E x) :
    trivializationOfIsLinear e ⟨x, v⟩ = (x, chartCoord e h v) :=
  pretrivialization_apply_mk e h v

/-- Over its base set, the inverse of the trivialization induced by a linear trivialization `e`
is the inverse chart coordinate of `e`. -/
theorem trivializationOfIsLinear_symm_apply (e : Trivialization F (π F E)) [e.IsLinear 𝕜]
    {x : B} (h : x ∈ e.baseSet) (c : 𝕜) :
    (trivializationOfIsLinear e).symm x c = (chartCoord e h).symm c :=
  pretrivialization_symm_apply e h c

instance (e : Trivialization F (π F E)) [e.IsLinear 𝕜] :
    (trivializationOfIsLinear (𝕜 := 𝕜) e).IsLinear 𝕜 :=
  ⟨fun _ ↦ (pretrivialization (𝕜 := 𝕜) e).linear 𝕜⟩

/-- The coordinate changes between the trivializations of `det E` induced by linear
trivializations `e` and `e'` of `E` are the determinants of the coordinate changes of `E`. -/
theorem coordChangeL_trivializationOfIsLinear (e e' : Trivialization F (π F E)) [e.IsLinear 𝕜]
    [e'.IsLinear 𝕜] {x : B} (hx : x ∈ e.baseSet ∩ e'.baseSet) (c : 𝕜) :
    (trivializationOfIsLinear (𝕜 := 𝕜) e).coordChangeL 𝕜 (trivializationOfIsLinear e') x c =
      (e.coordChangeL 𝕜 e' x : F →L[𝕜] F).det * c := by
  rw [Trivialization.coordChangeL_apply _ _ (by simpa using hx),
    trivializationOfIsLinear_symm_apply e hx.1,
    trivializationOfIsLinear_apply_mk e' hx.2, chartCoord_chartCoord_symm]

/-- For a trivialization `e` in the atlas of `E`, the trivialization of `det E` induced by `e` as
a linear trivialization is Tau Ceti's `TauCeti.DetBundle.trivialization e`. -/
theorem trivializationOfIsLinear_eq_trivialization (e : Trivialization F (π F E))
    [MemTrivializationAtlas e] :
    trivializationOfIsLinear (𝕜 := 𝕜) e = trivialization e :=
  Trivialization.toPretrivialization_injective <|
    (trivializationOfIsLinear_toPretrivialization e).trans
      (trivialization_toPretrivialization e).symm

end TauCeti.DetBundle

namespace SymplecticGeometry.Bundle

variable {𝕜 B F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {E : B → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)] [∀ x, TopologicalSpace (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle 𝕜 F E]

/-- If a vector bundle `E` with finite-dimensional model `F` has a finite trivializing cover,
then so does its determinant line `TauCeti.DetBundle 𝕜 F E`, with model `𝕜`: the trivializations
of the determinant line induced by those of the cover have the same base sets. -/
theorem HasFiniteTrivializingCover.detBundle (h : HasFiniteTrivializingCover 𝕜 F E) :
    HasFiniteTrivializingCover 𝕜 𝕜 (TauCeti.DetBundle 𝕜 F E) := by
  obtain ⟨s, hlin, hcover⟩ := (hasFiniteTrivializingCover_def 𝕜 F E).1 h
  have := fun e : s ↦ hlin e e.property
  refine .of_finite
    (fun e : s ↦ TauCeti.DetBundle.trivializationOfIsLinear (𝕜 := 𝕜) (e : Trivialization F _)) ?_
  simpa [iUnion_subtype] using hcover

end SymplecticGeometry.Bundle

end
