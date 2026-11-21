/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Cayley
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Section.Topology
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Symplectic.ComplexStructure.Basic

/-!
# Contractibility of tame and compatible structures and forms on a vector bundle

Let `V` be a real vector bundle of finite rank over a Hausdorff σ-compact manifold modelled on a
finite-dimensional space. This file proves that for a nondegenerate two-form `ω` on `V` the
complex structures tamed by `ω`, and those compatible with `ω`, form contractible spaces, and that
for a complex structure `J` the two-forms that tame `J`, and those compatible with `J`, form
contractible spaces, for the frame topologies of the endomorphism bundle and of the bundle of
alternating forms, in every regularity `Cⁿ`.

For the forms, the two sets are convex and nonempty in a topological vector space, so Mathlib's
`Convex.contractibleSpace` applies.

For the structures, fix a complex structure `J₀` compatible with `ω`. At each point `x` the
Cayley path `TauCeti.cayleyPathFormula (smoothTransition t) (J₀ x) (J x)` joins `J₀ x` to an
`ω`-tame `J x` through `ω`-tame structures, compatible ones when `J x` is compatible. The path is
a fibrewise formula in `J`, jointly smooth in `t` and the fibre value on an open set
`Bundle.cayleyPathDomain` of the endomorphism bundle that contains the values of every `ω`-tame
structure; so it gives complex structures
`SymplecticGeometry.Bundle.ContMDiffTwoForm.Compatible.cayleyPath`, jointly continuous in `t` and
`J` by `ContMDiffSection.continuous_fiberwiseMap`. Run backwards, it contracts the space of
`ω`-tame structures, and the space of `ω`-compatible structures, to `J₀`.

## Main definitions and results

* `SymplecticGeometry.Bundle.ContMDiffTwoForm.Compatible.cayleyPath`: the Cayley path from an
  `ω`-compatible to an `ω`-tame complex structure.
* `SymplecticGeometry.Bundle.ContMDiffTwoForm.IsNondegenerate.contractibleSpace_tames`,
  `SymplecticGeometry.Bundle.ContMDiffTwoForm.IsNondegenerate.contractibleSpace_compatible`: the
  complex structures tamed by, or compatible with, a nondegenerate form form contractible spaces.
* `SymplecticGeometry.Bundle.ContMDiffComplexStructure.contractibleSpace_tames`,
  `SymplecticGeometry.Bundle.ContMDiffComplexStructure.contractibleSpace_compatible`: the
  two-forms that tame, or are compatible with, a complex structure form contractible spaces.

The construction of `Compatible.cayleyPath` adapts Tau Ceti's
`TauCeti.SmoothTwoForm.Compatible.cayleyPath`, for the tangent bundle and smooth structures, to
any vector bundle and any regularity.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Proposition 2.5.13 and Proposition 2.6.4
-/

public section

noncomputable section

open _root_.Bundle Set Topology TopologicalSpace TauCeti
open scoped Manifold

namespace SymplecticGeometry.Bundle

variable {EB HB M : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [TopologicalSpace HB] {I : ModelWithCorners ℝ EB HB}
  [TopologicalSpace M] [ChartedSpace HB M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V] {n : ℕ∞}

namespace ContMDiffComplexStructure

/-- For a complex structure `J₀`, the Cayley path `cayleyPathFormula (smoothTransition t) (J₀ x) B`
from `J₀ x` to an endomorphism `B` of the fibre over `x` is jointly `Cⁿ` in `t` and the point
`⟨x, B⟩` of the endomorphism bundle, on the domain of the Cayley path from `J₀`. -/
theorem contMDiffOn_cayleyPathFormula
    (J₀ : ContMDiffComplexStructure I n F V) :
    ContMDiffOn (𝓘(ℝ).prod (I.prod 𝓘(ℝ, F →L[ℝ] F))) (I.prod 𝓘(ℝ, F →L[ℝ] F)) n
      (fun q : ℝ × TotalSpace (F →L[ℝ] F) (fun x ↦ V x →L[ℝ] V x) ↦
        TotalSpace.mk' (F →L[ℝ] F) (E := fun x ↦ V x →L[ℝ] V x) q.2.proj
          (cayleyPathFormula (Real.smoothTransition q.1) (J₀ q.2.proj) q.2.snd))
      (univ ×ˢ cayleyPathDomain F V fun q ↦ J₀ q.proj) := by
  rintro ⟨t, q⟩ ⟨-, hq⟩
  have hb : t.smoothTransition ∈ Icc (0 : ℝ) 1 :=
    ⟨Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t⟩
  have hu := isUnit_of_mem_cayleyPathDomain hq hb
  have hproj : ContMDiff (𝓘(ℝ).prod (I.prod 𝓘(ℝ, F →L[ℝ] F))) I n
      (fun p : ℝ × TotalSpace (F →L[ℝ] F) (fun x ↦ V x →L[ℝ] V x) ↦ p.2.proj) :=
    (contMDiff_proj _).comp contMDiff_snd
  exact (ContMDiffAt.cayleyPathFormula_hom_bundle_of_vectorBundle
    (f := fun p : ℝ × TotalSpace (F →L[ℝ] F) (fun x ↦ V x →L[ℝ] V x) ↦ p.2.proj)
    (b := fun p ↦ Real.smoothTransition p.1) (A := fun p ↦ J₀ p.2.proj) (B := fun p ↦ p.2.snd)
    hproj.contMDiffAt
    (Real.smoothTransition.contDiff.contMDiff.comp contMDiff_fst).contMDiffAt
    (J₀.toEndomorphism.contMDiff.comp hproj).contMDiffAt contMDiff_snd.contMDiffAt
    hu.1 hu.2).contMDiffWithinAt

end ContMDiffComplexStructure

namespace ContMDiffTwoForm

section CayleyPath

variable {ω : ContMDiffTwoForm I n F V} {J₀ J : ContMDiffComplexStructure I n F V}

/-- For an `ω`-compatible `J₀` and an `ω`-tame `J`, the values of `J` lie in the domain of the
Cayley path from `J₀`. -/
theorem Compatible.mem_cayleyPathDomain (h₀ : ω.Compatible J₀) (h : ω.Tames J) (x : M) :
    (⟨x, J x⟩ : TotalSpace (F →L[ℝ] F) (fun x ↦ V x →L[ℝ] V x)) ∈
      cayleyPathDomain F V fun q ↦ J₀ q.proj :=
  (h₀.compatibleAt x).mem_cayleyPathDomain (h₀.isNondegenerate.tames_iff.1 h x)
    (J₀.almostComplexStructureAt_toLinearMap x).symm
    (J.almostComplexStructureAt_toLinearMap x).symm


/-- The Cayley path from an `ω`-compatible complex structure `J₀` to an `ω`-tame complex
structure `J`, at time `t`: the complex structure whose value at `x` is
`cayleyPathFormula (smoothTransition t) (J₀ x) (J x)`. It is `J₀` for `t ≤ 0` and `J` for
`1 ≤ t`, and every structure on it is `ω`-tame. -/
def Compatible.cayleyPath (h₀ : ω.Compatible J₀) (h : ω.Tames J) (t : ℝ) :
    ContMDiffComplexStructure I n F V where
  toEndomorphism := ContMDiffSection.fiberwiseMap
    (fun t x B ↦ cayleyPathFormula (Real.smoothTransition t) (J₀ x) B)
    J₀.contMDiffOn_cayleyPathFormula t ⟨J.toEndomorphism, h₀.mem_cayleyPathDomain h⟩
  square_neg x := by
    obtain ⟨K, hK, -⟩ := (h₀.compatibleAt x).exists_toLinearMap_eq_cayleyPathFormula
      (h₀.isNondegenerate.tames_iff.1 h x)
      ((trivializationAt F V x).continuousLinearEquivAt ℝ x (mem_baseSet_trivializationAt F V x))
      (J₀.almostComplexStructureAt_toLinearMap x).symm
      (J.almostComplexStructureAt_toLinearMap x).symm t
    ext v
    have hv (w : V x) : cayleyPathFormula (Real.smoothTransition t) (J₀ x) (J x) w = K w :=
      (LinearMap.congr_fun hK w).symm
    simp only [ContMDiffSection.fiberwiseMap_apply, ContinuousLinearMap.comp_apply, hv,
      AlmostComplexStructure.apply_apply, neg_apply,
      ContinuousLinearMap.id_apply]

variable (h₀ : ω.Compatible J₀) (h : ω.Tames J)

/-- The value of the Cayley path at `x` is `cayleyPathFormula (smoothTransition t) (J₀ x) (J x)`.
-/
@[simp]
theorem Compatible.cayleyPath_apply (t : ℝ) (x : M) :
    h₀.cayleyPath h t x = cayleyPathFormula (Real.smoothTransition t) (J₀ x) (J x) :=
  ContMDiffSection.fiberwiseMap_apply _ _ t _ x

/-- At each point `x`, the value of the Cayley path is an almost complex structure `K` on the fibre
that the linear symplectic form of `ω` at `x` tames, and with which it is compatible when `ω` is
compatible with `J`. -/
theorem Compatible.exists_almostComplexStructureAt_cayleyPath (t : ℝ) (x : M) :
    ∃ K : AlmostComplexStructure (V x),
      (h₀.cayleyPath h t).almostComplexStructureAt x = K ∧
        (h₀.isNondegenerate.symplecticFormAt x).Tames K ∧
        (ω.Compatible J → (h₀.isNondegenerate.symplecticFormAt x).Compatible K) := by
  obtain ⟨K, hK, hT, hC⟩ := (h₀.compatibleAt x).exists_toLinearMap_eq_cayleyPathFormula
    (h₀.isNondegenerate.tames_iff.1 h x)
    ((trivializationAt F V x).continuousLinearEquivAt ℝ x (mem_baseSet_trivializationAt F V x))
    (J₀.almostComplexStructureAt_toLinearMap x).symm
    (J.almostComplexStructureAt_toLinearMap x).symm t
  refine ⟨K, AlmostComplexStructure.toLinearMap_injective ?_, hT, fun hJ ↦ hC ?_⟩
  · rw [ContMDiffComplexStructure.almostComplexStructureAt_toLinearMap, hK,
      h₀.cayleyPath_apply]
  · exact hJ.compatibleAt x

/-- Every structure on the Cayley path from an `ω`-compatible to an `ω`-tame structure is
`ω`-tame. -/
theorem Compatible.tames_cayleyPath (t : ℝ) : ω.Tames (h₀.cayleyPath h t) :=
  h₀.isNondegenerate.tames_iff.2 fun x ↦ by
    obtain ⟨K, hK, hT, -⟩ := h₀.exists_almostComplexStructureAt_cayleyPath h t x
    rwa [hK]

/-- Every structure on the Cayley path between two `ω`-compatible structures is
`ω`-compatible. -/
theorem Compatible.compatible_cayleyPath (h : ω.Compatible J) (t : ℝ) :
    ω.Compatible (h₀.cayleyPath h.tames t) :=
  h₀.isNondegenerate.compatible_iff.2 fun x ↦ by
    obtain ⟨K, hK, -, hC⟩ := h₀.exists_almostComplexStructureAt_cayleyPath h.tames t x
    rw [hK]
    exact hC h

/-- The Cayley path is at `J₀` for `t ≤ 0`. -/
@[simp]
theorem Compatible.cayleyPath_of_nonpos {t : ℝ} (ht : t ≤ 0) : h₀.cayleyPath h t = J₀ := by
  ext x v
  rw [h₀.cayleyPath_apply, Real.smoothTransition.zero_of_nonpos ht, cayleyPathFormula_zero]

/-- The Cayley path is at `J` for `1 ≤ t`. -/
@[simp]
theorem Compatible.cayleyPath_of_one_le {t : ℝ} (ht : 1 ≤ t) : h₀.cayleyPath h t = J := by
  ext x v
  have hJ₀ : J₀ x * J₀ x = -1 := by
    rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.one_def]
    exact J₀.square_neg x
  rw [h₀.cayleyPath_apply, Real.smoothTransition.one_of_one_le ht, cayleyPathFormula_one hJ₀
    (isUnit_of_mem_cayleyPathDomain (h₀.mem_cayleyPathDomain h x) ⟨zero_le_one, le_rfl⟩).1]

variable [IsManifold I n M] [ContMDiffVectorBundle n F V I] [LocallyCompactSpace EB] {ι : Type*}
  (e : ι → Trivialization (F →L[ℝ] F) (π (F →L[ℝ] F) (fun x ↦ V x →L[ℝ] V x)))
  [∀ i, MemTrivializationAtlas (e i)]
  (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)

/-- For a covering frame system, the Cayley path from an `ω`-compatible structure `J₀` to an
`ω`-tame structure `J` is jointly continuous in the time and in `J`, for the frame topology. -/
theorem Compatible.continuous_cayleyPath (hcover : ∀ x, ∃ i, x ∈ U i) :
    letI := ContMDiffComplexStructure.frameTopology (I := I) (n := n) e U hU
    Continuous fun p : ℝ × {J : ContMDiffComplexStructure I n F V // ω.Tames J} ↦
      h₀.cayleyPath p.2.property p.1 := by
  let _ := ContMDiffSection.frameTopology (I := I) (n := n) e U hU
  let _ := ContMDiffComplexStructure.frameTopology (I := I) (n := n) e U hU
  have hO : IsOpen (cayleyPathDomain F V fun q ↦ J₀ q.proj) := by
    simpa using isOpen_cayleyPathDomain (A := fun q ↦ J₀ q.proj) isOpen_univ
      (J₀.toEndomorphism.contMDiff.continuous.comp (FiberBundle.continuous_proj _ _)).continuousOn
  have hs : Continuous fun J : {J : ContMDiffComplexStructure I n F V // ω.Tames J} ↦
      (⟨J.val.toEndomorphism, h₀.mem_cayleyPathDomain J.property⟩ :
        {s : Cₛ^n⟮I; F →L[ℝ] F, fun x ↦ V x →L[ℝ] V x⟯ //
          ∀ x, ⟨x, s x⟩ ∈ cayleyPathDomain F V fun q ↦ J₀ q.proj}) :=
    ((ContMDiffComplexStructure.isEmbedding_toEndomorphism_frameTopology e U hU).continuous.comp
      continuous_subtypeVal).subtype_mk _
  refine (ContMDiffComplexStructure.continuous_frameTopology_iff e U hU).2 ?_
  exact (ContMDiffSection.continuous_fiberwiseMap _ J₀.contMDiffOn_cayleyPathFormula e U hU e U hU
    hO hcover).comp (continuous_fst.prodMk (hs.comp continuous_snd))

end CayleyPath

section Contractible

variable [FiniteDimensional ℝ EB] [T2Space M] [SigmaCompactSpace M]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] [ContMDiffVectorBundle n F V I]
  {ω : ContMDiffTwoForm I n F V} {ι : Type*}
  (e : ι → Trivialization (F →L[ℝ] F) (π (F →L[ℝ] F) (fun x ↦ V x →L[ℝ] V x)))
  [∀ i, MemTrivializationAtlas (e i)]
  (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)

/-- Over a Hausdorff σ-compact base modelled on a finite-dimensional space, the complex structures
tamed by a nondegenerate two-form `ω` on a vector bundle of finite rank form a contractible space,
for the frame topology in any covering frames. It is contracted to an `ω`-compatible structure
`J₀` along the Cayley paths from `J₀`. -/
theorem IsNondegenerate.contractibleSpace_tames (hω : ω.IsNondegenerate)
    (hcover : ∀ x, ∃ i, x ∈ U i) :
    letI := ContMDiffComplexStructure.frameTopology (I := I) (n := n) e U hU
    ContractibleSpace {J : ContMDiffComplexStructure I n F V // ω.Tames J} := by
  let _ := ContMDiffComplexStructure.frameTopology (I := I) (n := n) e U hU
  obtain ⟨J₀, h₀⟩ := hω.exists_compatible
  refine (contractible_iff_id_nullhomotopic _).2 ⟨⟨J₀, h₀.tames⟩, ⟨{
    toFun := fun p ↦ ⟨h₀.cayleyPath p.2.property (1 - p.1), h₀.tames_cayleyPath p.2.property _⟩
    continuous_toFun := ((h₀.continuous_cayleyPath e U hU hcover).comp
      ((continuous_const.sub (continuous_subtypeVal.comp continuous_fst)).prodMk
        continuous_snd)).subtype_mk _
    map_zero_left := fun J ↦ Subtype.ext (h₀.cayleyPath_of_one_le J.property (by simp))
    map_one_left := fun J ↦ Subtype.ext (h₀.cayleyPath_of_nonpos J.property (by simp)) }⟩⟩

/-- Over a Hausdorff σ-compact base modelled on a finite-dimensional space, the complex structures
compatible with a nondegenerate two-form `ω` on a vector bundle of finite rank form a contractible
space, for the frame topology in any covering frames. It is contracted to one of them, `J₀`, along
the Cayley paths from `J₀`. -/
theorem IsNondegenerate.contractibleSpace_compatible (hω : ω.IsNondegenerate)
    (hcover : ∀ x, ∃ i, x ∈ U i) :
    letI := ContMDiffComplexStructure.frameTopology (I := I) (n := n) e U hU
    ContractibleSpace {J : ContMDiffComplexStructure I n F V // ω.Compatible J} := by
  let _ := ContMDiffComplexStructure.frameTopology (I := I) (n := n) e U hU
  obtain ⟨J₀, h₀⟩ := hω.exists_compatible
  have hc : Continuous fun J : {J : ContMDiffComplexStructure I n F V // ω.Compatible J} ↦
      (⟨J.val, J.property.tames⟩ : {J : ContMDiffComplexStructure I n F V // ω.Tames J}) :=
    continuous_subtypeVal.subtype_mk _
  refine (contractible_iff_id_nullhomotopic _).2 ⟨⟨J₀, h₀⟩, ⟨{
    toFun := fun p ↦ ⟨h₀.cayleyPath p.2.property.tames (1 - p.1),
      h₀.compatible_cayleyPath p.2.property _⟩
    continuous_toFun := ((h₀.continuous_cayleyPath e U hU hcover).comp
      ((continuous_const.sub (continuous_subtypeVal.comp continuous_fst)).prodMk
        (hc.comp continuous_snd))).subtype_mk _
    map_zero_left := fun J ↦ Subtype.ext (h₀.cayleyPath_of_one_le J.property.tames (by simp))
    map_one_left := fun J ↦ Subtype.ext (h₀.cayleyPath_of_nonpos J.property.tames (by simp)) }⟩⟩

end Contractible

end ContMDiffTwoForm

namespace ContMDiffComplexStructure

variable [FiniteDimensional ℝ EB] [T2Space M] [SigmaCompactSpace M]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] [ContMDiffVectorBundle n F V I] {κ : Type*}
  (e : κ → Trivialization (F [⋀^Fin 2]→L[ℝ] ℝ)
    (π (F [⋀^Fin 2]→L[ℝ] ℝ) (fun x ↦ V x [⋀^Fin 2]→L[ℝ] Trivial M ℝ x)))
  [∀ j, MemTrivializationAtlas (e j)]
  (U : κ → Opens M) (hU : ∀ j, (U j : Set M) ⊆ (e j).baseSet)

/-- Over a Hausdorff σ-compact base modelled on a finite-dimensional space, the two-forms that
tame a complex structure `J` on a vector bundle of finite rank form a contractible space, for the
frame topology in any frames: a nonempty convex set in a topological vector space. Since a
contractible space is nonempty, such forms exist. -/
theorem contractibleSpace_tames (J : ContMDiffComplexStructure I n F V) :
    letI := ContMDiffSection.frameTopology (I := I) (n := n) e U hU
    ContractibleSpace {ω : ContMDiffTwoForm I n F V // ω.Tames J} := by
  let _ := ContMDiffSection.frameTopology (I := I) (n := n) e U hU
  let _ := ContMDiffSection.isTopologicalAddGroup_frameTopology (I := I) (n := n) e U hU
  let _ := ContMDiffSection.continuousSMul_frameTopology (I := I) (n := n) e U hU
  obtain ⟨ω, hω⟩ := J.exists_compatible
  exact (ContMDiffTwoForm.convex_setOf_tames J).contractibleSpace ⟨ω, hω.tames⟩

/-- Over a Hausdorff σ-compact base modelled on a finite-dimensional space, the two-forms
compatible with a complex structure `J` on a vector bundle of finite rank form a contractible
space, for the frame topology in any frames: a nonempty convex set in a topological vector space.
Since a contractible space is nonempty, such forms exist. -/
theorem contractibleSpace_compatible (J : ContMDiffComplexStructure I n F V) :
    letI := ContMDiffSection.frameTopology (I := I) (n := n) e U hU
    ContractibleSpace {ω : ContMDiffTwoForm I n F V // ω.Compatible J} := by
  let _ := ContMDiffSection.frameTopology (I := I) (n := n) e U hU
  let _ := ContMDiffSection.isTopologicalAddGroup_frameTopology (I := I) (n := n) e U hU
  let _ := ContMDiffSection.continuousSMul_frameTopology (I := I) (n := n) e U hU
  obtain ⟨ω, hω⟩ := J.exists_compatible
  exact (ContMDiffTwoForm.convex_setOf_compatible J).contractibleSpace ⟨ω, hω⟩

end ContMDiffComplexStructure

end SymplecticGeometry.Bundle

end
