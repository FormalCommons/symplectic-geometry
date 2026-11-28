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
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Map.Topology
import SymplecticGeometry.Topology.Homotopy.Affine

/-!
# Tame and compatible structures and forms on a vector bundle: contractibility and the polar map

Let `V` be a real vector bundle of finite rank over a Hausdorff σ-compact manifold modelled on a
finite-dimensional space. This file proves that for a nondegenerate two-form `ω` on `V` the
complex structures tamed by `ω`, and those compatible with `ω`, form contractible spaces, and that
for a complex structure `J` the two-forms that tame `J`, and those compatible with `J`, form
contractible spaces, for the frame topologies of the endomorphism bundle and of the bundle of
alternating forms, in every regularity `Cⁿ`. For a bundle metric `g`, the map `ω ↦ J_{g,ω}` from
the nondegenerate two-forms to the complex structures is moreover a homotopy equivalence, with
homotopy inverse `J ↦ ω_{g,J}`, and its homotopy class does not depend on `g`.

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
`ω`-tame structures, and the space of `ω`-compatible structures, to `J₀`, keeping `J₀` fixed
(`Compatible.cayleyContraction` and `Compatible.compatibleCayleyContraction`).

For the homotopy equivalence, `ω` and `ω_{g,J_{g,ω}}` both tame `J_{g,ω}`, so the segment between
them stays among the nondegenerate forms. For metrics `g₀` and `g₁`, the structures `J` and
`J_{g₁,ω_{g₀,J}}` are both compatible with `ω_{g₀,J}`, so `Compatible.cayleyPath` joins the
second to the first. For its continuity in `J`, the reference is read as a function of the fibre
value of `J`, defined and smooth on the open set
`Bundle.ContMDiffRiemannianMetric.polarEndDomain g₀`; both continuity statements come from
`Bundle.continuous_fiberwiseMap_cayleyPathFormula`, for any reference that is smooth on an open
set. With `g₀ = g₁ = g` the
segment and the path are the two homotopies of the equivalence; with two metrics they show that
`ω ↦ J_{g₀,ω}` and `ω ↦ J_{g₁,ω}` are homotopic.

## Main definitions and results

* `SymplecticGeometry.Bundle.ContMDiffTwoForm.Compatible.cayleyPath`: the Cayley path from an
  `ω`-compatible to an `ω`-tame complex structure, constant from `J₀` to itself
  (`Compatible.cayleyPath_self`).
* `SymplecticGeometry.Bundle.ContMDiffTwoForm.Compatible.cayleyContraction`,
  `SymplecticGeometry.Bundle.ContMDiffTwoForm.Compatible.compatibleCayleyContraction`: the
  contractions of the `ω`-tame, and of the `ω`-compatible, structures onto `J₀` along the Cayley
  paths run backwards, as homotopies relative to `{J₀}`.
* `SymplecticGeometry.Bundle.ContMDiffTwoForm.IsNondegenerate.contractibleSpace_tames`,
  `SymplecticGeometry.Bundle.ContMDiffTwoForm.IsNondegenerate.contractibleSpace_compatible`: the
  complex structures tamed by, or compatible with, a nondegenerate form form contractible spaces.
* `SymplecticGeometry.Bundle.ContMDiffComplexStructure.contractibleSpace_tames`,
  `SymplecticGeometry.Bundle.ContMDiffComplexStructure.contractibleSpace_compatible`: the
  two-forms that tame, or are compatible with, a complex structure form contractible spaces.
* `SymplecticGeometry.Bundle.ContMDiffTwoForm.continuous_polarComplexStructure`,
  `SymplecticGeometry.Bundle.ContMDiffComplexStructure.continuous_compatibleForm`: for a bundle
  metric `g`, the maps `ω ↦ J_{g,ω}` and `J ↦ ω_{g,J}` are continuous for the frame topologies.
  The first is a `ContMDiffSection.fiberwiseMap` without parameter, of the polar formula at the
  flat map `Bundle.flatAt`; the second is Tau Ceti's `ContMDiffSection.map` of the alternating
  map `Bundle.alternatingMapOfBilin` of `compatibleBilinAt`, continuous by
  `ContMDiffSection.continuous_map_frameTopology`.
* `Bundle.ContMDiffComplexStructure.homotopic_polarComplexStructure_compatibleForm`:
  for metrics `g₀` and `g₁`, the map `J ↦ J_{g₁,ω_{g₀,J}}` is homotopic to the identity, along
  the Cayley paths from `J_{g₁,ω_{g₀,J}}` to `J`.
* `SymplecticGeometry.Bundle.ContMDiffTwoForm.exists_homotopyEquiv_polarComplexStructure`: for a
  metric `g`, the map `ω ↦ J_{g,ω}` is a homotopy equivalence.
* `SymplecticGeometry.Bundle.ContMDiffTwoForm.polarComplexStructure_homotopic`: for two metrics,
  the two maps `ω ↦ J_{g,ω}` are homotopic.
* `SymplecticGeometry.Bundle.contractibleSpace_compatible_tames`: the conjunction of the
  contractibility statements and of the homotopy equivalence.

The construction of `Compatible.cayleyPath` adapts Tau Ceti's
`TauCeti.SmoothTwoForm.Compatible.cayleyPath`, for the tangent bundle and smooth structures, to
any vector bundle and any regularity; the two contractions follow Tau Ceti's linear
`TauCeti.SymplecticForm.Compatible.cayleyContraction` and
`TauCeti.SymplecticForm.Compatible.compatibleCayleyContraction`, whose names they take.
The homotopy equivalence follows this library's linear `SymplecticGeometry.polarHomotopyEquiv`,
whose two homotopies `polarStraightHomotopy` and `polarCayleyHomotopy` it carries over fibrewise.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Proposition 2.5.6, Proposition 2.5.13 and Proposition 2.6.4
-/

public section

noncomputable section

open _root_.Bundle Set Topology TopologicalSpace TauCeti
open scoped Manifold ContinuousMap

namespace SymplecticGeometry.Bundle

variable {EB HB M : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [TopologicalSpace HB] {I : ModelWithCorners ℝ EB HB}
  [TopologicalSpace M] [ChartedSpace HB M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V] {n : ℕ∞}

/-- Let `A` be a reference endomorphism, a function of the point `q` of the endomorphism bundle,
that is `Cⁿ` on an open set `W`. Then the Cayley path
`cayleyPathFormula (smoothTransition t) (A q) q.snd` from `A q` to the fibre value of `q` is
jointly `Cⁿ` in `t` and `q`, on the points of `W` in the domain of the Cayley path from `A`. -/
theorem contMDiffOn_cayleyPathFormula_of_contMDiffOn
    {W : Set (TotalSpace (F →L[ℝ] F) (fun x ↦ V x →L[ℝ] V x))} (hW : IsOpen W)
    {A : ∀ q : TotalSpace (F →L[ℝ] F) (fun x ↦ V x →L[ℝ] V x), V q.proj →L[ℝ] V q.proj}
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, F →L[ℝ] F)) (I.prod 𝓘(ℝ, F →L[ℝ] F)) n
      (fun q ↦ TotalSpace.mk' (F →L[ℝ] F) (E := fun x ↦ V x →L[ℝ] V x) q.proj (A q)) W) :
    ContMDiffOn (𝓘(ℝ).prod (I.prod 𝓘(ℝ, F →L[ℝ] F))) (I.prod 𝓘(ℝ, F →L[ℝ] F)) n
      (fun q : ℝ × TotalSpace (F →L[ℝ] F) (fun x ↦ V x →L[ℝ] V x) ↦
        TotalSpace.mk' (F →L[ℝ] F) (E := fun x ↦ V x →L[ℝ] V x) q.2.proj
          (cayleyPathFormula (Real.smoothTransition q.1) (A q.2) q.2.snd))
      (univ ×ˢ (W ∩ cayleyPathDomain F V A)) := by
  rintro ⟨t, q⟩ ⟨-, hq₁, hq₂⟩
  have hb : t.smoothTransition ∈ Icc (0 : ℝ) 1 :=
    ⟨Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t⟩
  have hu := isUnit_of_mem_cayleyPathDomain hq₂ hb
  have hproj : ContMDiff (𝓘(ℝ).prod (I.prod 𝓘(ℝ, F →L[ℝ] F))) I n
      (fun p : ℝ × TotalSpace (F →L[ℝ] F) (fun x ↦ V x →L[ℝ] V x) ↦ p.2.proj) :=
    (contMDiff_proj _).comp contMDiff_snd
  exact (ContMDiffAt.cayleyPathFormula_hom_bundle_of_vectorBundle
    (f := fun p : ℝ × TotalSpace (F →L[ℝ] F) (fun x ↦ V x →L[ℝ] V x) ↦ p.2.proj)
    (b := fun p ↦ Real.smoothTransition p.1) (A := fun p ↦ A p.2) (B := fun p ↦ p.2.snd)
    hproj.contMDiffAt
    (Real.smoothTransition.contDiff.contMDiff.comp contMDiff_fst).contMDiffAt
    (((hA q hq₁).contMDiffAt (hW.mem_nhds hq₁)).comp (t, q) contMDiff_snd.contMDiffAt)
    contMDiff_snd.contMDiffAt hu.1 hu.2).contMDiffWithinAt

section Continuity

variable [IsManifold I n M] [ContMDiffVectorBundle n F V I] [LocallyCompactSpace EB] {ι : Type*}
  (e : ι → Trivialization (F →L[ℝ] F) (π (F →L[ℝ] F) (fun x ↦ V x →L[ℝ] V x)))
  [∀ i, MemTrivializationAtlas (e i)]
  (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)

/-- Let `A` be a reference endomorphism, a function of the point of the endomorphism bundle, that
is `Cⁿ` on an open set `W`. For a covering frame system, the fibrewise Cayley path from `A` is
jointly continuous in the time and in the section of the endomorphism bundle, among the sections
whose values lie in `W` and in the domain of the Cayley path from `A`, for the frame topology. -/
theorem continuous_fiberwiseMap_cayleyPathFormula (hcover : ∀ x, ∃ i, x ∈ U i)
    {W : Set (TotalSpace (F →L[ℝ] F) (fun x ↦ V x →L[ℝ] V x))} (hW : IsOpen W)
    {A : ∀ q : TotalSpace (F →L[ℝ] F) (fun x ↦ V x →L[ℝ] V x), V q.proj →L[ℝ] V q.proj}
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, F →L[ℝ] F)) (I.prod 𝓘(ℝ, F →L[ℝ] F)) n
      (fun q ↦ TotalSpace.mk' (F →L[ℝ] F) (E := fun x ↦ V x →L[ℝ] V x) q.proj (A q)) W) :
    letI := ContMDiffSection.frameTopology (I := I) (n := n) e U hU
    Continuous fun p : ℝ × {s : Cₛ^n⟮I; F →L[ℝ] F, fun x ↦ V x →L[ℝ] V x⟯ //
        ∀ x, ⟨x, s x⟩ ∈ W ∩ cayleyPathDomain F V A} ↦
      ContMDiffSection.fiberwiseMap
        (fun t x B ↦ cayleyPathFormula (Real.smoothTransition t) (A ⟨x, B⟩) B)
        (contMDiffOn_cayleyPathFormula_of_contMDiffOn hW hA) p.1 p.2 := by
  let _ := ContMDiffSection.frameTopology (I := I) (n := n) e U hU
  exact ContMDiffSection.continuous_fiberwiseMap _ _ e U hU e U hU
    (isOpen_cayleyPathDomain hW (hA.continuousOn)) hcover

end Continuity


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
  simpa using contMDiffOn_cayleyPathFormula_of_contMDiffOn isOpen_univ
    (A := fun q ↦ J₀ q.proj) (J₀.toEndomorphism.contMDiff.comp (contMDiff_proj _)).contMDiffOn

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
      (VectorBundle.continuousLinearEquivAt ℝ F V x)
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
    (VectorBundle.continuousLinearEquivAt ℝ F V x)
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
  have hJ₀ : J₀ x * J₀ x = -1 :=
    ContinuousLinearMap.mul_self_eq_neg_one_iff_comp_eq_neg_id.2 (J₀.square_neg x)
  rw [h₀.cayleyPath_apply, Real.smoothTransition.one_of_one_le ht, cayleyPathFormula_one hJ₀
    (isUnit_of_mem_cayleyPathDomain (h₀.mem_cayleyPathDomain h x) ⟨zero_le_one, le_rfl⟩).1]

/-- The Cayley path from `J₀` to itself is constant at `J₀`. -/
@[simp]
theorem Compatible.cayleyPath_self (t : ℝ) : h₀.cayleyPath h₀.tames t = J₀ := by
  ext x v
  have hJ₀ : J₀ x * J₀ x = -1 :=
    ContinuousLinearMap.mul_self_eq_neg_one_iff_comp_eq_neg_id.2 (J₀.square_neg x)
  rw [h₀.cayleyPath_apply, cayleyPathFormula_self hJ₀]

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
  have hs : Continuous fun J : {J : ContMDiffComplexStructure I n F V // ω.Tames J} ↦
      (⟨J.val.toEndomorphism, fun x ↦ ⟨mem_univ _, h₀.mem_cayleyPathDomain J.property x⟩⟩ :
        {s : Cₛ^n⟮I; F →L[ℝ] F, fun x ↦ V x →L[ℝ] V x⟯ //
          ∀ x, ⟨x, s x⟩ ∈ univ ∩ cayleyPathDomain F V fun q ↦ J₀ q.proj}) :=
    ((ContMDiffComplexStructure.isEmbedding_toEndomorphism_frameTopology e U hU).continuous.comp
      continuous_subtypeVal).subtype_mk _
  refine (ContMDiffComplexStructure.continuous_frameTopology_iff e U hU).2 <|
    ((continuous_fiberwiseMap_cayleyPathFormula e U hU hcover isOpen_univ
      (A := fun q ↦ J₀ q.proj) (J₀.toEndomorphism.contMDiff.comp (contMDiff_proj _)).contMDiffOn
      ).comp (continuous_fst.prodMk (hs.comp continuous_snd))).congr fun p ↦
    ContMDiffSection.ext fun x ↦ ?_
  simp only [Function.comp_apply, ContMDiffSection.fiberwiseMap_apply]
  exact (h₀.cayleyPath_apply p.2.property p.1 x).symm

/-- For a covering frame system, the Cayley paths run backwards contract the `ω`-tame complex
structures onto an `ω`-compatible structure `J₀`, relative to `J₀`, for the frame topology: at
time `t` the homotopy sends `J` to the Cayley path from `J₀` to `J` at time `1 - t`, so it starts
at the identity, ends at the constant map at `J₀`, and fixes `J₀` at every time. -/
def Compatible.cayleyContraction (hcover : ∀ x, ∃ i, x ∈ U i) :
    letI := ContMDiffComplexStructure.frameTopology (I := I) (n := n) e U hU
    (ContinuousMap.id {J : ContMDiffComplexStructure I n F V // ω.Tames J}).HomotopyRel
      (ContinuousMap.const _ ⟨J₀, h₀.tames⟩) {⟨J₀, h₀.tames⟩} :=
  letI := ContMDiffComplexStructure.frameTopology (I := I) (n := n) e U hU
  { toFun := fun p ↦ ⟨h₀.cayleyPath p.2.property (1 - p.1), h₀.tames_cayleyPath p.2.property _⟩
    continuous_toFun := ((h₀.continuous_cayleyPath e U hU hcover).comp
      ((continuous_const.sub (continuous_subtypeVal.comp continuous_fst)).prodMk
        continuous_snd)).subtype_mk _
    map_zero_left := fun J ↦ Subtype.ext (h₀.cayleyPath_of_one_le J.property (by simp))
    map_one_left := fun J ↦ Subtype.ext (h₀.cayleyPath_of_nonpos J.property (by simp))
    prop' := fun t J hJ ↦ by
      obtain rfl := hJ
      exact Subtype.ext (h₀.cayleyPath_self _) }

/-- At time `t`, the Cayley contraction onto `J₀` sends an `ω`-tame structure `J` to the Cayley
path from `J₀` to `J` at time `1 - t`. -/
@[simp]
theorem Compatible.cayleyContraction_apply (hcover : ∀ x, ∃ i, x ∈ U i) (t : unitInterval)
    (J : {J : ContMDiffComplexStructure I n F V // ω.Tames J}) :
    (h₀.cayleyContraction e U hU hcover (t, J) : ContMDiffComplexStructure I n F V) =
      h₀.cayleyPath J.property (1 - t) :=
  (rfl)

/-- For a covering frame system, the Cayley paths run backwards contract the `ω`-compatible
complex structures onto one of them, `J₀`, relative to `J₀`, for the frame topology: the
restriction of `Compatible.cayleyContraction`, since the Cayley path between two `ω`-compatible
structures stays among them. -/
def Compatible.compatibleCayleyContraction (hcover : ∀ x, ∃ i, x ∈ U i) :
    letI := ContMDiffComplexStructure.frameTopology (I := I) (n := n) e U hU
    (ContinuousMap.id {J : ContMDiffComplexStructure I n F V // ω.Compatible J}).HomotopyRel
      (ContinuousMap.const _ ⟨J₀, h₀⟩) {⟨J₀, h₀⟩} :=
  letI := ContMDiffComplexStructure.frameTopology (I := I) (n := n) e U hU
  { toFun := fun p ↦ ⟨h₀.cayleyContraction e U hU hcover (p.1, ⟨p.2, p.2.property.tames⟩),
      h₀.compatible_cayleyPath p.2.property _⟩
    continuous_toFun := ((h₀.cayleyContraction e U hU hcover).continuous.comp
      (continuous_fst.prodMk ((continuous_subtypeVal.comp continuous_snd).subtype_mk _))
      ).subtype_mk _
    map_zero_left := fun J ↦ Subtype.ext (by simp)
    map_one_left := fun J ↦ Subtype.ext (by simp)
    prop' := fun t J hJ ↦ by
      obtain rfl := hJ
      exact Subtype.ext (by simp) }

/-- The compatible Cayley contraction onto `J₀` is the Cayley contraction of the `ω`-tame
structures, restricted to the `ω`-compatible ones. -/
@[simp]
theorem Compatible.coe_compatibleCayleyContraction (hcover : ∀ x, ∃ i, x ∈ U i)
    (t : unitInterval) (J : {J : ContMDiffComplexStructure I n F V // ω.Compatible J}) :
    (h₀.compatibleCayleyContraction e U hU hcover (t, J) : ContMDiffComplexStructure I n F V) =
      h₀.cayleyContraction e U hU hcover (t, ⟨J, J.property.tames⟩) :=
  (rfl)

/-- At time `t`, the compatible Cayley contraction onto `J₀` sends an `ω`-compatible structure
`J` to the Cayley path from `J₀` to `J` at time `1 - t`. -/
@[simp]
theorem Compatible.compatibleCayleyContraction_apply (hcover : ∀ x, ∃ i, x ∈ U i)
    (t : unitInterval) (J : {J : ContMDiffComplexStructure I n F V // ω.Compatible J}) :
    (h₀.compatibleCayleyContraction e U hU hcover (t, J) : ContMDiffComplexStructure I n F V) =
      h₀.cayleyPath J.property.tames (1 - t) :=
  (rfl)

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
  exact (contractible_iff_id_nullhomotopic _).2
    ⟨⟨J₀, h₀.tames⟩, ⟨(h₀.cayleyContraction e U hU hcover).toHomotopy⟩⟩

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
  exact (contractible_iff_id_nullhomotopic _).2
    ⟨⟨J₀, h₀⟩, ⟨(h₀.compatibleCayleyContraction e U hU hcover).toHomotopy⟩⟩

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
  exact (ContMDiffTwoForm.convex_setOfPred_tames J).contractibleSpace ⟨ω, hω.tames⟩

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
  exact (ContMDiffTwoForm.convex_setOfPred_compatible J).contractibleSpace ⟨ω, hω⟩

end ContMDiffComplexStructure

/-! ### The Cayley path from `J_{g₁,ω_{g₀,J}}` to `J` -/

namespace ContMDiffComplexStructure

variable (g₀ g₁ : ContMDiffRiemannianMetric I n F V)

/-- For every complex structure `J`, the point `⟨x, J x⟩` of the endomorphism bundle lies in
`polarEndDomain g₀` and in the domain of the Cayley path from `J_{g₁,ω_{g₀,J}}`, read as the
polar formula of `g₁` at `compatibleBilinAt g₀`: both `J_{g₁,ω_{g₀,J}}` and `J` are compatible
with `ω_{g₀,J}`. -/
theorem mk_mem_polarEndDomain_inter_cayleyPathDomain (J : ContMDiffComplexStructure I n F V)
    (x : M) :
    (⟨x, J x⟩ : TotalSpace (F →L[ℝ] F) (fun x ↦ V x →L[ℝ] V x)) ∈
      g₀.polarEndDomain ∩ cayleyPathDomain F V fun q ↦
        g₁.polarFormulaAt q.proj (g₀.compatibleBilinAt q.proj q.snd) := by
  have hc := compatible_compatibleForm g₀ J
  refine ⟨J.mk_mem_polarEndDomain g₀ x,
    ((hc.isNondegenerate.compatible_polarComplexStructure g₁).compatibleAt x).mem_cayleyPathDomain
      (hc.compatibleAt x).tames ?_ (J.almostComplexStructureAt_toLinearMap x).symm⟩
  rw [almostComplexStructureAt_toLinearMap, ← polarFormulaAt_compatibleBilinAt]

end ContMDiffComplexStructure

/-! ### Continuity of `ω ↦ J_{g,ω}` and `J ↦ ω_{g,J}` -/

section Continuity

variable [IsManifold I n M] [ContMDiffVectorBundle n F V I] [LocallyCompactSpace EB]
  {ι κ : Type*}
  (e : ι → Trivialization (F →L[ℝ] F) (π (F →L[ℝ] F) (fun x ↦ V x →L[ℝ] V x)))
  [∀ i, MemTrivializationAtlas (e i)]
  (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)
  (e' : κ → Trivialization (F [⋀^Fin 2]→L[ℝ] ℝ)
    (π (F [⋀^Fin 2]→L[ℝ] ℝ) (fun x ↦ V x [⋀^Fin 2]→L[ℝ] Trivial M ℝ x)))
  [∀ j, MemTrivializationAtlas (e' j)]
  (U' : κ → Opens M) (hU' : ∀ j, (U' j : Set M) ⊆ (e' j).baseSet)

/-- For a bundle metric `g`, the complex structure `J_{g,ω}` depends continuously on the
nondegenerate two-form `ω`, for the frame topologies of a covering frame system of the bundle of
alternating forms and of any frame system of the endomorphism bundle. -/
theorem ContMDiffTwoForm.continuous_polarComplexStructure
    (g : ContMDiffRiemannianMetric I n F V) (hcover' : ∀ x, ∃ j, x ∈ U' j) :
    letI := ContMDiffSection.frameTopology (I := I) (n := n) e' U' hU'
    letI := ContMDiffComplexStructure.frameTopology (I := I) (n := n) e U hU
    Continuous fun ω : {ω : ContMDiffTwoForm I n F V // ω.IsNondegenerate} ↦
      ω.property.polarComplexStructure g := by
  let _ := ContMDiffSection.frameTopology (I := I) (n := n) e' U' hU'
  let _ := ContMDiffSection.frameTopology (I := I) (n := n) e U hU
  let _ := ContMDiffComplexStructure.frameTopology (I := I) (n := n) e U hU
  -- The fibrewise nondegenerate alternating maps.
  let O := {q : TotalSpace (F [⋀^Fin 2]→L[ℝ] ℝ) (fun x ↦ V x [⋀^Fin 2]→L[ℝ] Trivial M ℝ x) |
    LinearMap.BilinForm.Nondegenerate (MultilinearMap.toBilinMap q.snd.toMultilinearMap)}
  have hO : IsOpen O := isOpen_setOfPred_nondegenerate
  -- The flat map on the bundle of alternating maps, and the polar formula at it, on `O`.
  have hflat : ContMDiff (I.prod 𝓘(ℝ, F [⋀^Fin 2]→L[ℝ] ℝ)) (I.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      fun q : TotalSpace (F [⋀^Fin 2]→L[ℝ] ℝ) (fun x ↦ V x [⋀^Fin 2]→L[ℝ] Trivial M ℝ x) ↦
        TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) (E := fun x ↦ V x →L[ℝ] V x →L[ℝ] ℝ) q.proj
          (_root_.Bundle.flatAt F q.snd) :=
    fun q ↦ contMDiffAt_sectionAlong_flatAt (IN := I.prod 𝓘(ℝ, F [⋀^Fin 2]→L[ℝ] ℝ))
      (b := TotalSpace.proj) (α := fun q ↦ q.snd) (y₀ := q) (n := n) contMDiffAt_id
  have hΦ : ContMDiffOn (𝓘(ℝ, Unit).prod (I.prod 𝓘(ℝ, F [⋀^Fin 2]→L[ℝ] ℝ)))
      (I.prod 𝓘(ℝ, F →L[ℝ] F)) n
      (fun q : Unit × TotalSpace (F [⋀^Fin 2]→L[ℝ] ℝ)
          (fun x ↦ V x [⋀^Fin 2]→L[ℝ] Trivial M ℝ x) ↦
        TotalSpace.mk' (F →L[ℝ] F) (E := fun x ↦ V x →L[ℝ] V x) q.2.proj
          (g.polarFormulaAt q.2.proj (_root_.Bundle.flatAt F q.2.snd)))
      (univ ×ˢ O) :=
    (g.contMDiffOn_polarFormulaAt.comp (hflat.contMDiffOn (s := O))
      fun _ hq ↦ _root_.Bundle.mk_flatAt_mem_polarFormulaDomain hq).comp
      contMDiff_snd.contMDiffOn fun _ hq ↦ hq.2
  have hs : Continuous fun ω : {ω : ContMDiffTwoForm I n F V // ω.IsNondegenerate} ↦
      (⟨ω.val, fun x ↦ by
        simpa only [O, Set.mem_ofPred_eq, ← bilinFormAt_def] using
          ω.property.nondegenerate_bilinFormAt x⟩ :
        {s : ContMDiffTwoForm I n F V // ∀ x, ⟨x, s x⟩ ∈ O}) :=
    continuous_subtypeVal.subtype_mk _
  refine (ContMDiffComplexStructure.continuous_frameTopology_iff e U hU).2 ?_
  convert (ContMDiffSection.continuous_fiberwiseMap
    (fun (_ : Unit) x α ↦ g.polarFormulaAt x (_root_.Bundle.flatAt F α)) hΦ e' U' hU' e U hU hO
    hcover').comp ((continuous_const (y := ())).prodMk hs) using 1
  funext ω
  refine ContMDiffSection.ext fun x ↦ ?_
  simp only [Function.comp_apply, ContMDiffSection.fiberwiseMap_apply]
  rw [← flat_def]
  exact ω.property.polarComplexStructure_eq_polarFormulaAt x

/-- For a bundle metric `g`, the two-form `ω_{g,J}` depends continuously on the complex
structure `J`, for the frame topologies of a covering frame system of the endomorphism bundle and
of any frame system of the bundle of alternating forms. -/
theorem ContMDiffComplexStructure.continuous_compatibleForm
    (g : ContMDiffRiemannianMetric I n F V) (hcover : ∀ x, ∃ i, x ∈ U i) :
    letI := ContMDiffComplexStructure.frameTopology (I := I) (n := n) e U hU
    letI := ContMDiffSection.frameTopology (I := I) (n := n) e' U' hU'
    Continuous
      (compatibleForm g : ContMDiffComplexStructure I n F V → ContMDiffTwoForm I n F V) := by
  let _ := ContMDiffSection.frameTopology (I := I) (n := n) e U hU
  let _ := ContMDiffComplexStructure.frameTopology (I := I) (n := n) e U hU
  let _ := ContMDiffSection.frameTopology (I := I) (n := n) e' U' hU'
  have hα (x : M) (B : V x →L[ℝ] V x) (v : V x) : g.compatibleBilinAt x B v v = 0 := by
    simpa using g.isAlt_compatibleBilinAt x B v
  -- The alternating map of `compatibleBilinAt`, on the whole endomorphism bundle.
  have hΦ : ContMDiff (I.prod 𝓘(ℝ, F →L[ℝ] F)) (I.prod 𝓘(ℝ, F [⋀^Fin 2]→L[ℝ] ℝ)) n
      (fun q : TotalSpace (F →L[ℝ] F) (fun x ↦ V x →L[ℝ] V x) ↦
        TotalSpace.mk' (F [⋀^Fin 2]→L[ℝ] ℝ) (E := fun x ↦ V x [⋀^Fin 2]→L[ℝ] Trivial M ℝ x)
          q.proj (_root_.Bundle.alternatingMapOfBilin F (g.compatibleBilinAt q.proj q.snd)
            (hα q.proj q.snd))) := fun q ↦
    contMDiffAt_sectionAlong_continuousAlternatingMap_of_bilinear (F₁ := F) (V₁ := V)
      (G := ℝ) (W := Trivial M ℝ) (IN := I.prod 𝓘(ℝ, F →L[ℝ] F)) (n := n) (y₀ := q)
      (b := fun q : TotalSpace (F →L[ℝ] F) (fun x ↦ V x →L[ℝ] V x) ↦ q.proj)
      (β := fun q ↦ g.compatibleBilinAt q.proj q.snd)
      g.contMDiff_compatibleBilinAt.contMDiffAt
      fun _ v ↦ _root_.Bundle.alternatingMapOfBilin_apply _ _ v
  convert (ContMDiffSection.continuous_map_frameTopology
    (fun x B ↦ _root_.Bundle.alternatingMapOfBilin F (g.compatibleBilinAt x B) (hα x B))
    hΦ e U hU e' U' hU' hcover).comp
      (isEmbedding_toEndomorphism_frameTopology e U hU).continuous using 1
  funext J
  refine ContMDiffSection.ext fun x ↦ ?_
  simp only [Function.comp_apply, ContMDiffSection.map_apply]
  exact compatibleForm_eq_alternatingMapOfBilin g J x

namespace ContMDiffComplexStructure

variable (g₀ g₁ : ContMDiffRiemannianMetric I n F V)

/-- For bundle metrics `g₀` and `g₁` and a covering frame system, the Cayley path from
`J_{g₁,ω_{g₀,J}}` to `J`, through the complex structures compatible with `ω_{g₀,J}`, is jointly
continuous in the time and in `J`, for the frame topology. -/
theorem continuous_cayleyPath_polarComplexStructure (hcover : ∀ x, ∃ i, x ∈ U i) :
    letI := frameTopology (I := I) (n := n) e U hU
    Continuous fun p : ℝ × ContMDiffComplexStructure I n F V ↦
      ((compatible_compatibleForm g₀ p.2).isNondegenerate.compatible_polarComplexStructure
        g₁).cayleyPath (compatible_compatibleForm g₀ p.2).tames p.1 := by
  let _ := ContMDiffSection.frameTopology (I := I) (n := n) e U hU
  let _ := frameTopology (I := I) (n := n) e U hU
  have hs : Continuous fun J : ContMDiffComplexStructure I n F V ↦
      (⟨J.toEndomorphism, mk_mem_polarEndDomain_inter_cayleyPathDomain g₀ g₁ J⟩ :
        {s : Cₛ^n⟮I; F →L[ℝ] F, fun x ↦ V x →L[ℝ] V x⟯ //
          ∀ x, ⟨x, s x⟩ ∈ g₀.polarEndDomain ∩ cayleyPathDomain F V fun q ↦
            g₁.polarFormulaAt q.proj (g₀.compatibleBilinAt q.proj q.snd)}) :=
    (isEmbedding_toEndomorphism_frameTopology e U hU).continuous.subtype_mk _
  refine (continuous_frameTopology_iff e U hU).2 <|
    ((continuous_fiberwiseMap_cayleyPathFormula e U hU hcover g₀.isOpen_polarEndDomain
      (g₀.contMDiffOn_polarFormulaAt_compatibleBilinAt g₁)).comp
        (continuous_fst.prodMk (hs.comp continuous_snd))).congr fun p ↦
    ContMDiffSection.ext fun x ↦ ?_
  simp only [Function.comp_apply, ContMDiffSection.fiberwiseMap_apply]
  rw [polarFormulaAt_compatibleBilinAt]
  exact (ContMDiffTwoForm.Compatible.cayleyPath_apply _ _ p.1 x).symm

/-- For bundle metrics `g₀` and `g₁` and a covering frame system, the complex structure
`J_{g₁,ω_{g₀,J}}` depends continuously on the complex structure `J`, for the frame topology. -/
theorem continuous_polarComplexStructure_compatibleForm (hcover : ∀ x, ∃ i, x ∈ U i) :
    letI := frameTopology (I := I) (n := n) e U hU
    Continuous fun J : ContMDiffComplexStructure I n F V ↦
      (compatible_compatibleForm g₀ J).isNondegenerate.polarComplexStructure g₁ := by
  let _ := frameTopology (I := I) (n := n) e U hU
  exact ((continuous_cayleyPath_polarComplexStructure e U hU g₀ g₁ hcover).comp
    (continuous_const.prodMk continuous_id)).congr
    fun J ↦ ((compatible_compatibleForm g₀ J).isNondegenerate.compatible_polarComplexStructure
      g₁).cayleyPath_of_nonpos (compatible_compatibleForm g₀ J).tames le_rfl

/-- For bundle metrics `g₀` and `g₁` and a covering frame system, the map
`J ↦ J_{g₁,ω_{g₀,J}}` of the complex structures to themselves is homotopic to the identity, for
the frame topology, along the Cayley paths from `J_{g₁,ω_{g₀,J}}` to `J`. -/
theorem homotopic_polarComplexStructure_compatibleForm (hcover : ∀ x, ∃ i, x ∈ U i) :
    letI := frameTopology (I := I) (n := n) e U hU
    ContinuousMap.Homotopic
      ⟨fun J : ContMDiffComplexStructure I n F V ↦
        (compatible_compatibleForm g₀ J).isNondegenerate.polarComplexStructure g₁,
        continuous_polarComplexStructure_compatibleForm e U hU g₀ g₁ hcover⟩
      (ContinuousMap.id _) := by
  let _ := frameTopology (I := I) (n := n) e U hU
  exact ⟨{
    toFun := fun p ↦
      ((compatible_compatibleForm g₀ p.2).isNondegenerate.compatible_polarComplexStructure
        g₁).cayleyPath (compatible_compatibleForm g₀ p.2).tames p.1
    continuous_toFun := (continuous_cayleyPath_polarComplexStructure e U hU g₀ g₁ hcover).comp
      ((continuous_subtypeVal.comp continuous_fst).prodMk continuous_snd)
    map_zero_left := fun _ ↦ ContMDiffTwoForm.Compatible.cayleyPath_of_nonpos _ _ (by simp)
    map_one_left := fun _ ↦ ContMDiffTwoForm.Compatible.cayleyPath_of_one_le _ _ (by simp) }⟩

end ContMDiffComplexStructure

/-! ### The homotopy equivalence -/

namespace ContMDiffTwoForm

/-- For a bundle metric `g` and covering frame systems of the endomorphism bundle and of the
bundle of alternating forms, the map `ω ↦ ω_{g,J_{g,ω}}` of the nondegenerate two-forms to
themselves is homotopic to the identity, for the frame topology of the second, along the segments
between `ω` and `ω_{g,J_{g,ω}}`. -/
theorem homotopic_compatibleForm_polarComplexStructure (g : ContMDiffRiemannianMetric I n F V)
    (hcover : ∀ x, ∃ i, x ∈ U i) (hcover' : ∀ x, ∃ j, x ∈ U' j) :
    letI := ContMDiffSection.frameTopology (I := I) (n := n) e' U' hU'
    letI := ContMDiffComplexStructure.frameTopology (I := I) (n := n) e U hU
    ContinuousMap.Homotopic
      ⟨fun ω : {ω : ContMDiffTwoForm I n F V // ω.IsNondegenerate} ↦
        (⟨ContMDiffComplexStructure.compatibleForm g (ω.property.polarComplexStructure g),
          (ContMDiffComplexStructure.compatible_compatibleForm g _).isNondegenerate⟩ :
          {ω : ContMDiffTwoForm I n F V // ω.IsNondegenerate}),
        ((ContMDiffComplexStructure.continuous_compatibleForm e U hU e' U' hU' g hcover).comp
          (continuous_polarComplexStructure e U hU e' U' hU' g hcover')).subtype_mk _⟩
      (ContinuousMap.id _) := by
  let _ := ContMDiffSection.frameTopology (I := I) (n := n) e' U' hU'
  let _ := ContMDiffSection.isTopologicalAddGroup_frameTopology (I := I) (n := n) e' U' hU'
  let _ := ContMDiffSection.continuousSMul_frameTopology (I := I) (n := n) e' U' hU'
  let _ := ContMDiffComplexStructure.frameTopology (I := I) (n := n) e U hU
  refine ContinuousMap.Homotopic.symm ⟨ContinuousMap.Homotopy.affineOfSegmentSubset
    (s := {ω : ContMDiffTwoForm I n F V | ω.IsNondegenerate}) _ _ fun ω ↦ ?_⟩
  rw [segment_eq_image_lineMap]
  rintro _ ⟨t, ht, rfl⟩
  exact (ω.property.tames_lineMap_compatibleForm g ht).isNondegenerate

/-- For a bundle metric `g`, the map `ω ↦ J_{g,ω}` from the nondegenerate two-forms to the complex
structures is a homotopy equivalence, for the frame topologies of covering frame systems of the
bundle of alternating forms and of the endomorphism bundle, with homotopy inverse
`J ↦ ω_{g,J}`. -/
theorem exists_homotopyEquiv_polarComplexStructure (g : ContMDiffRiemannianMetric I n F V)
    (hcover : ∀ x, ∃ i, x ∈ U i) (hcover' : ∀ x, ∃ j, x ∈ U' j) :
    letI := ContMDiffSection.frameTopology (I := I) (n := n) e' U' hU'
    letI := ContMDiffComplexStructure.frameTopology (I := I) (n := n) e U hU
    ∃ E : {ω : ContMDiffTwoForm I n F V // ω.IsNondegenerate} ≃ₕ
        ContMDiffComplexStructure I n F V,
      (∀ ω, E.toFun ω = ω.property.polarComplexStructure g) ∧
        ∀ J, (E.invFun J).val = ContMDiffComplexStructure.compatibleForm g J := by
  let _ := ContMDiffSection.frameTopology (I := I) (n := n) e' U' hU'
  let _ := ContMDiffComplexStructure.frameTopology (I := I) (n := n) e U hU
  exact ⟨{
    toFun := ⟨_, continuous_polarComplexStructure e U hU e' U' hU' g hcover'⟩
    invFun := ⟨fun J ↦ ⟨ContMDiffComplexStructure.compatibleForm g J,
        (ContMDiffComplexStructure.compatible_compatibleForm g J).isNondegenerate⟩,
      (ContMDiffComplexStructure.continuous_compatibleForm e U hU e' U' hU' g
        hcover).subtype_mk _⟩
    left_inv := homotopic_compatibleForm_polarComplexStructure e U hU e' U' hU' g hcover hcover'
    right_inv := ContMDiffComplexStructure.homotopic_polarComplexStructure_compatibleForm e U hU g g
      hcover }, fun _ ↦ rfl, fun _ ↦ rfl⟩

/-- For bundle metrics `g₀` and `g₁`, the maps `ω ↦ J_{g₀,ω}` and `ω ↦ J_{g₁,ω}` from the
nondegenerate two-forms to the complex structures are homotopic, for the frame topologies of
covering frame systems of the bundle of alternating forms and of the endomorphism bundle. -/
theorem polarComplexStructure_homotopic (g₀ g₁ : ContMDiffRiemannianMetric I n F V)
    (hcover : ∀ x, ∃ i, x ∈ U i) (hcover' : ∀ x, ∃ j, x ∈ U' j) :
    letI := ContMDiffSection.frameTopology (I := I) (n := n) e' U' hU'
    letI := ContMDiffComplexStructure.frameTopology (I := I) (n := n) e U hU
    ContinuousMap.Homotopic
      ⟨fun ω : {ω : ContMDiffTwoForm I n F V // ω.IsNondegenerate} ↦
        ω.property.polarComplexStructure g₀,
        continuous_polarComplexStructure e U hU e' U' hU' g₀ hcover'⟩
      ⟨fun ω : {ω : ContMDiffTwoForm I n F V // ω.IsNondegenerate} ↦
        ω.property.polarComplexStructure g₁,
        continuous_polarComplexStructure e U hU e' U' hU' g₁ hcover'⟩ := by
  let _ := ContMDiffSection.frameTopology (I := I) (n := n) e' U' hU'
  let _ := ContMDiffComplexStructure.frameTopology (I := I) (n := n) e U hU
  -- `J_{g₀,ω}` is homotopic to `J_{g₁,ω_{g₀,J_{g₀,ω}}}`, which is homotopic to `J_{g₁,ω}`.
  have h₀ := (ContMDiffComplexStructure.homotopic_polarComplexStructure_compatibleForm e U hU g₀ g₁
    hcover).comp (ContinuousMap.Homotopic.refl
      ⟨_, continuous_polarComplexStructure e U hU e' U' hU' g₀ hcover'⟩)
  have h₁ := (ContinuousMap.Homotopic.refl
      ⟨_, continuous_polarComplexStructure e U hU e' U' hU' g₁ hcover'⟩).comp
    (homotopic_compatibleForm_polarComplexStructure e U hU e' U' hU' g₀ hcover hcover')
  exact h₀.symm.trans h₁

end ContMDiffTwoForm

end Continuity

/-! ### The milestone -/

section Milestone

variable [FiniteDimensional ℝ EB] [T2Space M] [SigmaCompactSpace M]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] [ContMDiffVectorBundle n F V I] {ι κ : Type*}
  (e : ι → Trivialization (F →L[ℝ] F) (π (F →L[ℝ] F) (fun x ↦ V x →L[ℝ] V x)))
  [∀ i, MemTrivializationAtlas (e i)]
  (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)
  (e' : κ → Trivialization (F [⋀^Fin 2]→L[ℝ] ℝ)
    (π (F [⋀^Fin 2]→L[ℝ] ℝ) (fun x ↦ V x [⋀^Fin 2]→L[ℝ] Trivial M ℝ x)))
  [∀ j, MemTrivializationAtlas (e' j)]
  (U' : κ → Opens M) (hU' : ∀ j, (U' j : Set M) ⊆ (e' j).baseSet)

/-- Let `V` be a real vector bundle of finite rank over a Hausdorff σ-compact manifold modelled on
a finite-dimensional space, with the frame topologies of covering frame systems of its
endomorphism bundle and of its bundle of alternating forms. Then, in every regularity `Cⁿ`:
* for a nondegenerate two-form `ω`, the complex structures tamed by `ω`, and those compatible
  with `ω`, form contractible spaces;
* for a complex structure `J`, the two-forms that tame `J`, and those compatible with `J`, form
  contractible spaces;
* for a bundle metric `g`, the map `ω ↦ J_{g,ω}` from the nondegenerate two-forms to the complex
  structures is a homotopy equivalence, with homotopy inverse `J ↦ ω_{g,J}`.

A contractible space is nonempty, so in particular all four spaces are nonempty.

Milestone: *Compatible and tame complex structures on symplectic vector bundles*. -/
theorem contractibleSpace_compatible_tames (hcover : ∀ x, ∃ i, x ∈ U i)
    (hcover' : ∀ x, ∃ j, x ∈ U' j) :
    letI := ContMDiffSection.frameTopology (I := I) (n := n) e' U' hU'
    letI := ContMDiffComplexStructure.frameTopology (I := I) (n := n) e U hU
    (∀ ω : ContMDiffTwoForm I n F V, ω.IsNondegenerate →
        ContractibleSpace {J : ContMDiffComplexStructure I n F V // ω.Tames J} ∧
          ContractibleSpace {J : ContMDiffComplexStructure I n F V // ω.Compatible J}) ∧
      (∀ J : ContMDiffComplexStructure I n F V,
        ContractibleSpace {ω : ContMDiffTwoForm I n F V // ω.Tames J} ∧
          ContractibleSpace {ω : ContMDiffTwoForm I n F V // ω.Compatible J}) ∧
      ∀ g : ContMDiffRiemannianMetric I n F V,
        ∃ E : {ω : ContMDiffTwoForm I n F V // ω.IsNondegenerate} ≃ₕ
            ContMDiffComplexStructure I n F V,
          (∀ ω, E.toFun ω = ω.property.polarComplexStructure g) ∧
            ∀ J, (E.invFun J).val = ContMDiffComplexStructure.compatibleForm g J :=
  ⟨fun _ hω ↦ ⟨hω.contractibleSpace_tames e U hU hcover,
      hω.contractibleSpace_compatible e U hU hcover⟩,
    fun J ↦ ⟨J.contractibleSpace_tames e' U' hU', J.contractibleSpace_compatible e' U' hU'⟩,
    fun g ↦ ContMDiffTwoForm.exists_homotopyEquiv_polarComplexStructure e U hU e' U' hU' g hcover
      hcover'⟩

end Milestone

end SymplecticGeometry.Bundle

end
