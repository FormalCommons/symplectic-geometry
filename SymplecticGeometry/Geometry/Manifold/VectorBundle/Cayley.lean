/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Geometry.Symplectic.Cayley.Smooth
public import TauCeti.Topology.VectorBundle.Coordinates
public import SymplecticGeometry.Geometry.Symplectic.Cayley.Domain
import SymplecticGeometry.Topology.FiberBundle.Basic

/-!
# The Cayley path in the endomorphism bundle of a vector bundle

Let `V` be a real vector bundle with complete model fibre `F`. For endomorphisms `A`, `B` of a
fibre, Tau Ceti's Cayley path `TauCeti.cayleyPathFormula b A B = A (1 + b C)(1 - b C)⁻¹`, with
`C = TauCeti.cayleyFormula A B`, is a rational expression in `A` and `B`. Read in a trivialization,
an endomorphism of a fibre becomes its conjugate by the fibre equivalence, an algebra isomorphism,
so the expression is read as the same expression in `F →L[ℝ] F`, where it is smooth wherever both
denominators are units. This gives
`ContMDiffAt.cayleyPathFormula_hom_bundle_of_vectorBundle`: along a `Cⁿ` base map, the Cayley path
of `Cⁿ` families of fibre endomorphisms with a `Cⁿ` coefficient is `Cⁿ` as a map into the
endomorphism bundle, at every point where both denominators are units.

For a family `A` of reference endomorphisms indexed by the points of the endomorphism bundle,
`Bundle.cayleyPathDomain F V A` is the set of points `q` such that the Cayley path from `A q` to
`q` is defined for every coefficient in `[0, 1]`, read in the preferred trivialization at the base
point of `q`. It does not depend on the trivialization
(`Bundle.mem_cayleyPathDomain_iff_of_mem_baseSet`), gives the two units that the smoothness lemma
asks for (`Bundle.isUnit_of_mem_cayleyPathDomain`), is open where `A` is continuous
(`Bundle.isOpen_cayleyPathDomain`), and contains the points where `A q` is compatible with, and
`q` tamed by, a linear symplectic form on the fibre
(`TauCeti.SymplecticForm.Compatible.mem_cayleyPathDomain`).

## Main definitions and results

* `ContMDiffAt.cayleyPathFormula_hom_bundle_of_vectorBundle`: smoothness of the Cayley path in the
  endomorphism bundle.
* `Bundle.cayleyPathDomain`, with `Bundle.mem_cayleyPathDomain_iff`,
  `Bundle.mem_cayleyPathDomain_iff_of_mem_baseSet`, `Bundle.isUnit_of_mem_cayleyPathDomain`,
  `Bundle.isOpen_cayleyPathDomain` and `TauCeti.SymplecticForm.Compatible.mem_cayleyPathDomain`.

The proof of `ContMDiffAt.cayleyPathFormula_hom_bundle_of_vectorBundle` is Tau Ceti's proof of
`ContMDiffAt.cayleyPathFormula_hom_bundle`, for the tangent bundle and order `∞`, with the tangent
bundle replaced by `V` and `∞` by any order.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Proposition 2.5.13 and Proposition 2.6.4
-/

public section

noncomputable section

open Bundle Set Topology TauCeti SymplecticGeometry
open scoped Manifold

section Smooth

variable {EB HB M : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [TopologicalSpace HB] {I : ModelWithCorners ℝ EB HB} [TopologicalSpace M] [ChartedSpace HB M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {EP HP P : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
  {IP : ModelWithCorners ℝ EP HP} [TopologicalSpace P] [ChartedSpace HP P]

/-- The Cayley path of two families of fibre endomorphisms of a vector bundle, along a `Cⁿ` base
map and with a `Cⁿ` coefficient, is `Cⁿ` at a point as a map into the endomorphism bundle, if both
families are `Cⁿ` there and both denominators of the path are units at that point. -/
theorem ContMDiffAt.cayleyPathFormula_hom_bundle_of_vectorBundle {n : WithTop ℕ∞} {f : P → M}
    {b : P → ℝ} {A B : (q : P) → V (f q) →L[ℝ] V (f q)} {q₀ : P}
    (hf : ContMDiffAt IP I n f q₀) (hb : ContMDiffAt IP 𝓘(ℝ) n b q₀)
    (hA : ContMDiffAt IP (I.prod 𝓘(ℝ, F →L[ℝ] F)) n
      (fun q ↦ TotalSpace.mk' (F →L[ℝ] F) (E := fun x ↦ V x →L[ℝ] V x) (f q) (A q)) q₀)
    (hB : ContMDiffAt IP (I.prod 𝓘(ℝ, F →L[ℝ] F)) n
      (fun q ↦ TotalSpace.mk' (F →L[ℝ] F) (E := fun x ↦ V x →L[ℝ] V x) (f q) (B q)) q₀)
    (hu₁ : IsUnit (1 - A q₀ * B q₀))
    (hu₂ : IsUnit (1 - b q₀ • cayleyFormula (A q₀) (B q₀))) :
    ContMDiffAt IP (I.prod 𝓘(ℝ, F →L[ℝ] F)) n
      (fun q ↦ TotalSpace.mk' (F →L[ℝ] F) (E := fun x ↦ V x →L[ℝ] V x) (f q)
        (cayleyPathFormula (b q) (A q) (B q))) q₀ := by
  rw [contMDiffAt_hom_bundle]
  refine ⟨hf, ?_⟩
  let e := trivializationAt F V (f q₀)
  let coord : (x : M) → (V x →L[ℝ] V x) → F →L[ℝ] F :=
    fun x C ↦ ContinuousLinearMap.inCoordinates F V F V (f q₀) x (f q₀) x C
  have hconj {x : M} (hx : x ∈ e.baseSet) (C : V x →L[ℝ] V x) :
      coord x C = (e.continuousLinearEquivAt ℝ x hx).conjContinuousAlgEquiv C :=
    ContinuousLinearMap.inCoordinates_eq_conjContinuousAlgEquiv hx C
  have hx₀ : f q₀ ∈ e.baseSet := mem_baseSet_trivializationAt F V (f q₀)
  have hinner : ContMDiffAt IP 𝓘(ℝ, ℝ × (F →L[ℝ] F) × (F →L[ℝ] F)) n
      (fun q ↦ (b q, coord (f q) (A q), coord (f q) (B q))) q₀ :=
    hb.prodMk_space (((contMDiffAt_hom_bundle _).1 hA).2.prodMk_space
      ((contMDiffAt_hom_bundle _).1 hB).2)
  let φ := (e.continuousLinearEquivAt ℝ (f q₀) hx₀).conjContinuousAlgEquiv
  have hu : (b q₀, coord (f q₀) (A q₀), coord (f q₀) (B q₀)) ∈ cayleyDomain (F →L[ℝ] F) := by
    rw [hconj hx₀, hconj hx₀, map_mem_cayleyDomain_iff φ]
    exact mem_cayleyDomain.2 ⟨hu₁, hu₂⟩
  obtain ⟨hu₁', hu₂'⟩ := mem_cayleyDomain.1 hu
  refine ((contDiffAt_cayleyPathFormula hu₁' hu₂').comp_contMDiffAt
    (f := fun q ↦ (b q, coord (f q) (A q), coord (f q) (B q)))
    hinner).congr_of_eventuallyEq ?_
  filter_upwards [hf.continuousAt.eventually_mem_baseSet_trivializationAt F V] with q hq
  rw [Function.comp_apply, hconj hq, hconj hq]
  exact (hconj hq _).trans (map_cayleyPathFormula _ _ _ _)

end Smooth

namespace Bundle

variable {M : Type*} [TopologicalSpace M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]

variable (F V) in
/-- The points `q` of the endomorphism bundle of `V` such that the Cayley path from the reference
endomorphism `A q` to `q` is defined for every coefficient `b ∈ [0, 1]`: read in the preferred
trivialization at the base point of `q`, the triple `(b, A q, q)` lies in the domain
`SymplecticGeometry.cayleyDomain` of the Cayley path in `F →L[ℝ] F`. -/
def cayleyPathDomain
    (A : ∀ q : TotalSpace (F →L[ℝ] F) (fun x ↦ V x →L[ℝ] V x), V q.proj →L[ℝ] V q.proj) :
    Set (TotalSpace (F →L[ℝ] F) (fun x ↦ V x →L[ℝ] V x)) :=
  {q | ∀ b ∈ Icc (0 : ℝ) 1,
    (b, (VectorBundle.continuousLinearEquivAt ℝ F V q.proj).conjContinuousAlgEquiv (A q),
      (VectorBundle.continuousLinearEquivAt ℝ F V q.proj).conjContinuousAlgEquiv q.snd) ∈
      cayleyDomain (F →L[ℝ] F)}

variable {A : ∀ q : TotalSpace (F →L[ℝ] F) (fun x ↦ V x →L[ℝ] V x), V q.proj →L[ℝ] V q.proj}
  {q : TotalSpace (F →L[ℝ] F) (fun x ↦ V x →L[ℝ] V x)}

theorem mem_cayleyPathDomain_iff :
    q ∈ cayleyPathDomain F V A ↔ ∀ b ∈ Icc (0 : ℝ) 1,
      (b, (VectorBundle.continuousLinearEquivAt ℝ F V q.proj).conjContinuousAlgEquiv (A q),
        (VectorBundle.continuousLinearEquivAt ℝ F V q.proj).conjContinuousAlgEquiv q.snd) ∈
        cayleyDomain (F →L[ℝ] F) :=
  Iff.rfl

/-- A point `q` of the endomorphism bundle lies in the domain of the Cayley path exactly when the
triples `(b, A q, q)` for `b ∈ [0, 1]` lie in the domain of the Cayley path in the fibre ring. -/
theorem mem_cayleyPathDomain_iff_forall_mem_cayleyDomain :
    q ∈ cayleyPathDomain F V A ↔
      ∀ b ∈ Icc (0 : ℝ) 1, (b, A q, q.snd) ∈ cayleyDomain (V q.proj →L[ℝ] V q.proj) := by
  simp only [mem_cayleyPathDomain_iff, map_mem_cayleyDomain_iff]

/-- The domain of the Cayley path may be read through any linear trivialization whose base set
contains the base point: two such readings differ by an algebra automorphism of `F →L[ℝ] F`. -/
theorem mem_cayleyPathDomain_iff_of_mem_baseSet (e : Trivialization F (π F V)) [e.IsLinear ℝ]
    (hq : q.proj ∈ e.baseSet) :
    q ∈ cayleyPathDomain F V A ↔ ∀ b ∈ Icc (0 : ℝ) 1,
      (b, (e.continuousLinearEquivAt ℝ q.proj hq).conjContinuousAlgEquiv (A q),
        (e.continuousLinearEquivAt ℝ q.proj hq).conjContinuousAlgEquiv q.snd) ∈
        cayleyDomain (F →L[ℝ] F) := by
  simp only [mem_cayleyPathDomain_iff_forall_mem_cayleyDomain, map_mem_cayleyDomain_iff]

/-- At a point `q` of the domain of the Cayley path, both denominators of the Cayley path from
`A q` to `q` are units in the fibre ring, for every coefficient `b ∈ [0, 1]`. -/
theorem isUnit_of_mem_cayleyPathDomain (hq : q ∈ cayleyPathDomain F V A) {b : ℝ}
    (hb : b ∈ Icc (0 : ℝ) 1) :
    IsUnit (1 - A q * q.snd) ∧ IsUnit (1 - b • cayleyFormula (A q) q.snd) :=
  mem_cayleyDomain.1 (mem_cayleyPathDomain_iff_forall_mem_cayleyDomain.1 hq b hb)

/-- On an open set `U` of the endomorphism bundle on which the reference endomorphisms form a
continuous map into the endomorphism bundle, the points of the domain of the Cayley path form an
open set. -/
theorem isOpen_cayleyPathDomain [CompleteSpace F]
    {U : Set (TotalSpace (F →L[ℝ] F) (fun x ↦ V x →L[ℝ] V x))} (hU : IsOpen U)
    (hA : ContinuousOn
      (fun q ↦ TotalSpace.mk' (F →L[ℝ] F) (E := fun x ↦ V x →L[ℝ] V x) q.proj (A q)) U) :
    IsOpen (U ∩ cayleyPathDomain F V A) := by
  refine isOpen_iff_mem_nhds.2 fun q₀ hq₀ ↦ ?_
  -- Read both the reference and the point in the preferred trivialization at `q₀.proj`.
  let x₀ := q₀.proj
  let e := trivializationAt F V x₀
  let coord : ∀ q : TotalSpace (F →L[ℝ] F) (fun x ↦ V x →L[ℝ] V x),
      (V q.proj →L[ℝ] V q.proj) → F →L[ℝ] F :=
    fun q C ↦ ContinuousLinearMap.inCoordinates F V F V x₀ q.proj x₀ q.proj C
  have hcA : ContinuousAt (fun q ↦ coord q (A q)) q₀ :=
    ((continuousAt_hom_bundle _ _).1 ((hA q₀ hq₀.1).continuousAt (hU.mem_nhds hq₀.1))).2
  have hcB : ContinuousAt (fun q ↦ coord q q.snd) q₀ :=
    ((continuousAt_hom_bundle _ (fun q ↦ q)).1 continuousAt_id).2
  have hbase : {q : TotalSpace (F →L[ℝ] F) (fun x ↦ V x →L[ℝ] V x) | q.proj ∈ e.baseSet} ∈
      𝓝 q₀ :=
    (FiberBundle.continuous_proj _ _).continuousAt.eventually_mem_baseSet_trivializationAt F V
  -- In this trivialization, membership is an open condition on the pair of readings.
  have hmem {q : TotalSpace (F →L[ℝ] F) (fun x ↦ V x →L[ℝ] V x)} (hq : q.proj ∈ e.baseSet) :
      q ∈ cayleyPathDomain F V A ↔
        (coord q (A q), coord q q.snd) ∈
          {p : (F →L[ℝ] F) × (F →L[ℝ] F) | ∀ b ∈ Icc (0 : ℝ) 1,
            (b, p.1, p.2) ∈ cayleyDomain (F →L[ℝ] F)} := by
    simp only [coord, ContinuousLinearMap.inCoordinates_eq_conjContinuousAlgEquiv hq]
    exact mem_cayleyPathDomain_iff_of_mem_baseSet e hq
  have hW := (hcA.prodMk hcB).preimage_mem_nhds
    ((isOpen_setOfPred_forall_Icc_mem_cayleyDomain (F →L[ℝ] F)).mem_nhds
      ((hmem (mem_baseSet_trivializationAt F V x₀)).1 hq₀.2))
  filter_upwards [hU.mem_nhds hq₀.1, hbase, hW] with q hqU hqe hqW
  exact ⟨hqU, (hmem hqe).2 hqW⟩

end Bundle

namespace TauCeti.SymplecticForm

variable {M : Type*} [TopologicalSpace M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {A : ∀ q : TotalSpace (F →L[ℝ] F) (fun x ↦ V x →L[ℝ] V x), V q.proj →L[ℝ] V q.proj}
  {q : TotalSpace (F →L[ℝ] F) (fun x ↦ V x →L[ℝ] V x)}
  {ω : SymplecticForm (V q.proj)} {J₀ J : AlmostComplexStructure (V q.proj)}

/-- A point `q` of the endomorphism bundle lies in the domain of the Cayley path from `A q` if,
for some symplectic form `ω` on the fibre, `A q` represents an `ω`-compatible and `q` an
`ω`-tame complex structure. -/
theorem Compatible.mem_cayleyPathDomain (h₀ : ω.Compatible J₀) (h : ω.Tames J)
    (hA : (A q).toLinearMap = J₀.toLinearMap) (hB : q.snd.toLinearMap = J.toLinearMap) :
    q ∈ Bundle.cayleyPathDomain F V A :=
  Bundle.mem_cayleyPathDomain_iff_forall_mem_cayleyDomain.2 fun _ hb ↦
    h₀.mem_cayleyDomain_of_continuousLinearEquiv h
      (VectorBundle.continuousLinearEquivAt ℝ F V q.proj) hA hB
      (abs_le.2 ⟨by linarith [hb.1], hb.2⟩)

end TauCeti.SymplecticForm

end
