/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.VectorBundle.Orientation.FiberwiseEquiv
public import TauCeti.Topology.VectorBundle.Orientation.SectionIndex

/-!
# Local indices of sections along fibrewise isomorphisms

Let `φ x : E'_x ≃ E_x` be a fibrewise isomorphism of real vector bundles of rank `n + 1` over a
manifold `M` of dimension `n + 1`, carrying an orientation `o'` of `E'` to an orientation `o` of
`E`. Then the local index of a section `s` of `E'` at any point is the local index of the section
`x ↦ φ x (s x)` of `E` there
(`TauCeti.VectorBundleOrientation.sectionIndex_eq_of_fiberwise`). Both indices are Kronecker
pairings with pull-backs of Thom classes, and the map of Thom pairs of `φ` pulls the Thom class of
`(E, o)` back to that of `(E', o')`
(`TauCeti.VectorBundleOrientation.singularCohomologyMap_thomPairMapOfFiberwise_thomClass`).

## Main results

* `TauCeti.thomPairMapOfNeZero_comp_thomPairMapOfFiberwise_of_eq`: a map into the Thom pair of
  `E'`, followed by the map of Thom pairs of `φ`, is the map into the Thom pair of `E` of the
  composite.
* `TauCeti.VectorBundleOrientation.sectionIndex_eq_of_fiberwise`: orientation-preserving
  fibrewise isomorphisms preserve local indices of sections.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §9 (bundle maps and orientations) and §11 (the Euler class and sections).
-/

public section

noncomputable section

open Bundle CategoryTheory Module Set

universe w

namespace TauCeti

section ThomPair

variable {B : Type w} [TopologicalSpace B] {F : Type*} {E : B → Type w}
  [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)]
  [∀ b, TopologicalSpace (E b)] {B' : Type w} [TopologicalSpace B'] {F' : Type*}
  {E' : B' → Type w} [TopologicalSpace (TotalSpace F' E')] [∀ b, AddCommMonoid (E' b)]
  [∀ b, Module ℝ (E' b)] [∀ b, TopologicalSpace (E' b)] {g : C(B', B)}
  {φ : ∀ b', E' b' ≃L[ℝ] E (g b')} {X : Type w} [TopologicalSpace X]

/-- A map `f : X → E'` that is nonzero off `S`, as a map of pairs into the Thom pair of `E'`,
followed by the map of Thom pairs of a fibrewise isomorphism `φ b' : E'_{b'} ≃ E_{g b'}`, is the
map of pairs into the Thom pair of `E` given by `x ↦ φ (f x)`. -/
theorem thomPairMapOfNeZero_comp_thomPairMapOfFiberwise_of_eq (f : C(X, TotalSpace F' E'))
    {S : Set X} (h : ∀ x ∉ S, (f x).snd ≠ 0)
    (hφ : Continuous fun v : TotalSpace F' E' ↦ TotalSpace.mk' F (g v.proj) (φ v.proj v.snd))
    {f' : C(X, TotalSpace F E)}
    (hf' : ∀ x, f' x = TotalSpace.mk' F (g (f x).proj) (φ (f x).proj (f x).snd))
    (h' : ∀ x ∉ S, (f' x).snd ≠ 0) :
    thomPairMapOfNeZero f h ≫ thomPairMapOfFiberwise hφ = thomPairMapOfNeZero f' h' := by
  refine TopPair.hom_ext_of_fst _ (TopCat.ext fun x ↦ ?_)
  rw [TopPair.Hom.fst_comp, ConcreteCategory.comp_apply]
  -- The source of the pair is `X` only after unfolding `TopPair.ofSubset`.
  erw [thomPairMapOfNeZero_fst_apply, thomPairMapOfFiberwise_fst_apply,
    thomPairMapOfNeZero_fst_apply, hf']

end ThomPair

namespace VectorBundleOrientation

variable {M E' : Type} [TopologicalSpace M] [T2Space M] [NormedAddCommGroup E']
  [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [ChartedSpace E' M] {n : ℕ}
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {E : M → Type}
  [TopologicalSpace (TotalSpace F E)] [∀ x, AddCommMonoid (E x)] [∀ x, Module ℝ (E x)]
  [∀ x, TopologicalSpace (E x)] [FiberBundle F E] [VectorBundle ℝ F E]
  (o : VectorBundleOrientation F E (Fin (n + 1))) (hF : finrank ℝ F = n + 1)
  (oM : HomologicalOrientation M E' (n + 1))
  {F' : Type} [NormedAddCommGroup F'] [NormedSpace ℝ F'] {E₁ : M → Type}
  [TopologicalSpace (TotalSpace F' E₁)] [∀ x, AddCommMonoid (E₁ x)] [∀ x, Module ℝ (E₁ x)]
  [∀ x, TopologicalSpace (E₁ x)] [FiberBundle F' E₁] [VectorBundle ℝ F' E₁]
  (o' : VectorBundleOrientation F' E₁ (Fin (n + 1))) (hF' : finrank ℝ F' = n + 1)

/-- **Local indices along fibrewise isomorphisms.** Let `φ x : E₁_x ≃ E_x` be a fibrewise
isomorphism, with continuous total-space map, that carries the orientation `o'` of `E₁` to the
orientation `o` of `E`. Then the local index of a section `s` of `E₁` at `z` is the local index of
the section `x ↦ φ x (s x)` of `E` at `z`. -/
theorem sectionIndex_eq_of_fiberwise {φ : ∀ x, E₁ x ≃L[ℝ] E x}
    (hφ : Continuous fun v : TotalSpace F' E₁ ↦ TotalSpace.mk' F v.proj (φ v.proj v.snd))
    (ho : ∀ x, Orientation.map (Fin (n + 1)) (φ x).toLinearEquiv (o' x) = o x)
    {s : ∀ x, E₁ x} (hs : Continuous fun x ↦ TotalSpace.mk' F' x (s x)) (z : M) :
    o'.sectionIndex hF' oM hs z =
      o.sectionIndex hF oM (s := fun x ↦ φ x (s x)) (hφ.comp hs) z := by
  have hzero : ∀ x, φ x (s x) = 0 ↔ s x = 0 := fun x ↦ (φ x).map_eq_zero_iff
  by_cases h : ∃ U, IsOpen U ∧ z ∈ U ∧ ∀ x ∈ U, s x = 0 → x = z
  · obtain ⟨U, hU, hz, hUz⟩ := h
    rw [sectionIndex_eq o' hF' oM hs hU hz hUz,
      sectionIndex_eq o hF oM (hφ.comp hs) hU hz fun x hx h0 ↦ hUz x hx ((hzero x).1 h0),
      ← singularCohomologyMap_thomPairMapOfFiberwise_thomClass o hF o' hF'
        (g := ContinuousMap.id M) hφ ho, ← TopPair.singularCohomologyMap_comp_apply,
      thomPairMapOfNeZero_comp_thomPairMapOfFiberwise_of_eq (g := ContinuousMap.id M) _ _ hφ
      (f' := ⟨fun x : U ↦ TotalSpace.mk' F x.val (φ x.val (s x.val)),
        (hφ.comp hs).comp continuous_subtypeVal⟩) fun _ ↦ rfl]
  · rw [sectionIndex_of_not_isolated _ _ _ _ h, sectionIndex_of_not_isolated]
    simpa only [hzero] using h

end VectorBundleOrientation

end TauCeti

end
