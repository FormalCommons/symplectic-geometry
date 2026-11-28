/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.HPrinciple.FormSpaces
public import TauCeti.Topology.ConnectedComponents
public import TauCeti.Topology.Homotopy.HomotopyGroup.WeakHomotopyEquivalence
public import Mathlib.Topology.Homotopy.Equiv
import SymplecticGeometry.Geometry.Symplectic.HPrinciple.Components
import TauCeti.AlgebraicTopology.Homotopy.Whitehead
import SymplecticGeometry.Geometry.Symplectic.HPrinciple.Relative.Basic
import SymplecticGeometry.Geometry.Manifold.DeRham.Basic
import SymplecticGeometry.Geometry.Manifold.DeRham.Map
import SymplecticGeometry.AlgebraicTopology.Homotopy.Relative.WeakEquivalence
import SymplecticGeometry.AlgebraicTopology.Homotopy.Relative.FreeCompression
import TauCeti.Topology.Homotopy.Extension.Cube
import SymplecticGeometry.Topology.Homotopy.Cube.ConvexExtension
import TauCeti.Topology.Homotopy.Cube.Basic
import Mathlib.Topology.Homotopy.Path

/-!
# The parametric h-principle for symplectic forms on open manifolds

Throughout, `M` is a σ-compact Hausdorff manifold without boundary, modelled on a
finite-dimensional space, none of whose connected components is compact. Give the smooth
two-forms on its tangent bundle the frame topology of a covering frame system. For a closed
two-form `α`, the inclusion of the symplectic forms in the class of `α` into the nondegenerate
two-forms is then a weak homotopy equivalence
(`isWeakHomotopyEquivalence_inclusion_symplecticFormsInClass`).

When moreover each connected component of `M` compresses into a compact set by a smooth
isotopy starting at the identity, the inclusion is a homotopy equivalence
(`exists_homotopyEquiv_symplecticFormsInClass`).

## Proof

Write `X` for the space of nondegenerate forms and `A ⊆ X` for the symplectic forms in the class
of `α`. By `ContinuousMap.isWeakHomotopyEquivalence_subtypeVal_iff`, it suffices that every point
of `X` is joined to `A` by a path and that every relative homotopy set `π_{n+1}(X, A, a)` is
trivial. Both follow from one deformation statement, which is the continuous parametric relative
h-principle `exists_continuousMap_homotopy_closed`: a continuous family `g` of nondegenerate
forms over a compact Hausdorff `P`, lying in `A` over a closed `P₀ ⊆ P`, is homotopic, through
families that lie in `A` over `P₀`, to a family lying in `A`, as soon as there is a continuous
family `β` of forms in the class of `α` that agrees with `g` over `P₀`.

* For a point of `X`, take `P` a point, `P₀ = ∅` and `β` constant at `α`; the homotopy is the
  path.
* For a relative cube `g : (I × I^N, ∂) → (X, A)`, the forms in the class of `α` are a convex
  set, so the restriction of `g` to the boundary extends to a family `β` of forms in that class
  on the whole cube (`Convex.exists_continuousMap_eqOn_cubeBoundary`, read on `I × I^N` through
  `TauCeti.piOptionEquivProdHomeomorph`). The homotopy is then what
  `TauCeti.RelHomotopyGroup.subsingleton_ofSubset_of_forall_homotopicWith` asks for.

Last, `ContinuousMap.isWeakHomotopyEquivalence_inclusion_iff_subtypeVal` identifies the inclusion
of `A` into `X` with the inclusion of the symplectic forms into the nondegenerate forms.

For the homotopy equivalence, work on each component `c.opens` with the frame topology
`Bundle.ContMDiffTwoForm.trivializationAtFrameTopology`. The component is again a manifold as
above: it is σ-compact as a closed subset of `M` (a local instance inside the proof, from
`IsClosed.sigmaCompactSpace`), and its connected components are not compact, since the component
in `c.opens` of a point equals the component of that point in `M`, `c.opens` being clopen.
There both spaces have CW type (`cwType_nondegenerateForms`, `cwType_symplecticFormsInClass`),
so Whitehead's theorem,
Tau Ceti's `ContinuousMap.IsWeakHomotopyEquivalence.homotopyEquiv`, turns the weak equivalence
into a homotopy equivalence. The product of these over the components
(`ContinuousMap.HomotopyEquiv.piCongrRight`) is carried to `M` by the homeomorphisms
`symplecticFormsInClassHomeomorphPi` and `nondegenerateFormsHomeomorphPi` of
`HPrinciple/Components.lean`, which match the inclusions
(`nondegenerateFormsHomeomorphPi_inclusion`).

## References

* [Y. Eliashberg and N. Mishachev, *Introduction to the h-principle*][EliashbergMishachev2002],
  Theorems 10.2.1 and 10.2.2 (first edition).
* Y. Eliashberg and N. Mishachev, *Holonomic approximation and Gromov's h-principle*,
  arXiv:math/0101196, Theorem 2.1.2.
* M. Bertelson, *A h-principle for open relations invariant under foliated isotopies*,
  arXiv:math/0011045, Theorem 8.2.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Theorem 4.5 (Whitehead's
  theorem).
-/

public section

open Set Bundle SymplecticGeometry.Bundle TauCeti TopologicalSpace
open scoped Manifold Topology ContDiff ContinuousMap

namespace SymplecticGeometry

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-- A nondegenerate two-form on the tangent bundle whose Tau Ceti form is closed and lies in the
class of `α` is a symplectic form in that class. -/
private theorem mem_symplecticFormsInClass_of_mextDerivₗ_eq_zero {α : SmoothTwoForm I M}
    {σ : ContMDiffTwoForm I ⊤ E (TangentSpace I (M := M))} (hσ : σ.IsNondegenerate)
    (hd : mextDerivₗ I 2 (ContMDiffTwoForm.tangentEquiv σ) = 0)
    (hex : ContMDiffTwoForm.tangentEquiv σ - α ∈ exactForms I M 2) :
    σ ∈ symplecticFormsInClass α :=
  mem_symplecticFormsInClass.2
    ⟨⟨(SmoothForm.isClosed_iff_mem_closedForms _).2
      ((mem_closedForms_iff_mextDerivₗ_eq_zero (φ := _)).2 hd),
      ContMDiffTwoForm.isNondegenerate_tangentEquiv_iff.2 hσ⟩, hex⟩

variable [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless] {ι : Type*}
  (e : ι → Trivialization (E [⋀^Fin 2]→L[ℝ] ℝ)
    (π (E [⋀^Fin 2]→L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x [⋀^Fin 2]→L[ℝ] Trivial M ℝ x)))
  [∀ i, MemTrivializationAtlas (e i)]
  (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)

/-- The deformation step. Over a compact Hausdorff `P` with a closed `P₀ ⊆ P`, a continuous
family `g` of nondegenerate forms that agrees over `P₀` with a continuous family `β` of forms in
the class of the closed form `α` is homotopic, through families sending `P₀` to symplectic forms
in the class of `α`, to a family of symplectic forms in the class of `α`. -/
private theorem exists_homotopicWith_symplecticFormsInClass
    (hM : ∀ x : M, ¬ IsCompact (connectedComponent x)) (hcover : ∀ x, ∃ i, x ∈ U i)
    {α : SmoothTwoForm I M} (hα : α ∈ closedForms I M 2) {P : Type*} [TopologicalSpace P]
    [CompactSpace P] [T2Space P] {P₀ : Set P} (hP₀ : IsClosed P₀) :
    letI := ContMDiffSection.frameTopology (I := I) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) e U hU
    ∀ (g : C(P, nondegenerateForms I M))
      (β : C(P, ContMDiffTwoForm I ⊤ E (TangentSpace I (M := M)))),
      (∀ l, ContMDiffTwoForm.tangentEquiv (β l) - α ∈ exactForms I M 2) →
      (∀ l ∈ P₀, β l = g l) →
      ∃ g' : C(P, nondegenerateForms I M),
        (∀ l, (g' l : ContMDiffTwoForm I ⊤ E (TangentSpace I (M := M))) ∈
          symplecticFormsInClass α) ∧
        g.HomotopicWith g' fun f ↦ MapsTo f P₀ (Subtype.val ⁻¹' symplecticFormsInClass α) := by
  let _ := ContMDiffSection.frameTopology (I := I) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) e U hU
  intro g β hβ hβg
  let τ : C(P, {σ : ContMDiffTwoForm I ⊤ E (TangentSpace I (M := M)) // σ.IsNondegenerate}) :=
    ⟨fun l ↦ ⟨g l, mem_nondegenerateForms.1 (g l).property⟩,
      (continuous_subtypeVal.comp g.continuous).subtype_mk _⟩
  obtain ⟨F, hF₀, hFP₀, hF₁⟩ := exists_continuousMap_homotopy_closed e U hU hM hcover hP₀ τ
    (α := fun l ↦ ContMDiffTwoForm.tangentEquiv (β l)) (by simpa using β.continuous)
    (fun l ↦ (mem_closedForms_iff_mextDerivₗ_eq_zero (φ := _)).1 (by
      simpa using add_mem (exactForms_le_closedForms I 2 (hβ l)) hα)) hβ
    (fun l hl ↦ by simp [τ, hβg l hl])
  let G : C(unitInterval × P, nondegenerateForms I M) :=
    ⟨fun p ↦ ⟨(F (p.2, p.1)).val, mem_nondegenerateForms.2 (F (p.2, p.1)).property⟩,
      (continuous_subtypeVal.comp (F.continuous.comp continuous_swap)).subtype_mk _⟩
  refine ⟨G.curry 1, fun l ↦ mem_symplecticFormsInClass_of_mextDerivₗ_eq_zero
    (F (l, 1)).property (hF₁ l).1 (hF₁ l).2, ⟨{
      toFun := G
      continuous_toFun := G.continuous
      map_zero_left := fun l ↦ Subtype.ext (by simp [G, hF₀, τ])
      map_one_left := fun l ↦ (G.curry_apply 1 l).symm
      prop' := fun t l hl ↦ mem_symplecticFormsInClass_of_mextDerivₗ_eq_zero
        (F (l, t)).property (hFP₀ l hl t).1 (hFP₀ l hl t).2 }⟩⟩

/-- **The parametric h-principle for symplectic forms on open manifolds.** Suppose
that `M` is a Hausdorff, σ-compact manifold without boundary, modelled on a finite-dimensional
space, none of whose connected components is compact, and give the smooth two-forms on its
tangent bundle the frame topology of a covering frame system. For a closed two-form `α` on `M`,
the inclusion of the symplectic forms in the class of `α` into the nondegenerate two-forms is a
weak homotopy equivalence.

Milestone: *Gromov's h-principle for symplectic forms on open manifolds*. -/
theorem isWeakHomotopyEquivalence_inclusion_symplecticFormsInClass
    (hM : ∀ x : M, ¬ IsCompact (connectedComponent x)) (hcover : ∀ x, ∃ i, x ∈ U i)
    {α : SmoothTwoForm I M} (hα : α ∈ closedForms I M 2) :
    letI := ContMDiffSection.frameTopology (I := I) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) e U hU
    (ContinuousMap.inclusion
      (symplecticFormsInClass_subset_nondegenerateForms α)).IsWeakHomotopyEquivalence := by
  let _ := ContMDiffSection.frameTopology (I := I) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) e U hU
  have := ContMDiffSection.isTopologicalAddGroup_frameTopology (I := I)
    (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) e U hU
  have := ContMDiffSection.continuousSMul_frameTopology (𝕜 := ℝ) (I := I)
    (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) e U hU
  let S := symplecticFormsInClass α
  let A : Set (nondegenerateForms I M) := Subtype.val ⁻¹' S
  -- The forms in the class of `α`, a translate of a subspace.
  let C := {σ : ContMDiffTwoForm I ⊤ E (TangentSpace I (M := M)) |
    ContMDiffTwoForm.tangentEquiv σ - α ∈ exactForms I M 2}
  have hC : Convex ℝ C := by
    simpa [C, Set.preimage, sub_eq_neg_add] using
      ((exactForms I M 2).convex.translate_preimage_right (-α)).linear_preimage
        ContMDiffTwoForm.tangentEquiv.toLinearMap
  have hαC : ContMDiffTwoForm.tangentEquiv.symm α ∈ C := by
    simp only [C, mem_ofPred_eq, LinearEquiv.apply_symm_apply, sub_self]
    exact zero_mem _
  have hA : (ContinuousMap.subtypeVal A).IsWeakHomotopyEquivalence := by
    refine ContinuousMap.isWeakHomotopyEquivalence_subtypeVal_iff.2 ⟨fun x ↦ ?_, fun n a ↦ ?_⟩
    · obtain ⟨g', hg', ⟨G⟩⟩ := exists_homotopicWith_symplecticFormsInClass e U hU hM hcover hα
        (P := Unit) isClosed_empty (ContinuousMap.const _ x)
        (ContinuousMap.const _ (ContMDiffTwoForm.tangentEquiv.symm α)) (fun _ ↦ hαC)
        (fun _ h ↦ h.elim)
      exact ⟨⟨g' (), hg' ()⟩, ⟨(G.toHomotopy.evalAt ()).symm⟩⟩
    · refine RelHomotopyGroup.subsingleton_ofSubset_of_forall_homotopicWith
        (X := TopCat.of (nondegenerateForms I M)) (fun g hg ↦ ?_) a
      let φ := piOptionEquivProdHomeomorph fun _ : Option (Fin n) ↦ unitInterval
      obtain ⟨b, hb, hbC⟩ := hC.exists_continuousMap_eqOn_cubeBoundary ⟨_, hαC⟩
        (f := fun y ↦ ((g (φ y) : nondegenerateForms I M) :
          ContMDiffTwoForm I ⊤ E (TangentSpace I (M := M))))
        (by fun_prop) fun y hy ↦
          (mem_symplecticFormsInClass.1
            (hg (piOptionEquivProdHomeomorph_mem_prodBoundary_iff.2 hy))).2
      exact exists_homotopicWith_symplecticFormsInClass e U hU hM hcover hα
        hasHomotopyExtensionProperty_prodBoundary.isClosed g
        (b.comp φ.symm) (fun z ↦ hbC ⟨_, rfl⟩) fun z hz ↦
          (hb (piOptionEquivProdHomeomorph_symm_mem_boundary hz)).trans
            (by simp only [φ, Homeomorph.apply_symm_apply])
  exact (ContinuousMap.isWeakHomotopyEquivalence_inclusion_iff_subtypeVal
    (symplecticFormsInClass_subset_nondegenerateForms α)).2 hA

/-- Whitehead's theorem applied to the weak equivalence: if moreover a smooth isotopy from the
identity of `M` ends at a map whose image has compact closure, so that both spaces have CW type,
the inclusion of the symplectic forms in the class of `α` into the nondegenerate forms is the
forward map of a homotopy equivalence. -/
private theorem exists_homotopyEquiv_symplecticFormsInClass_of_smoothIsotopy
    (hM : ∀ x : M, ¬ IsCompact (connectedComponent x)) (hcover : ∀ x, ∃ i, x ∈ U i)
    {α : SmoothTwoForm I M} (hα : α ∈ closedForms I M 2) {j : C^∞⟮I, M; I, M⟯}
    (h : SmoothIsotopy (ContMDiffMap.id) j) (hj : IsCompact (closure (Set.range j))) :
    letI := ContMDiffSection.frameTopology (I := I) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) e U hU
    ∃ φ : symplecticFormsInClass α ≃ₕ nondegenerateForms I M,
      ⇑φ.toFun = Set.inclusion (symplecticFormsInClass_subset_nondegenerateForms α) := by
  let _ := ContMDiffSection.frameTopology (I := I) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) e U hU
  have := cwType_nondegenerateForms e U hU hcover h hj
  have := cwType_symplecticFormsInClass e U hU hcover hα h hj
  have hf := isWeakHomotopyEquivalence_inclusion_symplecticFormsInClass e U hU hM hcover hα
  exact ⟨hf.homotopyEquiv, by
    rw [ContinuousMap.IsWeakHomotopyEquivalence.homotopyEquiv_toFun]
    ext σ
    simp⟩

/-- **The homotopy equivalence of the spaces of forms.** Let `M` be a Hausdorff, σ-compact
manifold without boundary, modelled on a finite-dimensional space, none of whose connected
components is compact, and give the smooth two-forms on its tangent bundle the
frame topology of a covering frame system. Suppose that each connected component `c` of `M`
compresses into a compact set: some smooth isotopy of `c.opens` starts at the identity and ends
at a map `j` whose image has compact closure. Then, for a closed two-form `α` on `M`, the
inclusion of the symplectic forms in the class of `α` into the nondegenerate two-forms is a
homotopy equivalence.

The hypothesis holds when `M` itself compresses into a compact set, since each slice of such an
isotopy maps every component into itself; it also holds for a manifold of finite type, the
interior of a compact manifold with boundary, by compression along a collar of the boundary.
Without a hypothesis of this kind the two spaces need not have CW type. -/
theorem exists_homotopyEquiv_symplecticFormsInClass
    (hM : ∀ x : M, ¬ IsCompact (connectedComponent x)) (hcover : ∀ x, ∃ i, x ∈ U i)
    {α : SmoothTwoForm I M} (hα : α ∈ closedForms I M 2) :
    letI := I.toHomeomorph.locallyConnectedSpace
    letI := ChartedSpace.locallyConnectedSpace H M
    (∀ c : ConnectedComponents M, ∃ j : C^∞⟮I, c.opens; I, c.opens⟯,
      Nonempty (SmoothIsotopy (ContMDiffMap.id) j) ∧ IsCompact (closure (Set.range j))) →
    letI := ContMDiffSection.frameTopology (I := I) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) e U hU
    ∃ φ : symplecticFormsInClass α ≃ₕ nondegenerateForms I M,
      ⇑φ.toFun = Set.inclusion (symplecticFormsInClass_subset_nondegenerateForms α) := by
  have := I.toHomeomorph.locallyConnectedSpace
  have := ChartedSpace.locallyConnectedSpace H M
  intro hj
  let _ := ContMDiffSection.frameTopology (I := I) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) e U hU
  let _ (c : ConnectedComponents M) := ContMDiffTwoForm.trivializationAtFrameTopology I c.opens
  -- On each component, Whitehead's theorem gives a homotopy equivalence.
  have key (c : ConnectedComponents M) : ∃ φ : symplecticFormsInClass
      (SmoothForm.mpullback (Subtype.val : c.opens → M) contMDiff_subtypeVal α) ≃ₕ
        nondegenerateForms I c.opens,
      ⇑φ.toFun = Set.inclusion (symplecticFormsInClass_subset_nondegenerateForms _) := by
    have : SigmaCompactSpace c.opens := c.isClopen_opens.isClosed.sigmaCompactSpace
    obtain ⟨j, ⟨h⟩, hj⟩ := hj c
    -- The connected component of a point `x` of `c.opens` is that of `x` in `M`.
    have hc (x : c.opens) : ¬ IsCompact (connectedComponent x) := fun hx ↦
      hM x <| c.isClopen_opens.connectedComponentIn_eq x.property ▸
        connectedComponentIn_eq_image x.property ▸ hx.image continuous_subtypeVal
    have := exists_homotopyEquiv_symplecticFormsInClass_of_smoothIsotopy _ _
      (fun x ↦ (trivializationAt _ _ x).coe_baseSetOpens.subset) hc
      (FiberBundle.exists_mem_baseSetOpens_trivializationAt _ _)
      (SmoothForm.mpullback_mem_closedForms (Subtype.val : c.opens → M) contMDiff_subtypeVal hα)
      h hj
    rwa [← ContMDiffTwoForm.trivializationAtFrameTopology_def] at this
  choose φ hφ using key
  refine ⟨(symplecticFormsInClassHomeomorphPi e U hU hcover α).toHomotopyEquiv.trans
    ((ContinuousMap.HomotopyEquiv.piCongrRight φ).trans
      (nondegenerateFormsHomeomorphPi e U hU hcover).symm.toHomotopyEquiv), funext fun σ ↦ ?_⟩
  refine (Homeomorph.symm_apply_eq _).2 ?_
  rw [nondegenerateFormsHomeomorphPi_inclusion]
  funext c
  exact congrFun (hφ c) _

end SymplecticGeometry

end
